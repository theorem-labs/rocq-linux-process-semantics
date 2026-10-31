(** * EquivalenceDefinition.MeasureLib — the measure combinator library

    NOT A TRUST BOUNDARY, and the distinction is worth stating exactly
    rather than leaving to be inferred from the absence of the banner.
    [Measure] and [FinInput] are trusted because a top-level check
    ascribes against statements built from their definitions: change
    [Measure.weight_bound_T] and every submission that ever passed now
    means something else.  This file changes no statement.  A task's
    weight function and declared total are trusted metadata whatever
    their provenance — [Measure.DISTRIBUTION] declares [w] and [M] as
    [Parameter]s, asks two properties of [w] and nothing at all of
    [M] — so a distribution BUILT here is trusted neither more nor less
    than one written out by hand.  What this file emits is PROOFS: those
    two properties, and the partial-sum bounds a submission needs in
    order to get from a distribution to [Measure.weight_bound_T].
    Delete the file and every consumer of it could still be written; it
    would just be written again, once per task, by hand.

    An edit here can still break something, and it is worth naming which
    thing: not the meaning of any obligation, but the axioms a proof
    rests on.  Adding an [Axiom] to a proof library and leaning on it is
    a move available in any proof library, this one included; it is a
    question for an assumption audit of the submitted development, and
    not one this file's status answers either way.

    ** Every weight here is a function of the CORE, which is the design

    [Measure.DISTRIBUTION] carries [w_core_blind]: a weight must agree
    on records with equal [FinInput.fin_core].  The obligation is not
    hard, but it is stated once per distribution and a task author
    should never have to think about it.  So this library does not build
    weights on [FinInput.FinProcInput] at all.  It builds them on
    [FinInput.FinCore] — a [CoreDistribution] — and LIFTS through
    [FinInput.fin_core] ([cd_lift]).  [cd_lift_core_blind] is then a
    congruence: two records with the same core are handed to the same
    function at the same argument, so the values are not merely [Qeq],
    they are [eq], and the [Qeq] is [reflexivity] on top of a rewrite.
    [cd_lift_nonneg] is the [CoreDistribution]'s own field.  Those two
    obligations are discharged once, here, for every distribution this
    library will ever build, and the third — [M_nonneg], on the DECLARED
    mass and not on the weights — is discharged per combinator
    ([finite_support_mass_nonneg], [stdin_geometric_mass_nonneg], and
    [cd_scale_mass_nonneg] and [cd_mix2_mass_nonneg] to compose them),
    because nothing ties [cd_mass] to [cd_weight] and so no single lemma
    can cover it.  [Example_D] below is the claim compiled: a module
    that ascribes to [Measure.DISTRIBUTION] with no proof written at its
    definition site.

    Nothing is lost by that restriction, and it is not left as a
    plausible-sounding remark: [cd_lift_complete] proves that EVERY
    weight satisfying [Measure.DISTRIBUTION]'s two WEIGHT obligations is
    pointwise [Qeq] to the lift of a [CoreDistribution], at any declared
    mass one likes — [M_nonneg] constrains the mass alone and so puts no
    weight out of reach.  A weight this library cannot build is a weight
    [w_core_blind] would have rejected.  The library's shape is the
    obligation's shape.

    ** The sums bounded here are the sums the obligation talks about

    [Measure.weight_bound_T] is quantified over [Measure.sum_weights w l]
    for [l : list FinInput.FinProcInput].  [core_sum] is that sum for a
    lifted weight, and [core_sum_cd_lift] is the bridge — [eq], by
    conversion, not a transport a consumer has to remember to apply.
    Every bound below is stated on [core_sum], so a consumer proving
    [Measure.weight_bound_T] for [cd_lift D] rewrites once and is
    looking at a library lemma.

    Internally the sums are moved to [qsum] over
    [List.map FinInput.fin_core l] ([core_sum_map_fin_core]), which is
    what turns the obligation's hypothesis — [List.NoDup (List.map
    FinInput.fin_core l)], duplicate-freedom read on cores — into plain
    [List.NoDup] of a list of cores.  That is the form the counting
    arguments want, and it is why the bounds below can be proved by
    induction on a [List.NoDup] derivation at all.

    ** Finite support, and why its constructor demands a proof

    [finite_support] is the first combinator: a list of (core, weight)
    entries, weight zero off the listed cores, entries for a repeated
    core SUMMED rather than one of them silently winning
    ([dup_entries_weight_summed] pins that, and
    [dup_witness_attains_mass] pins why it has to be the summing
    reading).  Its declared mass is the sum of the entries' weights.

    It takes a proof that every entry is nonnegative, and there is no
    version of this constructor that does without one.
    [finite_support_bound] — the workhorse, that any list with
    duplicate-free cores sums to at most the declared mass — is FALSE
    otherwise, and false already on the EMPTY list: with a single entry
    of weight [-1] the declared mass is [-1] and the empty list sums to
    [0].  The refuting list being the empty one is what settles WHERE
    the hypothesis goes — no condition imposed on the list side can
    rescue the statement, so nonnegativity has to attach to the entries.
    Nor can it be demoted to a hypothesis of each lemma and dropped from
    the constructor: [cd_nonneg] is a FIELD of [CoreDistribution], so a
    [finite_support] that returned one without a proof would have to
    manufacture that field out of nothing.

    What a total constructor CAN do is CLAMP — replace each negative
    entry by zero, in the weights and in the declared mass together —
    and it is worth being exact about why that is refused, because no
    proof breaks under it: clamped entries are nonnegative, so
    [finite_support_bound] and both certificates go through unchanged.
    The objection is not mathematical.  It is that clamping silently
    rewrites the AUTHOR'S DECLARED MASS: someone who writes [-1] gets a
    distribution of mass [0], no error and no diagnostic, and a
    certificate pair that then truthfully certifies a total they never
    declared.  That is exactly the dishonesty the certificates exist to
    rule out, and a library that quietly repairs its input is worse than
    one that refuses it — the repair is invisible in the artifact a
    reader checks.  [negative_entries_no_core_distribution] is the
    refusal mechanized: no [CoreDistribution] whatever weighs cores the
    way a negative entry list does, because [cd_nonneg] refutes it at
    the rigged core.

    The bound has a REFINEMENT, and a task that does not use it is
    giving away its own margin: [finite_support_bound_subset] charges a
    list whose cores all satisfy a predicate [P] against the mass of
    the [P]-entries ALONE ([entries_restrict]), not against the
    declared total.  When a fire set is a known part of the support and
    the rest of the mass sits on cores the classifier accepts, the
    difference is the whole point —
    [finite_support_bound_subset_bites] pins it at the example, where
    restricting to one core halves the number the bound compares
    against.  Nothing is lost by having only the refinement:
    [entries_restrict_all] says [finite_support_bound] is its case at
    the predicate that accepts everything.

    ** Certificates: the declared mass is an upper bound, and it is attained

    [Measure]'s [M] is declared, never proved — the header there says so
    — and the honest thing a library can offer instead is a pair of
    finitary certificates about the [M] it declares.  Upper:
    [finite_support_mass_upper], which is [finite_support_bound] under
    the certificate's name, says no admissible list sums past the mass.
    Lower: [finite_support_mass_lower_witness] exhibits a list that
    reaches it, so the declared mass is not slack the author padded.
    [finite_support_mass_exact] puts the two together as a [Qeq].  The
    content of the lower half is separated from the CHOICE of list in
    [finite_support_mass_lower_on] — any duplicate-free list of cores
    covering the entries attains the mass — because a mixture has to
    attain two components on one list and neither's canonical witness
    need cover the other's cores.

    The lower witness needs a [FinInput.FinCore] to be wrapped back into
    a [FinInput.FinProcInput], since the obligation's lists are of
    records; [core_input] is that canonical embedding and
    [fin_core_core_input] is its section property.  The launch
    environment it invents is documented at the definition.  What is NOT
    claimed, and must not be read in, is that those records are VALID
    ([FinInput.valid_fin_input]) or rejected by anything: the
    certificate is arithmetic about the declared mass, not a statement
    about a fire set.  A task's actual [Measure.weight_bound_T] proof
    quantifies over lists it does not choose, and the bound — not the
    witness — is what it consumes.

    ** The geometric standard-input distribution

    [stdin_geometric] is the second combinator, and the one a task
    author wanting a BACKGROUND over inputs reaches for.  It fixes
    argv, envp and the file system to given values and spreads what is
    left over standard input the way a memoryless source does: stop
    after each byte with weight [p_stop], otherwise emit one of 256
    bytes.  A core whose argv, envp or file system differ from the
    fixed ones weighs zero; a matching core whose standard input has
    length [n] weighs [p_stop * (1 - p_stop) ^ n * (1 / 256) ^ n].  The
    declared mass is [1].

    Internally the two powers are carried as one ratio,
    [(1 - p_stop) * (1 # 256)] — [geo_mass] is its [n]-th power and
    [geo_point] is [p_stop] times that — because every proof below
    multiplies them together anyway.  The form this header and the
    plan quote is a LEMMA, not a second definition
    ([geo_mass_closed_form], [geo_point_closed_form]), so there is one
    object with two readings and no risk of them drifting apart.

    THE SIDE CONDITIONS ARE [0 <= p_stop] AND [p_stop <= 1], and they
    are constructor arguments for the reason [finite_support]'s
    nonnegativity proof is one: [cd_nonneg] is a field.  Those two are
    exactly what the weight's nonnegativity needs.  The intended family
    is [0 < p_stop <= 1] and the STRICT inequality is deliberately not
    demanded, because nothing the CONSTRUCTOR needs uses it.  What
    [p_stop = 0] costs is worth stating rather than hiding: the weight
    is then identically zero, the declared mass [1] remains an honest
    upper bound, and nothing comes near it — so it is the LOWER
    certificate ([stdin_geometric_mass_lower_certificate], below) that
    asks for [0 < p_stop], as a hypothesis of THAT LEMMA and not of the
    constructor.  Asking for a hypothesis in order not to use it would
    misreport where the strictness is load-bearing; tightening the
    constructor instead would invalidate every [stdin_geometric 0 …] a
    consumer had already built, for the benefit of one lemma.

    ** One counting lemma holds the whole thing up

    [injective_core_list_in_cylinder_length_bound]: a list of records
    with duplicate-free CORES, every core matching the fixed argv, envp
    and file system and carrying standard input of length exactly [n],
    has at most [256 ^ n] elements.  The proof is the obvious argument
    made mechanical.  Such a core is determined by its standard input,
    so the list injects into the length-[n] byte lists; [byte_lists n]
    enumerates those explicitly, with [256 ^ n] entries
    ([byte_lists_length]) and no length-[n] list missing
    ([byte_lists_complete]); and [List.NoDup_incl_length] turns an
    injection into a cardinality bound.

    It is stated first because the rest is arithmetic on top of it.
    The slice of inputs of length exactly [n] holds at most [256 ^ n]
    cores of weight [p_stop * (1 - p_stop) ^ n * (1/256) ^ n] apiece,
    so it carries at most [p_stop * (1 - p_stop) ^ n] — the geometric
    distribution over LENGTHS, with the [256 ^ n] and the [(1/256) ^ n]
    cancelling exactly ([geo_slice_total],
    [stdin_geometric_slice_bound]).

    BOTH constants are pinned as attained, at every [n] and over any
    launch-time environment, which is the difference between a bound
    that is true and one that is right.
    [injective_core_list_in_cylinder_length_bound_attained] exhibits an
    admissible list of exactly [256 ^ n] records — the enumeration
    itself, wrapped — and that needs [byte_lists_nodup], the third fact
    about the enumeration and the only one that is real work
    ([List.NoDup] through a [List.flat_map]: [NoDup_flat_map], since
    Stdlib stops at [List.NoDup_app]).  Cashing it in,
    [stdin_geometric_slice_bound_attained] says that list weighs
    [p_stop * (1 - p_stop) ^ n] exactly, and
    [stdin_geometric_slice_bound_sharp] says no smaller constant is a
    slice bound at all.  Nothing in any of this is computed: the
    enumeration stays a [List.flat_map] term, so the witness at [n]
    costs what the witness at [1] costs.

    Enumerating the 256 bytes is [all_bytes], and it is the one piece
    of this file with nothing to do with measures.  It is here because
    the rule for this file is to consume [BvBase], [FinInput] and
    [Measure] and never edit them; if [BvBase] ever grows a byte
    enumeration of its own, this one should be deleted in favour of it.

    ** The cylinder bound, and why it is proved by enumeration

    [Measure.weight_bound_T] quantifies over lists a task does not
    choose, so what a task needs exported is not "the mass of a
    cylinder" but "no admissible list inside that cylinder sums past
    it".  [stdin_geometric_bound] is that statement: a list whose cores
    all carry standard input EXTENDING a fixed prefix [bs] sums to at
    most [stdin_geometric_cylinder_mass p_stop bs], which is
    [(1 - p_stop) ^ length bs * (1 / 256) ^ length bs].  That number is
    exactly what the geometric weights inside the cylinder add up to,
    so the bound is sharp and not merely convenient: the [p_stop] a
    stopping core spends is the [p_stop] missing from its 256
    continuations, and the induction below is that cancellation, one
    byte at a time.

    Sharp there means a SUPREMUM and not a maximum, and the difference
    matters to anyone reading this for a witness.  For [p_stop < 1] the
    cylinder holds infinitely many cores of positive weight and every
    admissible list is finite, so NO list attains the cylinder mass;
    what a finite list can reach is the mass minus the tail it omits.
    That is a THEOREM here and not a remark —
    [stdin_geometric_mass_not_attained] proves it at the whole space,
    and [stdin_geometric_bound_by_max_length] is the quantitative form
    it comes from (a list reaching no further than length [n] weighs at
    most the partial sum at [n + 1], and
    [stdin_geometric_bound_by_max_length_attained] pins that this is
    tight, so the shortfall is the distribution's and not the proof's).
    That is why the lower witnesses below are to
    [1 - (1 - p_stop) ^ k] rather than to the mass itself
    ([stdin_geometric_mass_lower_witness]), and why the only attainment
    of a whole-space mass pinned here is at the degenerate [p_stop = 1]
    ([geo_point_cd_mass_attained]), where the tail is empty.  The
    LENGTH SLICE is the other story — it is finite, and its bound is
    attained outright ([stdin_geometric_slice_bound_attained]).

    No infinite series is summed.  [cyl_enum bs N] is the list of every
    core in the cylinder whose standard input exceeds [bs] by at most
    [N] bytes; [cyl_enum_sum_le] shows by induction on [N] that its own
    sum stays under the cylinder mass; and the task's list is then
    bounded by it.  That last step is [qsum_core_incl_le] — a
    duplicate-free list of cores sums to at most what any list
    containing it sums to, for a nonnegative weight — and what it does
    NOT require is worth noticing: the containing list need not be
    duplicate-free.  So [cyl_enum] never has to be proved
    [List.NoDup] (it is, but proving it would buy nothing).  The
    removal driving that induction takes out ONE occurrence
    ([core_remove_one]), not all of them, which is precisely what
    dropping the hypothesis costs.  [N] is read off the task's own
    list, as the largest standard-input length occurring in it; that is
    where the finiteness of the obligation's lists is spent, and it is
    the only place it is needed.

    ** Off the environment, and the whole-space certificate

    The membership requirement in [stdin_geometric_bound] cannot be
    dropped — a core matching the environment whose standard input
    leaves the cylinder has positive weight and refutes the weakened
    statement — but it CAN be widened by the one class of cores that is
    harmless: those that miss the fixed launch-time environment
    entirely and therefore weigh nothing.
    [stdin_geometric_bound_or_off_environment] is that widening, and it
    is exported rather than left to consumers because the repair is a
    dozen non-obvious lines (filter on [matches_env], discharge the
    dropped terms through [geo_weight_mismatch], carry [List.NoDup]
    across with [List.NoDup_filter], observe that a survivor took the
    left disjunct).  Both forms stay; neither weakens the other.

    [stdin_geometric_mass_upper] — every admissible list sums to at
    most the declared mass [1] — is then that bound at the EMPTY
    prefix, and the whole content is that the disjunction is
    EXHAUSTIVE there: a core either matches the environment, in which
    case its standard input is [[] ++ itself] and it is in the cylinder
    over [[]], or it does not.  The cylinder mass over the empty prefix
    is [1] because [Qpow] at exponent zero is.  Both halves of the
    certificate pair are proved here for [stdin_geometric]; the lower
    half is the one the next section is about, and per the
    side-condition discussion above it is the half that needs
    [0 < p_stop].

    ** Composition: scaling and mixture

    [cd_scale] multiplies a distribution's weights AND its declared
    mass by a nonnegative factor; [cd_mix2] adds two distributions'
    weights and adds their declared masses; [cd_mix] folds the binary
    mixture over a list, against the zero distribution [cd_zero].
    Between them a task author writes "most of the mass on this
    background, a named few cores on top" without proving anything
    twice.  [0 <= q] is a constructor argument of [cd_scale] for the
    reason [finite_support]'s nonnegativity proof is one, and
    [cd_scale_negative_no_core_distribution] is the refusal mechanized.

    The bounds compose the obvious way and that is the whole export:
    [cd_scale_bound] scales any bound, [cd_mix2_bound] adds two, and
    [cd_mix_bound] adds a list of them.  The bounds are arbitrary [Q]s,
    not necessarily declared masses, so a cylinder bound and a
    length-slice bound compose exactly as a mass certificate does.
    [cd_scale_bound_mass], [cd_mix2_bound_mass] and [cd_mix_bound_mass]
    are those three lemmas at the components' own declared masses, which
    is the case a certificate-carrying task meets.

    Two things about mixtures are worth stating outright because a
    reader may expect otherwise.  First, SUPPORTS MAY OVERLAP, and on a
    shared core the weights ADD — [cd_mix2_overlap_weights_add] pins
    [1 # 2] and [1 # 4] making [3 # 4].  That is the only reading that
    keeps the declared masses in step with the weights, exactly as with
    [finite_support]'s duplicate entries.  Second, and consequently,
    A MIXTURE'S BOUND IS NOT THE LARGER OF ITS COMPONENTS':
    [cd_mix2_bound_is_not_the_max] exhibits a one-element admissible
    list weighing [3 # 4] under a mixture of distributions of mass
    [1 # 2] and [3 # 8], so no max-shaped rule can be true and
    [cd_mix2_bound]'s sum is not a convenience to be sharpened later.

    The LOWER certificates compose too — [cd_scale_bound_lower] and
    [cd_mix2_bound_lower] at any [B], [cd_scale_mass_lower] and
    [cd_mix2_mass_lower] at the declared masses — but not as freely, and
    the asymmetry is real:
    an upper bound holds of every list, so components may be bounded on
    lists chosen independently, while an attainment must be witnessed by
    ONE list attaining both.  So [finite_support_mass_lower_on] is the
    general form BENEATH the canonical witness — attainment at ANY
    duplicate-free list covering the entries — and
    [finite_support_mass_lower_witness] is derived from it rather than
    proved a second time.  [cd_mix2_finite_support_mass_exact] is that
    generality spent: two finite supports, one shared witness, the
    mixture's declared mass attained exactly.

    ** The geometric lower certificate, and where the strictness goes

    [stdin_geometric_mass_lower_certificate]: for every margin [eps]
    there is an admissible list weighing at least [1 - eps].  With
    [stdin_geometric_mass_upper] above it, the declared mass [1] is
    pinned as the LEAST upper bound of the admissible partial sums —
    which is the strongest honest claim available, because for
    [p_stop < 1] no finite list attains [1] at all
    ([stdin_geometric_mass_not_attained], and
    [stdin_geometric_mass_supremum_not_maximum] under the name the
    claim is usually given).  Note which way that cuts: it also refutes
    the swapped reading of the certificate, since ONE list good for
    every [eps] would attain the mass, and none does.

    WHAT THAT DOES NOT SAY, and the misreading is worth naming because
    it is the one a consumer of this library is positioned to make:
    "the declared mass is the least upper bound of the admissible
    partial sums" is NOT "the [b * M] in [Measure.weight_bound_T]
    cannot be lowered for a given fire set".  The sums bounded here
    range over ALL admissible lists; a task's obligation ranges over
    the lists its classifier REJECTS, and nothing here claims the
    witness cores are rejected by anything (see [core_input] — they are
    not even claimed valid).  The supremum over rejected lists may be
    strictly smaller, and a task with a sharper argument about its own
    fire set is entitled to it.

    The witness at a given margin comes from a family, and the family
    is the obvious one: [geo_lower_witness argv envp fs k] holds one
    record per standard input SHORTER than [k] ([short_inputs]), and
    weighs exactly [1 - (1 - p_stop) ^ k]
    ([stdin_geometric_mass_lower_witness]).  That number is the
    geometric series stopped at [k]: the length-[n] slice contributes
    [p_stop * (1 - p_stop) ^ n] exactly — the same cancellation
    [geo_slice_total] does for the slice bound — and the partial sums
    telescope ([geo_prefix_sum_closed]).  Nothing here is approximated
    and nothing needs a side condition: the identity holds at every
    [p_stop] the constructor admits, [0] included.

    THE STRICTNESS IS SPENT IN EXACTLY ONE PLACE, and it is worth
    saying where, because "the lower certificate needs [0 < p_stop]" is
    otherwise a hypothesis a reader has to take on trust.  It is spent
    CHOOSING [k]: to get the tail [(1 - p_stop) ^ k] under a given
    [eps] one needs the tail to shrink at all, and [geo_gap_small]
    chooses [k] past [/ (eps * p_stop)] — a division that exists only
    because [p_stop] is non-zero.  The shrinking itself is
    [geo_gap_bound], [(1 - p) ^ k * (1 + k * p) <= 1], proved by one
    induction whose step is a square being nonnegative
    ([geo_gap_step]), and stated multiplied out so that it needs no
    non-zero side condition of its own.  The [k] exists because no
    rational bounds every [Qnat] ([Qnat_unbounded], on [QArith]'s
    [Qarchimedean]).  No real numbers and no limits are involved
    anywhere: a margin is asked for, and a finite list is produced.

    [geo_gap_small_above] is the same choice with a FLOOR, and it is
    stated because the margin is not always the only claim on a depth: a
    tail only shrinks as its exponent grows ([Qpow_le_exp]), so taking
    the larger of the margin's [k] and whatever floor is asked for keeps
    the bound.  The calibrated mixture's certificate is the caller, and
    the floor there is the one thing that makes its shared witness
    reach the environment its stdin-only component fixes.

    [stdin_geometric_mass_lower_needs_positive] is the other half of
    that account — at [p_stop = 0] EVERY admissible list weighs zero
    while the declared mass stays [1], so the certificate is false
    there, and the upper certificate is not.  An upper bound survives
    the degenerate member; a lower one does not.

    ** A worked distribution, and the recipe for spending it

    The combinators are worth what a task author can do with them, so
    the file ends with one authored distribution written the way a real
    one would be — [worked_cd] — and a [Measure.weight_bound_T] proof
    about it that is nothing but library lemmas applied in order.

    The distribution puts a quarter of its mass on three NAMED cores of
    one task ([worked_entries], a [finite_support]) and three
    quarters on standard input through [stdin_geometric], with argv,
    envp and the file system fixed to the task's own
    ([worked_argv], [worked_envp], [worked_fs]) and a stop weight of
    [1 # 8].  Both components are scaled and then mixed ([cd_scale]
    twice, [cd_mix2] once), so the declared mass is [1 # 4] of one plus
    [3 # 4] of the other and [worked_mass_is_one] is that arithmetic.
    The named cores sit in the SAME launch environment as the
    background, which is what makes this a foreground and not a second
    disjoint distribution: the supports overlap, and on the overlap the
    weights add ([cd_mix2_overlap_weights_add] is the general fact).
    [Worked_D] is the module, built the same way as [Example_D] with no
    arithmetic written at the site.

    THE RECIPE, which is the part a task author copies, is
    [worked_fire_bound] followed by [worked_weight_bound_T_of], in four
    steps:

    - Describe the fire set.  Here it is two cores — the standard
      inputs [[0]] and [[0; 65]] — and it enters as a HYPOTHESIS about
      the classifier ("every rejected record has one of these two
      cores"), because no classifier this file could name exists in
      this development.  A real task discharges that hypothesis from
      its own [Classifier.decides] proof; none of it is the library's
      business.  Note what the hypothesis does not exclude: a
      classifier that rejects NOTHING satisfies it vacuously, and the
      demonstrations below are then true and empty.  That is
      [Measure]'s own documented hole, closed by ascribing
      [Equivalence.IMAGE_WF] to the image, and no distribution — built
      here or by hand — can close it.
    - Bound each component ON THE TASK'S OWN LIST, with the sharpest
      library lemma that applies.  The foreground takes
      [finite_support_bound_subset] at [worked_is_fire], charging the
      [1 # 2] the two fire entries declare rather than the [1] the
      whole support declares.  The background takes
      [stdin_geometric_bound] at the prefix [[0]] — which both fire
      cores extend — charging the CYLINDER mass [7 # 2048] rather than
      the declared [1].
    - Compose: [cd_scale_bound] on each, then [cd_mix2_bound].  That
      the bound lemmas take arbitrary [Q]s rather than declared masses
      is exactly what lets a restricted mass and a cylinder mass meet
      in one application here.
    - Cross to the obligation: [core_sum_cd_lift] rewrites
      [Measure.sum_weights] of the lift into [core_sum], and what
      remains is one comparison of rationals against [b * M].

    The number that comes out is [1045 # 8192], and it is a HYPOTHESIS
    of [worked_weight_bound_T_of] rather than baked into it, so the two
    demonstrations are one proof at two multipliers:
    [worked_weight_bound_T_quarter] at a round [1 # 4], and
    [worked_weight_bound_T_ceiling] at [1045 # 8192] itself, where
    these bounds run out.

    WHAT THE CEILING IS, AND WHAT IT IS NOT.  [worked_fire_ceiling]
    pins that [1045 # 8192] is EXACTLY what the composition yields and
    not a round-up, and [worked_ceiling_slack] pins how much of it is
    real: the fire set's own two records weigh
    [16820371 # 134217728], a shade over 98 per cent of the ceiling and
    STRICTLY below it.  So the route does carry slack, all of it in the
    background half — the cylinder over [[0]] holds every core whose
    standard input begins with [0], and the fire set is two of them.
    What must NOT be read into [worked_weight_bound_T_ceiling] is that
    [1045 # 8192] is the least provable multiplier.  The warning at the
    geometric lower certificate above applies here word for word: a
    task with a sharper argument about its own fire set — the exact sum
    over two cores, say — is entitled to a smaller [b].  The ceiling is
    where the LIBRARY BOUNDS stop, which is a fact about this proof and
    not about the distribution.

    [Classifier] is required, and not imported, for this section alone:
    [Measure.weight_bound_T] quantifies over records its classifier
    [Classifier.rejects], so the demonstration has to name that
    predicate, and qualifying it is cheaper than importing a module
    whose other names this file has no use for.

    ** A second base family: the launch-time environment carries mass

    [stdin_geometric] fixes argv, envp and the file system and varies
    ONLY standard input, so a core whose environment differs from the
    fixed one weighs exactly zero.  The consequence is worth naming
    because it is easy to miss: a fire set living at non-canonical
    environments sits in a NULL set, so a [Measure.weight_bound_T] claim
    about it is satisfied vacuously and measures nothing at all.
    [stdin_envp_geometric] is the family that closes that gap, and
    [stdin_envp_geometric_envp_bites] is the gap stated as a theorem —
    one core, weighed zero by the old family and strictly positively by
    the new one.

    It fixes argv and the file system and spreads what is left over BOTH
    the environment and standard input.  An environment is a list of
    entries and each entry is a byte list, so it is spread by two nested
    memoryless sources: stop opening entries with weight [r], otherwise
    open one and spread ITS bytes the way [stdin_geometric] spreads
    standard input, with stop weight [q_e].  A core with entries
    [e_1 … e_k] and standard input of length [n] weighs

      [r * (1 - r) ^ k * Prod_i geo_point q_e |e_i| * geo_point p_stop n]

    ([envp_geo_weight_closed_form]), and the declared mass is [1].
    Internally the entry factors are carried as one running product,
    [envp_factor], for the reason [geo_mass] carries two powers as one
    ratio: every proof multiplies them together anyway, and the
    factored form is a lemma rather than a rival definition.

    SIX SIDE CONDITIONS, all of the form [0 <= · <= 1], and all
    constructor arguments for the reason [stdin_geometric]'s two are:
    [cd_nonneg] is a field.  None of the three STRICT inequalities is
    demanded, for the reason [0 < p_stop] is not demanded there —
    nothing the constructor needs uses them, and the lower certificate
    that does asks for all three as hypotheses of its own statement.

    ** The weight is a product, so the enumeration is a product

    A core of this family is a PAIR — an environment and a standard
    input — and the weight is one factor per coordinate.  So the two
    coordinates are enumerated apart and recombined
    ([envp_stdin_product]), and the sum over the product is the product
    of the sums ([qsum_envp_stdin_product]).  That identity is
    the only place the coordinates meet, and every bound below it is
    assembled from an envp bound and a standard-input bound proved
    separately.

    The standard-input half is not proved a second time.  [bytes_cyl] is
    [cyl_enum] with the environment forgotten, [cyl_enum_bytes_cyl] says
    the two are the same list under [mkFinCore], and the three sums this
    family charges against ([bytes_cyl_sum_le], [short_inputs_sum],
    [byte_lists_sum]) are the existing [qsum] lemmas transported across
    it.  Those sums range over BYTE LISTS rather than cores, which is
    why [qsum] leaves the element type open: one [fold_right] serves
    both, and only the two lemmas needing decidable equality on the
    element type stay at [FinInput.FinCore].

    The envp half is the new work, and it is one induction —
    [envp_enum_sum_le], the same shape [cyl_enum_sum_le] has, with one
    honest difference.  There the 256 continuations are charged a common
    constant and [256 * (1 # 256)] folds to [1] exactly, so the step is
    lossless.  Here a continuation is charged what its own entry costs
    and the continuations total [1 - (1 - q_e) ^ L] rather than [1]: an
    entry longer than the enumeration's depth is a continuation it
    omits.  The bound stays true because the omitted mass is
    nonnegative, and the slack is real — it is what the lower
    certificate below spends its choice of [L] on.

    THREE DEPTHS are read off the task's own list where
    [stdin_geometric] reads one ([cores_envp_depth],
    [cores_entry_depth], [cores_stdin_depth]): how many entries an
    environment has, how long an entry is, and how long a standard input
    is.  Each is a [List.list_max] over the list, so each exists because
    [Measure.weight_bound_T]'s lists are finite and for no other reason.

    The exports follow [stdin_geometric]'s, and three of the baseline's
    have no analogue here — the three attainment lemmas, accounted for
    two paragraphs down.  Everything else is present name for name:
    [stdin_envp_geometric_bound] over an (environment prefix, standard
    input prefix) cylinder, with the closed form at
    [stdin_envp_geometric_cylinder_mass_closed_form];
    [stdin_envp_geometric_bound_or_off_environment] widening it by the
    cores that miss the fixed argv or file system and therefore weigh
    nothing; [stdin_envp_geometric_mass_upper] as that bound at the two
    empty prefixes; and two bounds that charge the environment NOTHING —
    [stdin_envp_geometric_slice_bound] and
    [stdin_envp_geometric_bound_by_max_length], at exactly the constants
    [stdin_geometric] gives.  That last agreement is deliberate rather
    than a coincidence to be noticed: mixing an envp-varying component
    in must not make a stdin-only argument WORSE, and those two lemmas
    are that claim mechanized.

    NO ATTAINMENT LEMMA ACCOMPANIES ANY OF THE THREE, and the absences
    are deliberate rather than pending.  They are exactly
    [stdin_geometric_slice_bound_attained],
    [stdin_geometric_slice_bound_sharp] and
    [stdin_geometric_bound_by_max_length_attained]; the fourth thing a
    reader might look for, a refutation showing the [List.NoDup]
    hypothesis is load-bearing, IS present
    ([stdin_envp_geometric_bound_needs_nodup]).

    The slice pair goes first because the reason is the simpler one.
    [stdin_geometric]'s length slice is finite, so its constant is
    reached outright and no smaller one is a bound.  A slice of THIS
    family at a fixed standard-input length still holds one core per
    ENVIRONMENT, and for [r < 1] those carry positive weight
    ([stdin_envp_geometric_envp_bites] at one of them), so the counting
    argument does not run and nothing weaker is passed off as it.  The
    comment at [stdin_envp_geometric_slice_bound] says so where a reader
    meets it.

    The max-length absence has a sharper reason and it is worth stating
    rather than lumping in.  That bound charges the environment
    coordinate its WHOLE declared [1], and a finite list collects all of
    that only when all of the environment mass sits on finitely many
    environments — which happens exactly at [r = 1], where
    [envp_geo_weight_collapses_at_one_r] puts every bit of it on the
    empty environment.  For [r < 1] the constant is therefore not merely
    not-provably-tight but LOOSE, and an attainment lemma would be
    false rather than missing.  How loose is not mechanized here, and
    the sentence above is a description of where the slack comes from
    and not a theorem; a task wanting the difference should charge the
    environment through [stdin_envp_geometric_bound] instead, which does
    depend on it.

    ** The envp lower certificate, and where the three strictnesses go

    [stdin_envp_geometric_mass_not_attained] is
    [stdin_geometric_mass_not_attained]'s proof unchanged — the
    shortfall is already there on the standard-input axis, so
    [p_stop < 1] is the only hypothesis it needs — and it is why this
    certificate too has to be an approach rather than an attainment.

    [stdin_envp_geometric_mass_lower_certificate] produces, for every
    margin, a list within it, and each of the three strictnesses buys
    exactly one depth.  [envp_stdin_depths_above] on [r] gives an entry
    count [M]; on [p_stop] it gives a standard-input length [k]; and
    then — LAST, because the target it has to meet mentions [M] — on
    [q_e] it gives an entry length [L] whose tail is under a third of
    the margin divided by [M + 1], so that all [M] entry slots together
    miss at most a third of the margin.  The three thirds compose by
    [Qmargins_three], and the per-slot estimate is
    [Qpow_one_minus_lower] — Bernoulli, the FROM-BELOW counterpart of
    [geo_gap_bound], needed because the environment's shortfall is a
    power of a sum rather than a sum of powers.

    THE DEPTHS AND THE ARITHMETIC ARE STATED APART, and the split is not
    presentational: [envp_stdin_margin_at_depths] takes three depths
    meeting a summed bound and produces the margin, with no strict
    hypothesis anywhere, while [envp_stdin_depths_above] is where all
    three strictnesses are spent.  The calibrated mixture's certificate
    consumes the same two lemmas at DIFFERENT depths — its environment
    depths are floored by a fixed environment as well as by the margin —
    so leaving them fused would have meant proving the arithmetic
    twice.

    The witness family is a product of two duplicate-free enumerations,
    [envps_upto] over environments and [short_inputs] over standard
    inputs, and it weighs their partial sums multiplied
    ([stdin_envp_geometric_mass_lower_witness]).  [envp_enum] is not
    reused for it even though it enumerates the same environments,
    because a witness has to be duplicate-free and that one is not — it
    names the stopping environment at every depth it passes through.
    [envp_prefix_sum] is the environment coordinate's partial sum and is
    deliberately left WITHOUT a closed form: [geo_prefix_sum] telescopes
    because its ratio and its per-term factor are the same number, and
    here they are not, so a closed form would be a quotient carrying a
    side condition.  What the certificate needs is a lower bound, and
    [envp_prefix_sum_lower] gives one with no side condition at all.

    FIVE OF THE SIX ENDPOINTS THE CONSTRUCTOR ADMITS ARE PINNED — it
    admits [p_stop], [r] and [q_e] each at [0] and at [1].  The one left
    unpinned is [p_stop = 1], where the standard-input coordinate
    collapses to the empty input; that is [stdin_geometric]'s own
    degeneracy, documented and exhibited there ([geo_point_cd]) and
    inherited here unchanged rather than newly interesting.  (The
    file-varying family DOES pin its analogue,
    [file_envp_geo_weight_collapses_at_one_p], because there the [p_stop]
    axis is the input file — the coordinate that family exists for.)
    Three of the five
    are endpoints the LOWER CERTIFICATE needs excluded: at [p_stop = 0]
    and at [r = 0] the weight vanishes identically
    ([envp_geo_weight_zero_at_zero_p],
    [envp_geo_weight_zero_at_zero_r]), and
    [stdin_envp_geometric_mass_lower_needs_positive] is the certificate
    refuted at the first of them; at [q_e = 0] the weight does NOT
    vanish, and that degeneracy is the interesting one, because every
    core with a NON-EMPTY environment weighs zero
    ([stdin_envp_geometric_envp_needs_positive_q]) while the empty one
    keeps its weight, so the family goes blind to the launch-time
    environment without going quiet.

    THE OTHER TWO ARE THE ENVIRONMENT COORDINATE'S UPPER ENDPOINTS, and
    what asks for them is not the certificate: it is [envp_point_pos],
    and through it [stdin_envp_geometric_envp_bites] and
    [calibrated_mixture_envp_bites] — the very lemmas that say this
    family improves on [stdin_geometric].  At [r = 1] it does not:
    [envp_geo_weight_collapses_at_one_r] proves the family IS
    [stdin_geometric] over the empty environment, weight for weight at
    every core, with [stdin_envp_geometric_envp_needs_r_below_one] the
    blindness in the shape the [q_e = 0] pin states it.  At [q_e = 1] it
    does not either: [envp_geo_weight_zero_at_one_q] proves that an
    environment holding any NON-EMPTY ENTRY weighs nothing, with
    [stdin_envp_geometric_envp_needs_q_below_one] the [cd_weight] form.
    That last one is stated about an ENTRY and not about the environment
    because the environment [[[]]] still weighs something there, and it
    is the sharpest of the three in practice: a real entry is a
    [NAME=value] string, so at [q_e = 1] the family weighs zero at every
    environment a program will actually be launched with.

    Those last three are the failure modes worth pinning, because they
    are the ones that would go unnoticed: at each the distribution is
    still non-zero, still sums correctly, still declares mass [1]
    honestly — and still measures nothing about the environment, which is
    the only thing it is there to measure.

    ** The calibrated mixture

    [calibrated_mixture] is the composition the second family is
    for, written out at the constants a task configuration would
    use: [1 # 16] on the envp-varying component, [r = 1 # 5] (a mean of
    four entries), [q_e = 1 # 33] (a mean entry length of thirty-two,
    the shape of a [NAME=value] string), and [p_stop] left a parameter
    because it is chosen per binary by format class and nothing here
    depends on the choice.  So are argv, envp and the file system — the
    stdin-only component is the one that FIXES an environment, and which
    one it fixes is the task's canonical environment rather than
    necessarily the empty one, so it is passed in.

    NO NEW COMBINATOR IS INVOLVED, and writing the mixture out is how
    that is checked rather than asserted: [cd_scale] twice and [cd_mix2]
    once is the probabilist's mixture with mass additivity built in, so
    a second base family was the only thing missing.  Both components
    declare [1], so [calibrated_mixture_mass_is_one] is [ring] on four
    numerals; [calibrated_mixture_mass_upper] is the upper half of the
    certificate pair for the MIXTURE and not merely for its components,
    composed out of their two whole-space certificates by
    [cd_scale_bound_mass] and [cd_mix2_bound_mass]; and
    [calibrated_mixture_envp_bites] is the bite inherited — the
    stdin-only component still weighs a non-canonical environment zero,
    and the mixture does not.

    THE LOWER HALF IS NOT THE MIRROR COMPOSITION, and the comment at
    [calibrated_mixture_mass_upper] says why at length: [cd_scale_mass_lower]
    and [cd_mix2_mass_lower] ask each component's mass to be ATTAINED on
    the shared list, and no geometric member attains its mass for
    [p_stop < 1], so their hypotheses are unsatisfiable here rather than
    merely unproved.  A mixture lower certificate has to carry its own
    margin and exhibit one list good for both components; that is a
    proof and not a composition, and it is done in a section of its own.

    BOTH HALVES OF THAT PROOF ARE NAMED, because each is reusable and
    neither is obvious.  [cd_scale_bound_lower] and
    [cd_mix2_bound_lower] are the generic-[B] lower forms that carry a
    margin through a scaling and an addition, the mirror of
    [cd_scale_bound] and [cd_mix2_bound] rather than of the mass forms.
    And the ONE list is the envp-varying component's own witness: it
    contains the stdin-only component's cores as soon as the environment
    depths reach the environment that component fixes
    ([envps_upto_complete]), which is a CONSTRAINT on the depths and not
    a gift, met by choosing them above a floor ([geo_gap_small_above],
    on the strength of [Qpow_le_exp]).
    [stdin_envp_mix2_mass_lower_certificate] is the result, generic in
    the two shares and asking nothing of their sum, and
    [calibrated_mixture_mass_lower_certificate] is the instance at these
    constants — stated against [1] so that it reads beside
    [calibrated_mixture_mass_upper].  Both new hypotheses are pinned:
    [stdin_geometric_on_envp_geo_lower_witness_needs_the_depths] shows
    that short of either depth the shared list carries NONE of the
    stdin-only component's weight, and
    [calibrated_mixture_mass_lower_needs_positive] pins [0 < p_stop] for
    the mixture as the two base families pin it for themselves.

    AND THE CERTIFICATE IS PINNED AS NON-VACUOUS, which a margin lemma
    needs and this file asks of every existence claim it makes.  "Some
    admissible list weighs at least [1 - eps]" is worth what the reasons
    for satisfying it are worth, so
    [calibrated_mixture_mass_lower_certificate_needs_the_stdin_component]
    rules out the reason that would make the shared witness pointless:
    the envp-varying component carries a share of [1 # 16] and no list
    collects more than its declared [1], so at any margin under
    [15 # 16] the rest MUST come from the stdin-only component — whose
    cores are on the list only because [envps_upto_complete] put them
    there.  [qsum_positive_member] then reads a positive weight
    back out of that positive sum, and
    [calibrated_mixture_mass_lower_certificate_names_a_stdin_core]
    composes the two with the certificate itself, so the claim is
    unconditional rather than an implication nothing satisfies: at every
    [p_stop > 0] and every margin under [15 # 16] there is a list within
    the margin NAMING a core the stdin-only component weighs positively.

    THE [15 # 16] IN THAT IS A REAL BOUNDARY and is pinned from both
    sides.  [calibrated_shares_force_stdin_needs_the_threshold] is the
    arithmetic failing at exactly the threshold, where the hypothesis
    holds with equality and the conclusion asks [0 < 0]; and
    [calibrated_mixture_mass_lower_certificate_needs_the_threshold]
    exhibits an actual list past it — the shallowest envp witness, one
    core, carrying NONE of the stdin-only component's weight and meeting
    the certificate's conclusion exactly.  The two are not the same
    statement: at the threshold itself no list realizes the arithmetic
    counterexample, because the envp component's declared mass is never
    attained, so the distribution-level failure needs a strictly larger
    margin than the arithmetic does.

    ** A third base family: the INPUT FILE carries the mass

    Both families above vary STANDARD INPUT, and for a whole class of
    task corpora that is the wrong dimension.  A program that takes a
    file path as its first argument and reads that file — never touching
    fd 0 — is weighed by either family at cores that all carry the SAME
    file system, because both of them fix it.  Every weighted core then
    induces the same program behavior; [Classifier.good_input] and
    [Classifier.agree] are per-input predicates about that behavior, so
    each holds at ALL weighted cores or at none; the reject set is
    all-or-nothing on the support; and the least [b] a
    [Measure.weight_bound_T] claim can be proved at is exactly [0] or
    [1].  A printed bound read as a FRACTION of the input space is then
    reading a measure that cannot take an intermediate value at all.

    [file_geometric] is the family that closes that gap, and
    [file_geometric_fs_bites] is the gap stated as a theorem — one core,
    weighed zero by [stdin_geometric] and strictly positively by this
    one.  It fixes argv, envp and standard input exactly as
    [stdin_geometric] fixes them, fixes a BASE file system and a PATH,
    and spreads what is left over the contents of the file at that path,
    by the same memoryless source: stop after each byte with weight
    [p_stop], otherwise emit one of 256 bytes.  A matching core whose
    file holds [n] bytes weighs [geo_point p_stop n], the same object
    [stdin_geometric] weighs its cores by, and the declared mass is [1].

    ** How a file's contents are addressed inside a core, which is the
    one representation question

    [FinInput.FinCore]'s file-system component is an [Fs.Fs] — a
    path-to-contents association list, kept strictly sorted where
    [Fs.valid_fs] applies — so varying one file's contents needs a way to
    read that file out of a core and a way to put a contents back in.
    Both already exist in [Fs] and neither is added here: [Fs.fs_lookup]
    reads ([fs_file] is that with the absent file reading as the empty
    one, which only decides what is said about cores this family weighs
    zero), and [Fs.fs_set] writes.  [file_core argv envp fs0 pth s] is
    the resulting template — [mkFinCore] with the file-system field built
    as [Fs.fs_set fs0 pth d] — and it is the family's embedding of byte
    lists into cores, with [d] last so that the partial application is
    that embedding.

    "The file system is OTHERWISE CANONICAL" is exactly [fs0] together
    with [Fs.fs_set]: everything else the task's file system holds is
    [fs0]'s and is untouched, and the one varying path is overwritten.
    Two facts make the representation carry the whole construction, and
    both hold with NO hypothesis on [fs0] — not sortedness, not that
    [pth] is already present: the coordinate reads back off the template
    ([fs_file_file_core], from [fs_lookup_set]), and the template is
    INJECTIVE in the contents ([file_core_inj]).  The first is what lets
    the weight's decidable test be the same one-equation shape
    [geo_weight]'s is; the second is what makes the length slice really
    hold [256 ^ n] distinct cores and every witness family as long as it
    claims.  A representation losing either would have forced a weaker
    family, and neither is assumed — they are proved.

    ** Almost nothing is proved a second time

    The varying coordinate is a BYTE LIST, exactly as standard input is,
    so every byte-list-level fact this family needs already exists: it is
    the material [bytes_cyl], [short_inputs] and [byte_lists] enumerate
    and [bytes_cyl_sum_le], [short_inputs_sum] and [byte_lists_sum]
    evaluate — written over byte lists rather than cores for the
    envp-varying family, and reused here for that reason.  One lemma
    bridges them to this family's cores, [qsum_file_block]: a
    block of cores obtained by mapping the template over a list of byte
    lists weighs what that list weighs.  No enumeration, no cancellation
    and no telescoping identity is written again, and no [Fixpoint] is
    added at all.

    The exports follow [stdin_geometric]'s name for name:
    [file_geometric_bound] over a file-contents-prefix cylinder with
    [file_geometric_cylinder_mass_closed_form];
    [file_geometric_bound_or_off_environment] widening it by the cores
    that miss the fixed environment and therefore weigh nothing;
    [file_geometric_mass_upper] as that bound at the empty prefix;
    [file_geometric_slice_bound] with BOTH attainment lemmas
    ([file_geometric_slice_bound_attained],
    [file_geometric_slice_bound_sharp]), which the envp-varying family
    could not have because its slices are infinite and this family's are
    not; [file_geometric_bound_by_max_length] with its own attainment;
    [file_geometric_mass_not_attained] and
    [file_geometric_mass_supremum_not_maximum]; and
    [file_geometric_mass_lower_certificate], whose [0 < p_stop] is spent
    in [geo_gap_small] and nowhere else.

    BOTH DEGENERATE ENDPOINTS ARE PINNED, and they fail in the two
    different ways this file has names for.  At [p_stop = 0] the weight
    vanishes identically ([file_geo_weight_zero_at_zero_p]) and the lower
    certificate is refuted ([file_geometric_mass_lower_needs_positive]) —
    the [envp_geo_weight_zero_at_zero_p] shape.  At [p_stop = 1] the
    weight does NOT vanish and the mass is even attained
    ([file_point_cd_mass_attained]), but every core whose input file is
    non-empty weighs zero ([file_geo_weight_collapses_at_one_p],
    [file_geometric_needs_p_below_one]): the family goes blind to the
    file contents without going quiet, which is the [q_e = 0] shape and
    the failure mode that would go unnoticed.  [List.NoDup] is pinned as
    load-bearing at [file_geometric_bound_needs_nodup].

    ** A fourth base family: the input file AND the environment

    [file_envp_geometric] is [stdin_envp_geometric] with its
    standard-input factor replaced by [file_geometric]'s, and that is the
    whole difference: the envp coordinate is the same
    [envp_point r q_e], spread by the same two nested memoryless sources,
    and [geo_point p_stop] is applied to the length of the input file
    rather than of standard input.  A core with entries [e_1 … e_k] and
    an input file of [n] bytes weighs

      [r * (1 - r) ^ k * Prod_i geo_point q_e |e_i| * geo_point p_stop n]

    ([file_envp_geo_weight_closed_form]), and the declared mass is [1].

    IT IS A PRODUCT AND NOT A MIXTURE, and the distinction is the reason
    it exists rather than being composed out of the two families that
    precede it.  [cd_mix2] of [file_geometric] and
    [stdin_envp_geometric] would put weight on cores varying the file at
    the canonical environment and on cores varying the environment at the
    canonical file, and NONE on a core varying both — a defect reachable
    only from a non-canonical environment together with a particular
    input file would still sit in a null set.  This family is the product
    measure, so it does not.  It is kept ALONGSIDE [file_geometric] and
    not in place of it because the envp coordinate costs a factor and
    buys nothing for a program that never consults the environment, and
    many programs do not.

    Nothing is proved a third time.  The envp half is
    [envp_enum_sum_le], [envps_upto], [envp_prefix_sum] and
    [envp_prefix_sum_lower] unchanged; the file half is the byte-list
    sums [file_geometric] already reuses; the two round trips are
    [file_geometric]'s ([fs_file_file_envp_core] is [fs_file_file_core],
    and the
    injectivity both the block and the disjointness arguments spend is
    [file_core_inj]).  What is new is the recombination
    ([file_envp_product], [qsum_file_envp_product]) and the
    exports, which follow [stdin_envp_geometric]'s name for name:
    [file_envp_geometric_bound] over an (environment prefix, file-contents
    prefix) cylinder with its closed form;
    [file_envp_geometric_bound_or_off_environment];
    [file_envp_geometric_mass_upper] at the two empty prefixes;
    [file_envp_geometric_slice_bound] and
    [file_envp_geometric_bound_by_max_length], which charge the
    environment NOTHING and land on exactly [file_geometric]'s constants
    — that agreement is deliberate, since mixing an envp-varying
    component in must not make a file-only argument worse;
    [file_envp_geometric_mass_not_attained]; and
    [file_envp_geometric_mass_lower_certificate], whose three
    strictnesses buy the three depths in the order
    [stdin_envp_geometric_mass_lower_certificate] explains.

    NO ATTAINMENT ACCOMPANIES EITHER OF THE TWO ENVIRONMENT-FREE BOUNDS,
    and the two absences have the two different reasons the envp-varying
    family's have.  A slice at a fixed file length still holds one core
    per ENVIRONMENT, infinitely many of them carrying positive weight for
    [r < 1], so the counting argument does not run.  The max-length bound
    charges the environment its whole declared [1], which a finite list
    collects only at [r = 1] ([file_envp_geo_weight_collapses_at_one_r]),
    so for [r < 1] that constant is not merely not-provably-tight but
    LOOSE, and an attainment lemma would be false rather than missing.

    ALL SIX DEGENERATE MEMBERS ARE PINNED — every endpoint the
    constructor admits, one more than the envp-varying family's five,
    because [p_stop = 1] is a real degeneracy HERE where it was only
    [stdin_geometric]'s documented collapse there: this family's
    [p_stop] axis is the input file, which is the coordinate it exists
    for.  [p_stop = 0] and [r = 0] vanish identically
    and refute the lower certificate; [q_e = 0], [q_e = 1], [r = 1] and
    [p_stop = 1] do not vanish and are the dangerous ones — the first
    three make the family blind to the environment (at [r = 1] totally,
    since it IS [file_geometric] over the empty environment, weight for
    weight; at [q_e = 1] at every environment holding a non-empty ENTRY,
    which is every environment a program is really launched with)
    and [p_stop = 1] makes it blind to the input file.  [List.NoDup] is
    pinned as load-bearing at
    [file_envp_geometric_bound_needs_nodup].

    ** A further base family: the input file BEHIND A FIXED HEADER

    [file_geometric_prefix] is [file_geometric] with the first
    [length hdr] bytes of the file FIXED to a header the task names and
    the geometric source applied to what follows.  It exists because a
    driver that checks a header before it hands anything to the library
    under test — a length word, a magic number — rejects almost every
    file the whole-file family weighs: the header's bytes are uniform
    there too, so only the sliver of files whose random header happens
    to parse reaches the library, and a bound over the whole-file family
    prices the driver's reject path.  There is no conditioning
    combinator, and the header cylinder's own mass is too small to serve
    as a scale.  A matching core whose file is [hdr ++ t] weighs
    [geo_point p_stop (length t)]; a matching core whose file does not
    begin with [hdr] weighs zero ([file_prefix_geo_weight_off_header_zero],
    and [file_geometric_prefix_off_header_zero] together with the
    declared mass, which stays [1]); the declared mass is the payload's
    geometric mass, normalised.

    It is the whole-file family through the injective map
    [t |-> hdr ++ t] ([file_prefix_core], injective by [file_core_inj]
    and [List.app_inv_head]), and nothing about it is proved a third
    time: the block identity carries over through [qsum_map]
    ([qsum_file_prefix_block]), every byte-list sum is reused as it
    stands, and what is new is the weight's rewrite rules, the shifted
    block identity, and the depth step of the cylinder bound with
    [cores_file_depth] less [length hdr] ([cores_file_prefix_depth]).
    The exports mirror [file_geometric]'s name for name with [_prefix]:
    [file_geometric_prefix_bound] over a PAYLOAD-prefix cylinder
    ([in_file_prefix_cylinder], which is [in_file_cylinder] over
    [hdr ++ bs] by [in_file_prefix_cylinder_iff]) at the whole-file
    family's mass for the same payload prefix;
    [file_geometric_prefix_bound_or_off_environment], where "off" now
    also means "misses the header" ([matches_file_prefix_env]);
    [file_geometric_prefix_mass_upper]; the payload-length slice with
    both attainments; [file_geometric_prefix_bound_by_max_length], whose
    hypothesis is on the FILE's length with the shift done inside;
    [file_geometric_prefix_mass_not_attained] and the supremum reading;
    and [file_geometric_prefix_mass_lower_certificate].

    Two facts are the spec of record's own.  At the EMPTY header the
    family IS [file_geometric], pointwise and by conversion
    ([file_prefix_geo_weight_nil], [file_geometric_prefix_nil_pointwise]):
    a generalisation, not a rival.  And THE HEADER BITES
    ([file_geometric_prefix_header_bites]): the empty-file core the
    whole-file family weighs positively weighs zero here, the
    exact-header core weighs positively, and the mass is [1].  Both
    degenerate endpoints are pinned as for the whole-file family, with
    the [p_stop = 1] collapse now onto the exact-header file
    ([file_prefix_geo_weight_collapses_at_one_p]); [List.NoDup] is
    load-bearing at [file_geometric_prefix_bound_needs_nodup].  The
    alphabet-restricted variant — bytes i.i.d. over a fixed subset
    rather than all 256 — is a separate family, below.

    ** The same family over a fixed ALPHABET

    [file_geometric_prefix_over] is [file_geometric_prefix] with the
    payload's bytes spread uniformly over a fixed subset [alpha] of the
    bytes rather than over all of them: a text-consuming program wants
    printable input, and under the all-bytes law almost every payload
    holds a control byte.  A matching core whose file is [hdr ++ t] with
    every byte of [t] in the alphabet weighs
    [p_stop * ((1 - p_stop) * alpha_ratio alpha) ^ length t], where the
    ratio is one over the alphabet's size; a payload with any byte
    outside the alphabet weighs zero
    ([file_prefix_over_geo_weight_off_alphabet],
    [file_geometric_prefix_over_off_alphabet_zero] with the mass, which
    stays [1]); the declared mass is [1].  The alphabet's facts —
    duplicate-free, non-empty — are constructor arguments, for the
    reason the side conditions on [p_stop] are.

    NOTHING ABOVE THE ALPHABET SECTION CHANGES.  The enumerations and
    sums the all-bytes families use ([byte_lists], [short_inputs],
    [bytes_cyl], [geo_mass]) are stated once more over an alphabet
    ([alpha_lists], [alpha_short_inputs], [alpha_cyl],
    [alpha_geo_mass]), with the alphabet's facts where the all-bytes
    enumeration had its own, and completeness turned into the payload
    predicate [alpha_only]; the cancellation that bounds a cylinder
    ([alpha_cyl_sum_le]) and closes a slice ([alpha_slice_total]) spend
    "non-empty" exactly once each, in [alpha_ratio_cancel].  The
    all-bytes objects are the instance at [alpha = all_bytes], proved
    ([alpha_lists_all_bytes], [alpha_short_inputs_all_bytes],
    [alpha_cyl_all_bytes], [alpha_geo_mass_all_bytes]), and so is the
    family: at [all_bytes] it is [file_geometric_prefix] pointwise
    ([file_geometric_prefix_over_all_bytes_pointwise]).  The exports
    mirror [file_geometric_prefix]'s name for name with [_over], on the
    SAME cylinder predicate — a core in the cylinder whose payload
    leaves the alphabet weighs zero rather than being excluded — with
    one more step in each bound: the list is first filtered to the cores
    that weigh anything ([matches_file_prefix_over_env]).  Both slice
    statements, payload-shaped and file-length-shaped
    ([file_geometric_prefix_over_slice_bound_by_file_length], beside
    [file_geometric_prefix_slice_bound_by_file_length]), carry no
    premise on the alphabet.  THE ALPHABET BITES
    ([file_geometric_prefix_over_alphabet_bites]): the off-alphabet core
    the all-bytes header family weighs positively weighs zero here, the
    in-alphabet core weighs positively, and the mass is [1].  Both
    degenerate endpoints and [List.NoDup] are pinned as for the
    all-bytes header family.

    ** The argv/path coupling, which is the caller's obligation and not
    the family's property

    The file families take [argv] and [pth] as INDEPENDENT parameters,
    and a typical driver passes the varied file's path AS
    an argument.  So a task must pass the same path in both places, and
    nothing in the constructions makes it.  This is the one obligation a
    caller can get silently wrong, and getting it wrong reintroduces
    exactly the collapse these families exist to remove: the
    distribution varies a file the program never opens, while declaring
    mass [1], satisfying both halves of the certificate pair, and putting
    distinct positive weights on distinct file contents.  Nothing above
    this section distinguishes such an instance from a well-configured
    one.

    The last section of the file closes that three ways, none of them a
    comment.  [argv_names_path] NAMES the obligation — the path occurs
    somewhere in the fixed argv — and says what it is not: the real
    obligation is that the PROGRAM opens the file, which is a claim about
    the program and is no more mechanizable here than the worked
    demonstration's hypothesis about its classifier.  It is the part a
    library can check, and it catches the mistake a task author actually
    makes.

    [file_geometric_argv1], [file_envp_geometric_argv1],
    [file_geometric_prefix_argv1] and [file_geometric_prefix_over_argv1]
    make the
    mismatch UNREPRESENTABLE for the common driver shape: they
    take a program name and a path, build the argv out of the path
    ([path_argv]), and pass it to exactly one slot, so the two cannot
    disagree.  They are offered ALONGSIDE the general constructors rather
    than replacing them, because not every program takes its path at
    argv[1] — one may read a path out of a config file, or take it after
    a flag — and a task with a different shape uses the general
    constructor and discharges [argv_names_path] itself.

    And the collapse is PINNED rather than described.  [Fs.fs_set]
    touches one key and no other ([fs_lookup_set_other], again with no
    hypothesis on the file system), so every core either family weighs
    holds, at every path other than the one it varies, exactly the base
    file system's contents ([file_geo_weight_blind_off_path],
    [file_envp_geo_weight_blind_off_path]) and any two weighted cores
    therefore agree there ([file_geometric_blind_off_path],
    [file_envp_geometric_blind_off_path]).
    [file_geometric_needs_argv_to_name_the_path] and its envp counterpart
    exhibit the misconfigured instance itself: the obligation fails, two
    cores with different file contents both weigh something — so nothing
    about the instance looks degenerate — and yet at the path argv names
    those two cores hold the same bytes, so a program reading its
    argument cannot tell them apart.

    ** A further base family: FULL SUPPORT, every core carries mass

    Each of the families above weighs ZERO off one fixed template,
    and the warning at the top of the envp section applies at each of
    those null sets.  What a task needs here is full
    support — a classifier may misbehave freely where the weight is
    zero, so every argv, envp, file-system and standard-input
    combination must weigh something — and no family above has it.
    [full_support_base] is the one that does ([full_support_base_positive]
    at any eight rates strictly inside [(0, 1)], with
    [full_support_base_bites] the gap against every sibling on one
    core).  It is the product of four independent laws, one per field
    of [FinInput.FinCore]: [strings_point] — which IS [envp_point] under
    a field-neutral name — on argv and on envp at their own rates,
    [fs_point] on the file system (the same entry-count shell around a
    PAIR of byte-geometric factors per entry, path and contents), and
    [geo_point] on standard input.  There is no template and no
    [decide]; [base_weight_mk] is a computation.

    The enumeration behind every bound is the four-fold product
    [full_support_product], whose sum is the product of the four sums
    ([qsum_full_support_product]); three of the coordinates' sums are
    bounded by lemmas the earlier families already proved, and the
    file-system coordinate gets [fs_enum] and [fs_enum_sum_le], which
    are [envp_enum] and [envp_enum_sum_le] with a pair in the slot.
    [base_weight_product_bound] is the engine: four enumerations, four
    one-coordinate bounds, one product.  The exports follow the
    siblings' name for name — [full_support_base_bound] over a
    four-prefix cylinder with [full_support_base_cylinder_mass_closed_form],
    [full_support_base_mass_upper] at the four empty prefixes,
    [full_support_base_slice_bound] and
    [full_support_base_bound_by_max_length] on standard input,
    [full_support_base_mass_not_attained] and
    [full_support_base_mass_supremum_not_maximum], and
    [full_support_base_mass_lower_certificate], whose eight strictnesses
    buy eight depths.  What is new is the MARGINALS: a fire set
    described by ONE coordinate is charged that coordinate's weight and
    the other three are charged [1] ([full_support_base_argv_bound],
    [full_support_base_envp_bound], [full_support_base_fs_bound]), and a
    fire set described by the contents of ONE FILE — the entry count
    and every other entry free — is charged that prefix's cylinder mass
    through a weight-preserving injection ([core_strip],
    [full_support_base_file_bound]).  Their composition,
    [full_support_base_argv_file_bound], is what lets a task price a
    content-described fire set under the shipping mixture
    [cd_mix2 (cd_scale s structured) (cd_scale (1 - s) base)].

    The seam, decided the way this file decides validity everywhere:
    [fs_point] weighs every list of pairs, sorted or not, and the
    declared [1] is the mass of the LAW, not the mass reachable by
    [Fs.valid_fs] file systems.  The family's own header says why.

    ** Why powers are defined again

    [Qpow] is [QArith]'s [Qpower] with a [nat] exponent, and the reason
    is not the one it would be natural to guess.  It is NOT that
    [Qpower]'s algebra carries side conditions where [Qpow]'s does not:
    [Qmult_power] and [Qpower_1], the exact counterparts of [Qpow_mult]
    and [Qpow_1], are UNCONDITIONAL in Stdlib's [Qpower] module, base
    zero included.  Those two do not distinguish the operators at all.

    The reason is the other pair, the one every induction below
    actually rewrites with: [Qpow_0] and [Qpow_succ].  For a
    [nat]-indexed [Fixpoint] they hold BY CONVERSION.  Their [Qpower]
    counterpart — peeling one factor off [a ^ (1 + n)] — is reachable
    only through [Qpower_plus], since a [Z] exponent may be negative
    and a negative exponent is an inverse; and [Qpower_plus] demands a
    non-zero BASE.  The base here is [(1 - p_stop) * (1 # 256)], which
    is ZERO at [p_stop = 1] — the point mass on the empty standard
    input, a member of the family in good standing and the one
    [stdin_geometric_bound_needs_nodup] rigs its refutation with.  So
    the depth induction in [cyl_enum_sum_le] would carry a case split
    on [p_stop = 1] at every step, to prove nothing.  [Qnat] is
    [inject_Z] after [Z.of_nat], named so that "there are [256 ^ n] of
    them" is a rational that can multiply a weight.

    ** Conventions inherited from [Measure]

    No LIBRARY lemma decides a [Q] relation by computation: the
    combinators' BOUNDS are STATED as [Qle], and the two [Qeq]s that say
    a sum EQUALS a declared mass ([finite_support_mass_exact] and
    [cd_mix2_finite_support_mass_exact]) are DERIVED from [Qle] both
    ways, by [Qle_antisym] on a bound and a witness.  The other [Qeq]s
    in the file are equations by nature rather than bounds in disguise —
    arithmetic identities like [geo_slice_total] and
    [geo_prefix_sum_closed], and the exact value a witness weighs
    ([stdin_geometric_mass_lower_witness]) — and none of them is decided
    by computing either, on an open term or at all.
    Computation appears only in the bites, and only on operands this
    file wrote out as literals, in two forms.  One is a [Qle_bool]
    BOOLEAN reduced to [true] or [false] — the exception [Measure]'s
    header documents and takes, and the form
    [entries_nonneg_of_forallb] hands to a task author.  The other is a
    closed [Qeq] between literal rationals, in the arithmetic bites; that
    is NOT the pattern [Measure] warns against, which is
    [vm_compute; reflexivity] on a LEIBNIZ [eq] over [Q] — a test that
    can succeed for one representative of a value and fail for another.
    [Qeq] IS the cross-multiplied [Z] equation, so computing it is
    exactly the right decision procedure and gives the same answer for
    every representative.  Neither form is ever applied to an open or
    author-supplied term.

    [List.NoDup] is written qualified throughout, for the reason
    [Measure]'s header gives: [stdpp], in scope here through [BvBase],
    shadows the standard library's [NoDup] with one of its own. *)

From Stdlib Require Import ZArith NArith List QArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State StackLayout.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput Measure.
From LinuxProcessSemantics.EquivalenceDefinition Require Classifier GatedSize.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Arithmetic [QArith] does not ship
   ========================================================================= *)

(** A sum of nonnegative rationals is nonnegative.  [QArith] ships the
    MULTIPLICATIVE version of this ([Qmult_le_0_compat]) and not the
    additive one, so it is assembled here out of [Qplus_le_compat] and
    [Qplus_0_l], once, rather than open-coded at each use.  It says
    nothing about this development and is not named after it; the name
    is deliberately not [Qplus_le_0_compat], so that nothing here
    shadows a lemma [QArith] might later add under the name its own
    convention would pick. *)
Lemma Qplus_nonneg : forall a b, (0 <= a)%Q -> (0 <= b)%Q -> (0 <= a + b)%Q.
Proof.
  intros a b Ha Hb.
  apply (Qle_trans _ (0 + b)%Q).
  - rewrite Qplus_0_l. exact Hb.
  - apply Qplus_le_compat; [exact Ha | apply Qle_refl].
Qed.

(** Two numeral facts, named.  Both hold by conversion — [Qle] unfolds
    to a comparison of integers, and on literal numerators and
    denominators that comparison reduces — and both appear inside the
    induction steps of most of the arithmetic below, where a bare
    [reflexivity] in the middle of a [Qle] proof would read as a
    mistake.  Neither is the pattern [Measure]'s header warns against:
    the operands are numerals this file wrote out, and nothing
    author-supplied is ever decided by computation. *)
Lemma Qle_0_1 : (0 <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Lemma Qle_0_inv_256 : (0 <= 1 # 256)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

(** An equation read as an inequality.  [ring] closes [Qeq] goals and
    not [Qle] ones, so each place below where the two sides of an
    inequality are in fact equal goes through this rather than
    inlining the same two lines. *)
Lemma Qle_of_Qeq : forall a b, (a == b)%Q -> (a <= b)%Q.
Proof. intros a b H. rewrite H. apply Qle_refl. Qed.

(* =========================================================================
   Powers with a natural exponent
   ========================================================================= *)

(** [QArith]'s [Qpower] takes a [Z] exponent, and the cost is NOT
    where one would guess.  The multiplicative algebra is fine there:
    Stdlib's [Qpower] module proves [Qmult_power] and [Qpower_1] — the
    counterparts of [Qpow_mult] and [Qpow_1] below — with no side
    condition whatever, base zero included.

    The cost is on the two rules every induction in this file rewrites
    with, [Qpow_0] and [Qpow_succ].  Here they hold BY CONVERSION,
    because the recursion is on a [nat].  Peeling one factor off
    [a ^ (1 + n)] for a [Z] exponent goes through [Qpower_plus], which
    demands a NON-ZERO BASE — a [Z] exponent may be negative, and a
    negative exponent is an inverse.  The base raised to powers here is
    [(1 - p_stop) * (1 # 256)], and it is ZERO at [p_stop = 1], the
    point mass on the empty standard input and a member of the
    geometric family in good standing.  The depth induction in
    [cyl_enum_sum_le] would therefore carry a case split on
    [p_stop = 1] through every step, to prove nothing.

    The name is [Qpow] and not [Qpower_nat] so that nothing here
    shadows or is confused with the [QArith] operator, which this file
    neither imports nor uses. *)
Fixpoint Qpow (q : Q) (n : nat) : Q :=
  match n with
  | O => 1%Q
  | S n' => (q * Qpow q n')%Q
  end.

(** The two computation rules, as rewrite rules: both hold by
    conversion, and are stated so that no proof below has to [cbn] a
    goal it only wants to unfold in one place. *)
Lemma Qpow_0 : forall q, Qpow q 0 = 1%Q.
Proof. reflexivity. Qed.

Lemma Qpow_succ : forall q n, Qpow q (S n) = (q * Qpow q n)%Q.
Proof. reflexivity. Qed.

(** [Qpow] respects [Qeq] in its base.  No [Proper] instance is
    declared, for the reason given at [qsum_ext]: it is
    applied where it is wanted rather than found by [rewrite].  The
    induction step rewrites with the hypothesis BEFORE the base
    equation, because rewriting the base first would ask [rewrite] to
    go under [Qpow], which without a [Proper] instance it cannot. *)
Lemma Qpow_Qeq : forall q1 q2 n, (q1 == q2)%Q -> (Qpow q1 n == Qpow q2 n)%Q.
Proof.
  intros q1 q2 n Heq. induction n as [| n IH]; [reflexivity |].
  rewrite !Qpow_succ, IH, Heq. reflexivity.
Qed.

(** A nonnegative base has nonnegative powers — the fact that makes
    every geometric weight below nonnegative. *)
Lemma Qpow_nonneg : forall q n, (0 <= q)%Q -> (0 <= Qpow q n)%Q.
Proof.
  intros q n Hq. induction n as [| n IH]; [exact Qle_0_1 |].
  rewrite Qpow_succ. apply Qmult_le_0_compat; assumption.
Qed.

(** ... and a STRICTLY positive base has strictly positive powers.  The
    two are stated separately rather than one being derived from the
    other because they are used for opposite purposes: nonnegativity
    makes weights admissible, and this one is what makes a tail
    NON-ZERO — it is the whole content of
    [stdin_geometric_mass_not_attained], where the omitted tail being
    positive is exactly why a finite list falls short. *)
Lemma Qpow_pos : forall q n, (0 < q)%Q -> (0 < Qpow q n)%Q.
Proof.
  intros q n Hq. induction n as [| n IH]; [reflexivity |].
  rewrite Qpow_succ. apply Qmult_lt_0_compat; assumption.
Qed.

(** Powers distribute over products, with no side condition.  This is
    the lemma the whole cancellation rests on: it splits the ratio
    [(1 - p_stop) * (1 # 256)] into the two powers the plan's closed
    form quotes, and it recombines [256 ^ n] with [(1/256) ^ n] into
    [1 ^ n]. *)
Lemma Qpow_mult : forall a b n, (Qpow (a * b) n == Qpow a n * Qpow b n)%Q.
Proof.
  intros a b n. induction n as [| n IH]; [rewrite !Qpow_0; ring |].
  rewrite !Qpow_succ, IH. ring.
Qed.

Lemma Qpow_1 : forall n, (Qpow 1 n == 1)%Q.
Proof.
  induction n as [| n IH]; [reflexivity |].
  rewrite Qpow_succ, IH. ring.
Qed.

(* =========================================================================
   Counting, as a rational
   ========================================================================= *)

(** The rational named by a natural number.  The counting lemma below
    bounds the LENGTH of a list, and the bound it feeds is a sum of
    equal weights; getting from one to the other means multiplying a
    weight by a count, so the count has to become a [Q].  [inject_Z] of
    [Z.of_nat] is that, and the four facts below are all that is ever
    asked of it. *)
Definition Qnat (n : nat) : Q := inject_Z (Z.of_nat n).

Lemma Qnat_0 : (Qnat 0 == 0)%Q.
Proof. reflexivity. Qed.

Lemma Qnat_succ : forall n, (Qnat (S n) == 1 + Qnat n)%Q.
Proof.
  intros n. unfold Qnat. rewrite Nat2Z.inj_succ. unfold Z.succ.
  rewrite inject_Z_plus. ring.
Qed.

Lemma Qnat_mult : forall m n, (Qnat (m * n) == Qnat m * Qnat n)%Q.
Proof.
  intros m n. unfold Qnat. rewrite Nat2Z.inj_mul, inject_Z_mult. reflexivity.
Qed.

Lemma Qnat_nonneg : forall n, (0 <= Qnat n)%Q.
Proof.
  intros n. unfold Qnat.
  change 0%Q with (inject_Z 0). rewrite <- Zle_Qle. apply Nat2Z.is_nonneg.
Qed.

(** Counting is monotone, which is how "the list is no longer than
    [256 ^ n]" becomes "its sum is no more than [256 ^ n] weights". *)
Lemma Qnat_le : forall m n, (m <= n)%nat -> (Qnat m <= Qnat n)%Q.
Proof.
  intros m n H. unfold Qnat. rewrite <- Zle_Qle. apply Nat2Z.inj_le. exact H.
Qed.

(** The one numeral that matters, and its powers.  [Qnat 256 == 256 # 1]
    is conversion in [Z] — [Z.of_nat] on a literal — and not a decision
    about [Q]: the two sides are the same rational written twice. *)
Lemma Qnat_256 : (Qnat 256 == 256 # 1)%Q.
Proof. reflexivity. Qed.

Lemma Qnat_pow_256 : forall n, (Qnat (256 ^ n) == Qpow (256 # 1) n)%Q.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [Nat.pow]. rewrite Qnat_mult, Qnat_256, Qpow_succ, IH. reflexivity.
Qed.

(* =========================================================================
   Deciding equality of cores
   ========================================================================= *)

(** [FinInput.FinCore] has decidable equality, and every combinator that
    sums entries per core needs it: "the weight of [c] is the total of
    the entries naming [c]" is not a definition until "naming [c]" can
    be decided.

    It is derivable rather than assumed because every field is built
    from [BvBase.byte] and lists: [FinInput.core_argv] and
    [FinInput.core_envp] are [list (list byte)],
    [FinInput.core_stdin] is [list byte], and [Fs.Fs] is by definition
    [list (Fs.path * list byte)].  [stdpp]'s [solve_decision] assembles
    the instance from its own [bv] and [list] instances.  Declared with
    [Defined] rather than [Qed] because the examples below reduce
    [decide] on closed cores. *)
#[global] Instance FinCore_eq_dec : EqDecision FinCore.
Proof. solve_decision. Defined.

(* =========================================================================
   The author-facing packaging
   ========================================================================= *)

(** A weight on CORES together with the total it declares.

    Three fields and no more: the weight, the declared mass [M] that
    [Measure.weight_bound_T] multiplies by [b], and the nonnegativity
    the lift needs to discharge [Measure.DISTRIBUTION]'s [w_nonneg].
    Nonnegativity is a FIELD rather than a side condition on each lemma
    so that it travels with the object: a [CoreDistribution] in hand is
    already known to be usable, and a would-be distribution that fails
    it cannot be built (see [negative_entries_no_core_distribution]).

    There is deliberately no field relating [cd_mass] to [cd_weight].
    [Measure]'s header is explicit that [M] is trusted metadata with no
    normalization obligation, and inventing one here would be this
    library claiming an authority over the trusted layer that it does
    not have.  What is offered instead is the certificate pair —
    [finite_support_mass_upper] and [finite_support_mass_lower_witness]
    — which a task may prove and print, per combinator. *)
Record CoreDistribution := mkCoreDistribution {
  cd_weight : FinCore -> Q;
  cd_mass   : Q;
  cd_nonneg : forall c, (0 <= cd_weight c)%Q
}.

(** The weight on RECORDS that a [CoreDistribution] denotes: read the
    core, weigh it.  This is the only way a weight built here reaches
    [Measure.DISTRIBUTION], and it is what makes [w_core_blind] a
    theorem about the library rather than an obligation per task. *)
Definition cd_lift (D : CoreDistribution) : FinProcInput -> Q :=
  fun f => cd_weight D (fin_core f).

(** [Measure.DISTRIBUTION]'s [w_nonneg], for every lift: the record's
    own field, at the record's core. *)
Lemma cd_lift_nonneg : forall D f, (0 <= cd_lift D f)%Q.
Proof. intros D f. apply cd_nonneg. Qed.

(** [Measure.DISTRIBUTION]'s [w_core_blind], for every lift.  Equal
    cores are the same argument to the same function, so the values are
    [eq] and the [Qeq] follows; the rewrite is the whole proof.  This is
    the design move of the file cashed in — see the header. *)
Lemma cd_lift_core_blind : forall D f g,
  fin_core f = fin_core g -> (cd_lift D f == cd_lift D g)%Q.
Proof. intros D f g Heq. unfold cd_lift. rewrite Heq. reflexivity. Qed.

(* =========================================================================
   The sums the bounds are stated on
   ========================================================================= *)

(** [Measure.sum_weights] of a lifted weight.  Definitionally the
    measure layer's own sum — see [core_sum_sum_weights] and
    [core_sum_cd_lift] — so a bound proved about [core_sum] is a bound
    about the quantity [Measure.weight_bound_T] compares against
    [b * M], with nothing in between. *)
Definition core_sum (w : FinCore -> Q) (l : list FinProcInput) : Q :=
  sum_weights (fun f => w (fin_core f)) l.

(** The bridge to [Measure.sum_weights], by conversion. *)
Lemma core_sum_sum_weights : forall w l,
  core_sum w l = sum_weights (fun f => w (fin_core f)) l.
Proof. reflexivity. Qed.

(** The bridge in the form a consumer meets it: the sum
    [Measure.weight_bound_T] takes of a lifted distribution IS the
    library's sum of its core weight. *)
Lemma core_sum_cd_lift : forall D l,
  core_sum (cd_weight D) l = sum_weights (cd_lift D) l.
Proof. reflexivity. Qed.

(** THE PREDICATE-INDEXED CROSSING, at the level every bound in this
    library is actually proved at.

    [GatedSize.weight_bound_pred_T] bounds the mass OUTSIDE a predicate
    rather than the mass of a classifier's reject set, and this library
    needs no new machinery to reach it — which is the point.  Every
    arithmetic bound below is stated over an arbitrary list under
    [List.NoDup] of its cores plus a per-member side condition, and the
    classifier appears in exactly one place, as one hypothesis that
    turns "rejected" into "has a fire core"
    ([worked_weight_bound_T_of]).  Replace that hypothesis with
    "valid and outside [P]" and nothing else moves.

    The three arguments are the three things a task actually supplies:

    - [Fire], the set of cores its bound is proved about, as a
      predicate on [FinInput.FinCore] — the library's own vocabulary,
      not the classifier's;
    - the CROSSING, [Hfire]: every valid record outside [P] has a fire
      core.  This is the only place the task's own analysis of its
      programs enters, and it is where the [FinInput.FinCore] quotient
      is paid for: a predicate on RECORDS is being answered by a
      statement about CORES, which is sound in this direction because
      the conclusion charges every core with SOME representative
      outside [P];
    - the BOUND, [Hbound]: fire-core lists weigh at most [B].  Every
      composition lemma in this file — [cd_mix2_bound],
      [cd_scale_bound], [finite_support_bound_subset],
      [stdin_geometric_bound] — produces exactly this shape, so a task
      hands over what it already proved.

    [B <= b * cd_mass D] is the arithmetic step, kept separate rather
    than baked in for the reason [worked_weight_bound_T_of]'s comment
    gives: quantifying over [b] is what lets one proof serve every
    multiplier a task might declare, and it puts the ceiling where a
    reader can see it.

    The classifier reading is not lost by generalising.  A consumer
    holding this at [P := Classifier.accepts C] has
    [Measure.weight_bound_T C (cd_lift D) (cd_mass D) b] by
    [GatedSize.weight_bound_pred_of_classifier], which is an [iff] and
    not merely an implication — the two statements are the same
    statement. *)
Lemma weight_bound_pred_T_of_core_bound :
  forall (D : CoreDistribution) (P : FinProcInput -> Prop)
         (Fire : FinCore -> Prop) (B b : Q),
  (forall f, valid_fin_input f -> ~ P f -> Fire (fin_core f)) ->
  (forall l : list FinProcInput,
     List.NoDup (List.map fin_core l) ->
     (forall f, List.In f l -> Fire (fin_core f)) ->
     (core_sum (cd_weight D) l <= B)%Q) ->
  (B <= b * cd_mass D)%Q ->
  GatedSize.weight_bound_pred_T P (cd_lift D) (cd_mass D) b.
Proof.
  intros D P Fire B b Hfire Hbound Hb l Hnd Hall.
  rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ B); [| exact Hb].
  apply Hbound; [exact Hnd |].
  intros f Hf. destruct (Hall f Hf) as [Hv Hp]. exact (Hfire f Hv Hp).
Qed.

Lemma core_sum_nil : forall w, core_sum w [] = 0%Q.
Proof. reflexivity. Qed.

Lemma core_sum_cons : forall w f l,
  core_sum w (f :: l) = (w (fin_core f) + core_sum w l)%Q.
Proof. reflexivity. Qed.

(* =========================================================================
   Sums over a list of anything
   ========================================================================= *)

(** THE SUM every bound in this file is stated on: a [fold_right] of a
    weight over a list, at whatever element type the list has.

    ONE sum and not two.  The counting arguments run over lists of
    [FinInput.FinCore] — that is what [core_sum_map_fin_core] turns the
    obligation's records into — while the envp-varying families sum over
    BYTE LISTS (one envp entry, one standard input) and over LISTS of
    byte lists (a whole launch-time environment).

    Two lemmas genuinely cannot generalise, because they need decidable
    equality on the element type: [qsum_core_remove_one] and the
    inclusion bound [qsum_core_incl_le] that runs on it.  Those two keep
    [core] in their names and stay at [FinInput.FinCore], which is where
    this file spends them.  Everything else below is stated at the open
    element type. *)
Definition qsum {A : Type} (w : A -> Q) (l : list A) : Q :=
  fold_right (fun x acc => (w x + acc)%Q) 0%Q l.

Lemma qsum_nil : forall {A : Type} (w : A -> Q), qsum w (@nil A) = 0%Q.
Proof. reflexivity. Qed.

Lemma qsum_cons : forall {A : Type} (w : A -> Q) x l,
  qsum w (x :: l) = (w x + qsum w l)%Q.
Proof. reflexivity. Qed.

Lemma qsum_app : forall {A : Type} (w : A -> Q) l1 l2,
  (qsum w (l1 ++ l2) == qsum w l1 + qsum w l2)%Q.
Proof.
  intros A w l1 l2. induction l1 as [| x l1 IH].
  - cbn [List.app]. rewrite (@qsum_nil A w). ring.
  - cbn [List.app]. rewrite !qsum_cons, IH. ring.
Qed.

Lemma qsum_nonneg : forall {A : Type} (w : A -> Q) l,
  (forall x, List.In x l -> (0 <= w x)%Q) -> (0 <= qsum w l)%Q.
Proof.
  intros A w l. induction l as [| x l IH]; intros Hw; [apply Qle_refl |].
  rewrite qsum_cons. apply Qplus_nonneg.
  - apply Hw. left. reflexivity.
  - apply IH. intros y Hy. apply Hw. right. exact Hy.
Qed.

(** Weights that agree ON THE LIST sum equally.  No [Proper] instance
    is declared for [qsum]: its first argument is a function and the
    equivalence wanted of it is pointwise [Qeq], so the fact is a lemma
    applied where it is needed rather than something [rewrite] finds on
    its own.

    The hypothesis is [List.In x l] rather than agreement everywhere,
    and the difference is not cosmetic: every RESTRICTION argument —
    "this weight agrees with that one on the cores I am summing over,
    and nowhere else" — has the equality only on the list.
    [finite_support_bound_subset] is the case in point: the entries a
    core predicate rejects contribute nothing at the cores the predicate
    accepts, and nothing at all is known about them elsewhere. *)
Lemma qsum_ext : forall {A : Type} (w1 w2 : A -> Q) l,
  (forall x, List.In x l -> (w1 x == w2 x)%Q) ->
  (qsum w1 l == qsum w2 l)%Q.
Proof.
  intros A w1 w2 l. induction l as [| x l IH]; intros Hext; [reflexivity |].
  rewrite !qsum_cons, (Hext x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply Hext; right; exact Hy).
  reflexivity.
Qed.

Lemma qsum_mono : forall {A : Type} (w1 w2 : A -> Q) l,
  (forall x, List.In x l -> (w1 x <= w2 x)%Q) ->
  (qsum w1 l <= qsum w2 l)%Q.
Proof.
  intros A w1 w2 l. induction l as [| x l IH]; intros Hle; [apply Qle_refl |].
  rewrite !qsum_cons. apply Qplus_le_compat.
  - apply Hle. left. reflexivity.
  - apply IH. intros y Hy. apply Hle. right. exact Hy.
Qed.

Lemma qsum_scale : forall {A : Type} (c : Q) (w : A -> Q) l,
  (qsum (fun x => (c * w x)%Q) l == c * qsum w l)%Q.
Proof.
  intros A c w l. induction l as [| x l IH].
  - rewrite !qsum_nil. ring.
  - rewrite !qsum_cons. cbv beta. rewrite IH. ring.
Qed.

Lemma qsum_map : forall {A B : Type} (w : B -> Q) (f : A -> B) l,
  qsum w (List.map f l) = qsum (fun x => w (f x)) l.
Proof.
  intros A B w f l. induction l as [| x l IH]; [reflexivity |].
  cbn [List.map]. rewrite !qsum_cons, IH. reflexivity.
Qed.

(** A [List.flat_map] is the sum of its blocks EXACTLY, and not merely
    up to a uniform bound.  [qsum_flat_map_const_le] charges every
    block the same constant, which is right for the 256 continuations of
    a standard-input cylinder and wrong for the envp enumeration below,
    where the block under an entry [e] is charged a factor depending on
    [e]'s own length.  Stating the identity and deriving the inequality
    from [qsum_mono] gives both shapes out of one induction. *)
Lemma qsum_flat_map : forall {A B : Type} (w : B -> Q) (f : A -> list B) l,
  (qsum w (List.flat_map f l) == qsum (fun x => qsum w (f x)) l)%Q.
Proof.
  intros A B w f l. induction l as [| x l IH]; [reflexivity |].
  cbn [List.flat_map]. rewrite qsum_app, !qsum_cons. cbv beta.
  rewrite IH. reflexivity.
Qed.

Lemma qsum_flat_map_le :
  forall {A B : Type} (w : B -> Q) (f : A -> list B) (g : A -> Q) l,
    (forall x, List.In x l -> (qsum w (f x) <= g x)%Q) ->
    (qsum w (List.flat_map f l) <= qsum g l)%Q.
Proof.
  intros A B w f g l Hb. rewrite qsum_flat_map. apply qsum_mono. exact Hb.
Qed.

(** [List.map] commutes past [List.flat_map].  Stdlib ships
    [List.flat_map_concat_map] and [List.concat_map] and leaves the
    composite to be assembled; the direct induction is three lines and
    is what [cyl_enum_bytes_cyl] below needs. *)
Lemma map_flat_map_comm :
  forall (A B C : Type) (f : B -> C) (g : A -> list B) (l : list A),
    List.map f (List.flat_map g l)
      = List.flat_map (fun x => List.map f (g x)) l.
Proof.
  intros A B C f g l. induction l as [| x l IH]; [reflexivity |].
  cbn [List.flat_map]. rewrite List.map_app, IH. reflexivity.
Qed.

(** Summing a lifted weight over records is summing the weight over
    their cores.  Both folds add the same rationals in the same order;
    the induction is bookkeeping. *)
Lemma core_sum_map_fin_core : forall w l,
  core_sum w l = qsum w (List.map fin_core l).
Proof.
  intros w l. induction l as [| f l IH]; [reflexivity |].
  rewrite core_sum_cons, IH. cbn [List.map]. rewrite qsum_cons.
  reflexivity.
Qed.

(** The zero weight sums to zero. *)
Lemma qsum_zero : forall {A : Type} (cs : list A),
  (qsum (fun _ : A => 0%Q) cs == 0)%Q.
Proof.
  intros A cs. induction cs as [| c cs IH]; [reflexivity |].
  rewrite qsum_cons, IH. ring.
Qed.

(** Sums add pointwise.  This is what splits an entry list's weight into
    "the head entry" plus "the rest" without touching the list being
    summed over. *)
Lemma qsum_plus : forall {A : Type} (w1 w2 : A -> Q) cs,
  (qsum (fun c => (w1 c + w2 c)%Q) cs
     == qsum w1 cs + qsum w2 cs)%Q.
Proof.
  intros A w1 w2 cs. induction cs as [| c cs IH].
  - rewrite !qsum_nil. ring.
  - rewrite !qsum_cons. cbv beta. rewrite IH. ring.
Qed.

(* =========================================================================
   One entry's contribution
   ========================================================================= *)

(** The weight a single entry assigns: [q] at its own core, zero
    everywhere else.  Every [finite_support] weight is a sum of these,
    and the three lemmas below — absent, present, bounded — are the
    counting content of this file. *)
Definition core_indicator (c0 : FinCore) (q : Q) (c : FinCore) : Q :=
  if decide (c0 = c) then q else 0%Q.

(** Its two values, as rewrite rules.  Stated rather than unfolded at
    each use so that no proof below has to name [decide] or the
    [FinCore_eq_dec] instance: the case analysis happens here, once. *)
Lemma core_indicator_hit : forall c0 q, core_indicator c0 q c0 = q.
Proof.
  intros c0 q. unfold core_indicator.
  destruct (decide (c0 = c0)) as [_ | Hne]; [reflexivity | congruence].
Qed.

Lemma core_indicator_miss : forall c0 q c,
  c0 <> c -> core_indicator c0 q c = 0%Q.
Proof.
  intros c0 q c Hne. unfold core_indicator.
  destruct (decide (c0 = c)) as [Heq | _]; [congruence | reflexivity].
Qed.

(** Over a list that does not mention the entry's core, the entry
    contributes nothing. *)
Lemma qsum_indicator_absent : forall c0 q cs,
  ~ List.In c0 cs -> (qsum (core_indicator c0 q) cs == 0)%Q.
Proof.
  intros c0 q cs. induction cs as [| c cs IH]; intros Hnin.
  - rewrite qsum_nil. reflexivity.
  - rewrite qsum_cons.
    rewrite (core_indicator_miss c0 q c)
      by (intros Heq; apply Hnin; left; exact (eq_sym Heq)).
    rewrite IH by (intros Hin; apply Hnin; right; exact Hin).
    ring.
Qed.

(** Over a DUPLICATE-FREE list that does mention it, the entry
    contributes exactly its weight — once, which is the whole reason
    [Measure.weight_bound_T] carries the [List.NoDup] hypothesis.  The
    induction is on the [List.NoDup] derivation: its step case hands
    over precisely the "the head does not occur again" fact that
    [qsum_indicator_absent] consumes. *)
Lemma qsum_indicator_present : forall c0 q cs,
  List.NoDup cs -> List.In c0 cs ->
  (qsum (core_indicator c0 q) cs == q)%Q.
Proof.
  intros c0 q cs Hnd. induction Hnd as [| c cs Hnin Hnd IH]; intros Hin.
  - destruct Hin.
  - rewrite qsum_cons.
    destruct (decide (c0 = c)) as [Heq | Hne].
    + subst c. rewrite core_indicator_hit.
      rewrite (qsum_indicator_absent c0 q cs Hnin). ring.
    + rewrite (core_indicator_miss c0 q c Hne).
      destruct Hin as [Hc | Hin]; [congruence |].
      rewrite (IH Hin). ring.
Qed.

(** Either way, a nonnegative entry contributes at most its weight.
    This is the per-entry half of [finite_support_bound]; the list is
    duplicate-free, so the entry is either counted once or not at all,
    and both cases are already proved. *)
Lemma qsum_indicator_le : forall c0 q cs,
  (0 <= q)%Q -> List.NoDup cs ->
  (qsum (core_indicator c0 q) cs <= q)%Q.
Proof.
  intros c0 q cs Hq Hnd.
  destruct (List.in_dec (fun x y => decide (x = y)) c0 cs) as [Hin | Hnin].
  - rewrite (qsum_indicator_present c0 q cs Hnd Hin). apply Qle_refl.
  - rewrite (qsum_indicator_absent c0 q cs Hnin). exact Hq.
Qed.

(* =========================================================================
   Combinator: finite support
   ========================================================================= *)

(** The weight an entry list assigns to a core: the total of the entries
    naming it.  SUMMED, not "the first one wins": a duplicate core is
    an author writing the same core twice, and the reading that keeps
    [entries_mass] — a flat sum over the entries — equal to the total
    weight is the one that adds them.  The alternative would make
    [finite_support_mass_lower_witness] false on any list with a repeat.

    Both halves of that are pinned rather than asserted:
    [dup_entries_weight_summed] computes the repeated core's weight and
    finds the sum, and [dup_witness_attains_mass] shows the declared
    mass still attained on the very list a first-wins reading would
    strand below it. *)
Fixpoint entries_weight (entries : list (FinCore * Q)) (c : FinCore) : Q :=
  match entries with
  | [] => 0%Q
  | e :: rest => (core_indicator (fst e) (snd e) c + entries_weight rest c)%Q
  end.

(** The declared mass of an entry list: the sum of the entries'
    weights, with no reference to which cores they name. *)
Definition entries_mass (entries : list (FinCore * Q)) : Q :=
  fold_right (fun e acc => (snd e + acc)%Q) 0%Q entries.

Lemma entries_mass_nil : entries_mass [] = 0%Q.
Proof. reflexivity. Qed.

Lemma entries_mass_cons : forall e entries,
  entries_mass (e :: entries) = (snd e + entries_mass entries)%Q.
Proof. reflexivity. Qed.

(** The declared mass of a nonnegative entry list is nonnegative.  This
    is the first half of [Measure.DISTRIBUTION]'s [M_nonneg] for
    everything this library builds out of [finite_support]: [entries_mass]
    is a fold of [Qplus] over the entry weights, so the hypothesis the
    constructor already demands is the hypothesis this needs, entry by
    entry.

    Nothing here ties the mass to the weight FUNCTION — the header's
    "there is deliberately no field relating [cd_mass] to [cd_weight]"
    still stands.  The claim is only about the sign of a declared
    number. *)
Lemma entries_mass_nonneg : forall entries,
  (forall e, List.In e entries -> (0 <= snd e)%Q) ->
  (0 <= entries_mass entries)%Q.
Proof.
  induction entries as [| e rest IH]; intros Hnn.
  - apply Qle_refl.
  - rewrite entries_mass_cons.
    apply Qplus_nonneg.
    + apply Hnn. left. reflexivity.
    + apply IH. intros e' He'. apply Hnn. right. exact He'.
Qed.

(** Splitting the head entry off a sum, in the form the two bounds
    below both need: the entry list's weight summed over [cs] is the
    head's indicator summed over [cs] plus the tail's weight summed over
    [cs].  [qsum_plus] does the work; the extensionality step
    is there only because the fixpoint's unfolding is a pointwise
    equation. *)
Lemma qsum_entries_cons : forall e entries cs,
  (qsum (entries_weight (e :: entries)) cs
     == qsum (core_indicator (fst e) (snd e)) cs
        + qsum (entries_weight entries) cs)%Q.
Proof.
  intros e entries cs.
  rewrite <- qsum_plus.
  apply qsum_ext. intros c _. reflexivity.
Qed.

(** Nonnegative entries give a nonnegative weight — the field
    [finite_support] has to fill in.  Induction on the entries, with the
    head's indicator nonnegative by case analysis. *)
Lemma entries_weight_nonneg : forall entries,
  (forall e, List.In e entries -> (0 <= snd e)%Q) ->
  forall c, (0 <= entries_weight entries c)%Q.
Proof.
  intros entries. induction entries as [| e entries IH]; intros Hnn c.
  - apply Qle_refl.
  - cbn [entries_weight].
    assert (Hhead : (0 <= core_indicator (fst e) (snd e) c)%Q).
    { unfold core_indicator. destruct (decide (fst e = c)) as [_ | _].
      - apply Hnn. left. reflexivity.
      - apply Qle_refl. }
    assert (Htail : (0 <= entries_weight entries c)%Q).
    { apply IH. intros e' He'. apply Hnn. right. exact He'. }
    apply Qplus_nonneg; assumption.
Qed.

(** THE BOUND, over cores: any duplicate-free list of cores sums to at
    most the entry list's declared mass.  Induction on the ENTRIES, not
    on the list — the list is fixed and its duplicate-freedom is used
    once per entry, by [qsum_indicator_le], which is where the
    hypothesis does its work.  Each entry contributes at most its own
    weight to the sum, and the mass is exactly the total of those
    weights, so the bound falls out entry by entry.

    Nonnegativity is needed for entries the list does NOT mention: they
    contribute nothing to the sum but their weight to the mass, and a
    negative one would make the mass the smaller number. *)
Lemma entries_weight_qsum_le : forall entries cs,
  (forall e, List.In e entries -> (0 <= snd e)%Q) ->
  List.NoDup cs ->
  (qsum (entries_weight entries) cs <= entries_mass entries)%Q.
Proof.
  intros entries. induction entries as [| e entries IH]; intros cs Hnn Hnd.
  - rewrite entries_mass_nil.
    rewrite (qsum_ext (entries_weight []) (fun _ => 0%Q) cs)
      by (intros c _; reflexivity).
    rewrite qsum_zero. apply Qle_refl.
  - rewrite qsum_entries_cons, entries_mass_cons.
    apply Qplus_le_compat.
    + apply qsum_indicator_le; [| exact Hnd].
      apply Hnn. left. reflexivity.
    + apply IH; [| exact Hnd].
      intros e' He'. apply Hnn. right. exact He'.
Qed.

(** The distribution supported on a finite list of (core, weight)
    entries.  The nonnegativity proof is an ARGUMENT, not a side
    condition discovered later: see the header for why refusing it is
    not on offer, and [negative_entries_no_core_distribution] for what
    happens when the entries cannot supply it. *)
Definition finite_support (entries : list (FinCore * Q))
    (Hnn : forall e, List.In e entries -> (0 <= snd e)%Q) : CoreDistribution :=
  mkCoreDistribution (entries_weight entries) (entries_mass entries)
                     (entries_weight_nonneg entries Hnn).

(** [Measure.DISTRIBUTION]'s [M_nonneg], for a finite support: the
    proof argument the constructor already took is exactly what the
    declared mass needs, so an author who built the distribution owes
    nothing further.  [entries_mass_nonneg] is the content. *)
Lemma finite_support_mass_nonneg : forall entries
    (Hnn : forall e, List.In e entries -> (0 <= snd e)%Q),
  (0 <= cd_mass (finite_support entries Hnn))%Q.
Proof.
  intros entries Hnn. cbn [cd_mass finite_support].
  apply entries_mass_nonneg. exact Hnn.
Qed.

(** Discharging [finite_support]'s proof argument BY COMPUTATION, which
    is what a task author will actually want to do.  An entry list is
    written out as a literal, so "every entry is nonnegative" is a
    decidable fact about closed rationals, and this bridge turns it into
    one [Qle_bool] scan: the obligation becomes [eq_refl] at the
    definition site — see [example_entries_nonneg] and [dup_cd] below,
    which use it in the two available styles.

    Without it, every author writes the [destruct] chain over the entry
    list by hand, and it grows with the list.  The boolean scan stays
    inside the file's [Qle] discipline for the reason the header gives:
    [Qle_bool] on literal operands is the documented exception, and no
    [Q] EQUALITY is decided anywhere in it. *)
Lemma entries_nonneg_of_forallb : forall entries : list (FinCore * Q),
  List.forallb (fun e => Qle_bool 0 (snd e)) entries = true ->
  forall e, List.In e entries -> (0 <= snd e)%Q.
Proof.
  intros entries Hall e He.
  rewrite List.forallb_forall in Hall.
  apply (proj1 (Qle_bool_iff _ _)). apply Hall. exact He.
Qed.

(** THE EXPORT: any list of records with pairwise distinct cores — the
    exact hypothesis [Measure.weight_bound_T] carries — weighs at most
    the declared mass.  [core_sum_map_fin_core] turns the records into
    their cores and the hypothesis into an ordinary [List.NoDup]; the
    rest is [entries_weight_qsum_le].

    This is the lemma a task's [Measure.weight_bound_T] proof consumes.
    That obligation compares the sum against [b * M], so at [b = 1] it
    is this bound plus [Qmult_1_l], and [Measure.weight_bound_mono]
    carries a proof at one [b] to every larger one.

    The [List.NoDup] hypothesis is doing work, not inherited decoration:
    [finite_support_bound_needs_nodup] exhibits a two-element list that
    the bound fails on and that duplicate-freedom of the cores is
    exactly what excludes. *)
Lemma finite_support_bound : forall entries
    (Hnn : forall e, List.In e entries -> (0 <= snd e)%Q) l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (finite_support entries Hnn)) l
     <= cd_mass (finite_support entries Hnn))%Q.
Proof.
  intros entries Hnn l Hnd.
  cbn [cd_weight cd_mass finite_support].
  rewrite core_sum_map_fin_core.
  apply entries_weight_qsum_le; assumption.
Qed.

(* =========================================================================
   The same bound, refined to a subset of the cores
   ========================================================================= *)

(** The entries naming a core the predicate accepts.  A [bool]-valued
    predicate rather than a [Prop] one, because the restriction has to
    be COMPUTED — [entries_mass] of the restriction is the number the
    refined bound compares against, and a task author writing that
    number down wants it to reduce. *)
Definition entries_restrict (P : FinCore -> bool) (entries : list (FinCore * Q))
  : list (FinCore * Q) :=
  List.filter (fun e => P (fst e)) entries.

(** Restricting keeps every entry's weight nonnegative, since it only
    removes entries. *)
Lemma entries_restrict_nonneg : forall P entries,
  (forall e, List.In e entries -> (0 <= snd e)%Q) ->
  forall e, List.In e (entries_restrict P entries) -> (0 <= snd e)%Q.
Proof.
  intros P entries Hnn e He.
  apply (proj1 (List.filter_In _ _ _)) in He. apply Hnn. exact (proj1 He).
Qed.

(** AT AN ACCEPTED CORE, the discarded entries were contributing
    nothing: an entry the predicate rejects names a core the predicate
    rejects, which is not the core being weighed, so its indicator
    misses.  This is the whole content of the refinement, and note
    where it does NOT hold — at a core the predicate rejects, the two
    weights differ, which is why the bound below quantifies over lists
    of accepted cores and why [qsum_ext]'s hypothesis had to
    be the on-the-list one. *)
Lemma entries_weight_restrict : forall P entries c,
  P c = true ->
  (entries_weight entries c == entries_weight (entries_restrict P entries) c)%Q.
Proof.
  intros P entries c HP. unfold entries_restrict.
  induction entries as [| e entries IH]; [reflexivity |].
  cbn [List.filter]. destruct (P (fst e)) eqn:Hf.
  - cbn [entries_weight]. rewrite IH. reflexivity.
  - cbn [entries_weight].
    rewrite (core_indicator_miss (fst e) (snd e) c)
      by (intros Heq; rewrite Heq, HP in Hf; discriminate).
    rewrite IH. ring.
Qed.

(** THE PER-SUBSET REFINEMENT the plan's Interface assigns here: a list
    whose cores all satisfy [P] weighs at most the mass of the
    [P]-entries ALONE, not the mass of all of them.

    [finite_support_bound] is the case [P] accepts everything
    ([entries_restrict_all]), so nothing is lost by having only this
    one — but the refinement is what a task needs when its fire set is
    a known part of the support and the rest of the declared mass sits
    on cores the classifier accepts.  Charging that part against the
    fire set would be giving away the bound.

    The proof is one rewrite and then the unrefined bound: on the
    cores actually being summed over, the restricted entry list weighs
    what the full one does ([entries_weight_restrict]), and
    [entries_weight_qsum_le] applies to the restriction with
    the nonnegativity it inherits. *)
Lemma finite_support_bound_subset : forall (P : FinCore -> bool) entries
    (Hnn : forall e, List.In e entries -> (0 <= snd e)%Q) l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> P (fin_core f) = true) ->
  (core_sum (cd_weight (finite_support entries Hnn)) l
     <= entries_mass (entries_restrict P entries))%Q.
Proof.
  intros P entries Hnn l Hnd HP.
  cbn [cd_weight finite_support]. rewrite core_sum_map_fin_core.
  rewrite (qsum_ext (entries_weight entries)
             (entries_weight (entries_restrict P entries))
             (List.map fin_core l)).
  2:{ intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
      apply entries_weight_restrict. rewrite <- Hf. apply HP. exact Hin. }
  apply entries_weight_qsum_le;
    [ apply entries_restrict_nonneg; exact Hnn | exact Hnd ].
Qed.

(** The refinement subsumes the total-mass bound rather than sitting
    beside it: at the predicate that accepts everything, the
    restriction is the entry list itself, so
    [finite_support_bound_subset] IS [finite_support_bound]. *)
Lemma entries_restrict_all : forall entries,
  entries_restrict (fun _ => true) entries = entries.
Proof.
  induction entries as [| e entries IH]; [reflexivity |].
  cbn [entries_restrict List.filter]. unfold entries_restrict in IH.
  rewrite IH. reflexivity.
Qed.

(* =========================================================================
   Wrapping a core back up as a record
   ========================================================================= *)

(** A canonical [FinInput.FinProcInput] over a given core.  The four
    core fields are copied; the nine LAUNCH ENVIRONMENT fields and the
    two declarations are invented, and the choices are these:

    - [fin_uid], [fin_gid], [fin_nofile] and [fin_sigmask] are all
      [Z_to_bv 64 0].  [Run.valid_input] constrains four
      of the nine — the ids through [Run.valid_creds] and [Run.valid_id]
      ([bv_unsigned] below [2 ^ 32 - 1]), the descriptor limit through
      [Run.valid_nofile] ([bv_unsigned] at most [2 ^ 31 - 64]), and the
      blocked mask through [Run.valid_sigmask] (no [SIGKILL] or
      [SIGSTOP] bit) — and zero satisfies all four, being the smallest
      value for the first three and the empty mask for the last.  So if
      a caller ever does want validity, nothing here is in the way.
    - [fin_groups] is the empty list and [fin_net] is
      [State.net_silent], the quiet environment [State] declares for
      fixtures and callers that need SOME queue to name ([State] is
      explicit that it "carries no special status", and neither does
      this use of it).
      [Run.valid_input] constrains neither field, as [FinInput]'s record
      header records.
    - [fin_kernel] is [State.default_kernel], the build [State.mkProcInput]
      fills in; [Run.valid_input] does not constrain it either.
    - [fin_execfn] is [State.default_execfn], the one-byte name "a".
      [Run.valid_launch] DOES constrain it, and this is the value that
      can be valid: it is a name [getname_flags] (fs/namei.c, Linux
      v6.18.46, commit 1f99e9ab748f) can return, and it adds two bytes
      to a launch whose limit is two megabytes, so the joint E2BIG test
      of [bprm_stack_limits] (fs/exec.c) is decided by the core's argv
      and envp rather than by this choice.
    - [fin_abort_terminal] is [false], the task declaration
      [Run.valid_input] pins and so the one this embedding has to make
      if the record is to be valid at all.  It and [fin_va_size] are
      the declarations rather than environment facts, and the only
      fields [Run.valid_input] fixes rather than bounds.

    The choice is arbitrary and is allowed to be, because
    [FinInput.fin_core] forgets all eleven ([FinInput.fin_core_env_eq]
    pins that it forgets these and nothing else).  What the embedding is
    FOR is [fin_core_core_input]: it is a section of
    [FinInput.fin_core], so a statement about a list of cores can be
    re-stated as a statement about a list of records without changing
    any sum.

    It is NOT claimed that [core_input c] is valid: validity constrains
    argv, envp and the file system, which come from the core, and the
    library cannot know an author's cores denote a valid input.  Nor is
    it claimed anything rejects them.  See the header. *)
Definition core_input (c : FinCore) : FinProcInput :=
  mkFinProcInput (core_argv c) (core_envp c) (core_fs c) (core_stdin c)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) [] net_silent
                 (Z_to_bv 64 0) (Z_to_bv 64 0) hwcap_rv64gc false Sv48 [] []
                 default_kernel default_execfn.

(** THE LAUNCH-ENVIRONMENT FIELDS ARE NOT ARBITRARY, even though this
    definition claims nothing about them.  A caller proving its own
    core's input valid has to discharge every conjunct of
    [Run.valid_input], and the ones this library fills are the ones that
    caller cannot reach: the zero descriptor limit is inside
    [Run.valid_nofile]'s ceiling and the zero mask is the empty one
    [Run.valid_sigmask] asks for.  [Run.valid_hwcap] admits exactly two
    words, and a zero is neither, so the hwcap is [StackLayout] mask
    [hwcap_rv64gc] rather than another zero -- a zero here would make
    every core's input unprovable, whatever its argv said.  Choosing a
    value that CAN be valid is not the same as claiming it is.

    [fin_abort_terminal] is [false], the declaration [Run.valid_input]
    pins, for the same reason: it is the only value that can be valid
    under the predicate this library's callers discharge.  [fin_execfn]
    is [State.default_execfn] on the same ground -- the empty name is
    one [Run.valid_execfn] refuses, so a caller that wanted validity
    could not get there from it. *)

(** The embedding is a section of [FinInput.fin_core]: wrapping a core
    up and reading it back gives the core.  By [destruct] and
    conversion — a core is its own four fields. *)
Lemma fin_core_core_input : forall c, fin_core (core_input c) = c.
Proof. intros [a e fs s]. reflexivity. Qed.

(** ... and so a list of cores, wrapped, has exactly those cores. *)
Lemma map_fin_core_core_input : forall cs,
  List.map fin_core (List.map core_input cs) = cs.
Proof.
  induction cs as [| c cs IH]; [reflexivity |].
  cbn [List.map]. rewrite fin_core_core_input, IH. reflexivity.
Qed.

(** THE RESTRICTION TO CORES COSTS NOTHING, mechanized.  Building every
    weight on [FinInput.FinCore] looks like a narrowing — the library
    cannot express a weight that reads [FinInput.fin_uid] — and it is
    not one, because [Measure.DISTRIBUTION] cannot accept such a weight
    either.  Any [w] satisfying its two WEIGHT obligations agrees,
    pointwise up to [Qeq], with the lift of the [CoreDistribution] that
    weighs a core by [w] at that core's canonical record; the declared
    mass is free of [w], since no obligation ties [M] to it —
    [M_nonneg] constrains its sign and nothing more.

    So "this library builds all the distributions there are" is a
    theorem rather than a hope, and a task author who cannot see how to
    phrase their weight as a [CoreDistribution] is looking at a
    presentation problem, not at an expressiveness limit. *)
Lemma cd_lift_complete : forall (w : FinProcInput -> Q) (M : Q),
  (forall f, (0 <= w f)%Q) ->
  (forall f g, fin_core f = fin_core g -> (w f == w g)%Q) ->
  exists D : CoreDistribution,
    cd_mass D = M /\ forall f, (w f == cd_lift D f)%Q.
Proof.
  intros w M Hnn Hblind.
  exists (mkCoreDistribution (fun c => w (core_input c)) M
            (fun c => Hnn (core_input c))).
  split; [reflexivity |].
  intros f. unfold cd_lift. cbn [cd_weight].
  apply Hblind. rewrite fin_core_core_input. reflexivity.
Qed.

(* =========================================================================
   Honesty certificates for [finite_support]
   ========================================================================= *)

(** UPPER: every admissible partial sum is at most the declared mass.
    This is [finite_support_bound] under the name the certificate
    vocabulary uses — stated separately so that a consumer looking for
    the certificate finds one, and so that the pair
    (upper, lower) reads as a pair. *)
Lemma finite_support_mass_upper : forall entries
    (Hnn : forall e, List.In e entries -> (0 <= snd e)%Q) l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (finite_support entries Hnn)) l
     <= cd_mass (finite_support entries Hnn))%Q.
Proof. exact finite_support_bound. Qed.

(** The counting fact behind the lower witness: over a duplicate-free
    list of cores that COVERS every entry, the sum reaches the mass.
    Induction on the entries again, with
    [qsum_indicator_present] — rather than
    [qsum_indicator_le] — at the head, which is where the
    coverage hypothesis is spent.  Note this direction needs no
    nonnegativity: nothing is being dropped. *)
Lemma entries_mass_le_qsum : forall entries cs,
  List.NoDup cs ->
  (forall e, List.In e entries -> List.In (fst e) cs) ->
  (entries_mass entries <= qsum (entries_weight entries) cs)%Q.
Proof.
  intros entries. induction entries as [| e entries IH]; intros cs Hnd Hcov.
  - rewrite entries_mass_nil.
    rewrite (qsum_ext (entries_weight []) (fun _ => 0%Q) cs)
      by (intros c _; reflexivity).
    rewrite qsum_zero. apply Qle_refl.
  - rewrite qsum_entries_cons, entries_mass_cons.
    apply Qplus_le_compat.
    + rewrite (qsum_indicator_present (fst e) (snd e) cs Hnd)
        by (apply Hcov; left; reflexivity).
      apply Qle_refl.
    + apply IH; [exact Hnd |].
      intros e' He'. apply Hcov. right. exact He'.
Qed.

(** LOWER, with the CHOICE of list left to the caller: any
    duplicate-free list of cores that COVERS the entries attains the
    declared mass, once wrapped by [core_input].

    The content and the choice are separated because a MIXTURE needs
    them separated: [cd_mix2_finite_support_mass_exact], far below,
    has to attain two components on ONE list, and neither component's
    canonical witness need cover the other's cores.  That lemma is
    defined in the composition section, where mixtures are; this one
    is here, with the finite-support certificates it belongs to.

    [finite_support_mass_lower_witness] is this lemma at the canonical
    choice, and is derived from it rather than proved again. *)
Lemma finite_support_mass_lower_on : forall entries
    (Hnn : forall e, List.In e entries -> (0 <= snd e)%Q) cs,
  List.NoDup cs ->
  (forall e, List.In e entries -> List.In (fst e) cs) ->
  (cd_mass (finite_support entries Hnn)
     <= core_sum (cd_weight (finite_support entries Hnn))
          (List.map core_input cs))%Q.
Proof.
  intros entries Hnn cs Hnd Hcov.
  cbn [cd_weight cd_mass finite_support].
  rewrite core_sum_map_fin_core, map_fin_core_core_input.
  apply entries_mass_le_qsum; assumption.
Qed.

(** LOWER, at the canonical list: the entries' cores with duplicates
    removed ([List.nodup], whose [List.NoDup_nodup] and [List.nodup_In]
    are exactly the two facts the covering hypothesis asks for), each
    wrapped by [core_input].  So the mass is not padding: some list the
    obligation quantifies over does weigh that much.

    Again, and it matters: the witness list is not claimed valid or
    rejected.  A task that wants to say its mass is attained BY THE FIRE
    SET has to exhibit rejected inputs itself; this says only that the
    arithmetic leaves no slack. *)
Lemma finite_support_mass_lower_witness : forall entries
    (Hnn : forall e, List.In e entries -> (0 <= snd e)%Q),
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (cd_mass (finite_support entries Hnn)
          <= core_sum (cd_weight (finite_support entries Hnn)) l)%Q.
Proof.
  intros entries Hnn.
  exists (List.map core_input
            (List.nodup (fun x y => decide (x = y)) (List.map fst entries))).
  split.
  - rewrite map_fin_core_core_input. apply List.NoDup_nodup.
  - apply finite_support_mass_lower_on; [apply List.NoDup_nodup |].
    intros e He. apply List.nodup_In, List.in_map. exact He.
Qed.

(** The two certificates together: the declared mass is exactly what
    some admissible list weighs.  [Qle_antisym] on the pair — the
    equality is DERIVED from the two inequalities, never decided by
    computing on either side, which is the discipline [Measure]'s header
    sets out. *)
Lemma finite_support_mass_exact : forall entries
    (Hnn : forall e, List.In e entries -> (0 <= snd e)%Q),
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (core_sum (cd_weight (finite_support entries Hnn)) l
          == cd_mass (finite_support entries Hnn))%Q.
Proof.
  intros entries Hnn.
  destruct (finite_support_mass_lower_witness entries Hnn) as [l [Hnd Hlow]].
  exists l. split; [exact Hnd |].
  apply Qle_antisym; [apply finite_support_bound; exact Hnd | exact Hlow].
Qed.

(* =========================================================================
   Non-vacuity: the obligations really discharge
   ========================================================================= *)

(** Two concrete cores, differing in standard input alone: the empty
    input, and the one-byte input "A".  Everything else empty — an
    empty argv and envp and an empty file system are not claimed valid
    (see [core_input]); these are two points of [FinInput.FinCore] to
    hang weights on, nothing more. *)
Definition example_core_empty : FinCore := mkFinCore [] [] [] [].
Definition example_core_a : FinCore := mkFinCore [] [] [] [Z_to_bv 8 65].

(** A two-entry support: half the mass on the empty input, a quarter on
    "A", for a declared total of three quarters. *)
Definition example_entries : list (FinCore * Q) :=
  [(example_core_empty, (1 # 2)%Q); (example_core_a, (1 # 4)%Q)].

(** The nonnegativity obligation, discharged by the [Qle_bool] scan of
    [entries_nonneg_of_forallb] rather than by a [destruct] chain: the
    [eq_refl] is the whole proof, and it would still be the whole proof
    at fifty entries. *)
Lemma example_entries_nonneg :
  forall e, List.In e example_entries -> (0 <= snd e)%Q.
Proof. exact (entries_nonneg_of_forallb example_entries eq_refl). Qed.

Definition example_cd : CoreDistribution :=
  finite_support example_entries example_entries_nonneg.

(** THE POINT OF THE FILE, compiled: a [Measure.DISTRIBUTION] whose
    five components are all taken from the library, with no proof
    written here.  [w] is the lift, [M] is the declared mass, the two
    weight obligations are [cd_lift_nonneg] and [cd_lift_core_blind]
    applied to the distribution — the same two terms every distribution
    this library builds will use — and [M_nonneg] is
    [finite_support_mass_nonneg] at the entry list's own nonnegativity
    proof.  The ascription [<: DISTRIBUTION] is what checks it: were any
    obligation not actually discharged by the library's lemma, this
    module would fail to compile. *)
Module Example_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift example_cd.
  Definition M : Q := cd_mass example_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q := cd_lift_nonneg example_cd.
  Definition M_nonneg : (0 <= M)%Q :=
    finite_support_mass_nonneg example_entries example_entries_nonneg.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind example_cd.
End Example_D.

(** The example is not the ZERO distribution, which every obligation in
    sight would satisfy trivially and which would make the ascription
    above evidence of nothing: it puts at least [1 # 2] on the record
    over the empty core.  The [1 # 2] step is a [Qle] on literal
    operands decided through [Qle_bool] — the exception [Measure]'s
    header documents and this file's header repeats — and the [0 < 1 # 2]
    step is conversion in [Z], not a decision about [Q] at all. *)
Lemma example_D_w_positive :
  (0 < Example_D.w (core_input example_core_empty))%Q.
Proof.
  apply (Qlt_le_trans _ (1 # 2)%Q); [reflexivity |].
  unfold Example_D.w, cd_lift, example_cd.
  rewrite fin_core_core_input.
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(** ... and its mass certificates are inhabited at that instance: the
    mass its two entries declare (a half plus a quarter) is attained by
    an admissible list.  This is [finite_support_mass_exact] at the
    example, quoted so that the generic certificate is seen to apply to
    something; the sum is written on [core_sum] of the core weight,
    which by [core_sum_cd_lift] is the sum [Measure.weight_bound_T]
    would take of [Example_D.w]. *)
Lemma example_D_mass_attained :
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (core_sum (cd_weight example_cd) l == cd_mass example_cd)%Q.
Proof. apply finite_support_mass_exact. Qed.

(** THE PER-SUBSET REFINEMENT BITES, which is the only way to see that
    it is a refinement and not a restatement.  Restricting
    [example_entries] to the empty core alone leaves a mass of [1 # 2],
    and the declared total is [3 # 4] — a number the refined bound
    does NOT permit.  Both are closed [Q] facts on literals this file
    wrote, per the header's exception.

    Without the second conjunct the first would be consistent with the
    refinement being vacuous; together they say that a task whose fire
    set lies inside the empty core is held to half the mass, not to
    three quarters of it. *)
Definition example_is_empty_core (c : FinCore) : bool :=
  if decide (c = example_core_empty) then true else false.

Lemma finite_support_bound_subset_bites :
  (entries_mass (entries_restrict example_is_empty_core example_entries)
     == 1 # 2)%Q
  /\ ~ (entries_mass example_entries <= 1 # 2)%Q.
Proof.
  split.
  - vm_compute. reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(* =========================================================================
   Non-vacuity: duplicate cores are SUMMED, and [List.NoDup] is load-bearing
   ========================================================================= *)

(** An entry list that names one core TWICE — half and an eighth on the
    empty core, a quarter on "A" — so that the reading argued for at
    [entries_weight] is exercised by something instead of only asserted.
    [example_entries] has two distinct cores and therefore tests nothing
    about repeats.

    The nonnegativity obligation is discharged inline here, at the
    definition site, which is the other of the two styles
    [entries_nonneg_of_forallb] supports and the one a task author
    writing a distribution will use. *)
Definition dup_entries : list (FinCore * Q) :=
  [(example_core_empty, (1 # 2)%Q);
   (example_core_a, (1 # 4)%Q);
   (example_core_empty, (1 # 8)%Q)].

Definition dup_cd : CoreDistribution :=
  finite_support dup_entries (entries_nonneg_of_forallb dup_entries eq_refl).

(** The bite: the repeated core weighs [5 # 8], the SUM of its two
    entries, and not the [1 # 2] a "first entry wins" reading would give
    it.  A [Qeq] between closed literals, decided by computation — which
    is the right tool for [Qeq] and not the pattern [Measure]'s header
    warns about; the header above says why. *)
Lemma dup_entries_weight_summed :
  (entries_weight dup_entries example_core_empty == 5 # 8)%Q.
Proof. vm_compute. reflexivity. Qed.

(** ... and the declared mass is still the flat total of the entries,
    [7 # 8], which is the half of the story that makes the summing
    reading the only coherent one: a first-wins weight would total
    [3 # 4] against a declared [7 # 8], and no list could reach the
    declared mass. *)
Lemma dup_entries_mass : (entries_mass dup_entries == 7 # 8)%Q.
Proof. vm_compute. reflexivity. Qed.

(** The witness [finite_support_mass_lower_witness] builds for this
    entry list, written out.  [List.nodup] collapses the repeat, so it
    has two elements for three entries — and it still attains the
    declared [7 # 8], which is exactly the claim
    [finite_support_mass_lower_witness] would fail on under a first-wins
    reading. *)
Definition dup_witness : list FinProcInput :=
  List.map core_input
    (List.nodup (fun x y => decide (x = y)) (List.map fst dup_entries)).

Lemma dup_witness_collapses_the_repeat : length dup_witness = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma dup_witness_attains_mass :
  (core_sum (cd_weight dup_cd) dup_witness == cd_mass dup_cd)%Q.
Proof. vm_compute. reflexivity. Qed.

(** THE [List.NoDup] HYPOTHESIS IS LOAD-BEARING, and this is the
    combinator-level counterpart of [Measure.weight_bound_refutable]:
    without duplicate-freedom of the CORES, [finite_support_bound] is
    simply false.  Offer the same core twice — two records, so the list
    is [List.NoDup] as a list of RECORDS — and the sum is [5 # 4]
    against a declared mass of [7 # 8].

    Both conjuncts are needed to make the point.  The second says the
    bound really would fail on this list; the first says the list is
    excluded, and names what excludes it.  A reader can otherwise not
    tell whether the hypothesis is doing work or is decoration inherited
    from [Measure.weight_bound_T]'s shape. *)
Lemma finite_support_bound_needs_nodup :
  ~ List.NoDup (List.map fin_core
       [core_input example_core_empty; core_input example_core_empty])
  /\ ~ (core_sum (cd_weight dup_cd)
          [core_input example_core_empty; core_input example_core_empty]
          <= cd_mass dup_cd)%Q.
Proof.
  split.
  - intros Hnd. cbn [List.map] in Hnd.
    rewrite !fin_core_core_input in Hnd.
    apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd.
    destruct Hnd as [Hnin _]. apply Hnin. left. reflexivity.
  - intros Hle.
    apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(* =========================================================================
   Non-vacuity, the other way: a negative entry admits no distribution
   ========================================================================= *)

(** A rigged entry list: one core, weight [-1].  Nothing stops an author
    WRITING this list — it is a perfectly good [list (FinCore * Q)] —
    and the two lemmas below are what stops it becoming a
    [CoreDistribution]. *)
Definition negative_entries : list (FinCore * Q) :=
  [(example_core_empty, (- (1 # 1))%Q)].

(** The constructor's obligation is unsatisfiable for it: the weight it
    assigns to the rigged core is [-1], and no proof of nonnegativity
    exists.  Decided on a [Qle_bool] boolean over literals, per the
    header's exception. *)
Lemma negative_entries_no_nonneg_weight :
  ~ (forall c, (0 <= entries_weight negative_entries c)%Q).
Proof.
  intros Hnn. specialize (Hnn example_core_empty).
  apply (proj2 (Qle_bool_iff _ _)) in Hnn.
  vm_compute in Hnn. discriminate.
Qed.

(** So no [CoreDistribution] whatever weighs cores that way — not just
    none built by [finite_support], and not just none whose weight is
    that exact function: none whose weight so much as AGREES with it
    pointwise up to [Qeq], which is the strongest reading and the one a
    [Qeq]-respecting layer cares about.  The [cd_nonneg] FIELD is what
    refutes it, and that is the argument for making nonnegativity a
    field: the impossibility becomes a property of the record rather
    than of one combinator's typing. *)
Lemma negative_entries_no_core_distribution :
  forall D : CoreDistribution,
    ~ (forall c, (cd_weight D c == entries_weight negative_entries c)%Q).
Proof.
  intros D Hagree. apply negative_entries_no_nonneg_weight.
  intros c. rewrite <- (Hagree c). apply cd_nonneg.
Qed.

(* =========================================================================
   Enumerating the bytes, and the byte lists of a given length
   ========================================================================= *)

(** All 256 bytes, as a list.  Nothing here is about measures, and the
    header says where this would rather live: if [BvBase] grows an
    enumeration of [BvBase.byte], delete this one and use it.  It is
    written as [Z_to_bv] over [List.seq] rather than spelled out
    because the three facts wanted of it — its length, that it misses
    nothing, and that it repeats nothing — are then three short
    arguments about [List.seq] instead of a 256-line literal and a
    computation to check it. *)
Definition all_bytes : list byte :=
  List.map (fun n => Z_to_bv 8 (Z.of_nat n)) (List.seq 0 256).

Lemma all_bytes_length : length all_bytes = 256%nat.
Proof.
  unfold all_bytes. rewrite List.length_map, List.length_seq. reflexivity.
Qed.

(** It misses nothing.  A [BvBase.byte] is a [bv 8], whose
    [bv_unsigned] lies in [[0, bv_modulus 8)] — that modulus being
    [256] by conversion — so the byte is [Z_to_bv 8] of a number
    [List.seq 0 256] enumerates, and [Z_to_bv_bv_unsigned] is the
    round trip that says so. *)
Lemma all_bytes_complete : forall b : byte, List.In b all_bytes.
Proof.
  intros b. unfold all_bytes.
  destruct (bv_unsigned_in_range 8 b) as [Hlo Hhi].
  change (bv_modulus 8) with 256%Z in Hhi.
  apply List.in_map_iff. exists (Z.to_nat (bv_unsigned b)). split.
  - rewrite Z2Nat.id by exact Hlo. apply Z_to_bv_bv_unsigned.
  - apply List.in_seq. split; [apply Nat.le_0_l | cbn [Nat.add]; lia].
Qed.

(** Mapping an injective function over a duplicate-free list leaves it
    duplicate-free.  [Stdlib] ships [List.NoDup_map_inv], which is the
    other direction; this one is what a list built by [List.map] needs.
    Injectivity is asked for only ON THE LIST, which is what makes it
    usable for [Z_to_bv 8 (Z.of_nat _)] — a function injective on
    [[0, 256)] and on nothing wider. *)
Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, List.In x l -> List.In y l -> f x = f y -> x = y) ->
  List.NoDup l -> List.NoDup (List.map f l).
Proof.
  intros A B f l. induction l as [| x l IH]; intros Hinj Hnd.
  - cbn [List.map]. apply List.NoDup_nil.
  - cbn [List.map].
    apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd as [Hnin Hnd].
    apply List.NoDup_cons.
    + intros Hin. apply List.in_map_iff in Hin as [y [Hfy Hiny]].
      apply Hnin. rewrite (Hinj x y (or_introl eq_refl) (or_intror Hiny)
                             (eq_sym Hfy)). exact Hiny.
    + apply IH; [| exact Hnd].
      intros y z Hy Hz. apply Hinj; right; assumption.
Qed.

(** ... and it repeats nothing: below [256] the round trip through
    [bv_unsigned] is the identity ([Z_to_bv_small]), so the map is
    injective on [List.seq 0 256], which [List.seq_NoDup] hands over
    duplicate-free. *)
Lemma all_bytes_nodup : List.NoDup all_bytes.
Proof.
  unfold all_bytes. apply NoDup_map_inj; [| apply List.seq_NoDup].
  intros x y Hx Hy Heq.
  apply List.in_seq in Hx. apply List.in_seq in Hy. cbn [Nat.add] in Hx, Hy.
  apply (f_equal (@bv_unsigned 8)) in Heq.
  rewrite !Z_to_bv_small in Heq.
  - apply Nat2Z.inj. exact Heq.
  - change (bv_modulus 8) with 256%Z. lia.
  - change (bv_modulus 8) with 256%Z. lia.
Qed.

(** Every byte list of length [n], as a list of [256 ^ n] of them.
    This is the object the counting lemma counts against: an explicit
    finite enumeration, so that "there are at most [256 ^ n] of these"
    is [List.NoDup_incl_length] against a list whose length is known,
    rather than a cardinality argument about a type. *)
Fixpoint byte_lists (n : nat) : list (list byte) :=
  match n with
  | O => [[]]
  | S n' => List.flat_map (fun b => List.map (cons b) (byte_lists n')) all_bytes
  end.

(** The length of a [List.flat_map] whose blocks all have the same
    size.  [Stdlib] has [List.length_concat] over a sum of lengths;
    when every block is the same size the sum is a product, and that is
    the shape [byte_lists] produces. *)
Lemma length_flat_map_const :
  forall (A B : Type) (f : A -> list B) (l : list A) (c : nat),
    (forall x, List.In x l -> length (f x) = c) ->
    length (List.flat_map f l) = (length l * c)%nat.
Proof.
  intros A B f l c. induction l as [| x l IH]; intros Hc; [reflexivity |].
  cbn [List.flat_map length]. rewrite List.length_app.
  rewrite (Hc x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply Hc; right; exact Hy).
  reflexivity.
Qed.

Lemma byte_lists_length : forall n, length (byte_lists n) = (256 ^ n)%nat.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [byte_lists].
  rewrite (length_flat_map_const _ _ _ _ (256 ^ n)%nat)
    by (intros b _; rewrite List.length_map; exact IH).
  rewrite all_bytes_length. reflexivity.
Qed.

(** ... and none is missing.  Stated at [length l] rather than at an
    arbitrary [n] equal to it, so that the induction on [l] needs no
    generalization; the [n]-shaped form is one [subst] away and is
    taken at the single use site. *)
Lemma byte_lists_complete : forall l : list byte,
  List.In l (byte_lists (length l)).
Proof.
  induction l as [| b l IH]; [left; reflexivity |].
  cbn [length byte_lists]. apply List.in_flat_map.
  exists b. split; [apply all_bytes_complete |].
  apply List.in_map. exact IH.
Qed.

(** ... and nothing longer or shorter has crept in: the enumeration at
    [n] holds only length-[n] lists.  Needed because a witness list
    BUILT from [byte_lists n] has to satisfy the counting lemma's own
    length hypothesis, and that hypothesis is about its members. *)
Lemma byte_lists_In_length : forall n s,
  List.In s (byte_lists n) -> length s = n.
Proof.
  induction n as [| n IH]; intros s Hs.
  - destruct Hs as [Hs | []]. rewrite <- Hs. reflexivity.
  - cbn [byte_lists] in Hs. apply List.in_flat_map in Hs as [b [_ Hs]].
    apply List.in_map_iff in Hs as [s' [Hs' Hin]]. rewrite <- Hs'.
    cbn [length]. rewrite (IH s' Hin). reflexivity.
Qed.

(** [List.NoDup] through a [List.flat_map].  [Stdlib] ships nothing for
    this — [List.NoDup_app] is as far as it goes — so the three
    conditions are spelled out: the index list is duplicate-free, each
    block is, and no element lands in two blocks.  The third is what
    the second and third arguments of [List.NoDup_app] need at each
    step, and it is the one a caller has to think about.

    Stated generically rather than inlined into [byte_lists_nodup]
    because the shape recurs: [cyl_enum] is a [List.flat_map] of the
    same kind, and a later task wanting its duplicate-freedom (this
    file deliberately never needs it — see [qsum_core_incl_le])
    would otherwise write this again. *)
Lemma NoDup_flat_map : forall (A B : Type) (f : A -> list B) (l : list A),
  List.NoDup l ->
  (forall x, List.In x l -> List.NoDup (f x)) ->
  (forall x y b, List.In x l -> List.In y l ->
     List.In b (f x) -> List.In b (f y) -> x = y) ->
  List.NoDup (List.flat_map f l).
Proof.
  intros A B f l. induction l as [| x l IH]; intros Hnd Hblk Hdisj.
  - apply List.NoDup_nil.
  - cbn [List.flat_map].
    apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd as [Hnin Hnd].
    apply List.NoDup_app.
    + apply Hblk. left. reflexivity.
    + apply IH.
      * exact Hnd.
      * intros y Hy. apply Hblk. right. exact Hy.
      * intros y z b Hy Hz Hby Hbz.
        apply (Hdisj y z b (or_intror Hy) (or_intror Hz) Hby Hbz).
    + intros b Hbx Hbrest.
      apply List.in_flat_map in Hbrest as [y [Hy Hby]].
      apply Hnin.
      rewrite (Hdisj x y b (or_introl eq_refl) (or_intror Hy) Hbx Hby).
      exact Hy.
Qed.

(** ... and the enumeration repeats nothing.  Distinct first bytes give
    disjoint blocks — that is the whole content of the third condition
    here — and within a block the induction hypothesis carries over
    through [cons], which is injective.

    This is what a witness list of the FULL size [256 ^ n] needs, and
    it is the only thing that was missing:
    [injective_core_list_in_cylinder_length_bound_attained] is proved
    at every [n] with it and could not be proved at any [n] but the
    trivial ones without it. *)
Lemma byte_lists_nodup : forall n, List.NoDup (byte_lists n).
Proof.
  induction n as [| n IH].
  - cbn [byte_lists].
    apply List.NoDup_cons; [intros H; exact H | apply List.NoDup_nil].
  - cbn [byte_lists]. apply NoDup_flat_map.
    + apply all_bytes_nodup.
    + intros b _. apply NoDup_map_inj; [| exact IH].
      intros x y _ _ Heq. injection Heq as Heq. exact Heq.
    + intros x y bs _ _ Hx Hy.
      apply List.in_map_iff in Hx as [lx [Hlx _]].
      apply List.in_map_iff in Hy as [ly [Hly _]].
      rewrite <- Hly in Hlx. injection Hlx as Hxy _. exact Hxy.
Qed.

(* =========================================================================
   Sums over inclusions, concatenations and filters
   ========================================================================= *)

(** A POSITIVE sum has a positive member, which is the direction
    a non-vacuity argument needs, the companion of [qsum_nonneg].  A
    lemma of the shape "some admissible
    list weighs at least [1 - eps]" is worth exactly as much as the
    reasons a list could have for satisfying it, so the certificates
    below are followed by pins that read a positive WEIGHT back out of a
    positive SUM — the empty list and every list of cores the
    distribution weighs zero are then excluded by the statement itself
    rather than by a reader's confidence.

    Constructive, and the decision is [Qlt_le_dec] at one core at a
    time: either the head weighs something, or it weighs zero — its
    weight is nonnegative and not positive — and the tail carries the
    whole sum. *)
Lemma qsum_positive_member : forall {A : Type} (w : A -> Q) cs,
  (forall c, (0 <= w c)%Q) -> (0 < qsum w cs)%Q ->
  exists c, List.In c cs /\ (0 < w c)%Q.
Proof.
  intros A w cs Hw. induction cs as [| c cs IH]; intros Hpos.
  - rewrite qsum_nil in Hpos. exfalso. exact (Qlt_irrefl 0 Hpos).
  - rewrite qsum_cons in Hpos.
    destruct (Qlt_le_dec 0 (w c)) as [Hc | Hc].
    + exists c. split; [left; reflexivity | exact Hc].
    + assert (Hz : (w c == 0)%Q) by (apply Qle_antisym; [exact Hc | apply Hw]).
      assert (Hrest : (0 < qsum w cs)%Q).
      { rewrite Hz in Hpos.
        apply (Qlt_le_trans _ (0 + qsum w cs)%Q);
          [exact Hpos | apply Qle_of_Qeq; ring]. }
      destruct (IH Hrest) as [c' [Hin Hc']].
      exists c'. split; [right; exact Hin | exact Hc'].
Qed.

(** Removing ONE occurrence of a core from a list.  [List.remove]
    removes every occurrence, and that difference is the whole point:
    the sum lemma below is then an exact [Qeq] with NO duplicate-
    freedom hypothesis on the list, which is what lets
    [qsum_core_incl_le] bound a sum by a sum over a list nobody has
    proved duplicate-free. *)
Fixpoint core_remove_one (c : FinCore) (cs : list FinCore) : list FinCore :=
  match cs with
  | [] => []
  | x :: rest => if decide (c = x) then rest else x :: core_remove_one c rest
  end.

Lemma qsum_core_remove_one : forall (w : FinCore -> Q) c cs,
  List.In c cs ->
  (qsum w cs == w c + qsum w (core_remove_one c cs))%Q.
Proof.
  intros w c cs. induction cs as [| x cs IH]; intros Hin; [destruct Hin |].
  cbn [core_remove_one]. destruct (decide (c = x)) as [Heq | Hne].
  - subst x. rewrite qsum_cons. reflexivity.
  - rewrite !qsum_cons.
    destruct Hin as [Hx | Hin]; [congruence |].
    rewrite (IH Hin). ring.
Qed.

(** Everything else survives the removal. *)
Lemma In_core_remove_one : forall c x cs,
  List.In x cs -> x <> c -> List.In x (core_remove_one c cs).
Proof.
  intros c x cs. induction cs as [| y cs IH]; intros Hin Hne; [destruct Hin |].
  cbn [core_remove_one]. destruct (decide (c = y)) as [Heq | Hney].
  - subst y. destruct Hin as [Hx | Hin]; [congruence | exact Hin].
  - destruct Hin as [Hx | Hin]; [left; exact Hx | right; apply IH; assumption].
Qed.

(** THE MONOTONICITY THE CYLINDER BOUND RUNS ON: a duplicate-free list
    of cores sums to at most what any list containing it sums to.

    The induction peels the head [c], removes one occurrence of it from
    the containing list, and recurses; duplicate-freedom of the SMALL
    list is what makes the tail still included in the remainder, and it
    is the only place the hypothesis is used.  Nothing is asked of the
    containing list — it may repeat, and each repeat only makes its sum
    larger, which is why [cyl_enum] below is never proved
    [List.NoDup].

    Nonnegativity of the weight is genuinely needed and not decoration:
    the empty list already refutes the statement without it. *)
Lemma qsum_core_incl_le : forall (w : FinCore -> Q) cs ys,
  (forall c, (0 <= w c)%Q) -> List.NoDup cs -> List.incl cs ys ->
  (qsum w cs <= qsum w ys)%Q.
Proof.
  intros w cs. induction cs as [| c cs IH]; intros ys Hw Hnd Hincl.
  - rewrite qsum_nil. apply qsum_nonneg. intros c _. apply Hw.
  - apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd as [Hnin Hnd].
    assert (Hc : List.In c ys) by (apply Hincl; left; reflexivity).
    rewrite (qsum_core_remove_one w c ys Hc), qsum_cons.
    apply Qplus_le_compat; [apply Qle_refl |].
    apply IH; [exact Hw | exact Hnd |].
    intros x Hx. apply In_core_remove_one.
    + apply Hincl. right. exact Hx.
    + intros Hxc. subst x. exact (Hnin Hx).
Qed.

(** A [List.flat_map] of uniformly bounded blocks is bounded by the
    count of blocks times the bound.  This is the step that turns "each
    of the 256 continuations carries at most [m]" into "the 256 of them
    carry at most [256 * m]". *)
Lemma qsum_flat_map_const_le :
  forall {A B : Type} (w : B -> Q) (f : A -> list B) (l : list A) (C : Q),
    (forall x, List.In x l -> (qsum w (f x) <= C)%Q) ->
    (qsum w (List.flat_map f l) <= Qnat (length l) * C)%Q.
Proof.
  intros A B w f l C. induction l as [| x l IH]; intros Hb.
  - cbn [List.flat_map length]. rewrite qsum_nil, Qnat_0.
    rewrite Qmult_0_l. apply Qle_refl.
  - cbn [List.flat_map length]. rewrite qsum_app.
    apply (Qle_trans _ (C + Qnat (length l) * C)).
    + apply Qplus_le_compat.
      * apply Hb. left. reflexivity.
      * apply IH. intros y Hy. apply Hb. right. exact Hy.
    + rewrite Qnat_succ. apply Qle_of_Qeq. ring.
Qed.

(** A list on which the weight is constant sums to the count times the
    constant — the other half of the length-slice bound, where the
    counting lemma supplies the count. *)
Lemma qsum_const : forall {A : Type} (w : A -> Q) cs (C : Q),
  (forall c, List.In c cs -> (w c == C)%Q) ->
  (qsum w cs == Qnat (length cs) * C)%Q.
Proof.
  intros A w cs C. induction cs as [| c cs IH]; intros Hc.
  - cbn [length]. rewrite qsum_nil, Qnat_0. ring.
  - cbn [length]. rewrite qsum_cons, Qnat_succ.
    rewrite (Hc c (or_introl eq_refl)).
    rewrite IH by (intros x Hx; apply Hc; right; exact Hx).
    ring.
Qed.

(** Elements the weight ignores can be dropped.  Together with
    [List.NoDup_filter] this is what lets a bound proved for lists
    INSIDE a region be applied to a list that merely happens to weigh
    zero outside it — the step from the cylinder bound to the
    whole-space certificate. *)
Lemma qsum_filter : forall {A : Type} (w : A -> Q) (P : A -> bool) cs,
  (forall c, P c = false -> (w c == 0)%Q) ->
  (qsum w cs == qsum w (List.filter P cs))%Q.
Proof.
  intros A w P cs Hz. induction cs as [| c cs IH]; [reflexivity |].
  cbn [List.filter]. destruct (P c) eqn:HP.
  - rewrite !qsum_cons, IH. reflexivity.
  - rewrite qsum_cons, (Hz c HP), IH. ring.
Qed.

(** [List.list_max] bounds every member.  [Stdlib] states the
    equivalence [List.list_max_le] and not this consequence of it. *)
Lemma list_max_ge : forall l n, List.In n l -> (n <= List.list_max l)%nat.
Proof.
  intros l n Hin.
  assert (H := proj1 (List.list_max_le l (List.list_max l)) (Nat.le_refl _)).
  rewrite List.Forall_forall in H. apply H. exact Hin.
Qed.

(* =========================================================================
   THE COUNTING LEMMA
   ========================================================================= *)

(** A list of records with duplicate-free CORES, every core matching
    fixed argv, envp and file system and carrying standard input of
    length exactly [n], has at most [256 ^ n] elements.

    This is the fact the geometric distribution's bounds are built out
    of, and the reason it can be stated at all is the quotient:
    [Measure.weight_bound_T] reads duplicate-freedom on
    [FinInput.fin_core], so the list's records inject into their cores,
    and a core matching the fixed environment is determined by its
    standard input alone.  Length-[n] byte lists are enumerated by
    [byte_lists n], there are [256 ^ n] of them, and
    [List.NoDup_incl_length] converts the injection into the bound.

    The environment hypothesis is written as a single equation —
    [fin_core f = mkFinCore argv envp fs (fin_stdin f)] — rather than
    as three field equations, because that is the form the injection
    consumes directly and the form [geo_weight] below decides on.

    Read the hypothesis as: the list is a duplicate-free sample from
    ONE length slice of ONE launch-time environment.  Nothing is
    claimed about lists that mix slices; that is what
    [stdin_geometric_bound] is for, and it is proved a different
    way. *)
Lemma injective_core_list_in_cylinder_length_bound :
  forall (argv envp : list (list byte)) (fs : Fs.Fs) (n : nat)
         (l : list FinProcInput),
    List.NoDup (List.map fin_core l) ->
    (forall f, List.In f l ->
       fin_core f = mkFinCore argv envp fs (fin_stdin f)
       /\ length (fin_stdin f) = n) ->
    (length l <= 256 ^ n)%nat.
Proof.
  intros argv envp fs n l Hnd Hall.
  assert (Hle : (length (List.map fin_core l)
                 <= length (List.map (mkFinCore argv envp fs)
                              (byte_lists n)))%nat).
  { apply List.NoDup_incl_length; [exact Hnd |].
    intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
    destruct (Hall f Hin) as [Henv Hlen].
    apply List.in_map_iff. exists (fin_stdin f). split.
    - rewrite <- Henv. exact Hf.
    - rewrite <- Hlen. apply byte_lists_complete. }
  rewrite !List.length_map, byte_lists_length in Hle. exact Hle.
Qed.

(** THE BOUND IS ATTAINED AT EVERY [n], so [256 ^ n] is the right
    constant and not merely a true one: over any launch-time
    environment at all there is an admissible list of exactly [256 ^ n]
    records, one per length-[n] standard input.

    It is [byte_lists n] wrapped by [core_input], and the proof is
    symbolic throughout — [byte_lists_length] for the count,
    [byte_lists_nodup] through [NoDup_map_inj] for the duplicate
    freedom, [byte_lists_In_length] for the length hypothesis.  NOTHING
    IS EVER COMPUTED: [byte_lists n] stays a [List.flat_map] term, so
    the witness at [n = 2] costs exactly what the witness at [n = 1]
    costs, which is nothing.  (An earlier version of this lemma was
    stated at [n = 1] and blamed compile time for it.  That reason was
    false twice over: nothing reduces here, and the real obstruction
    was that [byte_lists_nodup] had not been proved.) *)
Lemma injective_core_list_in_cylinder_length_bound_attained :
  forall (argv envp : list (list byte)) (fs : Fs.Fs) (n : nat),
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (forall f, List.In f l ->
          fin_core f = mkFinCore argv envp fs (fin_stdin f)
          /\ length (fin_stdin f) = n)
    /\ length l = (256 ^ n)%nat.
Proof.
  intros argv envp fs n.
  exists (List.map (fun s => core_input (mkFinCore argv envp fs s))
            (byte_lists n)).
  split; [| split].
  - rewrite List.map_map.
    rewrite (List.map_ext _ (fun s => mkFinCore argv envp fs s))
      by (intros s; apply fin_core_core_input).
    apply NoDup_map_inj; [| apply byte_lists_nodup].
    intros x y _ _ Heq. apply (f_equal core_stdin) in Heq. exact Heq.
  - intros f Hf. apply List.in_map_iff in Hf as [s [Hs Hin]]. subst f.
    split; [rewrite fin_core_core_input; reflexivity |].
    cbn [core_input fin_stdin]. apply byte_lists_In_length. exact Hin.
  - rewrite List.length_map, byte_lists_length. reflexivity.
Qed.

(* =========================================================================
   Combinator: geometric standard input over a fixed environment
   ========================================================================= *)

(** The mass of the cylinder over a prefix of length [n], and the
    weight of a single core whose standard input has length [n].  Both
    are powers of ONE ratio, [(1 - p_stop) * (1 # 256)]: stopping costs
    a factor [p_stop], continuing costs [1 - p_stop] and choosing the
    next byte costs [1 # 256].  The plan's three-factor form is
    recovered below by [Qpow_mult] and is a lemma rather than a rival
    definition — see the header. *)
Definition geo_mass (p : Q) (n : nat) : Q := Qpow ((1 - p) * (1 # 256)) n.

Definition geo_point (p : Q) (n : nat) : Q := (p * geo_mass p n)%Q.

Lemma geo_mass_closed_form : forall p n,
  (geo_mass p n == Qpow (1 - p) n * Qpow (1 # 256) n)%Q.
Proof. intros p n. apply Qpow_mult. Qed.

Lemma geo_point_closed_form : forall p n,
  (geo_point p n == p * Qpow (1 - p) n * Qpow (1 # 256) n)%Q.
Proof. intros p n. unfold geo_point. rewrite geo_mass_closed_form. ring. Qed.

(** The ratio is nonnegative exactly when [p_stop <= 1], which is where
    the second side condition comes from and the only thing it is
    for. *)
Lemma geo_ratio_nonneg : forall p, (p <= 1)%Q -> (0 <= (1 - p) * (1 # 256))%Q.
Proof.
  intros p Hp1. apply Qmult_le_0_compat; [| exact Qle_0_inv_256].
  apply (Qle_minus_iff p 1). exact Hp1.
Qed.

Lemma geo_mass_nonneg : forall p n, (p <= 1)%Q -> (0 <= geo_mass p n)%Q.
Proof. intros p n Hp1. apply Qpow_nonneg, geo_ratio_nonneg, Hp1. Qed.

Lemma geo_point_nonneg : forall p n,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= geo_point p n)%Q.
Proof.
  intros p n Hp0 Hp1. apply Qmult_le_0_compat; [exact Hp0 |].
  apply geo_mass_nonneg, Hp1.
Qed.

(** A single core weighs at most the mass of the cylinder it sits at
    the tip of, because [p_stop <= 1].  This is the base case of the
    cylinder induction: a cylinder with no room to continue holds only
    its own stopping core. *)
Lemma geo_point_le_mass : forall p n,
  (p <= 1)%Q -> (geo_point p n <= geo_mass p n)%Q.
Proof.
  intros p n Hp1. unfold geo_point.
  rewrite <- (Qmult_1_l (geo_mass p n)) at 2.
  apply Qmult_le_compat_r; [exact Hp1 | apply geo_mass_nonneg, Hp1].
Qed.

(** THE WEIGHT.  Zero unless the core's argv, envp and file system are
    the fixed ones; otherwise the geometric weight of its
    standard-input length.

    The environment test is one decidable equation, "the core is the
    template with its own standard input plugged in", rather than three
    field tests conjoined.  That is not brevity: the three-way version
    would need [decide] over a conjunction, and this version is exactly
    the hypothesis the counting lemma above already carries, so no
    translation step stands between them. *)
Definition geo_weight (p : Q) (argv envp : list (list byte)) (fs : Fs.Fs)
    (c : FinCore) : Q :=
  if decide (c = mkFinCore argv envp fs (core_stdin c))
  then geo_point p (length (core_stdin c))
  else 0%Q.

(** Its two values, as rewrite rules, so that no proof below names
    [decide] or the [FinCore_eq_dec] instance. *)
Lemma geo_weight_match : forall p argv envp fs s,
  geo_weight p argv envp fs (mkFinCore argv envp fs s)
    = geo_point p (length s).
Proof.
  intros p argv envp fs s. unfold geo_weight. cbn [core_stdin].
  destruct (decide _) as [_ | Hne]; [reflexivity | congruence].
Qed.

Lemma geo_weight_mismatch : forall p argv envp fs c,
  c <> mkFinCore argv envp fs (core_stdin c) ->
  geo_weight p argv envp fs c = 0%Q.
Proof.
  intros p argv envp fs c Hne. unfold geo_weight.
  destruct (decide _) as [Heq | _]; [congruence | reflexivity].
Qed.

Lemma geo_weight_nonneg : forall p argv envp fs,
  (0 <= p)%Q -> (p <= 1)%Q -> forall c, (0 <= geo_weight p argv envp fs c)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 c. unfold geo_weight.
  destruct (decide _) as [_ | _]; [apply geo_point_nonneg; assumption
                                  | apply Qle_refl].
Qed.

(** The distribution.  Mass [1] is DECLARED, exactly as [Measure]'s
    header says every [M] is — nothing is proved by writing it, and
    [stdin_geometric_mass_upper] below is the proof that owes something
    to it.  The two side conditions are arguments for the same reason
    [finite_support]'s nonnegativity proof is: [cd_nonneg] is a field,
    and a constructor that returned one without a proof would have to
    invent it.  See the header for why [0 < p_stop] is NOT among
    them. *)
Definition stdin_geometric (p : Q) (argv envp : list (list byte)) (fs : Fs.Fs)
    (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q) : CoreDistribution :=
  mkCoreDistribution (geo_weight p argv envp fs) 1
    (geo_weight_nonneg p argv envp fs Hp0 Hp1).

(** [Measure.DISTRIBUTION]'s [M_nonneg] here is [0 <= 1] on the numeral
    the constructor writes, decided by [Qle_bool] on literal operands —
    the exception the header documents.  It is stated rather than left
    to the caller so that a distribution assembled from combinators can
    discharge the obligation without any arithmetic at the site. *)
Lemma stdin_geometric_mass_nonneg : forall p argv envp fs Hp0 Hp1,
  (0 <= cd_mass (stdin_geometric p argv envp fs Hp0 Hp1))%Q.
Proof.
  intros p argv envp fs Hp0 Hp1. cbn [cd_mass stdin_geometric].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(* =========================================================================
   The prefix cylinder, and the enumeration that bounds it
   ========================================================================= *)

(** The cores this bound is about: the fixed environment, and standard
    input EXTENDING [bs].  One existential rather than a conjunction of
    an environment test and a prefix test, for the same reason
    [geo_weight]'s test is one equation — it is the form both the
    construction and the enumeration want. *)
Definition in_stdin_cylinder (argv envp : list (list byte)) (fs : Fs.Fs)
    (bs : list byte) (c : FinCore) : Prop :=
  exists ext, c = mkFinCore argv envp fs (bs ++ ext).

(** Every core in the cylinder over [bs] whose standard input exceeds
    [bs] by at most [N] bytes, as a list: the stopping core, then for
    each byte the enumeration of the cylinder one byte deeper.  It
    recurses on [N], which is what makes it a [Fixpoint] at all —
    [bs] grows.

    Duplicate-freedom of this list is never proved and never needed:
    [qsum_core_incl_le] asks nothing of the list it bounds
    against. *)
Fixpoint cyl_enum (argv envp : list (list byte)) (fs : Fs.Fs)
    (bs : list byte) (N : nat) : list FinCore :=
  match N with
  | O => [mkFinCore argv envp fs bs]
  | S N' => mkFinCore argv envp fs bs
            :: List.flat_map (fun b => cyl_enum argv envp fs (bs ++ [b]) N')
                 all_bytes
  end.

(** It misses nothing within its depth. *)
Lemma cyl_enum_complete : forall argv envp fs N bs ext,
  (length ext <= N)%nat ->
  List.In (mkFinCore argv envp fs (bs ++ ext)) (cyl_enum argv envp fs bs N).
Proof.
  intros argv envp fs N. induction N as [| N IH]; intros bs ext Hlen.
  - destruct ext as [| b ext]; [| cbn [length] in Hlen; lia].
    rewrite List.app_nil_r. left. reflexivity.
  - destruct ext as [| b ext].
    + rewrite List.app_nil_r. left. reflexivity.
    + right. apply List.in_flat_map. exists b.
      split; [apply all_bytes_complete |].
      replace (bs ++ b :: ext) with ((bs ++ [b]) ++ ext)
        by (rewrite <- List.app_assoc; reflexivity).
      apply IH. cbn [length] in Hlen. lia.
Qed.

(** THE CANCELLATION, by induction on the depth: the whole enumeration
    weighs no more than the cylinder mass, at every depth and every
    prefix.

    The step is exact rather than lossy, which is why the constant
    below is the right one.  The stopping core contributes
    [p_stop * m], where [m] is the cylinder's mass; each of the 256
    continuations contributes at most the mass of a cylinder one byte
    deeper, which is [(1 - p_stop) * (1/256) * m]; and
    [p_stop + 256 * (1 - p_stop) * (1/256)] is [1] exactly.  [ring]
    does that last arithmetic, including folding [256 * (1 # 256)] to
    [1] — the constants are literals this file wrote, and no [Q]
    relation is decided by computation.

    The base case is the one place [p_stop <= 1] is spent for anything
    other than nonnegativity: a depth-zero cylinder holds only its
    stopping core, which weighs [p_stop * m] and must be under [m]. *)
Lemma cyl_enum_sum_le : forall p argv envp fs,
  (0 <= p)%Q -> (p <= 1)%Q ->
  forall N bs,
    (qsum (geo_weight p argv envp fs) (cyl_enum argv envp fs bs N)
       <= geo_mass p (length bs))%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 N. induction N as [| N IH]; intros bs.
  - cbn [cyl_enum]. rewrite qsum_cons, qsum_nil.
    rewrite geo_weight_match, Qplus_0_r.
    apply geo_point_le_mass, Hp1.
  - cbn [cyl_enum]. rewrite qsum_cons, geo_weight_match.
    eapply Qle_trans.
    + apply Qplus_le_compat; [apply Qle_refl |].
      apply (qsum_flat_map_const_le _ _ _ (geo_mass p (S (length bs)))).
      intros b _. eapply Qle_trans; [apply IH |].
      rewrite List.length_app. cbn [length]. rewrite Nat.add_1_r.
      apply Qle_refl.
    + rewrite all_bytes_length, Qnat_256.
      apply Qle_of_Qeq.
      unfold geo_point, geo_mass. rewrite Qpow_succ. ring.
Qed.

(** The bound over CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.

    The depth to enumerate to is read off the list — the largest
    standard-input length occurring in it — which is where the
    finiteness of [Measure.weight_bound_T]'s lists is spent, and the
    only place it is needed.  A core whose standard input is
    [bs ++ ext] has length at least that of [ext], so bounding the
    lengths bounds the depths. *)
Lemma geo_weight_cylinder_bound : forall p argv envp fs,
  (0 <= p)%Q -> (p <= 1)%Q ->
  forall bs cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> in_stdin_cylinder argv envp fs bs c) ->
    (qsum (geo_weight p argv envp fs) cs
       <= geo_mass p (length bs))%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 bs cs Hnd Hcyl.
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (cyl_enum argv envp fs bs
                  (List.list_max (List.map (fun c => length (core_stdin c)) cs))))
    | apply cyl_enum_sum_le; assumption ].
  - apply geo_weight_nonneg; assumption.
  - exact Hnd.
  - intros c Hc. destruct (Hcyl c Hc) as [ext Hext].
    rewrite Hext. apply cyl_enum_complete.
    assert (Hin : List.In (length (core_stdin c))
                    (List.map (fun c => length (core_stdin c)) cs)).
    { apply List.in_map_iff. exists c. split; [reflexivity | exact Hc]. }
    apply list_max_ge in Hin.
    rewrite Hext in Hin. cbn [core_stdin] in Hin.
    rewrite List.length_app in Hin. lia.
Qed.

(* =========================================================================
   The three exports
   ========================================================================= *)

(** The cylinder's mass, in closed form: a power of the ratio, which is
    the product of the two powers the plan quotes. *)
Definition stdin_geometric_cylinder_mass (p : Q) (bs : list byte) : Q :=
  geo_mass p (length bs).

Lemma stdin_geometric_cylinder_mass_closed_form : forall p bs,
  (stdin_geometric_cylinder_mass p bs
     == Qpow (1 - p) (length bs) * Qpow (1 # 256) (length bs))%Q.
Proof. intros p bs. apply geo_mass_closed_form. Qed.

(** THE EXPORT: a list of records with duplicate-free cores, all lying
    in the cylinder over [bs], weighs at most that cylinder's mass.
    The hypothesis is the one [Measure.weight_bound_T] carries, and
    [core_sum_map_fin_core] is the only step between them. *)
Lemma stdin_geometric_bound : forall p argv envp fs Hp0 Hp1 bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> in_stdin_cylinder argv envp fs bs (fin_core f)) ->
  (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
     <= stdin_geometric_cylinder_mass p bs)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 bs l Hnd Hcyl.
  cbn [cd_weight stdin_geometric]. rewrite core_sum_map_fin_core.
  apply geo_weight_cylinder_bound; [exact Hp0 | exact Hp1 | exact Hnd |].
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. apply Hcyl. exact Hin.
Qed.

(** The environment test as a boolean, so that [List.filter] can use
    it.  [Measure]'s [Qle_bool] exception is not in play here: this
    decides an equality of CORES, which [FinCore_eq_dec] decides
    outright, and no rational is involved. *)
Definition matches_env (argv envp : list (list byte)) (fs : Fs.Fs)
    (c : FinCore) : bool :=
  if decide (c = mkFinCore argv envp fs (core_stdin c)) then true else false.

Lemma matches_env_false : forall argv envp fs c,
  matches_env argv envp fs c = false ->
  c <> mkFinCore argv envp fs (core_stdin c).
Proof.
  intros argv envp fs c H. unfold matches_env in H.
  destruct (decide _) as [_ | Hne]; [discriminate | exact Hne].
Qed.

Lemma matches_env_true : forall argv envp fs c,
  matches_env argv envp fs c = true ->
  c = mkFinCore argv envp fs (core_stdin c).
Proof.
  intros argv envp fs c H. unfold matches_env in H.
  destruct (decide _) as [Heq | _]; [exact Heq | discriminate].
Qed.

(** THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE: each record
    is in the cylinder OR its core misses the fixed environment
    entirely.

    [stdin_geometric_bound] cannot be weakened to drop the membership
    requirement — a core that matches the environment but whose
    standard input leaves the cylinder has positive weight and refutes
    it.  What CAN be added is the one class of cores that is harmless
    because it weighs nothing, and this is that statement.  It is a
    strict generalization of [stdin_geometric_bound] (take the left
    disjunct everywhere) and both are exported: the membership form is
    what a task proves when its whole fire set is inside one cylinder,
    the disjunctive form is what it proves when the fire set was
    described some other way and merely happens to miss the
    environment elsewhere.

    Without this export every consumer re-derives the same repair —
    filter on [matches_env], discharge the dropped terms through
    [geo_weight_mismatch], carry [List.NoDup] across with
    [List.NoDup_filter], observe that a surviving core must have taken
    the left disjunct.  That is a dozen lines and none of them is
    obvious; a library that leaves it to the caller has exported the
    hard half and kept the easy one. *)
Lemma stdin_geometric_bound_or_off_environment :
  forall p argv envp fs Hp0 Hp1 bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_stdin_cylinder argv envp fs bs (fin_core f)
     \/ matches_env argv envp fs (fin_core f) = false) ->
  (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
     <= stdin_geometric_cylinder_mass p bs)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 bs l Hnd Hor.
  cbn [cd_weight stdin_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_env argv envp fs))
    by (intros c Hc; rewrite (geo_weight_mismatch p argv envp fs c
                                (matches_env_false _ _ _ _ Hc)); reflexivity).
  unfold stdin_geometric_cylinder_mass.
  apply geo_weight_cylinder_bound; [exact Hp0 | exact Hp1 | |].
  - apply List.NoDup_filter. exact Hnd.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (Hor f Hinl) as [Hcyl | Hoff].
    + rewrite <- Hf. exact Hcyl.
    + rewrite Hf in Hoff. rewrite Hoff in Hm. discriminate.
Qed.

(** UPPER CERTIFICATE: every admissible list weighs at most the
    declared mass [1].  This is the whole-space form the plan allowed
    to be deferred; it is not deferred.

    With the disjunctive bound in hand it is that bound at the EMPTY
    prefix, and the whole content is the observation that the
    disjunction is EXHAUSTIVE there: a core either matches the fixed
    launch-time environment — in which case its standard input is
    [[] ++ itself], so it is in the cylinder over [[]] — or it does
    not, which is the right disjunct.  Nothing is assumed about the
    list beyond [Measure.weight_bound_T]'s own [List.NoDup].  The
    cylinder mass over the empty prefix is [1] because [Qpow] at
    exponent zero is, definitionally.

    The LOWER certificate is [stdin_geometric_mass_lower_certificate]
    below, and note what it does NOT say: not that some admissible list
    reaches [1] — none does for [p_stop < 1], which is
    [stdin_geometric_mass_not_attained] and not a remark — but that
    lists come arbitrarily close.  It is the statement that needs
    [0 < p_stop], and this one does not. *)
Lemma stdin_geometric_mass_upper : forall p argv envp fs Hp0 Hp1 l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
     <= cd_mass (stdin_geometric p argv envp fs Hp0 Hp1))%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 l Hnd.
  cbn [cd_mass stdin_geometric].
  change 1%Q with (stdin_geometric_cylinder_mass p []).
  apply stdin_geometric_bound_or_off_environment; [exact Hnd |].
  intros f Hf. destruct (matches_env argv envp fs (fin_core f)) eqn:Hm.
  - left. exists (core_stdin (fin_core f)). cbn [List.app].
    apply matches_env_true. exact Hm.
  - right. reflexivity.
Qed.

(** THE LENGTH SLICE: a list drawn from one length slice weighs at most
    [p_stop * (1 - p_stop) ^ n] — the geometric distribution over
    LENGTHS, with no [1/256] left in it.

    This is the counting lemma cashed in, and it is the export that
    shows what the counting is for.  Every core in such a list weighs
    the same, [geo_point p_stop n], so the sum is the LENGTH of the
    list times that; the length is at most [256 ^ n]; and [256 ^ n]
    against the [(1 / 256) ^ n] inside the weight cancels exactly, by
    [Qpow_mult] and [Qpow_1].

    It is a stepping stone to nothing below — the cylinder bound is
    proved by enumeration and does not use it — and is exported because
    a task author summing over inputs of a fixed size wants this
    number, not a cylinder's. *)
(** The cancellation the slice bound turns on, on its own: a FULL
    slice — all [256 ^ n] of it — weighs exactly [p_stop * (1 -
    p_stop) ^ n].  The [256 ^ n] and the [(1 / 256) ^ n] inside each
    weight recombine into [1 ^ n] by [Qpow_mult] and [Qpow_1], with no
    side condition because [Qpow] has none.

    Stated separately because both directions need it: the bound needs
    it to know the constant is right, and
    [stdin_geometric_slice_bound_attained] needs it to know the
    constant is reached.  An identity used once to bound and once to
    attain is exactly the thing not to inline twice. *)
Lemma geo_slice_total : forall p n,
  (Qnat (256 ^ n) * geo_point p n == p * Qpow (1 - p) n)%Q.
Proof.
  intros p n.
  assert (H1 : (Qpow (256 # 1) n * Qpow (1 # 256) n == 1)%Q).
  { rewrite <- Qpow_mult.
    rewrite (Qpow_Qeq ((256 # 1) * (1 # 256)) 1 n) by ring.
    apply Qpow_1. }
  rewrite Qnat_pow_256. unfold geo_point, geo_mass. rewrite Qpow_mult.
  transitivity ((Qpow (256 # 1) n * Qpow (1 # 256) n)
                * (p * Qpow (1 - p) n))%Q; [ring |].
  rewrite H1. ring.
Qed.

Lemma stdin_geometric_slice_bound : forall p argv envp fs Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = mkFinCore argv envp fs (fin_stdin f)
     /\ length (fin_stdin f) = n) ->
  (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
     <= p * Qpow (1 - p) n)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 n l Hnd Hall.
  cbn [cd_weight stdin_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_const _ _ (geo_point p n)).
  2:{ intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
      destruct (Hall f Hin) as [Henv Hlen].
      rewrite <- Hf, Henv, geo_weight_match, Hlen. reflexivity. }
  rewrite <- (geo_slice_total p n).
  apply Qmult_le_compat_r; [| apply geo_point_nonneg; assumption].
  apply Qnat_le. rewrite List.length_map.
  apply (injective_core_list_in_cylinder_length_bound argv envp fs n l);
    assumption.
Qed.

(** THE SLICE BOUND'S CONSTANT IS REACHED, at every [n] and over any
    launch-time environment: the full slice is admissible, and it
    weighs [p_stop * (1 - p_stop) ^ n] exactly.

    This is what the counting lemma's attainability is FOR.  Pinning
    that a duplicate-free slice has at most [256 ^ n] elements says the
    counting is right; pinning that the bound those elements imply is
    reached says the EXPORT is right.  The witness is the counting
    lemma's own — every length-[n] standard input, wrapped — and the
    sum is [qsum_const] (every core in a slice weighs the
    same) followed by [geo_slice_total]. *)
Lemma stdin_geometric_slice_bound_attained :
  forall p argv envp fs Hp0 Hp1 n,
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (forall f, List.In f l ->
          fin_core f = mkFinCore argv envp fs (fin_stdin f)
          /\ length (fin_stdin f) = n)
    /\ (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
          == p * Qpow (1 - p) n)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 n.
  destruct (injective_core_list_in_cylinder_length_bound_attained
              argv envp fs n) as [l [Hnd [Hall Hlen]]].
  exists l. split; [exact Hnd | split; [exact Hall |]].
  cbn [cd_weight stdin_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_const _ _ (geo_point p n)).
  2:{ intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
      destruct (Hall f Hin) as [Henv Hlength].
      rewrite <- Hf, Henv, geo_weight_match, Hlength. reflexivity. }
  rewrite List.length_map, Hlen. apply geo_slice_total.
Qed.

(** ... and so NO SMALLER CONSTANT IS A SLICE BOUND.  Attainment says
    the number is reached; this says it therefore cannot be lowered,
    which is the claim a reader wants and the one that would be false
    if the bound were loose anywhere.  It is the contrapositive shape
    on purpose — quantified over every candidate [K] a future version
    of this file might try to prove instead — so it stays true as a
    regression test rather than as a fact about today's proof. *)
Lemma stdin_geometric_slice_bound_sharp :
  forall p argv envp fs Hp0 Hp1 n K,
  (forall l, List.NoDup (List.map fin_core l) ->
     (forall f, List.In f l ->
        fin_core f = mkFinCore argv envp fs (fin_stdin f)
        /\ length (fin_stdin f) = n) ->
     (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
        <= K)%Q) ->
  (p * Qpow (1 - p) n <= K)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 n K Hbound.
  destruct (stdin_geometric_slice_bound_attained p argv envp fs Hp0 Hp1 n)
    as [l [Hnd [Hall Hsum]]].
  rewrite <- Hsum. apply Hbound; assumption.
Qed.

(* =========================================================================
   Non-vacuity: the weight really vanishes off the fixed environment
   ========================================================================= *)

(** Differing in argv alone is enough to zero the weight — the general
    fact behind the concrete instance below.  Stated on argv because
    that is the field the example varies; envp and the file system go
    the same way, through the same [geo_weight_mismatch]. *)
Lemma geo_weight_off_environment_zero : forall p argv envp fs c,
  core_argv c <> argv -> geo_weight p argv envp fs c = 0%Q.
Proof.
  intros p argv envp fs c Hne. apply geo_weight_mismatch.
  intros Heq. apply (f_equal core_argv) in Heq. cbn [core_argv] in Heq.
  exact (Hne Heq).
Qed.

(** Two cores over the empty launch-time environment: the empty input,
    and one whose argv is not empty.  As at [example_core_empty],
    neither is claimed valid; they are two points of
    [FinInput.FinCore]. *)
Definition geo_example_core : FinCore := mkFinCore [] [] [] [].
Definition geo_example_other : FinCore := mkFinCore [[Z_to_bv 8 65]] [] [] [].

(** THE BITE, both ways: the distribution is not the zero
    distribution — it puts [p_stop] on the empty input, which is
    positive whenever [p_stop] is — and it is not a constant either,
    since a core with the wrong argv weighs exactly zero.  Without the
    second half, "weight zero off the fixed environment" would be a
    claim only the definition makes; without the first, every bound
    above would hold of a distribution that weighs nothing. *)
Lemma stdin_geometric_bites : forall p Hp0 Hp1,
  (0 < p)%Q ->
  (0 < cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) geo_example_core)%Q
  /\ cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) geo_example_other = 0%Q.
Proof.
  intros p Hp0 Hp1 Hlt. cbn [cd_weight stdin_geometric]. split.
  - unfold geo_example_core. rewrite geo_weight_match.
    unfold geo_point, geo_mass. cbn [length Qpow].
    rewrite Qmult_1_r. exact Hlt.
  - apply geo_weight_off_environment_zero.
    unfold geo_example_other. cbn [core_argv]. discriminate.
Qed.

(* =========================================================================
   Non-vacuity: the mass is reached, and [List.NoDup] is load-bearing
   ========================================================================= *)

(** The member of the family at [p_stop = 1]: stop immediately, always.
    It is the point mass on the empty standard input, it is admitted by
    the constructor — [Qle_0_1] and [Qle_refl] are its two side
    conditions — and it is the instance that makes the two bites below
    concrete arithmetic instead of open terms.  It is also why [Qpow]
    exists: its ratio is zero. *)
Definition geo_point_cd : CoreDistribution :=
  stdin_geometric 1 [] [] [] Qle_0_1 (Qle_refl 1).

Definition geo_empty_input : FinProcInput := core_input geo_example_core.

(** The declared mass [1] is not padding at this instance: a
    one-element admissible list reaches it OUTRIGHT.  That is special to
    [p_stop = 1], where the tail past the empty input is empty; the
    general lower certificate ([stdin_geometric_mass_lower_certificate])
    can only approach the mass, and this is the one member of the family
    where approaching and reaching coincide.

    It is also this file's witness that
    [stdin_geometric_mass_not_attained] cannot drop its [p_stop < 1]:
    that lemma says every admissible list weighs strictly less than the
    mass, and the list below refutes it at [p_stop = 1].  A closed
    [Qeq] between literals, decided by computation, per the header's
    exception. *)
Lemma geo_point_cd_mass_attained :
  List.NoDup (List.map fin_core [geo_empty_input])
  /\ (core_sum (cd_weight geo_point_cd) [geo_empty_input]
        == cd_mass geo_point_cd)%Q.
Proof.
  split.
  - cbn [List.map].
    apply List.NoDup_cons; [intros H; exact H | apply List.NoDup_nil].
  - vm_compute. reflexivity.
Qed.

(** THE [List.NoDup] HYPOTHESIS IS LOAD-BEARING for the cylinder bound
    too, and this is [finite_support_bound_needs_nodup] for the
    geometric family: offer the same core twice — two records, so the
    list is duplicate-free as a list of RECORDS, and both records lie
    in the cylinder over the empty prefix — and the sum is [2] against
    a cylinder mass of [1].

    All three conjuncts are needed.  The second says the list really
    does satisfy the cylinder hypothesis, so it is not excluded by
    that; the third says the bound genuinely fails on it; the first
    names what does exclude it.  Without the second a reader could
    suspect the list was ruled out for some other reason, and the
    refutation would say nothing about duplicate-freedom. *)
Lemma stdin_geometric_bound_needs_nodup :
  ~ List.NoDup (List.map fin_core [geo_empty_input; geo_empty_input])
  /\ (forall f, List.In f [geo_empty_input; geo_empty_input] ->
        in_stdin_cylinder [] [] [] [] (fin_core f))
  /\ ~ (core_sum (cd_weight geo_point_cd) [geo_empty_input; geo_empty_input]
          <= stdin_geometric_cylinder_mass 1 [])%Q.
Proof.
  split; [| split].
  - intros Hnd. cbn [List.map] in Hnd.
    apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd as [Hnin _].
    apply Hnin. left. reflexivity.
  - intros f Hf. destruct Hf as [Hf | [Hf | []]]; subst f;
      exists []; reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(* =========================================================================
   Sums, scaled and added
   ========================================================================= *)

(** The two sum identities the composition combinators need, stated on
    [core_sum] because that is the side a consumer's bound is on.  They
    are here rather than beside [core_sum_cons] because the combinators
    below are their only callers, and reading them next to the
    combinators is reading them next to the reason they exist. *)
Lemma core_sum_scale : forall (q : Q) w l,
  (core_sum (fun c => (q * w c)%Q) l == q * core_sum w l)%Q.
Proof.
  intros q w l. induction l as [| f l IH].
  - rewrite !core_sum_nil. ring.
  - rewrite !core_sum_cons. cbv beta. rewrite IH. ring.
Qed.

Lemma core_sum_plus : forall w1 w2 l,
  (core_sum (fun c => (w1 c + w2 c)%Q) l == core_sum w1 l + core_sum w2 l)%Q.
Proof.
  intros w1 w2 l. induction l as [| f l IH].
  - rewrite !core_sum_nil. ring.
  - rewrite !core_sum_cons. cbv beta. rewrite IH. ring.
Qed.

Lemma core_sum_zero : forall l, (core_sum (fun _ => 0%Q) l == 0)%Q.
Proof.
  induction l as [| f l IH]; [reflexivity |].
  rewrite core_sum_cons, IH. ring.
Qed.

(** A weight that vanishes everywhere sums to zero, whatever the list —
    [core_sum_zero] up to pointwise [Qeq].  It is what makes the
    degeneracy at [p_stop = 0] a statement about EVERY admissible list
    rather than about the witness family alone
    ([stdin_geometric_mass_lower_needs_positive]). *)
Lemma core_sum_zero_weight : forall w l,
  (forall c, (w c == 0)%Q) -> (core_sum w l == 0)%Q.
Proof.
  intros w l Hz. rewrite core_sum_map_fin_core.
  rewrite (qsum_ext w (fun _ => 0%Q)) by (intros c _; apply Hz).
  apply qsum_zero.
Qed.

(* =========================================================================
   Combinators: scaling and mixture
   ========================================================================= *)

(** Scaling a distribution by a nonnegative factor: every weight and the
    declared mass multiplied together, so that the relation the
    certificates report between them is preserved rather than left
    true by luck.

    [0 <= q] is a constructor argument for the reason
    [finite_support]'s nonnegativity proof and [stdin_geometric]'s two
    side conditions are: [cd_nonneg] is a FIELD, and a scaling that
    returned a [CoreDistribution] without a proof would have to invent
    that field.  At a negative [q] there is nothing to invent —
    [cd_scale_negative_no_core_distribution] refutes the existence of
    ANY [CoreDistribution] weighing cores the way a negative scaling of
    [example_cd] would. *)
Definition cd_scale (q : Q) (Hq : (0 <= q)%Q) (D : CoreDistribution)
  : CoreDistribution :=
  mkCoreDistribution (fun c => (q * cd_weight D c)%Q) (q * cd_mass D)%Q
    (fun c => Qmult_le_0_compat q (cd_weight D c) Hq (cd_nonneg D c)).

(** The mixture of two distributions: the weights ADD, pointwise, and
    the declared masses add with them.

    Nothing is normalized and nothing is halved.  A mixture in the
    probabilist's sense — [a] of one and [1 - a] of the other — is this
    combinator applied to two [cd_scale]s, and writing it that way keeps
    the two decisions (how much of each, and what to do with the sum)
    separate and both visible.  There is no side condition at all:
    nonnegativity composes by [Qplus_nonneg], and no obligation
    anywhere ties [cd_mass] to anything.

    SUPPORTS MAY OVERLAP, and on a shared core the weights add like
    everywhere else — which is the right reading and not a defect to be
    repaired, for the reason [entries_weight] sums duplicate entries:
    the declared mass is the sum of the declared masses, so a mixture
    that silently took a maximum on the overlap would declare a total
    no list could reach.  [cd_mix2_overlap_weights_add] pins the
    arithmetic at a concrete overlapping pair, and
    [cd_mix2_bound_is_not_the_max] pins the consequence a reader might
    otherwise guess wrong. *)
Definition cd_mix2 (D1 D2 : CoreDistribution) : CoreDistribution :=
  mkCoreDistribution (fun c => (cd_weight D1 c + cd_weight D2 c)%Q)
    (cd_mass D1 + cd_mass D2)%Q
    (fun c => Qplus_nonneg _ _ (cd_nonneg D1 c) (cd_nonneg D2 c)).

(** The empty mixture: weight zero everywhere, declared mass zero.  It
    is the unit the [n]-ary fold below folds against, and it is a
    legitimate [CoreDistribution] rather than a degenerate case to be
    avoided — every bound holds of it, trivially and truthfully. *)
Definition cd_zero : CoreDistribution :=
  mkCoreDistribution (fun _ => 0%Q) 0%Q (fun _ => Qle_refl 0%Q).

(** The [n]-ary mixture, as the fold of [cd_mix2] over [cd_zero].  A
    [Fixpoint] rather than a [fold_right] with a [CoreDistribution]
    accumulator so that [cd_weight (cd_mix (D :: Ds))] reduces to the
    sum of a weight and a recursive call by conversion, which is what
    the induction in [cd_mix_bound] wants. *)
Fixpoint cd_mix (Ds : list CoreDistribution) : CoreDistribution :=
  match Ds with
  | [] => cd_zero
  | D :: rest => cd_mix2 D (cd_mix rest)
  end.

(** The total a list of per-component numbers declares.  Kept as its
    own definition so that the [n]-ary bound and the [n]-ary mass are
    the SAME fold at two different arguments — [cd_mix_mass] below is
    that identification, and without it a consumer would have to match
    a [fold_right] against a [Fixpoint] by hand. *)
Definition cd_sum_over (B : CoreDistribution -> Q) (Ds : list CoreDistribution)
  : Q :=
  fold_right (fun D acc => (B D + acc)%Q) 0%Q Ds.

(** The mixture's declared mass IS the total of the components' —
    [Qeq] would do, and this is [eq], because both sides are the same
    fold. *)
Lemma cd_mix_mass : forall Ds, cd_mass (cd_mix Ds) = cd_sum_over cd_mass Ds.
Proof.
  induction Ds as [| D Ds IH]; [reflexivity |].
  cbn [cd_mix cd_mix2 cd_mass cd_sum_over fold_right] in *.
  rewrite IH. reflexivity.
Qed.

(* =========================================================================
   The bounds compose
   ========================================================================= *)

(** SCALING: a bound for [D] scales to a bound for the scaling.  [B] is
    any bound whatever, not necessarily the declared mass, so this
    applies to a cylinder bound and a length-slice bound exactly as it
    applies to a mass certificate.

    Nonnegativity of [q] is what makes the multiplication monotone; it
    is the constructor's argument, so a consumer never supplies it
    twice. *)
Lemma cd_scale_bound : forall q (Hq : (0 <= q)%Q) D l B,
  (core_sum (cd_weight D) l <= B)%Q ->
  (core_sum (cd_weight (cd_scale q Hq D)) l <= q * B)%Q.
Proof.
  intros q Hq D l B Hb. cbn [cd_weight cd_scale].
  rewrite core_sum_scale.
  apply (Qle_trans _ (core_sum (cd_weight D) l * q)%Q);
    [apply Qle_of_Qeq; ring |].
  apply (Qle_trans _ (B * q)%Q);
    [apply Qmult_le_compat_r; [exact Hb | exact Hq] | apply Qle_of_Qeq; ring].
Qed.

(** ... and the declared mass scales with it, so the mass certificate
    survives scaling: [cd_mass (cd_scale q Hq D)] is [q * cd_mass D] by
    conversion. *)
Lemma cd_scale_mass : forall q (Hq : (0 <= q)%Q) D,
  cd_mass (cd_scale q Hq D) = (q * cd_mass D)%Q.
Proof. reflexivity. Qed.

Lemma cd_scale_bound_mass : forall q (Hq : (0 <= q)%Q) D l,
  (core_sum (cd_weight D) l <= cd_mass D)%Q ->
  (core_sum (cd_weight (cd_scale q Hq D)) l
     <= cd_mass (cd_scale q Hq D))%Q.
Proof. intros q Hq D l Hb. apply cd_scale_bound. exact Hb. Qed.

(** ... and so does the SIGN of the mass, which is what
    [Measure.DISTRIBUTION]'s [M_nonneg] asks about: a nonnegative mass
    scaled by the nonnegative [q] the constructor already demanded stays
    nonnegative.  The [0 <= q] here is [cd_scale]'s own argument, not a
    new hypothesis. *)
Lemma cd_scale_mass_nonneg : forall q (Hq : (0 <= q)%Q) D,
  (0 <= cd_mass D)%Q -> (0 <= cd_mass (cd_scale q Hq D))%Q.
Proof.
  intros q Hq D HD. rewrite cd_scale_mass.
  apply Qmult_le_0_compat; assumption.
Qed.

(** MIXTURE: bounds for the two components add to a bound for the
    mixture, ON THE SAME LIST.  That the list is shared is the whole
    content — each component is bounded on the very list the mixture is
    being bounded on, so no rearrangement and no duplicate-freedom
    argument happens here; whatever hypotheses the two component bounds
    carried, the caller has already discharged them. *)
Lemma cd_mix2_bound : forall D1 D2 l B1 B2,
  (core_sum (cd_weight D1) l <= B1)%Q ->
  (core_sum (cd_weight D2) l <= B2)%Q ->
  (core_sum (cd_weight (cd_mix2 D1 D2)) l <= B1 + B2)%Q.
Proof.
  intros D1 D2 l B1 B2 H1 H2. cbn [cd_weight cd_mix2].
  rewrite core_sum_plus. apply Qplus_le_compat; assumption.
Qed.

Lemma cd_mix2_mass : forall D1 D2,
  cd_mass (cd_mix2 D1 D2) = (cd_mass D1 + cd_mass D2)%Q.
Proof. reflexivity. Qed.

Lemma cd_mix2_bound_mass : forall D1 D2 l,
  (core_sum (cd_weight D1) l <= cd_mass D1)%Q ->
  (core_sum (cd_weight D2) l <= cd_mass D2)%Q ->
  (core_sum (cd_weight (cd_mix2 D1 D2)) l <= cd_mass (cd_mix2 D1 D2))%Q.
Proof. intros D1 D2 l H1 H2. apply cd_mix2_bound; assumption. Qed.

(** The mixture's mass is nonnegative when both components' are, by
    [Qplus_nonneg] — the same fact that makes [cd_mix2]'s [cd_nonneg]
    field composable, one level up.  With [cd_scale_mass_nonneg] this
    closes [Measure.DISTRIBUTION]'s [M_nonneg] under the two
    combinators a probabilist's mixture is written with. *)
Lemma cd_mix2_mass_nonneg : forall D1 D2,
  (0 <= cd_mass D1)%Q -> (0 <= cd_mass D2)%Q ->
  (0 <= cd_mass (cd_mix2 D1 D2))%Q.
Proof.
  intros D1 D2 H1 H2. rewrite cd_mix2_mass.
  apply Qplus_nonneg; assumption.
Qed.

(** THE [n]-ARY FORM: a bound for every component gives the total of
    those bounds for the mixture.  The bounds are given as a FUNCTION of
    the component rather than as a parallel list, so nothing has to line
    up two lists of different provenance — and [cd_sum_over] is then
    literally the same fold as [cd_mix]'s mass. *)
Lemma cd_mix_bound : forall (B : CoreDistribution -> Q) Ds l,
  (forall D, List.In D Ds -> (core_sum (cd_weight D) l <= B D)%Q) ->
  (core_sum (cd_weight (cd_mix Ds)) l <= cd_sum_over B Ds)%Q.
Proof.
  intros B Ds l. induction Ds as [| D Ds IH]; intros Hb.
  - cbn [cd_mix cd_zero cd_weight cd_sum_over fold_right].
    rewrite core_sum_zero. apply Qle_refl.
  - cbn [cd_sum_over fold_right]. apply cd_mix2_bound.
    + apply Hb. left. reflexivity.
    + apply IH. intros D' HD'. apply Hb. right. exact HD'.
Qed.

(** ... and at the components' declared masses that is the mixture's own
    mass certificate, which is the statement a task author building a
    background-plus-foreground distribution consumes. *)
Lemma cd_mix_bound_mass : forall Ds l,
  (forall D, List.In D Ds -> (core_sum (cd_weight D) l <= cd_mass D)%Q) ->
  (core_sum (cd_weight (cd_mix Ds)) l <= cd_mass (cd_mix Ds))%Q.
Proof.
  intros Ds l Hb. rewrite cd_mix_mass. apply cd_mix_bound. exact Hb.
Qed.

(* =========================================================================
   The certificates compose too
   ========================================================================= *)

(** The LOWER half survives scaling and mixing, and it is worth stating
    separately from the upper half because the two travel differently:
    an upper bound holds of every admissible list, so the components'
    upper bounds may be proved on lists chosen independently, while an
    attaining list has to be ONE list that attains both.  Hence the
    shared [l] in the hypotheses below — a real requirement, not
    bookkeeping.  [cd_mix2_finite_support_mass_exact] shows the shared
    witness exists for a pair of finite supports, which is the case a
    task actually meets.

    THE GENERIC-[B] FORMS COME FIRST, and stating them first is not
    tidiness: they are the only ones a geometric component can use.  A
    family whose mass is a supremum and not a maximum never satisfies
    [cd_mass D <= core_sum (cd_weight D) l] —
    [stdin_geometric_mass_not_attained] refutes that hypothesis on every
    duplicate-free list — so a mixture of such families has to compose
    numbers that fall SHORT of the two declared masses, and the
    shortfall has to survive the scaling and the addition.  [B] is any
    number whatever, exactly as in [cd_scale_bound] and
    [cd_mix2_bound], and the mass forms below are the instances at
    [B = cd_mass D], the same way [cd_scale_bound_mass] is an instance
    of [cd_scale_bound]. *)
Lemma cd_scale_bound_lower : forall q (Hq : (0 <= q)%Q) D l B,
  (B <= core_sum (cd_weight D) l)%Q ->
  (q * B <= core_sum (cd_weight (cd_scale q Hq D)) l)%Q.
Proof.
  intros q Hq D l B Hb. cbn [cd_weight cd_scale].
  rewrite core_sum_scale.
  apply (Qle_trans _ (B * q)%Q); [apply Qle_of_Qeq; ring |].
  apply (Qle_trans _ (core_sum (cd_weight D) l * q)%Q);
    [apply Qmult_le_compat_r; [exact Hb | exact Hq] | apply Qle_of_Qeq; ring].
Qed.

Lemma cd_mix2_bound_lower : forall D1 D2 l B1 B2,
  (B1 <= core_sum (cd_weight D1) l)%Q ->
  (B2 <= core_sum (cd_weight D2) l)%Q ->
  (B1 + B2 <= core_sum (cd_weight (cd_mix2 D1 D2)) l)%Q.
Proof.
  intros D1 D2 l B1 B2 H1 H2. cbn [cd_weight cd_mix2].
  rewrite core_sum_plus. apply Qplus_le_compat; assumption.
Qed.

Lemma cd_scale_mass_lower : forall q (Hq : (0 <= q)%Q) D l,
  (cd_mass D <= core_sum (cd_weight D) l)%Q ->
  (cd_mass (cd_scale q Hq D) <= core_sum (cd_weight (cd_scale q Hq D)) l)%Q.
Proof. intros q Hq D l Hlow. apply cd_scale_bound_lower. exact Hlow. Qed.

Lemma cd_mix2_mass_lower : forall D1 D2 l,
  (cd_mass D1 <= core_sum (cd_weight D1) l)%Q ->
  (cd_mass D2 <= core_sum (cd_weight D2) l)%Q ->
  (cd_mass (cd_mix2 D1 D2) <= core_sum (cd_weight (cd_mix2 D1 D2)) l)%Q.
Proof. intros D1 D2 l H1 H2. apply cd_mix2_bound_lower; assumption. Qed.

(** A MIXTURE OF TWO FINITE SUPPORTS HAS ITS MASS ATTAINED, which is
    the case a task actually meets and the reason
    [finite_support_mass_lower_on] is stated up in the certificates
    section in the general form it has.  The canonical list of
    [finite_support_mass_lower_witness] would not do here: it covers one
    component's entries and says nothing about the other's, while
    [cd_mix2_mass_lower] needs ONE list attaining both.

    The list that works is the obvious one — the entries' cores of
    BOTH, duplicates removed — and it covers each component because
    each entry list is contained in their concatenation.
    [cd_mix2_mass_lower] then adds the two attainments,
    [cd_mix2_bound_mass] adds the two bounds, and the [Qeq] is
    [Qle_antisym] on those, never a computation. *)
Lemma cd_mix2_finite_support_mass_exact : forall e1 e2
    (H1 : forall e, List.In e e1 -> (0 <= snd e)%Q)
    (H2 : forall e, List.In e e2 -> (0 <= snd e)%Q),
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (core_sum (cd_weight (cd_mix2 (finite_support e1 H1)
                                     (finite_support e2 H2))) l
          == cd_mass (cd_mix2 (finite_support e1 H1)
                              (finite_support e2 H2)))%Q.
Proof.
  intros e1 e2 H1 H2.
  pose (cs := List.nodup (fun x y => decide (x = y))
                (List.map fst (e1 ++ e2))).
  assert (Hnd : List.NoDup cs) by apply List.NoDup_nodup.
  exists (List.map core_input cs).
  assert (Hndm : List.NoDup (List.map fin_core (List.map core_input cs)))
    by (rewrite map_fin_core_core_input; exact Hnd).
  split; [exact Hndm |].
  apply Qle_antisym.
  - apply cd_mix2_bound_mass; apply finite_support_bound; exact Hndm.
  - apply cd_mix2_mass_lower.
    + apply finite_support_mass_lower_on; [exact Hnd |].
      intros e He. apply List.nodup_In, List.in_map, List.in_or_app.
      left. exact He.
    + apply finite_support_mass_lower_on; [exact Hnd |].
      intros e He. apply List.nodup_In, List.in_map, List.in_or_app.
      right. exact He.
Qed.

(* =========================================================================
   Non-vacuity: what scaling and mixing DO, pinned
   ========================================================================= *)

(** Scaling by zero gives the zero distribution — pointwise, and in the
    declared mass.  It is a [Qeq] and not an [eq]: the weight of the
    scaling is [fun c => 0 * cd_weight D c], which is the zero function
    only up to [Qeq], and this file's discipline is that [Qeq] is the
    equality of rationals.  Worth pinning because it is the one input at
    which the constructor's [0 <= q] is tight, and because a reader
    should be able to see that scaling has not quietly been given a
    normalizing reading. *)
Lemma cd_scale_zero : forall D,
  (forall c, (cd_weight (cd_scale 0 (Qle_refl 0) D) c
                == cd_weight cd_zero c)%Q)
  /\ (cd_mass (cd_scale 0 (Qle_refl 0) D) == cd_mass cd_zero)%Q.
Proof.
  intros D. split.
  - intros c. cbn [cd_weight cd_scale cd_zero]. ring.
  - cbn [cd_mass cd_scale cd_zero]. ring.
Qed.

(** A NEGATIVE scaling admits no [CoreDistribution] at all, which is
    what makes [cd_scale]'s proof argument a refusal rather than an
    inconvenience.  This is [negative_entries_no_core_distribution] for
    the scaling combinator: no record whose weight so much as AGREES
    pointwise with [-1] times [example_cd]'s can exist, because
    [cd_nonneg] refutes it at the core where [example_cd] puts [1 # 2].
    A distribution with no positive weight anywhere would of course
    survive a negative scaling, which is why the statement names a
    concrete [example_cd] rather than quantifying over [D]. *)
Lemma cd_scale_negative_no_core_distribution : forall D : CoreDistribution,
  ~ (forall c, (cd_weight D c == (- (1)) * cd_weight example_cd c)%Q).
Proof.
  intros D Hagree.
  assert (H := cd_nonneg D example_core_empty).
  rewrite (Hagree example_core_empty) in H.
  apply (proj2 (Qle_bool_iff _ _)) in H. vm_compute in H. discriminate.
Qed.

(** Two finite supports whose supports OVERLAP: both put weight on the
    empty core, and one of them also weighs "A".  This is the pair the
    three bites below are about — [example_cd] and [dup_cd] would not
    do, since what is at issue is two distributions meeting on a core,
    not one distribution's repeated entries. *)
Definition overlap_entries_l : list (FinCore * Q) :=
  [(example_core_empty, (1 # 2)%Q)].

Definition overlap_entries_r : list (FinCore * Q) :=
  [(example_core_empty, (1 # 4)%Q); (example_core_a, (1 # 8)%Q)].

Definition overlap_cd_l : CoreDistribution :=
  finite_support overlap_entries_l
    (entries_nonneg_of_forallb overlap_entries_l eq_refl).

Definition overlap_cd_r : CoreDistribution :=
  finite_support overlap_entries_r
    (entries_nonneg_of_forallb overlap_entries_r eq_refl).

Definition overlap_mix : CoreDistribution := cd_mix2 overlap_cd_l overlap_cd_r.

(** THE OVERLAP BITE: on the shared core the weights ADD — [1 # 2] and
    [1 # 4] make [3 # 4], not [1 # 2] and not [3 # 8] — the core only
    one of them names keeps its own weight, and the declared mass is the
    sum of the two declared masses.  All three are closed [Qeq]s between
    literals this file wrote, per the header's exception.

    This is the "what IS true about mixtures of overlapping supports"
    statement.  Nothing is double-counted, because nothing was counted
    once to begin with: [cd_mix2] is defined to add, the masses are
    defined to add with it, and the third conjunct is what keeps the two
    halves in step. *)
Lemma cd_mix2_overlap_weights_add :
  (cd_weight overlap_mix example_core_empty == 3 # 4)%Q
  /\ (cd_weight overlap_mix example_core_a == 1 # 8)%Q
  /\ (cd_mass overlap_mix == 7 # 8)%Q.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ... AND THE MIXTURE'S BOUND IS NOT THE MAX OF THE COMPONENTS'.
    The one-element list over the shared core already weighs [3 # 4]
    under the mixture, which is past BOTH components' declared masses
    ([1 # 2] and [3 # 8]) — so no rule of the form "a mixture is bounded
    by the largest of its parts" can hold, and [cd_mix2_bound]'s [B1 +
    B2] is not a convenient over-approximation that a sharper lemma
    could later replace by a maximum.

    Stated as two refutations rather than as one inequality against a
    maximum, because the claim being ruled out is about every candidate
    reading of "the max", and the two components' masses are the only
    candidates here.  (No maximum on [Q] is used or imported anywhere in
    this file.) *)
Lemma cd_mix2_bound_is_not_the_max :
  (core_sum (cd_weight overlap_mix) [core_input example_core_empty]
     == 3 # 4)%Q
  /\ ~ (core_sum (cd_weight overlap_mix) [core_input example_core_empty]
          <= cd_mass overlap_cd_l)%Q
  /\ ~ (core_sum (cd_weight overlap_mix) [core_input example_core_empty]
          <= cd_mass overlap_cd_r)%Q.
Proof.
  split; [vm_compute; reflexivity |].
  split; intros Hle; apply (proj2 (Qle_bool_iff _ _)) in Hle;
    vm_compute in Hle; discriminate.
Qed.

(** The [n]-ary fold agrees with the binary combinator and with its own
    unit: the empty mixture declares zero, and the two-element mixture
    declares and weighs what [cd_mix2] does.  Without the first conjunct
    the fold could be anything at all on the empty list; without the
    other two, [cd_mix] could disagree with [cd_mix2] and every lemma
    above would still be true of each of them separately. *)
Lemma cd_mix_nary_agrees :
  (cd_mass (cd_mix []) == 0)%Q
  /\ (cd_mass (cd_mix [overlap_cd_l; overlap_cd_r]) == cd_mass overlap_mix)%Q
  /\ (cd_weight (cd_mix [overlap_cd_l; overlap_cd_r]) example_core_empty
        == cd_weight overlap_mix example_core_empty)%Q.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* =========================================================================
   How fast a power of a proper fraction shrinks
   ========================================================================= *)

(** Everything from here to the end serves ONE statement: the geometric
    distribution's declared mass [1] is not padding, because admissible
    lists come arbitrarily close to it.  The obstruction is that no
    finite list REACHES it (the header's supremum-versus-maximum
    paragraph, and [stdin_geometric_bound]'s discussion), so the
    certificate has to be an approach rather than an attainment, and an
    approach needs a rate.

    The rate is elementary and is proved here rather than assumed:
    [(1 - p) ^ k] shrinks at least like [1 / (1 + k * p)].  No real
    numbers, no limits, no infinite series — a single induction and one
    Archimedean step. *)

(** A power of a number in [[0, 1]] stays in [[0, 1]]. *)
Lemma Qpow_le_1 : forall x k, (0 <= x)%Q -> (x <= 1)%Q -> (Qpow x k <= 1)%Q.
Proof.
  intros x k Hx0 Hx1. induction k as [| k IH];
    [rewrite Qpow_0; apply Qle_refl |].
  rewrite Qpow_succ.
  apply (Qle_trans _ (1 * 1)%Q); [| apply Qle_of_Qeq; ring].
  apply Qmult_le_compat_nonneg;
    [ split; assumption
    | split; [apply Qpow_nonneg; exact Hx0 | exact IH] ].
Qed.

(** The induction step of the shrinking bound, as arithmetic on its
    own.  With [P] for [(1 - p) ^ k] and [n] for [k], it says: if
    [P * (1 + n * p)] is at most [1], then so is the same expression
    one step on.

    The step is the whole content and it is worth reading.  Expand:
    [(1 - p) * P * (1 + (1 + n) * p)] is
    [(1 - p) * (P * (1 + n * p))] plus [(1 - p) * P * p].  The first
    summand is at most [1 - p] by the hypothesis; the second is at most
    [(1 - p) * p] because [P <= 1]; and their total is
    [1 - p * p], which is at most [1] because a square is nonnegative.
    That last inequality is where the slack lives, and it is why the
    bound is [1 / (1 + k * p)] rather than something sharper. *)
Lemma geo_gap_step : forall p P n,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= P)%Q -> (P <= 1)%Q ->
  (P * (1 + n * p) <= 1)%Q ->
  ((1 - p) * P * (1 + (1 + n) * p) <= 1)%Q.
Proof.
  intros p P n Hp0 Hp1 HP0 HP1 HIH.
  assert (H1p : (0 <= 1 - p)%Q) by (apply (Qle_minus_iff p 1); exact Hp1).
  assert (Hpp : (0 <= p * p)%Q) by (apply Qmult_le_0_compat; assumption).
  assert (HA : ((1 - p) * (P * (1 + n * p)) <= 1 - p)%Q).
  { apply (Qle_trans _ ((P * (1 + n * p)) * (1 - p))%Q);
      [apply Qle_of_Qeq; ring |].
    apply (Qle_trans _ (1 * (1 - p))%Q);
      [apply Qmult_le_compat_r; [exact HIH | exact H1p]
      | apply Qle_of_Qeq; ring]. }
  assert (HB : ((1 - p) * P * p <= (1 - p) * p)%Q).
  { apply (Qle_trans _ (P * ((1 - p) * p))%Q); [apply Qle_of_Qeq; ring |].
    apply (Qle_trans _ (1 * ((1 - p) * p))%Q);
      [ apply Qmult_le_compat_r;
        [exact HP1 | apply Qmult_le_0_compat; assumption]
      | apply Qle_of_Qeq; ring]. }
  apply (Qle_trans _ ((1 - p) * (P * (1 + n * p)) + (1 - p) * P * p)%Q);
    [apply Qle_of_Qeq; ring |].
  apply (Qle_trans _ ((1 - p) + (1 - p) * p)%Q);
    [apply Qplus_le_compat; assumption |].
  apply (Qle_trans _ (1 - p * p)%Q); [apply Qle_of_Qeq; ring |].
  apply (proj2 (Qle_minus_iff (1 - p * p) 1)).
  apply (Qle_trans _ (p * p)%Q); [exact Hpp | apply Qle_of_Qeq; ring].
Qed.

(** THE SHRINKING BOUND: [(1 - p) ^ k * (1 + k * p) <= 1], for every
    [k] and every [p] in [[0, 1]].

    Written multiplied out rather than as [(1 - p) ^ k <= 1 / (1 + k *
    p)] on purpose: the division would need [1 + k * p] to be non-zero
    as a side condition, and the multiplied form needs nothing at all.
    Note that no STRICT hypothesis appears — at [p = 0] it says
    [1 <= 1], truthfully and uselessly, which is exactly how the
    degenerate member behaves and is why the strictness enters below,
    at the point where a [k] must be CHOSEN. *)
Lemma geo_gap_bound : forall p k,
  (0 <= p)%Q -> (p <= 1)%Q ->
  (Qpow (1 - p) k * (1 + Qnat k * p) <= 1)%Q.
Proof.
  intros p k Hp0 Hp1.
  assert (H1p : (0 <= 1 - p)%Q) by (apply (Qle_minus_iff p 1); exact Hp1).
  assert (H1p1 : (1 - p <= 1)%Q).
  { apply (proj2 (Qle_minus_iff (1 - p) 1)).
    apply (Qle_trans _ p); [exact Hp0 | apply Qle_of_Qeq; ring]. }
  induction k as [| k IH].
  - rewrite Qpow_0, Qnat_0. apply Qle_of_Qeq. ring.
  - rewrite Qpow_succ, Qnat_succ.
    apply geo_gap_step; try assumption.
    + apply Qpow_nonneg; exact H1p.
    + apply Qpow_le_1; assumption.
Qed.

(** The Archimedean step, in the only form this file needs: no rational
    bounds every [Qnat].  [QArith]'s [Qarchimedean] gives a POSITIVE
    exceeding the rational, and [Pos.to_nat] carries it to the [nat]
    the counting lemmas index by; [positive_nat_Z] is the round trip
    that makes the two the same number. *)
Lemma Qnat_unbounded : forall q : Q, exists k : nat, (q <= Qnat k)%Q.
Proof.
  intros q. destruct (Qarchimedean q) as [p Hp].
  exists (Pos.to_nat p). unfold Qnat. rewrite positive_nat_Z.
  apply Qlt_le_weak. exact Hp.
Qed.

(** ... AND SO THE GAP CAN BE MADE AS SMALL AS ASKED, which is the
    statement [0 < p_stop] is for and the first place in this file that
    a strict inequality is load-bearing.

    Given a target [eps], take [k] past [/ (eps * p)] — legitimate only
    because [eps * p] is non-zero, which is where BOTH strictnesses are
    spent — and the shrinking bound does the rest: [(1 - p) ^ k] times
    [1 + k * p] is at most [1], and [1 + k * p] is at least [/ eps].

    At [p = 0] the choice is unavailable and the conclusion is false:
    [(1 - 0) ^ k] is [1] for every [k], never below an [eps] under one.
    That is the same degeneracy
    [stdin_geometric_mass_lower_needs_positive] pins at the level of the
    distribution. *)
Lemma geo_gap_small : forall p eps,
  (0 < p)%Q -> (p <= 1)%Q -> (0 < eps)%Q ->
  exists k : nat, (Qpow (1 - p) k <= eps)%Q.
Proof.
  intros p eps Hp0 Hp1 Heps.
  assert (Hpne : ~ (p == 0)%Q) by (apply Qnot_eq_sym, Qlt_not_eq; exact Hp0).
  assert (Hene : ~ (eps == 0)%Q) by (apply Qnot_eq_sym, Qlt_not_eq; exact Heps).
  destruct (Qnat_unbounded (/ (eps * p))) as [k Hk].
  exists k.
  assert (Hpow0 : (0 <= Qpow (1 - p) k)%Q)
    by (apply Qpow_nonneg; apply (Qle_minus_iff p 1); exact Hp1).
  assert (Hstep : (/ eps <= Qnat k * p)%Q).
  { apply (Qle_trans _ ((/ (eps * p)) * p)%Q).
    - apply Qle_of_Qeq. rewrite Qinv_mult_distr, <- Qmult_assoc.
      rewrite (Qmult_comm (/ p) p), (Qmult_inv_r p Hpne), Qmult_1_r.
      reflexivity.
    - apply Qmult_le_compat_r; [exact Hk | apply Qlt_le_weak; exact Hp0]. }
  assert (HA : (/ eps <= 1 + Qnat k * p)%Q).
  { apply (Qle_trans _ (Qnat k * p)%Q); [exact Hstep |].
    apply (Qle_trans _ (0 + Qnat k * p)%Q); [apply Qle_of_Qeq; ring |].
    apply Qplus_le_compat; [exact Qle_0_1 | apply Qle_refl]. }
  assert (Hmul : (Qpow (1 - p) k * / eps <= 1)%Q).
  { apply (Qle_trans _ (Qpow (1 - p) k * (1 + Qnat k * p))%Q);
      [| apply geo_gap_bound; [apply Qlt_le_weak; exact Hp0 | exact Hp1]].
    apply (Qle_trans _ ((/ eps) * Qpow (1 - p) k)%Q);
      [apply Qle_of_Qeq; ring |].
    apply (Qle_trans _ ((1 + Qnat k * p) * Qpow (1 - p) k)%Q);
      [ apply Qmult_le_compat_r; [exact HA | exact Hpow0]
      | apply Qle_of_Qeq; ring]. }
  apply (Qle_trans _ (Qpow (1 - p) k * / eps * eps)%Q).
  - apply Qle_of_Qeq. rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (/ eps) eps), (Qmult_inv_r eps Hene), Qmult_1_r.
    reflexivity.
  - apply (Qle_trans _ (1 * eps)%Q);
      [ apply Qmult_le_compat_r; [exact Hmul | apply Qlt_le_weak; exact Heps]
      | apply Qle_of_Qeq; ring].
Qed.

(** ... AND THE DEPTH IT PRODUCES CAN BE PUSHED AS FAR OUT AS ASKED,
    which is what a certificate needs when something OTHER than the
    margin also has a say in how deep to go.

    A tail only shrinks as the exponent grows — that is
    [Qpow_le_exp], one induction on the gap — so replacing the [k] of
    [geo_gap_small] by [Nat.max k0 k] keeps the bound and clears any
    floor.  [stdin_envp_mix2_mass_lower_certificate] is the caller: its
    environment depths must be large enough for the margin AND large
    enough to reach one particular fixed environment, and taking the
    larger of the two is the whole of how those are reconciled. *)
Lemma Qpow_le_exp : forall x n m,
  (0 <= x)%Q -> (x <= 1)%Q -> (n <= m)%nat -> (Qpow x m <= Qpow x n)%Q.
Proof.
  intros x n m Hx0 Hx1 Hnm. induction Hnm as [| m Hnm IH].
  - apply Qle_refl.
  - rewrite Qpow_succ.
    apply (Qle_trans _ (1 * Qpow x m)%Q);
      [| apply (Qle_trans _ (Qpow x m)%Q);
         [apply Qle_of_Qeq; ring | exact IH]].
    apply Qmult_le_compat_r; [exact Hx1 | apply Qpow_nonneg; exact Hx0].
Qed.

Lemma geo_gap_small_above : forall p eps k0,
  (0 < p)%Q -> (p <= 1)%Q -> (0 < eps)%Q ->
  exists k : nat, (k0 <= k)%nat /\ (Qpow (1 - p) k <= eps)%Q.
Proof.
  intros p eps k0 Hp0 Hp1 Heps.
  destruct (geo_gap_small p eps Hp0 Hp1 Heps) as [k Hk].
  exists (Nat.max k0 k). split; [lia |].
  apply (Qle_trans _ (Qpow (1 - p) k)); [| exact Hk].
  apply Qpow_le_exp; [apply (Qle_minus_iff p 1); exact Hp1 | | lia].
  apply (proj2 (Qle_minus_iff (1 - p) 1)).
  apply (Qle_trans _ p);
    [apply Qlt_le_weak; exact Hp0 | apply Qle_of_Qeq; ring].
Qed.

(* =========================================================================
   The length-[< k] prefix family, and what it weighs
   ========================================================================= *)

(** Every standard input SHORTER than [k], as a list.  The recursion is
    "the length-[k'] slice, then everything shorter", which is what
    makes the two facts wanted of it — that its members have the
    lengths claimed, and that it repeats nothing — one [List.app]
    argument each, on top of the enumeration facts [byte_lists] already
    has.

    It could equally have been [List.flat_map byte_lists (List.seq 0
    k)]; the [Fixpoint] is preferred because the sum below is then an
    induction on [k] with [qsum_app] at each step, and no
    lemma about folds over [List.seq] is needed. *)
Fixpoint short_inputs (k : nat) : list (list byte) :=
  match k with
  | O => []
  | S k' => byte_lists k' ++ short_inputs k'
  end.

Lemma short_inputs_In_length : forall k s,
  List.In s (short_inputs k) -> (length s < k)%nat.
Proof.
  induction k as [| k IH]; intros s Hs; [destruct Hs |].
  cbn [short_inputs] in Hs. apply List.in_app_or in Hs as [Hs | Hs].
  - rewrite (byte_lists_In_length k s Hs). lia.
  - apply IH in Hs. lia.
Qed.

(** ... and CONVERSELY it misses nothing shorter than [k].  The witness
    family does not need this — a witness only has to be admissible and
    to weigh what is claimed — but
    [stdin_geometric_mass_not_attained] does: to show a finite list
    falls short of the mass one has to place that list INSIDE the
    family, and this is what puts it there. *)
Lemma short_inputs_complete : forall k s,
  (length s < k)%nat -> List.In s (short_inputs k).
Proof.
  induction k as [| k IH]; intros s Hlen; [exfalso; lia |].
  cbn [short_inputs]. apply List.in_or_app.
  destruct (Nat.eq_dec (length s) k) as [Heq | Hne].
  - left. rewrite <- Heq. apply byte_lists_complete.
  - right. apply IH. lia.
Qed.

(** ... and it repeats nothing: the two halves are duplicate-free
    already, and they are disjoint because a member of the first has
    length exactly [k'] while a member of the second is shorter.  The
    length is what separates the slices, which is the same observation
    the enumeration's own [List.NoDup] proof makes about first
    bytes. *)
Lemma short_inputs_nodup : forall k, List.NoDup (short_inputs k).
Proof.
  induction k as [| k IH]; [apply List.NoDup_nil |].
  cbn [short_inputs]. apply List.NoDup_app.
  - apply byte_lists_nodup.
  - exact IH.
  - intros s Hin1 Hin2. apply short_inputs_In_length in Hin2.
    rewrite (byte_lists_In_length k s Hin1) in Hin2. lia.
Qed.

(** THE WITNESS FAMILY: over a fixed launch-time environment, one
    record per standard input shorter than [k].  It is admissible —
    duplicate-free on cores — and its weight is computed exactly
    below.

    Records rather than cores, because the certificate is about the
    lists [Measure.weight_bound_T] quantifies over; [core_input] is the
    same canonical embedding the finite-support witness uses, and the
    same caveat applies unchanged: these records are NOT claimed valid
    or rejected by anything. *)
Definition geo_lower_witness (argv envp : list (list byte)) (fs : Fs.Fs)
    (k : nat) : list FinProcInput :=
  List.map (fun s => core_input (mkFinCore argv envp fs s)) (short_inputs k).

Lemma map_fin_core_geo_lower_witness : forall argv envp fs k,
  List.map fin_core (geo_lower_witness argv envp fs k)
    = List.map (mkFinCore argv envp fs) (short_inputs k).
Proof.
  intros argv envp fs k. unfold geo_lower_witness. rewrite List.map_map.
  apply List.map_ext. intros s. apply fin_core_core_input.
Qed.

Lemma geo_lower_witness_nodup : forall argv envp fs k,
  List.NoDup (List.map fin_core (geo_lower_witness argv envp fs k)).
Proof.
  intros argv envp fs k. rewrite map_fin_core_geo_lower_witness.
  apply NoDup_map_inj; [| apply short_inputs_nodup].
  intros x y _ _ Heq. apply (f_equal core_stdin) in Heq. exact Heq.
Qed.

(** The partial sum of the geometric series over LENGTHS, as a
    [Fixpoint] so that it is a rational a task can write down and not a
    limit.  [geo_prefix_sum_closed] is the telescoping identity that
    turns it into the closed form the plan and the header quote. *)
Fixpoint geo_prefix_sum (p : Q) (k : nat) : Q :=
  match k with
  | O => 0%Q
  | S k' => (p * Qpow (1 - p) k' + geo_prefix_sum p k')%Q
  end.

(** The identity needs NO side condition on [p], and saying so is the
    point of stating it separately: the arithmetic of the geometric sum
    is unconditional, and every hypothesis this file attaches to the
    lower certificate is attached for a different reason (choosing a
    [k], in [geo_gap_small]).  Reading the two apart is how one can tell
    which of them is load-bearing where. *)
Lemma geo_prefix_sum_closed : forall p k,
  (geo_prefix_sum p k == 1 - Qpow (1 - p) k)%Q.
Proof.
  intros p k. induction k as [| k IH].
  - cbn [geo_prefix_sum]. rewrite Qpow_0. ring.
  - cbn [geo_prefix_sum]. rewrite IH, Qpow_succ. ring.
Qed.

(** A FULL length-[n] slice weighs exactly [p * (1 - p) ^ n].  This is
    [stdin_geometric_slice_bound_attained]'s content on the CORE side,
    factored out because the prefix family is a concatenation of full
    slices and the induction below needs one block at a time.  Both
    halves are already proved: every core in a slice weighs the same
    ([qsum_const]), and the count against the [(1/256) ^ n]
    cancels ([geo_slice_total]). *)
Lemma qsum_full_slice : forall p argv envp fs n,
  (qsum (geo_weight p argv envp fs)
     (List.map (mkFinCore argv envp fs) (byte_lists n))
     == p * Qpow (1 - p) n)%Q.
Proof.
  intros p argv envp fs n.
  rewrite (qsum_const _ _ (geo_point p n)).
  2:{ intros c Hc. apply List.in_map_iff in Hc as [s [Hs Hin]].
      rewrite <- Hs, geo_weight_match, (byte_lists_In_length n s Hin).
      reflexivity. }
  rewrite List.length_map, byte_lists_length. apply geo_slice_total.
Qed.

(** ... and so the whole prefix family weighs the partial sum: block by
    block, with [qsum_app] splitting off one slice per step.
    Nothing is approximated here — this is a [Qeq], and the only
    inequality in the certificate below is the choice of [k]. *)
Lemma qsum_short_inputs : forall p argv envp fs k,
  (qsum (geo_weight p argv envp fs)
     (List.map (mkFinCore argv envp fs) (short_inputs k))
     == geo_prefix_sum p k)%Q.
Proof.
  intros p argv envp fs k. induction k as [| k IH]; [reflexivity |].
  cbn [short_inputs geo_prefix_sum].
  rewrite List.map_app, qsum_app, IH, qsum_full_slice.
  reflexivity.
Qed.

(* =========================================================================
   The lower certificate for [stdin_geometric]
   ========================================================================= *)

(** THE WITNESS, at each [k]: an admissible list weighing exactly
    [1 - (1 - p_stop) ^ k].

    This is the half of the certificate pair that
    [stdin_geometric_mass_upper] left open, and the target is [1 - (1 -
    p_stop) ^ k] rather than the declared mass [1] because the mass is
    not available: for [p_stop < 1] the space holds infinitely many
    cores of positive weight and every admissible list is finite, so no
    list attains it — [stdin_geometric_mass_not_attained], below, which
    is the converse of this lemma and is proved from the same family.
    What a list CAN do is omit only the tail past length [k], and
    [(1 - p_stop) ^ k] is exactly that tail.

    No hypothesis beyond the constructor's own is needed HERE, and that
    is deliberate — the equality is unconditional arithmetic.  The
    strictness enters one lemma later, where a [k] has to be chosen to
    meet a target. *)
Lemma stdin_geometric_mass_lower_witness :
  forall p argv envp fs Hp0 Hp1 k,
  List.NoDup (List.map fin_core (geo_lower_witness argv envp fs k))
  /\ (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
        (geo_lower_witness argv envp fs k) == 1 - Qpow (1 - p) k)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 k.
  split; [apply geo_lower_witness_nodup |].
  cbn [cd_weight stdin_geometric].
  rewrite core_sum_map_fin_core, map_fin_core_geo_lower_witness.
  rewrite qsum_short_inputs. apply geo_prefix_sum_closed.
Qed.

(** The same fact in the shape the certificate vocabulary uses, beside
    [finite_support_mass_lower_witness]: SOME admissible list weighs the
    target.  Both forms are exported because they are consumed
    differently — a task proving something about the witness wants it
    named, and a task quoting the certificate wants the existential. *)
Lemma stdin_geometric_mass_lower_prefix :
  forall p argv envp fs Hp0 Hp1 k,
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
          == 1 - Qpow (1 - p) k)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 k.
  exists (geo_lower_witness argv envp fs k).
  apply stdin_geometric_mass_lower_witness.
Qed.

(** THE LOWER CERTIFICATE: for every margin [eps] there is an
    admissible list weighing at least the declared mass MINUS that
    margin.  Together with [stdin_geometric_mass_upper] — no list ever
    exceeds the mass — this is the honest pair for [stdin_geometric]:
    the declared [1] is the least upper bound of the admissible partial
    sums, approached but never met.

    [0 < p_stop] IS A HYPOTHESIS OF THIS LEMMA AND NOT A TIGHTENING OF
    THE CONSTRUCTOR, and the distinction is not a matter of taste.
    Moving it into [stdin_geometric] would invalidate every
    [stdin_geometric 0 …] a consumer may already have built, and would
    put the strictness where it is not used: everything above this
    lemma, the upper certificate included, holds at [p_stop = 0].  Here
    it is used, exactly once, inside [geo_gap_small], to choose the [k]
    whose tail is under [eps] — and
    [stdin_geometric_mass_lower_needs_positive] shows the conclusion is
    false without it. *)
Lemma stdin_geometric_mass_lower_certificate :
  forall p argv envp fs Hp0 Hp1 eps,
  (0 < p)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (cd_mass (stdin_geometric p argv envp fs Hp0 Hp1) - eps
          <= core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
               l)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 eps Hpos Heps.
  destruct (geo_gap_small p eps Hpos Hp1 Heps) as [k Hk].
  destruct (stdin_geometric_mass_lower_prefix p argv envp fs Hp0 Hp1 k)
    as [l [Hnd Hsum]].
  exists l. split; [exact Hnd |].
  rewrite Hsum. cbn [cd_mass stdin_geometric].
  apply (proj2 (Qle_minus_iff (1 - eps) (1 - Qpow (1 - p) k))).
  apply (Qle_trans _ (eps + - Qpow (1 - p) k)%Q);
    [ apply (proj1 (Qle_minus_iff (Qpow (1 - p) k) eps)); exact Hk
    | apply Qle_of_Qeq; ring].
Qed.

(* =========================================================================
   ... and the mass is a SUPREMUM and not a maximum
   ========================================================================= *)

(** A list confined to standard inputs of length at most [n] weighs at
    most [1 - (1 - p_stop) ^ (n + 1)] — the partial sum at its own
    horizon.  It MISSES THE TAIL, and the tail is the whole point.

    The proof is the witness family read in the other direction.  The
    cores of such a list, once the ones missing the fixed launch-time
    environment are filtered away (they weigh nothing —
    [geo_weight_mismatch], and [List.NoDup_filter] carries the
    duplicate-freedom across), all lie in
    [short_inputs (S n)] ([short_inputs_complete]); so
    [qsum_core_incl_le] bounds the list by the family, which
    [qsum_short_inputs] evaluates exactly.  Duplicate-freedom
    is where the hypothesis is spent, and it is spent in the same place
    it is spent everywhere else in this file: without it a list may name
    one core repeatedly and outweigh any enumeration of distinct
    cores. *)
Lemma stdin_geometric_bound_by_max_length :
  forall p argv envp fs Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> (length (fin_stdin f) <= n)%nat) ->
  (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
     <= 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 n l Hnd Hlen.
  cbn [cd_weight stdin_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_env argv envp fs))
    by (intros c Hc; rewrite (geo_weight_mismatch p argv envp fs c
                                (matches_env_false _ _ _ _ Hc)); reflexivity).
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (List.map (mkFinCore argv envp fs) (short_inputs (S n))))
    | rewrite qsum_short_inputs, geo_prefix_sum_closed;
      apply Qle_refl ].
  - apply geo_weight_nonneg; assumption.
  - apply List.NoDup_filter. exact Hnd.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    apply List.in_map_iff. exists (core_stdin c). split.
    + symmetry. apply matches_env_true. exact Hm.
    + apply short_inputs_complete.
      assert (Hle := Hlen f Hinl).
      rewrite <- Hf. cbn [fin_core core_stdin]. lia.
Qed.

(** ... AND THAT BOUND IS EXACTLY TIGHT, which is what makes the
    strictness below a fact about the distribution rather than an
    artefact of a lossy estimate: the witness family at [k = n + 1] is
    a list of standard inputs of length at most [n], and it weighs the
    bound exactly.  So [1 - (1 - p_stop) ^ (n + 1)] is the most a list
    confined to that horizon can weigh, and it is also the least upper
    bound of what such lists weigh.

    The two conjuncts are the two halves of "the bound applies to this
    list and is met by it"; duplicate-freedom is
    [geo_lower_witness_nodup], stated there rather than repeated
    here. *)
Lemma stdin_geometric_bound_by_max_length_attained :
  forall p argv envp fs Hp0 Hp1 n,
  (forall f, List.In f (geo_lower_witness argv envp fs (S n)) ->
     (length (fin_stdin f) <= n)%nat)
  /\ (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
        (geo_lower_witness argv envp fs (S n))
        == 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 n. split.
  - intros f Hf. unfold geo_lower_witness in Hf.
    apply List.in_map_iff in Hf as [s [Hs Hin]]. subst f.
    cbn [core_input fin_stdin core_stdin].
    apply short_inputs_In_length in Hin. lia.
  - apply stdin_geometric_mass_lower_witness.
Qed.

(** THE CLAIM THE CERTIFICATE'S SHAPE RESTS ON, MECHANIZED: for
    [p_stop < 1] NO admissible list weighs the declared mass — every one
    of them weighs strictly less.

    Read against [stdin_geometric_mass_upper] (no list exceeds [1]) and
    [stdin_geometric_mass_lower_certificate] (some list beats [1 - eps],
    for every [eps]), this is what makes the declared mass a SUPREMUM
    and not a maximum, and it is why the lower certificate had to be an
    approach.

    The [n] is the list's own longest standard input — [List.list_max]
    of the lengths, exactly the trick [geo_weight_cylinder_bound] uses to
    pick an enumeration depth, and the only place the FINITENESS of
    [Measure.weight_bound_T]'s lists is needed.  A list may be as long as
    it likes; what it cannot be is infinite, so it has a horizon, and
    beyond that horizon sits a positive tail ([Qpow_pos]) it does not
    collect.

    Only [p_stop < 1] is asked for, and the missing lower bound is not
    an oversight: at [p_stop = 0] the statement is true and obvious
    (every list weighs zero), so the family this rules out is the whole
    of [0 <= p_stop < 1] and not merely the open interval the header's
    discussion names.  At [p_stop = 1] it is false, and
    [geo_point_cd_mass_attained] is the list that refutes it. *)
Lemma stdin_geometric_mass_not_attained : forall p argv envp fs Hp0 Hp1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
       < cd_mass (stdin_geometric p argv envp fs Hp0 Hp1))%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 Hlt l Hnd.
  cbn [cd_mass stdin_geometric].
  pose (n := List.list_max (List.map (fun f => length (fin_stdin f)) l)).
  apply (Qle_lt_trans _ (1 - Qpow (1 - p) (S n))%Q).
  - apply stdin_geometric_bound_by_max_length; [exact Hnd |].
    intros f Hf. apply list_max_ge. apply List.in_map_iff.
    exists f. split; [reflexivity | exact Hf].
  - apply (proj2 (Qlt_minus_iff (1 - Qpow (1 - p) (S n)) 1)).
    apply (Qlt_le_trans _ (Qpow (1 - p) (S n))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qpow_pos. apply (Qlt_minus_iff p 1). exact Hlt.
Qed.

(** The same fact under the name a reader looks for: the declared mass
    is not ATTAINED.  [Qlt_not_eq] on the strict inequality — stated
    because "no admissible list weighs the mass" is how the claim is
    phrased everywhere it is used, and a consumer should not have to
    perform the conversion. *)
Lemma stdin_geometric_mass_supremum_not_maximum :
  forall p argv envp fs Hp0 Hp1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    ~ (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
         == cd_mass (stdin_geometric p argv envp fs Hp0 Hp1))%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 Hlt l Hnd.
  apply Qlt_not_eq.
  apply stdin_geometric_mass_not_attained; assumption.
Qed.

(* =========================================================================
   Non-vacuity: the family, and why the certificate asks for [0 < p_stop]
   ========================================================================= *)

(** The family at [k = 1] is the single stopping core over the empty
    standard input — the [List.map] over [short_inputs 1] reduces to
    it, by conversion. *)
Lemma geo_lower_witness_at_one : forall argv envp fs,
  geo_lower_witness argv envp fs 1
    = [core_input (mkFinCore argv envp fs [])].
Proof. reflexivity. Qed.

(** ... and it weighs [p_stop] exactly, which is what the abstract
    [1 - (1 - p_stop) ^ k] says at [k = 1] and is worth seeing on a
    concrete list: the whole certificate is the observation that this
    one core already carries [p_stop] of the mass, and that longer
    prefixes carry the rest. *)
Lemma geo_lower_witness_at_one_weighs : forall p argv envp fs Hp0 Hp1,
  (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
     (geo_lower_witness argv envp fs 1) == p)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1.
  rewrite (proj2 (stdin_geometric_mass_lower_witness p argv envp fs Hp0 Hp1 1)).
  rewrite Qpow_succ, Qpow_0. ring.
Qed.

(** At [p_stop = 0] every weight is zero — the degenerate member the
    constructor deliberately still admits. *)
Lemma geo_weight_zero_at_zero_p : forall argv envp fs c,
  (geo_weight 0 argv envp fs c == 0)%Q.
Proof.
  intros argv envp fs c. unfold geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  unfold geo_point. ring.
Qed.

(** THE STRICTNESS IS LOAD-BEARING, pinned the way this file pins every
    other hypothesis it asks for.  At [p_stop = 0] EVERY admissible list
    weighs zero — not merely the witness family, which is why the first
    conjunct quantifies over all of them — and the declared mass is
    still [1], so no list comes within [1 # 2] of it.  The certificate
    above is therefore false at [p_stop = 0], and its hypothesis is not
    inherited caution.

    [stdin_geometric_mass_upper] remains true here, and that asymmetry
    is the honest content of the pair: an upper bound survives
    degeneracy, a lower one does not. *)
Lemma stdin_geometric_mass_lower_needs_positive : forall argv envp fs,
  (forall l : list FinProcInput,
     (core_sum (cd_weight (stdin_geometric 0 argv envp fs
                             (Qle_refl 0) Qle_0_1)) l == 0)%Q)
  /\ ~ (cd_mass (stdin_geometric 0 argv envp fs (Qle_refl 0) Qle_0_1)
          - (1 # 2) <= 0)%Q.
Proof.
  intros argv envp fs. split.
  - intros l. apply core_sum_zero_weight. intros c.
    cbn [cd_weight stdin_geometric]. apply geo_weight_zero_at_zero_p.
  - cbn [cd_mass stdin_geometric]. intros Hle.
    apply (proj2 (Qle_bool_iff _ _)) in Hle. vm_compute in Hle. discriminate.
Qed.

(* =========================================================================
   A WORKED DISTRIBUTION: named cores over a geometric background
   ========================================================================= *)

(** The worked task's fixed launch-time inputs: a program invoked as
    ["wc"], with no environment and an empty file system.  Only argv is
    given anything to look at, and that is deliberate — these three are
    the components [stdin_geometric] holds FIXED, so their content is
    irrelevant to every number below, and writing something into one of
    them makes it visible that they are a choice.  As at [core_input],
    nothing here is claimed VALID ([FinInput.valid_fin_input]); a task
    that cares supplies its own. *)
Definition worked_argv : list (list byte) := [[Z_to_bv 8 119; Z_to_bv 8 99]].
Definition worked_envp : list (list byte) := [].
Definition worked_fs : Fs.Fs := [].

(** A core of this family: the fixed environment, and a standard input.
    Every core named below goes through it, which is what puts the
    named cores INSIDE the geometric background's support rather than
    beside it. *)
Definition worked_core (s : list byte) : FinCore :=
  mkFinCore worked_argv worked_envp worked_fs s.

Definition worked_nul : byte := Z_to_bv 8 0.
Definition worked_byte_A : byte := Z_to_bv 8 65.

(** The three cores the author considers important: the empty standard
    input, and the two that begin with a NUL byte.  The latter two are
    what the fire set will be, and they share the prefix [[0]] — not a
    coincidence but the point, since a prefix is what
    [stdin_geometric_bound] charges against. *)
Definition worked_core_empty : FinCore := worked_core [].
Definition worked_core_nul : FinCore := worked_core [worked_nul].
Definition worked_core_nul_a : FinCore :=
  worked_core [worked_nul; worked_byte_A].

(** Half the foreground on the empty input, a quarter on each
    NUL-prefixed one: a declared foreground mass of [1]. *)
Definition worked_entries : list (FinCore * Q) :=
  [(worked_core_empty, (1 # 2)%Q);
   (worked_core_nul, (1 # 4)%Q);
   (worked_core_nul_a, (1 # 4)%Q)].

Lemma worked_entries_nonneg :
  forall e, List.In e worked_entries -> (0 <= snd e)%Q.
Proof. exact (entries_nonneg_of_forallb worked_entries eq_refl). Qed.

Definition worked_foreground : CoreDistribution :=
  finite_support worked_entries worked_entries_nonneg.

(** The background's stop weight.  [1 # 8] is an authored choice like
    every other number here: it makes a typical standard input a few
    bytes long, and it is far enough from both [0] and [1] that neither
    degenerate case is being exercised by accident. *)
Definition worked_p : Q := (1 # 8)%Q.

Lemma worked_p_nonneg : (0 <= worked_p)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Lemma worked_p_le_1 : (worked_p <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Definition worked_background : CoreDistribution :=
  stdin_geometric worked_p worked_argv worked_envp worked_fs
    worked_p_nonneg worked_p_le_1.

(** The two shares.  They are written as named [Qle] facts rather than
    inlined because [cd_scale] takes the proof as an argument, and a
    task author reading this wants to see what that costs: two lines,
    once. *)
Lemma worked_share_named_nonneg : (0 <= 1 # 4)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Lemma worked_share_background_nonneg : (0 <= 3 # 4)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

(** THE DISTRIBUTION: a quarter on the named cores, three quarters on
    the geometric background.  This is the probabilist's mixture
    written the way [cd_mix2]'s comment describes it — two [cd_scale]s
    and one [cd_mix2], with how much of each and what to do with the
    sum kept as separate, visible decisions. *)
Definition worked_cd : CoreDistribution :=
  cd_mix2 (cd_scale (1 # 4) worked_share_named_nonneg worked_foreground)
          (cd_scale (3 # 4) worked_share_background_nonneg worked_background).

(** The foreground's declared mass is [1] — the three entries as
    written.  [entries_mass] is a [fold_right] over a literal list, so
    this is [ring] on three numerals once the fold is unfolded, not a
    decision about [Q]. *)
Lemma worked_foreground_mass : (cd_mass worked_foreground == 1)%Q.
Proof.
  unfold worked_foreground. cbn [cd_mass finite_support].
  unfold worked_entries, entries_mass. cbn [fold_right snd]. ring.
Qed.

(** The background's is [1] by [stdin_geometric]'s own declaration —
    [eq] and not merely [Qeq], because the constructor writes the
    numeral. *)
Lemma worked_background_mass : cd_mass worked_background = 1%Q.
Proof. reflexivity. Qed.

(** ... so the mixture declares [1], and the shares are what make it
    come out that way.  The [b * M] of the obligation is therefore [b]
    up to [Qeq], which is why the demonstrations below can quote a
    multiplier and a bound as one number. *)
Lemma worked_mass_is_one : (cd_mass worked_cd == 1)%Q.
Proof.
  unfold worked_cd. cbn [cd_mass cd_mix2 cd_scale].
  rewrite worked_foreground_mass, worked_background_mass. ring.
Qed.

(** The module, over a distribution built from three combinators
    instead of one: the two weight obligations are still discharged by
    the library's two lemmas, and [M_nonneg] by composing the mass
    lemmas of exactly the combinators the distribution was assembled
    from, with no arithmetic written here.  That is the claim the header's design
    section makes, at the size of distribution a task actually
    ships. *)
Module Worked_D <: DISTRIBUTION.
  Definition w : FinProcInput -> Q := cd_lift worked_cd.
  Definition M : Q := cd_mass worked_cd.
  Definition w_nonneg : forall f, (0 <= w f)%Q := cd_lift_nonneg worked_cd.
  Lemma M_nonneg : (0 <= M)%Q.
  Proof.
    unfold M, worked_cd, worked_foreground, worked_background.
    apply cd_mix2_mass_nonneg; apply cd_scale_mass_nonneg;
      [apply finite_support_mass_nonneg | apply stdin_geometric_mass_nonneg].
  Qed.
  Definition w_core_blind :
    forall f g, fin_core f = fin_core g -> (w f == w g)%Q :=
    cd_lift_core_blind worked_cd.
End Worked_D.

(* =========================================================================
   ... and the recipe for discharging [Measure.weight_bound_T] with it
   ========================================================================= *)

(** THE FIRE SET, as a predicate on cores.  Two cores named
    explicitly, because [entries_restrict] has to COMPUTE and these two
    are what the entry list names.  A larger support would use a
    predicate that DESCRIBES the set rather than listing it — "the
    standard input begins with a NUL byte" is decidable too, and
    [finite_support_bound_subset] takes any [bool]-valued [P]
    whatever. *)
Definition worked_is_fire (c : FinCore) : bool :=
  if decide (c = worked_core_nul) then true
  else if decide (c = worked_core_nul_a) then true else false.

(** The refinement's payoff, computed: the fire entries declare [1 # 2]
    between them, against the support's own [1].  Charging the fire set
    the whole declared mass would double the foreground half of the
    bound for nothing. *)
Lemma worked_restricted_mass :
  (entries_mass (entries_restrict worked_is_fire worked_entries) == 1 # 2)%Q.
Proof. vm_compute. reflexivity. Qed.

(** THE CEILING, as an exact rational.  The two component bounds are a
    restricted mass ([1 # 2]) and a cylinder mass over the one-byte
    prefix [[0]] ([7 # 2048]); scaled by the two shares and added, they
    come to [1045 # 8192].

    It is stated as a [Qeq] before it is used, so that the number in
    the demonstrations is visibly WHAT THE COMPOSITION YIELDS and not a
    convenient rounding of it.  The difference matters, because
    [worked_ceiling_slack] below measures the remaining slack against
    exactly this number. *)
Lemma worked_fire_ceiling :
  ((1 # 4) * entries_mass (entries_restrict worked_is_fire worked_entries)
   + (3 # 4) * stdin_geometric_cylinder_mass worked_p [worked_nul]
     == 1045 # 8192)%Q.
Proof.
  rewrite worked_restricted_mass.
  unfold stdin_geometric_cylinder_mass, geo_mass, worked_p.
  cbn [length Qpow]. ring.
Qed.

(** THE RECIPE, steps two and three: every admissible list drawn from
    the fire set weighs at most the ceiling.

    Read the proof as the pattern to copy.  [rewrite <-
    worked_fire_ceiling] puts the goal into the shape the composition
    lemmas produce — a sum of two scaled component bounds — and then
    there is one [cd_mix2_bound], one [cd_scale_bound] per component,
    and one library bound under each.  Neither component bound is at a
    declared mass: the foreground is charged the restricted mass and
    the background a cylinder mass, and they compose anyway, because
    [cd_scale_bound] and [cd_mix2_bound] are stated over arbitrary
    [Q]s.

    The two side conditions are where the fire set is spent, and they
    are the only places any thinking happens.  For the foreground: a
    fire core satisfies [worked_is_fire], by a [decide] that reduces.
    For the background: a fire core LIES IN THE CYLINDER over [[0]] —
    [worked_core_nul] is that prefix followed by nothing,
    [worked_core_nul_a] by one byte — so the existential is discharged
    by naming the extension.  Both are conversions once the witness is
    given, which is what it means for a fire set to have been described
    in the library's own vocabulary. *)
Lemma worked_fire_bound : forall l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = worked_core_nul \/ fin_core f = worked_core_nul_a) ->
  (core_sum (cd_weight worked_cd) l <= 1045 # 8192)%Q.
Proof.
  intros l Hnd Hfire.
  rewrite <- worked_fire_ceiling.
  unfold worked_cd.
  apply cd_mix2_bound.
  - apply cd_scale_bound.
    unfold worked_foreground.
    apply (finite_support_bound_subset worked_is_fire worked_entries
             worked_entries_nonneg l Hnd).
    intros f Hf. destruct (Hfire f Hf) as [Hc | Hc]; rewrite Hc;
      unfold worked_is_fire; vm_compute; reflexivity.
  - apply cd_scale_bound.
    unfold worked_background.
    apply (stdin_geometric_bound worked_p worked_argv worked_envp worked_fs
             worked_p_nonneg worked_p_le_1 [worked_nul] l Hnd).
    intros f Hf. destruct (Hfire f Hf) as [Hc | Hc].
    + exists []. exact Hc.
    + exists [worked_byte_A]. exact Hc.
Qed.

(** THE RECIPE, step four: from the library's bound to
    [Measure.weight_bound_T] itself, at ANY multiplier the ceiling fits
    under.

    Three lines, and each is one of the crossings this library exists
    to make cheap.  [core_sum_cd_lift] carries [Measure.sum_weights] of
    the lifted weight to [core_sum] — an [eq] by conversion, so the
    [rewrite] is bookkeeping and not a transport.  The classifier
    hypothesis is spent turning the obligation's "every record in [l]
    is rejected" into the fire-set membership [worked_fire_bound]
    wants.  And [worked_mass_is_one] turns [b * M] into [b].

    Quantifying over [b] rather than fixing one is what makes the two
    demonstrations below a single proof, and it puts the ceiling where
    a reader can see it: the hypothesis [1045 # 8192 <= b] IS the
    statement that this route goes no lower. *)
Lemma worked_weight_bound_T_of : forall C b,
  (forall f, Classifier.rejects C f ->
     fin_core f = worked_core_nul \/ fin_core f = worked_core_nul_a) ->
  (1045 # 8192 <= b)%Q ->
  weight_bound_T C Worked_D.w Worked_D.M b.
Proof.
  intros C b Hfire Hb l Hnd Hrej.
  unfold Worked_D.w. rewrite <- core_sum_cd_lift.
  apply (Qle_trans _ (1045 # 8192)%Q).
  - apply worked_fire_bound;
      [exact Hnd | intros f Hf; apply Hfire, Hrej, Hf].
  - unfold Worked_D.M. rewrite worked_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

(** DEMONSTRATION ONE, at a round multiplier a task would plausibly
    declare: a classifier whose reject set is this fire set carries at
    most a quarter of the distribution's mass.  The whole proof is the
    recipe plus one [Qle] between literals — the [Qle_bool] form the
    header documents. *)
Lemma worked_weight_bound_T_quarter : forall C,
  (forall f, Classifier.rejects C f ->
     fin_core f = worked_core_nul \/ fin_core f = worked_core_nul_a) ->
  weight_bound_T C Worked_D.w Worked_D.M (1 # 4).
Proof.
  intros C Hfire. apply worked_weight_bound_T_of; [exact Hfire |].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(** DEMONSTRATION TWO, at the tightest multiplier these bounds reach.
    The same recipe, and the arithmetic step has become [Qle_refl] —
    which is the honest way to say that there is nothing left to give
    away HERE.  Where the remaining slack is, and why it is not zero,
    is [worked_ceiling_slack]. *)
Lemma worked_weight_bound_T_ceiling : forall C,
  (forall f, Classifier.rejects C f ->
     fin_core f = worked_core_nul \/ fin_core f = worked_core_nul_a) ->
  weight_bound_T C Worked_D.w Worked_D.M (1045 # 8192).
Proof.
  intros C Hfire. apply worked_weight_bound_T_of;
    [exact Hfire | apply Qle_refl].
Qed.

(** The fire set as an admissible list: one canonical record per fire
    core, through [core_input].  As everywhere else in this file these
    records are not claimed valid and not claimed rejected by anything
    — exhibiting them is arithmetic, not a claim about a classifier. *)
Definition worked_fire_list : list FinProcInput :=
  List.map core_input [worked_core_nul; worked_core_nul_a].

(** HOW MUCH OF THE CEILING IS REAL.  The fire set's own two records
    form an admissible list, and they weigh [16820371 # 134217728] — a
    shade over 98 per cent of the [1045 # 8192] the composition charges,
    and strictly under it.

    Three conjuncts, each load-bearing.  The first says the list is
    admissible, so [worked_fire_bound] applies to it and the comparison
    is between comparable things.  The second is the exact weight,
    computed on literals this file wrote.  The third is the strictness:
    the ceiling is NOT attained, so the route does carry slack.  All of
    that slack is in the background half — the cylinder over [[0]]
    holds every core whose standard input begins with a NUL byte, the
    fire set names two of them, and every other continuation of every
    length is charged for and absent.

    What this does NOT say is that no smaller multiplier is provable,
    and that is the misreading the header's warning at the geometric
    lower certificate names.  A task that sums its two cores exactly
    gets a bound near [16820371 # 134217728] and is entitled to it.
    This lemma measures THIS ROUTE's slack, which is a property of the
    proof and not of the distribution. *)
Lemma worked_ceiling_slack :
  List.NoDup (List.map fin_core worked_fire_list)
  /\ (core_sum (cd_weight worked_cd) worked_fire_list
        == 16820371 # 134217728)%Q
  /\ ~ (1045 # 8192 <= 16820371 # 134217728)%Q.
Proof.
  split; [| split].
  - unfold worked_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | []].
      unfold worked_core_nul, worked_core_nul_a, worked_core in Heq.
      inversion Heq.
    + apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - vm_compute. reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(* =========================================================================
   The same recipe, indexed by a predicate instead of a classifier
   ========================================================================= *)

(** THE PREDICATE TWIN of [worked_weight_bound_T_of], and the whole of
    what changes: [Classifier.rejects C f] becomes
    [FinInput.valid_fin_input f /\ ~ P f].  Nothing else in the recipe
    moves — the same [worked_fire_bound], the same
    [worked_mass_is_one], the same ceiling — because the classifier
    never entered the arithmetic in the first place.  It entered as one
    hypothesis, and this is that hypothesis rewritten.

    Its use is the gated size measure's per-slice bound.  The complement
    of a slice is what a consumer bounds; the bound on the complement is
    what it turns into a lower bound on the slice's own mass; and a
    slice is a [GatedSize.slice_accept] or [GatedSize.slice_rest], which
    is a predicate on records and not a classifier's reject set, so the
    classifier-indexed form would not have typed.

    The proof is [weight_bound_pred_T_of_core_bound] with the fire set
    named and [worked_fire_bound] handed over.  The two [unfold]s are
    bookkeeping: [Worked_D.w] IS [cd_lift worked_cd] and [Worked_D.M] IS
    [cd_mass worked_cd], by [Definition], so the generic lemma applies
    with no transport. *)
Lemma worked_weight_bound_pred_T_of : forall (P : FinProcInput -> Prop) b,
  (forall f, valid_fin_input f -> ~ P f ->
     fin_core f = worked_core_nul \/ fin_core f = worked_core_nul_a) ->
  (1045 # 8192 <= b)%Q ->
  GatedSize.weight_bound_pred_T P Worked_D.w Worked_D.M b.
Proof.
  intros P b Hfire Hb.
  unfold Worked_D.w, Worked_D.M.
  apply (weight_bound_pred_T_of_core_bound worked_cd P
           (fun c => c = worked_core_nul \/ c = worked_core_nul_a)
           (1045 # 8192)%Q b).
  - exact Hfire.
  - intros l Hnd Hall. exact (worked_fire_bound l Hnd Hall).
  - rewrite worked_mass_is_one.
    apply (Qle_trans _ b); [exact Hb | apply Qle_of_Qeq; ring].
Qed.

(** The predicate twin of [worked_weight_bound_T_quarter]: the same
    round multiplier a task would plausibly declare, over a slice
    predicate instead of a classifier.  One [Qle] between literals, as
    before. *)
Lemma worked_weight_bound_pred_T_quarter : forall (P : FinProcInput -> Prop),
  (forall f, valid_fin_input f -> ~ P f ->
     fin_core f = worked_core_nul \/ fin_core f = worked_core_nul_a) ->
  GatedSize.weight_bound_pred_T P Worked_D.w Worked_D.M (1 # 4).
Proof.
  intros P Hfire. apply worked_weight_bound_pred_T_of; [exact Hfire |].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(** A core the fire set does not name: the standard input ["A"], which
    does not begin with a NUL byte and is not one of [worked_entries].
    Together with [worked_core_empty] — which the entries DO name, at
    half the foreground, and which the fire set still leaves out — it
    is what the pin below is built from. *)
Definition worked_core_a : FinCore := worked_core [worked_byte_A].

(** Two records whose cores are outside the fire set, as an admissible
    list.  As at [worked_fire_list], these are not claimed valid and not
    claimed outside anything — exhibiting them is arithmetic. *)
Definition worked_off_fire_list : list FinProcInput :=
  List.map core_input [worked_core_empty; worked_core_a].

(** THE FIRE-SET HYPOTHESIS IS LOAD-BEARING, pinned the way
    [worked_ceiling_slack] pins the slack.  Three conjuncts, each
    doing work.  The list is admissible, so it is one of the lists the
    obligation quantifies over.  NEITHER core is a fire core, computed
    through [worked_is_fire] itself rather than argued in prose.  And
    the two together weigh MORE than the ceiling — [worked_core_empty]
    alone does, carrying a quarter of the foreground's half plus its
    share of the geometric background.

    So the hypothesis of [worked_weight_bound_pred_T_of] is not
    inherited caution: drop it and the conclusion is false at the
    ceiling.  This is the negative half the classifier-indexed recipe
    never had, and it is available here for the reason the twin exists
    at all — a predicate's complement is something a reader can name
    two members of, where a classifier's reject set was only ever
    described. *)
Lemma worked_off_fire_exceeds_the_ceiling :
  List.NoDup (List.map fin_core worked_off_fire_list)
  /\ (worked_is_fire worked_core_empty = false
      /\ worked_is_fire worked_core_a = false)
  /\ ~ (core_sum (cd_weight worked_cd) worked_off_fire_list
          <= 1045 # 8192)%Q.
Proof.
  split; [| split].
  - unfold worked_off_fire_list. rewrite map_fin_core_core_input.
    apply List.NoDup_cons.
    + intros [Heq | []].
      unfold worked_core_empty, worked_core_a, worked_core in Heq.
      inversion Heq.
    + apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - split; vm_compute; reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate.
Qed.

(** ... and the pin cashed in as a refutation of the twin's conclusion.
    Two VALID records outside [P] whose cores are the two the fire set
    leaves out refute the bound at the ceiling.  So the twin's
    hypothesis is not free: a [P] whose complement reaches either core
    cannot satisfy it, and a recipe that let one through would prove
    something false.

    Validity is a hypothesis rather than a claim about [core_input],
    for the reason that runs through this whole file: nothing here asserts that a fabricated record is a launch a
    kernel could have performed, and a refutation that named an invalid
    record would refute nothing, since
    [GatedSize.weight_bound_pred_T]'s membership hypothesis carries
    [FinInput.valid_fin_input].  A task that wants the
    unconditional form supplies its own two records. *)
Lemma worked_weight_bound_pred_T_needs_the_fire_set :
  forall (P : FinProcInput -> Prop) f1 f2,
  valid_fin_input f1 -> ~ P f1 -> fin_core f1 = worked_core_empty ->
  valid_fin_input f2 -> ~ P f2 -> fin_core f2 = worked_core_a ->
  ~ GatedSize.weight_bound_pred_T P Worked_D.w Worked_D.M (1045 # 8192).
Proof.
  intros P f1 f2 Hv1 Hp1 Hc1 Hv2 Hp2 Hc2 Hbound.
  assert (Hnd : List.NoDup (List.map fin_core [f1; f2])).
  { cbn [List.map]. rewrite Hc1, Hc2.
    apply List.NoDup_cons.
    - intros [Heq | []].
      unfold worked_core_empty, worked_core_a, worked_core in Heq.
      inversion Heq.
    - apply List.NoDup_cons; [intros [] | apply List.NoDup_nil]. }
  assert (Hall : forall f, List.In f [f1; f2] -> valid_fin_input f /\ ~ P f).
  { intros f [Heq | [Heq | []]]; subst f; split; assumption. }
  specialize (Hbound [f1; f2] Hnd Hall).
  unfold Worked_D.w in Hbound. rewrite <- core_sum_cd_lift in Hbound.
  rewrite !core_sum_cons, core_sum_nil, Hc1, Hc2 in Hbound.
  unfold Worked_D.M in Hbound. rewrite worked_mass_is_one in Hbound.
  apply (proj2 (Qle_bool_iff _ _)) in Hbound.
  vm_compute in Hbound. discriminate.
Qed.

(* =========================================================================
   The standard-input enumerations, read off the cores
   ========================================================================= *)

(** [cyl_enum] with the launch-time environment forgotten: the standard
    inputs that extend [bs] by at most [N] bytes, as BYTE LISTS.

    The envp-varying family cannot use [cyl_enum] directly — its cores
    vary in envp as well, so a core is a PAIR (environment, standard
    input) and the two coordinates have to be enumerated apart before
    they are recombined.  What is deliberately NOT done here is to prove
    the cancellation a second time: [cyl_enum_bytes_cyl] says the two
    enumerations are the same list under [mkFinCore], and
    [bytes_cyl_sum_le] is [cyl_enum_sum_le] transported across it. *)
Fixpoint bytes_cyl (bs : list byte) (N : nat) : list (list byte) :=
  match N with
  | O => [bs]
  | S N' => bs :: List.flat_map (fun b => bytes_cyl (bs ++ [b]) N') all_bytes
  end.

Lemma cyl_enum_bytes_cyl : forall argv envp fs N bs,
  cyl_enum argv envp fs bs N
    = List.map (mkFinCore argv envp fs) (bytes_cyl bs N).
Proof.
  intros argv envp fs N. induction N as [| N IH]; intros bs; [reflexivity |].
  cbn [cyl_enum bytes_cyl List.map]. rewrite map_flat_map_comm.
  f_equal. apply List.flat_map_ext. intros b. apply IH.
Qed.

Lemma bytes_cyl_In : forall N bs ext,
  (length ext <= N)%nat -> List.In (bs ++ ext) (bytes_cyl bs N).
Proof.
  intros N bs ext Hlen.
  assert (Hin := cyl_enum_complete [] [] [] N bs ext Hlen).
  rewrite cyl_enum_bytes_cyl in Hin.
  apply List.in_map_iff in Hin as [s [Hs Hins]].
  apply (f_equal core_stdin) in Hs. cbn [core_stdin] in Hs.
  rewrite <- Hs. exact Hins.
Qed.

(** The three standard-input sums the family below charges against,
    each transported from the [qsum] lemma that proved it: the
    cylinder ([cyl_enum_sum_le]), the length-[< k] prefix family
    ([qsum_short_inputs]) and one full length slice
    ([qsum_full_slice]).  The transport is the same three
    rewrites every time — the enumeration is a [List.map] of
    [mkFinCore], [qsum_map] strips it off, and [geo_weight_match] turns
    the weight back into the [geo_point] it was built from. *)
Lemma bytes_cyl_sum_le : forall p, (0 <= p)%Q -> (p <= 1)%Q ->
  forall N bs,
    (qsum (fun s => geo_point p (length s)) (bytes_cyl bs N)
       <= geo_mass p (length bs))%Q.
Proof.
  intros p Hp0 Hp1 N bs.
  apply (Qle_trans _ (qsum (geo_weight p [] [] [])
                        (cyl_enum [] [] [] bs N))).
  - apply Qle_of_Qeq.
    rewrite cyl_enum_bytes_cyl, qsum_map.
    apply qsum_ext. intros s _. rewrite geo_weight_match. reflexivity.
  - apply cyl_enum_sum_le; assumption.
Qed.

Lemma short_inputs_sum : forall p k,
  (qsum (fun s => geo_point p (length s)) (short_inputs k)
     == geo_prefix_sum p k)%Q.
Proof.
  intros p k. rewrite <- (qsum_short_inputs p [] [] [] k).
  rewrite qsum_map.
  apply qsum_ext. intros s _. rewrite geo_weight_match. reflexivity.
Qed.

Lemma byte_lists_sum : forall p n,
  (qsum (fun s => geo_point p (length s)) (byte_lists n)
     == p * Qpow (1 - p) n)%Q.
Proof.
  intros p n. rewrite <- (qsum_full_slice p [] [] [] n).
  rewrite qsum_map.
  apply qsum_ext. intros s _. rewrite geo_weight_match. reflexivity.
Qed.

(* =========================================================================
   Combinator: geometric standard input over a VARYING launch-time
   environment
   ========================================================================= *)

(** The per-entry half of the weight: the product, over the environment's
    entries, of the byte-geometric weight of each entry's own length.
    [geo_point q_e m] is [q_e * ((1 - q_e) * (1/256)) ^ m] by definition,
    which is the per-entry factor the family is specified with — the same
    memoryless source [stdin_geometric] spreads standard input by, run
    once per entry. *)
Fixpoint entries_geo_product (q : Q) (es : list (list byte)) : Q :=
  match es with
  | [] => 1%Q
  | e :: es' => (geo_point q (length e) * entries_geo_product q es')%Q
  end.

(** The mass of the environments EXTENDING a given list of entries, and
    the weight of the environment that stops there.  As with [geo_mass]
    and [geo_point] the two are one object: continuing past an entry
    costs [1 - r] and the entry itself costs its byte-geometric weight,
    so [envp_factor] is the running product of those, and [envp_point]
    is [r] times it — the [r] being the weight of stopping.

    The three-factor form the family is specified with,
    [r * (1 - r) ^ k * Prod_i geo_point q_e |e_i|], is
    [envp_point_closed_form] below and is a LEMMA rather than a rival
    definition, for the reason [geo_point_closed_form] is: every proof
    here multiplies the factors together anyway, and one object with two
    readings cannot drift. *)
Fixpoint envp_factor (r q : Q) (es : list (list byte)) : Q :=
  match es with
  | [] => 1%Q
  | e :: es' => ((1 - r) * geo_point q (length e) * envp_factor r q es')%Q
  end.

Definition envp_point (r q : Q) (es : list (list byte)) : Q :=
  (r * envp_factor r q es)%Q.

Lemma envp_factor_closed_form : forall r q es,
  (envp_factor r q es
     == Qpow (1 - r) (length es) * entries_geo_product q es)%Q.
Proof.
  intros r q es. induction es as [| e es IH].
  - cbn [envp_factor entries_geo_product length]. rewrite Qpow_0. ring.
  - cbn [envp_factor entries_geo_product length]. rewrite IH, Qpow_succ. ring.
Qed.

Lemma envp_point_closed_form : forall r q es,
  (envp_point r q es
     == r * Qpow (1 - r) (length es) * entries_geo_product q es)%Q.
Proof.
  intros r q es. unfold envp_point. rewrite envp_factor_closed_form. ring.
Qed.

(** Extending the prefix MULTIPLIES the factor, which is the whole reason
    the envp coordinate can be enumerated the way the standard-input
    coordinate is: the mass of the environments past [es ++ es'] is the
    mass past [es] scaled by what [es'] costs, and the induction below
    needs exactly that at [es' = [e]]. *)
Lemma envp_factor_app : forall r q es es',
  (envp_factor r q (es ++ es')
     == envp_factor r q es * envp_factor r q es')%Q.
Proof.
  intros r q es es'. induction es as [| e es IH].
  - cbn [List.app envp_factor]. ring.
  - cbn [List.app envp_factor]. rewrite IH. ring.
Qed.

Lemma envp_factor_one : forall r q e,
  (envp_factor r q [e] == (1 - r) * geo_point q (length e))%Q.
Proof. intros r q e. cbn [envp_factor]. ring. Qed.

(** Nonnegativity, and it costs the same three side conditions the two
    coordinates cost separately: [r <= 1] makes the continuation factor
    nonnegative, exactly as [p_stop <= 1] does in [geo_ratio_nonneg],
    and [0 <= q_e <= 1] is what [geo_point_nonneg] asks of the per-entry
    weight. *)
Lemma envp_factor_nonneg : forall r q,
  (r <= 1)%Q -> (0 <= q)%Q -> (q <= 1)%Q ->
  forall es, (0 <= envp_factor r q es)%Q.
Proof.
  intros r q Hr1 Hq0 Hq1 es. induction es as [| e es IH]; [exact Qle_0_1 |].
  cbn [envp_factor]. apply Qmult_le_0_compat; [| exact IH].
  apply Qmult_le_0_compat.
  - apply (Qle_minus_iff r 1). exact Hr1.
  - apply geo_point_nonneg; assumption.
Qed.

Lemma envp_point_nonneg : forall r q,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= q)%Q -> (q <= 1)%Q ->
  forall es, (0 <= envp_point r q es)%Q.
Proof.
  intros r q Hr0 Hr1 Hq0 Hq1 es. unfold envp_point.
  apply Qmult_le_0_compat; [exact Hr0 | apply envp_factor_nonneg; assumption].
Qed.

(** One environment weighs at most the mass of the environments
    extending it, because [r <= 1].  This is [geo_point_le_mass] on the
    other coordinate and it is the base case of the same induction. *)
Lemma envp_point_le_factor : forall r q,
  (r <= 1)%Q -> (0 <= q)%Q -> (q <= 1)%Q ->
  forall es, (envp_point r q es <= envp_factor r q es)%Q.
Proof.
  intros r q Hr1 Hq0 Hq1 es. unfold envp_point.
  rewrite <- (Qmult_1_l (envp_factor r q es)) at 2.
  apply Qmult_le_compat_r;
    [exact Hr1 | apply envp_factor_nonneg; assumption].
Qed.

(** THE WEIGHT.  Zero unless the core's argv and file system are the
    fixed ones; otherwise the environment's weight times the
    standard-input weight of its own length.

    Compare [geo_weight], which fixes envp too and therefore weighs
    ZERO at every core whose launch-time environment differs.  That is
    the gap this family exists to close: a defect reachable only under
    a non-canonical environment sits in a [geo_weight]-null set, so a
    fire-set bound proved against [stdin_geometric] alone says nothing
    about it.  Here the environment carries mass —
    [stdin_envp_geometric_envp_bites] below is that statement at a
    concrete pair of cores.

    The environment test is one decidable equation, "the core is the
    template with its own envp and standard input plugged in", for the
    reason [geo_weight]'s is: it is the hypothesis the enumeration
    argument already carries, so nothing stands between them. *)
Definition envp_geo_weight (p r q : Q) (argv : list (list byte))
    (fs : Fs.Fs) (c : FinCore) : Q :=
  if decide (c = mkFinCore argv (core_envp c) fs (core_stdin c))
  then (envp_point r q (core_envp c) * geo_point p (length (core_stdin c)))%Q
  else 0%Q.

Lemma envp_geo_weight_match : forall p r q argv fs es s,
  envp_geo_weight p r q argv fs (mkFinCore argv es fs s)
    = (envp_point r q es * geo_point p (length s))%Q.
Proof.
  intros p r q argv fs es s. unfold envp_geo_weight.
  cbn [core_envp core_stdin].
  destruct (decide _) as [_ | Hne]; [reflexivity | congruence].
Qed.

Lemma envp_geo_weight_mismatch : forall p r q argv fs c,
  c <> mkFinCore argv (core_envp c) fs (core_stdin c) ->
  envp_geo_weight p r q argv fs c = 0%Q.
Proof.
  intros p r q argv fs c Hne. unfold envp_geo_weight.
  destruct (decide _) as [Heq | _]; [congruence | reflexivity].
Qed.

(** THE FAMILY'S FORMULA, all six factors visible at once: entry-count
    geometric in [r], per-entry byte-geometric in [q_e], and the
    standard-input geometric in [p_stop] this file already had.  It is
    the product of [envp_point_closed_form] and
    [geo_point_closed_form], and it is stated because the specification
    is quoted in that shape and a reader should be able to check the
    definition against it without unfolding anything. *)
Lemma envp_geo_weight_closed_form : forall p r q argv fs es s,
  (envp_geo_weight p r q argv fs (mkFinCore argv es fs s)
     == r * Qpow (1 - r) (length es) * entries_geo_product q es
        * (p * Qpow (1 - p) (length s) * Qpow (1 # 256) (length s)))%Q.
Proof.
  intros p r q argv fs es s.
  rewrite envp_geo_weight_match, envp_point_closed_form,
    geo_point_closed_form.
  ring.
Qed.

Lemma envp_geo_weight_nonneg : forall p r q argv fs,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= r)%Q -> (r <= 1)%Q ->
  (0 <= q)%Q -> (q <= 1)%Q ->
  forall c, (0 <= envp_geo_weight p r q argv fs c)%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 c. unfold envp_geo_weight.
  destruct (decide _) as [_ | _]; [| apply Qle_refl].
  apply Qmult_le_0_compat;
    [apply envp_point_nonneg | apply geo_point_nonneg]; assumption.
Qed.

(** The distribution.  Mass [1] is DECLARED, as everywhere in this file,
    and [stdin_envp_geometric_mass_upper] below is the proof that owes
    something to it.  The six side conditions are constructor arguments
    for the reason [stdin_geometric]'s two are: [cd_nonneg] is a field.

    Declaring [1] — rather than, say, the envp mass times the stdin mass
    written out — is what keeps a MIXTURE of this family with
    [stdin_geometric] at total mass [1] under [cd_scale] by shares
    summing to [1], which is the composition the calibrated example at
    the end of the file spells out.

    None of the three strict inequalities is demanded, for the reason
    [stdin_geometric] does not demand [0 < p_stop]: nothing the
    constructor needs uses them, and the lower certificate that does
    asks for all three as hypotheses of ITS OWN statement. *)
Definition stdin_envp_geometric (p r q : Q) (argv : list (list byte))
    (fs : Fs.Fs)
    (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q)
    (Hr0 : (0 <= r)%Q) (Hr1 : (r <= 1)%Q)
    (Hq0 : (0 <= q)%Q) (Hq1 : (q <= 1)%Q) : CoreDistribution :=
  mkCoreDistribution (envp_geo_weight p r q argv fs) 1
    (envp_geo_weight_nonneg p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).

(* =========================================================================
   The envp cylinder, and the enumeration that bounds it
   ========================================================================= *)

(** Every environment extending [es] by at most [M] further entries,
    each of them shorter than [L], as a list.  It is [cyl_enum] one
    level up: the stopping environment, then for each admissible ENTRY
    the enumeration of the environments one entry deeper.

    Two depths where [cyl_enum] has one, and the second is not
    avoidable: an environment's continuations are indexed by an entry,
    an entry is a byte list, and there are infinitely many of those.
    [short_inputs L] is the same length-bounded enumeration of byte
    lists the geometric lower certificate already uses, so no new
    enumeration of entries is written here.

    As with [cyl_enum], duplicate-freedom of this list is never proved
    and never needed for the BOUNDS — [qsum_core_incl_le] asks
    nothing of the list it bounds against.  The lower certificate does
    need it, and proves it separately for the family it actually
    exhibits ([envps_upto_nodup]). *)
Fixpoint envp_enum (es : list (list byte)) (M L : nat)
    : list (list (list byte)) :=
  match M with
  | O => [es]
  | S M' =>
      es :: List.flat_map (fun e => envp_enum (es ++ [e]) M' L) (short_inputs L)
  end.

(** It misses nothing within its two depths. *)
Lemma envp_enum_complete : forall M L es rest,
  (length rest <= M)%nat ->
  (forall e, List.In e rest -> (length e < L)%nat) ->
  List.In (es ++ rest) (envp_enum es M L).
Proof.
  intros M L. induction M as [| M IH]; intros es rest Hlen Hent.
  - destruct rest as [| e rest]; [| cbn [length] in Hlen; lia].
    rewrite List.app_nil_r. left. reflexivity.
  - destruct rest as [| e rest].
    + rewrite List.app_nil_r. left. reflexivity.
    + right. apply List.in_flat_map. exists e. split.
      * apply short_inputs_complete. apply Hent. left. reflexivity.
      * replace (es ++ e :: rest) with ((es ++ [e]) ++ rest)
          by (rewrite <- List.app_assoc; reflexivity).
        apply IH.
        -- cbn [length] in Hlen. lia.
        -- intros x Hx. apply Hent. right. exact Hx.
Qed.

(** ONE STEP OF THE ENVP CANCELLATION, as an exact identity: the
    environments one entry deeper than [es] carry, between them,
    [envp_factor] of [es] times [(1 - r)] times what the entry
    enumeration itself weighs.

    This is where the per-entry byte-geometric is spent, and it is spent
    through the lemma that already knows the answer:
    [short_inputs_sum] evaluates the entry enumeration to
    [geo_prefix_sum q_e L], which [geo_prefix_sum_closed] closes to
    [1 - (1 - q_e) ^ L].  Only the [<= 1] of that number is used below,
    but the identity is stated exactly because a bound whose slack is
    invisible is a bound nobody can sharpen. *)
Lemma qsum_envp_factor_step : forall r q es L,
  (qsum (fun e => envp_factor r q (es ++ [e])) (short_inputs L)
     == envp_factor r q es * (1 - r) * (1 - Qpow (1 - q) L))%Q.
Proof.
  intros r q es L.
  rewrite (qsum_ext (fun e => envp_factor r q (es ++ [e]))
             (fun e => ((envp_factor r q es * (1 - r))
                        * geo_point q (length e))%Q))
    by (intros e _; rewrite envp_factor_app, envp_factor_one; ring).
  rewrite (qsum_scale (envp_factor r q es * (1 - r))%Q
             (fun e => geo_point q (length e)) (short_inputs L)).
  rewrite short_inputs_sum, geo_prefix_sum_closed. ring.
Qed.

(** THE CANCELLATION on the envp coordinate, by induction on the entry
    depth: the whole enumeration weighs no more than the mass of the
    environments extending [es], at every depth and every prefix.

    The step is the same shape [cyl_enum_sum_le]'s is, with one
    difference worth naming.  There the 256 continuations are charged a
    common constant and [256 * (1 # 256)] folds to [1] exactly, so the
    step is lossless.  Here the continuations are charged what their own
    entry costs and their total is [1 - (1 - q_e) ^ L], which is under
    [1] rather than equal to it: an entry longer than [L] is a
    continuation the enumeration omits.  The bound stays true because
    the omitted mass is nonnegative, and the slack is real — it is the
    same slack [stdin_geometric_bound_by_max_length] measures on the
    standard-input coordinate, and it vanishes as [L] grows, which is
    what the lower certificate below spends.

    The base case is where [r <= 1] is used for something other than
    nonnegativity: a depth-zero enumeration holds only the stopping
    environment, which weighs [r] times the mass and must be under
    it. *)
Lemma envp_enum_sum_le : forall r q,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= q)%Q -> (q <= 1)%Q ->
  forall M L es,
    (qsum (envp_point r q) (envp_enum es M L) <= envp_factor r q es)%Q.
Proof.
  intros r q Hr0 Hr1 Hq0 Hq1 M L. induction M as [| M IH]; intros es.
  - cbn [envp_enum]. rewrite qsum_cons, (@qsum_nil _ (envp_point r q)).
    rewrite Qplus_0_r. apply envp_point_le_factor; assumption.
  - cbn [envp_enum]. rewrite qsum_cons.
    apply (Qle_trans _ (envp_point r q es
                        + qsum (fun e => envp_factor r q (es ++ [e]))
                            (short_inputs L))%Q).
    + apply Qplus_le_compat; [apply Qle_refl |].
      apply (qsum_flat_map_le _ _
               (fun e => envp_factor r q (es ++ [e]))).
      intros e _. apply IH.
    + rewrite qsum_envp_factor_step. unfold envp_point.
      apply (Qle_trans _ (r * envp_factor r q es
                          + envp_factor r q es * (1 - r) * 1)%Q);
        [| apply Qle_of_Qeq; ring].
      apply Qplus_le_compat; [apply Qle_refl |].
      apply (Qle_trans _ ((1 - Qpow (1 - q) L)
                          * (envp_factor r q es * (1 - r)))%Q);
        [apply Qle_of_Qeq; ring |].
      apply (Qle_trans _ (1 * (envp_factor r q es * (1 - r)))%Q);
        [| apply Qle_of_Qeq; ring].
      apply Qmult_le_compat_r.
      * apply (proj2 (Qle_minus_iff (1 - Qpow (1 - q) L) 1)).
        apply (Qle_trans _ (Qpow (1 - q) L)%Q);
          [ apply Qpow_nonneg; apply (Qle_minus_iff q 1); exact Hq1
          | apply Qle_of_Qeq; ring].
      * apply Qmult_le_0_compat;
          [ apply envp_factor_nonneg; assumption
          | apply (Qle_minus_iff r 1); exact Hr1].
Qed.

(* =========================================================================
   The two coordinates, recombined
   ========================================================================= *)

(** Every core over the fixed argv and file system whose environment
    comes from [A] and whose standard input comes from [B].

    A core of this family is a PAIR — an environment and a standard
    input — and the weight is the product of one factor per coordinate,
    so the enumeration is the product of the two coordinates'
    enumerations and its sum is the product of their sums
    ([qsum_envp_stdin_product]).  That identity is what lets
    every bound below be assembled from an envp bound and a
    standard-input bound proved apart, and it is the only place the
    two coordinates meet. *)
Definition envp_stdin_product (argv : list (list byte)) (fs : Fs.Fs)
    (A : list (list (list byte))) (B : list (list byte)) : list FinCore :=
  List.flat_map (fun es => List.map (mkFinCore argv es fs) B) A.

Lemma In_envp_stdin_product : forall argv fs A B es s,
  List.In es A -> List.In s B ->
  List.In (mkFinCore argv es fs s) (envp_stdin_product argv fs A B).
Proof.
  intros argv fs A B es s HA HB. apply List.in_flat_map. exists es.
  split; [exact HA | apply List.in_map; exact HB].
Qed.

Lemma qsum_envp_geo_block : forall p r q argv fs es B,
  (qsum (envp_geo_weight p r q argv fs) (List.map (mkFinCore argv es fs) B)
     == qsum (fun s => geo_point p (length s)) B * envp_point r q es)%Q.
Proof.
  intros p r q argv fs es B. rewrite qsum_map.
  rewrite (qsum_ext (fun s => envp_geo_weight p r q argv fs
                                  (mkFinCore argv es fs s))
             (fun s => (envp_point r q es * geo_point p (length s))%Q))
    by (intros s _; rewrite envp_geo_weight_match; reflexivity).
  rewrite (qsum_scale (envp_point r q es)
             (fun s => geo_point p (length s)) B).
  ring.
Qed.

Lemma qsum_envp_stdin_product : forall p r q argv fs A B,
  (qsum (envp_geo_weight p r q argv fs)
     (envp_stdin_product argv fs A B)
     == qsum (envp_point r q) A
        * qsum (fun s => geo_point p (length s)) B)%Q.
Proof.
  intros p r q argv fs A B.
  unfold envp_stdin_product.
  rewrite qsum_flat_map. cbv beta.
  rewrite (qsum_ext (fun es => qsum (envp_geo_weight p r q argv fs)
                                   (List.map (mkFinCore argv es fs) B))
             (fun es => (qsum (fun s => geo_point p (length s)) B
                         * envp_point r q es)%Q))
    by (intros es _; apply qsum_envp_geo_block).
  rewrite (qsum_scale (qsum (fun s => geo_point p (length s)) B)
             (envp_point r q) A).
  ring.
Qed.

(** The product of two duplicate-free enumerations repeats nothing: the
    blocks are duplicate-free because a core determines its standard
    input, and two blocks are disjoint because a core determines its
    environment.  Only the lower certificate needs this — the bounds
    are proved against a containing list nobody has to show
    duplicate-free. *)
Lemma NoDup_envp_stdin_product : forall argv fs A B,
  List.NoDup A -> List.NoDup B ->
  List.NoDup (envp_stdin_product argv fs A B).
Proof.
  intros argv fs A B HA HB. unfold envp_stdin_product.
  apply NoDup_flat_map; [exact HA | |].
  - intros es _. apply NoDup_map_inj; [| exact HB].
    intros x y _ _ Heq. apply (f_equal core_stdin) in Heq. exact Heq.
  - intros es1 es2 c _ _ H1 H2.
    apply List.in_map_iff in H1 as [s1 [Hs1 _]].
    apply List.in_map_iff in H2 as [s2 [Hs2 _]].
    rewrite <- Hs1 in Hs2. apply (f_equal core_envp) in Hs2.
    cbn [core_envp] in Hs2. symmetry. exact Hs2.
Qed.

(* =========================================================================
   The three depths, read off the task's own list
   ========================================================================= *)

(** [Measure.weight_bound_T]'s lists are finite, and that is the whole
    of what the bounds below need from them.  Where [stdin_geometric]
    reads ONE depth off the list — the largest standard-input length —
    this family reads THREE, one per axis of the enumeration: how many
    entries an environment has, how long an entry is, and how long a
    standard input is.  Each is a [List.list_max] over the list, so each
    exists because the list is finite and for no other reason.

    The entry depth is [S] of a maximum rather than the maximum, because
    [short_inputs] enumerates the byte lists STRICTLY shorter than its
    argument and an entry of the maximum length has to be inside. *)
Definition cores_envp_depth (cs : list FinCore) : nat :=
  List.list_max (List.map (fun c => length (core_envp c)) cs).

Definition cores_entry_depth (cs : list FinCore) : nat :=
  S (List.list_max
       (List.map (fun c => List.list_max
                             (List.map (fun e => length e) (core_envp c))) cs)).

Definition cores_stdin_depth (cs : list FinCore) : nat :=
  List.list_max (List.map (fun c => length (core_stdin c)) cs).

Lemma cores_envp_depth_ge : forall cs c,
  List.In c cs -> (length (core_envp c) <= cores_envp_depth cs)%nat.
Proof.
  intros cs c Hc. apply list_max_ge. apply List.in_map_iff.
  exists c. split; [reflexivity | exact Hc].
Qed.

Lemma cores_entry_depth_gt : forall cs c e,
  List.In c cs -> List.In e (core_envp c) ->
  (length e < cores_entry_depth cs)%nat.
Proof.
  intros cs c e Hc He. unfold cores_entry_depth.
  assert (Hinner : (length e
                    <= List.list_max
                         (List.map (fun x => length x) (core_envp c)))%nat).
  { apply list_max_ge. apply List.in_map_iff.
    exists e. split; [reflexivity | exact He]. }
  assert (Houter : (List.list_max
                      (List.map (fun x => length x) (core_envp c))
                    <= List.list_max
                         (List.map (fun c0 => List.list_max
                                      (List.map (fun x => length x)
                                         (core_envp c0))) cs))%nat).
  { apply list_max_ge. apply List.in_map_iff.
    exists c. split; [reflexivity | exact Hc]. }
  lia.
Qed.

Lemma cores_stdin_depth_ge : forall cs c,
  List.In c cs -> (length (core_stdin c) <= cores_stdin_depth cs)%nat.
Proof.
  intros cs c Hc. apply list_max_ge. apply List.in_map_iff.
  exists c. split; [reflexivity | exact Hc].
Qed.

(* =========================================================================
   The cylinder bound over cores
   ========================================================================= *)

(** The cores this bound is about: the fixed argv and file system, an
    environment EXTENDING [es] and a standard input EXTENDING [bs].
    Two existentials rather than a conjunction of four tests, for the
    reason [in_stdin_cylinder] is one: it is the form both the
    construction and the enumeration want. *)
Definition in_envp_stdin_cylinder (argv : list (list byte)) (fs : Fs.Fs)
    (es : list (list byte)) (bs : list byte) (c : FinCore) : Prop :=
  exists eext ext, c = mkFinCore argv (es ++ eext) fs (bs ++ ext).

(** The cylinder's mass: the product of what the two coordinates
    contribute, which is [envp_factor] on one and [geo_mass] on the
    other. *)
Definition stdin_envp_geometric_cylinder_mass (p r q : Q)
    (es : list (list byte)) (bs : list byte) : Q :=
  (envp_factor r q es * geo_mass p (length bs))%Q.

Lemma stdin_envp_geometric_cylinder_mass_closed_form : forall p r q es bs,
  (stdin_envp_geometric_cylinder_mass p r q es bs
     == Qpow (1 - r) (length es) * entries_geo_product q es
        * (Qpow (1 - p) (length bs) * Qpow (1 # 256) (length bs)))%Q.
Proof.
  intros p r q es bs. unfold stdin_envp_geometric_cylinder_mass.
  rewrite envp_factor_closed_form, geo_mass_closed_form. ring.
Qed.

(** THE BOUND OVER CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.

    Three enumeration depths are read off the list and the product of
    the two coordinates' enumerations contains it; the sum of that
    product is the product of the two sums
    ([qsum_envp_stdin_product]), and each factor has its own
    bound already ([envp_enum_sum_le], [bytes_cyl_sum_le]).
    [Qmult_le_compat_nonneg] is what puts the two together, and the
    nonnegativity it asks for is the two enumerations' own. *)
Lemma envp_geo_weight_cylinder_bound : forall p r q argv fs,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= r)%Q -> (r <= 1)%Q ->
  (0 <= q)%Q -> (q <= 1)%Q ->
  forall es bs cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> in_envp_stdin_cylinder argv fs es bs c) ->
    (qsum (envp_geo_weight p r q argv fs) cs
       <= stdin_envp_geometric_cylinder_mass p r q es bs)%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs cs Hnd Hcyl.
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (envp_stdin_product argv fs
                  (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs))
                  (bytes_cyl bs (cores_stdin_depth cs))))
    | rewrite qsum_envp_stdin_product;
      unfold stdin_envp_geometric_cylinder_mass;
      apply Qmult_le_compat_nonneg;
      [ split;
        [ apply qsum_nonneg; intros x _; apply envp_point_nonneg; assumption
        | apply envp_enum_sum_le; assumption ]
      | split;
        [ apply qsum_nonneg; intros x _; apply geo_point_nonneg; assumption
        | apply bytes_cyl_sum_le; assumption ] ] ].
  - apply envp_geo_weight_nonneg; assumption.
  - exact Hnd.
  - intros c Hc. destruct (Hcyl c Hc) as [eext [ext Heq]].
    assert (Henvp := cores_envp_depth_ge cs c Hc).
    assert (Hstdin := cores_stdin_depth_ge cs c Hc).
    rewrite Heq in Henvp, Hstdin. cbn [core_envp core_stdin] in Henvp, Hstdin.
    rewrite List.length_app in Henvp, Hstdin.
    rewrite Heq. apply In_envp_stdin_product.
    + apply envp_enum_complete; [lia |].
      intros e He. apply (cores_entry_depth_gt cs c e Hc).
      rewrite Heq. cbn [core_envp]. apply List.in_or_app. right. exact He.
    + apply bytes_cyl_In. lia.
Qed.

(* =========================================================================
   The envp-varying family's exports
   ========================================================================= *)

(** THE EXPORT: a list of records with duplicate-free cores, all lying
    in the cylinder over an environment prefix and a standard-input
    prefix, weighs at most that cylinder's mass.  The hypothesis is the
    one [Measure.weight_bound_T] carries, and [core_sum_map_fin_core] is
    the only step between them.

    This is the statement the family exists for: a fire set described by
    "the environment begins with these entries and standard input begins
    with these bytes" is charged a number that DEPENDS ON THE
    ENVIRONMENT, where [stdin_geometric_bound] would charge either the
    stdin cylinder's whole mass (if the environment happened to be the
    fixed one) or nothing at all (if it did not, because nothing there
    weighs anything). *)
Lemma stdin_envp_geometric_bound :
  forall p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_envp_stdin_cylinder argv fs es bs (fin_core f)) ->
  (core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= stdin_envp_geometric_cylinder_mass p r q es bs)%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs l Hnd Hcyl.
  cbn [cd_weight stdin_envp_geometric]. rewrite core_sum_map_fin_core.
  apply envp_geo_weight_cylinder_bound; try assumption.
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. apply Hcyl. exact Hin.
Qed.

(** The launch-time test as a boolean, so that [List.filter] can use it.
    It is [matches_env] with the environment left free: this family
    fixes argv and the file system and nothing else, so the equation a
    core has to satisfy in order to weigh anything is the template with
    BOTH its envp and its standard input plugged in.

    [Measure]'s [Qle_bool] exception is not in play, for the reason it
    is not in [matches_env]: this decides an equality of CORES, which
    [FinCore_eq_dec] decides outright, and no rational is involved. *)
Definition matches_argv_fs (argv : list (list byte)) (fs : Fs.Fs)
    (c : FinCore) : bool :=
  if decide (c = mkFinCore argv (core_envp c) fs (core_stdin c))
  then true else false.

Lemma matches_argv_fs_false : forall argv fs c,
  matches_argv_fs argv fs c = false ->
  c <> mkFinCore argv (core_envp c) fs (core_stdin c).
Proof.
  intros argv fs c H. unfold matches_argv_fs in H.
  destruct (decide _) as [_ | Hne]; [discriminate H | exact Hne].
Qed.

Lemma matches_argv_fs_true : forall argv fs c,
  matches_argv_fs argv fs c = true ->
  c = mkFinCore argv (core_envp c) fs (core_stdin c).
Proof.
  intros argv fs c H. unfold matches_argv_fs in H.
  destruct (decide _) as [Heq | _]; [exact Heq | discriminate H].
Qed.

(** THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE, exactly as
    [stdin_geometric_bound_or_off_environment] slackens its own: each
    record is in the cylinder OR its core misses the fixed argv or file
    system and therefore weighs nothing.  Both forms stay; neither
    weakens the other, and the repair the widening saves a consumer is
    the same dozen non-obvious lines. *)
Lemma stdin_envp_geometric_bound_or_off_environment :
  forall p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_envp_stdin_cylinder argv fs es bs (fin_core f)
     \/ matches_argv_fs argv fs (fin_core f) = false) ->
  (core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= stdin_envp_geometric_cylinder_mass p r q es bs)%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs l Hnd Hor.
  cbn [cd_weight stdin_envp_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_argv_fs argv fs))
    by (intros c Hc;
        rewrite (envp_geo_weight_mismatch p r q argv fs c
                   (matches_argv_fs_false _ _ _ Hc)); reflexivity).
  apply envp_geo_weight_cylinder_bound; try assumption.
  - apply List.NoDup_filter. exact Hnd.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (Hor f Hinl) as [Hcyl | Hoff].
    + rewrite <- Hf. exact Hcyl.
    + rewrite Hf in Hoff. rewrite Hoff in Hm. discriminate Hm.
Qed.

(** UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass [1].  It is the disjunctive bound at the EMPTY environment
    prefix and the EMPTY standard-input prefix, and the whole content is
    that the disjunction is EXHAUSTIVE there — a core either matches the
    fixed argv and file system, in which case its environment is
    [[] ++ itself] and its standard input is [[] ++ itself], or it does
    not.  Both cylinder masses at the empty prefix are [1], one because
    [envp_factor] of no entries is and one because [Qpow] at exponent
    zero is. *)
Lemma stdin_envp_geometric_mass_upper :
  forall p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= cd_mass (stdin_envp_geometric p r q argv fs
                   Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 l Hnd.
  cbn [cd_mass stdin_envp_geometric].
  apply (Qle_trans _ (stdin_envp_geometric_cylinder_mass p r q [] [])).
  - apply stdin_envp_geometric_bound_or_off_environment; [exact Hnd |].
    intros f Hf. destruct (matches_argv_fs argv fs (fin_core f)) eqn:Hm.
    + left. exists (core_envp (fin_core f)), (core_stdin (fin_core f)).
      cbn [List.app]. apply matches_argv_fs_true. exact Hm.
    + right. reflexivity.
  - apply Qle_of_Qeq.
    unfold stdin_envp_geometric_cylinder_mass, geo_mass.
    cbn [length envp_factor]. rewrite Qpow_0. ring.
Qed.

(* =========================================================================
   Bounds that charge the environment nothing
   ========================================================================= *)

(** A list whose cores match the fixed argv and file system and whose
    standard inputs all come from a given enumeration [B] weighs at most
    what [B] weighs — the environment coordinate is charged [1], its
    whole declared mass, and nothing about the environment is assumed.

    This is the shape both remaining bounds take.  A task that knows
    nothing about the environments in its fire set gets exactly the
    standard-input bound [stdin_geometric] would have given it, which is
    the right answer: mixing an envp-varying component in must not make
    a stdin-only argument WORSE, and this lemma is that claim.  The
    price is that the envp enumeration still has to be built, because
    the cores have to sit inside SOMETHING finite — the two entry depths
    are read off the list and thrown away, and the [1] they are charged
    is [envp_enum_sum_le] at the empty prefix. *)
Lemma envp_geo_weight_stdin_family_bound : forall p r q argv fs,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= r)%Q -> (r <= 1)%Q ->
  (0 <= q)%Q -> (q <= 1)%Q ->
  forall (B : list (list byte)) (SB : Q) cs,
    (qsum (fun s => geo_point p (length s)) B <= SB)%Q ->
    List.NoDup cs ->
    (forall c, List.In c cs ->
       c = mkFinCore argv (core_envp c) fs (core_stdin c)
       /\ List.In (core_stdin c) B) ->
    (qsum (envp_geo_weight p r q argv fs) cs <= SB)%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 B SB cs HB Hnd Hall.
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (envp_stdin_product argv fs
                  (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs))
                  B))
    | rewrite qsum_envp_stdin_product;
      apply (Qle_trans _ (1 * SB)%Q); [| apply Qle_of_Qeq; ring];
      apply Qmult_le_compat_nonneg;
      [ split;
        [ apply qsum_nonneg; intros x _; apply envp_point_nonneg; assumption
        | apply (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ []) ]
      | split;
        [ apply qsum_nonneg; intros x _; apply geo_point_nonneg; assumption
        | exact HB ] ] ].
  - apply envp_geo_weight_nonneg; assumption.
  - exact Hnd.
  - intros c Hc. destruct (Hall c Hc) as [Hmatch Hstdin].
    assert (Hins : List.In ([] ++ core_envp c)
                     (envp_enum [] (cores_envp_depth cs)
                        (cores_entry_depth cs))).
    { apply envp_enum_complete; [apply cores_envp_depth_ge; exact Hc |].
      intros e He. apply (cores_entry_depth_gt cs c e Hc). exact He. }
    cbn [List.app] in Hins.
    assert (Hprod := In_envp_stdin_product argv fs
                       (envp_enum [] (cores_envp_depth cs)
                          (cores_entry_depth cs)) B
                       (core_envp c) (core_stdin c) Hins Hstdin).
    rewrite <- Hmatch in Hprod. exact Hprod.
Qed.

(** THE LENGTH SLICE: a list drawn from one standard-input length slice
    weighs at most [p_stop * (1 - p_stop) ^ n], with no [1/256] left in
    it and nothing charged for the environment.

    It is [stdin_geometric_slice_bound]'s constant exactly, which is the
    point — the counting lemma that produces it
    ([injective_core_list_in_cylinder_length_bound]) is not restated
    here and not needed, because the slice's total is already known
    ([byte_lists_sum], from [qsum_full_slice]).  Note that the
    hypothesis does NOT fix the environment: the records may carry any
    envp at all, and the slice still weighs no more.

    WHAT IS NOT CLAIMED, and the difference from [stdin_geometric] is
    worth naming rather than leaving to be inferred from an absent
    lemma: this constant is not pinned as ATTAINED, and no sharpness
    lemma accompanies it.  There the slice is finite and
    [stdin_geometric_slice_bound_attained] exhibits a list reaching the
    constant outright.  Here the slice over a fixed standard-input
    length still holds one core per ENVIRONMENT, of which there are
    infinitely many carrying positive weight whenever [r < 1], so a
    finite list reaching the constant is not available by the same
    argument and none is offered.  The bound is an upper bound and is
    stated as one. *)
Lemma stdin_envp_geometric_slice_bound :
  forall p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = mkFinCore argv (fin_envp f) fs (fin_stdin f)
     /\ length (fin_stdin f) = n) ->
  (core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= p * Qpow (1 - p) n)%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 n l Hnd Hall.
  cbn [cd_weight stdin_envp_geometric]. rewrite core_sum_map_fin_core.
  apply (envp_geo_weight_stdin_family_bound p r q argv fs
           Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 (byte_lists n));
    [ apply Qle_of_Qeq; apply byte_lists_sum | exact Hnd |].
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  destruct (Hall f Hin) as [Henv Hlen]. subst c. split; [exact Henv |].
  cbn [fin_core core_stdin]. rewrite <- Hlen. apply byte_lists_complete.
Qed.

(** A list confined to standard inputs of length at most [n] weighs at
    most [1 - (1 - p_stop) ^ (n + 1)] — the partial sum at its own
    horizon, and again the environment is charged nothing.  It is
    [stdin_geometric_bound_by_max_length]'s number, reached the same
    way: filter away the cores that miss the fixed argv or file system,
    place what remains inside [short_inputs (S n)], and evaluate that
    family exactly ([short_inputs_sum], [geo_prefix_sum_closed]).

    It MISSES THE TAIL, and the tail is what
    [stdin_envp_geometric_mass_not_attained] below is made of. *)
Lemma stdin_envp_geometric_bound_by_max_length :
  forall p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> (length (fin_stdin f) <= n)%nat) ->
  (core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 n l Hnd Hlen.
  cbn [cd_weight stdin_envp_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_argv_fs argv fs))
    by (intros c Hc;
        rewrite (envp_geo_weight_mismatch p r q argv fs c
                   (matches_argv_fs_false _ _ _ Hc)); reflexivity).
  apply (envp_geo_weight_stdin_family_bound p r q argv fs
           Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 (short_inputs (S n)));
    [ apply Qle_of_Qeq;
      rewrite short_inputs_sum; apply geo_prefix_sum_closed
    | apply List.NoDup_filter; exact Hnd |].
  intros c Hc. apply List.filter_In in Hc as [Hin Hm].
  split; [apply matches_argv_fs_true; exact Hm |].
  apply short_inputs_complete.
  apply List.in_map_iff in Hin as [f [Hf Hinl]].
  assert (Hle := Hlen f Hinl). rewrite <- Hf. cbn [fin_core core_stdin]. lia.
Qed.

(* =========================================================================
   ... and this mass is a SUPREMUM and not a maximum either
   ========================================================================= *)

(** For [p_stop < 1] NO admissible list weighs the declared mass — every
    one of them weighs strictly less.  The proof is
    [stdin_geometric_mass_not_attained]'s, unchanged: the list's own
    longest standard input is a horizon, and beyond it sits a positive
    tail the list does not collect.

    Only [p_stop < 1] is asked for.  The environment coordinate needs no
    hypothesis at all here, and the reason is worth stating: the
    shortfall is already there on the standard-input axis alone, so
    degenerate [r] or [q_e] can only make it larger.  A family that
    tried to derive the strictness from the ENVIRONMENT axis would need
    [r < 1] instead, and would then be false at [r = 1] — where every
    environment is empty and only the standard input varies. *)
Lemma stdin_envp_geometric_mass_not_attained :
  forall p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                            Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
       < cd_mass (stdin_envp_geometric p r q argv fs
                    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hlt l Hnd.
  cbn [cd_mass stdin_envp_geometric].
  pose (n := List.list_max (List.map (fun f => length (fin_stdin f)) l)).
  apply (Qle_lt_trans _ (1 - Qpow (1 - p) (S n))%Q).
  - apply stdin_envp_geometric_bound_by_max_length; [exact Hnd |].
    intros f Hf. apply list_max_ge. apply List.in_map_iff.
    exists f. split; [reflexivity | exact Hf].
  - apply (proj2 (Qlt_minus_iff (1 - Qpow (1 - p) (S n)) 1)).
    apply (Qlt_le_trans _ (Qpow (1 - p) (S n))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qpow_pos. apply (Qlt_minus_iff p 1). exact Hlt.
Qed.

(** The same fact under the name a reader looks for, beside
    [stdin_geometric_mass_supremum_not_maximum]. *)
Lemma stdin_envp_geometric_mass_supremum_not_maximum :
  forall p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    ~ (core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                              Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
         == cd_mass (stdin_envp_geometric p r q argv fs
                       Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hlt l Hnd.
  apply Qlt_not_eq.
  apply stdin_envp_geometric_mass_not_attained; assumption.
Qed.

(* =========================================================================
   Two elementary inequalities the envp lower certificate runs on
   ========================================================================= *)

(** BERNOULLI, in the one direction this file needs, stated multiplied
    out so that it carries no side condition beyond [0 <= x <= 1].

    [geo_gap_bound] above is the other elementary estimate on the same
    quantity, and the two are used for opposite purposes.  That one
    bounds a power of [1 - p_stop] from ABOVE, which is how a TAIL is
    made small.  This one bounds from BELOW, and it is needed because
    the environment coordinate's shortfall is a power OF A SUM: an
    enumeration of environments with at most [M] entries collects
    [G ^ M] of the per-entry mass, where [G] is what one entry slot
    collects, and turning "each slot misses at most [x]" into "the
    environment misses at most [M * x]" is exactly this inequality.

    The step is one square: [(1 - m * x) * (1 - x)] exceeds
    [1 - (1 + m) * x] by [m * x * x], and [ring] checks that. *)
Lemma Qpow_one_minus_lower : forall x m,
  (0 <= x)%Q -> (x <= 1)%Q -> (1 - Qnat m * x <= Qpow (1 - x) m)%Q.
Proof.
  intros x m Hx0 Hx1.
  assert (H1x : (0 <= 1 - x)%Q) by (apply (Qle_minus_iff x 1); exact Hx1).
  induction m as [| m IH].
  - rewrite Qpow_0, Qnat_0. apply Qle_of_Qeq. ring.
  - rewrite Qpow_succ, Qnat_succ.
    apply (Qle_trans _ ((1 - Qnat m * x) * (1 - x))%Q).
    + apply (proj2 (Qle_minus_iff (1 - (1 + Qnat m) * x)
                      ((1 - Qnat m * x) * (1 - x)))).
      apply (Qle_trans _ (Qnat m * x * x)%Q);
        [ apply Qmult_le_0_compat;
            [ apply Qmult_le_0_compat; [apply Qnat_nonneg | exact Hx0]
            | exact Hx0]
        | apply Qle_of_Qeq; ring].
    + apply (Qle_trans _ (Qpow (1 - x) m * (1 - x))%Q);
        [ apply Qmult_le_compat_r; [exact IH | exact H1x]
        | apply Qle_of_Qeq; ring].
Qed.

(** THREE MARGINS COMPOSE, which is the arithmetic the certificate's
    three independent approximations meet in: if three factors fall
    short of [1] by [a], [b] and [c], their product falls short by at
    most [a + b + c].  The difference is
    [a * b * (1 - c) + c * (a + b)], nonnegative term by term, and
    [ring] checks that identity.  No bound on [a] or [b] is needed —
    only [c <= 1], for the one factor the identity multiplies by. *)
Lemma Qmargins_three : forall a b c,
  (0 <= a)%Q -> (0 <= b)%Q -> (0 <= c)%Q -> (c <= 1)%Q ->
  (1 - (a + b + c) <= (1 - a) * (1 - b) * (1 - c))%Q.
Proof.
  intros a b c Ha Hb Hc Hc1.
  assert (H1c : (0 <= 1 - c)%Q) by (apply (Qle_minus_iff c 1); exact Hc1).
  apply (proj2 (Qle_minus_iff (1 - (a + b + c))
                  ((1 - a) * (1 - b) * (1 - c)))).
  apply (Qle_trans _ (a * b * (1 - c) + c * (a + b))%Q);
    [| apply Qle_of_Qeq; ring].
  apply Qplus_nonneg.
  - apply Qmult_le_0_compat;
      [apply Qmult_le_0_compat; [exact Ha | exact Hb] | exact H1c].
  - apply Qmult_le_0_compat;
      [exact Hc | apply Qplus_nonneg; [exact Ha | exact Hb]].
Qed.

(* =========================================================================
   The environment witness family, and what it weighs
   ========================================================================= *)

(** Every environment of EXACTLY [m] entries, each entry shorter than
    [L], and then every environment of FEWER than [M] entries — the two
    are to [envp_enum] what [byte_lists] and [short_inputs] are to
    [cyl_enum], and they are written the same way for the same reason:
    a slice at a time makes the sum below one [qsum_app] per
    step.

    [envp_enum] is not reused here even though it enumerates the same
    environments, because the certificate needs the list to be
    DUPLICATE-FREE and [envp_enum] is not: it names the stopping
    environment at every depth it passes through.  The bounds above
    never needed that, which is why they use the cheaper enumeration. *)
Fixpoint envps_len (L m : nat) : list (list (list byte)) :=
  match m with
  | O => [[]]
  | S m' =>
      List.flat_map
        (fun e => List.map (fun es => e :: es) (envps_len L m'))
        (short_inputs L)
  end.

Fixpoint envps_upto (L M : nat) : list (list (list byte)) :=
  match M with
  | O => []
  | S M' => envps_len L M' ++ envps_upto L M'
  end.

Lemma envps_len_In_length : forall L m es,
  List.In es (envps_len L m) -> length es = m.
Proof.
  intros L m. induction m as [| m IH]; intros es Hes.
  - destruct Hes as [Heq | []]. rewrite <- Heq. reflexivity.
  - cbn [envps_len] in Hes. apply List.in_flat_map in Hes as [e [He Hin]].
    apply List.in_map_iff in Hin as [es' [Heq Hin']].
    rewrite <- Heq. cbn [length]. rewrite (IH es' Hin'). reflexivity.
Qed.

Lemma envps_len_In_entry : forall L m es e,
  List.In es (envps_len L m) -> List.In e es -> (length e < L)%nat.
Proof.
  intros L m. induction m as [| m IH]; intros es e Hes He.
  - destruct Hes as [Heq | []]. rewrite <- Heq in He. destruct He.
  - cbn [envps_len] in Hes. apply List.in_flat_map in Hes as [e0 [He0 Hin]].
    apply List.in_map_iff in Hin as [es' [Heq Hin']].
    rewrite <- Heq in He. destruct He as [Hhd | Htl].
    + rewrite <- Hhd. apply short_inputs_In_length. exact He0.
    + exact (IH es' e Hin' Htl).
Qed.

(** ... and it repeats nothing.  Distinct first entries give disjoint
    blocks, which is [NoDup_flat_map]'s third condition, and within a
    block consing a fixed entry is injective. *)
Lemma envps_len_nodup : forall L m, List.NoDup (envps_len L m).
Proof.
  intros L m. induction m as [| m IH].
  - cbn [envps_len]. apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - cbn [envps_len]. apply NoDup_flat_map.
    + apply short_inputs_nodup.
    + intros e _. apply NoDup_map_inj; [| exact IH].
      intros x y _ _ Heq.
      apply (f_equal (@List.tl (list byte))) in Heq.
      cbn [List.tl] in Heq. exact Heq.
    + intros e1 e2 es _ _ H1 H2.
      apply List.in_map_iff in H1 as [x1 [Hx1 _]].
      apply List.in_map_iff in H2 as [x2 [Hx2 _]].
      rewrite <- Hx1 in Hx2.
      apply (f_equal (@List.hd (list byte) [])) in Hx2.
      cbn [List.hd] in Hx2. rewrite Hx2. reflexivity.
Qed.

Lemma envps_upto_In_length : forall L M es,
  List.In es (envps_upto L M) -> (length es < M)%nat.
Proof.
  intros L M. induction M as [| M IH]; intros es Hes; [destruct Hes |].
  cbn [envps_upto] in Hes. apply List.in_app_or in Hes as [Hes | Hes].
  - rewrite (envps_len_In_length L M es Hes). lia.
  - apply IH in Hes. lia.
Qed.

Lemma envps_upto_nodup : forall L M, List.NoDup (envps_upto L M).
Proof.
  intros L M. induction M as [| M IH]; [apply List.NoDup_nil |].
  cbn [envps_upto]. apply List.NoDup_app.
  - apply envps_len_nodup.
  - exact IH.
  - intros es Hin1 Hin2. apply envps_upto_In_length in Hin2.
    rewrite (envps_len_In_length L M es Hin1) in Hin2. lia.
Qed.

(** The entry-length half of what [envps_upto] promises, which
    [envps_upto_In_length] leaves to [envps_len_In_entry] one level
    down.  Stated because the pin below needs the two halves at the same
    level: "this environment is NOT in the enumeration" is what makes a
    depth constraint load-bearing, and either depth can be the reason. *)
Lemma envps_upto_In_entry : forall L M es e,
  List.In es (envps_upto L M) -> List.In e es -> (length e < L)%nat.
Proof.
  intros L M. induction M as [| M IH]; intros es e Hes He; [destruct Hes |].
  cbn [envps_upto] in Hes. apply List.in_app_or in Hes as [Hes | Hes].
  - exact (envps_len_In_entry L M es e Hes He).
  - exact (IH es e Hes He).
Qed.

(** ... and CONVERSELY the enumeration misses no environment inside its
    two depths, which is [short_inputs_complete] one level up and is
    needed for the same kind of reason: to place a FIXED environment
    inside the family rather than merely to read lengths off the family.

    This is the containment the mixture's shared witness turns on.
    [envps_upto L M] holds every environment of fewer than [M] entries
    each shorter than [L], so a task's canonical environment — whatever
    it is — is in there as soon as [M] exceeds its entry count and [L]
    its longest entry.  Neither depth is free: the certificate that
    chooses them for the margin has to be asked for depths at least this
    large as well, which is what [geo_gap_small_above] is for, and
    [stdin_geometric_on_envp_geo_lower_witness_needs_the_depths] shows
    what goes wrong when either is short. *)
Lemma envps_len_complete : forall L es,
  (forall e, List.In e es -> (length e < L)%nat) ->
  List.In es (envps_len L (length es)).
Proof.
  intros L es. induction es as [| e es IH]; intros Hlen.
  - left. reflexivity.
  - cbn [length envps_len]. apply List.in_flat_map. exists e. split.
    + apply short_inputs_complete. apply Hlen. left. reflexivity.
    + apply List.in_map. apply IH.
      intros e' He'. apply Hlen. right. exact He'.
Qed.

Lemma envps_upto_complete : forall L M es,
  (length es < M)%nat ->
  (forall e, List.In e es -> (length e < L)%nat) ->
  List.In es (envps_upto L M).
Proof.
  intros L M. induction M as [| M IH]; intros es Hlt Hlen; [exfalso; lia |].
  cbn [envps_upto]. apply List.in_or_app.
  destruct (Nat.eq_dec (length es) M) as [Heq | Hne].
  - left. rewrite <- Heq. apply envps_len_complete. exact Hlen.
  - right. apply IH; [lia | exact Hlen].
Qed.

(** ONE FULL ENTRY-COUNT SLICE weighs a power: the [m] entry slots are
    independent, each collects what the entry enumeration collects, and
    the total is that number to the [m]-th.  The base is
    [1 - (1 - q_e) ^ L], which is [short_inputs_sum] closed by
    [geo_prefix_sum_closed] — the same number
    [qsum_envp_factor_step] charges one slot above. *)
Lemma qsum_entries_geo_product_envps_len : forall q L m,
  (qsum (entries_geo_product q) (envps_len L m)
     == Qpow (1 - Qpow (1 - q) L) m)%Q.
Proof.
  intros q L m. induction m as [| m IH].
  - cbn [envps_len]. rewrite qsum_cons, (@qsum_nil _ (entries_geo_product q)).
    cbn [entries_geo_product]. rewrite Qpow_0. ring.
  - cbn [envps_len]. rewrite qsum_flat_map. cbv beta.
    rewrite (qsum_ext
               (fun e => qsum (entries_geo_product q)
                           (List.map (fun es => e :: es) (envps_len L m)))
               (fun e => (Qpow (1 - Qpow (1 - q) L) m
                          * geo_point q (length e))%Q)).
    2:{ intros e _. rewrite qsum_map. cbv beta.
        rewrite (qsum_ext (fun es => entries_geo_product q (e :: es))
                   (fun es => (geo_point q (length e)
                               * entries_geo_product q es)%Q))
          by (intros es _; cbn [entries_geo_product]; reflexivity).
        rewrite (qsum_scale (geo_point q (length e))
                   (entries_geo_product q) (envps_len L m)).
        rewrite IH. ring. }
    rewrite (qsum_scale (Qpow (1 - Qpow (1 - q) L) m)
               (fun e => geo_point q (length e)) (short_inputs L)).
    rewrite short_inputs_sum, geo_prefix_sum_closed, Qpow_succ. ring.
Qed.

Lemma qsum_envp_point_envps_len : forall r q L m,
  (qsum (envp_point r q) (envps_len L m)
     == r * Qpow (1 - r) m * Qpow (1 - Qpow (1 - q) L) m)%Q.
Proof.
  intros r q L m.
  rewrite (qsum_ext (envp_point r q)
             (fun es => ((r * Qpow (1 - r) m) * entries_geo_product q es)%Q)).
  2:{ intros es Hes. rewrite envp_point_closed_form.
      rewrite (envps_len_In_length L m es Hes). ring. }
  rewrite (qsum_scale (r * Qpow (1 - r) m)%Q (entries_geo_product q)
             (envps_len L m)).
  rewrite qsum_entries_geo_product_envps_len. ring.
Qed.

(** The partial sum of the environment series over ENTRY COUNTS, as a
    [Fixpoint] so that it is a rational a task can write down.  It is
    [geo_prefix_sum]'s counterpart on the other coordinate, with one
    difference that is the whole reason it needs its own definition:
    the ratio here is [(1 - r) * G] rather than [1 - r], because an
    environment that continues must also fill the slot it opened, and
    the slot collects [G] rather than everything.

    No closed form is stated, and that is deliberate.  [geo_prefix_sum]
    telescopes to [1 - (1 - p_stop) ^ k] because its ratio and its
    per-term factor are the same number; here they are not, so the
    closed form would be a quotient with a side condition on
    [1 - (1 - r) * G].  What the certificate actually needs is a LOWER
    bound, and [envp_prefix_sum_lower] gives one with no side condition
    at all. *)
Fixpoint envp_prefix_sum (r G : Q) (M : nat) : Q :=
  match M with
  | O => 0%Q
  | S M' => (r * Qpow (1 - r) M' * Qpow G M' + envp_prefix_sum r G M')%Q
  end.

Lemma qsum_envp_point_envps_upto : forall r q L M,
  (qsum (envp_point r q) (envps_upto L M)
     == envp_prefix_sum r (1 - Qpow (1 - q) L) M)%Q.
Proof.
  intros r q L M. induction M as [| M IH]; [reflexivity |].
  cbn [envps_upto envp_prefix_sum].
  rewrite qsum_app, IH, qsum_envp_point_envps_len. reflexivity.
Qed.

(** THE LOWER ESTIMATE: the partial sum is at least [G ^ M] times what
    the entry-count geometric alone would have collected.

    The estimate is the obvious one — every term of the sum carries
    [G ^ m] for some [m <= M], and [G ^ m] is at least [G ^ M] because
    [G <= 1] — and it is enough because BOTH factors go to [1] as their
    parameters grow: [1 - (1 - r) ^ M] by [geo_gap_small] on [r], and
    [G ^ M] by [Qpow_one_minus_lower] once [L] is chosen after [M].
    That ordering is the only subtlety in the certificate below, and it
    is why [L] is chosen last. *)
Lemma envp_prefix_sum_lower : forall r G M,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= G)%Q -> (G <= 1)%Q ->
  (Qpow G M * (1 - Qpow (1 - r) M) <= envp_prefix_sum r G M)%Q.
Proof.
  intros r G M Hr0 Hr1 HG0 HG1.
  assert (H1r : (0 <= 1 - r)%Q) by (apply (Qle_minus_iff r 1); exact Hr1).
  assert (H1r1 : (1 - r <= 1)%Q).
  { apply (proj2 (Qle_minus_iff (1 - r) 1)).
    apply (Qle_trans _ r); [exact Hr0 | apply Qle_of_Qeq; ring]. }
  induction M as [| M IH].
  - cbn [envp_prefix_sum]. rewrite !Qpow_0. apply Qle_of_Qeq. ring.
  - cbn [envp_prefix_sum].
    assert (HX : (0 <= 1 - Qpow (1 - r) (S M))%Q).
    { apply (Qle_minus_iff (Qpow (1 - r) (S M)) 1).
      apply Qpow_le_1; assumption. }
    apply (Qle_trans _ (Qpow G M * (1 - Qpow (1 - r) (S M)))%Q).
    + apply (Qle_trans _ ((G * Qpow G M) * (1 - Qpow (1 - r) (S M)))%Q);
        [rewrite (Qpow_succ G M); apply Qle_refl |].
      apply Qmult_le_compat_r; [| exact HX].
      apply (Qle_trans _ (1 * Qpow G M)%Q); [| apply Qle_of_Qeq; ring].
      apply Qmult_le_compat_r; [exact HG1 | apply Qpow_nonneg; exact HG0].
    + apply (Qle_trans _ (r * Qpow (1 - r) M * Qpow G M
                          + Qpow G M * (1 - Qpow (1 - r) M))%Q).
      * apply Qle_of_Qeq. rewrite (Qpow_succ (1 - r) M). ring.
      * apply Qplus_le_compat; [apply Qle_refl | exact IH].
Qed.

(* =========================================================================
   The lower certificate for [stdin_envp_geometric]
   ========================================================================= *)

(** THE WITNESS FAMILY: over the fixed argv and file system, one record
    per (environment, standard input) pair drawn from the two prefix
    families.  It is a product, exactly as the bounds' enumeration is,
    and it is duplicate-free because both coordinates are
    ([NoDup_envp_stdin_product]).

    As everywhere in this file, these records are NOT claimed valid and
    NOT claimed rejected by anything; the certificate is arithmetic
    about the declared mass. *)
Definition envp_geo_lower_witness (argv : list (list byte)) (fs : Fs.Fs)
    (M L k : nat) : list FinProcInput :=
  List.map core_input
    (envp_stdin_product argv fs (envps_upto L M) (short_inputs k)).

Lemma map_fin_core_envp_geo_lower_witness : forall argv fs M L k,
  List.map fin_core (envp_geo_lower_witness argv fs M L k)
    = envp_stdin_product argv fs (envps_upto L M) (short_inputs k).
Proof.
  intros argv fs M L k. unfold envp_geo_lower_witness.
  apply map_fin_core_core_input.
Qed.

Lemma envp_geo_lower_witness_nodup : forall argv fs M L k,
  List.NoDup (List.map fin_core (envp_geo_lower_witness argv fs M L k)).
Proof.
  intros argv fs M L k. rewrite map_fin_core_envp_geo_lower_witness.
  apply NoDup_envp_stdin_product;
    [apply envps_upto_nodup | apply short_inputs_nodup].
Qed.

(** THE WITNESS, at each triple of depths: an admissible list weighing
    exactly the product of the two coordinates' partial sums.

    No hypothesis beyond the constructor's own is needed HERE, for the
    reason [stdin_geometric_mass_lower_witness] needs none: the equality
    is unconditional arithmetic.  All three strictnesses enter one lemma
    later, where the three depths have to be CHOSEN to meet a target. *)
Lemma stdin_envp_geometric_mass_lower_witness :
  forall p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k,
  List.NoDup (List.map fin_core (envp_geo_lower_witness argv fs M L k))
  /\ (core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                             Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))
        (envp_geo_lower_witness argv fs M L k)
        == envp_prefix_sum r (1 - Qpow (1 - q) L) M
           * (1 - Qpow (1 - p) k))%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k.
  split; [apply envp_geo_lower_witness_nodup |].
  cbn [cd_weight stdin_envp_geometric].
  rewrite core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness.
  rewrite qsum_envp_stdin_product.
  rewrite qsum_envp_point_envps_upto, short_inputs_sum, geo_prefix_sum_closed.
  reflexivity.
Qed.

(** THE MARGIN ARITHMETIC OF THE CERTIFICATE, WITH THE DEPTHS STILL
    FREE.  Given three depths whose three tails together come in under
    [eps], the witness's partial sum is within [eps] of [1].  Nothing
    about a distribution appears — it is a statement about
    [envp_prefix_sum] and two powers — and that is why it is stated
    apart: the certificate below and the mixture certificate further
    down consume it at DIFFERENT depths, and only the choice of depths
    differs between them.

    Three approximations meet here and each is charged separately.  The
    entry-count tail is [(1 - r) ^ M]; the standard-input tail is
    [(1 - p_stop) ^ k]; and the entry-length shortfall is [M] slots each
    missing [(1 - q_e) ^ L], which is where the [Qnat M] factor comes
    from ([Qpow_one_minus_lower] turns a per-slot miss into a
    per-environment one).  [Qmargins_three] composes the three, and
    [envp_prefix_sum_lower] is what puts the entry-count partial sum
    under the product.

    NO STRICT HYPOTHESIS APPEARS, and that is the point of the split:
    strictness is spent choosing depths, never in the arithmetic that
    uses them. *)
Lemma envp_stdin_margin_at_depths : forall p r q eps M L k,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= r)%Q -> (r <= 1)%Q ->
  (0 <= q)%Q -> (q <= 1)%Q ->
  (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M + Qpow (1 - p) k <= eps)%Q ->
  (1 - eps <= envp_prefix_sum r (1 - Qpow (1 - q) L) M
                * (1 - Qpow (1 - p) k))%Q.
Proof.
  intros p r q eps M L k Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hsum.
  assert (Hx0 : (0 <= Qpow (1 - q) L)%Q)
    by (apply Qpow_nonneg; apply (Qle_minus_iff q 1); exact Hq1).
  assert (H1q1 : (1 - q <= 1)%Q).
  { apply (proj2 (Qle_minus_iff (1 - q) 1)).
    apply (Qle_trans _ q); [exact Hq0 | apply Qle_of_Qeq; ring]. }
  assert (Hx1 : (Qpow (1 - q) L <= 1)%Q)
    by (apply Qpow_le_1;
        [apply (Qle_minus_iff q 1); exact Hq1 | exact H1q1]).
  assert (Hb0 : (0 <= Qpow (1 - r) M)%Q)
    by (apply Qpow_nonneg; apply (Qle_minus_iff r 1); exact Hr1).
  assert (H1r1 : (1 - r <= 1)%Q).
  { apply (proj2 (Qle_minus_iff (1 - r) 1)).
    apply (Qle_trans _ r); [exact Hr0 | apply Qle_of_Qeq; ring]. }
  assert (Hb1 : (Qpow (1 - r) M <= 1)%Q)
    by (apply Qpow_le_1;
        [apply (Qle_minus_iff r 1); exact Hr1 | exact H1r1]).
  assert (Hc0 : (0 <= Qpow (1 - p) k)%Q)
    by (apply Qpow_nonneg; apply (Qle_minus_iff p 1); exact Hp1).
  assert (H1p1 : (1 - p <= 1)%Q).
  { apply (proj2 (Qle_minus_iff (1 - p) 1)).
    apply (Qle_trans _ p); [exact Hp0 | apply Qle_of_Qeq; ring]. }
  assert (Hc1 : (Qpow (1 - p) k <= 1)%Q)
    by (apply Qpow_le_1;
        [apply (Qle_minus_iff p 1); exact Hp1 | exact H1p1]).
  assert (Ha0 : (0 <= Qnat M * Qpow (1 - q) L)%Q)
    by (apply Qmult_le_0_compat; [apply Qnat_nonneg | exact Hx0]).
  assert (HG0 : (0 <= 1 - Qpow (1 - q) L)%Q)
    by (apply (Qle_minus_iff (Qpow (1 - q) L) 1); exact Hx1).
  assert (HG1 : (1 - Qpow (1 - q) L <= 1)%Q).
  { apply (proj2 (Qle_minus_iff (1 - Qpow (1 - q) L) 1)).
    apply (Qle_trans _ (Qpow (1 - q) L));
      [exact Hx0 | apply Qle_of_Qeq; ring]. }
  apply (Qle_trans _ (1 - (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M
                           + Qpow (1 - p) k))%Q).
  - apply (proj2 (Qle_minus_iff (1 - eps)
                    (1 - (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M
                          + Qpow (1 - p) k)))).
    apply (Qle_trans _ (eps + - (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M
                                 + Qpow (1 - p) k))%Q);
      [ apply (proj1 (Qle_minus_iff (Qnat M * Qpow (1 - q) L
                                     + Qpow (1 - r) M + Qpow (1 - p) k) eps));
        exact Hsum
      | apply Qle_of_Qeq; ring].
  - apply (Qle_trans _ ((1 - Qnat M * Qpow (1 - q) L)
                        * (1 - Qpow (1 - r) M)
                        * (1 - Qpow (1 - p) k))%Q);
      [apply Qmargins_three; assumption |].
    apply Qmult_le_compat_r.
    + apply (Qle_trans _ (Qpow (1 - Qpow (1 - q) L) M
                          * (1 - Qpow (1 - r) M))%Q).
      * apply Qmult_le_compat_r.
        -- apply Qpow_one_minus_lower; assumption.
        -- apply (Qle_minus_iff (Qpow (1 - r) M) 1); exact Hb1.
      * apply envp_prefix_sum_lower; assumption.
    + apply (Qle_minus_iff (Qpow (1 - p) k) 1); exact Hc1.
Qed.

(** ... AND THE DEPTHS THAT MEET IT, above any floors asked for.

    Each strictness buys exactly one depth, and the three are chosen in
    an order that matters.  [geo_gap_small_above] on [r] gives an entry
    count [M] past which the environments are too long to matter;
    [geo_gap_small] on [p_stop] gives a standard-input length [k]; and
    then — LAST, because the bound it has to meet mentions [M] — on
    [q_e] it gives an entry length [L] with [(1 - q_e) ^ L] under
    [eps / (3 * (M + 1))], so that all [M] entry slots together miss at
    most a third of the margin.  The three thirds are what
    [envp_stdin_margin_at_depths] then composes.

    [M0] AND [L0] ARE THE FLOORS, and they are the reason this is not
    inlined into the certificate.  A certificate serving one family
    takes them both [0] and the choice is the margin's alone; a mixture
    also has to reach a fixed environment, and passes that environment's
    entry count and longest entry.  Only the two environment depths are
    floored: nothing outside this family ever asks for a deeper standard
    input than the margin does.

    [Qpow (1 - p_stop) k <= eps] is reported separately from the sum
    even though it follows from it, because the mixture's OTHER
    component is bounded by that tail alone and would otherwise have to
    re-derive it from the nonnegativity of the two environment terms. *)
Lemma envp_stdin_depths_above : forall p r q eps M0 L0,
  (0 < p)%Q -> (p <= 1)%Q -> (0 < r)%Q -> (r <= 1)%Q ->
  (0 < q)%Q -> (q <= 1)%Q -> (0 < eps)%Q ->
  exists M L k : nat,
    (M0 <= M)%nat /\ (L0 <= L)%nat
    /\ (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M
          + Qpow (1 - p) k <= eps)%Q
    /\ (Qpow (1 - p) k <= eps)%Q.
Proof.
  intros p r q eps M0 L0 Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps.
  assert (Heps3 : (0 < eps * (1 # 3))%Q)
    by (apply Qmult_lt_0_compat; [exact Heps | reflexivity]).
  assert (Hthird : (eps * (1 # 3) <= eps)%Q).
  { apply (Qle_trans _ ((1 # 3) * eps)%Q); [apply Qle_of_Qeq; ring |].
    apply (Qle_trans _ (1 * eps)%Q); [| apply Qle_of_Qeq; ring].
    apply Qmult_le_compat_r;
      [apply Qlt_le_weak; reflexivity | apply Qlt_le_weak; exact Heps]. }
  destruct (geo_gap_small_above r (eps * (1 # 3)) M0 Hrpos Hr1 Heps3)
    as [M [HM0 HM]].
  destruct (geo_gap_small p (eps * (1 # 3)) Hppos Hp1 Heps3) as [k Hk].
  assert (HD : (0 < Qnat M + 1)%Q).
  { apply (Qlt_le_trans _ 1); [reflexivity |].
    apply (Qle_trans _ (0 + 1)%Q); [apply Qle_of_Qeq; ring |].
    apply Qplus_le_compat; [apply Qnat_nonneg | apply Qle_refl]. }
  assert (Hbnd : (0 < eps * (1 # 3) * / (Qnat M + 1))%Q)
    by (apply Qmult_lt_0_compat;
        [exact Heps3 | apply Qinv_lt_0_compat; exact HD]).
  destruct (geo_gap_small_above q (eps * (1 # 3) * / (Qnat M + 1)) L0
              Hqpos Hq1 Hbnd) as [L [HL0 HL]].
  exists M, L, k. split; [exact HM0 |]. split; [exact HL0 |].
  assert (HDne : ~ ((Qnat M + 1) == 0)%Q)
    by (apply Qnot_eq_sym, Qlt_not_eq; exact HD).
  assert (HMD : (Qnat M * / (Qnat M + 1) <= 1)%Q).
  { apply (Qle_trans _ ((Qnat M + 1) * / (Qnat M + 1))%Q).
    - apply Qmult_le_compat_r.
      + apply (Qle_trans _ (Qnat M + 0)%Q);
          [ apply Qle_of_Qeq; ring
          | apply Qplus_le_compat; [apply Qle_refl | apply Qle_0_1]].
      + apply Qinv_le_0_compat. apply Qlt_le_weak. exact HD.
    - apply Qle_of_Qeq. apply Qmult_inv_r. exact HDne. }
  assert (Ha : (Qnat M * Qpow (1 - q) L <= eps * (1 # 3))%Q).
  { apply (Qle_trans _ (Qpow (1 - q) L * Qnat M)%Q);
      [apply Qle_of_Qeq; ring |].
    apply (Qle_trans _ (eps * (1 # 3) * / (Qnat M + 1) * Qnat M)%Q);
      [apply Qmult_le_compat_r; [exact HL | apply Qnat_nonneg] |].
    apply (Qle_trans _ (Qnat M * / (Qnat M + 1) * (eps * (1 # 3)))%Q);
      [apply Qle_of_Qeq; ring |].
    apply (Qle_trans _ (1 * (eps * (1 # 3)))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qmult_le_compat_r;
      [exact HMD | apply Qlt_le_weak; exact Heps3]. }
  split.
  - apply (Qle_trans _ (eps * (1 # 3) + eps * (1 # 3) + eps * (1 # 3))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qplus_le_compat; [apply Qplus_le_compat |]; assumption.
  - apply (Qle_trans _ (eps * (1 # 3))%Q); [exact Hk | exact Hthird].
Qed.

(** THE LOWER CERTIFICATE: for every margin [eps] there is an admissible
    list weighing at least the declared mass minus that margin.  With
    [stdin_envp_geometric_mass_upper] above it, the declared [1] is the
    least upper bound of the admissible partial sums — approached but,
    by [stdin_envp_geometric_mass_not_attained], never met.

    ALL THREE STRICT INEQUALITIES ARE HYPOTHESES OF THIS LEMMA AND NOT
    TIGHTENINGS OF THE CONSTRUCTOR, for the reason
    [stdin_geometric_mass_lower_certificate] gives: everything above
    this lemma, the upper certificate included, holds at [p_stop = 0],
    [r = 0] and [q_e = 0], and moving the hypotheses into the
    constructor would invalidate every degenerate member a consumer had
    already built.

    Each strictness buys exactly one depth, and the order in which the
    three are chosen matters; [envp_stdin_depths_above] is where that
    happens, and it is asked for no floors here because nothing but the
    margin has a say for a single family.  What is left in this proof is
    the witness and its exact partial sum, with
    [envp_stdin_margin_at_depths] doing the arithmetic.

    Nothing here is a limit and nothing is approximated: a margin is
    asked for, three natural numbers are produced, and the finite list
    they name is exhibited. *)
Lemma stdin_envp_geometric_mass_lower_certificate :
  forall p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 eps,
  (0 < p)%Q -> (0 < r)%Q -> (0 < q)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (cd_mass (stdin_envp_geometric p r q argv fs
                   Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) - eps
          <= core_sum (cd_weight (stdin_envp_geometric p r q argv fs
                                    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l)%Q.
Proof.
  intros p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 eps Hppos Hrpos Hqpos Heps.
  destruct (envp_stdin_depths_above p r q eps 0 0
              Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps)
    as [M [L [k [_ [_ [Hsum _]]]]]].
  exists (envp_geo_lower_witness argv fs M L k).
  split; [apply envp_geo_lower_witness_nodup |].
  rewrite (proj2 (stdin_envp_geometric_mass_lower_witness
                    p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k)).
  cbn [cd_mass stdin_envp_geometric].
  apply envp_stdin_margin_at_depths; assumption.
Qed.

(* =========================================================================
   Non-vacuity: the environment really carries mass, and where each
   strictness is spent
   ========================================================================= *)

(** [geo_weight]'s envp instance, stated because the bite below needs it
    and the file has only the argv one.  It is the same
    [geo_weight_mismatch] the comment at
    [geo_weight_off_environment_zero] says envp goes through. *)
Lemma geo_weight_off_envp_zero : forall p argv envp fs c,
  core_envp c <> envp -> geo_weight p argv envp fs c = 0%Q.
Proof.
  intros p argv envp fs c Hne. apply geo_weight_mismatch.
  intros Heq. apply (f_equal core_envp) in Heq. cbn [core_envp] in Heq.
  exact (Hne Heq).
Qed.

(** Strict positivity of the two new factors, at any non-degenerate
    member of the family.  [envp_point_pos] is an induction over the
    entries and is where the family's whole point becomes arithmetic:
    an environment of ANY length weighs something, because every factor
    in the running product does. *)
Lemma geo_point_pos : forall q n,
  (0 < q)%Q -> (q < 1)%Q -> (0 < geo_point q n)%Q.
Proof.
  intros q n Hq0 Hq1. unfold geo_point. apply Qmult_lt_0_compat; [exact Hq0 |].
  unfold geo_mass. apply Qpow_pos.
  apply Qmult_lt_0_compat;
    [apply (Qlt_minus_iff q 1); exact Hq1 | reflexivity].
Qed.

Lemma envp_point_pos : forall r q es,
  (0 < r)%Q -> (r < 1)%Q -> (0 < q)%Q -> (q < 1)%Q ->
  (0 < envp_point r q es)%Q.
Proof.
  intros r q es Hr0 Hr1 Hq0 Hq1. unfold envp_point.
  apply Qmult_lt_0_compat; [exact Hr0 |].
  induction es as [| e es IH]; [reflexivity |].
  cbn [envp_factor]. apply Qmult_lt_0_compat; [| exact IH].
  apply Qmult_lt_0_compat;
    [ apply (Qlt_minus_iff r 1); exact Hr1
    | apply geo_point_pos; assumption].
Qed.

(** A core over a NON-CANONICAL launch-time environment: one entry, the
    single byte [A].  As at [geo_example_core] it is not claimed valid;
    it is a point of [FinInput.FinCore] chosen so that the two families
    disagree at it. *)
Definition envp_example_named : FinCore := mkFinCore [] [[Z_to_bv 8 65]] [] [].

(** THE BITE THE FAMILY EXISTS FOR, both halves on ONE core.
    [stdin_geometric] over the empty environment weighs
    [envp_example_named] exactly zero — its envp is not the fixed one —
    while [stdin_envp_geometric] weighs it strictly positively.

    That is the gap restated as a theorem.  Under a
    distribution built from [stdin_geometric] alone, a fire set living
    at cores like this one lies in a NULL set, so both classifier
    fire-set bounds are satisfied by it vacuously and say nothing about
    whatever defect put it there.  Under this family they do not: the
    core carries weight, so a [Measure.weight_bound_T] claim about a
    fire set containing it is a claim with content.

    What it does NOT say, and the misreading is the same one the header
    warns about at the geometric lower certificate: that any particular
    task's bound is thereby sharper.  Weight on a core is what makes a
    bound about that core non-vacuous; it is not itself a bound. *)
Lemma stdin_envp_geometric_envp_bites :
  forall p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  (0 < p)%Q -> (p < 1)%Q -> (0 < r)%Q -> (r < 1)%Q ->
  (0 < q)%Q -> (q < 1)%Q ->
  cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) envp_example_named = 0%Q
  /\ (0 < cd_weight (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
            envp_example_named)%Q.
Proof.
  intros p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hppos Hplt Hrpos Hrlt Hqpos Hqlt.
  split.
  - cbn [cd_weight stdin_geometric]. apply geo_weight_off_envp_zero.
    unfold envp_example_named. cbn [core_envp]. discriminate.
  - cbn [cd_weight stdin_envp_geometric]. unfold envp_example_named.
    rewrite envp_geo_weight_match.
    apply Qmult_lt_0_compat;
      [apply envp_point_pos; assumption | apply geo_point_pos; assumption].
Qed.

(** ... and the family is still not constant: a core whose argv misses
    the fixed one weighs exactly zero, exactly as under
    [stdin_geometric].  Both halves are needed for the same reason
    [stdin_geometric_bites] needs both — without this one, "weight zero
    off the fixed argv and file system" would be a claim only the
    definition makes. *)
Lemma envp_geo_weight_off_argv_zero : forall p r q argv fs c,
  core_argv c <> argv -> envp_geo_weight p r q argv fs c = 0%Q.
Proof.
  intros p r q argv fs c Hne. apply envp_geo_weight_mismatch.
  intros Heq. apply (f_equal core_argv) in Heq. cbn [core_argv] in Heq.
  exact (Hne Heq).
Qed.

Lemma stdin_envp_geometric_bites : forall p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  (0 < p)%Q -> (p < 1)%Q -> (0 < r)%Q -> (r < 1)%Q ->
  (0 < q)%Q -> (q < 1)%Q ->
  (0 < cd_weight (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
         geo_example_core)%Q
  /\ cd_weight (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
       geo_example_other = 0%Q.
Proof.
  intros p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hppos Hplt Hrpos Hrlt Hqpos Hqlt.
  cbn [cd_weight stdin_envp_geometric]. split.
  - unfold geo_example_core. rewrite envp_geo_weight_match.
    apply Qmult_lt_0_compat;
      [apply envp_point_pos; assumption | apply geo_point_pos; assumption].
  - apply envp_geo_weight_off_argv_zero.
    unfold geo_example_other. cbn [core_argv]. discriminate.
Qed.

(* =========================================================================
   Non-vacuity: [List.NoDup] is load-bearing here too
   ========================================================================= *)

(** The member of the family at [p_stop = r = q_e = 1]: stop
    immediately on every axis.  It is the point mass on the core with no
    environment and no standard input, it is admitted by the constructor
    — [Qle_0_1] and [Qle_refl 1] three times over — and it is what makes
    the refutation below closed arithmetic instead of open terms.  It is
    also the [r = 1] collapse at a concrete instance: by
    [envp_geo_weight_collapses_at_one_r] it weighs exactly as
    [geo_point_cd] does. *)
Definition envp_point_cd : CoreDistribution :=
  stdin_envp_geometric 1 1 1 [] []
    Qle_0_1 (Qle_refl 1) Qle_0_1 (Qle_refl 1) Qle_0_1 (Qle_refl 1).

(** THE [List.NoDup] HYPOTHESIS IS LOAD-BEARING for this family's
    cylinder bound, and this is [stdin_geometric_bound_needs_nodup]
    transposed: offer the same core twice — two records, so the list is
    duplicate-free as a list of RECORDS, and both records lie in the
    cylinder over the empty environment prefix and the empty
    standard-input prefix — and the sum is [2] against a cylinder mass
    of [1].

    All three conjuncts are needed, for the reasons the baseline lemma
    gives: the second says the list really does satisfy the cylinder
    hypothesis, so it is not excluded by that; the third says the bound
    genuinely fails on it; the first names what does exclude it. *)
Lemma stdin_envp_geometric_bound_needs_nodup :
  ~ List.NoDup (List.map fin_core [geo_empty_input; geo_empty_input])
  /\ (forall f, List.In f [geo_empty_input; geo_empty_input] ->
        in_envp_stdin_cylinder [] [] [] [] (fin_core f))
  /\ ~ (core_sum (cd_weight envp_point_cd)
          [geo_empty_input; geo_empty_input]
          <= stdin_envp_geometric_cylinder_mass 1 1 1 [] [])%Q.
Proof.
  split; [| split].
  - intros Hnd. cbn [List.map] in Hnd.
    apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd as [Hnin _].
    apply Hnin. left. reflexivity.
  - intros f Hf. destruct Hf as [Hf | [Hf | []]]; subst f;
      exists [], []; reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate Hle.
Qed.

(** THE FIVE DEGENERATE MEMBERS, and each one says which side condition
    is doing work where.

    At [p_stop = 0] and at [r = 0] the weight vanishes identically —
    every list weighs nothing while the declared mass stays [1], so the
    lower certificate is false there and its hypotheses are not
    inherited caution.  At [q_e = 0], at [r = 1] and at [q_e = 1] the
    weight does NOT vanish, and those three are the interesting ones:
    a whole class of non-empty environments weighs zero, so the family
    collapses back towards [stdin_geometric] and is as blind to the
    launch-time environment as [stdin_geometric] is.
    Those are the failure modes worth pinning, because they are the ones
    that would go unnoticed: the distribution is still non-zero, still
    sums correctly, and still measures nothing about the environment.

    The [q_e = 1] pin is at the
    end of this section; the class of environments it kills is described
    by a non-empty ENTRY rather than by a non-empty environment, and the
    comment there says why that distinction is load-bearing. *)
Lemma envp_geo_weight_zero_at_zero_p : forall r q argv fs c,
  (envp_geo_weight 0 r q argv fs c == 0)%Q.
Proof.
  intros r q argv fs c. unfold envp_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  unfold geo_point. ring.
Qed.

Lemma envp_geo_weight_zero_at_zero_r : forall p q argv fs c,
  (envp_geo_weight p 0 q argv fs c == 0)%Q.
Proof.
  intros p q argv fs c. unfold envp_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  unfold envp_point. ring.
Qed.

Lemma envp_geo_weight_zero_at_zero_q : forall p r argv fs c,
  core_envp c <> [] -> (envp_geo_weight p r 0 argv fs c == 0)%Q.
Proof.
  intros p r argv fs c Hne. unfold envp_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  destruct (core_envp c) as [| e es];
    [exfalso; exact (Hne eq_refl) |].
  unfold envp_point. cbn [envp_factor]. unfold geo_point. ring.
Qed.

(** [r = 1] IS ADMITTED BY THE CONSTRUCTOR — [Qle_0_1] and
    [Qle_refl 1] are its two side conditions, exactly as at
    [geo_point_cd] — and at it the running product's [1 - r] factor is
    zero, so every core with a non-empty environment weighs nothing.

    The collapse is total rather than partial, and stating it that way
    is sharper than stating the blindness: at [r = 1] this family IS
    [stdin_geometric] over the EMPTY launch-time environment, weight for
    weight and at every core, including the ones both weigh zero.  Two
    of the four cases below are the interesting ones — a core matching
    argv and the file system whose environment is empty is weighed the
    full standard-input weight by both, and one whose environment is not
    empty is weighed zero by both, the new family because its product
    has a zero factor and the old one because the environment misses the
    fixed value.

    [r < 1] is therefore genuinely asked for, by [envp_point_pos] and
    through it by [stdin_envp_geometric_envp_bites] and
    [calibrated_mixture_envp_bites], and this is where it is pinned. *)
Lemma envp_geo_weight_collapses_at_one_r : forall p q argv fs c,
  (envp_geo_weight p 1 q argv fs c == geo_weight p argv [] fs c)%Q.
Proof.
  intros p q argv fs c. unfold envp_geo_weight, geo_weight.
  destruct (decide (c = mkFinCore argv (core_envp c) fs (core_stdin c)))
    as [Hm | Hnm];
    destruct (decide (c = mkFinCore argv [] fs (core_stdin c)))
      as [He | Hne].
  - assert (Henv : core_envp c = [])
      by (apply (f_equal core_envp) in He; cbn [core_envp] in He; exact He).
    rewrite Henv. unfold envp_point. cbn [envp_factor]. ring.
  - destruct (core_envp c) as [| e es];
      [exfalso; exact (Hne Hm) |].
    unfold envp_point. cbn [envp_factor]. ring.
  - exfalso. apply Hnm.
    assert (Henv : core_envp c = [])
      by (apply (f_equal core_envp) in He; cbn [core_envp] in He; exact He).
    rewrite Henv. exact He.
  - reflexivity.
Qed.

Lemma stdin_envp_geometric_collapses_at_one_r :
  forall p q argv fs Hp0 Hp1 Hq0 Hq1 c,
  (cd_weight (stdin_envp_geometric p 1 q argv fs Hp0 Hp1
                Qle_0_1 (Qle_refl 1) Hq0 Hq1) c
     == cd_weight (stdin_geometric p argv [] fs Hp0 Hp1) c)%Q.
Proof.
  intros p q argv fs Hp0 Hp1 Hq0 Hq1 c.
  cbn [cd_weight stdin_envp_geometric stdin_geometric].
  apply envp_geo_weight_collapses_at_one_r.
Qed.

(** ... and so the blindness, in the shape
    [stdin_envp_geometric_envp_needs_positive_q] states it for the other
    non-vanishing degeneracy.  Both are exported: a reader asking "what
    goes wrong at this parameter" wants the blindness, and a reader
    asking "what does the family become" wants the collapse. *)
Lemma stdin_envp_geometric_envp_needs_r_below_one :
  forall p q argv fs Hp0 Hp1 Hq0 Hq1 c,
  core_envp c <> [] ->
  (cd_weight (stdin_envp_geometric p 1 q argv fs Hp0 Hp1
                Qle_0_1 (Qle_refl 1) Hq0 Hq1) c == 0)%Q.
Proof.
  intros p q argv fs Hp0 Hp1 Hq0 Hq1 c Hne.
  rewrite stdin_envp_geometric_collapses_at_one_r.
  cbn [cd_weight stdin_geometric].
  rewrite (geo_weight_off_envp_zero p argv [] fs c Hne). reflexivity.
Qed.

Lemma stdin_envp_geometric_mass_lower_needs_positive :
  forall argv fs r q Hr0 Hr1 Hq0 Hq1,
  (forall l : list FinProcInput,
     (core_sum (cd_weight (stdin_envp_geometric 0 r q argv fs
                             (Qle_refl 0) Qle_0_1 Hr0 Hr1 Hq0 Hq1)) l == 0)%Q)
  /\ ~ (cd_mass (stdin_envp_geometric 0 r q argv fs
                   (Qle_refl 0) Qle_0_1 Hr0 Hr1 Hq0 Hq1) - (1 # 2) <= 0)%Q.
Proof.
  intros argv fs r q Hr0 Hr1 Hq0 Hq1. split.
  - intros l. apply core_sum_zero_weight. intros c.
    cbn [cd_weight stdin_envp_geometric]. apply envp_geo_weight_zero_at_zero_p.
  - cbn [cd_mass stdin_envp_geometric]. intros Hle.
    apply (proj2 (Qle_bool_iff _ _)) in Hle. vm_compute in Hle.
    discriminate Hle.
Qed.

Lemma stdin_envp_geometric_envp_needs_positive_q :
  forall p r argv fs Hp0 Hp1 Hr0 Hr1 c,
  core_envp c <> [] ->
  (cd_weight (stdin_envp_geometric p r 0 argv fs Hp0 Hp1 Hr0 Hr1
                (Qle_refl 0) Qle_0_1) c == 0)%Q.
Proof.
  intros p r argv fs Hp0 Hp1 Hr0 Hr1 c Hne.
  cbn [cd_weight stdin_envp_geometric].
  apply envp_geo_weight_zero_at_zero_q. exact Hne.
Qed.

(** THE FIFTH DEGENERATE MEMBER, [q_e = 1], and it went unpinned when the
    other four were.  The constructor asks [0 <= q_e <= 1], so it is
    buildable, and at it [geo_point 1 m] is zero for every [m >= 1]: an
    environment holding ANY non-empty entry weighs nothing, while
    environments made only of empty entries keep their weight.

    That is the [q_e = 0] failure mode one axis over and it is worse in
    practice, because a real environment entry is a [NAME=value] string:
    the family is blind to every environment a program will actually see
    and has NOT gone quiet — still non-zero, still summing correctly,
    still declaring mass [1] honestly.  And [q_e < 1] IS asked for, by
    [envp_point_pos] and through it by
    [stdin_envp_geometric_envp_bites] and [calibrated_mixture_envp_bites],
    which is the file's own criterion for pinning an endpoint.

    THE HYPOTHESIS NAMES A NON-EMPTY ENTRY, NOT A NON-EMPTY ENVIRONMENT,
    and the difference is not pedantry: the environment [[[]]] — one
    entry, empty — weighs a positive amount at [q_e = 1], so this is not
    [stdin_envp_geometric_envp_needs_positive_q] with [0] replaced by
    [1].  Membership rather than "the first entry" because a real
    environment's blind entry need not be first, and the induction below
    costs nothing extra for the stronger form. *)
Lemma envp_factor_zero_at_one_q : forall r es e,
  List.In e es -> e <> [] -> (envp_factor r 1 es == 0)%Q.
Proof.
  intros r es. induction es as [| e0 es IH]; intros e Hin Hne; [destruct Hin |].
  cbn [envp_factor]. destruct Hin as [Heq | Hin].
  - subst e0. destruct e as [| b e']; [exfalso; exact (Hne eq_refl) |].
    unfold geo_point, geo_mass. cbn [length Qpow]. ring.
  - rewrite (IH e Hin Hne). ring.
Qed.

Lemma envp_geo_weight_zero_at_one_q : forall p r argv fs c e,
  List.In e (core_envp c) -> e <> [] ->
  (envp_geo_weight p r 1 argv fs c == 0)%Q.
Proof.
  intros p r argv fs c e Hin Hne. unfold envp_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  unfold envp_point.
  rewrite (envp_factor_zero_at_one_q r (core_envp c) e Hin Hne). ring.
Qed.

Lemma stdin_envp_geometric_envp_needs_q_below_one :
  forall p r argv fs Hp0 Hp1 Hr0 Hr1 c e,
  List.In e (core_envp c) -> e <> [] ->
  (cd_weight (stdin_envp_geometric p r 1 argv fs Hp0 Hp1 Hr0 Hr1
                Qle_0_1 (Qle_refl 1)) c == 0)%Q.
Proof.
  intros p r argv fs Hp0 Hp1 Hr0 Hr1 c e Hin Hne.
  cbn [cd_weight stdin_envp_geometric].
  exact (envp_geo_weight_zero_at_one_q p r argv fs c e Hin Hne).
Qed.

(** ... AND THE HYPOTHESIS CANNOT BE WEAKENED to "the environment is
    non-empty", which is what makes the shape above a decision rather
    than an accident of how the induction went.  At [q_e = 1] the
    environment with ONE EMPTY ENTRY weighs [2 # 25] — positive — while
    the one-entry-of-one-byte environment weighs zero.  Closed [Q]
    relations between literals this file wrote out, per the header's
    exception. *)
Lemma envp_geo_weight_at_one_q_needs_a_non_empty_entry :
  (envp_geo_weight (1 # 2) (1 # 5) 1 [] []
     (mkFinCore [] [[Z_to_bv 8 65]] [] []) == 0)%Q
  /\ (0 < envp_geo_weight (1 # 2) (1 # 5) 1 [] []
            (mkFinCore [] [[]] [] []))%Q.
Proof.
  split.
  - apply (envp_geo_weight_zero_at_one_q _ _ _ _ _ [Z_to_bv 8 65]);
      [cbn [core_envp]; left; reflexivity | intros H; discriminate H].
  - rewrite envp_geo_weight_match. vm_compute. reflexivity.
Qed.

(* =========================================================================
   THE CALIBRATED MIXTURE: most of the mass on standard input alone, a
   sixteenth on the environment
   ========================================================================= *)

(** The composition this family was requested for, written out at the
    constants a task configuration intends to ship.  NO NEW COMBINATOR
    IS INVOLVED, and that is the point of writing it: [cd_scale] twice
    and [cd_mix2] once is the probabilist's mixture
    [(1 - lambda) * w1 + lambda * w2], with mass additivity built in, so
    the second base family was the only thing missing.

    [lambda = 1 # 16] on the envp-varying component, [r = 1 # 5] (a mean
    of four entries) and [q_e = 1 # 33] (a mean entry length of
    thirty-two, the shape of a [NAME=value] string).  The stop weight
    [p_stop] stays a parameter, because a task configuration picks it
    per binary by format class and nothing here depends on the choice.

    So do argv, envp and the file system.  The stdin-only component is
    the one that FIXES an environment — that is what makes it
    stdin-only — and which environment it fixes is the task's canonical
    one, not necessarily the empty one, so it is passed in rather than
    written as [[]].  The envp-varying component takes the same argv and
    file system and no envp at all, which is the whole difference
    between them.

    The two shares are written as two independent numerals rather than
    one and its complement, so that nothing here silently normalizes:
    that they sum to [1] is a claim, and
    [calibrated_mixture_mass_is_one] is where it is checked.  Change one
    without the other and that lemma stops holding.

    [r] and [q_e] are on a different footing from the shares, and the
    section headed "The environment coordinate's two constants" below
    says so with lemmas rather than in prose: every guarantee this
    mixture offers holds at any pair in the open interval [(0, 1)]
    ([calibrated_mixture_at_mass_is_one],
    [calibrated_mixture_at_mass_upper],
    [calibrated_mixture_at_mass_lower_certificate]), and fails at each
    of that interval's four endpoints
    ([calibrated_mixture_at_endpoints_bite]).  So these two numerals are
    a calibration and not a proof obligation, where [15 # 16] is
    load-bearing and pinned as such by
    [calibrated_shares_force_stdin_needs_the_threshold]. *)
Definition calibrated_lambda : Q := (1 # 16)%Q.
Definition calibrated_co_lambda : Q := (15 # 16)%Q.
Definition calibrated_r : Q := (1 # 5)%Q.
Definition calibrated_q : Q := (1 # 33)%Q.

Lemma calibrated_lambda_nonneg : (0 <= calibrated_lambda)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Lemma calibrated_co_lambda_nonneg : (0 <= calibrated_co_lambda)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Lemma calibrated_r_nonneg : (0 <= calibrated_r)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Lemma calibrated_r_le_1 : (calibrated_r <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Lemma calibrated_q_nonneg : (0 <= calibrated_q)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Lemma calibrated_q_le_1 : (calibrated_q <= 1)%Q.
Proof. apply Qlt_le_weak. reflexivity. Qed.

Definition calibrated_mixture (p : Q) (argv envp : list (list byte))
    (fs : Fs.Fs) (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q) : CoreDistribution :=
  cd_mix2
    (cd_scale calibrated_co_lambda calibrated_co_lambda_nonneg
       (stdin_geometric p argv envp fs Hp0 Hp1))
    (cd_scale calibrated_lambda calibrated_lambda_nonneg
       (stdin_envp_geometric p calibrated_r calibrated_q argv fs
          Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1
          calibrated_q_nonneg calibrated_q_le_1)).

(** Both components declare [1], so the mixture declares
    [15 # 16] of one plus [1 # 16] of the other, and that is [1].  The
    arithmetic is [ring] on four numerals — the declared masses are
    written by the two constructors and nothing is decided by
    computation. *)
Lemma calibrated_mixture_mass_is_one : forall p argv envp fs Hp0 Hp1,
  (cd_mass (calibrated_mixture p argv envp fs Hp0 Hp1) == 1)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1. unfold calibrated_mixture.
  cbn [cd_mass cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
  unfold calibrated_lambda, calibrated_co_lambda. ring.
Qed.

(** THE UPPER HALF OF THE CERTIFICATE PAIR, for the mixture and not
    merely for its components.  A declared mass ships with a finitary
    pair everywhere else in this file, and the mixture is the object a
    task would actually hand to [Measure.DISTRIBUTION], so it is the
    object the pair is owed about.

    It is a composition and nothing more: each component has its own
    whole-space upper certificate, [cd_scale_bound_mass] carries one
    through a scaling and [cd_mix2_bound_mass] adds two, and
    [calibrated_mixture_mass_is_one] turns the composed declared mass
    into the [1] a consumer wants to read.  Note that the two component
    bounds are discharged ON THE SAME LIST, which is what
    [cd_mix2_bound]'s comment says the mixture bound requires and what
    makes this four lines instead of an argument.

    THE LOWER HALF DOES NOT COMPOSE THE SAME WAY, and the asymmetry is
    worth naming because the shape of [cd_scale_mass_lower] and
    [cd_mix2_mass_lower] invites the guess that it does.  Those two ask
    for each component's mass to be ATTAINED on the shared list —
    [cd_mass D <= core_sum (cd_weight D) l] — and no geometric member
    attains its mass for [p_stop < 1]
    ([stdin_geometric_mass_not_attained],
    [stdin_envp_geometric_mass_not_attained]), so their hypotheses are
    unsatisfiable here rather than merely unproved.  A mixture lower
    certificate has to be an approach carrying its own margin —
    [cd_scale_bound_lower] and [cd_mix2_bound_lower] are the generic-[B]
    forms that carry one through a scaling and an addition — and it
    needs ONE list good for both components at once.

    Such a list does exist, and the reason is worth getting right
    because it CONSTRAINS THE DEPTHS rather than coming for free.
    [envps_upto L M] holds the environments of fewer than [M] entries
    each shorter than [L], so it contains the stdin-only component's
    FIXED environment as soon as [M] exceeds that environment's entry
    count and [L] exceeds its longest entry.  At those depths the envp
    witness carries the stdin-only component's cores too, at the
    environment that component actually fixes — which is whichever one
    a task names, the empty one having no privileged role here since
    [calibrated_mixture] takes it as a parameter.

    Two pieces are what that route needs and neither is a formality.
    The containment is the CONVERSE of [envps_upto_In_length] and
    [envps_len_In_entry], and it is [envps_upto_complete].  And
    [stdin_envp_geometric_mass_lower_certificate] chooses [M] and [L]
    from the margin arithmetic alone, while a mixture has to take them
    at least as large as both that and the fixed environment ask for —
    [geo_gap_small_above] is what delivers a depth meeting both, on the
    strength of a tail only shrinking as its exponent grows
    ([Qpow_le_exp]).  So it is a proof and not a composition, and it is
    done in the section below, generically in the two shares
    ([stdin_envp_mix2_mass_lower_certificate]) and then at this
    mixture's own constants
    ([calibrated_mixture_mass_lower_certificate]). *)
Lemma calibrated_mixture_mass_upper : forall p argv envp fs Hp0 Hp1 l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1)) l
     <= 1)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 l Hnd.
  rewrite <- (calibrated_mixture_mass_is_one p argv envp fs Hp0 Hp1).
  unfold calibrated_mixture.
  apply cd_mix2_bound_mass; apply cd_scale_bound_mass.
  - apply stdin_geometric_mass_upper. exact Hnd.
  - apply stdin_envp_geometric_mass_upper. exact Hnd.
Qed.

(* =========================================================================
   THE LOWER HALF: one list both components can be certified on
   ========================================================================= *)

(** THE SHARED WITNESS, read from the ENVP-VARYING component's side.

    [envp_geo_lower_witness] enumerates (environment, standard input)
    pairs over that component's two prefix families, and the stdin-only
    component can weigh a core of that list only where the core's
    environment is the one it FIXES — every other environment it weighs
    zero.  So the list contains the stdin-only component's own witness
    family, [geo_lower_witness]'s cores at the same standard-input depth
    [k], as a sublist — PROVIDED the fixed environment is in
    [envps_upto L M], which is what the two depth hypotheses say and
    what [envps_upto_complete] then delivers.

    An inequality and not an equality, deliberately: the sum over the
    whole list is what the mixture needs, the sum over the sublist is
    what is exactly known ([qsum_short_inputs]), and
    [qsum_core_incl_le] is the step between them.  That step asks
    for a nonnegative weight and a duplicate-free SMALL list, both
    already proved ([geo_weight_nonneg], [geo_lower_witness_nodup]), and
    asks nothing at all of the containing list — so no duplicate-freedom
    of the product is used here, even though the certificate below
    proves one for the unrelated reason that its own conclusion demands
    it.

    The two depth hypotheses are not decoration:
    [stdin_geometric_on_envp_geo_lower_witness_needs_the_depths] shows
    that at depths short of either, the list carries NONE of this
    component's weight. *)
Lemma stdin_geometric_on_envp_geo_lower_witness :
  forall p argv envp fs Hp0 Hp1 M L k,
  (length envp < M)%nat ->
  (forall e, List.In e envp -> (length e < L)%nat) ->
  (1 - Qpow (1 - p) k
     <= core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
          (envp_geo_lower_witness argv fs M L k))%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 M L k HM HL.
  rewrite core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness.
  cbn [cd_weight stdin_geometric].
  apply (Qle_trans _ (qsum (geo_weight p argv envp fs)
                        (List.map (mkFinCore argv envp fs) (short_inputs k)))).
  - rewrite qsum_short_inputs.
    apply Qle_of_Qeq. symmetry. apply geo_prefix_sum_closed.
  - apply qsum_core_incl_le.
    + apply geo_weight_nonneg; assumption.
    + rewrite <- map_fin_core_geo_lower_witness.
      apply geo_lower_witness_nodup.
    + intros c Hc. apply List.in_map_iff in Hc as [s [Hs Hin]].
      rewrite <- Hs. apply In_envp_stdin_product; [| exact Hin].
      apply envps_upto_complete; assumption.
Qed.

(** THE MIXTURE'S LOWER CERTIFICATE, at any two nonnegative shares.

    Stated of [cd_mix2] of two [cd_scale]s rather than of
    [calibrated_mixture], because nothing in the argument turns on the
    calibration constants: the shares [a] and [b] are arbitrary and are
    NOT required to sum to [1], so the lemma says something true of an
    unnormalized pair as well.  What the argument does turn on is that
    the two components are these two families over the same argv and
    file system, with the stdin-only one fixing an environment the other
    varies.

    THE MARGIN IS SPLIT BY THE SHARES: each component is certified to
    [eps / (a + b + 1)], and [a + b] of that is at most [eps] whatever
    the shares are.  The [+ 1] is there only to make the division
    unconditional — at [a = b = 0] there is nothing to divide by
    otherwise — and costs nothing, since a certificate to a smaller
    margin is a certificate.

    THE DEPTHS ARE CHOSEN ONCE, by [envp_stdin_depths_above], with the
    floors the fixed environment asks for: one past its entry count, one
    past its longest entry.  That single choice is the only place the
    two components interact.  After it,
    [stdin_envp_geometric_mass_lower_witness] evaluates the
    envp-varying component on the list exactly and
    [envp_stdin_margin_at_depths] puts that within the margin;
    [stdin_geometric_on_envp_geo_lower_witness] certifies the stdin-only
    component on the SAME list from its standard-input tail alone; and
    [cd_scale_bound_lower] with [cd_mix2_bound_lower] scale and add the
    two.

    [envp] is a parameter throughout and the empty environment has no
    privileged role: a task naming a long canonical environment simply
    gets deeper depths, which is exactly what the floors are for. *)
Lemma stdin_envp_mix2_mass_lower_certificate :
  forall p r q a b (Ha : (0 <= a)%Q) (Hb : (0 <= b)%Q)
         argv envp fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 eps,
  (0 < p)%Q -> (0 < r)%Q -> (0 < q)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (cd_mass (cd_mix2
                   (cd_scale a Ha (stdin_geometric p argv envp fs Hp0 Hp1))
                   (cd_scale b Hb (stdin_envp_geometric p r q argv fs
                                     Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))) - eps
          <= core_sum
               (cd_weight (cd_mix2
                   (cd_scale a Ha (stdin_geometric p argv envp fs Hp0 Hp1))
                   (cd_scale b Hb (stdin_envp_geometric p r q argv fs
                                     Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)))) l)%Q.
Proof.
  intros p r q a b Ha Hb argv envp fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 eps
         Hppos Hrpos Hqpos Heps.
  assert (HS : (0 < a + b + 1)%Q).
  { apply (Qlt_le_trans _ 1); [reflexivity |].
    apply (Qle_trans _ (0 + 0 + 1)%Q); [apply Qle_of_Qeq; ring |].
    apply Qplus_le_compat;
      [apply Qplus_le_compat; [exact Ha | exact Hb] | apply Qle_refl]. }
  set (eps' := (eps * / (a + b + 1))%Q).
  assert (Heps' : (0 < eps')%Q)
    by (apply Qmult_lt_0_compat;
        [exact Heps | apply Qinv_lt_0_compat; exact HS]).
  destruct (envp_stdin_depths_above p r q eps'
              (S (length envp))
              (S (List.list_max (List.map (fun e => length e) envp)))
              Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps')
    as [M [L [k [HM0 [HL0 [Hsum Hk]]]]]].
  assert (HLe : forall e, List.In e envp -> (length e < L)%nat).
  { intros e He.
    assert (Hmax : (length e
                    <= List.list_max
                         (List.map (fun e' => length e') envp))%nat)
      by (apply list_max_ge; apply List.in_map; exact He).
    lia. }
  exists (envp_geo_lower_witness argv fs M L k).
  split; [apply envp_geo_lower_witness_nodup |].
  assert (H1 : (1 - eps'
                  <= core_sum
                       (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
                       (envp_geo_lower_witness argv fs M L k))%Q).
  { apply (Qle_trans _ (1 - Qpow (1 - p) k)%Q).
    - apply (proj2 (Qle_minus_iff (1 - eps') (1 - Qpow (1 - p) k))).
      apply (Qle_trans _ (eps' + - Qpow (1 - p) k)%Q);
        [ apply (proj1 (Qle_minus_iff (Qpow (1 - p) k) eps')); exact Hk
        | apply Qle_of_Qeq; ring].
    - apply stdin_geometric_on_envp_geo_lower_witness; [lia | exact HLe]. }
  assert (H2 : (1 - eps'
                  <= core_sum
                       (cd_weight (stdin_envp_geometric p r q argv fs
                                     Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))
                       (envp_geo_lower_witness argv fs M L k))%Q).
  { rewrite (proj2 (stdin_envp_geometric_mass_lower_witness
                      p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k)).
    apply envp_stdin_margin_at_depths; assumption. }
  assert (HSne : ~ ((a + b + 1) == 0)%Q)
    by (apply Qnot_eq_sym, Qlt_not_eq; exact HS).
  assert (HAB : ((a + b) * / (a + b + 1) <= 1)%Q).
  { apply (Qle_trans _ ((a + b + 1) * / (a + b + 1))%Q).
    - apply Qmult_le_compat_r.
      + apply (Qle_trans _ (a + b + 0)%Q);
          [ apply Qle_of_Qeq; ring
          | apply Qplus_le_compat; [apply Qle_refl | apply Qle_0_1]].
      + apply Qinv_le_0_compat. apply Qlt_le_weak. exact HS.
    - apply Qle_of_Qeq. apply Qmult_inv_r. exact HSne. }
  assert (Hmar : ((a + b) * eps' <= eps)%Q).
  { unfold eps'.
    apply (Qle_trans _ ((a + b) * / (a + b + 1) * eps)%Q);
      [apply Qle_of_Qeq; ring |].
    apply (Qle_trans _ (1 * eps)%Q);
      [ apply Qmult_le_compat_r; [exact HAB | apply Qlt_le_weak; exact Heps]
      | apply Qle_of_Qeq; ring]. }
  apply (Qle_trans _ (a * (1 - eps') + b * (1 - eps'))%Q);
    [| apply cd_mix2_bound_lower; apply cd_scale_bound_lower; assumption].
  cbn [cd_mass cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
  apply (proj2 (Qle_minus_iff (a * 1 + b * 1 - eps)
                  (a * (1 - eps') + b * (1 - eps')))).
  apply (Qle_trans _ (eps + - ((a + b) * eps'))%Q);
    [ apply (proj1 (Qle_minus_iff ((a + b) * eps') eps)); exact Hmar
    | apply Qle_of_Qeq; ring].
Qed.

(** ... AND AT THE CALIBRATED CONSTANTS, which is the object a task
    ships.

    It is the instance and nothing more: [calibrated_mixture] IS the
    [cd_mix2] of two [cd_scale]s the lemma above quantifies over, so the
    only work is exhibiting [0 < r] and [0 < q_e] at the two numerals.
    [p_stop] stays a parameter, as everywhere else in this family.

    Stated against [1] rather than against [cd_mass] so that it pairs
    with [calibrated_mixture_mass_upper] term for term: no admissible
    list exceeds [1], and for every margin some admissible list comes
    within it.  [calibrated_mixture_mass_is_one] is what turns the
    composed [15 # 16] plus [1 # 16] into the [1] both halves quote. *)
Lemma calibrated_mixture_mass_lower_certificate :
  forall p argv envp fs Hp0 Hp1 eps,
  (0 < p)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - eps
          <= core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1))
               l)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 eps Hppos Heps.
  assert (Hrpos : (0 < calibrated_r)%Q) by reflexivity.
  assert (Hqpos : (0 < calibrated_q)%Q) by reflexivity.
  destruct (stdin_envp_mix2_mass_lower_certificate p calibrated_r calibrated_q
              calibrated_co_lambda calibrated_lambda
              calibrated_co_lambda_nonneg calibrated_lambda_nonneg
              argv envp fs Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1
              calibrated_q_nonneg calibrated_q_le_1 eps
              Hppos Hrpos Hqpos Heps) as [l [Hnd Hle]].
  exists l. split; [exact Hnd |].
  apply (Qle_trans _ (cd_mass (calibrated_mixture p argv envp fs Hp0 Hp1)
                        - eps)%Q); [| exact Hle].
  rewrite (calibrated_mixture_mass_is_one p argv envp fs Hp0 Hp1).
  apply Qle_refl.
Qed.

(* =========================================================================
   ... and where the mixture's own hypotheses are spent
   ========================================================================= *)

(** BOTH DEPTH CONSTRAINTS ARE LOAD-BEARING, and the failure is total
    rather than a degradation.  At depths that do not reach the fixed
    environment the shared list carries NONE of the stdin-only
    component's weight — every core of [envp_stdin_product] draws its
    environment from [envps_upto L M], and the component weighs every
    environment but its own zero ([geo_weight_off_envp_zero]).

    Either depth alone loses it, which is why the hypothesis is a
    disjunction: too few entry slots is [envps_upto_In_length]'s
    contrapositive, too short an entry is [envps_upto_In_entry]'s.  So
    the floors [stdin_envp_mix2_mass_lower_certificate] passes are not
    caution — a certificate that chose [M] and [L] from the margin
    arithmetic alone would have nothing whatever to say about the
    stdin-only component's share of the mixture on the list it
    exhibits.

    The second conjunct is the [1 # 2] gap the file's other degeneracy
    pins use: the declared mass is still [1], so a list weighing zero is
    not within any margin under one. *)
Lemma stdin_geometric_on_envp_geo_lower_witness_needs_the_depths :
  forall p argv envp fs Hp0 Hp1 M L k,
  ((M <= length envp)%nat
   \/ (exists e, List.In e envp /\ (L <= length e)%nat)) ->
  (core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
     (envp_geo_lower_witness argv fs M L k) == 0)%Q
  /\ ~ (cd_mass (stdin_geometric p argv envp fs Hp0 Hp1) - (1 # 2) <= 0)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 M L k Hdeep.
  assert (Hout : ~ List.In envp (envps_upto L M)).
  { intros Hin. destruct Hdeep as [Hlen | [e [He Hle]]].
    - apply envps_upto_In_length in Hin. lia.
    - assert (Hlt : (length e < L)%nat)
        by (apply (envps_upto_In_entry L M envp e Hin He)). lia. }
  split.
  - rewrite core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness.
    rewrite (qsum_ext _ (fun _ => 0%Q)).
    2:{ intros c Hc. unfold envp_stdin_product in Hc.
        apply List.in_flat_map in Hc as [es [Hes Hin]].
        apply List.in_map_iff in Hin as [s [Hs _]].
        cbn [cd_weight stdin_geometric]. rewrite <- Hs.
        rewrite (geo_weight_off_envp_zero p argv envp fs
                   (mkFinCore argv es fs s)); [reflexivity |].
        cbn [core_envp]. intros Heq. apply Hout. rewrite <- Heq. exact Hes. }
    apply qsum_zero.
  - cbn [cd_mass stdin_geometric]. intros Hle.
    apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate Hle.
Qed.

(** THE CERTIFICATE CANNOT BE MET BY THE ENVP-VARYING COMPONENT ALONE,
    which is the check that isolates what the shared witness actually
    buys.

    The lemma above says SOME admissible list weighs at least [1 - eps],
    and such a lemma is worth exactly as much as the reasons a list
    could have for satisfying it.  One reason has to be ruled out here:
    if the envp-varying component could supply the whole [1 - eps] by
    itself, the containment argument would be doing nothing and the
    certificate would be reporting on the wrong distribution.  It
    cannot.  That component carries a share of [1 # 16], and no
    admissible list collects more than its declared [1]
    ([stdin_envp_geometric_mass_upper]), so it contributes at most
    [1 # 16] however the list is chosen — and at any margin under
    [15 # 16] the rest has to come from the STDIN-ONLY component, whose
    cores are on that list only because [envps_upto_complete] put them
    there.

    The arithmetic is separated out because it is about the two SHARES
    and not about either family, and because it is where the calibration
    constants earn their keep: [15 # 16] of a nonpositive number plus
    [1 # 16] of something at most [1] cannot reach [1 - eps] for
    [eps < 15 # 16].  A mixture that put most of its mass on the envp
    side would fail this and would need a different argument. *)
Lemma calibrated_shares_force_stdin : forall S1 S2 eps,
  (S2 <= 1)%Q -> (eps < 15 # 16)%Q ->
  (1 - eps <= (15 # 16) * S1 + (1 # 16) * S2)%Q ->
  (0 < S1)%Q.
Proof.
  intros S1 S2 eps HS21 Heps Hle.
  destruct (Qlt_le_dec 0 S1) as [H | H]; [exact H | exfalso].
  assert (HA : ((15 # 16) * S1 <= 0)%Q).
  { apply (Qle_trans _ (S1 * (15 # 16))%Q); [apply Qle_of_Qeq; ring |].
    apply (Qle_trans _ (0 * (15 # 16))%Q);
      [ apply Qmult_le_compat_r; [exact H | apply Qlt_le_weak; reflexivity]
      | apply Qle_of_Qeq; ring]. }
  assert (HB : ((1 # 16) * S2 <= 1 # 16)%Q).
  { apply (Qle_trans _ (S2 * (1 # 16))%Q); [apply Qle_of_Qeq; ring |].
    apply (Qle_trans _ (1 * (1 # 16))%Q);
      [ apply Qmult_le_compat_r; [exact HS21 | apply Qlt_le_weak; reflexivity]
      | apply Qle_of_Qeq; ring]. }
  assert (HC : (1 - eps <= 1 # 16)%Q).
  { apply (Qle_trans _ ((15 # 16) * S1 + (1 # 16) * S2)%Q); [exact Hle |].
    apply (Qle_trans _ (0 + (1 # 16))%Q);
      [apply Qplus_le_compat; [exact HA | exact HB] | apply Qle_of_Qeq; ring]. }
  apply (Qlt_not_le _ _ Heps).
  apply (proj2 (Qle_minus_iff (15 # 16) eps)).
  apply (Qle_trans _ ((1 # 16) + - (1 - eps))%Q);
    [ apply (proj1 (Qle_minus_iff (1 - eps) (1 # 16))); exact HC
    | apply Qle_of_Qeq; ring].
Qed.

(** THE THRESHOLD IS LOAD-BEARING AND THERE IS NO SLACK IN IT: at [eps]
    exactly [15 # 16] the lemma above is FALSE.  Take [S1 = 0] and
    [S2 = 1] — the envp-varying component at its declared mass, the
    stdin-only one contributing nothing — and the hypothesis holds with
    EQUALITY, [1 - 15 # 16] and [1 # 16] of [1] being the same number,
    while the conclusion asks for [0 < 0].

    That the boundary falls exactly there is the arithmetic reporting
    where the envp component's own ceiling is: [1 - 15 # 16] is
    precisely the mass that component declares, so a margin at or past
    it is a margin the shares alone can no longer force the stdin-only
    side to help with.  It is the hypothesis of the three that would be
    easiest to drop by accident, which is the reason it is pinned rather
    than described. *)
Lemma calibrated_shares_force_stdin_needs_the_threshold :
  exists S1 S2 eps : Q,
    (S2 <= 1)%Q
    /\ ~ (eps < 15 # 16)%Q
    /\ (1 - eps <= (15 # 16) * S1 + (1 # 16) * S2)%Q
    /\ ~ (0 < S1)%Q.
Proof.
  exists 0%Q, 1%Q, (15 # 16)%Q.
  split; [apply Qle_refl |].
  split; [apply Qlt_irrefl |].
  split; [apply Qle_of_Qeq; ring |].
  intros H. exact (Qlt_irrefl 0 H).
Qed.

(** The mixture's sum read as the two shares of its components' sums —
    [core_sum_plus] and [core_sum_scale] applied where [cd_mix2] and
    [cd_scale] left them.  It is stated rather than inlined because the
    pin below is the only place in the file that needs the mixture taken
    APART again, everything else having been built up. *)
Lemma calibrated_mixture_sum_split : forall p argv envp fs Hp0 Hp1 l,
  (core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1)) l
     == calibrated_co_lambda
          * core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l
        + calibrated_lambda
          * core_sum (cd_weight (stdin_envp_geometric p calibrated_r
                                   calibrated_q argv fs Hp0 Hp1
                                   calibrated_r_nonneg calibrated_r_le_1
                                   calibrated_q_nonneg calibrated_q_le_1)) l)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 l.
  unfold calibrated_mixture. cbn [cd_weight cd_mix2 cd_scale].
  rewrite (core_sum_plus
             (fun c => (calibrated_co_lambda
                        * cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)
                            c)%Q)
             (fun c => (calibrated_lambda
                        * cd_weight (stdin_envp_geometric p calibrated_r
                                       calibrated_q argv fs Hp0 Hp1
                                       calibrated_r_nonneg calibrated_r_le_1
                                       calibrated_q_nonneg calibrated_q_le_1)
                            c)%Q)
             l).
  rewrite !core_sum_scale. reflexivity.
Qed.

Lemma calibrated_mixture_mass_lower_certificate_needs_the_stdin_component :
  forall p argv envp fs Hp0 Hp1 eps l,
  List.NoDup (List.map fin_core l) ->
  (eps < 15 # 16)%Q ->
  (1 - eps
     <= core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1)) l)%Q ->
  (0 < core_sum (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)) l)%Q
  /\ exists c, List.In c (List.map fin_core l)
               /\ (0 < cd_weight (stdin_geometric p argv envp fs Hp0 Hp1) c)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 eps l Hnd Heps Hle.
  rewrite calibrated_mixture_sum_split in Hle.
  unfold calibrated_co_lambda, calibrated_lambda in Hle.
  assert (Hpos : (0 < core_sum
                      (cd_weight (stdin_geometric p argv envp fs Hp0 Hp1))
                      l)%Q).
  { eapply calibrated_shares_force_stdin;
      [ apply stdin_envp_geometric_mass_upper; exact Hnd
      | exact Heps | exact Hle]. }
  split; [exact Hpos |].
  rewrite core_sum_map_fin_core in Hpos.
  apply qsum_positive_member; [apply cd_nonneg | exact Hpos].
Qed.

(** ... AND THE HYPOTHESIS OF THAT PIN IS MET, which is the half that
    keeps it from being a safe vacuity.  An implication about lists
    satisfying the certificate says nothing until some list does, and
    [calibrated_mixture_mass_lower_certificate] produces one — so the
    two compose into an unconditional existence claim, which is the
    statement worth quoting: at every [p_stop > 0] and every margin in
    [(0, 15 # 16)] there is an admissible list within the margin that
    NAMES a core the stdin-only component weighs positively.  The empty
    list does not satisfy it and neither does any list of cores the
    mixture weighs zero. *)
Lemma calibrated_mixture_mass_lower_certificate_names_a_stdin_core :
  forall p argv envp fs Hp0 Hp1 eps,
  (0 < p)%Q -> (0 < eps)%Q -> (eps < 15 # 16)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - eps
          <= core_sum (cd_weight (calibrated_mixture p argv envp fs Hp0 Hp1))
               l)%Q
    /\ exists c, List.In c (List.map fin_core l)
                 /\ (0 < cd_weight (stdin_geometric p argv envp fs Hp0 Hp1)
                          c)%Q.
Proof.
  intros p argv envp fs Hp0 Hp1 eps Hppos Heps Hsmall.
  destruct (calibrated_mixture_mass_lower_certificate p argv envp fs Hp0 Hp1
              eps Hppos Heps) as [l [Hnd Hle]].
  exists l. split; [exact Hnd |]. split; [exact Hle |].
  apply (proj2
           (calibrated_mixture_mass_lower_certificate_needs_the_stdin_component
              p argv envp fs Hp0 Hp1 eps l Hnd Hsmall Hle)).
Qed.

(** The shallowest envp witness names exactly ONE core.  [envps_upto 1 1]
    is the single environment [[]] and [short_inputs 1] the single
    standard input [[]], so their product is a one-element list — which
    is what makes the pin below a computation a reader can check by
    eye rather than an appeal to a family. *)
Lemma envp_stdin_product_at_depth_one :
  envp_stdin_product [] [] (envps_upto 1 1) (short_inputs 1)
    = [mkFinCore [] [] [] []].
Proof. reflexivity. Qed.

(** ... AND THE THRESHOLD IS LOAD-BEARING AT THE DISTRIBUTION TOO, where
    it needs a STRICTLY larger margin than the arithmetic does.  The
    difference is worth stating rather than glossing: at [eps] exactly
    [15 # 16] no admissible list realizes
    [calibrated_shares_force_stdin_needs_the_threshold]'s
    counterexample, because its [S2 = 1] is not attained — no list ever
    collects the envp-varying component's declared mass
    ([stdin_envp_geometric_mass_not_attained]).  Past the boundary a
    list does realize it, and this is one.

    The mixture here fixes the one-entry environment [[Z_to_bv 8 65]]
    for its stdin-only component, and the list is the shallowest envp
    witness — the single core [mkFinCore [] [] [] []], whose
    environment is [[]].  So the stdin-only component weighs that list
    ZERO, which is exactly the depth failure
    [stdin_geometric_on_envp_geo_lower_witness_needs_the_depths]
    describes, at [M = 1] against an environment of one entry.  What the
    mixture collects is [1 # 16] of [1 # 5] of [1 # 2], namely
    [1 # 160]; and [1 - (159 # 160)] is [1 # 160] as well, so the
    certificate's conclusion is met WITH EQUALITY by a list carrying
    none of the stdin-only component's weight.

    So the threshold in
    [calibrated_mixture_mass_lower_certificate_needs_the_stdin_component]
    cannot be relaxed to [eps < 1], and this says so with a witness
    rather than by pointing at the arithmetic. *)
Lemma calibrated_mixture_mass_lower_certificate_needs_the_threshold :
  forall (Hp0 : (0 <= 1 # 2)%Q) (Hp1 : ((1 # 2) <= 1)%Q),
  ((15 # 16) < (159 # 160))%Q /\ ((159 # 160) < 1)%Q
  /\ List.NoDup (List.map fin_core (envp_geo_lower_witness [] [] 1 1 1))
  /\ (1 - (159 # 160)
        <= core_sum
             (cd_weight (calibrated_mixture (1 # 2) []
                           [[Z_to_bv 8 65]] [] Hp0 Hp1))
             (envp_geo_lower_witness [] [] 1 1 1))%Q
  /\ (core_sum
        (cd_weight (stdin_geometric (1 # 2) [] [[Z_to_bv 8 65]] [] Hp0 Hp1))
        (envp_geo_lower_witness [] [] 1 1 1) == 0)%Q.
Proof.
  intros Hp0 Hp1.
  split; [reflexivity |]. split; [reflexivity |].
  split; [apply envp_geo_lower_witness_nodup |].
  split.
  - rewrite core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness.
    rewrite envp_stdin_product_at_depth_one, qsum_cons,
      qsum_nil.
    unfold calibrated_mixture.
    cbn [cd_weight cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
    rewrite (geo_weight_off_envp_zero (1 # 2) [] [[Z_to_bv 8 65]] []
               (mkFinCore [] [] [] []))
      by (cbn [core_envp]; intros Heq; discriminate Heq).
    rewrite envp_geo_weight_match.
    apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
  - rewrite core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness.
    rewrite envp_stdin_product_at_depth_one, qsum_cons,
      qsum_nil.
    cbn [cd_weight stdin_geometric].
    rewrite (geo_weight_off_envp_zero (1 # 2) [] [[Z_to_bv 8 65]] []
               (mkFinCore [] [] [] []))
      by (cbn [core_envp]; intros Heq; discriminate Heq).
    ring.
Qed.

(** [0 < p_stop] IS AS LOAD-BEARING FOR THE MIXTURE AS FOR EITHER
    COMPONENT, pinned the way the two base families pin it
    ([stdin_geometric_mass_lower_needs_positive],
    [stdin_envp_geometric_mass_lower_needs_positive]).  At [p_stop = 0]
    both components weigh every core zero
    ([geo_weight_zero_at_zero_p], [envp_geo_weight_zero_at_zero_p]), so
    fifteen sixteenths of one plus a sixteenth of the other is zero on
    EVERY admissible list — the first conjunct quantifies over all of
    them for that reason — while the declared mass is still [1].

    [calibrated_mixture_mass_upper] remains true here, and the asymmetry
    is the same honest content the base families' pairs report: an upper
    bound survives degeneracy, a lower one does not. *)
Lemma calibrated_mixture_mass_lower_needs_positive : forall argv envp fs,
  (forall l : list FinProcInput,
     (core_sum (cd_weight (calibrated_mixture 0 argv envp fs
                             (Qle_refl 0) Qle_0_1)) l == 0)%Q)
  /\ ~ (cd_mass (calibrated_mixture 0 argv envp fs (Qle_refl 0) Qle_0_1)
          - (1 # 2) <= 0)%Q.
Proof.
  intros argv envp fs. split.
  - intros l. apply core_sum_zero_weight. intros c.
    unfold calibrated_mixture.
    cbn [cd_weight cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
    rewrite geo_weight_zero_at_zero_p, envp_geo_weight_zero_at_zero_p. ring.
  - unfold calibrated_mixture.
    cbn [cd_mass cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
    intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate Hle.
Qed.

(** ... AND THE MIXTURE INHERITS THE BITE, which is the whole reason for
    mixing rather than replacing.  The stdin-only component still weighs
    a non-canonical environment zero; the mixture does not, because a
    sixteenth of a positive number is positive.  So a task keeps
    whatever its stdin-only argument bought and gains a fire set over
    the environment that is no longer null. *)
Lemma calibrated_mixture_envp_bites : forall p Hp0 Hp1,
  (0 < p)%Q -> (p < 1)%Q ->
  cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) envp_example_named = 0%Q
  /\ (0 < cd_weight (calibrated_mixture p [] [] [] Hp0 Hp1)
            envp_example_named)%Q.
Proof.
  intros p Hp0 Hp1 Hppos Hplt. split.
  - cbn [cd_weight stdin_geometric]. apply geo_weight_off_envp_zero.
    unfold envp_example_named. cbn [core_envp]. discriminate.
  - unfold calibrated_mixture, envp_example_named.
    cbn [cd_weight cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
    rewrite (geo_weight_off_envp_zero p [] [] []
               (mkFinCore [] [[Z_to_bv 8 65]] [] []))
      by (cbn [core_envp]; discriminate).
    rewrite envp_geo_weight_match.
    apply (Qlt_le_trans _ (calibrated_lambda
                           * (envp_point calibrated_r calibrated_q
                                [[Z_to_bv 8 65]]
                              * geo_point p (length (@nil byte))))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qmult_lt_0_compat; [reflexivity |].
    apply Qmult_lt_0_compat.
    + apply envp_point_pos; reflexivity.
    + apply geo_point_pos; assumption.
Qed.

(* =========================================================================
   The environment coordinate's two constants, pinned from both sides
   ========================================================================= *)

(** [calibrated_lambda] IS load-bearing and is pinned as such:
    [calibrated_shares_force_stdin_needs_the_threshold] exhibits shares
    and a margin at which [15 # 16] is exactly false, so the mixture's
    lower certificate does not survive an arbitrary reweighting.

    [calibrated_r] and [calibrated_q] are NOT like that, and saying so
    in place is the point of this section.  Nothing derives [1 # 5] or
    [1 # 33] and nothing needs to: they are a CALIBRATION — a mean of
    four environment entries and a mean entry length of thirty-two, the
    shape of a [NAME=value] string — and every guarantee the mixture
    offers holds at ANY pair in the open interval [(0, 1)].
    [calibrated_mixture_at] is the same composition with the pair left
    open, [calibrated_mixture_at_calibrated_r_q] is [reflexivity], and
    the three lemmas after it are the mass, the upper certificate and
    the lower certificate at an arbitrary admissible pair.

    THE INTERVAL IS NOT SLACK EITHER, and that is the other direction
    the [15 # 16] pin has and this pair was missing.  At each of its
    four endpoints a guarantee actually fails, on cores the calibrated
    instance weighs positively: [r = 0] and [r = 1] and [q_e = 0] kill
    every core with a non-empty environment, and [q_e = 1] kills every
    core with a non-empty ENTRY.  [calibrated_mixture_at_endpoints_bite]
    assembles the four, and [calibrated_mixture_envp_bites] above is the
    positive half — at the calibrated pair such a core weighs more than
    zero.  So the open interval is exactly the admissible region, not a
    convenient over-restriction. *)
Definition calibrated_mixture_at (r q : Q)
    (Hr0 : (0 <= r)%Q) (Hr1 : (r <= 1)%Q)
    (Hq0 : (0 <= q)%Q) (Hq1 : (q <= 1)%Q)
    (p : Q) (argv envp : list (list byte)) (fs : Fs.Fs)
    (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q) : CoreDistribution :=
  cd_mix2
    (cd_scale calibrated_co_lambda calibrated_co_lambda_nonneg
       (stdin_geometric p argv envp fs Hp0 Hp1))
    (cd_scale calibrated_lambda calibrated_lambda_nonneg
       (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)).

(** The calibrated mixture IS that composition at the calibrated pair,
    by conversion — so nothing below is a second object that could drift
    from the one the task ships. *)
Lemma calibrated_mixture_at_calibrated_r_q : forall p argv envp fs Hp0 Hp1,
  calibrated_mixture p argv envp fs Hp0 Hp1
  = calibrated_mixture_at calibrated_r calibrated_q
      calibrated_r_nonneg calibrated_r_le_1
      calibrated_q_nonneg calibrated_q_le_1 p argv envp fs Hp0 Hp1.
Proof. reflexivity. Qed.

(** The two constants lie in the open interval — the hypothesis every
    lemma below asks for, discharged at the calibrated pair once. *)
Lemma calibrated_r_q_in_the_open_interval :
  (0 < calibrated_r)%Q /\ (calibrated_r < 1)%Q
  /\ (0 < calibrated_q)%Q /\ (calibrated_q < 1)%Q.
Proof. repeat split; reflexivity. Qed.

(** THE MASS, at any admissible pair: the shares are what make it [1],
    and the environment coordinate's parameters do not enter. *)
Lemma calibrated_mixture_at_mass_is_one :
  forall r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1,
  (cd_mass (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1)
     == 1)%Q.
Proof.
  intros r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1.
  unfold calibrated_mixture_at.
  cbn [cd_mass cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
  unfold calibrated_lambda, calibrated_co_lambda. ring.
Qed.

(** THE UPPER CERTIFICATE, at any admissible pair. *)
Lemma calibrated_mixture_at_mass_upper :
  forall r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1 l,
  List.NoDup (List.map fin_core l) ->
  (core_sum
     (cd_weight (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p argv envp fs
                   Hp0 Hp1)) l
     <= 1)%Q.
Proof.
  intros r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1 l Hnd.
  rewrite <- (calibrated_mixture_at_mass_is_one r q Hr0 Hr1 Hq0 Hq1
                p argv envp fs Hp0 Hp1).
  unfold calibrated_mixture_at.
  apply cd_mix2_bound_mass; apply cd_scale_bound_mass.
  - apply stdin_geometric_mass_upper. exact Hnd.
  - apply stdin_envp_geometric_mass_upper. exact Hnd.
Qed.

(** THE LOWER CERTIFICATE, at any admissible pair — and this is the one
    that shows the interval is what matters rather than the numerals,
    because it is the only guarantee whose hypotheses mention [r] and
    [q_e] at all, and what it asks of them is exactly positivity. *)
Lemma calibrated_mixture_at_mass_lower_certificate :
  forall r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1 eps,
  (0 < p)%Q -> (0 < r)%Q -> (0 < q)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (1 - eps
          <= core_sum
               (cd_weight (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1
                             p argv envp fs Hp0 Hp1)) l)%Q.
Proof.
  intros r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1 eps Hppos Hrpos Hqpos Heps.
  destruct (stdin_envp_mix2_mass_lower_certificate p r q
              calibrated_co_lambda calibrated_lambda
              calibrated_co_lambda_nonneg calibrated_lambda_nonneg
              argv envp fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 eps
              Hppos Hrpos Hqpos Heps) as [l [Hnd Hle]].
  exists l. split; [exact Hnd |].
  apply (Qle_trans _ (cd_mass (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1
                                 p argv envp fs Hp0 Hp1) - eps)%Q);
    [| exact Hle].
  rewrite (calibrated_mixture_at_mass_is_one r q Hr0 Hr1 Hq0 Hq1
             p argv envp fs Hp0 Hp1).
  apply Qle_refl.
Qed.

(** THE OTHER DIRECTION.  Four endpoints, four collapses, all on the
    stdin-only component's own fixed environment [[]] so that the first
    component contributes nothing either and the number a reader sees is
    the mixture's and not one component's.

    [r = 0] gives every environment weight zero outright; [r = 1] puts
    the whole environment coordinate on the empty environment; [q_e = 0]
    charges any entry at all an infinite price; and [q_e = 1] charges
    any NON-EMPTY entry one, which is why the fourth conjunct asks for a
    non-empty entry rather than a non-empty environment — the
    environment of one empty entry keeps its weight there, and
    [envp_geo_weight_at_one_q_needs_a_non_empty_entry] is the exhibit.

    Read against [calibrated_mixture_envp_bites], which puts POSITIVE
    weight on such a core at the calibrated pair, this pins the
    point: the pair is free inside [(0, 1)] and not free at
    its ends. *)
Lemma calibrated_mixture_at_endpoints_bite :
  forall p q r argv Hp0 Hp1 Hq0 Hq1 Hr0 Hr1 c,
  core_envp c <> [] ->
  (cd_weight (calibrated_mixture_at 0 q (Qle_refl 0) Qle_0_1 Hq0 Hq1
                p argv [] [] Hp0 Hp1) c == 0)%Q
  /\ (cd_weight (calibrated_mixture_at 1 q Qle_0_1 (Qle_refl 1) Hq0 Hq1
                  p argv [] [] Hp0 Hp1) c == 0)%Q
  /\ (cd_weight (calibrated_mixture_at r 0 Hr0 Hr1 (Qle_refl 0) Qle_0_1
                  p argv [] [] Hp0 Hp1) c == 0)%Q
  /\ (forall e, List.In e (core_envp c) -> e <> [] ->
        (cd_weight (calibrated_mixture_at r 1 Hr0 Hr1 Qle_0_1 (Qle_refl 1)
                      p argv [] [] Hp0 Hp1) c == 0)%Q).
Proof.
  intros p q r argv Hp0 Hp1 Hq0 Hq1 Hr0 Hr1 c Hne.
  assert (Hgeo : geo_weight p argv [] [] c = 0%Q)
    by (apply geo_weight_off_envp_zero; exact Hne).
  split; [| split; [| split]].
  - unfold calibrated_mixture_at.
    cbn [cd_weight cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
    rewrite Hgeo, (envp_geo_weight_zero_at_zero_r p q argv [] c). ring.
  - unfold calibrated_mixture_at.
    cbn [cd_weight cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
    rewrite Hgeo, (envp_geo_weight_collapses_at_one_r p q argv [] c), Hgeo.
    ring.
  - unfold calibrated_mixture_at.
    cbn [cd_weight cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
    rewrite Hgeo, (envp_geo_weight_zero_at_zero_q p r argv [] c Hne). ring.
  - intros e Hin Hene. unfold calibrated_mixture_at.
    cbn [cd_weight cd_mix2 cd_scale stdin_geometric stdin_envp_geometric].
    rewrite Hgeo, (envp_geo_weight_zero_at_one_q p r argv [] c e Hin Hene).
    ring.
Qed.


(* =========================================================================
   Addressing ONE file's contents inside a core's file system
   ========================================================================= *)

(** The contents of the file at [pth], read out of a file system, with
    the absent file reading as the empty one.

    THIS IS THE FAMILY'S COORDINATE, and the representation question it
    settles is the only one the two families below turn on, so it is
    settled here and in one place.  [Fs.Fs] is an association list from
    [Fs.path] to bytes, kept strictly sorted ([Fs.valid_fs]), and a
    weight that wants to vary ONE file's contents therefore needs two
    things of it: a way to read that file out of a core, and a way to put
    a given contents back in.  [Fs.fs_lookup] is the first and
    [Fs.fs_set] is the second, both already in [Fs] and neither added
    here.

    Collapsing "absent" onto "empty" is what makes this total, and it
    costs nothing the family uses: the cores this family weighs all have
    the file PRESENT, because they are built by [file_core] below, which
    sets it.  The collapse only decides what [fs_file] says about cores
    the family weighs zero, and it says the same thing [Fs.fs_lookup]
    would have said one [option] later. *)
Definition fs_file (pth : Fs.path) (fs : Fs.Fs) : list byte :=
  match Fs.fs_lookup fs pth with
  | Some d => d
  | None => []
  end.

(** Setting a path and reading it back gives what was set, at every file
    system and with no sortedness hypothesis.  [Fs.fs_set] either
    inserts before the first larger key, replaces an equal one, or
    recurses past a smaller one; in all three cases the entry it lands on
    is the one [Fs.fs_lookup] finds first.  Sortedness is what makes
    [Fs.fs_set] preserve the CANONICAL form and is [Fs.valid_fs]'s
    business, not this lemma's — the round trip holds either way, so
    nothing below has to carry a validity hypothesis in order to read its
    own coordinate back. *)
Lemma fs_lookup_set : forall fs pth d,
  Fs.fs_lookup (Fs.fs_set fs pth d) pth = Some d.
Proof.
  intros fs pth d. induction fs as [| [q e] r IH].
  - cbn [Fs.fs_set Fs.fs_lookup]. rewrite Fs.path_eqb_refl. reflexivity.
  - cbn [Fs.fs_set]. destruct (Fs.path_ltb pth q) eqn:Hlt.
    + cbn [Fs.fs_lookup]. rewrite Fs.path_eqb_refl. reflexivity.
    + destruct (Fs.path_eqb pth q) eqn:Heq.
      * cbn [Fs.fs_lookup]. rewrite Fs.path_eqb_refl. reflexivity.
      * cbn [Fs.fs_lookup]. rewrite Heq. exact IH.
Qed.

Lemma fs_file_set : forall fs0 pth d, fs_file pth (Fs.fs_set fs0 pth d) = d.
Proof.
  intros fs0 pth d. unfold fs_file. rewrite fs_lookup_set. reflexivity.
Qed.

(** THE TEMPLATE: the core over fixed argv, envp, standard input and a
    fixed BASE file system, carrying [d] as the contents of the file at
    [pth].  It is [mkFinCore] with one field built rather than passed,
    and [d] is its LAST argument on purpose — partially applied, it is
    the embedding [list byte -> FinInput.FinCore] that every enumeration
    below maps over, exactly as [mkFinCore argv envp fs] is the embedding
    [stdin_geometric]'s enumerations map over.

    "The file system is otherwise canonical" is [fs0] together with
    [Fs.fs_set]: whatever else the task's file system holds is [fs0]'s
    and is untouched, and the one path the family varies is overwritten.
    Note what that does NOT require of [fs0] — it need not already
    contain [pth], and it need not be sorted for anything below to hold
    (see [fs_lookup_set]).  A task whose [fs0] is [Fs.valid_fs] gets
    weighted cores whose file systems are too; that is a fact about
    [Fs.fs_set] and about the task's [fs0], and this library neither
    needs it nor claims it, exactly as it neither needs nor claims that
    [core_input]'s records are valid. *)
Definition file_core (argv envp : list (list byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : list byte) (d : list byte) : FinCore :=
  mkFinCore argv envp (Fs.fs_set fs0 pth d) s.

(** The coordinate is READABLE OFF the template, which is what makes the
    weight below well defined: the decidable test can ask "is this core
    the template with its own file contents plugged in" only because a
    core has file contents to plug in. *)
Lemma fs_file_file_core : forall argv envp fs0 pth s d,
  fs_file pth (core_fs (file_core argv envp fs0 pth s d)) = d.
Proof.
  intros argv envp fs0 pth s d. cbn [file_core core_fs]. apply fs_file_set.
Qed.

(** ... and so the template is INJECTIVE in the contents.  This is the
    fact the counting and the duplicate-freedom arguments below spend,
    and it is the one place the choice of representation could have gone
    wrong: an embedding that lost information — two contents landing on
    one core — would make the length slice smaller than [256 ^ n] and
    every witness family shorter than it claims. *)
Lemma file_core_inj : forall argv envp fs0 pth s d1 d2,
  file_core argv envp fs0 pth s d1 = file_core argv envp fs0 pth s d2 ->
  d1 = d2.
Proof.
  intros argv envp fs0 pth s d1 d2 Heq.
  rewrite <- (fs_file_file_core argv envp fs0 pth s d1),
          <- (fs_file_file_core argv envp fs0 pth s d2), Heq.
  reflexivity.
Qed.

(* =========================================================================
   Combinator: geometric file contents over a fixed environment
   ========================================================================= *)

(** THE WEIGHT.  Zero unless the core is the template with its own file
    contents plugged in; otherwise the geometric weight of that file's
    LENGTH.

    It is [geo_weight] with the varying coordinate moved: there the core
    is [mkFinCore argv envp fs (core_stdin c)] and the weight reads
    [length (core_stdin c)], here it is [file_core argv envp fs0 pth s
    (fs_file pth (core_fs c))] and the weight reads the length of that.
    Nothing about the memoryless source changes — [geo_point] is the same
    object, so [geo_mass], [geo_slice_total] and [geo_prefix_sum] below
    are the same lemmas and are not proved a second time.

    The environment test is one decidable equation for the reason
    [geo_weight]'s is: it is the hypothesis the counting argument already
    carries, so no translation step stands between them.

    [argv] AND [pth] ARE INDEPENDENT PARAMETERS AND NOTHING HERE TIES
    THEM, which is the one thing a caller of this family can silently get
    wrong.  A typical driver passes the varied file's path AS
    an argument, so a task must pass the SAME path in both places; pass
    two different ones and the distribution varies a file the program
    never opens, which reintroduces exactly the all-or-nothing collapse
    the family exists to remove — while still declaring mass [1], still
    satisfying both certificates, and still putting distinct positive
    weights on distinct contents.  That hazard is not left as a remark:
    the section "The argv/path coupling" at the end of this file names
    the obligation ([argv_names_path]), gives a constructor that makes
    the mismatch UNREPRESENTABLE for the common shape
    ([file_geometric_argv1]), and pins the collapse that happens when it
    is violated ([file_geometric_blind_off_path],
    [file_geometric_needs_argv_to_name_the_path]). *)
Definition file_geo_weight (p : Q) (argv envp : list (list byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : list byte) (c : FinCore) : Q :=
  if decide (c = file_core argv envp fs0 pth s (fs_file pth (core_fs c)))
  then geo_point p (length (fs_file pth (core_fs c)))
  else 0%Q.

(** Its two values, as rewrite rules, so that no proof below names
    [decide] or the [FinCore_eq_dec] instance. *)
Lemma file_geo_weight_match : forall p argv envp fs0 pth s d,
  file_geo_weight p argv envp fs0 pth s (file_core argv envp fs0 pth s d)
    = geo_point p (length d).
Proof.
  intros p argv envp fs0 pth s d. unfold file_geo_weight.
  rewrite fs_file_file_core.
  destruct (decide _) as [_ | Hne]; [reflexivity | congruence].
Qed.

Lemma file_geo_weight_mismatch : forall p argv envp fs0 pth s c,
  c <> file_core argv envp fs0 pth s (fs_file pth (core_fs c)) ->
  file_geo_weight p argv envp fs0 pth s c = 0%Q.
Proof.
  intros p argv envp fs0 pth s c Hne. unfold file_geo_weight.
  destruct (decide _) as [Heq | _]; [congruence | reflexivity].
Qed.

Lemma file_geo_weight_nonneg : forall p argv envp fs0 pth s,
  (0 <= p)%Q -> (p <= 1)%Q ->
  forall c, (0 <= file_geo_weight p argv envp fs0 pth s c)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 c. unfold file_geo_weight.
  destruct (decide _) as [_ | _]; [apply geo_point_nonneg; assumption
                                  | apply Qle_refl].
Qed.

(** The distribution.  Mass [1] is DECLARED, as everywhere in this file,
    and [file_geometric_mass_upper] below is the proof that owes
    something to it.  Declaring [1] rather than anything else is what
    keeps a MIXTURE of this family with the others at total mass [1]
    under [cd_scale] by shares summing to [1] — the composition
    [calibrated_mixture] spells out, and the reason this family
    needs no mixture combinator of its own: there already is one.

    The two side conditions are constructor arguments for the reason
    [stdin_geometric]'s two are: [cd_nonneg] is a field.  [0 < p_stop] is
    NOT among them, for the reason it is not there — nothing the
    constructor needs uses it, and
    [file_geometric_mass_lower_certificate] asks for it as a hypothesis
    of its own statement. *)
Definition file_geometric (p : Q) (argv envp : list (list byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : list byte)
    (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q) : CoreDistribution :=
  mkCoreDistribution (file_geo_weight p argv envp fs0 pth s) 1
    (file_geo_weight_nonneg p argv envp fs0 pth s Hp0 Hp1).

(* =========================================================================
   The block identity: the byte-list sums, read on cores
   ========================================================================= *)

(** THE ONE BRIDGE THIS FAMILY NEEDS, and the reason it is short: a block
    of cores obtained by mapping the template over a list of byte lists
    weighs exactly what that list of byte lists weighs under
    [geo_point].

    Every enumeration below is such a block, and the three byte-list sums
    they are charged against — [bytes_cyl_sum_le] for a cylinder,
    [short_inputs_sum] for a length-bounded prefix family,
    [byte_lists_sum] for one full slice — already exist, proved for the
    envp-varying family and stated over BYTE LISTS rather than cores
    precisely so that a second core-level family could use them.  So no
    enumeration, no cancellation and no telescoping identity is written
    again here: this lemma is the whole of the translation. *)
Lemma qsum_file_block : forall p argv envp fs0 pth s B,
  (qsum (file_geo_weight p argv envp fs0 pth s)
     (List.map (file_core argv envp fs0 pth s) B)
     == qsum (fun d => geo_point p (length d)) B)%Q.
Proof.
  intros p argv envp fs0 pth s B.
  rewrite qsum_map.
  apply qsum_ext. intros d _. rewrite file_geo_weight_match. reflexivity.
Qed.

(* =========================================================================
   The prefix cylinder, and the enumeration that bounds it
   ========================================================================= *)

(** The cores this bound is about: the fixed environment, and file
    contents EXTENDING [bs].  One existential rather than a conjunction
    of an environment test and a prefix test, for the reason
    [in_stdin_cylinder] is one — it is the form both the construction and
    the enumeration want. *)
Definition in_file_cylinder (argv envp : list (list byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : list byte) (bs : list byte) (c : FinCore) : Prop :=
  exists ext, c = file_core argv envp fs0 pth s (bs ++ ext).

(** The depth to enumerate to, read off the task's own list: the longest
    file contents occurring in it.  It is [cores_stdin_depth] on the
    other coordinate, and it exists for the same single reason —
    [Measure.weight_bound_T]'s lists are finite. *)
Definition cores_file_depth (pth : Fs.path) (cs : list FinCore) : nat :=
  List.list_max (List.map (fun c => length (fs_file pth (core_fs c))) cs).

Lemma cores_file_depth_ge : forall pth cs c,
  List.In c cs ->
  (length (fs_file pth (core_fs c)) <= cores_file_depth pth cs)%nat.
Proof.
  intros pth cs c Hc. apply list_max_ge. apply List.in_map_iff.
  exists c. split; [reflexivity | exact Hc].
Qed.

(** THE BOUND OVER CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.

    The shape is [geo_weight_cylinder_bound]'s exactly — enumerate the
    cylinder to a depth read off the list, observe the list is contained
    in the enumeration, and bound the enumeration.  What is different is
    that the enumeration is [bytes_cyl] mapped through the template
    rather than a [Fixpoint] over cores written a second time, and the
    cancellation that bounds it ([bytes_cyl_sum_le]) is the one
    [cyl_enum_sum_le] already proved.  [qsum_core_incl_le] asks
    nothing of the containing list, so [bytes_cyl] never has to be shown
    duplicate-free. *)
Lemma file_geo_weight_cylinder_bound : forall p argv envp fs0 pth s,
  (0 <= p)%Q -> (p <= 1)%Q ->
  forall bs cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> in_file_cylinder argv envp fs0 pth s bs c) ->
    (qsum (file_geo_weight p argv envp fs0 pth s) cs
       <= geo_mass p (length bs))%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 bs cs Hnd Hcyl.
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (List.map (file_core argv envp fs0 pth s)
                  (bytes_cyl bs (cores_file_depth pth cs))))
    | rewrite qsum_file_block;
      apply bytes_cyl_sum_le; assumption ].
  - apply file_geo_weight_nonneg; assumption.
  - exact Hnd.
  - intros c Hc. destruct (Hcyl c Hc) as [ext Hext].
    assert (Hd := cores_file_depth_ge pth cs c Hc).
    rewrite Hext in Hd. rewrite fs_file_file_core in Hd.
    rewrite List.length_app in Hd.
    rewrite Hext. apply List.in_map. apply bytes_cyl_In. lia.
Qed.

(* =========================================================================
   The exports
   ========================================================================= *)

(** The cylinder's mass, in closed form.  It is [stdin_geometric]'s
    number at the same prefix length, and that agreement is the point
    rather than a coincidence: the source spreading the file's bytes is
    the same memoryless source, so a task moving an argument from
    standard input to the input file changes which cores it is talking
    about and not what they cost. *)
Definition file_geometric_cylinder_mass (p : Q) (bs : list byte) : Q :=
  geo_mass p (length bs).

Lemma file_geometric_cylinder_mass_closed_form : forall p bs,
  (file_geometric_cylinder_mass p bs
     == Qpow (1 - p) (length bs) * Qpow (1 # 256) (length bs))%Q.
Proof. intros p bs. apply geo_mass_closed_form. Qed.

(** THE EXPORT: a list of records with duplicate-free cores, all lying in
    the cylinder over a file-contents prefix [bs], weighs at most that
    cylinder's mass.  The hypothesis is the one
    [Measure.weight_bound_T] carries, and [core_sum_map_fin_core] is the
    only step between them.

    This is the statement the family exists for.  A fire set described by
    "the input file begins with these bytes" — a magic number, a header
    field, a malformed length — is charged a number that DEPENDS ON THE
    FILE, where [stdin_geometric] would charge either its whole declared
    mass (if the file system happened to be the fixed one) or nothing at
    all (if it did not, because nothing there weighs anything). *)
Lemma file_geometric_bound : forall p argv envp fs0 pth s Hp0 Hp1 bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_cylinder argv envp fs0 pth s bs (fin_core f)) ->
  (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
     <= file_geometric_cylinder_mass p bs)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 bs l Hnd Hcyl.
  cbn [cd_weight file_geometric]. rewrite core_sum_map_fin_core.
  apply file_geo_weight_cylinder_bound; [exact Hp0 | exact Hp1 | exact Hnd |].
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. apply Hcyl. exact Hin.
Qed.

(** The environment test as a boolean, so that [List.filter] can use it.
    [Measure]'s [Qle_bool] exception is not in play, for the reason it is
    not in [matches_env]: this decides an equality of CORES, which
    [FinCore_eq_dec] decides outright, and no rational is involved. *)
Definition matches_file_env (argv envp : list (list byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : list byte) (c : FinCore) : bool :=
  if decide (c = file_core argv envp fs0 pth s (fs_file pth (core_fs c)))
  then true else false.

Lemma matches_file_env_false : forall argv envp fs0 pth s c,
  matches_file_env argv envp fs0 pth s c = false ->
  c <> file_core argv envp fs0 pth s (fs_file pth (core_fs c)).
Proof.
  intros argv envp fs0 pth s c H. unfold matches_file_env in H.
  destruct (decide _) as [_ | Hne]; [discriminate H | exact Hne].
Qed.

Lemma matches_file_env_true : forall argv envp fs0 pth s c,
  matches_file_env argv envp fs0 pth s c = true ->
  c = file_core argv envp fs0 pth s (fs_file pth (core_fs c)).
Proof.
  intros argv envp fs0 pth s c H. unfold matches_file_env in H.
  destruct (decide _) as [Heq | _]; [exact Heq | discriminate H].
Qed.

(** THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE, exactly as
    [stdin_geometric_bound_or_off_environment] slackens its own: each
    record is in the cylinder OR its core misses the fixed environment
    entirely and therefore weighs nothing.  Both forms stay; neither
    weakens the other, and the repair the widening saves a consumer is
    the same dozen non-obvious lines. *)
Lemma file_geometric_bound_or_off_environment :
  forall p argv envp fs0 pth s Hp0 Hp1 bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_cylinder argv envp fs0 pth s bs (fin_core f)
     \/ matches_file_env argv envp fs0 pth s (fin_core f) = false) ->
  (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
     <= file_geometric_cylinder_mass p bs)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 bs l Hnd Hor.
  cbn [cd_weight file_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_file_env argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_geo_weight_mismatch p argv envp fs0 pth s c
                   (matches_file_env_false _ _ _ _ _ _ Hc)); reflexivity).
  unfold file_geometric_cylinder_mass.
  apply file_geo_weight_cylinder_bound; [exact Hp0 | exact Hp1 | |].
  - apply List.NoDup_filter. exact Hnd.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (Hor f Hinl) as [Hcyl | Hoff].
    + rewrite <- Hf. exact Hcyl.
    + rewrite Hf in Hoff. rewrite Hoff in Hm. discriminate Hm.
Qed.

(** UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass [1].  It is the disjunctive bound at the EMPTY prefix, and the
    whole content is that the disjunction is EXHAUSTIVE there — a core
    either matches the fixed environment, in which case its file contents
    are [[] ++ themselves] and it is in the cylinder over [[]], or it
    does not.  The cylinder mass over the empty prefix is [1] because
    [Qpow] at exponent zero is.

    The LOWER certificate is [file_geometric_mass_lower_certificate]
    below, and it is the half that needs [0 < p_stop]; this one does
    not. *)
Lemma file_geometric_mass_upper : forall p argv envp fs0 pth s Hp0 Hp1 l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
     <= cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1))%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 l Hnd.
  cbn [cd_mass file_geometric].
  change 1%Q with (file_geometric_cylinder_mass p []).
  apply file_geometric_bound_or_off_environment; [exact Hnd |].
  intros f Hf.
  destruct (matches_file_env argv envp fs0 pth s (fin_core f)) eqn:Hm.
  - left. exists (fs_file pth (core_fs (fin_core f))). cbn [List.app].
    apply matches_file_env_true. exact Hm.
  - right. reflexivity.
Qed.

(* =========================================================================
   The counting lemma and the length slice
   ========================================================================= *)

(** A list of records with duplicate-free CORES, every core matching the
    fixed environment and carrying file contents of length exactly [n],
    has at most [256 ^ n] elements.

    It is [injective_core_list_in_cylinder_length_bound] on the file
    coordinate and is proved the same way: such a core is determined by
    its file contents ([file_core_inj], though only the containment
    direction is needed here), [byte_lists n] enumerates the length-[n]
    byte lists, and [List.NoDup_incl_length] turns the injection into a
    cardinality bound.  UNLIKE the envp-varying family, this slice really
    is finite — the environment is fixed here — which is why the two
    attainment lemmas below exist for it and do not exist there. *)
Lemma injective_core_list_in_file_cylinder_length_bound :
  forall (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
         (s : list byte) (n : nat) (l : list FinProcInput),
    List.NoDup (List.map fin_core l) ->
    (forall f, List.In f l ->
       fin_core f = file_core argv envp fs0 pth s (fs_file pth (fin_image_fs f))
       /\ length (fs_file pth (fin_image_fs f)) = n) ->
    (length l <= 256 ^ n)%nat.
Proof.
  intros argv envp fs0 pth s n l Hnd Hall.
  assert (Hle : (length (List.map fin_core l)
                 <= length (List.map (file_core argv envp fs0 pth s)
                              (byte_lists n)))%nat).
  { apply List.NoDup_incl_length; [exact Hnd |].
    intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
    destruct (Hall f Hin) as [Henv Hlen].
    apply List.in_map_iff. exists (fs_file pth (fin_image_fs f)). split.
    - rewrite <- Henv. exact Hf.
    - rewrite <- Hlen. apply byte_lists_complete. }
  rewrite !List.length_map, byte_lists_length in Hle. exact Hle.
Qed.

(** THE BOUND IS ATTAINED AT EVERY [n]: over any launch-time environment,
    any base file system and any path, there is an admissible list of
    exactly [256 ^ n] records, one per length-[n] file contents.  This is
    where [file_core_inj] is spent — the enumeration has to be
    duplicate-free ON CORES, and it is only because distinct contents
    give distinct cores.  Nothing is computed: [byte_lists n] stays a
    [List.flat_map] term. *)
Lemma injective_core_list_in_file_cylinder_length_bound_attained :
  forall (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
         (s : list byte) (n : nat),
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (forall f, List.In f l ->
          fin_core f = file_core argv envp fs0 pth s (fs_file pth (fin_image_fs f))
          /\ length (fs_file pth (fin_image_fs f)) = n)
    /\ length l = (256 ^ n)%nat.
Proof.
  intros argv envp fs0 pth s n.
  exists (List.map (fun d => core_input (file_core argv envp fs0 pth s d))
            (byte_lists n)).
  split; [| split].
  - rewrite List.map_map.
    rewrite (List.map_ext _ (file_core argv envp fs0 pth s))
      by (intros d; apply fin_core_core_input).
    apply NoDup_map_inj; [| apply byte_lists_nodup].
    intros x y _ _ Heq. exact (file_core_inj _ _ _ _ _ _ _ Heq).
  - intros f Hf. apply List.in_map_iff in Hf as [d [Hd Hin]]. subst f.
    cbn [core_input fin_image_fs].
    rewrite fs_file_file_core, fin_core_core_input.
    split; [reflexivity |]. apply byte_lists_In_length. exact Hin.
  - rewrite List.length_map, byte_lists_length. reflexivity.
Qed.

(** THE LENGTH SLICE: a list drawn from one file-length slice weighs at
    most [p_stop * (1 - p_stop) ^ n] — the geometric distribution over
    LENGTHS, with no [1/256] left in it.  The counting lemma supplies the
    count, [qsum_const] observes that every core in a slice
    weighs the same, and [geo_slice_total] is the cancellation, unchanged
    from the standard-input family. *)
Lemma file_geometric_slice_bound : forall p argv envp fs0 pth s Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = file_core argv envp fs0 pth s (fs_file pth (fin_image_fs f))
     /\ length (fs_file pth (fin_image_fs f)) = n) ->
  (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
     <= p * Qpow (1 - p) n)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 n l Hnd Hall.
  cbn [cd_weight file_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_const _ _ (geo_point p n)).
  2:{ intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
      destruct (Hall f Hin) as [Henv Hlen].
      rewrite <- Hf, Henv, file_geo_weight_match, Hlen. reflexivity. }
  rewrite <- (geo_slice_total p n).
  apply Qmult_le_compat_r; [| apply geo_point_nonneg; assumption].
  apply Qnat_le. rewrite List.length_map.
  apply (injective_core_list_in_file_cylinder_length_bound
           argv envp fs0 pth s n l); assumption.
Qed.

(** THE SLICE BOUND'S CONSTANT IS REACHED, at every [n]: the full slice
    is admissible and weighs [p_stop * (1 - p_stop) ^ n] exactly.
    Pinning that a duplicate-free slice has at most [256 ^ n] elements
    says the counting is right; pinning that the bound those elements
    imply is reached says the EXPORT is right. *)
Lemma file_geometric_slice_bound_attained :
  forall p argv envp fs0 pth s Hp0 Hp1 n,
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (forall f, List.In f l ->
          fin_core f = file_core argv envp fs0 pth s (fs_file pth (fin_image_fs f))
          /\ length (fs_file pth (fin_image_fs f)) = n)
    /\ (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
          == p * Qpow (1 - p) n)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 n.
  destruct (injective_core_list_in_file_cylinder_length_bound_attained
              argv envp fs0 pth s n) as [l [Hnd [Hall Hlen]]].
  exists l. split; [exact Hnd | split; [exact Hall |]].
  cbn [cd_weight file_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_const _ _ (geo_point p n)).
  2:{ intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
      destruct (Hall f Hin) as [Henv Hlength].
      rewrite <- Hf, Henv, file_geo_weight_match, Hlength. reflexivity. }
  rewrite List.length_map, Hlen. apply geo_slice_total.
Qed.

(** ... and so NO SMALLER CONSTANT IS A SLICE BOUND.  The contrapositive
    shape is deliberate, as at [stdin_geometric_slice_bound_sharp]: it is
    quantified over every candidate [K] a future version of this file
    might try to prove instead, so it stays true as a regression test
    rather than as a fact about today's proof. *)
Lemma file_geometric_slice_bound_sharp :
  forall p argv envp fs0 pth s Hp0 Hp1 n K,
  (forall l, List.NoDup (List.map fin_core l) ->
     (forall f, List.In f l ->
        fin_core f = file_core argv envp fs0 pth s (fs_file pth (fin_image_fs f))
        /\ length (fs_file pth (fin_image_fs f)) = n) ->
     (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
        <= K)%Q) ->
  (p * Qpow (1 - p) n <= K)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 n K Hbound.
  destruct (file_geometric_slice_bound_attained p argv envp fs0 pth s
              Hp0 Hp1 n) as [l [Hnd [Hall Hsum]]].
  rewrite <- Hsum. apply Hbound; assumption.
Qed.

(* =========================================================================
   The lower certificate for [file_geometric]
   ========================================================================= *)

(** THE WITNESS FAMILY: over a fixed environment, one record per file
    contents SHORTER than [k].  [short_inputs] is the same length-bounded
    enumeration of byte lists the standard-input certificate uses; only
    the embedding into cores is this family's.

    As everywhere in this file, these records are NOT claimed valid and
    NOT claimed rejected by anything; the certificate is arithmetic about
    the declared mass. *)
Definition file_geo_lower_witness (argv envp : list (list byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : list byte) (k : nat)
    : list FinProcInput :=
  List.map (fun d => core_input (file_core argv envp fs0 pth s d))
    (short_inputs k).

Lemma map_fin_core_file_geo_lower_witness : forall argv envp fs0 pth s k,
  List.map fin_core (file_geo_lower_witness argv envp fs0 pth s k)
    = List.map (file_core argv envp fs0 pth s) (short_inputs k).
Proof.
  intros argv envp fs0 pth s k. unfold file_geo_lower_witness.
  rewrite List.map_map. apply List.map_ext. intros d.
  apply fin_core_core_input.
Qed.

Lemma file_geo_lower_witness_nodup : forall argv envp fs0 pth s k,
  List.NoDup
    (List.map fin_core (file_geo_lower_witness argv envp fs0 pth s k)).
Proof.
  intros argv envp fs0 pth s k. rewrite map_fin_core_file_geo_lower_witness.
  apply NoDup_map_inj; [| apply short_inputs_nodup].
  intros x y _ _ Heq. exact (file_core_inj _ _ _ _ _ _ _ Heq).
Qed.

(** ... and it weighs the partial sum of the geometric series over
    lengths.  Both halves are already proved elsewhere — the block
    identity above and [short_inputs_sum] — so this is two rewrites and
    no induction. *)
Lemma qsum_file_short_inputs : forall p argv envp fs0 pth s k,
  (qsum (file_geo_weight p argv envp fs0 pth s)
     (List.map (file_core argv envp fs0 pth s) (short_inputs k))
     == geo_prefix_sum p k)%Q.
Proof.
  intros p argv envp fs0 pth s k.
  rewrite qsum_file_block. apply short_inputs_sum.
Qed.

(** THE WITNESS, at each [k]: an admissible list weighing exactly
    [1 - (1 - p_stop) ^ k].  The target is that rather than the declared
    mass because the mass is not available — for [p_stop < 1] no finite
    list attains it ([file_geometric_mass_not_attained] below).  No
    hypothesis beyond the constructor's own is needed here; the equality
    is unconditional arithmetic. *)
Lemma file_geometric_mass_lower_witness :
  forall p argv envp fs0 pth s Hp0 Hp1 k,
  List.NoDup
    (List.map fin_core (file_geo_lower_witness argv envp fs0 pth s k))
  /\ (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1))
        (file_geo_lower_witness argv envp fs0 pth s k)
        == 1 - Qpow (1 - p) k)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 k.
  split; [apply file_geo_lower_witness_nodup |].
  cbn [cd_weight file_geometric].
  rewrite core_sum_map_fin_core, map_fin_core_file_geo_lower_witness.
  rewrite qsum_file_short_inputs. apply geo_prefix_sum_closed.
Qed.

(** The same fact in the shape the certificate vocabulary uses, beside
    [stdin_geometric_mass_lower_prefix]: SOME admissible list weighs the
    target. *)
Lemma file_geometric_mass_lower_prefix :
  forall p argv envp fs0 pth s Hp0 Hp1 k,
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
          == 1 - Qpow (1 - p) k)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 k.
  exists (file_geo_lower_witness argv envp fs0 pth s k).
  apply file_geometric_mass_lower_witness.
Qed.

(** THE LOWER CERTIFICATE: for every margin [eps] there is an admissible
    list weighing at least the declared mass minus that margin.  With
    [file_geometric_mass_upper] above it, the declared [1] is the least
    upper bound of the admissible partial sums — approached but, by
    [file_geometric_mass_not_attained], never met.

    [0 < p_stop] IS A HYPOTHESIS OF THIS LEMMA AND NOT A TIGHTENING OF
    THE CONSTRUCTOR, for the reason
    [stdin_geometric_mass_lower_certificate] gives.  It is spent exactly
    once, inside [geo_gap_small], choosing the [k] whose tail is under
    [eps]; [file_geometric_mass_lower_needs_positive] shows the
    conclusion is false without it. *)
Lemma file_geometric_mass_lower_certificate :
  forall p argv envp fs0 pth s Hp0 Hp1 eps,
  (0 < p)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1) - eps
          <= core_sum (cd_weight (file_geometric p argv envp fs0 pth s
                                    Hp0 Hp1)) l)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 eps Hpos Heps.
  destruct (geo_gap_small p eps Hpos Hp1 Heps) as [k Hk].
  destruct (file_geometric_mass_lower_prefix p argv envp fs0 pth s Hp0 Hp1 k)
    as [l [Hnd Hsum]].
  exists l. split; [exact Hnd |].
  rewrite Hsum. cbn [cd_mass file_geometric].
  apply (proj2 (Qle_minus_iff (1 - eps) (1 - Qpow (1 - p) k))).
  apply (Qle_trans _ (eps + - Qpow (1 - p) k)%Q);
    [ apply (proj1 (Qle_minus_iff (Qpow (1 - p) k) eps)); exact Hk
    | apply Qle_of_Qeq; ring].
Qed.

(* =========================================================================
   ... and this mass is a SUPREMUM and not a maximum
   ========================================================================= *)

(** A list confined to file contents of length at most [n] weighs at most
    [1 - (1 - p_stop) ^ (n + 1)] — the partial sum at its own horizon.
    It MISSES THE TAIL, and the tail is the whole point.  The proof is
    the witness family read in the other direction, exactly as
    [stdin_geometric_bound_by_max_length] reads its own. *)
Lemma file_geometric_bound_by_max_length :
  forall p argv envp fs0 pth s Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> (length (fs_file pth (fin_image_fs f)) <= n)%nat) ->
  (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
     <= 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 n l Hnd Hlen.
  cbn [cd_weight file_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_file_env argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_geo_weight_mismatch p argv envp fs0 pth s c
                   (matches_file_env_false _ _ _ _ _ _ Hc)); reflexivity).
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (List.map (file_core argv envp fs0 pth s) (short_inputs (S n))))
    | rewrite qsum_file_short_inputs, geo_prefix_sum_closed;
      apply Qle_refl ].
  - apply file_geo_weight_nonneg; assumption.
  - apply List.NoDup_filter. exact Hnd.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    apply List.in_map_iff. exists (fs_file pth (core_fs c)). split.
    + symmetry. apply matches_file_env_true. exact Hm.
    + apply short_inputs_complete.
      assert (Hle := Hlen f Hinl).
      rewrite <- Hf. cbn [fin_core core_fs]. lia.
Qed.

(** ... AND THAT BOUND IS EXACTLY TIGHT: the witness family at
    [k = n + 1] is a list of file contents of length at most [n], and it
    weighs the bound exactly.  So the shortfall below is the
    distribution's and not the proof's. *)
Lemma file_geometric_bound_by_max_length_attained :
  forall p argv envp fs0 pth s Hp0 Hp1 n,
  (forall f, List.In f (file_geo_lower_witness argv envp fs0 pth s (S n)) ->
     (length (fs_file pth (fin_image_fs f)) <= n)%nat)
  /\ (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1))
        (file_geo_lower_witness argv envp fs0 pth s (S n))
        == 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 n. split.
  - intros f Hf. unfold file_geo_lower_witness in Hf.
    apply List.in_map_iff in Hf as [d [Hd Hin]]. subst f.
    cbn [core_input fin_image_fs]. rewrite fs_file_file_core.
    apply short_inputs_In_length in Hin. lia.
  - apply file_geometric_mass_lower_witness.
Qed.

(** For [p_stop < 1] NO admissible list weighs the declared mass — every
    one of them weighs strictly less.  The [n] is the list's own longest
    file contents, which is the only place the FINITENESS of
    [Measure.weight_bound_T]'s lists is needed: a list has a horizon, and
    beyond it sits a positive tail ([Qpow_pos]) it does not collect.

    At [p_stop = 1] it is false, and [file_point_cd_mass_attained] is the
    list that refutes it. *)
Lemma file_geometric_mass_not_attained :
  forall p argv envp fs0 pth s Hp0 Hp1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
       < cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1))%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 Hlt l Hnd.
  cbn [cd_mass file_geometric].
  pose (n := List.list_max
               (List.map (fun f => length (fs_file pth (fin_image_fs f))) l)).
  apply (Qle_lt_trans _ (1 - Qpow (1 - p) (S n))%Q).
  - apply file_geometric_bound_by_max_length; [exact Hnd |].
    intros f Hf. apply list_max_ge. apply List.in_map_iff.
    exists f. split; [reflexivity | exact Hf].
  - apply (proj2 (Qlt_minus_iff (1 - Qpow (1 - p) (S n)) 1)).
    apply (Qlt_le_trans _ (Qpow (1 - p) (S n))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qpow_pos. apply (Qlt_minus_iff p 1). exact Hlt.
Qed.

(** The same fact under the name a reader looks for, beside
    [stdin_geometric_mass_supremum_not_maximum]. *)
Lemma file_geometric_mass_supremum_not_maximum :
  forall p argv envp fs0 pth s Hp0 Hp1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    ~ (core_sum (cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1)) l
         == cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1))%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 Hlt l Hnd.
  apply Qlt_not_eq.
  apply file_geometric_mass_not_attained; assumption.
Qed.

(* =========================================================================
   Non-vacuity: the input file really carries mass
   ========================================================================= *)

(** [geo_weight]'s file-system instance, stated because the bite below
    needs it and the file had only the argv and envp ones.  It is the
    same [geo_weight_mismatch] the comment at
    [geo_weight_off_environment_zero] says the other two fields go
    through. *)
Lemma geo_weight_off_fs_zero : forall p argv envp fs c,
  core_fs c <> fs -> geo_weight p argv envp fs c = 0%Q.
Proof.
  intros p argv envp fs c Hne. apply geo_weight_mismatch.
  intros Heq. apply (f_equal core_fs) in Heq. cbn [core_fs] in Heq.
  exact (Hne Heq).
Qed.

Lemma file_geo_weight_off_environment_zero : forall p argv envp fs0 pth s c,
  core_argv c <> argv -> file_geo_weight p argv envp fs0 pth s c = 0%Q.
Proof.
  intros p argv envp fs0 pth s c Hne. apply file_geo_weight_mismatch.
  intros Heq. apply (f_equal core_argv) in Heq.
  cbn [file_core core_argv] in Heq. exact (Hne Heq).
Qed.

(** A path and a core over it: the one-byte path [i], and the core over
    the empty launch-time environment whose file at that path is empty.
    As at [geo_example_core], neither is claimed valid; they are points
    of [Fs.path] and [FinInput.FinCore] chosen so that the two families
    disagree at the second. *)
Definition file_example_path : Fs.path := [Z_to_bv 8 105].

Definition file_example_core : FinCore :=
  file_core [] [] [] file_example_path [] [].

(** THE BITE THE FAMILY EXISTS FOR, both halves on ONE core.
    [stdin_geometric] over the empty file system weighs
    [file_example_core] exactly zero — its file system is not the fixed
    one, because it HAS the input file in it — while [file_geometric]
    weighs it strictly positively.

    That is the gap restated as a theorem.  Take a program that is
    passed a file path as [argv[1]], reads that file, and reads nothing
    from standard input.  Under a distribution built
    from [stdin_geometric] alone every weighted core carries the SAME
    file system and therefore induces the same program behavior, so
    [Classifier.good_input] and [Classifier.agree] — per-input predicates
    about that behavior — hold at all weighted cores or at none, the
    reject set is all-or-nothing on the support, and the least [b] that
    [Measure.weight_bound_T] can be proved at is exactly [0] or [1].
    Under this family it is not: the file's bytes carry mass, so
    intermediate values are available and a bound read as a fraction of
    the input space is reading a measure that can take one.

    What it does NOT say, and the misreading is the one the header warns
    about at the geometric lower certificate: that any particular task's
    bound is thereby sharper.  Weight on a core is what makes a bound
    about that core non-vacuous; it is not itself a bound. *)
Lemma file_geometric_fs_bites : forall p Hp0 Hp1,
  (0 < p)%Q ->
  cd_weight (stdin_geometric p [] [] [] Hp0 Hp1) file_example_core = 0%Q
  /\ (0 < cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
            file_example_core)%Q.
Proof.
  intros p Hp0 Hp1 Hlt. split.
  - cbn [cd_weight stdin_geometric]. apply geo_weight_off_fs_zero.
    unfold file_example_core, file_core, file_example_path.
    cbn [core_fs Fs.fs_set]. discriminate.
  - cbn [cd_weight file_geometric]. unfold file_example_core.
    rewrite file_geo_weight_match.
    unfold geo_point, geo_mass. cbn [length Qpow].
    rewrite Qmult_1_r. exact Hlt.
Qed.

(** ... and the family is not a constant either: a core whose argv misses
    the fixed one weighs exactly zero.  Both halves are needed for the
    reason [stdin_geometric_bites] needs both — without the second,
    "weight zero off the fixed environment" would be a claim only the
    definition makes; without the first, every bound above would hold of
    a distribution that weighs nothing. *)
Lemma file_geometric_bites : forall p Hp0 Hp1,
  (0 < p)%Q ->
  (0 < cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
         file_example_core)%Q
  /\ cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
       geo_example_other = 0%Q.
Proof.
  intros p Hp0 Hp1 Hlt. split.
  - apply (file_geometric_fs_bites p Hp0 Hp1 Hlt).
  - cbn [cd_weight file_geometric].
    apply file_geo_weight_off_environment_zero.
    unfold geo_example_other. cbn [core_argv]. discriminate.
Qed.

(* =========================================================================
   Non-vacuity: the mass is reached at [p_stop = 1], and [List.NoDup] is
   load-bearing
   ========================================================================= *)

(** The member of the family at [p_stop = 1]: stop immediately, always.
    It is the point mass on the empty file, it is admitted by the
    constructor — [Qle_0_1] and [Qle_refl] are its two side conditions —
    and it is what makes the two refutations below closed arithmetic
    instead of open terms. *)
Definition file_point_cd : CoreDistribution :=
  file_geometric 1 [] [] [] file_example_path [] Qle_0_1 (Qle_refl 1).

Definition file_empty_input : FinProcInput := core_input file_example_core.

(** The declared mass [1] is not padding at this instance: a one-element
    admissible list reaches it OUTRIGHT.  That is special to
    [p_stop = 1], where the tail past the empty file is empty, and it is
    this file's witness that [file_geometric_mass_not_attained] cannot
    drop its [p_stop < 1].  A closed [Qeq] between literals, decided by
    computation, per the header's exception. *)
Lemma file_point_cd_mass_attained :
  List.NoDup (List.map fin_core [file_empty_input])
  /\ (core_sum (cd_weight file_point_cd) [file_empty_input]
        == cd_mass file_point_cd)%Q.
Proof.
  split.
  - cbn [List.map].
    apply List.NoDup_cons; [intros H; exact H | apply List.NoDup_nil].
  - vm_compute. reflexivity.
Qed.

(** THE [List.NoDup] HYPOTHESIS IS LOAD-BEARING for this family's
    cylinder bound, and this is [stdin_geometric_bound_needs_nodup]
    transposed: offer the same core twice — two records, so the list is
    duplicate-free as a list of RECORDS, and both records lie in the
    cylinder over the empty prefix — and the sum is [2] against a
    cylinder mass of [1].  All three conjuncts are needed, for the
    reasons the baseline lemma gives. *)
Lemma file_geometric_bound_needs_nodup :
  ~ List.NoDup (List.map fin_core [file_empty_input; file_empty_input])
  /\ (forall f, List.In f [file_empty_input; file_empty_input] ->
        in_file_cylinder [] [] [] file_example_path [] [] (fin_core f))
  /\ ~ (core_sum (cd_weight file_point_cd)
          [file_empty_input; file_empty_input]
          <= file_geometric_cylinder_mass 1 [])%Q.
Proof.
  split; [| split].
  - intros Hnd. cbn [List.map] in Hnd.
    apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd as [Hnin _].
    apply Hnin. left. reflexivity.
  - intros f Hf. destruct Hf as [Hf | [Hf | []]]; subst f;
      exists []; reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate Hle.
Qed.

(* =========================================================================
   The two degenerate endpoints, both pinned
   ========================================================================= *)

(** BOTH ENDPOINTS THE CONSTRUCTOR ADMITS ARE PINNED, and they fail in
    the two different ways this file has names for.  At [p_stop = 0] the
    weight vanishes identically, so every list weighs nothing while the
    declared mass stays [1] and the lower certificate is false — the
    [envp_geo_weight_zero_at_zero_p] shape.  At [p_stop = 1] the weight
    does NOT vanish, and that degeneracy is the interesting one, because
    every core whose input file is NON-EMPTY weighs zero while the
    empty-file core keeps its weight: the family goes blind to the file
    contents without going quiet — the [q_e = 0] shape, and the failure
    mode that would go unnoticed, since at that endpoint the distribution
    is still non-zero, still sums correctly, still declares mass [1]
    honestly, and still measures nothing about the only thing it was
    added to measure. *)
Lemma file_geo_weight_zero_at_zero_p : forall argv envp fs0 pth s c,
  (file_geo_weight 0 argv envp fs0 pth s c == 0)%Q.
Proof.
  intros argv envp fs0 pth s c. unfold file_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  unfold geo_point. ring.
Qed.

Lemma file_geometric_mass_lower_needs_positive : forall argv envp fs0 pth s,
  (forall l : list FinProcInput,
     (core_sum (cd_weight (file_geometric 0 argv envp fs0 pth s
                             (Qle_refl 0) Qle_0_1)) l == 0)%Q)
  /\ ~ (cd_mass (file_geometric 0 argv envp fs0 pth s (Qle_refl 0) Qle_0_1)
          - (1 # 2) <= 0)%Q.
Proof.
  intros argv envp fs0 pth s. split.
  - intros l. apply core_sum_zero_weight. intros c.
    cbn [cd_weight file_geometric]. apply file_geo_weight_zero_at_zero_p.
  - cbn [cd_mass file_geometric]. intros Hle.
    apply (proj2 (Qle_bool_iff _ _)) in Hle. vm_compute in Hle.
    discriminate Hle.
Qed.

Lemma file_geo_weight_collapses_at_one_p : forall argv envp fs0 pth s c,
  fs_file pth (core_fs c) <> [] ->
  (file_geo_weight 1 argv envp fs0 pth s c == 0)%Q.
Proof.
  intros argv envp fs0 pth s c Hne. unfold file_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  destruct (fs_file pth (core_fs c)) as [| b d];
    [exfalso; exact (Hne eq_refl) |].
  unfold geo_point, geo_mass. cbn [length Qpow]. ring.
Qed.

(** ... and the blindness in the shape
    [stdin_envp_geometric_envp_needs_positive_q] states it for the other
    non-vanishing degeneracy.  Both are exported: a reader asking "what
    goes wrong at this parameter" wants the blindness, and a reader
    asking "what does the weight become" wants the identity above. *)
Lemma file_geometric_needs_p_below_one : forall argv envp fs0 pth s c,
  fs_file pth (core_fs c) <> [] ->
  (cd_weight (file_geometric 1 argv envp fs0 pth s Qle_0_1 (Qle_refl 1)) c
     == 0)%Q.
Proof.
  intros argv envp fs0 pth s c Hne. cbn [cd_weight file_geometric].
  apply file_geo_weight_collapses_at_one_p. exact Hne.
Qed.

(* =========================================================================
   Combinator: geometric file contents BEHIND A FIXED HEADER
   ========================================================================= *)

(** THE FAMILY [file_geometric] IS NOT, and the reason it is needed.  A
    driver that reads its input file through a fixed header — a length
    word, a magic number, a field the driver checks before it hands
    anything to the library under test — rejects almost every file
    [file_geometric] weighs, because that family spreads the header's
    bytes uniformly along with the rest.  Only the sliver of files whose
    random header happens to parse reaches the library, so a
    [Measure.weight_bound_T] bound over the whole-file family prices the
    driver's reject path and not the library.  Conditioning on the
    header is not available (there is no conditioning combinator), and
    the header cylinder's own mass is [geo_mass p_stop (length hdr)],
    far too small to serve as a scale.

    So this family takes the header as a PARAMETER and weighs only the
    bytes after it: a matching core whose file is [hdr ++ t] weighs
    [geo_point p_stop (length t)], a matching core whose file does not
    begin with [hdr] weighs zero, and the declared mass is [1] — the
    geometric mass of the payload alone, normalised, exactly as if the
    header had been conditioned on.

    ** It is a LENGTH SHIFT through an injective map, and nothing else

    Every fact about [file_geometric] goes through [qsum_file_block] onto
    the byte-list sums ([bytes_cyl_sum_le], [short_inputs_sum],
    [byte_lists_sum]) and the length-only arithmetic ([geo_slice_total],
    [geo_prefix_sum_closed]), none of which mentions a core.  This family
    is that family with its embedding of byte lists into cores composed
    with [t |-> hdr ++ t] ([file_prefix_core]), which is injective by
    [file_core_inj] and [List.app_inv_head].  So the block identity
    ([qsum_file_prefix_block]) carries over through [qsum_map] unchanged,
    every byte-list sum is reused as it stands, and what is proved anew
    is exactly: the weight's rewrite rules, nonnegativity, the shifted
    block identity, and the depth step of the cylinder bound, where the
    enumeration depth is [cores_file_depth] less [length hdr].

    ** The two facts the spec of record asks for by name

    At the EMPTY header the family is [file_geometric] pointwise
    ([file_prefix_geo_weight_nil], [file_geometric_prefix_nil_pointwise]):
    the header-conditioned family is a generalisation and not a rival.
    And the HEADER BITES ([file_geometric_prefix_off_header_zero],
    [file_geometric_prefix_header_bites]): a core whose file does not
    start with the header weighs zero while the declared mass stays [1],
    exhibited on the very core the whole-file family weighs positively.

    The alphabet-restricted variant — bytes i.i.d. over a fixed subset
    rather than all 256 — is scoped as a separate addition and is not
    here. *)

(** Splitting a header off a byte list: [Some t] exactly when
    [d = hdr ++ t].  A [Fixpoint] with one decidable byte comparison per
    header byte, so that it computes under [vm_compute] on closed
    instances (the pins at the end of this section, and the demo). *)
Fixpoint strip_prefix (hdr d : list byte) : option (list byte) :=
  match hdr, d with
  | [], _ => Some d
  | _ :: _, [] => None
  | h :: hdr', b :: d' =>
      if decide (h = b) then strip_prefix hdr' d' else None
  end.

Lemma strip_prefix_app : forall hdr t, strip_prefix hdr (hdr ++ t) = Some t.
Proof.
  induction hdr as [| h hdr IH]; intros t; [reflexivity |].
  cbn [List.app strip_prefix].
  destruct (decide (h = h)) as [_ | Hne];
    [apply IH | exfalso; apply Hne; reflexivity].
Qed.

Lemma strip_prefix_Some : forall hdr d t,
  strip_prefix hdr d = Some t -> d = hdr ++ t.
Proof.
  induction hdr as [| h hdr IH]; intros d t H.
  - cbn [strip_prefix] in H. injection H as <-. reflexivity.
  - destruct d as [| b d]; cbn [strip_prefix] in H; [discriminate H |].
    destruct (decide (h = b)) as [<- | _]; [| discriminate H].
    cbn [List.app]. f_equal. apply IH. exact H.
Qed.

Lemma strip_prefix_None : forall hdr d,
  strip_prefix hdr d = None -> forall t, d <> hdr ++ t.
Proof.
  intros hdr d H t Heq. subst d. rewrite strip_prefix_app in H.
  discriminate H.
Qed.

Lemma strip_prefix_None_of_no_extension : forall hdr d,
  (forall t, d <> hdr ++ t) -> strip_prefix hdr d = None.
Proof.
  intros hdr d H. destruct (strip_prefix hdr d) as [t |] eqn:Hs; [| reflexivity].
  exfalso. apply (H t). apply strip_prefix_Some. exact Hs.
Qed.

Lemma strip_prefix_nil : forall d, strip_prefix [] d = Some d.
Proof. reflexivity. Qed.

(** THE EMBEDDING: [file_core] composed with [t |-> hdr ++ t].  It is
    the map every enumeration below is pushed through, with [t] last so
    that the partial application is that map, and it is injective — the
    one new fact the counting and duplicate-freedom arguments spend. *)
Definition file_prefix_core (hdr : list byte) (argv envp : list (list byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : list byte) (t : list byte) : FinCore :=
  file_core argv envp fs0 pth s (hdr ++ t).

Lemma fs_file_file_prefix_core : forall hdr argv envp fs0 pth s t,
  fs_file pth (core_fs (file_prefix_core hdr argv envp fs0 pth s t)) = hdr ++ t.
Proof. intros hdr argv envp fs0 pth s t. apply fs_file_file_core. Qed.

Lemma file_prefix_core_inj : forall hdr argv envp fs0 pth s t1 t2,
  file_prefix_core hdr argv envp fs0 pth s t1
    = file_prefix_core hdr argv envp fs0 pth s t2 ->
  t1 = t2.
Proof.
  intros hdr argv envp fs0 pth s t1 t2 Heq.
  apply file_core_inj in Heq. apply (List.app_inv_head hdr). exact Heq.
Qed.

(** THE WEIGHT.  The environment test is [file_geo_weight]'s, unchanged;
    what differs is what is read off a matching core: the file's PAYLOAD
    past the header, or nothing if the header is not there. *)
Definition file_prefix_geo_weight (hdr : list byte) (p : Q)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : list byte) (c : FinCore) : Q :=
  if decide (c = file_core argv envp fs0 pth s (fs_file pth (core_fs c)))
  then match strip_prefix hdr (fs_file pth (core_fs c)) with
       | Some t => geo_point p (length t)
       | None => 0%Q
       end
  else 0%Q.

(** Its three values, as rewrite rules. *)
Lemma file_prefix_geo_weight_match : forall hdr p argv envp fs0 pth s t,
  file_prefix_geo_weight hdr p argv envp fs0 pth s
    (file_prefix_core hdr argv envp fs0 pth s t)
    = geo_point p (length t).
Proof.
  intros hdr p argv envp fs0 pth s t.
  unfold file_prefix_geo_weight, file_prefix_core.
  rewrite fs_file_file_core.
  destruct (decide _) as [_ | Hne]; [| congruence].
  rewrite strip_prefix_app. reflexivity.
Qed.

Lemma file_prefix_geo_weight_mismatch : forall hdr p argv envp fs0 pth s c,
  c <> file_core argv envp fs0 pth s (fs_file pth (core_fs c)) ->
  file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros hdr p argv envp fs0 pth s c Hne. unfold file_prefix_geo_weight.
  destruct (decide _) as [Heq | _]; [congruence | reflexivity].
Qed.

Lemma file_prefix_geo_weight_off_header : forall hdr p argv envp fs0 pth s c,
  strip_prefix hdr (fs_file pth (core_fs c)) = None ->
  file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros hdr p argv envp fs0 pth s c Hn. unfold file_prefix_geo_weight.
  destruct (decide _) as [_ | _]; [rewrite Hn; reflexivity | reflexivity].
Qed.

(** ZERO ON A FILE THAT DOES NOT EXTEND THE HEADER, in the form a caller
    states it: no payload [t] makes the file [hdr ++ t]. *)
Lemma file_prefix_geo_weight_off_header_zero :
  forall hdr p argv envp fs0 pth s c,
  (forall t, fs_file pth (core_fs c) <> hdr ++ t) ->
  file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros hdr p argv envp fs0 pth s c Hno.
  apply file_prefix_geo_weight_off_header.
  apply strip_prefix_None_of_no_extension. exact Hno.
Qed.

Lemma file_prefix_geo_weight_nonneg : forall hdr p argv envp fs0 pth s,
  (0 <= p)%Q -> (p <= 1)%Q ->
  forall c, (0 <= file_prefix_geo_weight hdr p argv envp fs0 pth s c)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 c. unfold file_prefix_geo_weight.
  destruct (decide _) as [_ | _]; [| apply Qle_refl].
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |];
    [apply geo_point_nonneg; assumption | apply Qle_refl].
Qed.

(** The distribution.  Mass [1] is DECLARED, as everywhere in this file:
    it is the geometric mass of the PAYLOAD, and
    [file_geometric_prefix_mass_upper] and
    [file_geometric_prefix_mass_lower_certificate] below are the two
    halves of the certificate that it is honest. *)
Definition file_geometric_prefix (hdr : list byte) (p : Q)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : list byte) (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q)
    : CoreDistribution :=
  mkCoreDistribution (file_prefix_geo_weight hdr p argv envp fs0 pth s) 1
    (file_prefix_geo_weight_nonneg hdr p argv envp fs0 pth s Hp0 Hp1).

(* =========================================================================
   The empty header: [file_geometric], pointwise
   ========================================================================= *)

(** At [hdr = []] the payload IS the file, and the weight is
    [file_geo_weight]'s by conversion — [strip_prefix [] d] is [Some d]
    definitionally, so the [match] disappears. *)
Lemma file_prefix_geo_weight_nil : forall p argv envp fs0 pth s c,
  file_prefix_geo_weight [] p argv envp fs0 pth s c
    = file_geo_weight p argv envp fs0 pth s c.
Proof.
  intros p argv envp fs0 pth s c. unfold file_prefix_geo_weight, file_geo_weight.
  destruct (decide _) as [_ | _]; reflexivity.
Qed.

Lemma file_geometric_prefix_nil_pointwise :
  forall p argv envp fs0 pth s Hp0 Hp1 c,
  (cd_weight (file_geometric_prefix [] p argv envp fs0 pth s Hp0 Hp1) c
     == cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1) c)%Q.
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 c.
  cbn [cd_weight file_geometric_prefix file_geometric].
  rewrite file_prefix_geo_weight_nil. reflexivity.
Qed.

Lemma file_geometric_prefix_nil_mass : forall p argv envp fs0 pth s Hp0 Hp1,
  cd_mass (file_geometric_prefix [] p argv envp fs0 pth s Hp0 Hp1)
    = cd_mass (file_geometric p argv envp fs0 pth s Hp0 Hp1).
Proof. reflexivity. Qed.

(* =========================================================================
   The block identity, shifted
   ========================================================================= *)

(** [qsum_file_block] through the shifted embedding: a block of cores
    obtained by mapping [file_prefix_core] over a list of PAYLOADS weighs
    what that list of payloads weighs under [geo_point].  The header
    contributes no factor, which is the whole design. *)
Lemma qsum_file_prefix_block : forall hdr p argv envp fs0 pth s B,
  (qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s)
     (List.map (file_prefix_core hdr argv envp fs0 pth s) B)
     == qsum (fun t => geo_point p (length t)) B)%Q.
Proof.
  intros hdr p argv envp fs0 pth s B.
  rewrite qsum_map.
  apply qsum_ext. intros t _. rewrite file_prefix_geo_weight_match. reflexivity.
Qed.

(* =========================================================================
   The payload cylinder, and the enumeration that bounds it
   ========================================================================= *)

(** The cores this bound is about: the fixed environment, and a file
    whose PAYLOAD extends [bs] — the file itself is [hdr ++ bs ++ ext].
    It is [in_file_cylinder] over [hdr ++ bs], and
    [in_file_prefix_cylinder_iff] says so. *)
Definition in_file_prefix_cylinder (hdr : list byte)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : list byte) (bs : list byte) (c : FinCore) : Prop :=
  exists ext, c = file_prefix_core hdr argv envp fs0 pth s (bs ++ ext).

Lemma in_file_prefix_cylinder_iff : forall hdr argv envp fs0 pth s bs c,
  in_file_prefix_cylinder hdr argv envp fs0 pth s bs c
  <-> in_file_cylinder argv envp fs0 pth s (hdr ++ bs) c.
Proof.
  intros hdr argv envp fs0 pth s bs c.
  unfold in_file_prefix_cylinder, in_file_cylinder, file_prefix_core.
  split; intros [ext Hext]; exists ext; rewrite Hext.
  - rewrite List.app_assoc. reflexivity.
  - rewrite <- List.app_assoc. reflexivity.
Qed.

(** The depth to enumerate PAYLOADS to: the longest file in the list,
    less the header.  [cores_file_depth_ge] shifted by [length hdr]. *)
Definition cores_file_prefix_depth (hdr : list byte) (pth : Fs.path)
    (cs : list FinCore) : nat :=
  (cores_file_depth pth cs - length hdr)%nat.

Lemma cores_file_prefix_depth_ge : forall hdr pth cs c t,
  List.In c cs ->
  fs_file pth (core_fs c) = hdr ++ t ->
  (length t <= cores_file_prefix_depth hdr pth cs)%nat.
Proof.
  intros hdr pth cs c t Hc Ht. unfold cores_file_prefix_depth.
  assert (Hd := cores_file_depth_ge pth cs c Hc).
  rewrite Ht, List.length_app in Hd. lia.
Qed.

(** THE BOUND OVER CORES, [file_geo_weight_cylinder_bound]'s shape: the
    enumeration is [bytes_cyl] over payloads mapped through the shifted
    embedding, and [bytes_cyl_sum_le] bounds it unchanged. *)
Lemma file_prefix_geo_weight_cylinder_bound : forall hdr p argv envp fs0 pth s,
  (0 <= p)%Q -> (p <= 1)%Q ->
  forall bs cs,
    List.NoDup cs ->
    (forall c, List.In c cs ->
       in_file_prefix_cylinder hdr argv envp fs0 pth s bs c) ->
    (qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s) cs
       <= geo_mass p (length bs))%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 bs cs Hnd Hcyl.
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (List.map (file_prefix_core hdr argv envp fs0 pth s)
                  (bytes_cyl bs (cores_file_prefix_depth hdr pth cs))))
    | rewrite qsum_file_prefix_block;
      apply bytes_cyl_sum_le; assumption ].
  - apply file_prefix_geo_weight_nonneg; assumption.
  - exact Hnd.
  - intros c Hc. destruct (Hcyl c Hc) as [ext Hext].
    assert (Hd := cores_file_prefix_depth_ge hdr pth cs c (bs ++ ext) Hc).
    rewrite Hext, fs_file_file_prefix_core in Hd.
    specialize (Hd eq_refl). rewrite List.length_app in Hd.
    rewrite Hext. apply List.in_map. apply bytes_cyl_In. lia.
Qed.

(* =========================================================================
   The exports
   ========================================================================= *)

(** The payload cylinder's mass is the whole-file family's number at the
    same PAYLOAD prefix: the header costs nothing, which is what
    conditioning on it means. *)
Definition file_geometric_prefix_cylinder_mass (p : Q) (bs : list byte) : Q :=
  file_geometric_cylinder_mass p bs.

Lemma file_geometric_prefix_cylinder_mass_closed_form : forall p bs,
  (file_geometric_prefix_cylinder_mass p bs
     == Qpow (1 - p) (length bs) * Qpow (1 # 256) (length bs))%Q.
Proof. intros p bs. apply file_geometric_cylinder_mass_closed_form. Qed.

(** THE EXPORT: a list of records with duplicate-free cores, all lying
    in the cylinder over a payload prefix [bs] behind the header, weighs
    at most that cylinder's mass.  A fire set described by "after the
    header, the input begins with these bytes" is charged a number that
    does not pay for the header. *)
Lemma file_geometric_prefix_bound :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)) ->
  (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
     <= file_geometric_prefix_cylinder_mass p bs)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 bs l Hnd Hcyl.
  cbn [cd_weight file_geometric_prefix]. rewrite core_sum_map_fin_core.
  unfold file_geometric_prefix_cylinder_mass, file_geometric_cylinder_mass.
  apply file_prefix_geo_weight_cylinder_bound;
    [exact Hp0 | exact Hp1 | exact Hnd |].
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. apply Hcyl. exact Hin.
Qed.

(** The membership tests as booleans.  The environment half is
    [matches_file_env] unchanged; the header half asks whether the file
    strips. *)
Definition matches_file_header (hdr : list byte) (pth : Fs.path)
    (c : FinCore) : bool :=
  match strip_prefix hdr (fs_file pth (core_fs c)) with
  | Some _ => true
  | None => false
  end.

Definition matches_file_prefix_env (hdr : list byte)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : list byte) (c : FinCore) : bool :=
  matches_file_env argv envp fs0 pth s c && matches_file_header hdr pth c.

Lemma matches_file_prefix_env_false : forall hdr argv envp fs0 pth s c,
  matches_file_prefix_env hdr argv envp fs0 pth s c = false ->
  c <> file_core argv envp fs0 pth s (fs_file pth (core_fs c))
  \/ strip_prefix hdr (fs_file pth (core_fs c)) = None.
Proof.
  intros hdr argv envp fs0 pth s c H. unfold matches_file_prefix_env in H.
  apply Bool.andb_false_iff in H as [H | H].
  - left. apply matches_file_env_false. exact H.
  - right. unfold matches_file_header in H.
    destruct (strip_prefix hdr (fs_file pth (core_fs c)));
      [discriminate H | reflexivity].
Qed.

Lemma file_prefix_geo_weight_unmatched : forall hdr p argv envp fs0 pth s c,
  matches_file_prefix_env hdr argv envp fs0 pth s c = false ->
  file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros hdr p argv envp fs0 pth s c H.
  destruct (matches_file_prefix_env_false hdr argv envp fs0 pth s c H)
    as [Hne | Hn].
  - apply file_prefix_geo_weight_mismatch. exact Hne.
  - apply file_prefix_geo_weight_off_header. exact Hn.
Qed.

Lemma matches_file_prefix_env_true : forall hdr argv envp fs0 pth s c,
  matches_file_prefix_env hdr argv envp fs0 pth s c = true ->
  exists t, c = file_prefix_core hdr argv envp fs0 pth s t.
Proof.
  intros hdr argv envp fs0 pth s c H. unfold matches_file_prefix_env in H.
  apply Bool.andb_true_iff in H as [Henv Hh].
  apply matches_file_env_true in Henv.
  unfold matches_file_header in Hh.
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |] eqn:Hs;
    [| discriminate Hh].
  exists t. unfold file_prefix_core.
  rewrite <- (strip_prefix_Some hdr _ t Hs). exact Henv.
Qed.

(** THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE: each record is
    in the cylinder OR weighs nothing — off the environment, or its file
    misses the header. *)
Lemma file_geometric_prefix_bound_or_off_environment :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)
     \/ matches_file_prefix_env hdr argv envp fs0 pth s (fin_core f) = false) ->
  (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
     <= file_geometric_prefix_cylinder_mass p bs)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 bs l Hnd Hor.
  cbn [cd_weight file_geometric_prefix]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_file_prefix_env hdr argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_prefix_geo_weight_unmatched hdr p argv envp fs0 pth s c Hc);
        reflexivity).
  unfold file_geometric_prefix_cylinder_mass, file_geometric_cylinder_mass.
  apply file_prefix_geo_weight_cylinder_bound; [exact Hp0 | exact Hp1 | |].
  - apply List.NoDup_filter. exact Hnd.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (Hor f Hinl) as [Hcyl | Hoff].
    + rewrite <- Hf. exact Hcyl.
    + rewrite Hf in Hoff. rewrite Hoff in Hm. discriminate Hm.
Qed.

(** UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass [1].  The disjunction is exhaustive at the empty payload prefix:
    a core either matches environment and header, and then its payload
    is [[] ++ itself], or it weighs nothing. *)
Lemma file_geometric_prefix_mass_upper :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
     <= cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1))%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 l Hnd.
  cbn [cd_mass file_geometric_prefix].
  change 1%Q with (file_geometric_prefix_cylinder_mass p []).
  apply file_geometric_prefix_bound_or_off_environment; [exact Hnd |].
  intros f Hf.
  destruct (matches_file_prefix_env hdr argv envp fs0 pth s (fin_core f))
    eqn:Hm.
  - left.
    destruct (matches_file_prefix_env_true hdr argv envp fs0 pth s
                (fin_core f) Hm) as [t Ht].
    exists t. cbn [List.app]. exact Ht.
  - right. reflexivity.
Qed.

(* =========================================================================
   The counting lemma and the payload-length slice
   ========================================================================= *)

(** A list of records with duplicate-free cores, every core the shifted
    template at a payload of length exactly [n], has at most [256 ^ n]
    elements: the payload determines the core ([file_prefix_core_inj],
    containment direction), and [byte_lists n] enumerates payloads. *)
Lemma injective_core_list_in_file_prefix_cylinder_length_bound :
  forall (hdr : list byte) (argv envp : list (list byte)) (fs0 : Fs.Fs)
         (pth : Fs.path) (s : list byte) (n : nat) (l : list FinProcInput),
    List.NoDup (List.map fin_core l) ->
    (forall f, List.In f l ->
       exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
                 /\ length t = n) ->
    (length l <= 256 ^ n)%nat.
Proof.
  intros hdr argv envp fs0 pth s n l Hnd Hall.
  assert (Hle : (length (List.map fin_core l)
                 <= length (List.map (file_prefix_core hdr argv envp fs0 pth s)
                              (byte_lists n)))%nat).
  { apply List.NoDup_incl_length; [exact Hnd |].
    intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
    destruct (Hall f Hin) as [t [Ht Hlen]].
    apply List.in_map_iff. exists t. split.
    - rewrite <- Ht. exact Hf.
    - rewrite <- Hlen. apply byte_lists_complete. }
  rewrite !List.length_map, byte_lists_length in Hle. exact Hle.
Qed.

(** ... attained at every [n], where [file_prefix_core_inj] is spent. *)
Lemma injective_core_list_in_file_prefix_cylinder_length_bound_attained :
  forall (hdr : list byte) (argv envp : list (list byte)) (fs0 : Fs.Fs)
         (pth : Fs.path) (s : list byte) (n : nat),
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (forall f, List.In f l ->
          exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
                    /\ length t = n)
    /\ length l = (256 ^ n)%nat.
Proof.
  intros hdr argv envp fs0 pth s n.
  exists (List.map
            (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
            (byte_lists n)).
  split; [| split].
  - rewrite List.map_map.
    rewrite (List.map_ext _ (file_prefix_core hdr argv envp fs0 pth s))
      by (intros t; apply fin_core_core_input).
    apply NoDup_map_inj; [| apply byte_lists_nodup].
    intros x y _ _ Heq. exact (file_prefix_core_inj _ _ _ _ _ _ _ _ Heq).
  - intros f Hf. apply List.in_map_iff in Hf as [t [Ht Hin]]. subst f.
    exists t. rewrite fin_core_core_input.
    split; [reflexivity |]. apply byte_lists_In_length. exact Hin.
  - rewrite List.length_map, byte_lists_length. reflexivity.
Qed.

(** THE PAYLOAD-LENGTH SLICE: a list drawn from one payload-length slice
    weighs at most [p_stop * (1 - p_stop) ^ n], the same constant the
    whole-file family has at FILE length [n]. *)
Lemma file_geometric_prefix_slice_bound :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
               /\ length t = n) ->
  (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
     <= p * Qpow (1 - p) n)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 n l Hnd Hall.
  cbn [cd_weight file_geometric_prefix]. rewrite core_sum_map_fin_core.
  rewrite (qsum_const _ _ (geo_point p n)).
  2:{ intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
      destruct (Hall f Hin) as [t [Ht Hlen]].
      rewrite <- Hf, Ht, file_prefix_geo_weight_match, Hlen. reflexivity. }
  rewrite <- (geo_slice_total p n).
  apply Qmult_le_compat_r; [| apply geo_point_nonneg; assumption].
  apply Qnat_le. rewrite List.length_map.
  apply (injective_core_list_in_file_prefix_cylinder_length_bound
           hdr argv envp fs0 pth s n l); assumption.
Qed.

Lemma file_geometric_prefix_slice_bound_attained :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 n,
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (forall f, List.In f l ->
          exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
                    /\ length t = n)
    /\ (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s
                               Hp0 Hp1)) l
          == p * Qpow (1 - p) n)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 n.
  destruct (injective_core_list_in_file_prefix_cylinder_length_bound_attained
              hdr argv envp fs0 pth s n) as [l [Hnd [Hall Hlen]]].
  exists l. split; [exact Hnd | split; [exact Hall |]].
  cbn [cd_weight file_geometric_prefix]. rewrite core_sum_map_fin_core.
  rewrite (qsum_const _ _ (geo_point p n)).
  2:{ intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
      destruct (Hall f Hin) as [t [Ht Hlength]].
      rewrite <- Hf, Ht, file_prefix_geo_weight_match, Hlength. reflexivity. }
  rewrite List.length_map, Hlen. apply geo_slice_total.
Qed.

Lemma file_geometric_prefix_slice_bound_sharp :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 n K,
  (forall l, List.NoDup (List.map fin_core l) ->
     (forall f, List.In f l ->
        exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
                  /\ length t = n) ->
     (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s
                             Hp0 Hp1)) l
        <= K)%Q) ->
  (p * Qpow (1 - p) n <= K)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 n K Hbound.
  destruct (file_geometric_prefix_slice_bound_attained hdr p argv envp fs0 pth s
              Hp0 Hp1 n) as [l [Hnd [Hall Hsum]]].
  rewrite <- Hsum. apply Hbound; assumption.
Qed.


(* =========================================================================
   The slice, stated on the FILE's length
   ========================================================================= *)

(** The counting lemma on CORES rather than records: a duplicate-free
    list of cores, each the shifted template at a payload of length [n],
    has at most [256 ^ n] members.  It is the record-level lemma above
    with [List.map fin_core] already applied, and it exists because the
    wider slice statement below counts a FILTERED list of cores, which
    has no record list behind it. *)
Lemma file_prefix_core_list_length_bound :
  forall hdr argv envp fs0 pth s n (cs : list FinCore),
    List.NoDup cs ->
    (forall c, List.In c cs ->
       exists t, c = file_prefix_core hdr argv envp fs0 pth s t
                 /\ length t = n) ->
    (length cs <= 256 ^ n)%nat.
Proof.
  intros hdr argv envp fs0 pth s n cs Hnd Hall.
  assert (Hle : (length cs
                 <= length (List.map (file_prefix_core hdr argv envp fs0 pth s)
                              (byte_lists n)))%nat).
  { apply List.NoDup_incl_length; [exact Hnd |].
    intros c Hc. destruct (Hall c Hc) as [t [Ht Hlen]].
    apply List.in_map_iff. exists t. split; [symmetry; exact Ht |].
    rewrite <- Hlen. apply byte_lists_complete. }
  rewrite List.length_map, byte_lists_length in Hle. exact Hle.
Qed.

(** A record whose core is the shifted template at [t] and whose file
    has length [length hdr + n] has a payload of length [n]: the shift,
    done once. *)
Lemma file_prefix_payload_length :
  forall hdr argv envp fs0 pth s (f : FinProcInput) t n,
  fin_core f = file_prefix_core hdr argv envp fs0 pth s t ->
  length (fs_file pth (fin_image_fs f)) = (length hdr + n)%nat ->
  length t = n.
Proof.
  intros hdr argv envp fs0 pth s f t n Hf Hlen.
  apply (f_equal (fun c => length (fs_file pth (core_fs c)))) in Hf.
  cbn [fin_core core_fs] in Hf.
  rewrite fs_file_file_prefix_core, List.length_app in Hf. lia.
Qed.

(** THE WIDER SLICE STATEMENT, in the whole-file family's shape: every
    record matches the environment and carries a FILE of length
    [length hdr + n], with NO premise that the file starts with the
    header.  It holds because a core whose file has the right length but
    the wrong header weighs zero, so filtering it out changes nothing —
    the same filter [file_geometric_prefix_bound_by_max_length] uses.
    The payload-shaped statement above stays; a task with a header in
    hand uses that one, a task that only knows its files' lengths uses
    this one. *)
Lemma file_geometric_prefix_slice_bound_by_file_length :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = file_core argv envp fs0 pth s (fs_file pth (fin_image_fs f))
     /\ length (fs_file pth (fin_image_fs f)) = (length hdr + n)%nat) ->
  (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
     <= p * Qpow (1 - p) n)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 n l Hnd Hall.
  cbn [cd_weight file_geometric_prefix]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_file_prefix_env hdr argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_prefix_geo_weight_unmatched hdr p argv envp fs0 pth s c Hc);
        reflexivity).
  assert (Hslice : forall c,
            List.In c (List.filter (matches_file_prefix_env hdr argv envp fs0 pth s)
                         (List.map fin_core l)) ->
            exists t, c = file_prefix_core hdr argv envp fs0 pth s t
                      /\ length t = n).
  { intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (matches_file_prefix_env_true hdr argv envp fs0 pth s c Hm)
      as [t Ht].
    exists t. split; [exact Ht |].
    apply (file_prefix_payload_length hdr argv envp fs0 pth s f t n);
      [rewrite Hf; exact Ht | exact (proj2 (Hall f Hinl))]. }
  rewrite (qsum_const _ _ (geo_point p n)).
  2:{ intros c Hc. destruct (Hslice c Hc) as [t [Ht Hlen]].
      rewrite Ht, file_prefix_geo_weight_match, Hlen. reflexivity. }
  rewrite <- (geo_slice_total p n).
  apply Qmult_le_compat_r; [| apply geo_point_nonneg; assumption].
  apply Qnat_le.
  apply (file_prefix_core_list_length_bound hdr argv envp fs0 pth s n).
  - apply List.NoDup_filter. exact Hnd.
  - exact Hslice.
Qed.
(* =========================================================================
   The lower certificate for [file_geometric_prefix]
   ========================================================================= *)

(** THE WITNESS FAMILY: one record per PAYLOAD shorter than [k], behind
    the header.  [short_inputs] is reused; only the embedding is this
    family's. *)
Definition file_prefix_geo_lower_witness (hdr : list byte)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : list byte) (k : nat) : list FinProcInput :=
  List.map (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
    (short_inputs k).

Lemma map_fin_core_file_prefix_geo_lower_witness :
  forall hdr argv envp fs0 pth s k,
  List.map fin_core (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k)
    = List.map (file_prefix_core hdr argv envp fs0 pth s) (short_inputs k).
Proof.
  intros hdr argv envp fs0 pth s k. unfold file_prefix_geo_lower_witness.
  rewrite List.map_map. apply List.map_ext. intros t.
  apply fin_core_core_input.
Qed.

Lemma file_prefix_geo_lower_witness_nodup : forall hdr argv envp fs0 pth s k,
  List.NoDup
    (List.map fin_core (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k)).
Proof.
  intros hdr argv envp fs0 pth s k.
  rewrite map_fin_core_file_prefix_geo_lower_witness.
  apply NoDup_map_inj; [| apply short_inputs_nodup].
  intros x y _ _ Heq. exact (file_prefix_core_inj _ _ _ _ _ _ _ _ Heq).
Qed.

Lemma qsum_file_prefix_short_inputs : forall hdr p argv envp fs0 pth s k,
  (qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s)
     (List.map (file_prefix_core hdr argv envp fs0 pth s) (short_inputs k))
     == geo_prefix_sum p k)%Q.
Proof.
  intros hdr p argv envp fs0 pth s k.
  rewrite qsum_file_prefix_block. apply short_inputs_sum.
Qed.

Lemma file_geometric_prefix_mass_lower_witness :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 k,
  List.NoDup
    (List.map fin_core (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k))
  /\ (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s
                             Hp0 Hp1))
        (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k)
        == 1 - Qpow (1 - p) k)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 k.
  split; [apply file_prefix_geo_lower_witness_nodup |].
  cbn [cd_weight file_geometric_prefix].
  rewrite core_sum_map_fin_core, map_fin_core_file_prefix_geo_lower_witness.
  rewrite qsum_file_prefix_short_inputs. apply geo_prefix_sum_closed.
Qed.

Lemma file_geometric_prefix_mass_lower_prefix :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 k,
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s
                               Hp0 Hp1)) l
          == 1 - Qpow (1 - p) k)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 k.
  exists (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k).
  apply file_geometric_prefix_mass_lower_witness.
Qed.

(** THE LOWER CERTIFICATE, with [0 < p_stop] spent in [geo_gap_small]
    and nowhere else, exactly as for the whole-file family. *)
Lemma file_geometric_prefix_mass_lower_certificate :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 eps,
  (0 < p)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) - eps
          <= core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s
                                    Hp0 Hp1)) l)%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 eps Hpos Heps.
  destruct (geo_gap_small p eps Hpos Hp1 Heps) as [k Hk].
  destruct (file_geometric_prefix_mass_lower_prefix hdr p argv envp fs0 pth s
              Hp0 Hp1 k) as [l [Hnd Hsum]].
  exists l. split; [exact Hnd |].
  rewrite Hsum. cbn [cd_mass file_geometric_prefix].
  apply (proj2 (Qle_minus_iff (1 - eps) (1 - Qpow (1 - p) k))).
  apply (Qle_trans _ (eps + - Qpow (1 - p) k)%Q);
    [ apply (proj1 (Qle_minus_iff (Qpow (1 - p) k) eps)); exact Hk
    | apply Qle_of_Qeq; ring].
Qed.

(* =========================================================================
   ... and this mass is a SUPREMUM and not a maximum
   ========================================================================= *)

(** A list confined to files of length at most [length hdr + n] — payloads
    of length at most [n] — weighs at most the partial sum at that
    horizon.  The hypothesis is on the FILE's length, which is what a
    task has; the shift by the header is done here. *)
Lemma file_geometric_prefix_bound_by_max_length :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     (length (fs_file pth (fin_image_fs f)) <= length hdr + n)%nat) ->
  (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1)) l
     <= 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 n l Hnd Hlen.
  cbn [cd_weight file_geometric_prefix]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_file_prefix_env hdr argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_prefix_geo_weight_unmatched hdr p argv envp fs0 pth s c Hc);
        reflexivity).
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (List.map (file_prefix_core hdr argv envp fs0 pth s)
                  (short_inputs (S n))))
    | rewrite qsum_file_prefix_short_inputs, geo_prefix_sum_closed;
      apply Qle_refl ].
  - apply file_prefix_geo_weight_nonneg; assumption.
  - apply List.NoDup_filter. exact Hnd.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (matches_file_prefix_env_true hdr argv envp fs0 pth s c Hm)
      as [t Ht].
    apply List.in_map_iff. exists t. split; [symmetry; exact Ht |].
    apply short_inputs_complete.
    assert (Hle := Hlen f Hinl).
    assert (Hc' : fs_file pth (core_fs c) = hdr ++ t)
      by (rewrite Ht; apply fs_file_file_prefix_core).
    rewrite <- Hf in Hc'. cbn [fin_core core_fs] in Hc'.
    rewrite Hc', List.length_app in Hle. lia.
Qed.

Lemma file_geometric_prefix_bound_by_max_length_attained :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 n,
  (forall f,
     List.In f (file_prefix_geo_lower_witness hdr argv envp fs0 pth s (S n)) ->
     (length (fs_file pth (fin_image_fs f)) <= length hdr + n)%nat)
  /\ (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s
                             Hp0 Hp1))
        (file_prefix_geo_lower_witness hdr argv envp fs0 pth s (S n))
        == 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 n. split.
  - intros f Hf. unfold file_prefix_geo_lower_witness in Hf.
    apply List.in_map_iff in Hf as [t [Ht Hin]]. subst f.
    cbn [core_input fin_image_fs].
    rewrite fs_file_file_prefix_core, List.length_app.
    apply short_inputs_In_length in Hin. lia.
  - apply file_geometric_prefix_mass_lower_witness.
Qed.

Lemma file_geometric_prefix_mass_not_attained :
  forall hdr p argv envp fs0 pth s Hp0 Hp1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s
                            Hp0 Hp1)) l
       < cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1))%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 Hlt l Hnd.
  cbn [cd_mass file_geometric_prefix].
  pose (n := List.list_max
               (List.map (fun f => length (fs_file pth (fin_image_fs f))) l)).
  apply (Qle_lt_trans _ (1 - Qpow (1 - p) (S n))%Q).
  - apply file_geometric_prefix_bound_by_max_length; [exact Hnd |].
    intros f Hf.
    enough (length (fs_file pth (fin_image_fs f)) <= n)%nat by lia.
    apply list_max_ge. apply List.in_map_iff.
    exists f. split; [reflexivity | exact Hf].
  - apply (proj2 (Qlt_minus_iff (1 - Qpow (1 - p) (S n)) 1)).
    apply (Qlt_le_trans _ (Qpow (1 - p) (S n))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qpow_pos. apply (Qlt_minus_iff p 1). exact Hlt.
Qed.

Lemma file_geometric_prefix_mass_supremum_not_maximum :
  forall hdr p argv envp fs0 pth s Hp0 Hp1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    ~ (core_sum (cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s
                              Hp0 Hp1)) l
         == cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1))%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 Hlt l Hnd.
  apply Qlt_not_eq.
  apply file_geometric_prefix_mass_not_attained; assumption.
Qed.

(* =========================================================================
   Non-vacuity: the header bites, and the payload really carries mass
   ========================================================================= *)

Lemma file_prefix_geo_weight_off_environment_zero :
  forall hdr p argv envp fs0 pth s c,
  core_argv c <> argv -> file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros hdr p argv envp fs0 pth s c Hne. apply file_prefix_geo_weight_mismatch.
  intros Heq. apply (f_equal core_argv) in Heq.
  cbn [file_core core_argv] in Heq. exact (Hne Heq).
Qed.

(** THE HEADER BITES, in general: a core whose file does not start with
    the header weighs zero, and the declared mass is still [1].  Both
    conjuncts are the spec of record's; the second is what makes the
    first a statement about a normalised family rather than about a
    family that was quietly scaled down. *)
Lemma file_geometric_prefix_off_header_zero :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 c,
  (forall t, fs_file pth (core_fs c) <> hdr ++ t) ->
  cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) c = 0%Q
  /\ cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) = 1%Q.
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 c Hno. split; [| reflexivity].
  cbn [cd_weight file_geometric_prefix].
  apply file_prefix_geo_weight_off_header_zero. exact Hno.
Qed.

(** A one-byte header, and the core over the empty environment whose
    file is exactly that header.  [file_example_core]'s file is empty,
    so it does NOT start with the header. *)
Definition file_example_hdr : list byte := [Z_to_bv 8 104].

Definition file_example_hdr_core : FinCore :=
  file_core [] [] [] file_example_path [] file_example_hdr.

(** THE HEADER BITES, exhibited, all on cores the whole-file family
    treats alike.  The empty-file core — the very one
    [file_geometric_fs_bites] shows [file_geometric] weighing positively
    — weighs ZERO here, the exact-header core weighs positively, the
    declared mass is [1], and the whole-file family's positive weight on
    the first core is restated beside it so that the difference is
    visibly the header and nothing else. *)
Lemma file_geometric_prefix_header_bites : forall p Hp0 Hp1,
  (0 < p)%Q ->
  cd_weight (file_geometric_prefix file_example_hdr p [] [] []
               file_example_path [] Hp0 Hp1) file_example_core = 0%Q
  /\ (0 < cd_weight (file_geometric_prefix file_example_hdr p [] [] []
                       file_example_path [] Hp0 Hp1) file_example_hdr_core)%Q
  /\ cd_mass (file_geometric_prefix file_example_hdr p [] [] []
                file_example_path [] Hp0 Hp1) = 1%Q
  /\ (0 < cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
            file_example_core)%Q.
Proof.
  intros p Hp0 Hp1 Hlt. split; [| split; [| split]].
  - cbn [cd_weight file_geometric_prefix].
    apply file_prefix_geo_weight_off_header.
    unfold file_example_core. rewrite fs_file_file_core. reflexivity.
  - cbn [cd_weight file_geometric_prefix].
    change file_example_hdr_core
      with (file_prefix_core file_example_hdr [] [] [] file_example_path [] []).
    rewrite file_prefix_geo_weight_match.
    unfold geo_point, geo_mass. cbn [length Qpow].
    rewrite Qmult_1_r. exact Hlt.
  - reflexivity.
  - apply (file_geometric_fs_bites p Hp0 Hp1 Hlt).
Qed.

(** ... and the family is not a constant either: positive on the
    exact-header core, zero off the fixed argv. *)
Lemma file_geometric_prefix_bites : forall p Hp0 Hp1,
  (0 < p)%Q ->
  (0 < cd_weight (file_geometric_prefix file_example_hdr p [] [] []
                    file_example_path [] Hp0 Hp1) file_example_hdr_core)%Q
  /\ cd_weight (file_geometric_prefix file_example_hdr p [] [] []
                  file_example_path [] Hp0 Hp1) geo_example_other = 0%Q.
Proof.
  intros p Hp0 Hp1 Hlt. split.
  - apply (file_geometric_prefix_header_bites p Hp0 Hp1 Hlt).
  - cbn [cd_weight file_geometric_prefix].
    apply file_prefix_geo_weight_off_environment_zero.
    unfold geo_example_other. cbn [core_argv]. discriminate.
Qed.

(* =========================================================================
   Non-vacuity: the mass is reached at [p_stop = 1], and [List.NoDup] is
   load-bearing
   ========================================================================= *)

(** The member at [p_stop = 1]: the point mass on the EXACT-HEADER file.
    Closed arithmetic, decided by computation; [strip_prefix] is a
    [Fixpoint] so that it is. *)
Definition file_prefix_point_cd : CoreDistribution :=
  file_geometric_prefix file_example_hdr 1 [] [] [] file_example_path []
    Qle_0_1 (Qle_refl 1).

Definition file_hdr_input : FinProcInput := core_input file_example_hdr_core.

Lemma file_prefix_point_cd_mass_attained :
  List.NoDup (List.map fin_core [file_hdr_input])
  /\ (core_sum (cd_weight file_prefix_point_cd) [file_hdr_input]
        == cd_mass file_prefix_point_cd)%Q.
Proof.
  split.
  - cbn [List.map].
    apply List.NoDup_cons; [intros H; exact H | apply List.NoDup_nil].
  - vm_compute. reflexivity.
Qed.

Lemma file_geometric_prefix_bound_needs_nodup :
  ~ List.NoDup (List.map fin_core [file_hdr_input; file_hdr_input])
  /\ (forall f, List.In f [file_hdr_input; file_hdr_input] ->
        in_file_prefix_cylinder file_example_hdr [] [] [] file_example_path []
          [] (fin_core f))
  /\ ~ (core_sum (cd_weight file_prefix_point_cd)
          [file_hdr_input; file_hdr_input]
          <= file_geometric_prefix_cylinder_mass 1 [])%Q.
Proof.
  split; [| split].
  - intros Hnd. cbn [List.map] in Hnd.
    apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd as [Hnin _].
    apply Hnin. left. reflexivity.
  - intros f Hf. destruct Hf as [Hf | [Hf | []]]; subst f;
      exists []; reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate Hle.
Qed.

(* =========================================================================
   The two degenerate endpoints, both pinned
   ========================================================================= *)

(** At [p_stop = 0] the weight vanishes identically; at [p_stop = 1]
    every core whose file is not EXACTLY the header weighs zero — a
    longer payload by the geometric collapse, a file missing the header
    by the header's own bite — while the exact-header core keeps its
    weight.  The family goes blind to the payload without going quiet,
    which is the failure mode that would go unnoticed. *)
Lemma file_prefix_geo_weight_zero_at_zero_p : forall hdr argv envp fs0 pth s c,
  (file_prefix_geo_weight hdr 0 argv envp fs0 pth s c == 0)%Q.
Proof.
  intros hdr argv envp fs0 pth s c. unfold file_prefix_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |];
    [| reflexivity].
  unfold geo_point. ring.
Qed.

Lemma file_geometric_prefix_mass_lower_needs_positive :
  forall hdr argv envp fs0 pth s,
  (forall l : list FinProcInput,
     (core_sum (cd_weight (file_geometric_prefix hdr 0 argv envp fs0 pth s
                             (Qle_refl 0) Qle_0_1)) l == 0)%Q)
  /\ ~ (cd_mass (file_geometric_prefix hdr 0 argv envp fs0 pth s
                   (Qle_refl 0) Qle_0_1)
          - (1 # 2) <= 0)%Q.
Proof.
  intros hdr argv envp fs0 pth s. split.
  - intros l. apply core_sum_zero_weight. intros c.
    cbn [cd_weight file_geometric_prefix].
    apply file_prefix_geo_weight_zero_at_zero_p.
  - cbn [cd_mass file_geometric_prefix]. intros Hle.
    apply (proj2 (Qle_bool_iff _ _)) in Hle. vm_compute in Hle.
    discriminate Hle.
Qed.

Lemma file_prefix_geo_weight_collapses_at_one_p :
  forall hdr argv envp fs0 pth s c,
  fs_file pth (core_fs c) <> hdr ->
  (file_prefix_geo_weight hdr 1 argv envp fs0 pth s c == 0)%Q.
Proof.
  intros hdr argv envp fs0 pth s c Hne. unfold file_prefix_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |] eqn:Hs;
    [| reflexivity].
  apply strip_prefix_Some in Hs.
  destruct t as [| b t].
  - exfalso. apply Hne. rewrite Hs. apply List.app_nil_r.
  - unfold geo_point, geo_mass. cbn [length Qpow]. ring.
Qed.

Lemma file_geometric_prefix_needs_p_below_one :
  forall hdr argv envp fs0 pth s c,
  fs_file pth (core_fs c) <> hdr ->
  (cd_weight (file_geometric_prefix hdr 1 argv envp fs0 pth s
                Qle_0_1 (Qle_refl 1)) c
     == 0)%Q.
Proof.
  intros hdr argv envp fs0 pth s c Hne. cbn [cd_weight file_geometric_prefix].
  apply file_prefix_geo_weight_collapses_at_one_p. exact Hne.
Qed.

(* =========================================================================
   Byte lists over a fixed ALPHABET, and the geometric arithmetic over it
   ========================================================================= *)

(** THE ALPHABET-RESTRICTED FAMILY [file_geometric_prefix_over] below
    spreads the payload's bytes i.i.d. UNIFORMLY OVER A FIXED SUBSET
    [alpha] of the bytes rather than over all of them: a text-consuming
    program wants printable input, and under the 256-byte law almost
    every payload holds a control byte.  Everything the 256-byte
    families count and sum — [byte_lists], [short_inputs], [bytes_cyl],
    [geo_mass] — is [all_bytes] or [1 # 256] applied to a shape that
    never depended on which bytes they were.  So that shape is stated
    here ONCE over an alphabet, with hypotheses where the 256-byte
    enumeration had facts: the alphabet is duplicate-free
    (what [all_bytes_nodup] gave) and non-empty (what [all_bytes_length]
    gave, in the only way the arithmetic spends it: the per-byte ratio
    cancels against the count).  Completeness is not a hypothesis — an
    alphabet is not asked to be all the bytes — and turns into a
    PREDICATE on payloads, [alpha_only], which the weight tests.

    The 256-byte objects are the instance at [alpha = all_bytes], and
    that is proved rather than said ([alpha_lists_all_bytes],
    [alpha_short_inputs_all_bytes], [alpha_cyl_all_bytes],
    [alpha_geo_mass_all_bytes]).  Nothing above this section changes:
    the existing statements are byte-identical, and the existing sums
    stay proved the way they were.  What is generalised is written
    beside them, and the instance lemmas are what tie the two. *)

(** Membership in the alphabet, as a boolean, and "every byte of [t] is
    in the alphabet". *)
Definition alpha_memb (alpha : list byte) (b : byte) : bool :=
  List.existsb (fun a => if decide (a = b) then true else false) alpha.

Lemma alpha_memb_In : forall alpha b,
  alpha_memb alpha b = true <-> List.In b alpha.
Proof.
  intros alpha b. unfold alpha_memb. rewrite List.existsb_exists. split.
  - intros [a [Ha Hab]].
    destruct (decide (a = b)) as [<- | _]; [exact Ha | discriminate Hab].
  - intros Hb. exists b. split; [exact Hb |].
    destruct (decide (b = b)) as [_ | Hne];
      [reflexivity | exfalso; apply Hne; reflexivity].
Qed.

Definition alpha_only (alpha t : list byte) : bool :=
  List.forallb (alpha_memb alpha) t.

Lemma alpha_only_In : forall alpha t,
  alpha_only alpha t = true <-> (forall b, List.In b t -> List.In b alpha).
Proof.
  intros alpha t. unfold alpha_only. rewrite List.forallb_forall.
  split; intros H b Hb; apply alpha_memb_In; apply H; exact Hb.
Qed.

Lemma alpha_only_app : forall alpha t1 t2,
  alpha_only alpha (t1 ++ t2) = (alpha_only alpha t1 && alpha_only alpha t2)%bool.
Proof. intros alpha t1 t2. unfold alpha_only. apply List.forallb_app. Qed.

(** Every payload is over the full alphabet: the predicate is
    [all_bytes_complete] read as a boolean. *)
Lemma alpha_only_all_bytes : forall t, alpha_only all_bytes t = true.
Proof.
  intros t. apply alpha_only_In. intros b _. apply all_bytes_complete.
Qed.

Lemma all_bytes_ne : all_bytes <> [].
Proof.
  intros H. apply (f_equal (@length byte)) in H.
  rewrite all_bytes_length in H. discriminate H.
Qed.

(** The per-byte ratio: one over the alphabet's size.  [Qinv] of a
    [Qnat] rather than a [Qmake] with a [positive] denominator, so that
    the size is the list's own [length] and the cancellation below is
    [Qmult_inv_r] under "non-empty". *)
Definition alpha_ratio (alpha : list byte) : Q := (/ Qnat (length alpha))%Q.

Lemma alpha_ratio_nonneg : forall alpha, (0 <= alpha_ratio alpha)%Q.
Proof. intros alpha. apply Qinv_le_0_compat. apply Qnat_nonneg. Qed.

Lemma Qnat_length_pos : forall (alpha : list byte),
  alpha <> [] -> (0 < Qnat (length alpha))%Q.
Proof.
  intros alpha Hne. destruct alpha as [| a alpha]; [exfalso; apply Hne; reflexivity |].
  cbn [length]. rewrite Qnat_succ.
  apply (Qlt_le_trans _ 1); [reflexivity |].
  apply (Qle_trans _ (1 + 0)); [apply Qle_of_Qeq; ring |].
  apply Qplus_le_r. apply Qnat_nonneg.
Qed.

Lemma alpha_ratio_pos : forall alpha, alpha <> [] -> (0 < alpha_ratio alpha)%Q.
Proof.
  intros alpha Hne. apply Qinv_lt_0_compat. apply Qnat_length_pos. exact Hne.
Qed.

Lemma alpha_ratio_cancel : forall alpha,
  alpha <> [] -> (Qnat (length alpha) * alpha_ratio alpha == 1)%Q.
Proof.
  intros alpha Hne. unfold alpha_ratio. apply Qmult_inv_r.
  intros H. apply (Qlt_not_eq _ _ (Qnat_length_pos alpha Hne)).
  symmetry. exact H.
Qed.

Lemma alpha_ratio_all_bytes : (alpha_ratio all_bytes == 1 # 256)%Q.
Proof. unfold alpha_ratio. rewrite all_bytes_length. reflexivity. Qed.

(** The mass of a payload cylinder and the weight of one payload, over
    the alphabet: powers of ONE ratio, [(1 - p_stop) * alpha_ratio],
    exactly as [geo_mass] is powers of [(1 - p_stop) * (1 # 256)]. *)
Definition alpha_geo_mass (alpha : list byte) (p : Q) (n : nat) : Q :=
  Qpow ((1 - p) * alpha_ratio alpha) n.

Definition alpha_geo_point (alpha : list byte) (p : Q) (n : nat) : Q :=
  (p * alpha_geo_mass alpha p n)%Q.

Lemma alpha_geo_mass_closed_form : forall alpha p n,
  (alpha_geo_mass alpha p n == Qpow (1 - p) n * Qpow (alpha_ratio alpha) n)%Q.
Proof. intros alpha p n. apply Qpow_mult. Qed.

Lemma alpha_geo_point_closed_form : forall alpha p n,
  (alpha_geo_point alpha p n
     == p * Qpow (1 - p) n * Qpow (alpha_ratio alpha) n)%Q.
Proof.
  intros alpha p n. unfold alpha_geo_point. rewrite alpha_geo_mass_closed_form.
  ring.
Qed.

Lemma alpha_geo_ratio_nonneg : forall alpha p,
  (p <= 1)%Q -> (0 <= (1 - p) * alpha_ratio alpha)%Q.
Proof.
  intros alpha p Hp1. apply Qmult_le_0_compat; [| apply alpha_ratio_nonneg].
  apply (Qle_minus_iff p 1). exact Hp1.
Qed.

Lemma alpha_geo_mass_nonneg : forall alpha p n,
  (p <= 1)%Q -> (0 <= alpha_geo_mass alpha p n)%Q.
Proof.
  intros alpha p n Hp1. apply Qpow_nonneg, alpha_geo_ratio_nonneg, Hp1.
Qed.

Lemma alpha_geo_point_nonneg : forall alpha p n,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= alpha_geo_point alpha p n)%Q.
Proof.
  intros alpha p n Hp0 Hp1. apply Qmult_le_0_compat; [exact Hp0 |].
  apply alpha_geo_mass_nonneg, Hp1.
Qed.

Lemma alpha_geo_point_le_mass : forall alpha p n,
  (p <= 1)%Q -> (alpha_geo_point alpha p n <= alpha_geo_mass alpha p n)%Q.
Proof.
  intros alpha p n Hp1. unfold alpha_geo_point.
  rewrite <- (Qmult_1_l (alpha_geo_mass alpha p n)) at 2.
  apply Qmult_le_compat_r; [exact Hp1 | apply alpha_geo_mass_nonneg, Hp1].
Qed.

Lemma alpha_geo_point_pos : forall alpha p n,
  (0 < p)%Q -> (p < 1)%Q -> alpha <> [] -> (0 < alpha_geo_point alpha p n)%Q.
Proof.
  intros alpha p n Hp0 Hp1 Hne. unfold alpha_geo_point.
  apply Qmult_lt_0_compat; [exact Hp0 |].
  unfold alpha_geo_mass. apply Qpow_pos.
  apply Qmult_lt_0_compat; [| apply alpha_ratio_pos; exact Hne].
  apply (Qlt_minus_iff p 1). exact Hp1.
Qed.

(** The instance at [all_bytes] is the 256-byte arithmetic. *)
Lemma alpha_geo_mass_all_bytes : forall p n,
  (alpha_geo_mass all_bytes p n == geo_mass p n)%Q.
Proof.
  intros p n. unfold alpha_geo_mass, geo_mass. apply Qpow_Qeq.
  rewrite alpha_ratio_all_bytes. reflexivity.
Qed.

Lemma alpha_geo_point_all_bytes : forall p n,
  (alpha_geo_point all_bytes p n == geo_point p n)%Q.
Proof.
  intros p n. unfold alpha_geo_point, geo_point.
  rewrite alpha_geo_mass_all_bytes. reflexivity.
Qed.

(** THE ENUMERATION of length-[n] lists over the alphabet, [byte_lists]
    with [alpha] in place of [all_bytes]. *)
Fixpoint alpha_lists (alpha : list byte) (n : nat) : list (list byte) :=
  match n with
  | O => [[]]
  | S n' => List.flat_map (fun b => List.map (cons b) (alpha_lists alpha n')) alpha
  end.

Lemma alpha_lists_all_bytes : forall n, alpha_lists all_bytes n = byte_lists n.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [alpha_lists byte_lists]. rewrite IH. reflexivity.
Qed.

Lemma alpha_lists_length : forall alpha n,
  length (alpha_lists alpha n) = (length alpha ^ n)%nat.
Proof.
  intros alpha. induction n as [| n IH]; [reflexivity |].
  cbn [alpha_lists].
  rewrite (length_flat_map_const _ _ _ _ (length alpha ^ n)%nat)
    by (intros b _; rewrite List.length_map; exact IH).
  reflexivity.
Qed.

Lemma alpha_lists_complete : forall alpha (l : list byte),
  alpha_only alpha l = true -> List.In l (alpha_lists alpha (length l)).
Proof.
  intros alpha l. induction l as [| b l IH]; intros Hl; [left; reflexivity |].
  unfold alpha_only in Hl. cbn [List.forallb] in Hl.
  apply Bool.andb_true_iff in Hl as [Hb Hl].
  cbn [length alpha_lists]. apply List.in_flat_map.
  exists b. split; [apply alpha_memb_In; exact Hb |].
  apply List.in_map. apply IH. exact Hl.
Qed.

Lemma alpha_lists_In_length : forall alpha n s,
  List.In s (alpha_lists alpha n) -> length s = n.
Proof.
  intros alpha n. induction n as [| n IH]; intros s Hs.
  - destruct Hs as [Hs | []]. rewrite <- Hs. reflexivity.
  - cbn [alpha_lists] in Hs. apply List.in_flat_map in Hs as [b [_ Hs]].
    apply List.in_map_iff in Hs as [s' [Hs' Hin]]. rewrite <- Hs'.
    cbn [length]. rewrite (IH s' Hin). reflexivity.
Qed.

Lemma alpha_lists_In_alpha : forall alpha n s,
  List.In s (alpha_lists alpha n) -> alpha_only alpha s = true.
Proof.
  intros alpha n. induction n as [| n IH]; intros s Hs.
  - destruct Hs as [Hs | []]. rewrite <- Hs. reflexivity.
  - cbn [alpha_lists] in Hs. apply List.in_flat_map in Hs as [b [Hb Hs]].
    apply List.in_map_iff in Hs as [s' [Hs' Hin]]. rewrite <- Hs'.
    unfold alpha_only. cbn [List.forallb]. apply Bool.andb_true_iff.
    split; [apply alpha_memb_In; exact Hb | apply IH; exact Hin].
Qed.

Lemma alpha_lists_nodup : forall alpha,
  List.NoDup alpha -> forall n, List.NoDup (alpha_lists alpha n).
Proof.
  intros alpha Hnd. induction n as [| n IH].
  - cbn [alpha_lists].
    apply List.NoDup_cons; [intros H; exact H | apply List.NoDup_nil].
  - cbn [alpha_lists]. apply NoDup_flat_map.
    + exact Hnd.
    + intros b _. apply NoDup_map_inj; [| exact IH].
      intros x y _ _ Heq. injection Heq as Heq. exact Heq.
    + intros x y bs _ _ Hx Hy.
      apply List.in_map_iff in Hx as [lx [Hlx _]].
      apply List.in_map_iff in Hy as [ly [Hly _]].
      rewrite <- Hly in Hlx. injection Hlx as Hxy _. exact Hxy.
Qed.

(** A full length-[n] slice over the alphabet weighs [p (1 - p) ^ n]:
    the size [length alpha ^ n] and the ratio's [n]th power cancel,
    which is where "non-empty" is spent. *)
Lemma Qnat_pow : forall m n, (Qnat (m ^ n) == Qpow (Qnat m) n)%Q.
Proof.
  intros m n. induction n as [| n IH]; [reflexivity |].
  cbn [Nat.pow]. rewrite Qnat_mult, Qpow_succ, IH. reflexivity.
Qed.

Lemma alpha_slice_total : forall alpha p n,
  alpha <> [] ->
  (Qnat (length alpha ^ n) * alpha_geo_point alpha p n == p * Qpow (1 - p) n)%Q.
Proof.
  intros alpha p n Hne.
  assert (H1 : (Qpow (Qnat (length alpha)) n * Qpow (alpha_ratio alpha) n == 1)%Q).
  { rewrite <- Qpow_mult.
    rewrite (Qpow_Qeq (Qnat (length alpha) * alpha_ratio alpha) 1 n)
      by (apply alpha_ratio_cancel; exact Hne).
    apply Qpow_1. }
  rewrite Qnat_pow. unfold alpha_geo_point, alpha_geo_mass. rewrite Qpow_mult.
  transitivity ((Qpow (Qnat (length alpha)) n * Qpow (alpha_ratio alpha) n)
                * (p * Qpow (1 - p) n))%Q; [ring |].
  rewrite H1. ring.
Qed.

Lemma alpha_lists_sum : forall alpha p n,
  alpha <> [] ->
  (qsum (fun s => alpha_geo_point alpha p (length s)) (alpha_lists alpha n)
     == p * Qpow (1 - p) n)%Q.
Proof.
  intros alpha p n Hne.
  rewrite (qsum_const _ _ (alpha_geo_point alpha p n))
    by (intros s Hs; rewrite (alpha_lists_In_length alpha n s Hs); reflexivity).
  rewrite alpha_lists_length. apply alpha_slice_total. exact Hne.
Qed.

(** The length-bounded prefix family over the alphabet, [short_inputs]
    with [alpha_lists] in place of [byte_lists]. *)
Fixpoint alpha_short_inputs (alpha : list byte) (k : nat) : list (list byte) :=
  match k with
  | O => []
  | S k' => alpha_lists alpha k' ++ alpha_short_inputs alpha k'
  end.

Lemma alpha_short_inputs_all_bytes : forall k,
  alpha_short_inputs all_bytes k = short_inputs k.
Proof.
  induction k as [| k IH]; [reflexivity |].
  cbn [alpha_short_inputs short_inputs]. rewrite IH, alpha_lists_all_bytes.
  reflexivity.
Qed.

Lemma alpha_short_inputs_In_length : forall alpha k s,
  List.In s (alpha_short_inputs alpha k) -> (length s < k)%nat.
Proof.
  intros alpha k. induction k as [| k IH]; intros s Hs; [destruct Hs |].
  cbn [alpha_short_inputs] in Hs. apply List.in_app_or in Hs as [Hs | Hs].
  - rewrite (alpha_lists_In_length alpha k s Hs). lia.
  - apply IH in Hs. lia.
Qed.

Lemma alpha_short_inputs_In_alpha : forall alpha k s,
  List.In s (alpha_short_inputs alpha k) -> alpha_only alpha s = true.
Proof.
  intros alpha k. induction k as [| k IH]; intros s Hs; [destruct Hs |].
  cbn [alpha_short_inputs] in Hs. apply List.in_app_or in Hs as [Hs | Hs].
  - exact (alpha_lists_In_alpha alpha k s Hs).
  - apply IH. exact Hs.
Qed.

Lemma alpha_short_inputs_complete : forall alpha k s,
  alpha_only alpha s = true -> (length s < k)%nat ->
  List.In s (alpha_short_inputs alpha k).
Proof.
  intros alpha k. induction k as [| k IH]; intros s Ha Hlen; [exfalso; lia |].
  cbn [alpha_short_inputs]. apply List.in_or_app.
  destruct (Nat.eq_dec (length s) k) as [Heq | Hne].
  - left. rewrite <- Heq. apply alpha_lists_complete. exact Ha.
  - right. apply IH; [exact Ha | lia].
Qed.

Lemma alpha_short_inputs_nodup : forall alpha,
  List.NoDup alpha -> forall k, List.NoDup (alpha_short_inputs alpha k).
Proof.
  intros alpha Hnd. induction k as [| k IH]; [apply List.NoDup_nil |].
  cbn [alpha_short_inputs]. apply List.NoDup_app.
  - apply alpha_lists_nodup. exact Hnd.
  - exact IH.
  - intros s Hin1 Hin2. apply alpha_short_inputs_In_length in Hin2.
    rewrite (alpha_lists_In_length alpha k s Hin1) in Hin2. lia.
Qed.

Lemma alpha_short_inputs_sum : forall alpha p k,
  alpha <> [] ->
  (qsum (fun s => alpha_geo_point alpha p (length s)) (alpha_short_inputs alpha k)
     == geo_prefix_sum p k)%Q.
Proof.
  intros alpha p k Hne. induction k as [| k IH]; [reflexivity |].
  cbn [alpha_short_inputs geo_prefix_sum].
  rewrite qsum_app, IH, (alpha_lists_sum alpha p k Hne). reflexivity.
Qed.

(** The cylinder enumeration over the alphabet, [bytes_cyl] with [alpha]
    in place of [all_bytes], and the cancellation that bounds it —
    [cyl_enum_sum_le]'s argument, stated over byte lists: a cylinder of
    depth [N + 1] is its own stopping payload plus [length alpha]
    cylinders one deeper, and [p + length alpha * (1 - p) * alpha_ratio]
    is [1] exactly, by [alpha_ratio_cancel]. *)
Fixpoint alpha_cyl (alpha bs : list byte) (N : nat) : list (list byte) :=
  match N with
  | O => [bs]
  | S N' => bs :: List.flat_map (fun b => alpha_cyl alpha (bs ++ [b]) N') alpha
  end.

Lemma alpha_cyl_all_bytes : forall N bs, alpha_cyl all_bytes bs N = bytes_cyl bs N.
Proof.
  induction N as [| N IH]; intros bs; [reflexivity |].
  cbn [alpha_cyl bytes_cyl]. f_equal. apply List.flat_map_ext. intros b. apply IH.
Qed.

Lemma alpha_cyl_In : forall alpha N bs ext,
  alpha_only alpha ext = true -> (length ext <= N)%nat ->
  List.In (bs ++ ext) (alpha_cyl alpha bs N).
Proof.
  intros alpha N. induction N as [| N IH]; intros bs ext Hext Hlen.
  - destruct ext as [| b ext]; [| cbn [length] in Hlen; lia].
    rewrite List.app_nil_r. left. reflexivity.
  - destruct ext as [| b ext].
    + rewrite List.app_nil_r. left. reflexivity.
    + right. apply List.in_flat_map.
      unfold alpha_only in Hext. cbn [List.forallb] in Hext.
      apply Bool.andb_true_iff in Hext as [Hb Hext].
      exists b. split; [apply alpha_memb_In; exact Hb |].
      replace (bs ++ b :: ext) with ((bs ++ [b]) ++ ext)
        by (rewrite <- List.app_assoc; reflexivity).
      apply IH; [exact Hext | cbn [length] in Hlen; lia].
Qed.

Lemma alpha_cyl_sum_le : forall alpha p,
  alpha <> [] -> (0 <= p)%Q -> (p <= 1)%Q ->
  forall N bs,
    (qsum (fun s => alpha_geo_point alpha p (length s)) (alpha_cyl alpha bs N)
       <= alpha_geo_mass alpha p (length bs))%Q.
Proof.
  intros alpha p Hne Hp0 Hp1 N. induction N as [| N IH]; intros bs.
  - cbn [alpha_cyl]. rewrite qsum_cons, qsum_nil, Qplus_0_r. cbv beta.
    apply alpha_geo_point_le_mass, Hp1.
  - cbn [alpha_cyl]. rewrite qsum_cons. cbv beta.
    eapply Qle_trans.
    + apply Qplus_le_compat; [apply Qle_refl |].
      apply (qsum_flat_map_const_le _ _ _ (alpha_geo_mass alpha p (S (length bs)))).
      intros b _. eapply Qle_trans; [apply IH |].
      rewrite List.length_app. cbn [length]. rewrite Nat.add_1_r.
      apply Qle_refl.
    + unfold alpha_geo_point, alpha_geo_mass. rewrite Qpow_succ.
      set (m := Qpow ((1 - p) * alpha_ratio alpha) (length bs)).
      apply (Qle_trans _ (p * m + (Qnat (length alpha) * alpha_ratio alpha)
                                    * ((1 - p) * m))%Q);
        [apply Qle_of_Qeq; ring |].
      rewrite (alpha_ratio_cancel alpha Hne). apply Qle_of_Qeq. ring.
Qed.

(* =========================================================================
   Combinator: geometric file contents behind a fixed header, over a
   fixed ALPHABET
   ========================================================================= *)

(** THE WEIGHT: [file_prefix_geo_weight] with one more test on the
    payload — every byte in the alphabet — and the alphabet's ratio in
    place of [1 # 256].  A matching core whose file is [hdr ++ t] with
    [t] over the alphabet weighs [p * ((1 - p) * alpha_ratio) ^ length t];
    a payload with any byte outside the alphabet weighs zero, as does a
    file that misses the header or a core off the environment. *)
Definition file_prefix_over_geo_weight (alpha hdr : list byte) (p : Q)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : list byte) (c : FinCore) : Q :=
  if decide (c = file_core argv envp fs0 pth s (fs_file pth (core_fs c)))
  then match strip_prefix hdr (fs_file pth (core_fs c)) with
       | Some t => if alpha_only alpha t
                   then alpha_geo_point alpha p (length t)
                   else 0%Q
       | None => 0%Q
       end
  else 0%Q.

Lemma file_prefix_over_geo_weight_match : forall alpha hdr p argv envp fs0 pth s t,
  alpha_only alpha t = true ->
  file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
    (file_prefix_core hdr argv envp fs0 pth s t)
    = alpha_geo_point alpha p (length t).
Proof.
  intros alpha hdr p argv envp fs0 pth s t Ha.
  unfold file_prefix_over_geo_weight, file_prefix_core.
  rewrite fs_file_file_core.
  destruct (decide _) as [_ | Hne]; [| congruence].
  rewrite strip_prefix_app, Ha. reflexivity.
Qed.

(** ZERO ON A PAYLOAD OUTSIDE THE ALPHABET, the rule this family adds. *)
Lemma file_prefix_over_geo_weight_off_alphabet :
  forall alpha hdr p argv envp fs0 pth s t,
  alpha_only alpha t = false ->
  file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
    (file_prefix_core hdr argv envp fs0 pth s t)
    = 0%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s t Ha.
  unfold file_prefix_over_geo_weight, file_prefix_core.
  rewrite fs_file_file_core.
  destruct (decide _) as [_ | Hne]; [| reflexivity].
  rewrite strip_prefix_app, Ha. reflexivity.
Qed.

Lemma file_prefix_over_geo_weight_mismatch : forall alpha hdr p argv envp fs0 pth s c,
  c <> file_core argv envp fs0 pth s (fs_file pth (core_fs c)) ->
  file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s c Hne.
  unfold file_prefix_over_geo_weight.
  destruct (decide _) as [Heq | _]; [congruence | reflexivity].
Qed.

Lemma file_prefix_over_geo_weight_off_header :
  forall alpha hdr p argv envp fs0 pth s c,
  strip_prefix hdr (fs_file pth (core_fs c)) = None ->
  file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s c Hn.
  unfold file_prefix_over_geo_weight.
  destruct (decide _) as [_ | _]; [rewrite Hn; reflexivity | reflexivity].
Qed.

Lemma file_prefix_over_geo_weight_off_header_zero :
  forall alpha hdr p argv envp fs0 pth s c,
  (forall t, fs_file pth (core_fs c) <> hdr ++ t) ->
  file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s c Hno.
  apply file_prefix_over_geo_weight_off_header.
  apply strip_prefix_None_of_no_extension. exact Hno.
Qed.

Lemma file_prefix_over_geo_weight_nonneg : forall alpha hdr p argv envp fs0 pth s,
  (0 <= p)%Q -> (p <= 1)%Q ->
  forall c, (0 <= file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c)%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s Hp0 Hp1 c.
  unfold file_prefix_over_geo_weight.
  destruct (decide _) as [_ | _]; [| apply Qle_refl].
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |];
    [| apply Qle_refl].
  destruct (alpha_only alpha t);
    [apply alpha_geo_point_nonneg; assumption | apply Qle_refl].
Qed.

(** The weight is at most the alphabet-geometric weight of the payload
    at EVERY payload, alphabet or not — the [<=] form of the block
    identity, which needs no hypothesis on the payloads enumerated. *)
Lemma file_prefix_over_geo_weight_le_point :
  forall alpha hdr p argv envp fs0 pth s t,
  (0 <= p)%Q -> (p <= 1)%Q ->
  (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
     (file_prefix_core hdr argv envp fs0 pth s t)
     <= alpha_geo_point alpha p (length t))%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s t Hp0 Hp1.
  destruct (alpha_only alpha t) eqn:Ha.
  - rewrite (file_prefix_over_geo_weight_match _ _ _ _ _ _ _ _ _ Ha).
    apply Qle_refl.
  - rewrite (file_prefix_over_geo_weight_off_alphabet _ _ _ _ _ _ _ _ _ Ha).
    apply alpha_geo_point_nonneg; assumption.
Qed.

(** The distribution.  The alphabet's facts are constructor
    arguments, as the side conditions on [p_stop] are: nothing the
    constructor itself needs uses them — nonnegativity does not — but
    every certificate below does, [NoDup] for the witness families'
    duplicate-freedom and non-emptiness for the cancellation, and a
    distribution whose declared mass [1] could not be certified is not
    one this file wants to build. *)
Definition file_geometric_prefix_over (alpha : list byte)
    (Hnd : List.NoDup alpha) (Hne : alpha <> []) (hdr : list byte) (p : Q)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : list byte) (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q)
    : CoreDistribution :=
  mkCoreDistribution (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) 1
    (file_prefix_over_geo_weight_nonneg alpha hdr p argv envp fs0 pth s Hp0 Hp1).

(* =========================================================================
   The full alphabet: [file_geometric_prefix], pointwise
   ========================================================================= *)

Lemma file_prefix_over_geo_weight_all_bytes : forall hdr p argv envp fs0 pth s c,
  (file_prefix_over_geo_weight all_bytes hdr p argv envp fs0 pth s c
     == file_prefix_geo_weight hdr p argv envp fs0 pth s c)%Q.
Proof.
  intros hdr p argv envp fs0 pth s c.
  unfold file_prefix_over_geo_weight, file_prefix_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |];
    [| reflexivity].
  rewrite alpha_only_all_bytes. apply alpha_geo_point_all_bytes.
Qed.

Lemma file_geometric_prefix_over_all_bytes_pointwise :
  forall Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 c,
  (cd_weight (file_geometric_prefix_over all_bytes Hnd Hne hdr p argv envp fs0
                pth s Hp0 Hp1) c
     == cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) c)%Q.
Proof.
  intros Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 c.
  cbn [cd_weight file_geometric_prefix_over file_geometric_prefix].
  apply file_prefix_over_geo_weight_all_bytes.
Qed.

Lemma file_geometric_prefix_over_all_bytes_mass :
  forall Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1,
  cd_mass (file_geometric_prefix_over all_bytes Hnd Hne hdr p argv envp fs0
             pth s Hp0 Hp1)
    = cd_mass (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).
Proof. reflexivity. Qed.

(* =========================================================================
   The block identity, over the alphabet
   ========================================================================= *)

Lemma qsum_file_prefix_over_block : forall alpha hdr p argv envp fs0 pth s B,
  (forall t, List.In t B -> alpha_only alpha t = true) ->
  (qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
     (List.map (file_prefix_core hdr argv envp fs0 pth s) B)
     == qsum (fun t => alpha_geo_point alpha p (length t)) B)%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s B HB.
  rewrite qsum_map.
  apply qsum_ext. intros t Ht.
  rewrite (file_prefix_over_geo_weight_match _ _ _ _ _ _ _ _ _ (HB t Ht)).
  reflexivity.
Qed.

Lemma qsum_file_prefix_over_block_le : forall alpha hdr p argv envp fs0 pth s B,
  (0 <= p)%Q -> (p <= 1)%Q ->
  (qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
     (List.map (file_prefix_core hdr argv envp fs0 pth s) B)
     <= qsum (fun t => alpha_geo_point alpha p (length t)) B)%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s B Hp0 Hp1.
  rewrite qsum_map.
  apply qsum_mono. intros t _.
  apply file_prefix_over_geo_weight_le_point; assumption.
Qed.

(* =========================================================================
   The payload cylinder, and the enumeration that bounds it
   ========================================================================= *)

(** The cylinder is [in_file_prefix_cylinder] unchanged: the fire set is
    described by a payload prefix, and a core in it whose payload leaves
    the alphabet weighs zero rather than being excluded.  The membership
    test carries the alphabet, for the filter. *)
Definition matches_file_prefix_over_env (alpha hdr : list byte)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : list byte) (c : FinCore) : bool :=
  matches_file_prefix_env hdr argv envp fs0 pth s c
  && match strip_prefix hdr (fs_file pth (core_fs c)) with
     | Some t => alpha_only alpha t
     | None => false
     end.

Lemma file_prefix_over_geo_weight_unmatched :
  forall alpha hdr p argv envp fs0 pth s c,
  matches_file_prefix_over_env alpha hdr argv envp fs0 pth s c = false ->
  file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s c H.
  unfold matches_file_prefix_over_env in H.
  apply Bool.andb_false_iff in H as [H | H].
  - destruct (matches_file_prefix_env_false hdr argv envp fs0 pth s c H)
      as [Hne | Hn].
    + apply file_prefix_over_geo_weight_mismatch. exact Hne.
    + apply file_prefix_over_geo_weight_off_header. exact Hn.
  - unfold file_prefix_over_geo_weight.
    destruct (decide _) as [_ | _]; [| reflexivity].
    destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |];
      [| reflexivity].
    rewrite H. reflexivity.
Qed.

Lemma matches_file_prefix_over_env_true :
  forall alpha hdr argv envp fs0 pth s c,
  matches_file_prefix_over_env alpha hdr argv envp fs0 pth s c = true ->
  exists t, c = file_prefix_core hdr argv envp fs0 pth s t
            /\ alpha_only alpha t = true.
Proof.
  intros alpha hdr argv envp fs0 pth s c H.
  unfold matches_file_prefix_over_env in H.
  apply Bool.andb_true_iff in H as [Henv Ha].
  destruct (matches_file_prefix_env_true hdr argv envp fs0 pth s c Henv)
    as [t Ht].
  exists t. split; [exact Ht |].
  rewrite Ht, fs_file_file_prefix_core, strip_prefix_app in Ha. exact Ha.
Qed.

(** THE BOUND OVER CORES.  One step more than the 256-byte family:
    the list is first filtered to the cores that weigh anything (the
    rest weigh zero), and the survivors — payloads over the alphabet
    extending [bs] — are contained in [alpha_cyl] mapped through the
    template; the enumeration is then bounded by the [<=] block identity
    and [alpha_cyl_sum_le].  No hypothesis on [bs] itself: a prefix that
    leaves the alphabet gives an empty filter and a bound of a positive
    number over zero. *)
Lemma file_prefix_over_geo_weight_cylinder_bound :
  forall alpha hdr p argv envp fs0 pth s,
  alpha <> [] -> (0 <= p)%Q -> (p <= 1)%Q ->
  forall bs cs,
    List.NoDup cs ->
    (forall c, List.In c cs ->
       in_file_prefix_cylinder hdr argv envp fs0 pth s bs c) ->
    (qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) cs
       <= alpha_geo_mass alpha p (length bs))%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s Hne Hp0 Hp1 bs cs Hnd Hcyl.
  rewrite (qsum_filter _ (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_prefix_over_geo_weight_unmatched
                   alpha hdr p argv envp fs0 pth s c Hc);
        reflexivity).
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (List.map (file_prefix_core hdr argv envp fs0 pth s)
                  (alpha_cyl alpha bs (cores_file_prefix_depth hdr pth cs))))
    | eapply Qle_trans;
      [ apply qsum_file_prefix_over_block_le; assumption
      | apply alpha_cyl_sum_le; assumption ] ].
  - apply file_prefix_over_geo_weight_nonneg; assumption.
  - apply List.NoDup_filter. exact Hnd.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    destruct (Hcyl c Hin) as [ext Hext].
    destruct (matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm)
      as [t [Ht Ha]].
    assert (Hteq : t = bs ++ ext).
    { apply (file_prefix_core_inj hdr argv envp fs0 pth s).
      rewrite <- Ht, <- Hext. reflexivity. }
    subst t. rewrite alpha_only_app in Ha.
    apply Bool.andb_true_iff in Ha as [_ Hae].
    assert (Hd := cores_file_prefix_depth_ge hdr pth cs c (bs ++ ext) Hin).
    rewrite Hext, fs_file_file_prefix_core in Hd.
    specialize (Hd eq_refl). rewrite List.length_app in Hd.
    rewrite Hext. apply List.in_map. apply alpha_cyl_In; [exact Hae | lia].
Qed.

(* =========================================================================
   The exports
   ========================================================================= *)

Definition file_geometric_prefix_over_cylinder_mass (alpha : list byte) (p : Q)
    (bs : list byte) : Q :=
  alpha_geo_mass alpha p (length bs).

Lemma file_geometric_prefix_over_cylinder_mass_closed_form : forall alpha p bs,
  (file_geometric_prefix_over_cylinder_mass alpha p bs
     == Qpow (1 - p) (length bs) * Qpow (alpha_ratio alpha) (length bs))%Q.
Proof. intros alpha p bs. apply alpha_geo_mass_closed_form. Qed.

Lemma file_geometric_prefix_over_cylinder_mass_all_bytes : forall p bs,
  (file_geometric_prefix_over_cylinder_mass all_bytes p bs
     == file_geometric_prefix_cylinder_mass p bs)%Q.
Proof. intros p bs. apply alpha_geo_mass_all_bytes. Qed.

Lemma file_geometric_prefix_over_bound :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)) ->
  (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                          fs0 pth s Hp0 Hp1)) l
     <= file_geometric_prefix_over_cylinder_mass alpha p bs)%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 bs l Hndl Hcyl.
  cbn [cd_weight file_geometric_prefix_over]. rewrite core_sum_map_fin_core.
  unfold file_geometric_prefix_over_cylinder_mass.
  apply file_prefix_over_geo_weight_cylinder_bound;
    [exact Hne | exact Hp0 | exact Hp1 | exact Hndl |].
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. apply Hcyl. exact Hin.
Qed.

Lemma file_geometric_prefix_over_bound_or_off_environment :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)
     \/ matches_file_prefix_over_env alpha hdr argv envp fs0 pth s (fin_core f)
        = false) ->
  (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                          fs0 pth s Hp0 Hp1)) l
     <= file_geometric_prefix_over_cylinder_mass alpha p bs)%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 bs l Hndl Hor.
  cbn [cd_weight file_geometric_prefix_over]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_prefix_over_geo_weight_unmatched
                   alpha hdr p argv envp fs0 pth s c Hc);
        reflexivity).
  unfold file_geometric_prefix_over_cylinder_mass.
  apply file_prefix_over_geo_weight_cylinder_bound;
    [exact Hne | exact Hp0 | exact Hp1 | |].
  - apply List.NoDup_filter. exact Hndl.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (Hor f Hinl) as [Hcyl | Hoff].
    + rewrite <- Hf. exact Hcyl.
    + rewrite Hf in Hoff. rewrite Hoff in Hm. discriminate Hm.
Qed.

Lemma file_geometric_prefix_over_mass_upper :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                          fs0 pth s Hp0 Hp1)) l
     <= cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                   fs0 pth s Hp0 Hp1))%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 l Hndl.
  cbn [cd_mass file_geometric_prefix_over].
  change 1%Q with (file_geometric_prefix_over_cylinder_mass alpha p []).
  apply file_geometric_prefix_over_bound_or_off_environment; [exact Hndl |].
  intros f Hf.
  destruct (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s
              (fin_core f)) eqn:Hm.
  - left.
    destruct (matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s
                (fin_core f) Hm) as [t [Ht _]].
    exists t. cbn [List.app]. exact Ht.
  - right. reflexivity.
Qed.

(* =========================================================================
   The counting lemma and the payload-length slice, over the alphabet
   ========================================================================= *)

Lemma file_prefix_over_core_list_length_bound :
  forall alpha hdr argv envp fs0 pth s n (cs : list FinCore),
    List.NoDup cs ->
    (forall c, List.In c cs ->
       exists t, c = file_prefix_core hdr argv envp fs0 pth s t
                 /\ length t = n /\ alpha_only alpha t = true) ->
    (length cs <= length alpha ^ n)%nat.
Proof.
  intros alpha hdr argv envp fs0 pth s n cs Hnd Hall.
  assert (Hle : (length cs
                 <= length (List.map (file_prefix_core hdr argv envp fs0 pth s)
                              (alpha_lists alpha n)))%nat).
  { apply List.NoDup_incl_length; [exact Hnd |].
    intros c Hc. destruct (Hall c Hc) as [t [Ht [Hlen Ha]]].
    apply List.in_map_iff. exists t. split; [symmetry; exact Ht |].
    rewrite <- Hlen. apply alpha_lists_complete. exact Ha. }
  rewrite List.length_map, alpha_lists_length in Hle. exact Hle.
Qed.

Lemma injective_core_list_in_file_prefix_over_cylinder_length_bound :
  forall (alpha hdr : list byte) (argv envp : list (list byte)) (fs0 : Fs.Fs)
         (pth : Fs.path) (s : list byte) (n : nat) (l : list FinProcInput),
    List.NoDup (List.map fin_core l) ->
    (forall f, List.In f l ->
       exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
                 /\ length t = n /\ alpha_only alpha t = true) ->
    (length l <= length alpha ^ n)%nat.
Proof.
  intros alpha hdr argv envp fs0 pth s n l Hnd Hall.
  rewrite <- (List.length_map fin_core l).
  apply (file_prefix_over_core_list_length_bound alpha hdr argv envp fs0 pth s n);
    [exact Hnd |].
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  destruct (Hall f Hin) as [t Ht]. exists t. rewrite <- Hf. exact Ht.
Qed.

Lemma injective_core_list_in_file_prefix_over_cylinder_length_bound_attained :
  forall (alpha hdr : list byte), List.NoDup alpha ->
  forall (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
         (s : list byte) (n : nat),
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (forall f, List.In f l ->
          exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
                    /\ length t = n /\ alpha_only alpha t = true)
    /\ length l = (length alpha ^ n)%nat.
Proof.
  intros alpha hdr Hnd argv envp fs0 pth s n.
  exists (List.map
            (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
            (alpha_lists alpha n)).
  split; [| split].
  - rewrite List.map_map.
    rewrite (List.map_ext _ (file_prefix_core hdr argv envp fs0 pth s))
      by (intros t; apply fin_core_core_input).
    apply NoDup_map_inj; [| apply alpha_lists_nodup; exact Hnd].
    intros x y _ _ Heq. exact (file_prefix_core_inj _ _ _ _ _ _ _ _ Heq).
  - intros f Hf. apply List.in_map_iff in Hf as [t [Ht Hin]]. subst f.
    exists t. rewrite fin_core_core_input.
    split; [reflexivity | split].
    + apply alpha_lists_In_length in Hin. exact Hin.
    + apply alpha_lists_In_alpha in Hin. exact Hin.
  - rewrite List.length_map, alpha_lists_length. reflexivity.
Qed.

(** THE PAYLOAD-LENGTH SLICE, with no premise that the payloads are over
    the alphabet: the ones that are not weigh zero and are filtered
    away, and the survivors number at most [length alpha ^ n]. *)
Lemma file_geometric_prefix_over_slice_bound :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
               /\ length t = n) ->
  (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                          fs0 pth s Hp0 Hp1)) l
     <= p * Qpow (1 - p) n)%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n l Hndl Hall.
  cbn [cd_weight file_geometric_prefix_over]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_prefix_over_geo_weight_unmatched
                   alpha hdr p argv envp fs0 pth s c Hc);
        reflexivity).
  assert (Hslice : forall c,
            List.In c (List.filter
                         (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s)
                         (List.map fin_core l)) ->
            exists t, c = file_prefix_core hdr argv envp fs0 pth s t
                      /\ length t = n /\ alpha_only alpha t = true).
  { intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (Hall f Hinl) as [t [Ht Hlen]].
    destruct (matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm)
      as [t' [Ht' Ha]].
    assert (Hteq : t' = t).
    { apply (file_prefix_core_inj hdr argv envp fs0 pth s).
      rewrite <- Ht', <- Hf. exact Ht. }
    subst t'. exists t. split; [exact Ht' | split; [exact Hlen | exact Ha]]. }
  rewrite (qsum_const _ _ (alpha_geo_point alpha p n)).
  2:{ intros c Hc. destruct (Hslice c Hc) as [t [Ht [Hlen Ha]]].
      rewrite Ht, (file_prefix_over_geo_weight_match _ _ _ _ _ _ _ _ _ Ha), Hlen.
      reflexivity. }
  rewrite <- (alpha_slice_total alpha p n Hne).
  apply Qmult_le_compat_r; [| apply alpha_geo_point_nonneg; assumption].
  apply Qnat_le.
  apply (file_prefix_over_core_list_length_bound alpha hdr argv envp fs0 pth s n).
  - apply List.NoDup_filter. exact Hndl.
  - exact Hslice.
Qed.

(** THE WIDER SLICE STATEMENT for this family, in the whole-file shape:
    environment matched and file length [length hdr + n], with no premise
    on the header or the alphabet. *)
Lemma file_geometric_prefix_over_slice_bound_by_file_length :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = file_core argv envp fs0 pth s (fs_file pth (fin_image_fs f))
     /\ length (fs_file pth (fin_image_fs f)) = (length hdr + n)%nat) ->
  (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                          fs0 pth s Hp0 Hp1)) l
     <= p * Qpow (1 - p) n)%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n l Hndl Hall.
  cbn [cd_weight file_geometric_prefix_over]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_prefix_over_geo_weight_unmatched
                   alpha hdr p argv envp fs0 pth s c Hc);
        reflexivity).
  assert (Hslice : forall c,
            List.In c (List.filter
                         (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s)
                         (List.map fin_core l)) ->
            exists t, c = file_prefix_core hdr argv envp fs0 pth s t
                      /\ length t = n /\ alpha_only alpha t = true).
  { intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm)
      as [t [Ht Ha]].
    exists t. split; [exact Ht | split; [| exact Ha]].
    apply (file_prefix_payload_length hdr argv envp fs0 pth s f t n);
      [rewrite Hf; exact Ht | exact (proj2 (Hall f Hinl))]. }
  rewrite (qsum_const _ _ (alpha_geo_point alpha p n)).
  2:{ intros c Hc. destruct (Hslice c Hc) as [t [Ht [Hlen Ha]]].
      rewrite Ht, (file_prefix_over_geo_weight_match _ _ _ _ _ _ _ _ _ Ha), Hlen.
      reflexivity. }
  rewrite <- (alpha_slice_total alpha p n Hne).
  apply Qmult_le_compat_r; [| apply alpha_geo_point_nonneg; assumption].
  apply Qnat_le.
  apply (file_prefix_over_core_list_length_bound alpha hdr argv envp fs0 pth s n).
  - apply List.NoDup_filter. exact Hndl.
  - exact Hslice.
Qed.

Lemma file_geometric_prefix_over_slice_bound_attained :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n,
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (forall f, List.In f l ->
          exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
                    /\ length t = n)
    /\ (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv
                               envp fs0 pth s Hp0 Hp1)) l
          == p * Qpow (1 - p) n)%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n.
  destruct (injective_core_list_in_file_prefix_over_cylinder_length_bound_attained
              alpha hdr Hnd argv envp fs0 pth s n) as [l [Hndl [Hall Hlen]]].
  exists l. split; [exact Hndl | split].
  - intros f Hf. destruct (Hall f Hf) as [t [Ht [Hl _]]].
    exists t. split; [exact Ht | exact Hl].
  - cbn [cd_weight file_geometric_prefix_over]. rewrite core_sum_map_fin_core.
    rewrite (qsum_const _ _ (alpha_geo_point alpha p n)).
    2:{ intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
        destruct (Hall f Hin) as [t [Ht [Hlength Ha]]].
        rewrite <- Hf, Ht,
          (file_prefix_over_geo_weight_match _ _ _ _ _ _ _ _ _ Ha), Hlength.
        reflexivity. }
    rewrite List.length_map, Hlen. apply alpha_slice_total. exact Hne.
Qed.

Lemma file_geometric_prefix_over_slice_bound_sharp :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n K,
  (forall l, List.NoDup (List.map fin_core l) ->
     (forall f, List.In f l ->
        exists t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t
                  /\ length t = n) ->
     (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv
                             envp fs0 pth s Hp0 Hp1)) l
        <= K)%Q) ->
  (p * Qpow (1 - p) n <= K)%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n K Hbound.
  destruct (file_geometric_prefix_over_slice_bound_attained alpha Hnd Hne hdr p
              argv envp fs0 pth s Hp0 Hp1 n) as [l [Hndl [Hall Hsum]]].
  rewrite <- Hsum. apply Hbound; assumption.
Qed.

(* =========================================================================
   The lower certificate for [file_geometric_prefix_over]
   ========================================================================= *)

Definition file_prefix_over_geo_lower_witness (alpha hdr : list byte)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : list byte) (k : nat) : list FinProcInput :=
  List.map (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
    (alpha_short_inputs alpha k).

Lemma map_fin_core_file_prefix_over_geo_lower_witness :
  forall alpha hdr argv envp fs0 pth s k,
  List.map fin_core (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k)
    = List.map (file_prefix_core hdr argv envp fs0 pth s) (alpha_short_inputs alpha k).
Proof.
  intros alpha hdr argv envp fs0 pth s k.
  unfold file_prefix_over_geo_lower_witness.
  rewrite List.map_map. apply List.map_ext. intros t.
  apply fin_core_core_input.
Qed.

Lemma file_prefix_over_geo_lower_witness_nodup :
  forall alpha, List.NoDup alpha ->
  forall hdr argv envp fs0 pth s k,
  List.NoDup
    (List.map fin_core
       (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k)).
Proof.
  intros alpha Hnd hdr argv envp fs0 pth s k.
  rewrite map_fin_core_file_prefix_over_geo_lower_witness.
  apply NoDup_map_inj; [| apply alpha_short_inputs_nodup; exact Hnd].
  intros x y _ _ Heq. exact (file_prefix_core_inj _ _ _ _ _ _ _ _ Heq).
Qed.

Lemma qsum_file_prefix_over_short_inputs :
  forall alpha hdr p argv envp fs0 pth s k,
  alpha <> [] ->
  (qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
     (List.map (file_prefix_core hdr argv envp fs0 pth s) (alpha_short_inputs alpha k))
     == geo_prefix_sum p k)%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s k Hne.
  rewrite qsum_file_prefix_over_block
    by (intros t Ht; exact (alpha_short_inputs_In_alpha alpha k t Ht)).
  apply alpha_short_inputs_sum. exact Hne.
Qed.

Lemma file_geometric_prefix_over_mass_lower_witness :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 k,
  List.NoDup
    (List.map fin_core
       (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k))
  /\ (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                             fs0 pth s Hp0 Hp1))
        (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k)
        == 1 - Qpow (1 - p) k)%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 k.
  split; [apply file_prefix_over_geo_lower_witness_nodup; exact Hnd |].
  cbn [cd_weight file_geometric_prefix_over].
  rewrite core_sum_map_fin_core, map_fin_core_file_prefix_over_geo_lower_witness.
  rewrite (qsum_file_prefix_over_short_inputs _ _ _ _ _ _ _ _ _ Hne).
  apply geo_prefix_sum_closed.
Qed.

Lemma file_geometric_prefix_over_mass_lower_prefix :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 k,
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv
                               envp fs0 pth s Hp0 Hp1)) l
          == 1 - Qpow (1 - p) k)%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 k.
  exists (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k).
  apply file_geometric_prefix_over_mass_lower_witness.
Qed.

Lemma file_geometric_prefix_over_mass_lower_certificate :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 eps,
  (0 < p)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
                   Hp0 Hp1) - eps
          <= core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p
                                    argv envp fs0 pth s Hp0 Hp1)) l)%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 eps Hpos Heps.
  destruct (geo_gap_small p eps Hpos Hp1 Heps) as [k Hk].
  destruct (file_geometric_prefix_over_mass_lower_prefix alpha Hnd Hne hdr p argv
              envp fs0 pth s Hp0 Hp1 k) as [l [Hndl Hsum]].
  exists l. split; [exact Hndl |].
  rewrite Hsum. cbn [cd_mass file_geometric_prefix_over].
  apply (proj2 (Qle_minus_iff (1 - eps) (1 - Qpow (1 - p) k))).
  apply (Qle_trans _ (eps + - Qpow (1 - p) k)%Q);
    [ apply (proj1 (Qle_minus_iff (Qpow (1 - p) k) eps)); exact Hk
    | apply Qle_of_Qeq; ring].
Qed.

(* =========================================================================
   ... and this mass is a SUPREMUM and not a maximum
   ========================================================================= *)

Lemma file_geometric_prefix_over_bound_by_max_length :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     (length (fs_file pth (fin_image_fs f)) <= length hdr + n)%nat) ->
  (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                          fs0 pth s Hp0 Hp1)) l
     <= 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n l Hndl Hlen.
  cbn [cd_weight file_geometric_prefix_over]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s))
    by (intros c Hc;
        rewrite (file_prefix_over_geo_weight_unmatched
                   alpha hdr p argv envp fs0 pth s c Hc);
        reflexivity).
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (List.map (file_prefix_core hdr argv envp fs0 pth s)
                  (alpha_short_inputs alpha (S n))))
    | rewrite (qsum_file_prefix_over_short_inputs _ _ _ _ _ _ _ _ _ Hne),
        geo_prefix_sum_closed;
      apply Qle_refl ].
  - apply file_prefix_over_geo_weight_nonneg; assumption.
  - apply List.NoDup_filter. exact Hndl.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm)
      as [t [Ht Ha]].
    apply List.in_map_iff. exists t. split; [symmetry; exact Ht |].
    apply alpha_short_inputs_complete; [exact Ha |].
    assert (Hle := Hlen f Hinl).
    assert (Hc' : fs_file pth (core_fs c) = hdr ++ t)
      by (rewrite Ht; apply fs_file_file_prefix_core).
    rewrite <- Hf in Hc'. cbn [fin_core core_fs] in Hc'.
    rewrite Hc', List.length_app in Hle. lia.
Qed.

Lemma file_geometric_prefix_over_bound_by_max_length_attained :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n,
  (forall f,
     List.In f (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s (S n)) ->
     (length (fs_file pth (fin_image_fs f)) <= length hdr + n)%nat)
  /\ (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                             fs0 pth s Hp0 Hp1))
        (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s (S n))
        == 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 n. split.
  - intros f Hf. unfold file_prefix_over_geo_lower_witness in Hf.
    apply List.in_map_iff in Hf as [t [Ht Hin]]. subst f.
    cbn [core_input fin_image_fs].
    rewrite fs_file_file_prefix_core, List.length_app.
    apply alpha_short_inputs_In_length in Hin. lia.
  - apply file_geometric_prefix_over_mass_lower_witness.
Qed.

Lemma file_geometric_prefix_over_mass_not_attained :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                            fs0 pth s Hp0 Hp1)) l
       < cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
                    Hp0 Hp1))%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 Hlt l Hndl.
  cbn [cd_mass file_geometric_prefix_over].
  pose (n := List.list_max
               (List.map (fun f => length (fs_file pth (fin_image_fs f))) l)).
  apply (Qle_lt_trans _ (1 - Qpow (1 - p) (S n))%Q).
  - apply file_geometric_prefix_over_bound_by_max_length; [exact Hndl |].
    intros f Hf.
    enough (length (fs_file pth (fin_image_fs f)) <= n)%nat by lia.
    apply list_max_ge. apply List.in_map_iff.
    exists f. split; [reflexivity | exact Hf].
  - apply (proj2 (Qlt_minus_iff (1 - Qpow (1 - p) (S n)) 1)).
    apply (Qlt_le_trans _ (Qpow (1 - p) (S n))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qpow_pos. apply (Qlt_minus_iff p 1). exact Hlt.
Qed.

Lemma file_geometric_prefix_over_mass_supremum_not_maximum :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    ~ (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp
                              fs0 pth s Hp0 Hp1)) l
         == cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0
                       pth s Hp0 Hp1))%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 Hlt l Hndl.
  apply Qlt_not_eq.
  apply file_geometric_prefix_over_mass_not_attained; assumption.
Qed.

(* =========================================================================
   Non-vacuity: the alphabet bites
   ========================================================================= *)

Lemma file_prefix_over_geo_weight_off_environment_zero :
  forall alpha hdr p argv envp fs0 pth s c,
  core_argv c <> argv ->
  file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0%Q.
Proof.
  intros alpha hdr p argv envp fs0 pth s c Hne.
  apply file_prefix_over_geo_weight_mismatch.
  intros Heq. apply (f_equal core_argv) in Heq.
  cbn [file_core core_argv] in Heq. exact (Hne Heq).
Qed.

Lemma file_geometric_prefix_over_off_header_zero :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 c,
  (forall t, fs_file pth (core_fs c) <> hdr ++ t) ->
  cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
               Hp0 Hp1) c = 0%Q
  /\ cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
                Hp0 Hp1) = 1%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 c Hno.
  split; [| reflexivity].
  cbn [cd_weight file_geometric_prefix_over].
  apply file_prefix_over_geo_weight_off_header_zero. exact Hno.
Qed.

(** THE ALPHABET BITES, in general: a payload with a byte outside the
    alphabet weighs zero while the declared mass stays [1]. *)
Lemma file_geometric_prefix_over_off_alphabet_zero :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 t,
  alpha_only alpha t = false ->
  cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
               Hp0 Hp1) (file_prefix_core hdr argv envp fs0 pth s t) = 0%Q
  /\ cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
                Hp0 Hp1) = 1%Q.
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 t Ha.
  split; [| reflexivity].
  cbn [cd_weight file_geometric_prefix_over].
  apply file_prefix_over_geo_weight_off_alphabet. exact Ha.
Qed.

(** A one-byte alphabet, a payload in it and a payload outside it, all
    behind the one-byte example header. *)
Definition file_example_alpha : list byte := [Z_to_bv 8 65].

Lemma file_example_alpha_nodup : List.NoDup file_example_alpha.
Proof. apply List.NoDup_cons; [intros H; exact H | apply List.NoDup_nil]. Qed.

Lemma file_example_alpha_ne : file_example_alpha <> [].
Proof. discriminate. Qed.

Definition file_example_in_alpha_core : FinCore :=
  file_prefix_core file_example_hdr [] [] [] file_example_path [] [Z_to_bv 8 65].

Definition file_example_off_alpha_core : FinCore :=
  file_prefix_core file_example_hdr [] [] [] file_example_path [] [Z_to_bv 8 66].

(** THE ALPHABET BITES, exhibited: the off-alphabet core — which the
    256-byte header family weighs positively — weighs zero, the
    in-alphabet core weighs positively, and the mass is [1]. *)
Lemma file_geometric_prefix_over_alphabet_bites : forall p Hp0 Hp1,
  (0 < p)%Q -> (p < 1)%Q ->
  cd_weight (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
               file_example_alpha_ne file_example_hdr p [] [] []
               file_example_path [] Hp0 Hp1) file_example_off_alpha_core = 0%Q
  /\ (0 < cd_weight (file_geometric_prefix_over file_example_alpha
                       file_example_alpha_nodup file_example_alpha_ne
                       file_example_hdr p [] [] [] file_example_path [] Hp0 Hp1)
            file_example_in_alpha_core)%Q
  /\ cd_mass (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
                file_example_alpha_ne file_example_hdr p [] [] []
                file_example_path [] Hp0 Hp1) = 1%Q
  /\ (0 < cd_weight (file_geometric_prefix file_example_hdr p [] [] []
                       file_example_path [] Hp0 Hp1)
            file_example_off_alpha_core)%Q.
Proof.
  intros p Hp0 Hp1 Hpos Hlt. split; [| split; [| split]].
  - cbn [cd_weight file_geometric_prefix_over].
    apply file_prefix_over_geo_weight_off_alphabet. vm_compute. reflexivity.
  - cbn [cd_weight file_geometric_prefix_over].
    unfold file_example_in_alpha_core.
    rewrite file_prefix_over_geo_weight_match by (vm_compute; reflexivity).
    apply alpha_geo_point_pos; [exact Hpos | exact Hlt | exact file_example_alpha_ne].
  - reflexivity.
  - cbn [cd_weight file_geometric_prefix]. unfold file_example_off_alpha_core.
    rewrite file_prefix_geo_weight_match.
    apply geo_point_pos; assumption.
Qed.

Lemma file_geometric_prefix_over_bites : forall p Hp0 Hp1,
  (0 < p)%Q -> (p < 1)%Q ->
  (0 < cd_weight (file_geometric_prefix_over file_example_alpha
                    file_example_alpha_nodup file_example_alpha_ne
                    file_example_hdr p [] [] [] file_example_path [] Hp0 Hp1)
         file_example_in_alpha_core)%Q
  /\ cd_weight (file_geometric_prefix_over file_example_alpha
                  file_example_alpha_nodup file_example_alpha_ne
                  file_example_hdr p [] [] [] file_example_path [] Hp0 Hp1)
       geo_example_other = 0%Q.
Proof.
  intros p Hp0 Hp1 Hpos Hlt. split.
  - apply (file_geometric_prefix_over_alphabet_bites p Hp0 Hp1 Hpos Hlt).
  - cbn [cd_weight file_geometric_prefix_over].
    apply file_prefix_over_geo_weight_off_environment_zero.
    unfold geo_example_other. cbn [core_argv]. discriminate.
Qed.

(* =========================================================================
   Non-vacuity: the mass is reached at [p_stop = 1], and [List.NoDup] is
   load-bearing
   ========================================================================= *)

Definition file_prefix_over_point_cd : CoreDistribution :=
  file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
    file_example_alpha_ne file_example_hdr 1 [] [] [] file_example_path []
    Qle_0_1 (Qle_refl 1).

Lemma file_prefix_over_point_cd_mass_attained :
  List.NoDup (List.map fin_core [file_hdr_input])
  /\ (core_sum (cd_weight file_prefix_over_point_cd) [file_hdr_input]
        == cd_mass file_prefix_over_point_cd)%Q.
Proof.
  split.
  - cbn [List.map].
    apply List.NoDup_cons; [intros H; exact H | apply List.NoDup_nil].
  - vm_compute. reflexivity.
Qed.

Lemma file_geometric_prefix_over_bound_needs_nodup :
  ~ List.NoDup (List.map fin_core [file_hdr_input; file_hdr_input])
  /\ (forall f, List.In f [file_hdr_input; file_hdr_input] ->
        in_file_prefix_cylinder file_example_hdr [] [] [] file_example_path []
          [] (fin_core f))
  /\ ~ (core_sum (cd_weight file_prefix_over_point_cd)
          [file_hdr_input; file_hdr_input]
          <= file_geometric_prefix_over_cylinder_mass file_example_alpha 1 [])%Q.
Proof.
  split; [| split].
  - intros Hnd. cbn [List.map] in Hnd.
    apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd as [Hnin _].
    apply Hnin. left. reflexivity.
  - intros f Hf. destruct Hf as [Hf | [Hf | []]]; subst f;
      exists []; reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate Hle.
Qed.

(* =========================================================================
   The two degenerate endpoints, both pinned
   ========================================================================= *)

Lemma file_prefix_over_geo_weight_zero_at_zero_p :
  forall alpha hdr argv envp fs0 pth s c,
  (file_prefix_over_geo_weight alpha hdr 0 argv envp fs0 pth s c == 0)%Q.
Proof.
  intros alpha hdr argv envp fs0 pth s c. unfold file_prefix_over_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |];
    [| reflexivity].
  destruct (alpha_only alpha t); [| reflexivity].
  unfold alpha_geo_point. ring.
Qed.

Lemma file_geometric_prefix_over_mass_lower_needs_positive :
  forall alpha Hnd Hne hdr argv envp fs0 pth s,
  (forall l : list FinProcInput,
     (core_sum (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr 0 argv envp
                             fs0 pth s (Qle_refl 0) Qle_0_1)) l == 0)%Q)
  /\ ~ (cd_mass (file_geometric_prefix_over alpha Hnd Hne hdr 0 argv envp fs0 pth s
                   (Qle_refl 0) Qle_0_1)
          - (1 # 2) <= 0)%Q.
Proof.
  intros alpha Hnd Hne hdr argv envp fs0 pth s. split.
  - intros l. apply core_sum_zero_weight. intros c.
    cbn [cd_weight file_geometric_prefix_over].
    apply file_prefix_over_geo_weight_zero_at_zero_p.
  - cbn [cd_mass file_geometric_prefix_over]. intros Hle.
    apply (proj2 (Qle_bool_iff _ _)) in Hle. vm_compute in Hle.
    discriminate Hle.
Qed.

Lemma file_prefix_over_geo_weight_collapses_at_one_p :
  forall alpha hdr argv envp fs0 pth s c,
  fs_file pth (core_fs c) <> hdr ->
  (file_prefix_over_geo_weight alpha hdr 1 argv envp fs0 pth s c == 0)%Q.
Proof.
  intros alpha hdr argv envp fs0 pth s c Hne. unfold file_prefix_over_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |] eqn:Hs;
    [| reflexivity].
  apply strip_prefix_Some in Hs.
  destruct (alpha_only alpha t); [| reflexivity].
  destruct t as [| b t].
  - exfalso. apply Hne. rewrite Hs. apply List.app_nil_r.
  - unfold alpha_geo_point, alpha_geo_mass. cbn [length Qpow]. ring.
Qed.

Lemma file_geometric_prefix_over_needs_p_below_one :
  forall alpha Hnd Hne hdr argv envp fs0 pth s c,
  fs_file pth (core_fs c) <> hdr ->
  (cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr 1 argv envp fs0 pth s
                Qle_0_1 (Qle_refl 1)) c
     == 0)%Q.
Proof.
  intros alpha Hnd Hne hdr argv envp fs0 pth s c Hne'.
  cbn [cd_weight file_geometric_prefix_over].
  apply file_prefix_over_geo_weight_collapses_at_one_p. exact Hne'.
Qed.

(* =========================================================================
   Combinator: geometric file contents over a VARYING launch-time
   environment
   ========================================================================= *)

(** THE TEMPLATE, with both varying coordinates plugged in: the core over
    a fixed argv, a fixed base file system and a fixed standard input,
    carrying environment [es] and file contents [d].

    It is [file_core] with the environment moved from the fixed
    parameters to the varying ones, and it is DEFINED as [file_core]
    rather than written out again so that the two round trips this family
    needs are the ones [file_geometric] already proved:
    [fs_file_file_envp_core] is [fs_file_file_core], and the injectivity
    in the contents that both the counting and the duplicate-freedom
    arguments spend is [file_core_inj] unchanged. *)
Definition file_envp_core (argv : list (list byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : list byte) (es : list (list byte)) (d : list byte)
    : FinCore :=
  file_core argv es fs0 pth s d.

Lemma fs_file_file_envp_core : forall argv fs0 pth s es d,
  fs_file pth (core_fs (file_envp_core argv fs0 pth s es d)) = d.
Proof.
  intros argv fs0 pth s es d. apply fs_file_file_core.
Qed.

Lemma core_envp_file_envp_core : forall argv fs0 pth s es d,
  core_envp (file_envp_core argv fs0 pth s es d) = es.
Proof. reflexivity. Qed.

(** THE WEIGHT.  Zero unless the core's argv, standard input and the rest
    of its file system are the fixed ones; otherwise the environment's
    weight times the geometric weight of its input file's length.

    It is [envp_geo_weight] WITH ITS STANDARD-INPUT FACTOR REPLACED, and
    that is the whole difference: [envp_point r q_e] on the environment
    coordinate is the same object, spread by the same two nested
    memoryless sources, and [geo_point p_stop] is applied to
    [length (fs_file pth (core_fs c))] where the other family applies it
    to [length (core_stdin c)].  A core with entries [e_1 ... e_k] and an
    input file of [n] bytes weighs

      [r * (1 - r) ^ k * Prod_i geo_point q_e |e_i| * geo_point p_stop n]

    ([file_envp_geo_weight_closed_form]), and the declared mass is [1].

    WHY BOTH COORDINATES AT ONCE, rather than mixing [file_geometric]
    with [stdin_envp_geometric] through [cd_mix2]: a mixture of the two
    would put weight on cores varying the file at the CANONICAL
    environment and on cores varying the environment at the CANONICAL
    file, and none at all on a core varying both.  A defect reachable
    only from a non-canonical environment AND a particular input file
    would still sit in a null set.  This family is the product measure,
    so it does not. *)
Definition file_envp_geo_weight (p r q : Q) (argv : list (list byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : list byte) (c : FinCore) : Q :=
  if decide (c = file_envp_core argv fs0 pth s (core_envp c)
                   (fs_file pth (core_fs c)))
  then (envp_point r q (core_envp c)
        * geo_point p (length (fs_file pth (core_fs c))))%Q
  else 0%Q.

Lemma file_envp_geo_weight_match : forall p r q argv fs0 pth s es d,
  file_envp_geo_weight p r q argv fs0 pth s
    (file_envp_core argv fs0 pth s es d)
    = (envp_point r q es * geo_point p (length d))%Q.
Proof.
  intros p r q argv fs0 pth s es d. unfold file_envp_geo_weight.
  rewrite fs_file_file_envp_core, core_envp_file_envp_core.
  destruct (decide _) as [_ | Hne]; [reflexivity | congruence].
Qed.

Lemma file_envp_geo_weight_mismatch : forall p r q argv fs0 pth s c,
  c <> file_envp_core argv fs0 pth s (core_envp c) (fs_file pth (core_fs c)) ->
  file_envp_geo_weight p r q argv fs0 pth s c = 0%Q.
Proof.
  intros p r q argv fs0 pth s c Hne. unfold file_envp_geo_weight.
  destruct (decide _) as [Heq | _]; [congruence | reflexivity].
Qed.

(** THE FAMILY'S FORMULA, all six factors visible at once, stated for the
    reason [envp_geo_weight_closed_form] is: the specification is quoted
    in that shape and a reader should be able to check the definition
    against it without unfolding anything. *)
Lemma file_envp_geo_weight_closed_form : forall p r q argv fs0 pth s es d,
  (file_envp_geo_weight p r q argv fs0 pth s
     (file_envp_core argv fs0 pth s es d)
     == r * Qpow (1 - r) (length es) * entries_geo_product q es
        * (p * Qpow (1 - p) (length d) * Qpow (1 # 256) (length d)))%Q.
Proof.
  intros p r q argv fs0 pth s es d.
  rewrite file_envp_geo_weight_match, envp_point_closed_form,
    geo_point_closed_form.
  ring.
Qed.

Lemma file_envp_geo_weight_nonneg : forall p r q argv fs0 pth s,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= r)%Q -> (r <= 1)%Q ->
  (0 <= q)%Q -> (q <= 1)%Q ->
  forall c, (0 <= file_envp_geo_weight p r q argv fs0 pth s c)%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 c.
  unfold file_envp_geo_weight.
  destruct (decide _) as [_ | _]; [| apply Qle_refl].
  apply Qmult_le_0_compat;
    [apply envp_point_nonneg | apply geo_point_nonneg]; assumption.
Qed.

(** The distribution.  Mass [1] is DECLARED, as everywhere in this file.
    The six side conditions are constructor arguments for the reason
    [stdin_envp_geometric]'s six are: [cd_nonneg] is a field.  None of
    the three STRICT inequalities is demanded, for the reason none is
    demanded there — nothing the constructor needs uses them, and the
    lower certificate that does asks for all three as hypotheses of its
    own statement. *)
Definition file_envp_geometric (p r q : Q) (argv : list (list byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : list byte)
    (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q)
    (Hr0 : (0 <= r)%Q) (Hr1 : (r <= 1)%Q)
    (Hq0 : (0 <= q)%Q) (Hq1 : (q <= 1)%Q) : CoreDistribution :=
  mkCoreDistribution (file_envp_geo_weight p r q argv fs0 pth s) 1
    (file_envp_geo_weight_nonneg p r q argv fs0 pth s
       Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).

(* =========================================================================
   The two coordinates, recombined
   ========================================================================= *)

(** Every core over the fixed argv, base file system and standard input
    whose environment comes from [A] and whose file contents come from
    [B].

    A core of this family is a PAIR and the weight is one factor per
    coordinate, so the enumeration is the product of the two
    coordinates' enumerations and its sum is the product of their sums
    ([qsum_file_envp_product]).  That identity is the only place
    the coordinates meet, and every bound below is assembled from an envp
    bound and a file-contents bound proved apart — the envp ones being
    [envp_enum_sum_le] and the entry-count machinery the envp-varying
    family already proved, and the file-contents ones being the byte-list
    sums [file_geometric] already reuses. *)
Definition file_envp_product (argv : list (list byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : list byte)
    (A : list (list (list byte))) (B : list (list byte)) : list FinCore :=
  List.flat_map (fun es => List.map (file_envp_core argv fs0 pth s es) B) A.

Lemma In_file_envp_product : forall argv fs0 pth s A B es d,
  List.In es A -> List.In d B ->
  List.In (file_envp_core argv fs0 pth s es d)
    (file_envp_product argv fs0 pth s A B).
Proof.
  intros argv fs0 pth s A B es d HA HB. apply List.in_flat_map. exists es.
  split; [exact HA | apply List.in_map; exact HB].
Qed.

Lemma qsum_file_envp_block : forall p r q argv fs0 pth s es B,
  (qsum (file_envp_geo_weight p r q argv fs0 pth s)
     (List.map (file_envp_core argv fs0 pth s es) B)
     == qsum (fun d => geo_point p (length d)) B * envp_point r q es)%Q.
Proof.
  intros p r q argv fs0 pth s es B. rewrite qsum_map.
  rewrite (qsum_ext (fun d => file_envp_geo_weight p r q argv fs0 pth s
                                  (file_envp_core argv fs0 pth s es d))
             (fun d => (envp_point r q es * geo_point p (length d))%Q))
    by (intros d _; rewrite file_envp_geo_weight_match; reflexivity).
  rewrite (qsum_scale (envp_point r q es)
             (fun d => geo_point p (length d)) B).
  ring.
Qed.

Lemma qsum_file_envp_product : forall p r q argv fs0 pth s A B,
  (qsum (file_envp_geo_weight p r q argv fs0 pth s)
     (file_envp_product argv fs0 pth s A B)
     == qsum (envp_point r q) A
        * qsum (fun d => geo_point p (length d)) B)%Q.
Proof.
  intros p r q argv fs0 pth s A B.
  unfold file_envp_product.
  rewrite qsum_flat_map. cbv beta.
  rewrite (qsum_ext
             (fun es => qsum (file_envp_geo_weight p r q argv fs0 pth s)
                          (List.map (file_envp_core argv fs0 pth s es) B))
             (fun es => (qsum (fun d => geo_point p (length d)) B
                         * envp_point r q es)%Q))
    by (intros es _; apply qsum_file_envp_block).
  rewrite (qsum_scale (qsum (fun d => geo_point p (length d)) B)
             (envp_point r q) A).
  ring.
Qed.

(** The product of two duplicate-free enumerations repeats nothing: the
    blocks are duplicate-free because a core determines its file contents
    ([file_core_inj]), and two blocks are disjoint because a core
    determines its environment.  Only the lower certificate needs this —
    the bounds are proved against a containing list nobody has to show
    duplicate-free. *)
Lemma NoDup_file_envp_product : forall argv fs0 pth s A B,
  List.NoDup A -> List.NoDup B ->
  List.NoDup (file_envp_product argv fs0 pth s A B).
Proof.
  intros argv fs0 pth s A B HA HB. unfold file_envp_product.
  apply NoDup_flat_map; [exact HA | |].
  - intros es _. apply NoDup_map_inj; [| exact HB].
    intros x y _ _ Heq. exact (file_core_inj _ _ _ _ _ _ _ Heq).
  - intros es1 es2 c _ _ H1 H2.
    apply List.in_map_iff in H1 as [d1 [Hd1 _]].
    apply List.in_map_iff in H2 as [d2 [Hd2 _]].
    rewrite <- Hd1 in Hd2. apply (f_equal core_envp) in Hd2.
    rewrite !core_envp_file_envp_core in Hd2. symmetry. exact Hd2.
Qed.

(* =========================================================================
   The cylinder bound over cores
   ========================================================================= *)

(** The cores this bound is about: the fixed argv, base file system and
    standard input, an environment EXTENDING [es] and file contents
    EXTENDING [bs].  Two existentials rather than a conjunction of four
    tests, for the reason [in_envp_stdin_cylinder] is two. *)
Definition in_file_envp_cylinder (argv : list (list byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : list byte) (es : list (list byte)) (bs : list byte)
    (c : FinCore) : Prop :=
  exists eext ext, c = file_envp_core argv fs0 pth s (es ++ eext) (bs ++ ext).

(** The cylinder's mass: the product of what the two coordinates
    contribute, [envp_factor] on one and [geo_mass] on the other. *)
Definition file_envp_geometric_cylinder_mass (p r q : Q)
    (es : list (list byte)) (bs : list byte) : Q :=
  (envp_factor r q es * geo_mass p (length bs))%Q.

Lemma file_envp_geometric_cylinder_mass_closed_form : forall p r q es bs,
  (file_envp_geometric_cylinder_mass p r q es bs
     == Qpow (1 - r) (length es) * entries_geo_product q es
        * (Qpow (1 - p) (length bs) * Qpow (1 # 256) (length bs)))%Q.
Proof.
  intros p r q es bs. unfold file_envp_geometric_cylinder_mass.
  rewrite envp_factor_closed_form, geo_mass_closed_form. ring.
Qed.

(** THE BOUND OVER CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.

    THREE DEPTHS are read off the task's own list, exactly as the
    envp-varying family reads three: how many entries an environment has
    ([cores_envp_depth]), how long an entry is ([cores_entry_depth]) and
    how long the input file is ([cores_file_depth], [file_geometric]'s,
    in the place [cores_stdin_depth] took there).  Each is a
    [List.list_max], so
    each exists because [Measure.weight_bound_T]'s lists are finite and
    for no other reason.  The product of the two coordinates'
    enumerations contains the list, its sum is the product of the two
    sums, and each factor has its bound already ([envp_enum_sum_le],
    [bytes_cyl_sum_le]). *)
Lemma file_envp_geo_weight_cylinder_bound : forall p r q argv fs0 pth s,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= r)%Q -> (r <= 1)%Q ->
  (0 <= q)%Q -> (q <= 1)%Q ->
  forall es bs cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> in_file_envp_cylinder argv fs0 pth s es bs c) ->
    (qsum (file_envp_geo_weight p r q argv fs0 pth s) cs
       <= file_envp_geometric_cylinder_mass p r q es bs)%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs cs Hnd Hcyl.
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (file_envp_product argv fs0 pth s
                  (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs))
                  (bytes_cyl bs (cores_file_depth pth cs))))
    | rewrite qsum_file_envp_product;
      unfold file_envp_geometric_cylinder_mass;
      apply Qmult_le_compat_nonneg;
      [ split;
        [ apply qsum_nonneg; intros x _; apply envp_point_nonneg; assumption
        | apply envp_enum_sum_le; assumption ]
      | split;
        [ apply qsum_nonneg; intros x _; apply geo_point_nonneg; assumption
        | apply bytes_cyl_sum_le; assumption ] ] ].
  - apply file_envp_geo_weight_nonneg; assumption.
  - exact Hnd.
  - intros c Hc. destruct (Hcyl c Hc) as [eext [ext Heq]].
    assert (Henvp := cores_envp_depth_ge cs c Hc).
    assert (Hfile := cores_file_depth_ge pth cs c Hc).
    rewrite Heq in Henvp, Hfile.
    rewrite core_envp_file_envp_core in Henvp.
    rewrite fs_file_file_envp_core in Hfile.
    rewrite !List.length_app in Henvp, Hfile.
    rewrite Heq. apply In_file_envp_product.
    + apply envp_enum_complete; [lia |].
      intros e He. apply (cores_entry_depth_gt cs c e Hc).
      rewrite Heq, core_envp_file_envp_core.
      apply List.in_or_app. right. exact He.
    + apply bytes_cyl_In. lia.
Qed.

(* =========================================================================
   The file-and-environment family's exports
   ========================================================================= *)

(** THE EXPORT: a list of records with duplicate-free cores, all lying in
    the cylinder over an environment prefix and a file-contents prefix,
    weighs at most that cylinder's mass.

    This is the statement the family exists for.  A fire set described by
    "the environment begins with these entries and the input file begins
    with these bytes" is charged a number that depends on BOTH, where
    [file_geometric_bound] would charge the file cylinder's whole mass at
    the canonical environment and nothing anywhere else, and
    [stdin_envp_geometric_bound] would charge nothing at all at any core
    whose file system is not the fixed one. *)
Lemma file_envp_geometric_bound :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_envp_cylinder argv fs0 pth s es bs (fin_core f)) ->
  (core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= file_envp_geometric_cylinder_mass p r q es bs)%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs l Hnd Hcyl.
  cbn [cd_weight file_envp_geometric]. rewrite core_sum_map_fin_core.
  apply file_envp_geo_weight_cylinder_bound; try assumption.
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. apply Hcyl. exact Hin.
Qed.

(** The launch-time test as a boolean, so that [List.filter] can use it.
    It is [matches_file_env] with the environment left free: this family
    fixes argv, standard input and the base file system, so the equation
    a core has to satisfy in order to weigh anything is the template with
    BOTH its envp and its file contents plugged in. *)
Definition matches_argv_file_fs (argv : list (list byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : list byte) (c : FinCore) : bool :=
  if decide (c = file_envp_core argv fs0 pth s (core_envp c)
                   (fs_file pth (core_fs c)))
  then true else false.

Lemma matches_argv_file_fs_false : forall argv fs0 pth s c,
  matches_argv_file_fs argv fs0 pth s c = false ->
  c <> file_envp_core argv fs0 pth s (core_envp c) (fs_file pth (core_fs c)).
Proof.
  intros argv fs0 pth s c H. unfold matches_argv_file_fs in H.
  destruct (decide _) as [_ | Hne]; [discriminate H | exact Hne].
Qed.

Lemma matches_argv_file_fs_true : forall argv fs0 pth s c,
  matches_argv_file_fs argv fs0 pth s c = true ->
  c = file_envp_core argv fs0 pth s (core_envp c) (fs_file pth (core_fs c)).
Proof.
  intros argv fs0 pth s c H. unfold matches_argv_file_fs in H.
  destruct (decide _) as [Heq | _]; [exact Heq | discriminate H].
Qed.

(** THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE, exactly as the
    other three families slacken theirs: each record is in the cylinder
    OR its core misses the fixed argv, standard input or base file system
    and therefore weighs nothing. *)
Lemma file_envp_geometric_bound_or_off_environment :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_file_envp_cylinder argv fs0 pth s es bs (fin_core f)
     \/ matches_argv_file_fs argv fs0 pth s (fin_core f) = false) ->
  (core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= file_envp_geometric_cylinder_mass p r q es bs)%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs l Hnd Hor.
  cbn [cd_weight file_envp_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_argv_file_fs argv fs0 pth s))
    by (intros c Hc;
        rewrite (file_envp_geo_weight_mismatch p r q argv fs0 pth s c
                   (matches_argv_file_fs_false _ _ _ _ _ Hc)); reflexivity).
  apply file_envp_geo_weight_cylinder_bound; try assumption.
  - apply List.NoDup_filter. exact Hnd.
  - intros c Hc. apply List.filter_In in Hc as [Hin Hm].
    apply List.in_map_iff in Hin as [f [Hf Hinl]].
    destruct (Hor f Hinl) as [Hcyl | Hoff].
    + rewrite <- Hf. exact Hcyl.
    + rewrite Hf in Hoff. rewrite Hoff in Hm. discriminate Hm.
Qed.

(** UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass [1].  It is the disjunctive bound at the two EMPTY prefixes, and
    the whole content is that the disjunction is EXHAUSTIVE there.  Both
    cylinder masses at the empty prefix are [1], one because
    [envp_factor] of no entries is and one because [Qpow] at exponent
    zero is. *)
Lemma file_envp_geometric_mass_upper :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= cd_mass (file_envp_geometric p r q argv fs0 pth s
                   Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 l Hnd.
  cbn [cd_mass file_envp_geometric].
  apply (Qle_trans _ (file_envp_geometric_cylinder_mass p r q [] [])).
  - apply file_envp_geometric_bound_or_off_environment; [exact Hnd |].
    intros f Hf.
    destruct (matches_argv_file_fs argv fs0 pth s (fin_core f)) eqn:Hm.
    + left. exists (core_envp (fin_core f)),
                   (fs_file pth (core_fs (fin_core f))).
      cbn [List.app]. apply matches_argv_file_fs_true. exact Hm.
    + right. reflexivity.
  - apply Qle_of_Qeq.
    unfold file_envp_geometric_cylinder_mass, geo_mass.
    cbn [length envp_factor]. rewrite Qpow_0. ring.
Qed.

(* =========================================================================
   Bounds that charge the environment nothing
   ========================================================================= *)

(** A list whose cores match the fixed argv, standard input and base file
    system and whose file contents all come from a given enumeration [B]
    weighs at most what [B] weighs — the environment coordinate is
    charged [1], its whole declared mass, and nothing about the
    environment is assumed.

    This is the shape both remaining bounds take, and it is
    [envp_geo_weight_stdin_family_bound] on the other coordinate.  A task
    that knows nothing about the environments in its fire set gets
    exactly the bound [file_geometric] would have given it: mixing an
    envp-varying component in must not make a file-only argument WORSE. *)
Lemma file_envp_geo_weight_file_family_bound : forall p r q argv fs0 pth s,
  (0 <= p)%Q -> (p <= 1)%Q -> (0 <= r)%Q -> (r <= 1)%Q ->
  (0 <= q)%Q -> (q <= 1)%Q ->
  forall (B : list (list byte)) (SB : Q) cs,
    (qsum (fun d => geo_point p (length d)) B <= SB)%Q ->
    List.NoDup cs ->
    (forall c, List.In c cs ->
       c = file_envp_core argv fs0 pth s (core_envp c)
             (fs_file pth (core_fs c))
       /\ List.In (fs_file pth (core_fs c)) B) ->
    (qsum (file_envp_geo_weight p r q argv fs0 pth s) cs <= SB)%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 B SB cs HB Hnd Hall.
  eapply Qle_trans;
    [ apply (qsum_core_incl_le _ _
               (file_envp_product argv fs0 pth s
                  (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs))
                  B))
    | rewrite qsum_file_envp_product;
      apply (Qle_trans _ (1 * SB)%Q); [| apply Qle_of_Qeq; ring];
      apply Qmult_le_compat_nonneg;
      [ split;
        [ apply qsum_nonneg; intros x _; apply envp_point_nonneg; assumption
        | apply (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ []) ]
      | split;
        [ apply qsum_nonneg; intros x _; apply geo_point_nonneg; assumption
        | exact HB ] ] ].
  - apply file_envp_geo_weight_nonneg; assumption.
  - exact Hnd.
  - intros c Hc. destruct (Hall c Hc) as [Hmatch Hfile].
    assert (Hins : List.In ([] ++ core_envp c)
                     (envp_enum [] (cores_envp_depth cs)
                        (cores_entry_depth cs))).
    { apply envp_enum_complete; [apply cores_envp_depth_ge; exact Hc |].
      intros e He. apply (cores_entry_depth_gt cs c e Hc). exact He. }
    cbn [List.app] in Hins.
    assert (Hprod := In_file_envp_product argv fs0 pth s
                       (envp_enum [] (cores_envp_depth cs)
                          (cores_entry_depth cs)) B
                       (core_envp c) (fs_file pth (core_fs c)) Hins Hfile).
    rewrite <- Hmatch in Hprod. exact Hprod.
Qed.

(** THE LENGTH SLICE: a list drawn from one file-length slice weighs at
    most [p_stop * (1 - p_stop) ^ n], with no [1/256] left in it and
    nothing charged for the environment.  It is
    [file_geometric_slice_bound]'s constant exactly, and the hypothesis
    does NOT fix the environment: the records may carry any envp at all.

    WHAT IS NOT CLAIMED, and the difference from [file_geometric] is
    worth naming rather than leaving to be inferred from an absent
    lemma: this constant is not pinned as ATTAINED, and no sharpness
    lemma accompanies it.  There the slice is finite and
    [file_geometric_slice_bound_attained] reaches the constant outright.
    Here a slice at a fixed file length still holds one core per
    ENVIRONMENT, of which there are infinitely many carrying positive
    weight whenever [r < 1] ([file_envp_geometric_envp_bites] at one of
    them), so the counting argument does not run and nothing weaker is
    passed off as it.  The same absence, for the same reason, is
    documented at [stdin_envp_geometric_slice_bound]. *)
Lemma file_envp_geometric_slice_bound :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_core f = file_envp_core argv fs0 pth s (fin_envp f)
                    (fs_file pth (fin_image_fs f))
     /\ length (fs_file pth (fin_image_fs f)) = n) ->
  (core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= p * Qpow (1 - p) n)%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 n l Hnd Hall.
  cbn [cd_weight file_envp_geometric]. rewrite core_sum_map_fin_core.
  apply (file_envp_geo_weight_file_family_bound p r q argv fs0 pth s
           Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 (byte_lists n));
    [ apply Qle_of_Qeq; apply byte_lists_sum | exact Hnd |].
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  destruct (Hall f Hin) as [Henv Hlen]. subst c. split; [exact Henv |].
  cbn [fin_core core_fs]. rewrite <- Hlen. apply byte_lists_complete.
Qed.

(** A list confined to input files of length at most [n] weighs at most
    [1 - (1 - p_stop) ^ (n + 1)] — the partial sum at its own horizon,
    and again the environment is charged nothing.  It MISSES THE TAIL,
    and the tail is what [file_envp_geometric_mass_not_attained] below is
    made of.

    THE ENVIRONMENT'S SHARE OF THIS CONSTANT IS LOOSE for [r < 1], and
    the reason is the one given at
    [stdin_envp_geometric_bound_by_max_length]: the bound charges that
    coordinate its whole declared [1], and a finite list collects all of
    it only when the environment mass sits on finitely many
    environments, which happens exactly at [r = 1]
    ([file_envp_geo_weight_collapses_at_one_r]).  So an attainment lemma
    here would be false rather than missing, and a task wanting the
    difference should charge the environment through
    [file_envp_geometric_bound] instead, which does depend on it. *)
Lemma file_envp_geometric_bound_by_max_length :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> (length (fs_file pth (fin_image_fs f)) <= n)%nat) ->
  (core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
                          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
     <= 1 - Qpow (1 - p) (S n))%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 n l Hnd Hlen.
  cbn [cd_weight file_envp_geometric]. rewrite core_sum_map_fin_core.
  rewrite (qsum_filter _ (matches_argv_file_fs argv fs0 pth s))
    by (intros c Hc;
        rewrite (file_envp_geo_weight_mismatch p r q argv fs0 pth s c
                   (matches_argv_file_fs_false _ _ _ _ _ Hc)); reflexivity).
  apply (file_envp_geo_weight_file_family_bound p r q argv fs0 pth s
           Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 (short_inputs (S n)));
    [ apply Qle_of_Qeq;
      rewrite short_inputs_sum; apply geo_prefix_sum_closed
    | apply List.NoDup_filter; exact Hnd |].
  intros c Hc. apply List.filter_In in Hc as [Hin Hm].
  split; [apply matches_argv_file_fs_true; exact Hm |].
  apply short_inputs_complete.
  apply List.in_map_iff in Hin as [f [Hf Hinl]].
  assert (Hle := Hlen f Hinl). rewrite <- Hf. cbn [fin_core core_fs]. lia.
Qed.

(* =========================================================================
   ... and this mass is a SUPREMUM and not a maximum either
   ========================================================================= *)

(** For [p_stop < 1] NO admissible list weighs the declared mass.  The
    proof is [file_geometric_mass_not_attained]'s, unchanged: the list's
    own longest input file is a horizon, and beyond it sits a positive
    tail the list does not collect.

    Only [p_stop < 1] is asked for.  The environment coordinate needs no
    hypothesis at all, for the reason
    [stdin_envp_geometric_mass_not_attained] needs none: the shortfall is
    already there on the file axis, so degenerate [r] or [q_e] can only
    make it larger. *)
Lemma file_envp_geometric_mass_not_attained :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
                            Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
       < cd_mass (file_envp_geometric p r q argv fs0 pth s
                    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hlt l Hnd.
  cbn [cd_mass file_envp_geometric].
  pose (n := List.list_max
               (List.map (fun f => length (fs_file pth (fin_image_fs f))) l)).
  apply (Qle_lt_trans _ (1 - Qpow (1 - p) (S n))%Q).
  - apply file_envp_geometric_bound_by_max_length; [exact Hnd |].
    intros f Hf. apply list_max_ge. apply List.in_map_iff.
    exists f. split; [reflexivity | exact Hf].
  - apply (proj2 (Qlt_minus_iff (1 - Qpow (1 - p) (S n)) 1)).
    apply (Qlt_le_trans _ (Qpow (1 - p) (S n))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qpow_pos. apply (Qlt_minus_iff p 1). exact Hlt.
Qed.

(** The same fact under the name a reader looks for. *)
Lemma file_envp_geometric_mass_supremum_not_maximum :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  (p < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    ~ (core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
                              Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l
         == cd_mass (file_envp_geometric p r q argv fs0 pth s
                       Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hlt l Hnd.
  apply Qlt_not_eq.
  apply file_envp_geometric_mass_not_attained; assumption.
Qed.

(* =========================================================================
   The lower certificate for [file_envp_geometric]
   ========================================================================= *)

(** THE WITNESS FAMILY: over the fixed argv, base file system and
    standard input, one record per (environment, file contents) pair
    drawn from the two prefix families.  [envps_upto] and [short_inputs]
    are the envp-varying family's own enumerations, unchanged; only the
    embedding into cores is this family's, and the product is
    duplicate-free because both coordinates are.

    As everywhere in this file, these records are NOT claimed valid and
    NOT claimed rejected by anything. *)
Definition file_envp_geo_lower_witness (argv : list (list byte))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : list byte) (M L k : nat)
    : list FinProcInput :=
  List.map core_input
    (file_envp_product argv fs0 pth s (envps_upto L M) (short_inputs k)).

Lemma map_fin_core_file_envp_geo_lower_witness :
  forall argv fs0 pth s M L k,
  List.map fin_core (file_envp_geo_lower_witness argv fs0 pth s M L k)
    = file_envp_product argv fs0 pth s (envps_upto L M) (short_inputs k).
Proof.
  intros argv fs0 pth s M L k. unfold file_envp_geo_lower_witness.
  apply map_fin_core_core_input.
Qed.

Lemma file_envp_geo_lower_witness_nodup : forall argv fs0 pth s M L k,
  List.NoDup
    (List.map fin_core (file_envp_geo_lower_witness argv fs0 pth s M L k)).
Proof.
  intros argv fs0 pth s M L k.
  rewrite map_fin_core_file_envp_geo_lower_witness.
  apply NoDup_file_envp_product;
    [apply envps_upto_nodup | apply short_inputs_nodup].
Qed.

(** THE WITNESS, at each triple of depths: an admissible list weighing
    exactly the product of the two coordinates' partial sums.  No
    hypothesis beyond the constructor's own is needed here; all three
    strictnesses enter one lemma later, where the depths have to be
    CHOSEN to meet a target. *)
Lemma file_envp_geometric_mass_lower_witness :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k,
  List.NoDup
    (List.map fin_core (file_envp_geo_lower_witness argv fs0 pth s M L k))
  /\ (core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
                             Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))
        (file_envp_geo_lower_witness argv fs0 pth s M L k)
        == envp_prefix_sum r (1 - Qpow (1 - q) L) M
           * (1 - Qpow (1 - p) k))%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k.
  split; [apply file_envp_geo_lower_witness_nodup |].
  cbn [cd_weight file_envp_geometric].
  rewrite core_sum_map_fin_core, map_fin_core_file_envp_geo_lower_witness.
  rewrite qsum_file_envp_product.
  rewrite qsum_envp_point_envps_upto, short_inputs_sum, geo_prefix_sum_closed.
  reflexivity.
Qed.

(** THE LOWER CERTIFICATE: for every margin [eps] there is an admissible
    list weighing at least the declared mass minus that margin.  With
    [file_envp_geometric_mass_upper] above it, the declared [1] is the
    least upper bound of the admissible partial sums — approached but, by
    [file_envp_geometric_mass_not_attained], never met.

    Each strictness buys exactly one depth and the order matters,
    exactly as at [stdin_envp_geometric_mass_lower_certificate] — and
    for that reason it is not spelled out a second time here.
    [envp_stdin_depths_above] chooses the three depths and
    [envp_stdin_margin_at_depths] does the arithmetic; both are stated
    over [envp_prefix_sum] and two powers with no distribution in sight,
    so this family consumes them unchanged.

    That the file-varying family meets the very same numbers as the
    standard-input one is not a coincidence a reader has to check: it is
    the shape of [file_envp_geometric_mass_lower_witness], whose partial
    sum is literally the same expression in [M], [L] and [k].  Before
    those two were factored out this proof was a ninety-line copy of its
    sibling, and a copy of an arithmetic argument is a thing that
    drifts.

    Nothing here is a limit and nothing is approximated: a margin is
    asked for, three natural numbers are produced, and the finite list
    they name is exhibited. *)
Lemma file_envp_geometric_mass_lower_certificate :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 eps,
  (0 < p)%Q -> (0 < r)%Q -> (0 < q)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (cd_mass (file_envp_geometric p r q argv fs0 pth s
                   Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) - eps
          <= core_sum (cd_weight (file_envp_geometric p r q argv fs0 pth s
                                    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)) l)%Q.
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 eps
    Hppos Hrpos Hqpos Heps.
  destruct (envp_stdin_depths_above p r q eps 0 0
              Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps)
    as [M [L [k [_ [_ [Hsum _]]]]]].
  exists (file_envp_geo_lower_witness argv fs0 pth s M L k).
  split; [apply file_envp_geo_lower_witness_nodup |].
  rewrite (proj2 (file_envp_geometric_mass_lower_witness
                    p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k)).
  cbn [cd_mass file_envp_geometric].
  apply envp_stdin_margin_at_depths; assumption.
Qed.

(* =========================================================================
   Non-vacuity: the environment carries mass here too
   ========================================================================= *)

(** [file_geo_weight]'s envp instance, stated because the bite below
    needs it.  It is the same [file_geo_weight_mismatch] the argv
    instance goes through. *)
Lemma file_geo_weight_off_envp_zero : forall p argv envp fs0 pth s c,
  core_envp c <> envp -> file_geo_weight p argv envp fs0 pth s c = 0%Q.
Proof.
  intros p argv envp fs0 pth s c Hne. apply file_geo_weight_mismatch.
  intros Heq. apply (f_equal core_envp) in Heq.
  cbn [file_core core_envp] in Heq. exact (Hne Heq).
Qed.

Lemma file_envp_geo_weight_off_argv_zero : forall p r q argv fs0 pth s c,
  core_argv c <> argv -> file_envp_geo_weight p r q argv fs0 pth s c = 0%Q.
Proof.
  intros p r q argv fs0 pth s c Hne. apply file_envp_geo_weight_mismatch.
  intros Heq. apply (f_equal core_argv) in Heq.
  cbn [file_envp_core file_core core_argv] in Heq. exact (Hne Heq).
Qed.

(** A core over a NON-CANONICAL launch-time environment carrying the
    input file: one entry, the single byte [A], and the empty file at
    [file_example_path].  As at [envp_example_named] it is not claimed
    valid; it is the point of [FinInput.FinCore] at which the two file
    families disagree. *)
Definition file_envp_example_named : FinCore :=
  file_envp_core [] [] file_example_path [] [[Z_to_bv 8 65]] [].

(** THE BITE THIS FAMILY EXISTS FOR, both halves on ONE core.
    [file_geometric] over the empty environment weighs
    [file_envp_example_named] exactly zero — its envp is not the fixed
    one — while [file_envp_geometric] weighs it strictly positively.

    It is [stdin_envp_geometric_envp_bites] on the file coordinate and
    the reading is the same: under a distribution built from
    [file_geometric] alone, a fire set living at cores like this one lies
    in a NULL set, so a [Measure.weight_bound_T] claim about it is
    satisfied vacuously.  Under this family it is not.  The
    environment axis is kept because many programs consult the
    environment somewhere in library code; others are
    environment-blind by construction, and for those the envp
    coordinate costs a factor and buys nothing, which is why this family
    is offered ALONGSIDE [file_geometric] rather than in place of it. *)
Lemma file_envp_geometric_envp_bites :
  forall p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  (0 < p)%Q -> (p < 1)%Q -> (0 < r)%Q -> (r < 1)%Q ->
  (0 < q)%Q -> (q < 1)%Q ->
  cd_weight (file_geometric p [] [] [] file_example_path [] Hp0 Hp1)
    file_envp_example_named = 0%Q
  /\ (0 < cd_weight (file_envp_geometric p r q [] [] file_example_path []
                       Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) file_envp_example_named)%Q.
Proof.
  intros p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hppos Hplt Hrpos Hrlt Hqpos Hqlt.
  split.
  - cbn [cd_weight file_geometric]. apply file_geo_weight_off_envp_zero.
    unfold file_envp_example_named.
    rewrite core_envp_file_envp_core. discriminate.
  - cbn [cd_weight file_envp_geometric]. unfold file_envp_example_named.
    rewrite file_envp_geo_weight_match.
    apply Qmult_lt_0_compat;
      [apply envp_point_pos; assumption | apply geo_point_pos; assumption].
Qed.

(** ... and the family is still not constant: a core whose argv misses
    the fixed one weighs exactly zero.  Both halves are needed for the
    reason [stdin_envp_geometric_bites] needs both. *)
Lemma file_envp_geometric_bites :
  forall p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  (0 < p)%Q -> (p < 1)%Q -> (0 < r)%Q -> (r < 1)%Q ->
  (0 < q)%Q -> (q < 1)%Q ->
  (0 < cd_weight (file_envp_geometric p r q [] [] file_example_path []
                    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) file_example_core)%Q
  /\ cd_weight (file_envp_geometric p r q [] [] file_example_path []
                  Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) geo_example_other = 0%Q.
Proof.
  intros p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hppos Hplt Hrpos Hrlt Hqpos Hqlt.
  cbn [cd_weight file_envp_geometric]. split.
  - unfold file_example_core.
    change (file_core [] [] [] file_example_path [] [])
      with (file_envp_core [] [] file_example_path [] [] []).
    rewrite file_envp_geo_weight_match.
    apply Qmult_lt_0_compat;
      [apply envp_point_pos; assumption | apply geo_point_pos; assumption].
  - apply file_envp_geo_weight_off_argv_zero.
    unfold geo_example_other. cbn [core_argv]. discriminate.
Qed.

(* =========================================================================
   Non-vacuity: [List.NoDup] is load-bearing here too
   ========================================================================= *)

(** The member of the family at [p_stop = r = q_e = 1]: stop immediately
    on every axis.  It is the point mass on the core with no environment
    and an empty input file, it is admitted by the constructor, and it is
    what makes the refutation below closed arithmetic instead of open
    terms. *)
Definition file_envp_point_cd : CoreDistribution :=
  file_envp_geometric 1 1 1 [] [] file_example_path []
    Qle_0_1 (Qle_refl 1) Qle_0_1 (Qle_refl 1) Qle_0_1 (Qle_refl 1).

(** THE [List.NoDup] HYPOTHESIS IS LOAD-BEARING for this family's
    cylinder bound, and this is [file_geometric_bound_needs_nodup]
    transposed: offer the same core twice — two records, so the list is
    duplicate-free as a list of RECORDS, and both lie in the cylinder
    over the two empty prefixes — and the sum is [2] against a cylinder
    mass of [1].  All three conjuncts are needed, for the reasons the
    baseline lemma gives. *)
Lemma file_envp_geometric_bound_needs_nodup :
  ~ List.NoDup (List.map fin_core [file_empty_input; file_empty_input])
  /\ (forall f, List.In f [file_empty_input; file_empty_input] ->
        in_file_envp_cylinder [] [] file_example_path [] [] []
          (fin_core f))
  /\ ~ (core_sum (cd_weight file_envp_point_cd)
          [file_empty_input; file_empty_input]
          <= file_envp_geometric_cylinder_mass 1 1 1 [] [])%Q.
Proof.
  split; [| split].
  - intros Hnd. cbn [List.map] in Hnd.
    apply (proj1 (List.NoDup_cons_iff _ _)) in Hnd as [Hnin _].
    apply Hnin. left. reflexivity.
  - intros f Hf. destruct Hf as [Hf | [Hf | []]]; subst f;
      exists [], []; reflexivity.
  - intros Hle. apply (proj2 (Qle_bool_iff _ _)) in Hle.
    vm_compute in Hle. discriminate Hle.
Qed.

(* =========================================================================
   Family 2: the SIX degenerate members, each pinned
   ========================================================================= *)

(** EVERY ENDPOINT THE CONSTRUCTOR ADMITS, which is one more than the
    envp-varying family pins, because this family's file coordinate
    degenerates at [p_stop = 1] the way its envp coordinate degenerates
    at [q_e = 0] — there the [p_stop] axis is standard input and its
    collapse is [stdin_geometric]'s already-documented one, here it is
    the input file, the coordinate this family exists for.

    At [p_stop = 0] and at [r = 0] the weight vanishes identically —
    every list weighs nothing while the declared mass stays [1], so the
    lower certificate is false there and its hypotheses are not inherited
    caution.  At [q_e = 0], at [q_e = 1], at [r = 1] and at [p_stop = 1]
    the weight does NOT vanish, and those four are the interesting ones:
    the first three kill a whole class of non-empty environments, so the
    family collapses back towards [file_geometric] and is as blind to the
    launch-time environment as the family it extends; at the fourth every
    core whose INPUT FILE is non-empty weighs zero, so it goes blind to
    the coordinate both file families were built for.  Those four are
    the failure modes worth pinning, because they are the ones that would
    go unnoticed: the distribution is still non-zero, still sums
    correctly, still declares mass [1] honestly, and still measures
    nothing about the axis in question. *)
Lemma file_envp_geo_weight_zero_at_zero_p : forall r q argv fs0 pth s c,
  (file_envp_geo_weight 0 r q argv fs0 pth s c == 0)%Q.
Proof.
  intros r q argv fs0 pth s c. unfold file_envp_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  unfold geo_point. ring.
Qed.

Lemma file_envp_geo_weight_zero_at_zero_r : forall p q argv fs0 pth s c,
  (file_envp_geo_weight p 0 q argv fs0 pth s c == 0)%Q.
Proof.
  intros p q argv fs0 pth s c. unfold file_envp_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  unfold envp_point. ring.
Qed.

Lemma file_envp_geo_weight_zero_at_zero_q : forall p r argv fs0 pth s c,
  core_envp c <> [] -> (file_envp_geo_weight p r 0 argv fs0 pth s c == 0)%Q.
Proof.
  intros p r argv fs0 pth s c Hne. unfold file_envp_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  destruct (core_envp c) as [| e es];
    [exfalso; exact (Hne eq_refl) |].
  unfold envp_point. cbn [envp_factor]. unfold geo_point. ring.
Qed.

Lemma file_envp_geo_weight_collapses_at_one_p :
  forall r q argv fs0 pth s c,
  fs_file pth (core_fs c) <> [] ->
  (file_envp_geo_weight 1 r q argv fs0 pth s c == 0)%Q.
Proof.
  intros r q argv fs0 pth s c Hne. unfold file_envp_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  destruct (fs_file pth (core_fs c)) as [| b d];
    [exfalso; exact (Hne eq_refl) |].
  unfold geo_point, geo_mass. cbn [length Qpow]. ring.
Qed.

(** [r = 1] is stated as a COLLAPSE rather than as a blindness, which is
    the sharper form and the one [envp_geo_weight_collapses_at_one_r]
    takes: at [r = 1] this family IS [file_geometric] over the EMPTY
    launch-time environment, weight for weight and at every core,
    including the ones both weigh zero.  [r < 1] is therefore genuinely
    asked for, by [envp_point_pos] and through it by
    [file_envp_geometric_envp_bites] — the very lemma that says this
    family improves on the one it extends. *)
Lemma file_envp_geo_weight_collapses_at_one_r : forall p q argv fs0 pth s c,
  (file_envp_geo_weight p 1 q argv fs0 pth s c
     == file_geo_weight p argv [] fs0 pth s c)%Q.
Proof.
  intros p q argv fs0 pth s c.
  unfold file_envp_geo_weight, file_geo_weight, file_envp_core.
  destruct (decide (c = file_core argv (core_envp c) fs0 pth s
                          (fs_file pth (core_fs c)))) as [Hm | Hnm];
    destruct (decide (c = file_core argv [] fs0 pth s
                            (fs_file pth (core_fs c)))) as [He | Hne].
  - assert (Henv : core_envp c = [])
      by (apply (f_equal core_envp) in He;
          cbn [file_core core_envp] in He; exact He).
    rewrite Henv. unfold envp_point. cbn [envp_factor]. ring.
  - destruct (core_envp c) as [| e es];
      [exfalso; exact (Hne Hm) |].
    unfold envp_point. cbn [envp_factor]. ring.
  - exfalso. apply Hnm.
    assert (Henv : core_envp c = [])
      by (apply (f_equal core_envp) in He;
          cbn [file_core core_envp] in He; exact He).
    rewrite Henv. exact He.
  - reflexivity.
Qed.

Lemma file_envp_geometric_collapses_at_one_r :
  forall p q argv fs0 pth s Hp0 Hp1 Hq0 Hq1 c,
  (cd_weight (file_envp_geometric p 1 q argv fs0 pth s Hp0 Hp1
                Qle_0_1 (Qle_refl 1) Hq0 Hq1) c
     == cd_weight (file_geometric p argv [] fs0 pth s Hp0 Hp1) c)%Q.
Proof.
  intros p q argv fs0 pth s Hp0 Hp1 Hq0 Hq1 c.
  cbn [cd_weight file_envp_geometric file_geometric].
  apply file_envp_geo_weight_collapses_at_one_r.
Qed.

(** ... and the three blindnesses, in the shape
    [stdin_envp_geometric_envp_needs_positive_q] states its own.  Both
    forms are exported everywhere both exist: a reader asking "what goes
    wrong at this parameter" wants the blindness, and a reader asking
    "what does the family become" wants the collapse. *)
Lemma file_envp_geometric_envp_needs_r_below_one :
  forall p q argv fs0 pth s Hp0 Hp1 Hq0 Hq1 c,
  core_envp c <> [] ->
  (cd_weight (file_envp_geometric p 1 q argv fs0 pth s Hp0 Hp1
                Qle_0_1 (Qle_refl 1) Hq0 Hq1) c == 0)%Q.
Proof.
  intros p q argv fs0 pth s Hp0 Hp1 Hq0 Hq1 c Hne.
  rewrite file_envp_geometric_collapses_at_one_r.
  cbn [cd_weight file_geometric].
  rewrite (file_geo_weight_off_envp_zero p argv [] fs0 pth s c Hne).
  reflexivity.
Qed.

Lemma file_envp_geometric_envp_needs_positive_q :
  forall p r argv fs0 pth s Hp0 Hp1 Hr0 Hr1 c,
  core_envp c <> [] ->
  (cd_weight (file_envp_geometric p r 0 argv fs0 pth s Hp0 Hp1 Hr0 Hr1
                (Qle_refl 0) Qle_0_1) c == 0)%Q.
Proof.
  intros p r argv fs0 pth s Hp0 Hp1 Hr0 Hr1 c Hne.
  cbn [cd_weight file_envp_geometric].
  apply file_envp_geo_weight_zero_at_zero_q. exact Hne.
Qed.

(** [q_e = 1] is the SIXTH endpoint the constructor admits, and it fails
    the way [envp_geo_weight_zero_at_one_q] fails for the family this one
    extends: [geo_point 1 m] is zero for every [m >= 1], so an
    environment holding ANY non-empty entry weighs nothing while
    environments of empty entries keep their weight.  Since a real
    environment entry is a [NAME=value] string, the family is blind to
    every environment a program will actually see, and it has not gone
    quiet.

    As there, the hypothesis names a non-empty ENTRY and not a non-empty
    ENVIRONMENT — [[[]]] weighs a positive amount at [q_e = 1] — so this
    is not [file_envp_geometric_envp_needs_positive_q] with [0] replaced
    by [1].  The entry-product half of the weight is shared with the
    envp-varying family, so the arithmetic is shared too:
    [envp_factor_zero_at_one_q] is proved once and spent twice. *)
Lemma file_envp_geo_weight_zero_at_one_q : forall p r argv fs0 pth s c e,
  List.In e (core_envp c) -> e <> [] ->
  (file_envp_geo_weight p r 1 argv fs0 pth s c == 0)%Q.
Proof.
  intros p r argv fs0 pth s c e Hin Hne. unfold file_envp_geo_weight.
  destruct (decide _) as [_ | _]; [| reflexivity].
  unfold envp_point.
  rewrite (envp_factor_zero_at_one_q r (core_envp c) e Hin Hne). ring.
Qed.

Lemma file_envp_geometric_envp_needs_q_below_one :
  forall p r argv fs0 pth s Hp0 Hp1 Hr0 Hr1 c e,
  List.In e (core_envp c) -> e <> [] ->
  (cd_weight (file_envp_geometric p r 1 argv fs0 pth s Hp0 Hp1 Hr0 Hr1
                Qle_0_1 (Qle_refl 1)) c == 0)%Q.
Proof.
  intros p r argv fs0 pth s Hp0 Hp1 Hr0 Hr1 c e Hin Hne.
  cbn [cd_weight file_envp_geometric].
  exact (file_envp_geo_weight_zero_at_one_q p r argv fs0 pth s c e Hin Hne).
Qed.

(** ... and the hypothesis cannot be weakened here either, at the same
    two environments and the same [2 # 25], beside
    [envp_geo_weight_at_one_q_needs_a_non_empty_entry]. *)
Lemma file_envp_geo_weight_at_one_q_needs_a_non_empty_entry :
  (file_envp_geo_weight (1 # 2) (1 # 5) 1 [] [] file_example_path []
     file_envp_example_named == 0)%Q
  /\ (0 < file_envp_geo_weight (1 # 2) (1 # 5) 1 [] [] file_example_path []
            (file_envp_core [] [] file_example_path [] [[]] []))%Q.
Proof.
  split.
  - apply (file_envp_geo_weight_zero_at_one_q _ _ _ _ _ _ _
             [Z_to_bv 8 65]);
      [ unfold file_envp_example_named;
        rewrite core_envp_file_envp_core; left; reflexivity
      | intros H; discriminate H].
  - rewrite file_envp_geo_weight_match. vm_compute. reflexivity.
Qed.

Lemma file_envp_geometric_needs_p_below_one :
  forall r q argv fs0 pth s Hr0 Hr1 Hq0 Hq1 c,
  fs_file pth (core_fs c) <> [] ->
  (cd_weight (file_envp_geometric 1 r q argv fs0 pth s
                Qle_0_1 (Qle_refl 1) Hr0 Hr1 Hq0 Hq1) c == 0)%Q.
Proof.
  intros r q argv fs0 pth s Hr0 Hr1 Hq0 Hq1 c Hne.
  cbn [cd_weight file_envp_geometric].
  apply file_envp_geo_weight_collapses_at_one_p. exact Hne.
Qed.

(** THE STRICTNESS AT [p_stop] IS LOAD-BEARING for the lower certificate,
    pinned the way this file pins every other hypothesis it asks for: at
    [p_stop = 0] EVERY admissible list weighs zero — not merely the
    witness family, which is why the first conjunct quantifies over all
    of them — and the declared mass is still [1], so no list comes within
    [1 # 2] of it.  [file_envp_geometric_mass_upper] remains true here,
    and that asymmetry is the honest content of the pair: an upper bound
    survives degeneracy, a lower one does not. *)
Lemma file_envp_geometric_mass_lower_needs_positive :
  forall argv fs0 pth s r q Hr0 Hr1 Hq0 Hq1,
  (forall l : list FinProcInput,
     (core_sum (cd_weight (file_envp_geometric 0 r q argv fs0 pth s
                             (Qle_refl 0) Qle_0_1 Hr0 Hr1 Hq0 Hq1)) l == 0)%Q)
  /\ ~ (cd_mass (file_envp_geometric 0 r q argv fs0 pth s
                   (Qle_refl 0) Qle_0_1 Hr0 Hr1 Hq0 Hq1) - (1 # 2) <= 0)%Q.
Proof.
  intros argv fs0 pth s r q Hr0 Hr1 Hq0 Hq1. split.
  - intros l. apply core_sum_zero_weight. intros c.
    cbn [cd_weight file_envp_geometric].
    apply file_envp_geo_weight_zero_at_zero_p.
  - cbn [cd_mass file_envp_geometric]. intros Hle.
    apply (proj2 (Qle_bool_iff _ _)) in Hle. vm_compute in Hle.
    discriminate Hle.
Qed.

(* =========================================================================
   The argv/path coupling: the one obligation a caller can get silently
   wrong
   ========================================================================= *)

(** BOTH FILE FAMILIES TAKE [argv] AND [pth] AS INDEPENDENT PARAMETERS,
    and a typical driver passes the varied file's path AS
    an argument.  So a task must pass the same path in both places, and
    nothing in the constructions makes it.  Pass two different ones and
    the distribution varies a file the program never opens: it still
    declares mass [1], still satisfies both halves of the certificate
    pair, and still puts distinct positive weights on distinct file
    contents — while every core it weighs is one the program cannot tell
    apart from the others, which is exactly the all-or-nothing collapse
    these families exist to remove.

    This section closes that three ways, and none of them is a comment.
    [argv_names_path] NAMES the obligation.  [file_geometric_argv1] and
    [file_envp_geometric_argv1] make the mismatch UNREPRESENTABLE for the
    common shape, by deriving argv from the path rather than taking both.
    And the two blindness lemmas plus
    [file_geometric_needs_argv_to_name_the_path] PIN the collapse, so a
    misconfigured instance is visibly different from a well-configured
    one rather than merely differently intended.

    WHAT [argv_names_path] IS AND IS NOT.  It is the syntactic proxy:
    the path occurs somewhere in the fixed argv.  The real obligation is
    that the program OPENS the file at [pth], which is a claim about the
    program and is no more mechanizable here than the worked
    demonstration's hypothesis about its classifier is — a program may
    hardcode a path it is never given, or be given one it never opens.
    So this is neither necessary nor sufficient for the real thing; it is
    the part a library can check, and it catches the one mistake a task
    author actually makes, which is passing two different paths. *)
Definition argv_names_path (argv : list (list byte)) (pth : Fs.path) : Prop :=
  List.In pth argv.

(** The argv of the common driver shape: a program name, then the
    input file's path.  [file_geometric_argv1] below is the constructor
    that takes this shape rather than an arbitrary argv, and it is
    offered ALONGSIDE the general constructor rather than replacing it
    because not every program takes its path at argv[1] — one may read a
    path out of a config file, or take it after a flag.  A task with a
    different shape uses the general constructor and discharges
    [argv_names_path] itself. *)
Definition path_argv (prog : list byte) (pth : Fs.path) : list (list byte) :=
  [prog; pth].

Lemma path_argv_names_path : forall prog pth,
  argv_names_path (path_argv prog pth) pth.
Proof. intros prog pth. right. left. reflexivity. Qed.

(** The two derived constructors.  [pth] is passed ONCE and reaches both
    slots, so the two cannot disagree: the misconfiguration is not a
    thing a caller of these can express. *)
Definition file_geometric_argv1 (p : Q) (prog : list byte)
    (envp : list (list byte)) (fs0 : Fs.Fs) (pth : Fs.path) (s : list byte)
    (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q) : CoreDistribution :=
  file_geometric p (path_argv prog pth) envp fs0 pth s Hp0 Hp1.

Definition file_envp_geometric_argv1 (p r q : Q) (prog : list byte)
    (fs0 : Fs.Fs) (pth : Fs.path) (s : list byte)
    (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q)
    (Hr0 : (0 <= r)%Q) (Hr1 : (r <= 1)%Q)
    (Hq0 : (0 <= q)%Q) (Hq1 : (q <= 1)%Q) : CoreDistribution :=
  file_envp_geometric p r q (path_argv prog pth) fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1.

(** ... and they discharge the obligation by construction, which is the
    whole content of offering them: a task that uses one owes nothing. *)
Lemma file_geometric_argv1_names_path : forall p prog envp fs0 pth s Hp0 Hp1,
  argv_names_path (path_argv prog pth) pth
  /\ file_geometric_argv1 p prog envp fs0 pth s Hp0 Hp1
     = file_geometric p (path_argv prog pth) envp fs0 pth s Hp0 Hp1.
Proof.
  intros p prog envp fs0 pth s Hp0 Hp1.
  split; [apply path_argv_names_path | reflexivity].
Qed.

Lemma file_envp_geometric_argv1_names_path :
  forall p r q prog fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  argv_names_path (path_argv prog pth) pth
  /\ file_envp_geometric_argv1 p r q prog fs0 pth s
       Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
     = file_envp_geometric p r q (path_argv prog pth) fs0 pth s
         Hp0 Hp1 Hr0 Hr1 Hq0 Hq1.
Proof.
  intros p r q prog fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1.
  split; [apply path_argv_names_path | reflexivity].
Qed.

(** The header-conditioned family's coupled constructor, the same shape:
    [pth] is passed once and reaches both slots. *)
Definition file_geometric_prefix_argv1 (hdr : list byte) (p : Q)
    (prog : list byte) (envp : list (list byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : list byte)
    (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q) : CoreDistribution :=
  file_geometric_prefix hdr p (path_argv prog pth) envp fs0 pth s Hp0 Hp1.

Lemma file_geometric_prefix_argv1_names_path :
  forall hdr p prog envp fs0 pth s Hp0 Hp1,
  argv_names_path (path_argv prog pth) pth
  /\ file_geometric_prefix_argv1 hdr p prog envp fs0 pth s Hp0 Hp1
     = file_geometric_prefix hdr p (path_argv prog pth) envp fs0 pth s Hp0 Hp1.
Proof.
  intros hdr p prog envp fs0 pth s Hp0 Hp1.
  split; [apply path_argv_names_path | reflexivity].
Qed.

(** The alphabet-restricted family's coupled constructor, the same
    shape. *)
Definition file_geometric_prefix_over_argv1 (alpha : list byte)
    (Hnd : List.NoDup alpha) (Hne : alpha <> []) (hdr : list byte) (p : Q)
    (prog : list byte) (envp : list (list byte)) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : list byte)
    (Hp0 : (0 <= p)%Q) (Hp1 : (p <= 1)%Q) : CoreDistribution :=
  file_geometric_prefix_over alpha Hnd Hne hdr p (path_argv prog pth) envp fs0
    pth s Hp0 Hp1.

Lemma file_geometric_prefix_over_argv1_names_path :
  forall alpha Hnd Hne hdr p prog envp fs0 pth s Hp0 Hp1,
  argv_names_path (path_argv prog pth) pth
  /\ file_geometric_prefix_over_argv1 alpha Hnd Hne hdr p prog envp fs0 pth s
       Hp0 Hp1
     = file_geometric_prefix_over alpha Hnd Hne hdr p (path_argv prog pth) envp
         fs0 pth s Hp0 Hp1.
Proof.
  intros alpha Hnd Hne hdr p prog envp fs0 pth s Hp0 Hp1.
  split; [apply path_argv_names_path | reflexivity].
Qed.

(* =========================================================================
   ... and what goes wrong when the coupling is violated
   ========================================================================= *)

(** [Fs.fs_set] TOUCHES ONE KEY AND NO OTHER, with no hypothesis on the
    file system — the companion of [fs_lookup_set], and the fact the
    blindness below is made of.  The three-way case split is
    [fs_lookup_set]'s, read at a query key that is not the one being
    set: the inserted or replaced entry is skipped, and what is left is
    the original lookup. *)
Lemma fs_lookup_set_other : forall fs pth d pth',
  pth' <> pth ->
  Fs.fs_lookup (Fs.fs_set fs pth d) pth' = Fs.fs_lookup fs pth'.
Proof.
  intros fs pth d pth' Hne. induction fs as [| [q e] r IH].
  - cbn [Fs.fs_set Fs.fs_lookup].
    destruct (Fs.path_eqb pth' pth) eqn:Hpq; [| reflexivity].
    exfalso. apply Hne. apply (proj1 (Fs.path_eqb_eq pth' pth)). exact Hpq.
  - cbn [Fs.fs_set]. destruct (Fs.path_ltb pth q) eqn:Hlt.
    + cbn [Fs.fs_lookup]. destruct (Fs.path_eqb pth' pth) eqn:Hpq;
        [| reflexivity].
      exfalso. apply Hne. apply (proj1 (Fs.path_eqb_eq pth' pth)). exact Hpq.
    + destruct (Fs.path_eqb pth q) eqn:Heq.
      * assert (Hq : pth = q)
          by (apply (proj1 (Fs.path_eqb_eq pth q)); exact Heq).
        subst q. cbn [Fs.fs_lookup].
        destruct (Fs.path_eqb pth' pth) eqn:Hpq; [| reflexivity].
        exfalso. apply Hne. apply (proj1 (Fs.path_eqb_eq pth' pth)).
        exact Hpq.
      * cbn [Fs.fs_lookup]. destruct (Fs.path_eqb pth' q) eqn:Hpq;
          [reflexivity | exact IH].
Qed.

Lemma fs_file_set_other : forall fs0 pth d pth',
  pth' <> pth -> fs_file pth' (Fs.fs_set fs0 pth d) = fs_file pth' fs0.
Proof.
  intros fs0 pth d pth' Hne. unfold fs_file.
  rewrite (fs_lookup_set_other fs0 pth d pth' Hne). reflexivity.
Qed.

Lemma fs_file_file_core_other : forall argv envp fs0 pth s d pth',
  pth' <> pth ->
  fs_file pth' (core_fs (file_core argv envp fs0 pth s d)) = fs_file pth' fs0.
Proof.
  intros argv envp fs0 pth s d pth' Hne. cbn [file_core core_fs].
  apply fs_file_set_other. exact Hne.
Qed.

(** A core the weight does not zero IS the template with its own
    coordinates plugged in — the [decide] read backwards, so that the
    blindness lemmas can talk about "every core this family weighs" and
    not about the membership test. *)
Lemma file_geo_weight_positive_matches : forall p argv envp fs0 pth s c,
  (0 < file_geo_weight p argv envp fs0 pth s c)%Q ->
  c = file_core argv envp fs0 pth s (fs_file pth (core_fs c)).
Proof.
  intros p argv envp fs0 pth s c Hpos. unfold file_geo_weight in Hpos.
  destruct (decide _) as [Heq | _]; [exact Heq |].
  exfalso. exact (Qlt_irrefl 0 Hpos).
Qed.

Lemma file_envp_geo_weight_positive_matches :
  forall p r q argv fs0 pth s c,
  (0 < file_envp_geo_weight p r q argv fs0 pth s c)%Q ->
  c = file_envp_core argv fs0 pth s (core_envp c) (fs_file pth (core_fs c)).
Proof.
  intros p r q argv fs0 pth s c Hpos. unfold file_envp_geo_weight in Hpos.
  destruct (decide _) as [Heq | _]; [exact Heq |].
  exfalso. exact (Qlt_irrefl 0 Hpos).
Qed.

(** THE COLLAPSE, stated once per family: at EVERY path other than the
    one it varies, every core the family weighs holds exactly the base
    file system's contents.

    Read it against the obligation.  If [argv] names some [pth'] other
    than [pth], then the file the program is told to open is the same in
    every weighted core, so every weighted core induces the same program
    behavior, so [Classifier.good_input] and [Classifier.agree] hold at
    all of them or at none — which is the all-or-nothing reject set and
    the [b in {0, 1}] collapse, arrived at from the other direction.
    The family is not broken at such a configuration; it is measuring a
    file nobody reads. *)
Lemma file_geo_weight_blind_off_path :
  forall p argv envp fs0 pth s pth' c,
  pth' <> pth ->
  (0 < file_geo_weight p argv envp fs0 pth s c)%Q ->
  fs_file pth' (core_fs c) = fs_file pth' fs0.
Proof.
  intros p argv envp fs0 pth s pth' c Hne Hpos.
  assert (Heq := file_geo_weight_positive_matches p argv envp fs0 pth s c Hpos).
  set (d := fs_file pth (core_fs c)) in Heq.
  rewrite Heq. apply fs_file_file_core_other. exact Hne.
Qed.

Lemma file_envp_geo_weight_blind_off_path :
  forall p r q argv fs0 pth s pth' c,
  pth' <> pth ->
  (0 < file_envp_geo_weight p r q argv fs0 pth s c)%Q ->
  fs_file pth' (core_fs c) = fs_file pth' fs0.
Proof.
  intros p r q argv fs0 pth s pth' c Hne Hpos.
  assert (Heq := file_envp_geo_weight_positive_matches
                   p r q argv fs0 pth s c Hpos).
  set (es := core_envp c) in Heq. set (d := fs_file pth (core_fs c)) in Heq.
  rewrite Heq. unfold file_envp_core. apply fs_file_file_core_other.
  exact Hne.
Qed.

(** ... and so ANY TWO weighted cores agree off [pth], which is the form
    a reader wants: whatever the family varies, it is invisible at every
    other path. *)
Lemma file_geometric_blind_off_path :
  forall p argv envp fs0 pth s Hp0 Hp1 pth' c1 c2,
  pth' <> pth ->
  (0 < cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1) c1)%Q ->
  (0 < cd_weight (file_geometric p argv envp fs0 pth s Hp0 Hp1) c2)%Q ->
  fs_file pth' (core_fs c1) = fs_file pth' (core_fs c2).
Proof.
  intros p argv envp fs0 pth s Hp0 Hp1 pth' c1 c2 Hne H1 H2.
  cbn [cd_weight file_geometric] in H1, H2.
  rewrite (file_geo_weight_blind_off_path p argv envp fs0 pth s pth' c1 Hne H1).
  rewrite (file_geo_weight_blind_off_path p argv envp fs0 pth s pth' c2 Hne H2).
  reflexivity.
Qed.

Lemma file_envp_geometric_blind_off_path :
  forall p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 pth' c1 c2,
  pth' <> pth ->
  (0 < cd_weight (file_envp_geometric p r q argv fs0 pth s
                    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) c1)%Q ->
  (0 < cd_weight (file_envp_geometric p r q argv fs0 pth s
                    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) c2)%Q ->
  fs_file pth' (core_fs c1) = fs_file pth' (core_fs c2).
Proof.
  intros p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 pth' c1 c2 Hne H1 H2.
  cbn [cd_weight file_envp_geometric] in H1, H2.
  rewrite (file_envp_geo_weight_blind_off_path
             p r q argv fs0 pth s pth' c1 Hne H1).
  rewrite (file_envp_geo_weight_blind_off_path
             p r q argv fs0 pth s pth' c2 Hne H2).
  reflexivity.
Qed.

(* =========================================================================
   The misconfigured instance, exhibited
   ========================================================================= *)

(** A program name and a second path, both distinct from
    [file_example_path] and distinguished from it by LENGTH so that the
    inequalities below are three lines of [length] and not a fact about
    bytes.  As everywhere in this file these are points of [Fs.path], not
    claims that anything is valid. *)
Definition file_example_prog : list byte :=
  [Z_to_bv 8 105; Z_to_bv 8 105; Z_to_bv 8 105].

Definition file_other_path : Fs.path := [Z_to_bv 8 105; Z_to_bv 8 105].

Lemma file_other_path_ne : file_other_path <> file_example_path.
Proof.
  intros H. apply (f_equal (@length byte)) in H.
  unfold file_other_path, file_example_path in H. cbn [length] in H.
  discriminate H.
Qed.

(** The misconfiguration: an argv that names [file_other_path] while the
    family varies [file_example_path]. *)
Definition file_misconfigured_argv : list (list byte) :=
  [file_example_prog; file_other_path].

(** THE HAZARD, EXHIBITED, so that a misconfigured instance is visibly
    different from a well-configured one rather than merely differently
    intended.  Four conjuncts, and each is needed.

    The first says the configuration really is bad: the varied path
    occurs nowhere in the fixed argv, so [argv_names_path] fails.  The
    second and third say the distribution nevertheless looks entirely
    healthy — two cores with DIFFERENT file contents, both of positive
    weight; nothing about it is degenerate in any sense this file
    otherwise pins, and it declares mass [1] and satisfies both
    certificates exactly as a well-configured instance does.  The fourth
    is the collapse: at the path argv actually names, those two cores
    hold the same bytes, so a program reading its argument cannot tell
    them apart and the whole variation is invisible to it.

    That is the finding this section answers.  A task that reads only
    [file_geometric_mass_upper] and
    [file_geometric_mass_lower_certificate] cannot distinguish this
    instance from a correct one; the fourth conjunct is what does.

    [0 < p_stop < 1] is asked for because the second core's file is one
    byte long: at [p_stop = 1] that core weighs zero and the instance is
    degenerate for a different and already-pinned reason
    ([file_geo_weight_collapses_at_one_p]), which would muddy what this
    lemma is about. *)
Lemma file_geometric_needs_argv_to_name_the_path : forall p Hp0 Hp1,
  (0 < p)%Q -> (p < 1)%Q ->
  ~ argv_names_path file_misconfigured_argv file_example_path
  /\ (0 < cd_weight (file_geometric p file_misconfigured_argv [] []
                       file_example_path [] Hp0 Hp1)
            (file_core file_misconfigured_argv [] [] file_example_path [] []))%Q
  /\ (0 < cd_weight (file_geometric p file_misconfigured_argv [] []
                       file_example_path [] Hp0 Hp1)
            (file_core file_misconfigured_argv [] [] file_example_path []
               [Z_to_bv 8 65]))%Q
  /\ fs_file file_other_path
       (core_fs (file_core file_misconfigured_argv [] [] file_example_path []
                   []))
     = fs_file file_other_path
         (core_fs (file_core file_misconfigured_argv [] [] file_example_path []
                     [Z_to_bv 8 65])).
Proof.
  intros p Hp0 Hp1 Hpos Hlt. split; [| split; [| split]].
  - intros Hin. unfold argv_names_path, file_misconfigured_argv in Hin.
    destruct Hin as [Heq | [Heq | []]].
    + apply (f_equal (@length byte)) in Heq.
      unfold file_example_prog, file_example_path in Heq.
      cbn [length] in Heq. discriminate Heq.
    + exact (file_other_path_ne Heq).
  - cbn [cd_weight file_geometric]. rewrite file_geo_weight_match.
    apply geo_point_pos; assumption.
  - cbn [cd_weight file_geometric]. rewrite file_geo_weight_match.
    apply geo_point_pos; assumption.
  - rewrite !(fs_file_file_core_other _ _ _ _ _ _ _ file_other_path_ne).
    reflexivity.
Qed.

(** The same hazard for the envp-varying file family, at the same
    misconfiguration and with the envp coordinate left where it is: two
    weighted cores over one environment, differing in the input file,
    agreeing at the path argv names.  The general statement is
    [file_envp_geometric_blind_off_path]; this is it made concrete, for
    the reason the family-one exhibit is concrete — a reader wants to see
    that the instance looks healthy, not only that a universally
    quantified lemma applies to it. *)
Lemma file_envp_geometric_needs_argv_to_name_the_path :
  forall p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1,
  (0 < p)%Q -> (p < 1)%Q -> (0 < r)%Q -> (r < 1)%Q ->
  (0 < q)%Q -> (q < 1)%Q ->
  ~ argv_names_path file_misconfigured_argv file_example_path
  /\ (0 < cd_weight (file_envp_geometric p r q file_misconfigured_argv []
                       file_example_path [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
            (file_envp_core file_misconfigured_argv [] file_example_path []
               [] []))%Q
  /\ (0 < cd_weight (file_envp_geometric p r q file_misconfigured_argv []
                       file_example_path [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1)
            (file_envp_core file_misconfigured_argv [] file_example_path []
               [] [Z_to_bv 8 65]))%Q
  /\ fs_file file_other_path
       (core_fs (file_envp_core file_misconfigured_argv [] file_example_path []
                   [] []))
     = fs_file file_other_path
         (core_fs (file_envp_core file_misconfigured_argv []
                     file_example_path [] [] [Z_to_bv 8 65])).
Proof.
  intros p r q Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hppos Hplt Hrpos Hrlt Hqpos Hqlt.
  split; [| split; [| split]].
  - intros Hin. unfold argv_names_path, file_misconfigured_argv in Hin.
    destruct Hin as [Heq | [Heq | []]].
    + apply (f_equal (@length byte)) in Heq.
      unfold file_example_prog, file_example_path in Heq.
      cbn [length] in Heq. discriminate Heq.
    + exact (file_other_path_ne Heq).
  - cbn [cd_weight file_envp_geometric].
    rewrite file_envp_geo_weight_match.
    apply Qmult_lt_0_compat;
      [apply envp_point_pos; assumption | apply geo_point_pos; assumption].
  - cbn [cd_weight file_envp_geometric].
    rewrite file_envp_geo_weight_match.
    apply Qmult_lt_0_compat;
      [apply envp_point_pos; assumption | apply geo_point_pos; assumption].
  - unfold file_envp_core.
    rewrite !(fs_file_file_core_other _ _ _ _ _ _ _ file_other_path_ne).
    reflexivity.
Qed.

(* =========================================================================
   The same coupling, for the header-conditioned family
   ========================================================================= *)

(** [file_geometric_prefix] takes [argv] and [pth] independently exactly
    as [file_geometric] does, so it owes the same three closures: the
    obligation is [argv_names_path] unchanged, the coupled constructor
    is [file_geometric_prefix_argv1] above, and the collapse is pinned
    here.  A core the weight does not zero is the whole-file template at
    its own contents — and, one step further, the SHIFTED template at
    some payload. *)
Lemma file_prefix_geo_weight_positive_matches :
  forall hdr p argv envp fs0 pth s c,
  (0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c)%Q ->
  c = file_core argv envp fs0 pth s (fs_file pth (core_fs c)).
Proof.
  intros hdr p argv envp fs0 pth s c Hpos.
  unfold file_prefix_geo_weight in Hpos.
  destruct (decide _) as [Heq | _]; [exact Heq |].
  exfalso. exact (Qlt_irrefl 0 Hpos).
Qed.

Lemma file_prefix_geo_weight_positive_extends :
  forall hdr p argv envp fs0 pth s c,
  (0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c)%Q ->
  exists t, c = file_prefix_core hdr argv envp fs0 pth s t.
Proof.
  intros hdr p argv envp fs0 pth s c Hpos.
  assert (Heq := file_prefix_geo_weight_positive_matches
                   hdr p argv envp fs0 pth s c Hpos).
  unfold file_prefix_geo_weight in Hpos.
  destruct (decide _) as [_ | _]; [| exfalso; exact (Qlt_irrefl 0 Hpos)].
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |] eqn:Hs;
    [| exfalso; exact (Qlt_irrefl 0 Hpos)].
  exists t. unfold file_prefix_core.
  rewrite <- (strip_prefix_Some hdr _ t Hs). exact Heq.
Qed.

Lemma file_prefix_geo_weight_blind_off_path :
  forall hdr p argv envp fs0 pth s pth' c,
  pth' <> pth ->
  (0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c)%Q ->
  fs_file pth' (core_fs c) = fs_file pth' fs0.
Proof.
  intros hdr p argv envp fs0 pth s pth' c Hne Hpos.
  assert (Heq := file_prefix_geo_weight_positive_matches
                   hdr p argv envp fs0 pth s c Hpos).
  set (d := fs_file pth (core_fs c)) in Heq.
  rewrite Heq. apply fs_file_file_core_other. exact Hne.
Qed.

Lemma file_geometric_prefix_blind_off_path :
  forall hdr p argv envp fs0 pth s Hp0 Hp1 pth' c1 c2,
  pth' <> pth ->
  (0 < cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) c1)%Q ->
  (0 < cd_weight (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1) c2)%Q ->
  fs_file pth' (core_fs c1) = fs_file pth' (core_fs c2).
Proof.
  intros hdr p argv envp fs0 pth s Hp0 Hp1 pth' c1 c2 Hne H1 H2.
  cbn [cd_weight file_geometric_prefix] in H1, H2.
  rewrite (file_prefix_geo_weight_blind_off_path
             hdr p argv envp fs0 pth s pth' c1 Hne H1).
  rewrite (file_prefix_geo_weight_blind_off_path
             hdr p argv envp fs0 pth s pth' c2 Hne H2).
  reflexivity.
Qed.

(** The misconfigured instance for this family, at the same
    misconfiguration and behind the one-byte example header: two
    weighted cores whose payloads differ, agreeing at the path argv
    names. *)
Lemma file_geometric_prefix_needs_argv_to_name_the_path : forall p Hp0 Hp1,
  (0 < p)%Q -> (p < 1)%Q ->
  ~ argv_names_path file_misconfigured_argv file_example_path
  /\ (0 < cd_weight (file_geometric_prefix file_example_hdr p
                       file_misconfigured_argv [] [] file_example_path []
                       Hp0 Hp1)
            (file_prefix_core file_example_hdr file_misconfigured_argv [] []
               file_example_path [] []))%Q
  /\ (0 < cd_weight (file_geometric_prefix file_example_hdr p
                       file_misconfigured_argv [] [] file_example_path []
                       Hp0 Hp1)
            (file_prefix_core file_example_hdr file_misconfigured_argv [] []
               file_example_path [] [Z_to_bv 8 65]))%Q
  /\ fs_file file_other_path
       (core_fs (file_prefix_core file_example_hdr file_misconfigured_argv [] []
                   file_example_path [] []))
     = fs_file file_other_path
         (core_fs (file_prefix_core file_example_hdr file_misconfigured_argv
                     [] [] file_example_path [] [Z_to_bv 8 65])).
Proof.
  intros p Hp0 Hp1 Hpos Hlt. split; [| split; [| split]].
  - exact (proj1 (file_geometric_needs_argv_to_name_the_path p Hp0 Hp1 Hpos Hlt)).
  - cbn [cd_weight file_geometric_prefix]. rewrite file_prefix_geo_weight_match.
    apply geo_point_pos; assumption.
  - cbn [cd_weight file_geometric_prefix]. rewrite file_prefix_geo_weight_match.
    apply geo_point_pos; assumption.
  - unfold file_prefix_core.
    rewrite !(fs_file_file_core_other _ _ _ _ _ _ _ file_other_path_ne).
    reflexivity.
Qed.

(* =========================================================================
   The same coupling, for the alphabet-restricted family
   ========================================================================= *)

Lemma file_prefix_over_geo_weight_positive_matches :
  forall alpha hdr p argv envp fs0 pth s c,
  (0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c)%Q ->
  c = file_core argv envp fs0 pth s (fs_file pth (core_fs c)).
Proof.
  intros alpha hdr p argv envp fs0 pth s c Hpos.
  unfold file_prefix_over_geo_weight in Hpos.
  destruct (decide _) as [Heq | _]; [exact Heq |].
  exfalso. exact (Qlt_irrefl 0 Hpos).
Qed.

Lemma file_prefix_over_geo_weight_positive_extends :
  forall alpha hdr p argv envp fs0 pth s c,
  (0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c)%Q ->
  exists t, c = file_prefix_core hdr argv envp fs0 pth s t
            /\ alpha_only alpha t = true.
Proof.
  intros alpha hdr p argv envp fs0 pth s c Hpos.
  assert (Heq := file_prefix_over_geo_weight_positive_matches
                   alpha hdr p argv envp fs0 pth s c Hpos).
  unfold file_prefix_over_geo_weight in Hpos.
  destruct (decide _) as [_ | _]; [| exfalso; exact (Qlt_irrefl 0 Hpos)].
  destruct (strip_prefix hdr (fs_file pth (core_fs c))) as [t |] eqn:Hs;
    [| exfalso; exact (Qlt_irrefl 0 Hpos)].
  destruct (alpha_only alpha t) eqn:Ha; [| exfalso; exact (Qlt_irrefl 0 Hpos)].
  exists t. split; [| exact Ha]. unfold file_prefix_core.
  rewrite <- (strip_prefix_Some hdr _ t Hs). exact Heq.
Qed.

Lemma file_prefix_over_geo_weight_blind_off_path :
  forall alpha hdr p argv envp fs0 pth s pth' c,
  pth' <> pth ->
  (0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c)%Q ->
  fs_file pth' (core_fs c) = fs_file pth' fs0.
Proof.
  intros alpha hdr p argv envp fs0 pth s pth' c Hne Hpos.
  assert (Heq := file_prefix_over_geo_weight_positive_matches
                   alpha hdr p argv envp fs0 pth s c Hpos).
  set (d := fs_file pth (core_fs c)) in Heq.
  rewrite Heq. apply fs_file_file_core_other. exact Hne.
Qed.

Lemma file_geometric_prefix_over_blind_off_path :
  forall alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 pth' c1 c2,
  pth' <> pth ->
  (0 < cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
                    Hp0 Hp1) c1)%Q ->
  (0 < cd_weight (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
                    Hp0 Hp1) c2)%Q ->
  fs_file pth' (core_fs c1) = fs_file pth' (core_fs c2).
Proof.
  intros alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1 pth' c1 c2 Hne' H1 H2.
  cbn [cd_weight file_geometric_prefix_over] in H1, H2.
  rewrite (file_prefix_over_geo_weight_blind_off_path
             alpha hdr p argv envp fs0 pth s pth' c1 Hne' H1).
  rewrite (file_prefix_over_geo_weight_blind_off_path
             alpha hdr p argv envp fs0 pth s pth' c2 Hne' H2).
  reflexivity.
Qed.

(** The misconfigured instance for this family, over the one-byte
    example alphabet: the payloads are the empty one and the
    alphabet's own byte. *)
Lemma file_geometric_prefix_over_needs_argv_to_name_the_path : forall p Hp0 Hp1,
  (0 < p)%Q -> (p < 1)%Q ->
  ~ argv_names_path file_misconfigured_argv file_example_path
  /\ (0 < cd_weight (file_geometric_prefix_over file_example_alpha
                       file_example_alpha_nodup file_example_alpha_ne
                       file_example_hdr p file_misconfigured_argv [] []
                       file_example_path [] Hp0 Hp1)
            (file_prefix_core file_example_hdr file_misconfigured_argv [] []
               file_example_path [] []))%Q
  /\ (0 < cd_weight (file_geometric_prefix_over file_example_alpha
                       file_example_alpha_nodup file_example_alpha_ne
                       file_example_hdr p file_misconfigured_argv [] []
                       file_example_path [] Hp0 Hp1)
            (file_prefix_core file_example_hdr file_misconfigured_argv [] []
               file_example_path [] [Z_to_bv 8 65]))%Q
  /\ fs_file file_other_path
       (core_fs (file_prefix_core file_example_hdr file_misconfigured_argv [] []
                   file_example_path [] []))
     = fs_file file_other_path
         (core_fs (file_prefix_core file_example_hdr file_misconfigured_argv
                     [] [] file_example_path [] [Z_to_bv 8 65])).
Proof.
  intros p Hp0 Hp1 Hpos Hlt. split; [| split; [| split]].
  - exact (proj1 (file_geometric_needs_argv_to_name_the_path p Hp0 Hp1 Hpos Hlt)).
  - cbn [cd_weight file_geometric_prefix_over].
    rewrite file_prefix_over_geo_weight_match by reflexivity.
    apply alpha_geo_point_pos; [exact Hpos | exact Hlt | exact file_example_alpha_ne].
  - cbn [cd_weight file_geometric_prefix_over].
    rewrite file_prefix_over_geo_weight_match by (vm_compute; reflexivity).
    apply alpha_geo_point_pos; [exact Hpos | exact Hlt | exact file_example_alpha_ne].
  - unfold file_prefix_core.
    rewrite !(fs_file_file_core_other _ _ _ _ _ _ _ file_other_path_ne).
    reflexivity.
Qed.

(* =========================================================================
   Combinator: the FULL-SUPPORT base family — every core carries mass
   ========================================================================= *)

(** Every family above weighs ZERO off one fixed template: [geo_weight]
    off its argv, envp and file system; [envp_geo_weight] off its argv
    and file system; the file families off their argv, envp and
    standard input and at every path but one.  The header's warning
    applies at each of those null sets — a fire set living there is
    charged nothing, and a [Measure.weight_bound_T] claim about it holds
    vacuously.  This family is the one under which NO core is in a null
    set: four independent factors, one per field of [FinInput.FinCore],
    each strictly positive at every value of its coordinate when its
    rates are strictly inside [(0, 1)] ([full_support_base_positive]).

    The four factors are the memoryless sources this file already has,
    run over the fields the earlier families held fixed.  argv and envp
    are lists of byte strings, and both are spread by the entry-count /
    per-entry-byte source [envp_point] was built for; [strings_point] is
    that source under a field-neutral name, so that "the argv law" and
    "the envp law" are visibly the same object at different rates.  The
    file system is a list of (path, contents) PAIRS, and [fs_point] is
    the same entry-count shell around a pair of byte-geometric factors
    per entry, one for the path and one for the contents.  Standard
    input is [geo_point] as everywhere.  Eight rates in all: a stop rate
    and a per-entry byte rate for argv ([ra], [qa]) and for envp ([re],
    [qe]); an entry stop rate, a path byte rate and a contents byte rate
    for the file system ([u], [v], [w]); and the standard-input stop
    rate [ps].  Setting all eight to
    [1 # 2] makes every byte string weigh [(1 # 2) * (1 # 512) ^
    length] and every list weigh [(1 # 2) ^ (count + 1)] times its
    entries' product; the demo file at
    [Examples/measure_lib_demo/FullSupportBase.v] works that instance.

    Mass [1] is DECLARED, as everywhere in this file, and
    [full_support_base_mass_upper] is the proof that owes something to
    it.  The enumeration behind every bound is the four-fold product of
    the coordinates' enumerations ([full_support_product]), and its sum
    is the product of the four sums ([qsum_full_support_product]) —
    [envp_stdin_product] and [file_envp_product] two coordinates deeper,
    with [qsum_flat_map] doing the same work at each layer.  Three of
    the four coordinates' own sums are already bounded above
    ([envp_enum_sum_le] twice, [bytes_cyl_sum_le]); the file-system
    coordinate gets its own enumeration and cancellation below
    ([fs_enum], [fs_enum_sum_le]), which are [envp_enum] and
    [envp_enum_sum_le] with a pair where they have a string.

    WHAT IS NOT CLAIMED.  [fs_point] weighs EVERY list of pairs, sorted
    or not, duplicate keys or not, and those lists are never
    [Fs.valid_fs] and so never the file system of a real input.  This
    seam is decided rather than hidden,
    and it is decided the way every other family in this file decides
    validity: not at all.  [file_core]'s comment already says the
    library neither needs nor claims that the cores it weighs are valid,
    and this family is no different — the declared [1] is the mass of
    the LAW over all finite cores, and the mass reachable by valid
    images is strictly less than it.  A task that needs "valid images
    still carry at least so much" needs a lemma this file does not yet
    offer; restricting the law to sorted lists instead would need a
    sorted enumeration for every bound below and would make this family
    the only one in the file that ties weight to validity.

    The composability bound — cores whose argv is a
    fixed list and whose file at a path EXTENDS given bytes weigh at
    most the argv's weight times the byte cylinder's mass — is
    [full_support_base_argv_file_bound].  It is not an instance of the
    cylinder bound, because the file condition constrains ONE ENTRY of
    the file-system list while the entry count and every other entry
    stay free; it is proved instead by a weight-preserving injection
    ([core_strip]) that strips the prefix off the distinguished entry
    and pays exactly [geo_mass w (length bs)] for it. *)

(** The argv law and the envp law are ONE source.  [strings_point r q]
    is [envp_point r q], and [strings_factor] is [envp_factor]; the
    field-neutral names exist so that a statement about the argv
    coordinate does not read as a statement about the environment.
    Every lemma about [envp_point] applies through [unfold]. *)
Definition strings_factor : Q -> Q -> list (list byte) -> Q := envp_factor.
Definition strings_point : Q -> Q -> list (list byte) -> Q := envp_point.

Lemma strings_point_closed_form : forall r q xs,
  (strings_point r q xs
     == r * Qpow (1 - r) (length xs) * entries_geo_product q xs)%Q.
Proof. intros r q xs. unfold strings_point. apply envp_point_closed_form. Qed.

Lemma strings_point_nonneg : forall r q,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= q)%Q -> (q <= 1)%Q ->
  forall xs, (0 <= strings_point r q xs)%Q.
Proof.
  intros r q Hr0 Hr1 Hq0 Hq1 xs. unfold strings_point.
  apply envp_point_nonneg; assumption.
Qed.

Lemma strings_point_pos : forall r q xs,
  (0 < r)%Q -> (r < 1)%Q -> (0 < q)%Q -> (q < 1)%Q ->
  (0 < strings_point r q xs)%Q.
Proof.
  intros r q xs Hr0 Hr1 Hq0 Hq1. unfold strings_point.
  apply envp_point_pos; assumption.
Qed.

(** The file-system law.  [fs_entries_product] is [entries_geo_product]
    with two byte-geometric factors per entry — the path's and the
    contents' — and [fs_factor] is [envp_factor]'s running product with
    the same pair inside: continuing past an entry costs [1 - u], the
    entry costs its path's weight times its contents' weight.
    [fs_point] is [u] times it, [u] being the weight of stopping.  As
    with [envp_point], the three-factor form the family is specified
    with is [fs_point_closed_form] and is a LEMMA, not a rival
    definition. *)
Fixpoint fs_entries_product (v w : Q) (fs : Fs.Fs) : Q :=
  match fs with
  | [] => 1%Q
  | (pth, d) :: fs' =>
      (geo_point v (length pth) * geo_point w (length d)
       * fs_entries_product v w fs')%Q
  end.

Fixpoint fs_factor (u v w : Q) (fs : Fs.Fs) : Q :=
  match fs with
  | [] => 1%Q
  | (pth, d) :: fs' =>
      ((1 - u) * geo_point v (length pth) * geo_point w (length d)
       * fs_factor u v w fs')%Q
  end.

Definition fs_point (u v w : Q) (fs : Fs.Fs) : Q := (u * fs_factor u v w fs)%Q.

Lemma fs_factor_closed_form : forall u v w fs,
  (fs_factor u v w fs
     == Qpow (1 - u) (length fs) * fs_entries_product v w fs)%Q.
Proof.
  intros u v w fs. induction fs as [| [pth d] fs IH].
  - cbn [fs_factor fs_entries_product length]. rewrite Qpow_0. ring.
  - cbn [fs_factor fs_entries_product length]. rewrite IH, Qpow_succ. ring.
Qed.

Lemma fs_point_closed_form : forall u v w fs,
  (fs_point u v w fs
     == u * Qpow (1 - u) (length fs) * fs_entries_product v w fs)%Q.
Proof.
  intros u v w fs. unfold fs_point. rewrite fs_factor_closed_form. ring.
Qed.

Lemma fs_factor_app : forall u v w fs fs',
  (fs_factor u v w (fs ++ fs') == fs_factor u v w fs * fs_factor u v w fs')%Q.
Proof.
  intros u v w fs fs'. induction fs as [| [pth d] fs IH].
  - cbn [List.app fs_factor]. ring.
  - cbn [List.app fs_factor]. rewrite IH. ring.
Qed.

Lemma fs_factor_one : forall u v w pth d,
  (fs_factor u v w [(pth, d)]
     == (1 - u) * geo_point v (length pth) * geo_point w (length d))%Q.
Proof. intros u v w pth d. cbn [fs_factor]. ring. Qed.

(** Nonnegativity costs the five side conditions the three rates cost
    separately, exactly as [envp_factor_nonneg]'s cost its three. *)
Lemma fs_factor_nonneg : forall u v w,
  (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q -> (0 <= w)%Q -> (w <= 1)%Q ->
  forall fs, (0 <= fs_factor u v w fs)%Q.
Proof.
  intros u v w Hu1 Hv0 Hv1 Hw0 Hw1 fs.
  induction fs as [| [pth d] fs IH]; [exact Qle_0_1 |].
  cbn [fs_factor]. apply Qmult_le_0_compat; [| exact IH].
  apply Qmult_le_0_compat; [apply Qmult_le_0_compat |].
  - apply (Qle_minus_iff u 1). exact Hu1.
  - apply geo_point_nonneg; assumption.
  - apply geo_point_nonneg; assumption.
Qed.

Lemma fs_point_nonneg : forall u v w,
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q ->
  forall fs, (0 <= fs_point u v w fs)%Q.
Proof.
  intros u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 fs. unfold fs_point.
  apply Qmult_le_0_compat; [exact Hu0 | apply fs_factor_nonneg; assumption].
Qed.

(** One file system weighs at most the mass of the file systems
    extending it (as lists), because [u <= 1] — [envp_point_le_factor]
    on this coordinate, and the base case of the same induction. *)
Lemma fs_point_le_factor : forall u v w,
  (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q -> (0 <= w)%Q -> (w <= 1)%Q ->
  forall fs, (fs_point u v w fs <= fs_factor u v w fs)%Q.
Proof.
  intros u v w Hu1 Hv0 Hv1 Hw0 Hw1 fs. unfold fs_point.
  rewrite <- (Qmult_1_l (fs_factor u v w fs)) at 2.
  apply Qmult_le_compat_r; [exact Hu1 | apply fs_factor_nonneg; assumption].
Qed.

(** Strict positivity at every list of pairs, sorted or not: every
    factor of the running product is positive, so the product is.
    [envp_point_pos]'s induction with two [geo_point_pos] per entry. *)
Lemma fs_point_pos : forall u v w fs,
  (0 < u)%Q -> (u < 1)%Q -> (0 < v)%Q -> (v < 1)%Q -> (0 < w)%Q -> (w < 1)%Q ->
  (0 < fs_point u v w fs)%Q.
Proof.
  intros u v w fs Hu0 Hu1 Hv0 Hv1 Hw0 Hw1. unfold fs_point.
  apply Qmult_lt_0_compat; [exact Hu0 |].
  induction fs as [| [pth d] fs IH]; [reflexivity |].
  cbn [fs_factor]. apply Qmult_lt_0_compat; [| exact IH].
  apply Qmult_lt_0_compat; [apply Qmult_lt_0_compat |].
  - apply (Qlt_minus_iff u 1). exact Hu1.
  - apply geo_point_pos; assumption.
  - apply geo_point_pos; assumption.
Qed.

(** THE WEIGHT: the product of the four coordinates' laws, with no
    template and no [decide] — there is no environment to match, because
    every environment is in the support.  [base_weight_mk] is the
    rewrite rule on a constructed core, and it is [eq] by computation
    rather than a [Qeq] through a decision, which is the whole
    difference from [geo_weight_match]. *)
Definition base_weight (ra qa re qe u v w ps : Q) (c : FinCore) : Q :=
  (strings_point ra qa (core_argv c) * strings_point re qe (core_envp c)
   * fs_point u v w (core_fs c) * geo_point ps (length (core_stdin c)))%Q.

Lemma base_weight_mk : forall ra qa re qe u v w ps argv envp fs s,
  base_weight ra qa re qe u v w ps (mkFinCore argv envp fs s)
    = (strings_point ra qa argv * strings_point re qe envp
       * fs_point u v w fs * geo_point ps (length s))%Q.
Proof. reflexivity. Qed.

(** THE FAMILY'S FORMULA with all eight rates visible, stated because
    the law is usually written in this shape and a reader should be able
    to check the definition against it without unfolding anything. *)
Lemma base_weight_closed_form : forall ra qa re qe u v w ps argv envp fs s,
  (base_weight ra qa re qe u v w ps (mkFinCore argv envp fs s)
     == (ra * Qpow (1 - ra) (length argv) * entries_geo_product qa argv)
        * (re * Qpow (1 - re) (length envp) * entries_geo_product qe envp)
        * (u * Qpow (1 - u) (length fs) * fs_entries_product v w fs)
        * (ps * Qpow (1 - ps) (length s) * Qpow (1 # 256) (length s)))%Q.
Proof.
  intros ra qa re qe u v w ps argv envp fs s.
  rewrite base_weight_mk, !strings_point_closed_form, fs_point_closed_form,
    geo_point_closed_form.
  ring.
Qed.

Lemma base_weight_nonneg : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall c, (0 <= base_weight ra qa re qe u v w ps c)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 c.
  unfold base_weight.
  apply Qmult_le_0_compat;
    [apply Qmult_le_0_compat; [apply Qmult_le_0_compat |] |].
  - apply strings_point_nonneg; assumption.
  - apply strings_point_nonneg; assumption.
  - apply fs_point_nonneg; assumption.
  - apply geo_point_nonneg; assumption.
Qed.

(** The distribution.  Mass [1] is DECLARED, and the sixteen side
    conditions are constructor arguments for the reason
    [stdin_geometric]'s two are: [cd_nonneg] is a field.  None of the
    eight STRICT inequalities is demanded — nothing the constructor
    needs uses them, and the two lemmas that do
    ([full_support_base_positive], the lower certificate) ask for them
    as hypotheses of their own statements, so a degenerate member (a
    rate at [0] or [1]) is a member in good standing, as everywhere in
    this file. *)
Definition full_support_base (ra qa re qe u v w ps : Q)
    (Hra0 : (0 <= ra)%Q) (Hra1 : (ra <= 1)%Q)
    (Hqa0 : (0 <= qa)%Q) (Hqa1 : (qa <= 1)%Q)
    (Hre0 : (0 <= re)%Q) (Hre1 : (re <= 1)%Q)
    (Hqe0 : (0 <= qe)%Q) (Hqe1 : (qe <= 1)%Q)
    (Hu0 : (0 <= u)%Q) (Hu1 : (u <= 1)%Q)
    (Hv0 : (0 <= v)%Q) (Hv1 : (v <= 1)%Q)
    (Hw0 : (0 <= w)%Q) (Hw1 : (w <= 1)%Q)
    (Hps0 : (0 <= ps)%Q) (Hps1 : (ps <= 1)%Q) : CoreDistribution :=
  mkCoreDistribution (base_weight ra qa re qe u v w ps) 1
    (base_weight_nonneg ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
       Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).

Lemma full_support_base_mass_nonneg :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1,
  (0 <= cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                   Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))%Q.
Proof.
  intros. cbn [cd_mass full_support_base].
  apply (proj1 (Qle_bool_iff _ _)). vm_compute. reflexivity.
Qed.

(* =========================================================================
   Full support: every core weighs something
   ========================================================================= *)

(** THE FULL-SUPPORT LEMMA.  At any eight rates
    strictly inside [(0, 1)], every core — every argv, every
    environment, every file system, every standard input, however
    long — weighs strictly more than zero.  Under this family no fire
    set sits in a null set, so a [Measure.weight_bound_T] claim is
    never vacuous.  Four positivity facts, one per coordinate, and the
    product of positives is positive. *)
Lemma full_support_base_positive :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1,
  (0 < ra)%Q -> (ra < 1)%Q -> (0 < qa)%Q -> (qa < 1)%Q ->
  (0 < re)%Q -> (re < 1)%Q -> (0 < qe)%Q -> (qe < 1)%Q ->
  (0 < u)%Q -> (u < 1)%Q -> (0 < v)%Q -> (v < 1)%Q ->
  (0 < w)%Q -> (w < 1)%Q -> (0 < ps)%Q -> (ps < 1)%Q ->
  forall c,
    (0 < cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)
           c)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    Hrapos Hralt Hqapos Hqalt Hrepos Hrelt Hqepos Hqelt
    Hupos Hult Hvpos Hvlt Hwpos Hwlt Hpspos Hpslt c.
  cbn [cd_weight full_support_base]. unfold base_weight.
  apply Qmult_lt_0_compat;
    [apply Qmult_lt_0_compat; [apply Qmult_lt_0_compat |] |].
  - apply strings_point_pos; assumption.
  - apply strings_point_pos; assumption.
  - apply fs_point_pos; assumption.
  - apply geo_point_pos; assumption.
Qed.

(** The same fact on RECORDS, which is the form [Measure.DISTRIBUTION]'s
    [w] is consulted in: every record weighs something. *)
Lemma full_support_base_lift_positive :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1,
  (0 < ra)%Q -> (ra < 1)%Q -> (0 < qa)%Q -> (qa < 1)%Q ->
  (0 < re)%Q -> (re < 1)%Q -> (0 < qe)%Q -> (qe < 1)%Q ->
  (0 < u)%Q -> (u < 1)%Q -> (0 < v)%Q -> (v < 1)%Q ->
  (0 < w)%Q -> (w < 1)%Q -> (0 < ps)%Q -> (ps < 1)%Q ->
  forall f : FinProcInput,
    (0 < cd_lift (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)
           f)%Q.
Proof.
  intros. unfold cd_lift. apply full_support_base_positive; assumption.
Qed.

(** THE BITE, against every sibling at once: a core off every fixed
    template — its argv, envp, file system and standard input each one
    byte — weighs zero under each of the template families over the
    empty environment (the header families at the empty header, the
    alphabet one over the one-byte alphabet), and strictly positively
    here.  The zeros are the
    [_mismatch] rules, one per sibling; the positive is
    [full_support_base_positive] at concrete rates. *)
Definition full_support_example_core : FinCore :=
  mkFinCore [[Z_to_bv 8 65]] [[Z_to_bv 8 65]] [([Z_to_bv 8 65], [Z_to_bv 8 65])]
    [Z_to_bv 8 65].

Lemma full_support_base_bites : forall p r q,
  geo_weight p [] [] [] full_support_example_core = 0%Q
  /\ envp_geo_weight p r q [] [] full_support_example_core = 0%Q
  /\ file_geo_weight p [] [] [] [Z_to_bv 8 65] [] full_support_example_core = 0%Q
  /\ file_envp_geo_weight p r q [] [] [Z_to_bv 8 65] [] full_support_example_core
     = 0%Q
  /\ file_prefix_geo_weight [] p [] [] [] [Z_to_bv 8 65] [] full_support_example_core
     = 0%Q
  /\ file_prefix_over_geo_weight [Z_to_bv 8 65] [] p [] [] [] [Z_to_bv 8 65] []
       full_support_example_core = 0%Q
  /\ (0 < base_weight (1 # 2) (1 # 2) (1 # 2) (1 # 2) (1 # 2) (1 # 2) (1 # 2)
                      (1 # 2) full_support_example_core)%Q.
Proof.
  intros p r q. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply geo_weight_mismatch. intros Heq.
    apply (f_equal core_argv) in Heq. cbn [core_argv] in Heq. discriminate Heq.
  - apply envp_geo_weight_mismatch. intros Heq.
    apply (f_equal core_argv) in Heq. cbn [core_argv] in Heq. discriminate Heq.
  - apply file_geo_weight_mismatch. intros Heq.
    apply (f_equal core_argv) in Heq. cbn [core_argv] in Heq. discriminate Heq.
  - apply file_envp_geo_weight_mismatch. intros Heq.
    apply (f_equal core_argv) in Heq. cbn [core_argv] in Heq. discriminate Heq.
  - apply file_prefix_geo_weight_mismatch. intros Heq.
    apply (f_equal core_argv) in Heq. cbn [core_argv] in Heq. discriminate Heq.
  - apply file_prefix_over_geo_weight_mismatch. intros Heq.
    apply (f_equal core_argv) in Heq. cbn [core_argv] in Heq. discriminate Heq.
  - unfold full_support_example_core. rewrite base_weight_mk.
    vm_compute. reflexivity.
Qed.

(* =========================================================================
   The four coordinates, recombined
   ========================================================================= *)

(** Every core whose argv comes from [Av], envp from [Ae], file system
    from [Af] and standard input from [B].  Three [flat_map] layers over
    one [map], and its sum is the product of the four coordinates' sums
    ([qsum_full_support_product]) — [qsum_envp_stdin_product] two
    layers deeper, each layer discharged by [qsum_flat_map] and one
    [qsum_scale].  This identity is the only place the four coordinates
    meet; every bound below is assembled from four one-coordinate bounds
    proved apart. *)
Definition full_support_product (Av Ae : list (list (list byte)))
    (Af : list Fs.Fs) (B : list (list byte)) : list FinCore :=
  List.flat_map (fun argv =>
    List.flat_map (fun envp =>
      List.flat_map (fun fs => List.map (mkFinCore argv envp fs) B) Af) Ae) Av.

Lemma In_full_support_product : forall Av Ae Af B argv envp fs s,
  List.In argv Av -> List.In envp Ae -> List.In fs Af -> List.In s B ->
  List.In (mkFinCore argv envp fs s) (full_support_product Av Ae Af B).
Proof.
  intros Av Ae Af B argv envp fs s Ha He Hf Hs. unfold full_support_product.
  apply List.in_flat_map. exists argv. split; [exact Ha |].
  apply List.in_flat_map. exists envp. split; [exact He |].
  apply List.in_flat_map. exists fs. split; [exact Hf |].
  apply List.in_map. exact Hs.
Qed.

Lemma qsum_base_stdin_block : forall ra qa re qe u v w ps argv envp fs B,
  (qsum (base_weight ra qa re qe u v w ps) (List.map (mkFinCore argv envp fs) B)
     == strings_point ra qa argv * strings_point re qe envp * fs_point u v w fs
        * qsum (fun s => geo_point ps (length s)) B)%Q.
Proof.
  intros ra qa re qe u v w ps argv envp fs B. rewrite qsum_map.
  rewrite (qsum_ext (fun s => base_weight ra qa re qe u v w ps
                                  (mkFinCore argv envp fs s))
             (fun s => ((strings_point ra qa argv * strings_point re qe envp
                         * fs_point u v w fs) * geo_point ps (length s))%Q))
    by (intros s _; rewrite base_weight_mk; reflexivity).
  rewrite (qsum_scale (strings_point ra qa argv * strings_point re qe envp
                       * fs_point u v w fs)%Q
             (fun s => geo_point ps (length s)) B).
  reflexivity.
Qed.

Lemma qsum_base_fs_block : forall ra qa re qe u v w ps argv envp Af B,
  (qsum (base_weight ra qa re qe u v w ps)
     (List.flat_map (fun fs => List.map (mkFinCore argv envp fs) B) Af)
     == strings_point ra qa argv * strings_point re qe envp
        * qsum (fs_point u v w) Af * qsum (fun s => geo_point ps (length s)) B)%Q.
Proof.
  intros ra qa re qe u v w ps argv envp Af B.
  rewrite qsum_flat_map. cbv beta.
  rewrite (qsum_ext (fun fs => qsum (base_weight ra qa re qe u v w ps)
                                   (List.map (mkFinCore argv envp fs) B))
             (fun fs => ((strings_point ra qa argv * strings_point re qe envp
                          * qsum (fun s => geo_point ps (length s)) B)
                         * fs_point u v w fs)%Q))
    by (intros fs _; rewrite qsum_base_stdin_block; ring).
  rewrite (qsum_scale (strings_point ra qa argv * strings_point re qe envp
                       * qsum (fun s => geo_point ps (length s)) B)%Q
             (fs_point u v w) Af).
  ring.
Qed.

Lemma qsum_base_envp_block : forall ra qa re qe u v w ps argv Ae Af B,
  (qsum (base_weight ra qa re qe u v w ps)
     (List.flat_map (fun envp =>
        List.flat_map (fun fs => List.map (mkFinCore argv envp fs) B) Af) Ae)
     == strings_point ra qa argv * qsum (strings_point re qe) Ae
        * qsum (fs_point u v w) Af * qsum (fun s => geo_point ps (length s)) B)%Q.
Proof.
  intros ra qa re qe u v w ps argv Ae Af B.
  rewrite qsum_flat_map. cbv beta.
  rewrite (qsum_ext (fun envp => qsum (base_weight ra qa re qe u v w ps)
                                   (List.flat_map (fun fs =>
                                      List.map (mkFinCore argv envp fs) B) Af))
             (fun envp => ((strings_point ra qa argv * qsum (fs_point u v w) Af
                            * qsum (fun s => geo_point ps (length s)) B)
                           * strings_point re qe envp)%Q))
    by (intros envp _; rewrite qsum_base_fs_block; ring).
  rewrite (qsum_scale (strings_point ra qa argv * qsum (fs_point u v w) Af
                       * qsum (fun s => geo_point ps (length s)) B)%Q
             (strings_point re qe) Ae).
  ring.
Qed.

Lemma qsum_full_support_product : forall ra qa re qe u v w ps Av Ae Af B,
  (qsum (base_weight ra qa re qe u v w ps) (full_support_product Av Ae Af B)
     == qsum (strings_point ra qa) Av * qsum (strings_point re qe) Ae
        * qsum (fs_point u v w) Af * qsum (fun s => geo_point ps (length s)) B)%Q.
Proof.
  intros ra qa re qe u v w ps Av Ae Af B. unfold full_support_product.
  rewrite qsum_flat_map. cbv beta.
  rewrite (qsum_ext (fun argv => qsum (base_weight ra qa re qe u v w ps)
                                   (List.flat_map (fun envp =>
                                      List.flat_map (fun fs =>
                                        List.map (mkFinCore argv envp fs) B)
                                        Af) Ae))
             (fun argv => ((qsum (strings_point re qe) Ae
                            * qsum (fs_point u v w) Af
                            * qsum (fun s => geo_point ps (length s)) B)
                           * strings_point ra qa argv)%Q))
    by (intros argv _; rewrite qsum_base_envp_block; ring).
  rewrite (qsum_scale (qsum (strings_point re qe) Ae * qsum (fs_point u v w) Af
                       * qsum (fun s => geo_point ps (length s)) B)%Q
             (strings_point ra qa) Av).
  ring.
Qed.

(** The product of four duplicate-free enumerations repeats nothing: a
    core determines each of its four fields, so within a block the
    innermost map is injective and any two blocks at any layer are
    disjoint.  Only the lower certificate needs this. *)
Lemma NoDup_full_support_product : forall Av Ae Af B,
  List.NoDup Av -> List.NoDup Ae -> List.NoDup Af -> List.NoDup B ->
  List.NoDup (full_support_product Av Ae Af B).
Proof.
  intros Av Ae Af B HA HE HF HB. unfold full_support_product.
  apply NoDup_flat_map; [exact HA | |].
  - intros argv _. apply NoDup_flat_map; [exact HE | |].
    + intros envp _. apply NoDup_flat_map; [exact HF | |].
      * intros fs _. apply NoDup_map_inj; [| exact HB].
        intros x y _ _ Heq. apply (f_equal core_stdin) in Heq. exact Heq.
      * intros fs1 fs2 c _ _ H1 H2.
        apply List.in_map_iff in H1 as [s1 [Hs1 _]].
        apply List.in_map_iff in H2 as [s2 [Hs2 _]].
        rewrite <- Hs1 in Hs2. apply (f_equal core_fs) in Hs2.
        cbn [core_fs] in Hs2. symmetry. exact Hs2.
    + intros envp1 envp2 c _ _ H1 H2.
      apply List.in_flat_map in H1 as [fs1 [_ H1]].
      apply List.in_map_iff in H1 as [s1 [Hs1 _]].
      apply List.in_flat_map in H2 as [fs2 [_ H2]].
      apply List.in_map_iff in H2 as [s2 [Hs2 _]].
      rewrite <- Hs1 in Hs2. apply (f_equal core_envp) in Hs2.
      cbn [core_envp] in Hs2. symmetry. exact Hs2.
  - intros argv1 argv2 c _ _ H1 H2.
    apply List.in_flat_map in H1 as [envp1 [_ H1]].
    apply List.in_flat_map in H1 as [fs1 [_ H1]].
    apply List.in_map_iff in H1 as [s1 [Hs1 _]].
    apply List.in_flat_map in H2 as [envp2 [_ H2]].
    apply List.in_flat_map in H2 as [fs2 [_ H2]].
    apply List.in_map_iff in H2 as [s2 [Hs2 _]].
    rewrite <- Hs1 in Hs2. apply (f_equal core_argv) in Hs2.
    cbn [core_argv] in Hs2. symmetry. exact Hs2.
Qed.

(** THE ENGINE every bound below runs on: a duplicate-free list of cores
    each of whose four fields lies in a given enumeration weighs at most
    the product of four numbers bounding the four enumerations' sums.
    [qsum_core_incl_le] places the list inside the product enumeration,
    [qsum_full_support_product] evaluates that, and
    [Qmult_le_compat_nonneg] three times puts the four bounds together;
    the nonnegativity it asks for is the four enumerations' own.  Every
    export chooses its four enumerations and cites four one-coordinate
    bounds, and nothing else varies between them. *)
Lemma base_weight_product_bound : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall (Av Ae : list (list (list byte))) (Af : list Fs.Fs)
         (B : list (list byte)) (SA SE SF SB : Q) cs,
    (qsum (strings_point ra qa) Av <= SA)%Q ->
    (qsum (strings_point re qe) Ae <= SE)%Q ->
    (qsum (fs_point u v w) Af <= SF)%Q ->
    (qsum (fun s => geo_point ps (length s)) B <= SB)%Q ->
    List.NoDup cs ->
    (forall c, List.In c cs ->
       List.In (core_argv c) Av /\ List.In (core_envp c) Ae
       /\ List.In (core_fs c) Af /\ List.In (core_stdin c) B) ->
    (qsum (base_weight ra qa re qe u v w ps) cs <= SA * SE * SF * SB)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 Av Ae Af B SA SE SF SB cs
    HA HE HF HB Hnd Hall.
  assert (HA0 : (0 <= qsum (strings_point ra qa) Av)%Q)
    by (apply qsum_nonneg; intros x _; apply strings_point_nonneg; assumption).
  assert (HE0 : (0 <= qsum (strings_point re qe) Ae)%Q)
    by (apply qsum_nonneg; intros x _; apply strings_point_nonneg; assumption).
  assert (HF0 : (0 <= qsum (fs_point u v w) Af)%Q)
    by (apply qsum_nonneg; intros x _; apply fs_point_nonneg; assumption).
  assert (HB0 : (0 <= qsum (fun s => geo_point ps (length s)) B)%Q)
    by (apply qsum_nonneg; intros x _; apply geo_point_nonneg; assumption).
  eapply Qle_trans.
  - apply (qsum_core_incl_le _ _ (full_support_product Av Ae Af B)).
    + apply base_weight_nonneg; assumption.
    + exact Hnd.
    + intros c Hc. destruct (Hall c Hc) as [Ha [He [Hf Hs]]].
      destruct c as [argv envp fs s].
      cbn [core_argv core_envp core_fs core_stdin] in Ha, He, Hf, Hs.
      apply In_full_support_product; assumption.
  - rewrite qsum_full_support_product.
    apply Qmult_le_compat_nonneg; [| split; [exact HB0 | exact HB]].
    split.
    + apply Qmult_le_0_compat; [apply Qmult_le_0_compat |]; assumption.
    + apply Qmult_le_compat_nonneg; [| split; [exact HF0 | exact HF]].
      split.
      * apply Qmult_le_0_compat; assumption.
      * apply Qmult_le_compat_nonneg;
          [split; [exact HA0 | exact HA] | split; [exact HE0 | exact HE]].
Qed.

(* =========================================================================
   The file-system enumeration, and its cancellation
   ========================================================================= *)

(** Every file system extending [fs0] (as a list) by at most [M]
    further entries, each with a path shorter than [Lp] and contents
    shorter than [Lc].  It is [envp_enum] with a pair where that has an
    entry: two nested [short_inputs] enumerations per step, one for the
    path and one for the contents.  As with [envp_enum], duplicate-
    freedom is never proved and never needed for the bounds. *)
Fixpoint fs_enum (fs0 : Fs.Fs) (M Lp Lc : nat) : list Fs.Fs :=
  match M with
  | O => [fs0]
  | S M' =>
      fs0 :: List.flat_map (fun pth =>
               List.flat_map (fun d => fs_enum (fs0 ++ [(pth, d)]) M' Lp Lc)
                 (short_inputs Lc))
             (short_inputs Lp)
  end.

Lemma fs_enum_complete : forall M Lp Lc fs0 rest,
  (length rest <= M)%nat ->
  (forall e, List.In e rest ->
     (length (fst e) < Lp)%nat /\ (length (snd e) < Lc)%nat) ->
  List.In (fs0 ++ rest) (fs_enum fs0 M Lp Lc).
Proof.
  intros M Lp Lc. induction M as [| M IH]; intros fs0 rest Hlen Hent.
  - destruct rest as [| e rest]; [| cbn [length] in Hlen; lia].
    rewrite List.app_nil_r. left. reflexivity.
  - destruct rest as [| [pth d] rest].
    + rewrite List.app_nil_r. left. reflexivity.
    + destruct (Hent (pth, d) (or_introl eq_refl)) as [Hp Hd].
      cbn [fst snd] in Hp, Hd.
      right. apply List.in_flat_map. exists pth. split.
      * apply short_inputs_complete. exact Hp.
      * apply List.in_flat_map. exists d. split.
        -- apply short_inputs_complete. exact Hd.
        -- replace (fs0 ++ (pth, d) :: rest) with ((fs0 ++ [(pth, d)]) ++ rest)
             by (rewrite <- List.app_assoc; reflexivity).
           apply IH; [cbn [length] in Hlen; lia |].
           intros x Hx. apply Hent. right. exact Hx.
Qed.

(** ONE STEP OF THE FILE-SYSTEM CANCELLATION, exactly: the file systems
    one entry deeper than [fs0] carry [fs_factor fs0] times [(1 - u)]
    times what the path enumeration weighs times what the contents
    enumeration weighs — [qsum_envp_factor_step] with the second
    [short_inputs_sum] inside the first. *)
Lemma qsum_fs_factor_step : forall u v w fs0 Lp Lc,
  (qsum (fun pth => qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
                      (short_inputs Lc))
     (short_inputs Lp)
     == fs_factor u v w fs0 * (1 - u)
        * (1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc))%Q.
Proof.
  intros u v w fs0 Lp Lc.
  rewrite (qsum_ext (fun pth => qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
                                  (short_inputs Lc))
             (fun pth => ((fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - w) Lc))
                          * geo_point v (length pth))%Q)).
  2:{ intros pth _.
      rewrite (qsum_ext (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
                 (fun d => ((fs_factor u v w fs0 * (1 - u)
                             * geo_point v (length pth))
                            * geo_point w (length d))%Q))
        by (intros d _; rewrite fs_factor_app, fs_factor_one; ring).
      rewrite (qsum_scale (fs_factor u v w fs0 * (1 - u)
                           * geo_point v (length pth))%Q
                 (fun d => geo_point w (length d)) (short_inputs Lc)).
      rewrite short_inputs_sum, geo_prefix_sum_closed. ring. }
  rewrite (qsum_scale (fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - w) Lc))%Q
             (fun pth => geo_point v (length pth)) (short_inputs Lp)).
  rewrite short_inputs_sum, geo_prefix_sum_closed. ring.
Qed.

(** Three small facts about a rate in [[0, 1]] and its geometric tail,
    stated once because eight rates each need them below. *)
Lemma one_minus_unit : forall q,
  (0 <= q)%Q -> (q <= 1)%Q -> (0 <= 1 - q)%Q /\ (1 - q <= 1)%Q.
Proof.
  intros q Hq0 Hq1. split.
  - apply (Qle_minus_iff q 1). exact Hq1.
  - apply (proj2 (Qle_minus_iff (1 - q) 1)).
    apply (Qle_trans _ q); [exact Hq0 | apply Qle_of_Qeq; ring].
Qed.

Lemma geo_tail_unit : forall q L,
  (0 <= q)%Q -> (q <= 1)%Q ->
  (0 <= Qpow (1 - q) L)%Q /\ (Qpow (1 - q) L <= 1)%Q.
Proof.
  intros q L Hq0 Hq1. destruct (one_minus_unit q Hq0 Hq1) as [H0 H1].
  split; [apply Qpow_nonneg; exact H0 | apply Qpow_le_1; assumption].
Qed.

Lemma geo_head_unit : forall q L,
  (0 <= q)%Q -> (q <= 1)%Q ->
  (0 <= 1 - Qpow (1 - q) L)%Q /\ (1 - Qpow (1 - q) L <= 1)%Q.
Proof.
  intros q L Hq0 Hq1. destruct (geo_tail_unit q L Hq0 Hq1) as [H0 H1].
  apply one_minus_unit; assumption.
Qed.

(** THE CANCELLATION on the file-system coordinate: the whole enumeration
    weighs no more than the mass of the file systems extending [fs0].
    [envp_enum_sum_le]'s induction; the step charges the continuations
    [(1 - u)] times two partial sums each under [1], and the base case
    is [fs_point_le_factor]. *)
Lemma fs_enum_sum_le : forall u v w,
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q ->
  forall M Lp Lc fs0,
    (qsum (fs_point u v w) (fs_enum fs0 M Lp Lc) <= fs_factor u v w fs0)%Q.
Proof.
  intros u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 M Lp Lc.
  induction M as [| M IH]; intros fs0.
  - cbn [fs_enum]. rewrite qsum_cons, (@qsum_nil _ (fs_point u v w)).
    rewrite Qplus_0_r. apply fs_point_le_factor; assumption.
  - cbn [fs_enum]. rewrite qsum_cons.
    apply (Qle_trans _ (fs_point u v w fs0
                        + qsum (fun pth =>
                                  qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
                                    (short_inputs Lc))
                            (short_inputs Lp))%Q).
    + apply Qplus_le_compat; [apply Qle_refl |].
      apply (qsum_flat_map_le _ _
               (fun pth => qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
                             (short_inputs Lc))).
      intros pth _.
      apply (qsum_flat_map_le _ _
               (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))).
      intros d _. apply IH.
    + rewrite qsum_fs_factor_step. unfold fs_point.
      apply (Qle_trans _ (u * fs_factor u v w fs0
                          + fs_factor u v w fs0 * (1 - u) * 1 * 1)%Q);
        [| apply Qle_of_Qeq; ring].
      apply Qplus_le_compat; [apply Qle_refl |].
      assert (HF : (0 <= fs_factor u v w fs0 * (1 - u))%Q).
      { apply Qmult_le_0_compat; [apply fs_factor_nonneg; assumption |].
        apply (Qle_minus_iff u 1). exact Hu1. }
      destruct (geo_head_unit v Lp Hv0 Hv1) as [HGv0 HGv1].
      destruct (geo_head_unit w Lc Hw0 Hw1) as [HGw0 HGw1].
      apply Qmult_le_compat_nonneg; [| split; [exact HGw0 | exact HGw1]].
      split.
      * apply Qmult_le_0_compat; [exact HF | exact HGv0].
      * apply Qmult_le_compat_nonneg;
          [split; [exact HF | apply Qle_refl] | split; [exact HGv0 | exact HGv1]].
Qed.

(* =========================================================================
   The depths, read off the task's own list
   ========================================================================= *)

(** Eight depths where the envp-varying family reads three: an entry
    count and an entry length for argv, the same two for envp
    ([cores_envp_depth], [cores_entry_depth]), an entry count, a path
    length and a contents length for the file system, and the
    standard-input length ([cores_stdin_depth]).  Each exists because
    [Measure.weight_bound_T]'s lists are finite and for no other reason;
    the length depths are [S] of a maximum because [short_inputs]
    enumerates STRICTLY shorter lists. *)
Definition cores_argv_depth (cs : list FinCore) : nat :=
  List.list_max (List.map (fun c => length (core_argv c)) cs).

Definition cores_argv_entry_depth (cs : list FinCore) : nat :=
  S (List.list_max
       (List.map (fun c => List.list_max
                             (List.map (fun e => length e) (core_argv c))) cs)).

Definition cores_fs_depth (cs : list FinCore) : nat :=
  List.list_max (List.map (fun c => length (core_fs c)) cs).

Definition cores_fs_path_depth (cs : list FinCore) : nat :=
  S (List.list_max
       (List.map (fun c => List.list_max
                             (List.map (fun e => length (fst e)) (core_fs c)))
          cs)).

Definition cores_fs_contents_depth (cs : list FinCore) : nat :=
  S (List.list_max
       (List.map (fun c => List.list_max
                             (List.map (fun e => length (snd e)) (core_fs c)))
          cs)).

Lemma cores_argv_depth_ge : forall cs c,
  List.In c cs -> (length (core_argv c) <= cores_argv_depth cs)%nat.
Proof.
  intros cs c Hc. apply list_max_ge. apply List.in_map_iff.
  exists c. split; [reflexivity | exact Hc].
Qed.

Lemma cores_fs_depth_ge : forall cs c,
  List.In c cs -> (length (core_fs c) <= cores_fs_depth cs)%nat.
Proof.
  intros cs c Hc. apply list_max_ge. apply List.in_map_iff.
  exists c. split; [reflexivity | exact Hc].
Qed.

(** The three "strictly shorter than" depths share one proof: the entry
    is under its core's inner maximum, and that is under the outer
    maximum. *)
Lemma cores_inner_max_gt :
  forall (A : Type) (proj : FinCore -> list A) (len : A -> nat) cs c e,
    List.In c cs -> List.In e (proj c) ->
    (len e < S (List.list_max
                  (List.map (fun c0 => List.list_max (List.map len (proj c0)))
                     cs)))%nat.
Proof.
  intros A proj len cs c e Hc He.
  assert (Hinner : (len e <= List.list_max (List.map len (proj c)))%nat).
  { apply list_max_ge. apply List.in_map_iff.
    exists e. split; [reflexivity | exact He]. }
  assert (Houter : (List.list_max (List.map len (proj c))
                    <= List.list_max
                         (List.map (fun c0 => List.list_max
                                                (List.map len (proj c0))) cs))%nat).
  { apply list_max_ge. apply List.in_map_iff.
    exists c. split; [reflexivity | exact Hc]. }
  lia.
Qed.

Lemma cores_argv_entry_depth_gt : forall cs c e,
  List.In c cs -> List.In e (core_argv c) ->
  (length e < cores_argv_entry_depth cs)%nat.
Proof.
  intros cs c e Hc He. unfold cores_argv_entry_depth.
  exact (cores_inner_max_gt _ core_argv (fun e => length e) cs c e Hc He).
Qed.

Lemma cores_fs_path_depth_gt : forall cs c e,
  List.In c cs -> List.In e (core_fs c) ->
  (length (fst e) < cores_fs_path_depth cs)%nat.
Proof.
  intros cs c e Hc He. unfold cores_fs_path_depth.
  exact (cores_inner_max_gt _ core_fs (fun e => length (fst e)) cs c e Hc He).
Qed.

Lemma cores_fs_contents_depth_gt : forall cs c e,
  List.In c cs -> List.In e (core_fs c) ->
  (length (snd e) < cores_fs_contents_depth cs)%nat.
Proof.
  intros cs c e Hc He. unfold cores_fs_contents_depth.
  exact (cores_inner_max_gt _ core_fs (fun e => length (snd e)) cs c e Hc He).
Qed.

(** The four UNCONSTRAINED enumerations at the depths a list dictates:
    one per coordinate, from the empty prefix, each containing that
    coordinate of every core of the list and each summing to at most
    [1].  A marginal bound fixes one coordinate and cites these for the
    other three. *)
Definition argv_free (cs : list FinCore) : list (list (list byte)) :=
  envp_enum [] (cores_argv_depth cs) (cores_argv_entry_depth cs).

Definition envp_free (cs : list FinCore) : list (list (list byte)) :=
  envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs).

Definition fs_free (cs : list FinCore) : list Fs.Fs :=
  fs_enum [] (cores_fs_depth cs) (cores_fs_path_depth cs)
    (cores_fs_contents_depth cs).

Definition stdin_free (cs : list FinCore) : list (list byte) :=
  bytes_cyl [] (cores_stdin_depth cs).

Lemma argv_free_In : forall cs c,
  List.In c cs -> List.In (core_argv c) (argv_free cs).
Proof.
  intros cs c Hc. unfold argv_free.
  change (core_argv c) with ([] ++ core_argv c).
  apply envp_enum_complete; [apply cores_argv_depth_ge; exact Hc |].
  intros e He. apply (cores_argv_entry_depth_gt cs c e Hc). exact He.
Qed.

Lemma envp_free_In : forall cs c,
  List.In c cs -> List.In (core_envp c) (envp_free cs).
Proof.
  intros cs c Hc. unfold envp_free.
  change (core_envp c) with ([] ++ core_envp c).
  apply envp_enum_complete; [apply cores_envp_depth_ge; exact Hc |].
  intros e He. apply (cores_entry_depth_gt cs c e Hc). exact He.
Qed.

Lemma fs_free_In : forall cs c,
  List.In c cs -> List.In (core_fs c) (fs_free cs).
Proof.
  intros cs c Hc. unfold fs_free.
  change (core_fs c) with ([] ++ core_fs c).
  apply fs_enum_complete; [apply cores_fs_depth_ge; exact Hc |].
  intros e He.
  split; [apply (cores_fs_path_depth_gt cs c e Hc)
         | apply (cores_fs_contents_depth_gt cs c e Hc)]; exact He.
Qed.

Lemma stdin_free_In : forall cs c,
  List.In c cs -> List.In (core_stdin c) (stdin_free cs).
Proof.
  intros cs c Hc. unfold stdin_free.
  change (core_stdin c) with ([] ++ core_stdin c).
  apply bytes_cyl_In. apply cores_stdin_depth_ge. exact Hc.
Qed.

Lemma argv_free_sum_le : forall r q,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= q)%Q -> (q <= 1)%Q ->
  forall cs, (qsum (strings_point r q) (argv_free cs) <= 1)%Q.
Proof.
  intros r q Hr0 Hr1 Hq0 Hq1 cs. unfold argv_free, strings_point.
  apply (Qle_trans _ (envp_factor r q []));
    [apply envp_enum_sum_le; assumption | cbn [envp_factor]; apply Qle_refl].
Qed.

Lemma envp_free_sum_le : forall r q,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= q)%Q -> (q <= 1)%Q ->
  forall cs, (qsum (strings_point r q) (envp_free cs) <= 1)%Q.
Proof.
  intros r q Hr0 Hr1 Hq0 Hq1 cs. unfold envp_free, strings_point.
  apply (Qle_trans _ (envp_factor r q []));
    [apply envp_enum_sum_le; assumption | cbn [envp_factor]; apply Qle_refl].
Qed.

Lemma fs_free_sum_le : forall u v w,
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q ->
  forall cs, (qsum (fs_point u v w) (fs_free cs) <= 1)%Q.
Proof.
  intros u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 cs. unfold fs_free.
  apply (Qle_trans _ (fs_factor u v w []));
    [apply fs_enum_sum_le; assumption | cbn [fs_factor]; apply Qle_refl].
Qed.

Lemma stdin_free_sum_le : forall p,
  (0 <= p)%Q -> (p <= 1)%Q ->
  forall cs, (qsum (fun s => geo_point p (length s)) (stdin_free cs) <= 1)%Q.
Proof.
  intros p Hp0 Hp1 cs. unfold stdin_free.
  apply (Qle_trans _ (geo_mass p (length (@nil byte))));
    [apply bytes_cyl_sum_le; assumption |].
  unfold geo_mass. cbn [length]. rewrite Qpow_0. apply Qle_refl.
Qed.

(* =========================================================================
   The cylinder bound over cores, and the whole-space certificate
   ========================================================================= *)

(** The cores this bound is about: argv extending [xs], environment
    extending [es], file system extending [fs0] AS A LIST, standard
    input extending [bs].  Four existentials, for the reason
    [in_envp_stdin_cylinder] has two.  The file-system prefix is a LIST
    prefix — the first entries of the association list — which is the
    shape the enumeration wants; a task describing a fire set by ONE
    file's contents wants [full_support_base_file_bound] below
    instead. *)
Definition in_full_support_cylinder (xs es : list (list byte)) (fs0 : Fs.Fs)
    (bs : list byte) (c : FinCore) : Prop :=
  exists aext eext fext sext,
    c = mkFinCore (xs ++ aext) (es ++ eext) (fs0 ++ fext) (bs ++ sext).

(** The cylinder's mass: one continuation factor per coordinate. *)
Definition full_support_base_cylinder_mass (ra qa re qe u v w ps : Q)
    (xs es : list (list byte)) (fs0 : Fs.Fs) (bs : list byte) : Q :=
  (strings_factor ra qa xs * strings_factor re qe es * fs_factor u v w fs0
   * geo_mass ps (length bs))%Q.

Lemma full_support_base_cylinder_mass_closed_form :
  forall ra qa re qe u v w ps xs es fs0 bs,
  (full_support_base_cylinder_mass ra qa re qe u v w ps xs es fs0 bs
     == (Qpow (1 - ra) (length xs) * entries_geo_product qa xs)
        * (Qpow (1 - re) (length es) * entries_geo_product qe es)
        * (Qpow (1 - u) (length fs0) * fs_entries_product v w fs0)
        * (Qpow (1 - ps) (length bs) * Qpow (1 # 256) (length bs)))%Q.
Proof.
  intros ra qa re qe u v w ps xs es fs0 bs.
  unfold full_support_base_cylinder_mass, strings_factor.
  rewrite !envp_factor_closed_form, fs_factor_closed_form, geo_mass_closed_form.
  ring.
Qed.

(** THE BOUND OVER CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.  Eight depths are read
    off the list, the four enumerations at those depths contain it, and
    each enumeration is bounded by its own cancellation lemma. *)
Lemma base_weight_cylinder_bound : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall xs es fs0 bs cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> in_full_support_cylinder xs es fs0 bs c) ->
    (qsum (base_weight ra qa re qe u v w ps) cs
       <= full_support_base_cylinder_mass ra qa re qe u v w ps xs es fs0 bs)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs es fs0 bs cs Hnd Hcyl.
  unfold full_support_base_cylinder_mass, strings_factor.
  apply (base_weight_product_bound ra qa re qe u v w ps
           Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1
           Hps0 Hps1
           (envp_enum xs (cores_argv_depth cs) (cores_argv_entry_depth cs))
           (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs))
           (fs_enum fs0 (cores_fs_depth cs) (cores_fs_path_depth cs)
              (cores_fs_contents_depth cs))
           (bytes_cyl bs (cores_stdin_depth cs))).
  - unfold strings_point. apply envp_enum_sum_le; assumption.
  - unfold strings_point. apply envp_enum_sum_le; assumption.
  - apply fs_enum_sum_le; assumption.
  - apply bytes_cyl_sum_le; assumption.
  - exact Hnd.
  - intros c Hc. destruct (Hcyl c Hc) as [aext [eext [fext [sext Heq]]]].
    assert (Hargv := cores_argv_depth_ge cs c Hc).
    assert (Henvp := cores_envp_depth_ge cs c Hc).
    assert (Hfs := cores_fs_depth_ge cs c Hc).
    assert (Hstdin := cores_stdin_depth_ge cs c Hc).
    rewrite Heq in Hargv, Henvp, Hfs, Hstdin.
    cbn [core_argv core_envp core_fs core_stdin] in Hargv, Henvp, Hfs, Hstdin.
    rewrite List.length_app in Hargv, Henvp, Hfs, Hstdin.
    rewrite Heq. cbn [core_argv core_envp core_fs core_stdin].
    split; [| split; [| split]].
    + apply envp_enum_complete; [lia |].
      intros e He. apply (cores_argv_entry_depth_gt cs c e Hc).
      rewrite Heq. cbn [core_argv]. apply List.in_or_app. right. exact He.
    + apply envp_enum_complete; [lia |].
      intros e He. apply (cores_entry_depth_gt cs c e Hc).
      rewrite Heq. cbn [core_envp]. apply List.in_or_app. right. exact He.
    + apply fs_enum_complete;
        [exact (Nat.le_trans _ _ _ (Nat.le_add_l _ _) Hfs) |].
      intros e He.
      split; [apply (cores_fs_path_depth_gt cs c e Hc)
             | apply (cores_fs_contents_depth_gt cs c e Hc)];
        rewrite Heq; cbn [core_fs]; apply List.in_or_app; right; exact He.
    + apply bytes_cyl_In. lia.
Qed.

(** Any duplicate-free list of cores at all weighs at most [1]: the
    cylinder bound at the four empty prefixes, where every continuation
    factor is [1]. *)
Lemma base_weight_mass_le_1 : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall cs, List.NoDup cs ->
    (qsum (base_weight ra qa re qe u v w ps) cs <= 1)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 cs Hnd.
  apply (Qle_trans _ (full_support_base_cylinder_mass ra qa re qe u v w ps
                        [] [] [] [])).
  - apply base_weight_cylinder_bound; try assumption.
    intros c _. destruct c as [argv envp fs s].
    exists argv, envp, fs, s. reflexivity.
  - apply Qle_of_Qeq.
    unfold full_support_base_cylinder_mass, strings_factor, geo_mass.
    cbn [envp_factor fs_factor length]. rewrite Qpow_0. ring.
Qed.

(** THE EXPORT: a list of records with duplicate-free cores, all lying
    in the cylinder, weighs at most the cylinder's mass.  The hypothesis
    is the one [Measure.weight_bound_T] carries, and
    [core_sum_map_fin_core] is the only step between them. *)
Lemma full_support_base_bound :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs es fs0 bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     in_full_support_cylinder xs es fs0 bs (fin_core f)) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l
     <= full_support_base_cylinder_mass ra qa re qe u v w ps xs es fs0 bs)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs es fs0 bs l Hnd Hcyl.
  cbn [cd_weight full_support_base]. rewrite core_sum_map_fin_core.
  apply base_weight_cylinder_bound; try assumption.
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. apply Hcyl. exact Hin.
Qed.

(** UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass [1].  There is no "off the environment" disjunct to widen by,
    because there is no environment to be off: every core is in the
    cylinder at the four empty prefixes. *)
Lemma full_support_base_mass_upper :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 l,
  List.NoDup (List.map fin_core l) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l
     <= cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                   Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 l Hnd.
  cbn [cd_weight cd_mass full_support_base]. rewrite core_sum_map_fin_core.
  apply base_weight_mass_le_1; assumption.
Qed.

(* =========================================================================
   The marginal bounds: one coordinate constrained, three charged [1]
   ========================================================================= *)

(** Fixing ONE coordinate exactly and charging the other three their
    whole declared mass.  These are the bounds a task composes the base
    family with a structured family through: a fire set described by
    its argv alone is charged the argv's own weight, and nothing about
    the other coordinates is assumed.  Each is the engine with one
    singleton enumeration and three free ones. *)
Lemma base_weight_argv_bound : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall xs cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> core_argv c = xs) ->
    (qsum (base_weight ra qa re qe u v w ps) cs <= strings_point ra qa xs)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs cs Hnd Hall.
  apply (Qle_trans _ (strings_point ra qa xs * 1 * 1 * 1)%Q);
    [| apply Qle_of_Qeq; ring].
  apply (base_weight_product_bound ra qa re qe u v w ps
           Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1
           Hps0 Hps1 [xs] (envp_free cs) (fs_free cs) (stdin_free cs)).
  - rewrite qsum_cons, qsum_nil. apply Qle_of_Qeq. ring.
  - apply envp_free_sum_le; assumption.
  - apply fs_free_sum_le; assumption.
  - apply stdin_free_sum_le; assumption.
  - exact Hnd.
  - intros c Hc. split; [| split; [| split]].
    + left. symmetry. apply Hall. exact Hc.
    + apply envp_free_In. exact Hc.
    + apply fs_free_In. exact Hc.
    + apply stdin_free_In. exact Hc.
Qed.

Lemma base_weight_envp_bound : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall es cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> core_envp c = es) ->
    (qsum (base_weight ra qa re qe u v w ps) cs <= strings_point re qe es)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 es cs Hnd Hall.
  apply (Qle_trans _ (1 * strings_point re qe es * 1 * 1)%Q);
    [| apply Qle_of_Qeq; ring].
  apply (base_weight_product_bound ra qa re qe u v w ps
           Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1
           Hps0 Hps1 (argv_free cs) [es] (fs_free cs) (stdin_free cs)).
  - apply argv_free_sum_le; assumption.
  - rewrite qsum_cons, qsum_nil. apply Qle_of_Qeq. ring.
  - apply fs_free_sum_le; assumption.
  - apply stdin_free_sum_le; assumption.
  - exact Hnd.
  - intros c Hc. split; [| split; [| split]].
    + apply argv_free_In. exact Hc.
    + left. symmetry. apply Hall. exact Hc.
    + apply fs_free_In. exact Hc.
    + apply stdin_free_In. exact Hc.
Qed.

Lemma base_weight_fs_bound : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall fs0 cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> core_fs c = fs0) ->
    (qsum (base_weight ra qa re qe u v w ps) cs <= fs_point u v w fs0)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 fs0 cs Hnd Hall.
  apply (Qle_trans _ (1 * 1 * fs_point u v w fs0 * 1)%Q);
    [| apply Qle_of_Qeq; ring].
  apply (base_weight_product_bound ra qa re qe u v w ps
           Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1
           Hps0 Hps1 (argv_free cs) (envp_free cs) [fs0] (stdin_free cs)).
  - apply argv_free_sum_le; assumption.
  - apply envp_free_sum_le; assumption.
  - rewrite qsum_cons, qsum_nil. apply Qle_of_Qeq. ring.
  - apply stdin_free_sum_le; assumption.
  - exact Hnd.
  - intros c Hc. split; [| split; [| split]].
    + apply argv_free_In. exact Hc.
    + apply envp_free_In. exact Hc.
    + left. symmetry. apply Hall. exact Hc.
    + apply stdin_free_In. exact Hc.
Qed.

(** The standard-input coordinate's two bounds, in the shapes the other
    families export them: a list drawn from one LENGTH slice weighs at
    most [ps * (1 - ps) ^ n] ([stdin_envp_geometric_slice_bound]'s
    constant), and a list confined to standard inputs of length at most
    [n] weighs at most [1 - (1 - ps) ^ (n + 1)]
    ([stdin_envp_geometric_bound_by_max_length]'s).  Neither fixes any
    other coordinate.  The second MISSES THE TAIL, and the tail is what
    [full_support_base_mass_not_attained] is made of. *)
Lemma base_weight_stdin_slice_bound : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall n cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> length (core_stdin c) = n) ->
    (qsum (base_weight ra qa re qe u v w ps) cs <= ps * Qpow (1 - ps) n)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n cs Hnd Hall.
  apply (Qle_trans _ (1 * 1 * 1 * (ps * Qpow (1 - ps) n))%Q);
    [| apply Qle_of_Qeq; ring].
  apply (base_weight_product_bound ra qa re qe u v w ps
           Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1
           Hps0 Hps1 (argv_free cs) (envp_free cs) (fs_free cs) (byte_lists n)).
  - apply argv_free_sum_le; assumption.
  - apply envp_free_sum_le; assumption.
  - apply fs_free_sum_le; assumption.
  - apply Qle_of_Qeq. apply byte_lists_sum.
  - exact Hnd.
  - intros c Hc. split; [| split; [| split]].
    + apply argv_free_In. exact Hc.
    + apply envp_free_In. exact Hc.
    + apply fs_free_In. exact Hc.
    + rewrite <- (Hall c Hc). apply byte_lists_complete.
Qed.

Lemma base_weight_bound_by_max_length : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall n cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> (length (core_stdin c) <= n)%nat) ->
    (qsum (base_weight ra qa re qe u v w ps) cs <= 1 - Qpow (1 - ps) (S n))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n cs Hnd Hall.
  apply (Qle_trans _ (1 * 1 * 1 * (1 - Qpow (1 - ps) (S n)))%Q);
    [| apply Qle_of_Qeq; ring].
  apply (base_weight_product_bound ra qa re qe u v w ps
           Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1
           Hps0 Hps1 (argv_free cs) (envp_free cs) (fs_free cs)
           (short_inputs (S n))).
  - apply argv_free_sum_le; assumption.
  - apply envp_free_sum_le; assumption.
  - apply fs_free_sum_le; assumption.
  - apply Qle_of_Qeq. rewrite short_inputs_sum. apply geo_prefix_sum_closed.
  - exact Hnd.
  - intros c Hc. split; [| split; [| split]].
    + apply argv_free_In. exact Hc.
    + apply envp_free_In. exact Hc.
    + apply fs_free_In. exact Hc.
    + apply short_inputs_complete. assert (H := Hall c Hc). lia.
Qed.

(* =========================================================================
   The file-contents marginal: one entry constrained, the rest of the
   file system free
   ========================================================================= *)

(** The cores the composability bound prices: the file at [pth] — what [fs_file]
    reads, the first entry with that key, or nothing — EXTENDS [bs].
    Nothing else about the file system is fixed: not its entry count,
    not any other entry, not the position of the entry at [pth]. *)
Definition file_at_extends (pth : Fs.path) (bs : list byte) (c : FinCore) : Prop :=
  exists ext, fs_file pth (core_fs c) = bs ++ ext.

(** THE INJECTION.  Strip the first [n] bytes off the contents of the
    first entry keyed [pth], leave everything else alone.  On the cores
    [file_at_extends pth bs] describes, with [n = length bs], it is
    weight-preserving up to the one factor [geo_mass w (length bs)]
    ([base_weight_strip]) and injective ([core_strip_inj]), and those
    two facts are the whole of the marginal bound: the stripped list is
    a duplicate-free list of cores, which weighs at most [1], and the
    original weighs the stripped list times the factor. *)
Fixpoint fs_strip (pth : Fs.path) (n : nat) (fs : Fs.Fs) : Fs.Fs :=
  match fs with
  | [] => []
  | (q, d) :: r =>
      if Fs.path_eqb pth q then (q, List.skipn n d) :: r
      else (q, d) :: fs_strip pth n r
  end.

Definition core_strip (pth : Fs.path) (n : nat) (c : FinCore) : FinCore :=
  mkFinCore (core_argv c) (core_envp c) (fs_strip pth n (core_fs c)) (core_stdin c).

Lemma skipn_length_app : forall {A : Type} (l1 l2 : list A),
  List.skipn (length l1) (l1 ++ l2) = l2.
Proof.
  intros A l1 l2. induction l1 as [| x l1 IH]; [reflexivity |].
  cbn [length List.app List.skipn]. exact IH.
Qed.

Lemma Qpow_plus_exp : forall x m n, (Qpow x (m + n) == Qpow x m * Qpow x n)%Q.
Proof.
  intros x m n. induction m as [| m IH].
  - cbn [Nat.add]. rewrite Qpow_0. ring.
  - cbn [Nat.add]. rewrite !Qpow_succ, IH. ring.
Qed.

(** A byte string that extends [bs] weighs [geo_mass] of the prefix
    times the weight of what follows: the single identity the injection
    pays with. *)
Lemma geo_point_app : forall p (bs ext : list byte),
  (geo_point p (length (bs ++ ext))
     == geo_mass p (length bs) * geo_point p (length ext))%Q.
Proof.
  intros p bs ext. unfold geo_point, geo_mass.
  rewrite List.length_app, Qpow_plus_exp. ring.
Qed.

Lemma fs_strip_zero : forall pth fs, fs_strip pth 0 fs = fs.
Proof.
  intros pth fs. induction fs as [| [q d] r IH]; [reflexivity |].
  cbn [fs_strip]. destruct (Fs.path_eqb pth q); [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma fs_lookup_of_fs_file_cons : forall pth fs b l,
  fs_file pth fs = b :: l -> Fs.fs_lookup fs pth = Some (b :: l).
Proof.
  intros pth fs b l H. unfold fs_file in H.
  destruct (Fs.fs_lookup fs pth) as [d |]; cbn in H;
    [rewrite H; reflexivity | discriminate H].
Qed.

Lemma fs_factor_strip : forall u v w pth bs ext fs,
  Fs.fs_lookup fs pth = Some (bs ++ ext) ->
  (fs_factor u v w fs
     == geo_mass w (length bs) * fs_factor u v w (fs_strip pth (length bs) fs))%Q.
Proof.
  intros u v w pth bs ext fs. induction fs as [| [q d] r IH]; intros Hlk.
  - cbn [Fs.fs_lookup] in Hlk. discriminate Hlk.
  - cbn [Fs.fs_lookup] in Hlk. cbn [fs_strip].
    destruct (Fs.path_eqb pth q) eqn:Heq.
    + injection Hlk as Hd. subst d. cbn [fs_factor].
      rewrite skipn_length_app, geo_point_app. ring.
    + cbn [fs_factor]. rewrite (IH Hlk). ring.
Qed.

Lemma fs_strip_inj : forall pth bs fs1 fs2 ext1 ext2,
  Fs.fs_lookup fs1 pth = Some (bs ++ ext1) ->
  Fs.fs_lookup fs2 pth = Some (bs ++ ext2) ->
  fs_strip pth (length bs) fs1 = fs_strip pth (length bs) fs2 ->
  fs1 = fs2.
Proof.
  intros pth bs fs1. induction fs1 as [| [q1 d1] r1 IH];
    intros fs2 ext1 ext2 H1 H2 Hs.
  - cbn [Fs.fs_lookup] in H1. discriminate H1.
  - destruct fs2 as [| [q2 d2] r2]; [cbn [Fs.fs_lookup] in H2; discriminate H2 |].
    cbn [Fs.fs_lookup] in H1, H2. cbn [fs_strip] in Hs.
    destruct (Fs.path_eqb pth q1) eqn:Hq1; destruct (Fs.path_eqb pth q2) eqn:Hq2.
    + injection H1 as Hd1. injection H2 as Hd2. subst d1 d2.
      injection Hs as Hq Hsk Hr. subst q2 r2.
      rewrite !skipn_length_app in Hsk. subst ext2. reflexivity.
    + injection Hs as Hq _ _. subst q2. rewrite Hq1 in Hq2. discriminate Hq2.
    + injection Hs as Hq _ _. subst q2. rewrite Hq1 in Hq2. discriminate Hq2.
    + injection Hs as Hq Hd Hr. subst q2 d2.
      rewrite (IH r2 ext1 ext2 H1 H2 Hr). reflexivity.
Qed.

Lemma base_weight_strip : forall ra qa re qe u v w ps pth bs c,
  file_at_extends pth bs c ->
  (base_weight ra qa re qe u v w ps c
     == geo_mass w (length bs)
        * base_weight ra qa re qe u v w ps (core_strip pth (length bs) c))%Q.
Proof.
  intros ra qa re qe u v w ps pth bs c [ext Hext].
  unfold base_weight, core_strip. cbn [core_argv core_envp core_fs core_stdin].
  destruct bs as [| b bs'].
  - cbn [length]. rewrite fs_strip_zero. unfold geo_mass. rewrite Qpow_0. ring.
  - cbn [List.app] in Hext. apply fs_lookup_of_fs_file_cons in Hext.
    unfold fs_point.
    rewrite (fs_factor_strip u v w pth (b :: bs') ext (core_fs c) Hext).
    ring.
Qed.

Lemma core_strip_inj : forall pth bs c1 c2,
  file_at_extends pth bs c1 -> file_at_extends pth bs c2 ->
  core_strip pth (length bs) c1 = core_strip pth (length bs) c2 ->
  c1 = c2.
Proof.
  intros pth bs [a1 e1 f1 s1] [a2 e2 f2 s2] [ext1 H1] [ext2 H2] Heq.
  unfold core_strip in Heq.
  cbn [core_argv core_envp core_fs core_stdin] in Heq, H1, H2.
  injection Heq as Ha He Hf Hs. subst a2 e2 s2.
  f_equal. destruct bs as [| b bs'].
  - cbn [length] in Hf. rewrite !fs_strip_zero in Hf. exact Hf.
  - cbn [List.app] in H1, H2.
    apply fs_lookup_of_fs_file_cons in H1, H2.
    exact (fs_strip_inj pth (b :: bs') f1 f2 ext1 ext2 H1 H2 Hf).
Qed.

Lemma core_strip_argv : forall pth n c, core_argv (core_strip pth n c) = core_argv c.
Proof. reflexivity. Qed.

Lemma NoDup_map_core_strip : forall pth bs cs,
  (forall c, List.In c cs -> file_at_extends pth bs c) ->
  List.NoDup cs ->
  List.NoDup (List.map (core_strip pth (length bs)) cs).
Proof.
  intros pth bs cs Hall Hnd. apply NoDup_map_inj; [| exact Hnd].
  intros x y Hx Hy Heq. exact (core_strip_inj pth bs x y (Hall x Hx) (Hall y Hy) Heq).
Qed.

Lemma qsum_base_weight_strip : forall ra qa re qe u v w ps pth bs cs,
  (forall c, List.In c cs -> file_at_extends pth bs c) ->
  (qsum (base_weight ra qa re qe u v w ps) cs
     == geo_mass w (length bs)
        * qsum (base_weight ra qa re qe u v w ps)
            (List.map (core_strip pth (length bs)) cs))%Q.
Proof.
  intros ra qa re qe u v w ps pth bs cs Hall. rewrite qsum_map.
  rewrite <- (qsum_scale (geo_mass w (length bs))
                (fun c => base_weight ra qa re qe u v w ps
                            (core_strip pth (length bs) c)) cs).
  apply qsum_ext. intros c Hc. apply base_weight_strip. apply Hall. exact Hc.
Qed.

(** THE FILE-CONTENTS MARGINAL: cores whose file at [pth] extends [bs]
    weigh at most [geo_mass w (length bs)] — the prefix's cylinder mass
    on the contents coordinate, with the entry count, every other
    entry, the path's own bytes and the other three coordinates all
    charged [1].  At [bs = []] the hypothesis is vacuous and the bound
    is the whole-space [1]. *)
Lemma base_weight_file_bound : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall pth bs cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> file_at_extends pth bs c) ->
    (qsum (base_weight ra qa re qe u v w ps) cs <= geo_mass w (length bs))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 pth bs cs Hnd Hall.
  rewrite (qsum_base_weight_strip ra qa re qe u v w ps pth bs cs Hall).
  apply (Qle_trans _ (geo_mass w (length bs) * 1)%Q);
    [| apply Qle_of_Qeq; ring].
  apply Qmult_le_compat_nonneg.
  - split; [apply geo_mass_nonneg; exact Hw1 | apply Qle_refl].
  - split.
    + apply qsum_nonneg. intros x _. apply base_weight_nonneg; assumption.
    + apply base_weight_mass_le_1; try assumption.
      apply NoDup_map_core_strip; assumption.
Qed.

(** THE COMPOSABILITY BOUND: cores whose
    argv is [xs] and whose file at [pth] extends [bs] weigh at most
    [strings_point ra qa xs * geo_mass w (length bs)], the remaining
    coordinates' total being under [1].  The injection pays the
    contents factor and preserves argv ([core_strip_argv]), so the
    stripped list is one [base_weight_argv_bound] applies to. *)
Lemma base_weight_argv_file_bound : forall ra qa re qe u v w ps,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  forall xs pth bs cs,
    List.NoDup cs ->
    (forall c, List.In c cs -> core_argv c = xs /\ file_at_extends pth bs c) ->
    (qsum (base_weight ra qa re qe u v w ps) cs
       <= strings_point ra qa xs * geo_mass w (length bs))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs pth bs cs Hnd Hall.
  rewrite (qsum_base_weight_strip ra qa re qe u v w ps pth bs cs)
    by (intros c Hc; exact (proj2 (Hall c Hc))).
  apply (Qle_trans _ (geo_mass w (length bs) * strings_point ra qa xs)%Q);
    [| apply Qle_of_Qeq; ring].
  apply Qmult_le_compat_nonneg.
  - split; [apply geo_mass_nonneg; exact Hw1 | apply Qle_refl].
  - split.
    + apply qsum_nonneg. intros x _. apply base_weight_nonneg; assumption.
    + apply base_weight_argv_bound; try assumption.
      * apply NoDup_map_core_strip; [intros c Hc; exact (proj2 (Hall c Hc)) | exact Hnd].
      * intros c Hc. apply List.in_map_iff in Hc as [c0 [Hc0 Hin]].
        rewrite <- Hc0, core_strip_argv. exact (proj1 (Hall c0 Hin)).
Qed.

(* =========================================================================
   The marginal exports, on records
   ========================================================================= *)

Lemma full_support_base_argv_bound :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> fin_argv f = xs) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l <= strings_point ra qa xs)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs l Hnd Hall.
  cbn [cd_weight full_support_base]. rewrite core_sum_map_fin_core.
  apply base_weight_argv_bound; try assumption.
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. cbn [fin_core core_argv]. apply Hall. exact Hin.
Qed.

Lemma full_support_base_envp_bound :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 es l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> fin_envp f = es) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l <= strings_point re qe es)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 es l Hnd Hall.
  cbn [cd_weight full_support_base]. rewrite core_sum_map_fin_core.
  apply base_weight_envp_bound; try assumption.
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. cbn [fin_core core_envp]. apply Hall. exact Hin.
Qed.

Lemma full_support_base_fs_bound :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 fs0 l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> fin_image_fs f = fs0) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l <= fs_point u v w fs0)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 fs0 l Hnd Hall.
  cbn [cd_weight full_support_base]. rewrite core_sum_map_fin_core.
  apply base_weight_fs_bound; try assumption.
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. cbn [fin_core core_fs]. apply Hall. exact Hin.
Qed.

Lemma full_support_base_slice_bound :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> length (fin_stdin f) = n) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l <= ps * Qpow (1 - ps) n)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n l Hnd Hall.
  cbn [cd_weight full_support_base]. rewrite core_sum_map_fin_core.
  apply base_weight_stdin_slice_bound; try assumption.
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. cbn [fin_core core_stdin]. apply Hall. exact Hin.
Qed.

Lemma full_support_base_bound_by_max_length :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> (length (fin_stdin f) <= n)%nat) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l <= 1 - Qpow (1 - ps) (S n))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n l Hnd Hall.
  cbn [cd_weight full_support_base]. rewrite core_sum_map_fin_core.
  apply base_weight_bound_by_max_length; try assumption.
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. cbn [fin_core core_stdin]. apply Hall. exact Hin.
Qed.

Lemma full_support_base_file_bound :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 pth bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l -> file_at_extends pth bs (fin_core f)) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l <= geo_mass w (length bs))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 pth bs l Hnd Hall.
  cbn [cd_weight full_support_base]. rewrite core_sum_map_fin_core.
  apply (base_weight_file_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
           Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 pth bs);
    [exact Hnd |].
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. apply Hall. exact Hin.
Qed.

(** The composability bound at the [_argv1] driver shape: argv is [prog; pth] and
    the file at [pth] extends [bs].  [path_argv] is the argv shape the
    file families' [_argv1] constructors build, so a task that already
    couples its argv to its path through it lands here directly. *)
Lemma full_support_base_argv_file_bound :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs pth bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_argv f = xs /\ file_at_extends pth bs (fin_core f)) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l <= strings_point ra qa xs * geo_mass w (length bs))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs pth bs l Hnd Hall.
  cbn [cd_weight full_support_base]. rewrite core_sum_map_fin_core.
  apply (base_weight_argv_file_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
           Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs pth bs);
    [exact Hnd |].
  intros c Hc. apply List.in_map_iff in Hc as [f [Hf Hin]].
  rewrite <- Hf. destruct (Hall f Hin) as [Ha Hfile].
  split; [cbn [fin_core core_argv]; exact Ha | exact Hfile].
Qed.

Lemma full_support_base_path_argv_file_bound :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 prog pth bs l,
  List.NoDup (List.map fin_core l) ->
  (forall f, List.In f l ->
     fin_argv f = path_argv prog pth /\ file_at_extends pth bs (fin_core f)) ->
  (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
     l <= strings_point ra qa [prog; pth] * geo_mass w (length bs))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 prog pth bs l Hnd Hall.
  exact (full_support_base_argv_file_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
           Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
           (path_argv prog pth) pth bs l Hnd Hall).
Qed.

(* =========================================================================
   ... and this mass is a SUPREMUM and not a maximum either
   ========================================================================= *)

(** For [ps < 1] NO admissible list weighs the declared mass.  The
    proof is [stdin_envp_geometric_mass_not_attained]'s unchanged: the
    list's own longest standard input is a horizon, and beyond it sits
    a positive tail the list does not collect.  Only [ps < 1] is asked
    for — the shortfall is already there on the standard-input axis, so
    the other seven rates may be as degenerate as they like. *)
Lemma full_support_base_mass_not_attained :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1,
  (ps < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                            Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
       l
       < cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 Hlt l Hnd.
  cbn [cd_mass full_support_base].
  pose (n := List.list_max (List.map (fun f => length (fin_stdin f)) l)).
  apply (Qle_lt_trans _ (1 - Qpow (1 - ps) (S n))%Q).
  - apply full_support_base_bound_by_max_length; [exact Hnd |].
    intros f Hf. apply list_max_ge. apply List.in_map_iff.
    exists f. split; [reflexivity | exact Hf].
  - apply (proj2 (Qlt_minus_iff (1 - Qpow (1 - ps) (S n)) 1)).
    apply (Qlt_le_trans _ (Qpow (1 - ps) (S n))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qpow_pos. apply (Qlt_minus_iff ps 1). exact Hlt.
Qed.

Lemma full_support_base_mass_supremum_not_maximum :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1,
  (ps < 1)%Q ->
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    ~ (core_sum (cd_weight (full_support_base ra qa re qe u v w ps
                              Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
                              Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l
         == cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                       Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 Hlt l Hnd.
  apply Qlt_not_eq.
  apply full_support_base_mass_not_attained; assumption.
Qed.

(* =========================================================================
   The lower certificate for [full_support_base]
   ========================================================================= *)

(** THE FILE-SYSTEM WITNESS FAMILY: every list of exactly [m] pairs
    whose paths are shorter than [Lp] and whose contents are shorter
    than [Lc], and the union of those over [m < M].  It is [envps_len]
    and [envps_upto] with a pair where they have an entry, and it is
    duplicate-free for the same reason ([fss_len_nodup]).  [fs_enum] is
    not reused, for the reason [envp_enum] is not: the certificate needs
    a duplicate-free list and the bounds' enumeration is not one. *)
Fixpoint fss_len (Lp Lc m : nat) : list Fs.Fs :=
  match m with
  | O => [[]]
  | S m' =>
      List.flat_map
        (fun pth =>
           List.flat_map
             (fun d => List.map (fun fs => (pth, d) :: fs) (fss_len Lp Lc m'))
             (short_inputs Lc))
        (short_inputs Lp)
  end.

Fixpoint fss_upto (Lp Lc M : nat) : list Fs.Fs :=
  match M with
  | O => []
  | S M' => fss_len Lp Lc M' ++ fss_upto Lp Lc M'
  end.

Lemma fss_len_In_length : forall Lp Lc m fs,
  List.In fs (fss_len Lp Lc m) -> length fs = m.
Proof.
  intros Lp Lc m. induction m as [| m IH]; intros fs Hfs.
  - destruct Hfs as [Heq | []]. rewrite <- Heq. reflexivity.
  - cbn [fss_len] in Hfs.
    apply List.in_flat_map in Hfs as [pth [_ Hfs]].
    apply List.in_flat_map in Hfs as [d [_ Hfs]].
    apply List.in_map_iff in Hfs as [fs' [Heq Hin]].
    rewrite <- Heq. cbn [length]. rewrite (IH fs' Hin). reflexivity.
Qed.

Lemma fss_len_nodup : forall Lp Lc m, List.NoDup (fss_len Lp Lc m).
Proof.
  intros Lp Lc m. induction m as [| m IH].
  - cbn [fss_len]. apply List.NoDup_cons; [intros [] | apply List.NoDup_nil].
  - cbn [fss_len]. apply NoDup_flat_map.
    + apply short_inputs_nodup.
    + intros pth _. apply NoDup_flat_map.
      * apply short_inputs_nodup.
      * intros d _. apply NoDup_map_inj; [| exact IH].
        intros x y _ _ Heq.
        apply (f_equal (@List.tl (Fs.path * list byte))) in Heq.
        cbn [List.tl] in Heq. exact Heq.
      * intros d1 d2 fs _ _ H1 H2.
        apply List.in_map_iff in H1 as [x1 [Hx1 _]].
        apply List.in_map_iff in H2 as [x2 [Hx2 _]].
        rewrite <- Hx1 in Hx2. injection Hx2. intros. symmetry. assumption.
    + intros p1 p2 fs _ _ H1 H2.
      apply List.in_flat_map in H1 as [d1 [_ H1]].
      apply List.in_map_iff in H1 as [x1 [Hx1 _]].
      apply List.in_flat_map in H2 as [d2 [_ H2]].
      apply List.in_map_iff in H2 as [x2 [Hx2 _]].
      rewrite <- Hx1 in Hx2. injection Hx2. intros. symmetry. assumption.
Qed.

Lemma fss_upto_In_length : forall Lp Lc M fs,
  List.In fs (fss_upto Lp Lc M) -> (length fs < M)%nat.
Proof.
  intros Lp Lc M. induction M as [| M IH]; intros fs Hfs; [destruct Hfs |].
  cbn [fss_upto] in Hfs. apply List.in_app_or in Hfs as [Hfs | Hfs].
  - rewrite (fss_len_In_length Lp Lc M fs Hfs). lia.
  - apply IH in Hfs. lia.
Qed.

Lemma fss_upto_nodup : forall Lp Lc M, List.NoDup (fss_upto Lp Lc M).
Proof.
  intros Lp Lc M. induction M as [| M IH]; [apply List.NoDup_nil |].
  cbn [fss_upto]. apply List.NoDup_app.
  - apply fss_len_nodup.
  - exact IH.
  - intros fs Hin1 Hin2. apply fss_upto_In_length in Hin2.
    rewrite (fss_len_In_length Lp Lc M fs Hin1) in Hin2. lia.
Qed.

(** ONE FULL ENTRY-COUNT SLICE of file systems weighs a power, as
    [qsum_entries_geo_product_envps_len] does for environments; the
    base is the PRODUCT of what the path enumeration and the contents
    enumeration collect, because each slot draws both. *)
Lemma qsum_fs_entries_product_fss_len : forall v w Lp Lc m,
  (qsum (fs_entries_product v w) (fss_len Lp Lc m)
     == Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m)%Q.
Proof.
  intros v w Lp Lc m. induction m as [| m IH].
  - cbn [fss_len]. unfold qsum. cbn [List.fold_right fs_entries_product].
    rewrite Qpow_0. ring.
  - cbn [fss_len]. rewrite qsum_flat_map. cbv beta.
    rewrite (qsum_ext
               (fun pth => qsum (fs_entries_product v w)
                             (List.flat_map
                                (fun d => List.map (fun fs => (pth, d) :: fs)
                                            (fss_len Lp Lc m))
                                (short_inputs Lc)))
               (fun pth => ((Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m
                             * (1 - Qpow (1 - w) Lc))
                            * geo_point v (length pth))%Q)).
    2:{ intros pth _. rewrite qsum_flat_map. cbv beta.
        rewrite (qsum_ext
                   (fun d => qsum (fs_entries_product v w)
                               (List.map (fun fs => (pth, d) :: fs) (fss_len Lp Lc m)))
                   (fun d => ((Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m
                               * geo_point v (length pth))
                              * geo_point w (length d))%Q)).
        2:{ intros d _. rewrite qsum_map. cbv beta.
            rewrite (qsum_ext (fun fs => fs_entries_product v w ((pth, d) :: fs))
                       (fun fs => ((geo_point v (length pth) * geo_point w (length d))
                                   * fs_entries_product v w fs)%Q))
              by (intros fs _; cbn [fs_entries_product]; reflexivity).
            rewrite (qsum_scale (geo_point v (length pth) * geo_point w (length d))%Q
                       (fs_entries_product v w) (fss_len Lp Lc m)).
            rewrite IH. ring. }
        rewrite (qsum_scale (Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m
                             * geo_point v (length pth))%Q
                   (fun d => geo_point w (length d)) (short_inputs Lc)).
        rewrite short_inputs_sum, geo_prefix_sum_closed. ring. }
    rewrite (qsum_scale (Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m
                         * (1 - Qpow (1 - w) Lc))%Q
               (fun pth => geo_point v (length pth)) (short_inputs Lp)).
    rewrite short_inputs_sum, geo_prefix_sum_closed, Qpow_succ. ring.
Qed.

Lemma qsum_fs_point_fss_len : forall u v w Lp Lc m,
  (qsum (fs_point u v w) (fss_len Lp Lc m)
     == u * Qpow (1 - u) m
        * Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m)%Q.
Proof.
  intros u v w Lp Lc m.
  rewrite (qsum_ext (fs_point u v w)
             (fun fs => ((u * Qpow (1 - u) m) * fs_entries_product v w fs)%Q)).
  2:{ intros fs Hfs. rewrite fs_point_closed_form.
      rewrite (fss_len_In_length Lp Lc m fs Hfs). ring. }
  rewrite (qsum_scale (u * Qpow (1 - u) m)%Q (fs_entries_product v w)
             (fss_len Lp Lc m)).
  rewrite qsum_fs_entries_product_fss_len. ring.
Qed.

(** The partial sum over entry counts is [envp_prefix_sum] at the
    product base — the same [Fixpoint], because the file-system
    coordinate is the environment coordinate with a different slot
    total. *)
Lemma qsum_fs_point_fss_upto : forall u v w Lp Lc M,
  (qsum (fs_point u v w) (fss_upto Lp Lc M)
     == envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) M)%Q.
Proof.
  intros u v w Lp Lc M. induction M as [| M IH]; [reflexivity |].
  cbn [fss_upto envp_prefix_sum].
  rewrite qsum_app, IH, qsum_fs_point_fss_len. reflexivity.
Qed.

(* =========================================================================
   The margin arithmetic, four factors deep
   ========================================================================= *)

(** TWO FACTORS IN [[0, 1]] COMPOSE THEIR MARGINS: if each falls short
    of [1] by at most its margin, the product falls short by at most
    the sum.  [Qmargins_three] is this at three factors with a
    different hypothesis shape; this form asks only that the two
    factors be in the unit interval, which is what lets it be applied
    to a running product without tracking which margins are under
    [1] — an entry-length margin [M * x] need not be.  The proof is one
    square: [x * y] exceeds [x + y - 1] by [(1 - x) * (1 - y)]. *)
Lemma Qprod_margin : forall x y a b,
  (0 <= x)%Q -> (x <= 1)%Q -> (0 <= y)%Q -> (y <= 1)%Q ->
  (1 - a <= x)%Q -> (1 - b <= y)%Q ->
  (1 - (a + b) <= x * y)%Q.
Proof.
  intros x y a b Hx0 Hx1 Hy0 Hy1 Ha Hb.
  apply (Qle_trans _ (x + y - 1)%Q).
  - apply (Qle_trans _ ((1 - a) + (1 - b) - 1)%Q); [apply Qle_of_Qeq; ring |].
    apply Qplus_le_compat;
      [apply Qplus_le_compat; [exact Ha | exact Hb] | apply Qle_refl].
  - apply (proj2 (Qle_minus_iff (x + y - 1) (x * y))).
    apply (Qle_trans _ ((1 - x) * (1 - y))%Q); [| apply Qle_of_Qeq; ring].
    apply Qmult_le_0_compat;
      [apply (Qle_minus_iff x 1); exact Hx1 | apply (Qle_minus_iff y 1); exact Hy1].
Qed.

Lemma Qmult_unit : forall x y,
  (0 <= x)%Q -> (x <= 1)%Q -> (0 <= y)%Q -> (y <= 1)%Q ->
  (0 <= x * y)%Q /\ (x * y <= 1)%Q.
Proof.
  intros x y Hx0 Hx1 Hy0 Hy1. split.
  - apply Qmult_le_0_compat; assumption.
  - apply (Qle_trans _ (1 * 1)%Q); [| apply Qle_of_Qeq; ring].
    apply Qmult_le_compat_nonneg; split; assumption.
Qed.

(** The partial sum is in the unit interval: nonnegative term by term,
    and under [1 - (1 - r) ^ M] because each slot collects at most
    [1]. *)
Lemma envp_prefix_sum_nonneg : forall r G M,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= G)%Q ->
  (0 <= envp_prefix_sum r G M)%Q.
Proof.
  intros r G M Hr0 Hr1 HG0. induction M as [| M IH]; [apply Qle_refl |].
  cbn [envp_prefix_sum]. apply Qplus_nonneg; [| exact IH].
  apply Qmult_le_0_compat; [| apply Qpow_nonneg; exact HG0].
  apply Qmult_le_0_compat; [exact Hr0 |].
  apply Qpow_nonneg. apply (Qle_minus_iff r 1). exact Hr1.
Qed.

Lemma envp_prefix_sum_le : forall r G M,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= G)%Q -> (G <= 1)%Q ->
  (envp_prefix_sum r G M <= 1 - Qpow (1 - r) M)%Q.
Proof.
  intros r G M Hr0 Hr1 HG0 HG1. induction M as [| M IH].
  - cbn [envp_prefix_sum]. rewrite Qpow_0. apply Qle_of_Qeq. ring.
  - cbn [envp_prefix_sum]. rewrite (Qpow_succ (1 - r) M).
    apply (Qle_trans _ (r * Qpow (1 - r) M * 1 + (1 - Qpow (1 - r) M))%Q);
      [| apply Qle_of_Qeq; ring].
    apply Qplus_le_compat; [| exact IH].
    assert (HrP : (0 <= r * Qpow (1 - r) M)%Q).
    { apply Qmult_le_0_compat; [exact Hr0 |].
      apply Qpow_nonneg. apply (Qle_minus_iff r 1). exact Hr1. }
    apply Qmult_le_compat_nonneg;
      [split; [exact HrP | apply Qle_refl]
      | split; [apply Qpow_nonneg; exact HG0 | apply Qpow_le_1; assumption]].
Qed.

Lemma envp_prefix_sum_unit : forall r G M,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= G)%Q -> (G <= 1)%Q ->
  (0 <= envp_prefix_sum r G M)%Q /\ (envp_prefix_sum r G M <= 1)%Q.
Proof.
  intros r G M Hr0 Hr1 HG0 HG1. split; [apply envp_prefix_sum_nonneg; assumption |].
  apply (Qle_trans _ (1 - Qpow (1 - r) M)%Q);
    [apply envp_prefix_sum_le; assumption | apply geo_head_unit; assumption].
Qed.

(** ONE STRING COORDINATE'S MARGIN: its partial sum at depths [(M, L)]
    is within [M * (1 - q) ^ L + (1 - r) ^ M] of [1] — the entry-length
    shortfall over [M] slots ([Qpow_one_minus_lower]) plus the
    entry-count tail, composed by [Qprod_margin] and put under the sum
    by [envp_prefix_sum_lower].  No strict hypothesis appears; the
    strictness is spent choosing the depths. *)
Lemma strings_prefix_margin : forall r q L M,
  (0 <= r)%Q -> (r <= 1)%Q -> (0 <= q)%Q -> (q <= 1)%Q ->
  (1 - (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M)
     <= envp_prefix_sum r (1 - Qpow (1 - q) L) M)%Q.
Proof.
  intros r q L M Hr0 Hr1 Hq0 Hq1.
  destruct (geo_tail_unit q L Hq0 Hq1) as [Hx0 Hx1].
  destruct (geo_head_unit q L Hq0 Hq1) as [HG0 HG1].
  destruct (geo_tail_unit r M Hr0 Hr1) as [Hb0 Hb1].
  destruct (geo_head_unit r M Hr0 Hr1) as [Hc0 Hc1].
  apply (Qle_trans _ (Qpow (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - r) M))%Q).
  - apply Qprod_margin.
    + apply Qpow_nonneg. exact HG0.
    + apply Qpow_le_1; assumption.
    + exact Hc0.
    + exact Hc1.
    + apply Qpow_one_minus_lower; assumption.
    + apply Qle_refl.
  - apply envp_prefix_sum_lower; assumption.
Qed.

(** THE FILE-SYSTEM COORDINATE'S MARGIN: two entry-length shortfalls,
    one per half of the pair, and one entry-count tail. *)
Lemma fs_prefix_margin : forall u v w Lp Lc M,
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q ->
  (1 - (Qnat M * Qpow (1 - v) Lp + Qnat M * Qpow (1 - w) Lc + Qpow (1 - u) M)
     <= envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) M)%Q.
Proof.
  intros u v w Lp Lc M Hu0 Hu1 Hv0 Hv1 Hw0 Hw1.
  destruct (geo_tail_unit v Lp Hv0 Hv1) as [Hxv0 Hxv1].
  destruct (geo_head_unit v Lp Hv0 Hv1) as [HGv0 HGv1].
  destruct (geo_tail_unit w Lc Hw0 Hw1) as [Hxw0 Hxw1].
  destruct (geo_head_unit w Lc Hw0 Hw1) as [HGw0 HGw1].
  destruct (geo_head_unit u M Hu0 Hu1) as [Hc0 Hc1].
  destruct (Qmult_unit _ _ HGv0 HGv1 HGw0 HGw1) as [HG0 HG1].
  apply (Qle_trans _ (Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) M
                      * (1 - Qpow (1 - u) M))%Q).
  - apply Qprod_margin.
    + apply Qpow_nonneg. exact HG0.
    + apply Qpow_le_1; assumption.
    + exact Hc0.
    + exact Hc1.
    + rewrite Qpow_mult. apply Qprod_margin.
      * apply Qpow_nonneg. exact HGv0.
      * apply Qpow_le_1; assumption.
      * apply Qpow_nonneg. exact HGw0.
      * apply Qpow_le_1; assumption.
      * apply Qpow_one_minus_lower; assumption.
      * apply Qpow_one_minus_lower; assumption.
    + apply Qle_refl.
  - apply envp_prefix_sum_lower; assumption.
Qed.

(** THE MARGIN ARITHMETIC OF THE CERTIFICATE, WITH THE EIGHT DEPTHS
    STILL FREE: if the eight tails together come in under [eps], the
    witness's partial sum is within [eps] of [1].  Four factors, each
    in the unit interval, each within its own margin; [Qprod_margin]
    three times.  No strict hypothesis appears. *)
Lemma full_support_margin_at_depths :
  forall ra qa re qe u v w ps eps Ma La Me Le Mf Lp Lc k,
  (0 <= ra)%Q -> (ra <= 1)%Q -> (0 <= qa)%Q -> (qa <= 1)%Q ->
  (0 <= re)%Q -> (re <= 1)%Q -> (0 <= qe)%Q -> (qe <= 1)%Q ->
  (0 <= u)%Q -> (u <= 1)%Q -> (0 <= v)%Q -> (v <= 1)%Q ->
  (0 <= w)%Q -> (w <= 1)%Q -> (0 <= ps)%Q -> (ps <= 1)%Q ->
  (Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
   + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
   + (Qnat Mf * Qpow (1 - v) Lp + Qnat Mf * Qpow (1 - w) Lc + Qpow (1 - u) Mf)
   + Qpow (1 - ps) k <= eps)%Q ->
  (1 - eps
     <= envp_prefix_sum ra (1 - Qpow (1 - qa) La) Ma
        * envp_prefix_sum re (1 - Qpow (1 - qe) Le) Me
        * envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) Mf
        * (1 - Qpow (1 - ps) k))%Q.
Proof.
  intros ra qa re qe u v w ps eps Ma La Me Le Mf Lp Lc k
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    Hsum.
  destruct (geo_head_unit qa La Hqa0 Hqa1) as [HGa0 HGa1].
  destruct (geo_head_unit qe Le Hqe0 Hqe1) as [HGe0 HGe1].
  destruct (geo_head_unit v Lp Hv0 Hv1) as [HGv0 HGv1].
  destruct (geo_head_unit w Lc Hw0 Hw1) as [HGw0 HGw1].
  destruct (Qmult_unit _ _ HGv0 HGv1 HGw0 HGw1) as [HGf0 HGf1].
  destruct (envp_prefix_sum_unit ra _ Ma Hra0 Hra1 HGa0 HGa1) as [HSa0 HSa1].
  destruct (envp_prefix_sum_unit re _ Me Hre0 Hre1 HGe0 HGe1) as [HSe0 HSe1].
  destruct (envp_prefix_sum_unit u _ Mf Hu0 Hu1 HGf0 HGf1) as [HSf0 HSf1].
  destruct (geo_head_unit ps k Hps0 Hps1) as [HSs0 HSs1].
  destruct (Qmult_unit _ _ HSa0 HSa1 HSe0 HSe1) as [HSae0 HSae1].
  destruct (Qmult_unit _ _ HSae0 HSae1 HSf0 HSf1) as [HSaef0 HSaef1].
  apply (Qle_trans _ (1 - (Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
                           + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
                           + (Qnat Mf * Qpow (1 - v) Lp + Qnat Mf * Qpow (1 - w) Lc
                              + Qpow (1 - u) Mf)
                           + Qpow (1 - ps) k))%Q).
  - apply (proj2 (Qle_minus_iff (1 - eps) _)).
    apply (Qle_trans _ (eps + - (Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
                                 + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
                                 + (Qnat Mf * Qpow (1 - v) Lp
                                    + Qnat Mf * Qpow (1 - w) Lc + Qpow (1 - u) Mf)
                                 + Qpow (1 - ps) k))%Q);
      [apply (proj1 (Qle_minus_iff _ eps)); exact Hsum | apply Qle_of_Qeq; ring].
  - apply Qprod_margin; [exact HSaef0 | exact HSaef1 | exact HSs0 | exact HSs1 | | apply Qle_refl].
    apply Qprod_margin; [exact HSae0 | exact HSae1 | exact HSf0 | exact HSf1 | | apply fs_prefix_margin; assumption].
    apply Qprod_margin; [exact HSa0 | exact HSa1 | exact HSe0 | exact HSe1 | |];
      apply strings_prefix_margin; assumption.
Qed.

(** ... AND THE DEPTHS THAT MEET IT.  Each strictness buys exactly one
    depth, eight in all, and each is asked for an eighth of the margin.
    An entry-count depth is [geo_gap_small] on its stop rate; an
    entry-length depth is chosen AFTER the entry count it has to cover
    ([entry_depth_for], which is the [M + 1] division
    [envp_stdin_depths_above] does inline, named because it is done
    four times here).  No floors are taken: nothing but the margin has
    a say for a single family. *)
Lemma entry_depth_for : forall q delta M,
  (0 < q)%Q -> (q <= 1)%Q -> (0 < delta)%Q ->
  exists L : nat, (Qnat M * Qpow (1 - q) L <= delta)%Q.
Proof.
  intros q delta M Hqpos Hq1 Hd.
  assert (HD : (0 < Qnat M + 1)%Q).
  { apply (Qlt_le_trans _ 1); [reflexivity |].
    apply (Qle_trans _ (0 + 1)%Q); [apply Qle_of_Qeq; ring |].
    apply Qplus_le_compat; [apply Qnat_nonneg | apply Qle_refl]. }
  assert (Hbnd : (0 < delta * / (Qnat M + 1))%Q)
    by (apply Qmult_lt_0_compat; [exact Hd | apply Qinv_lt_0_compat; exact HD]).
  destruct (geo_gap_small q (delta * / (Qnat M + 1)) Hqpos Hq1 Hbnd) as [L HL].
  exists L.
  assert (HDne : ~ ((Qnat M + 1) == 0)%Q)
    by (apply Qnot_eq_sym, Qlt_not_eq; exact HD).
  assert (HMD : (Qnat M * / (Qnat M + 1) <= 1)%Q).
  { apply (Qle_trans _ ((Qnat M + 1) * / (Qnat M + 1))%Q).
    - apply Qmult_le_compat_r.
      + apply (Qle_trans _ (Qnat M + 0)%Q);
          [ apply Qle_of_Qeq; ring
          | apply Qplus_le_compat; [apply Qle_refl | apply Qle_0_1]].
      + apply Qinv_le_0_compat. apply Qlt_le_weak. exact HD.
    - apply Qle_of_Qeq. apply Qmult_inv_r. exact HDne. }
  apply (Qle_trans _ (Qpow (1 - q) L * Qnat M)%Q); [apply Qle_of_Qeq; ring |].
  apply (Qle_trans _ (delta * / (Qnat M + 1) * Qnat M)%Q);
    [apply Qmult_le_compat_r; [exact HL | apply Qnat_nonneg] |].
  apply (Qle_trans _ (Qnat M * / (Qnat M + 1) * delta)%Q);
    [apply Qle_of_Qeq; ring |].
  apply (Qle_trans _ (1 * delta)%Q); [| apply Qle_of_Qeq; ring].
  apply Qmult_le_compat_r; [exact HMD | apply Qlt_le_weak; exact Hd].
Qed.

Lemma full_support_depths_above : forall ra qa re qe u v w ps eps,
  (0 < ra)%Q -> (ra <= 1)%Q -> (0 < qa)%Q -> (qa <= 1)%Q ->
  (0 < re)%Q -> (re <= 1)%Q -> (0 < qe)%Q -> (qe <= 1)%Q ->
  (0 < u)%Q -> (u <= 1)%Q -> (0 < v)%Q -> (v <= 1)%Q ->
  (0 < w)%Q -> (w <= 1)%Q -> (0 < ps)%Q -> (ps <= 1)%Q ->
  (0 < eps)%Q ->
  exists Ma La Me Le Mf Lp Lc k : nat,
    (Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
     + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
     + (Qnat Mf * Qpow (1 - v) Lp + Qnat Mf * Qpow (1 - w) Lc + Qpow (1 - u) Mf)
     + Qpow (1 - ps) k <= eps)%Q.
Proof.
  intros ra qa re qe u v w ps eps Hrapos Hra1 Hqapos Hqa1 Hrepos Hre1 Hqepos Hqe1
    Hupos Hu1 Hvpos Hv1 Hwpos Hw1 Hpspos Hps1 Heps.
  assert (Heps8 : (0 < eps * (1 # 8))%Q)
    by (apply Qmult_lt_0_compat; [exact Heps | reflexivity]).
  destruct (geo_gap_small ra (eps * (1 # 8)) Hrapos Hra1 Heps8) as [Ma HMa].
  destruct (entry_depth_for qa (eps * (1 # 8)) Ma Hqapos Hqa1 Heps8) as [La HLa].
  destruct (geo_gap_small re (eps * (1 # 8)) Hrepos Hre1 Heps8) as [Me HMe].
  destruct (entry_depth_for qe (eps * (1 # 8)) Me Hqepos Hqe1 Heps8) as [Le HLe].
  destruct (geo_gap_small u (eps * (1 # 8)) Hupos Hu1 Heps8) as [Mf HMf].
  destruct (entry_depth_for v (eps * (1 # 8)) Mf Hvpos Hv1 Heps8) as [Lp HLp].
  destruct (entry_depth_for w (eps * (1 # 8)) Mf Hwpos Hw1 Heps8) as [Lc HLc].
  destruct (geo_gap_small ps (eps * (1 # 8)) Hpspos Hps1 Heps8) as [k Hk].
  exists Ma, La, Me, Le, Mf, Lp, Lc, k.
  apply (Qle_trans _ (eps * (1 # 8) + eps * (1 # 8)
                      + (eps * (1 # 8) + eps * (1 # 8))
                      + (eps * (1 # 8) + eps * (1 # 8) + eps * (1 # 8))
                      + eps * (1 # 8))%Q);
    [| apply Qle_of_Qeq; ring].
  repeat apply Qplus_le_compat; assumption.
Qed.

(* =========================================================================
   The witness, and the certificate
   ========================================================================= *)

(** THE WITNESS FAMILY: one record per quadruple drawn from the four
    prefix families.  It is a product, exactly as the bounds'
    enumeration is, and duplicate-free because all four coordinates are
    ([NoDup_full_support_product]).  Nothing in it is claimed valid. *)
Definition full_support_lower_witness (Ma La Me Le Mf Lp Lc k : nat)
    : list FinProcInput :=
  List.map core_input
    (full_support_product (envps_upto La Ma) (envps_upto Le Me)
       (fss_upto Lp Lc Mf) (short_inputs k)).

Lemma map_fin_core_full_support_lower_witness : forall Ma La Me Le Mf Lp Lc k,
  List.map fin_core (full_support_lower_witness Ma La Me Le Mf Lp Lc k)
    = full_support_product (envps_upto La Ma) (envps_upto Le Me)
        (fss_upto Lp Lc Mf) (short_inputs k).
Proof.
  intros Ma La Me Le Mf Lp Lc k. unfold full_support_lower_witness.
  apply map_fin_core_core_input.
Qed.

Lemma full_support_lower_witness_nodup : forall Ma La Me Le Mf Lp Lc k,
  List.NoDup (List.map fin_core (full_support_lower_witness Ma La Me Le Mf Lp Lc k)).
Proof.
  intros Ma La Me Le Mf Lp Lc k. rewrite map_fin_core_full_support_lower_witness.
  apply NoDup_full_support_product;
    [apply envps_upto_nodup | apply envps_upto_nodup
    | apply fss_upto_nodup | apply short_inputs_nodup].
Qed.

(** THE WITNESS, at each choice of the eight depths: an admissible list
    weighing exactly the product of the four coordinates' partial sums.
    Unconditional arithmetic, as [stdin_envp_geometric_mass_lower_witness]
    is. *)
Lemma full_support_base_mass_lower_witness :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 Ma La Me Le Mf Lp Lc k,
  List.NoDup (List.map fin_core (full_support_lower_witness Ma La Me Le Mf Lp Lc k))
  /\ (core_sum (cd_weight (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                             Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1))
        (full_support_lower_witness Ma La Me Le Mf Lp Lc k)
        == envp_prefix_sum ra (1 - Qpow (1 - qa) La) Ma
           * envp_prefix_sum re (1 - Qpow (1 - qe) Le) Me
           * envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) Mf
           * (1 - Qpow (1 - ps) k))%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 Ma La Me Le Mf Lp Lc k.
  split; [apply full_support_lower_witness_nodup |].
  cbn [cd_weight full_support_base].
  rewrite core_sum_map_fin_core, map_fin_core_full_support_lower_witness.
  rewrite qsum_full_support_product. unfold strings_point.
  rewrite !qsum_envp_point_envps_upto, qsum_fs_point_fss_upto,
    short_inputs_sum, geo_prefix_sum_closed.
  reflexivity.
Qed.

(** THE LOWER CERTIFICATE: for every margin [eps] there is an admissible
    list weighing at least the declared mass minus that margin.  With
    [full_support_base_mass_upper] above it, the declared [1] is the
    least upper bound of the admissible partial sums — approached but,
    by [full_support_base_mass_not_attained], never met.

    ALL EIGHT STRICT INEQUALITIES ARE HYPOTHESES OF THIS LEMMA AND NOT
    TIGHTENINGS OF THE CONSTRUCTOR, for the reason
    [stdin_geometric_mass_lower_certificate] gives: everything above
    this lemma holds at every degenerate rate, and moving the
    hypotheses into the constructor would invalidate every degenerate
    member a consumer had already built.  A margin is asked for, eight
    natural numbers are produced, and the finite list they name is
    exhibited. *)
Lemma full_support_base_mass_lower_certificate :
  forall ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
         Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 eps,
  (0 < ra)%Q -> (0 < qa)%Q -> (0 < re)%Q -> (0 < qe)%Q ->
  (0 < u)%Q -> (0 < v)%Q -> (0 < w)%Q -> (0 < ps)%Q -> (0 < eps)%Q ->
  exists l : list FinProcInput,
    List.NoDup (List.map fin_core l)
    /\ (cd_mass (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
                   Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) - eps
          <= core_sum (cd_weight (full_support_base ra qa re qe u v w ps
                                    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
                                    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1)) l)%Q.
Proof.
  intros ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 eps
    Hrapos Hqapos Hrepos Hqepos Hupos Hvpos Hwpos Hpspos Heps.
  destruct (full_support_depths_above ra qa re qe u v w ps eps
              Hrapos Hra1 Hqapos Hqa1 Hrepos Hre1 Hqepos Hqe1
              Hupos Hu1 Hvpos Hv1 Hwpos Hw1 Hpspos Hps1 Heps)
    as [Ma [La [Me [Le [Mf [Lp [Lc [k Hsum]]]]]]]].
  exists (full_support_lower_witness Ma La Me Le Mf Lp Lc k).
  split; [apply full_support_lower_witness_nodup |].
  rewrite (proj2 (full_support_base_mass_lower_witness ra qa re qe u v w ps
                    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
                    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 Ma La Me Le Mf Lp Lc k)).
  cbn [cd_mass full_support_base].
  apply full_support_margin_at_depths; assumption.
Qed.
