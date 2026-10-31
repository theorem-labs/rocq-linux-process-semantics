(** * EquivalenceDefinition.MustExit — every maximal execution exits with one code

    TRUST BOUNDARY: this file is part of the trusted specification.
    Proof files never edit it.  A top-level check that ascribes against a
    module type mentioning [must_exit_with] depends on the definitions
    here remaining fixed, exactly as the baseline check depends on
    [Equivalence].

    [Equivalence] states obligations about the RELATION between two
    binaries — the baseline shape and its error-free strengthening.
    This file states an obligation about ONE
    binary: on this input, whatever the nondeterminism resolves to, the
    process terminates, and the status a waiting parent reads is [code].
    That is the shape a decision procedure needs — a classifier binary
    answers by exiting 0 or 1, and "answers" has to mean every execution
    answers, the same way, in finite time.

    ** Why an inductive, and why three premises

    The definition is [must_exit_at] below: an accessibility predicate
    over the [Run.SNext] transitions, following [Run.all_traces_error]'s
    shape.  Three properties are wanted and each buys one premise.

    - TERMINATION.  Being INDUCTIVE is what supplies it: a configuration
      with an infinite [Run.SNext] execution cannot construct the proof
      merely because an exiting alternative stays available at every
      finite prefix.  This is the same argument [Run.all_traces_error]'s
      header makes, and it is the reason the predicate is not defined as
      "every maximal trace contains an [State.ExitEv]", which a
      coinductive reading would satisfy vacuously.
    - NO STUCK EXECUTION.  The progress premise ([exists evs st, sstep
      …]) stops a configuration with no successor at all from passing
      because the [forall]-over-successors premise is vacuous there.
      Without it, a wedged run would count as "exits with 0".
    - NO ERRORING EXECUTION.  Premise [forall evs, ~ sstep … SError] is
      the one thing this predicate needs that [Run.all_traces_error] does
      not have, and it is not optional.  [Run.SError] is a step_to
      CONSTRUCTOR, not a configuration, so quantifying over [SNext]
      successors says nothing about it: a configuration that can either
      step on to an exit or take the error transition would satisfy an
      [SNext]-only definition.  A classifier that faults on some
      resolution has not decided anything, so error branches are refuted
      explicitly.

    The two cases are made syntactically exclusive by giving the step
    case the premise [m_halted (cfg_model c) = None].  That premise is
    DERIVABLE from progress — every [Run.sstep] constructor requires
    [m_halted model = None], which [sstep_not_halted] below records — so
    it does not change which configurations satisfy the predicate; it is
    there so that case analysis on one proof against another
    ([must_exit_at_exclusive]) does not have to re-derive it.  The
    consequence worth stating: a configuration halted with a DIFFERENT
    code satisfies neither case, so [must_exit_at] pins the code rather
    than merely asserting termination ([must_exit_at_wrong_code]).

    ** The exit code is compared DIRECTLY, not masked here

    Design decision, and the evidence for it.  [Sys.Kernel.Exit.exit_spec]
    (theories/LinuxProcessSem/Sys/Kernel/Exit.v) is

        set_halted (bv_and code (Z_to_bv 64 255)) ;; ret_only (Z_to_bv 64 0)

    — the MASK IS APPLIED BY THE SPEC, before the status reaches the
    model.  [Sys.Kernel.Exit.exit_spec] is the only spec arm that writes
    [State.m_halted] at all, and [Sys.SyscallTable.spec_table] routes
    both exit (93) and exit_group (94) to it, so every value
    [State.m_halted] can ever hold is already [bv_and a0 255].  The
    routing half of that is machine-checked, by
    [Checks.Examples.exit_dispatch_iff]; the "only arm" half is not, and
    it is the half a reader should re-check when a syscall lands.  Note
    that [State.with_halted], the setter underneath [Monad.set_halted],
    is ALSO applied directly about a dozen times elsewhere — in the
    executable checker ([Checks.Sys.Kernel.Exit]), its witness
    ([Checks.Witness.Kernel.Exit]), the simulation layers
    ([Common.ExitSim], [Common.ShapeAlg], [Common.MmapSim],
    [Common.FileSim], [Common.CatSim], [Common.WallSim]) and
    [Checks.Examples] itself.  Every such site passes a value already
    masked with 255, so
    the conclusion survives, but "[Monad.set_halted] is the only writer"
    would not be true and is not what this rests on.

    [Run.sstep_exit] copies that stored word
    verbatim into the [State.ExitEv] it emits.

    Therefore [must_exit_with] compares the stored word with plain
    equality and applies NO mask of its own.  Masking again would be
    idempotent and harmless, but it would also be a second, independent
    statement of the ABI that could drift from the spec's; comparing
    directly keeps [Sys.Kernel.Exit.exit_spec] the single place the low
    byte is defined.

    What a caller must supply, in consequence: [must_exit_with] means
    what Linux observes exactly when [code] is itself a masked byte.
    That the low byte is what a waiting parent reads is the kernel's
    own encoding: [SYSCALL_DEFINE1(exit, int, error_code)] calls
    [do_exit((error_code & 0xff) << 8)] and
    [SYSCALL_DEFINE1(exit_group, ...)] calls
    [do_group_exit((error_code & 0xff) << 8)], and the wait side reads
    that field back with [infop->status = status >> 8] — so the seven
    high bytes of the argument are discarded before any status exists
    and cannot be recovered (kernel/exit.c, Linux v6.18.46, commit
    1f99e9ab748f).  [Z_to_bv 64 0] and [Z_to_bv 64 1] — the two verdicts
    a classifier uses — are already in that range, so
    [must_exit_with (Z_to_bv 64 0)] is precisely "exit(0) as a waiting
    parent sees it".  A [code] outside
    [0 .. 255] names a status no run of this model can reach, which is
    sound but useless; it is not rejected here because the config-level
    predicate is about arbitrary configurations, and a config's
    [State.m_halted] field is not itself constrained to the byte range.

    Write those words PLAIN, with no [bv_and … 255] wrapper.  Re-masking
    is the identity on a value already in [0 .. 255], so a wrapped form
    would be propositionally correct — but it is not SYNTACTICALLY equal
    to the plain form, and equality on [code] is what the lemmas here
    conclude and consume.  [must_exit_at_exclusive] and
    [must_exit_with_exclusive] hand back a bare [code1 = code2]; under a
    mixed convention, turning that into the fact one wanted takes a
    conversion step at every use site instead of none.  One convention,
    the plain one.

    ** Non-vacuity

    [must_exit_with_realizes] is this file's guard, the analogue of
    [Run.all_traces_error_reaches_error]: whatever satisfies the
    predicate really does emit an [State.ExitEv] carrying [code] on some
    execution, so the predicate cannot be satisfied by saying nothing.
    Refutability is [must_exit_at_refuted_by_error] and
    [must_exit_at_wrong_code] at the definition level.  The run-level
    witnesses are example-side, and both directions of the guard are
    there: [Checks.Examples.exit0_image_must_exit_zero] is a concrete
    image this predicate HOLDS of, and
    [Checks.Examples.undecodable_image_refutes_must_exit] one it fails
    for at every code.  The positive one is what separates a demanding
    predicate from an empty one — the premises below are easy to write
    and hard to meet all at once, and nothing here would have noticed if
    no image met them. *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Three facts about [Run.sstep] that the lemmas below rely on
   ========================================================================= *)

(** Nothing steps out of a halted configuration: every [Run.sstep]
    constructor carries [m_halted model = None] as a premise.  This is
    what makes the progress premise of [must_exit_at]'s step case
    unsatisfiable at a halted configuration, hence what makes the two
    cases exclusive. *)
Lemma sstep_not_halted : forall segs c evs st,
  sstep segs c evs st -> m_halted (cfg_model c) = None.
Proof.
  intros segs c evs st Hss.
  inversion Hss; subst; cbn [cfg_model]; assumption.
Qed.

(** A run cannot leave a halted configuration, so a [Run.star] out of one
    is the empty one. *)
Lemma star_from_halted : forall segs c tr c',
  star segs c tr c' -> m_halted (cfg_model c) <> None -> tr = [] /\ c' = c.
Proof.
  intros segs c tr c' Hstar Hh.
  destruct Hstar as [c0 | c0 evs c1 tr1 c2 Hss Hstar1].
  - split; reflexivity.
  - exfalso. apply Hh. exact (sstep_not_halted _ _ _ _ Hss).
Qed.

(** The step that HALTS a configuration is the exit step, and it emits
    the [State.ExitEv] carrying the stored code.  Every other successor
    transition leaves [State.m_halted] alone:

    - [Run.sstep_instr] changes the model only through
      [Run.mi_account_step], whose frame lemma keeps [State.m_proc]
      fixed, and [State.m_halted] is a projection of it;
    - [Run.sstep_syscall] has [m_halted model' = None] as an explicit
      premise and then materializes, which
      [State.materialize_model_accesses_frame] also shows keeps
      [State.m_proc] fixed;
    - the remaining constructors go to [Run.SError].

    So [Run.sstep_exit] is the only way into a halted configuration, and
    the exit event is emitted BY that transition rather than at the
    halted configuration — exits are interior transitions here, not
    terminal ones.  [must_exit_at_realizes] needs exactly this to turn
    "reaches a halted configuration" into "emits an [State.ExitEv]". *)
Lemma sstep_next_halts_by_exit : forall segs c evs c',
  sstep segs c evs (SNext c') ->
  m_halted (cfg_model c') = None
  \/ (exists evs0 code,
        evs = evs0 ++ [ExitEv code (m_fs (cfg_model c'))]
        /\ m_halted (cfg_model c') = Some code
        /\ m_killed (cfg_model c') = None)
  \/ (exists evs0 sig,
        evs = evs0 ++ [KillEv sig (m_fs (cfg_model c'))]
        /\ m_killed (cfg_model c') = Some sig).
Proof.
  intros segs c evs c' Hss.
  inversion Hss as [ms model ms' model' Hh Hsvc Hacc Heq1 Heq2 Heq3
                   | | |ms model fn n eff model' model'' evs1 Hh Hsvc Hfn Hno Hspec Hef Hh' Hmat Heq1 Heq2 Heq3
                   | |
                   |ms model x8 eff model' model'' evs1 Hh Hsvc Hspec Hh' Hmat Heq1 Heq2 Heq3
                   | |ms model x8 eff model' evs1 code Hh Hsvc Hspec Hh' Hk Heq1 Heq2 Heq3
                   |ms model x8 eff model' evs1 sig Hh Hsvc Hspec Hk Heq1 Heq2 Heq3
                   | ]; subst.
  - (* sstep_instr *)
    left. cbn [cfg_model].
    destruct (mi_account_step_model_frame _ _ _ _ _ Hacc)
      as (_ & _ & _ & _ & _ & Hproc & _).
    unfold m_halted in *. rewrite Hproc. exact Hh.
  - (* sstep_vdso_call: materialization keeps [m_proc], and so does the
       call count *)
    left. cbn [cfg_model].
    destruct (materialize_model_accesses_frame _ _ _ Hmat)
      as (_ & _ & _ & _ & _ & Hproc & _).
    unfold m_halted in *. rewrite m_proc_with_vdso_bump, Hproc. exact Hh'.
  - (* sstep_syscall *)
    left. cbn [cfg_model].
    destruct (materialize_model_accesses_frame _ _ _ Hmat)
      as (_ & _ & _ & _ & _ & Hproc & _).
    unfold m_halted in *. rewrite Hproc. exact Hh'.
  - (* sstep_exit *)
    right; left. cbn [cfg_model]. exists evs1, code.
    split; [reflexivity | split; [exact Hh' | exact Hk]].
  - (* sstep_killed *)
    right; right. cbn [cfg_model]. exists evs1, sig.
    split; [reflexivity | exact Hk].
Qed.

(* =========================================================================
   The predicate
   ========================================================================= *)

(** Every maximal execution from [c] halts, after finitely many steps,
    with [State.m_halted] equal to [Some code].  See this file's header
    for what each premise buys; in one line: inductive for termination,
    progress against stuck configurations, [SError]-refutation against
    faulting ones, and the [forall]-over-successors premise so that one
    exiting resolution cannot hide a sibling that does something else. *)
Inductive must_exit_at (segs : list Segment) (code : word) : config -> Prop :=
| must_exit_at_halted : forall c,
    m_halted (cfg_model c) = Some code ->
    m_killed (cfg_model c) = None ->
    must_exit_at segs code c
| must_exit_at_running : forall c,
    m_halted (cfg_model c) = None ->
    (exists evs st, sstep segs c evs st) ->
    (forall evs, ~ sstep segs c evs SError) ->
    (forall evs c', sstep segs c evs (SNext c') -> must_exit_at segs code c') ->
    must_exit_at segs code c.

(** The run-level statement: every execution of [img] from the [execve]
    choices [en] on inputs [inp], under the memory budget [lim], exits
    with [code].

    Written as a MATCH on the image and the [execve] entry for the same
    reason [Run.run] is (Run.v, [Run.run]'s header): a proof unfolding it
    with [cbn [must_exit_with …]] gets the underlying [Run.init_config]
    application back as soon as those two arguments are concrete records,
    instead of having to name the projections in every such [cbn].  The
    [State.ProcInput] is passed whole and read by projections, which
    reduce, so the same works for a variable [inp].  [Run.ExecEntry] has
    four fields — the stack pointer, the program break, the mmap base and
    the AT_RANDOM draw, all chosen non-deterministically — and all four
    are consumed here exactly as [Run.run] consumes them, so that
    [must_exit_with code img lim en inp] and [Run.run img lim en inp]
    always speak about the SAME configuration. *)
Definition must_exit_with (code : word) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      must_exit_at segs code (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

(* =========================================================================
   What the predicate rules out: errors, and hence unmodeled behavior
   ========================================================================= *)

(** No execution reaches the explicit error transition.  The
    [SError]-refutation premise holds at every configuration the
    induction passes through, and [Run.reaches_error] names a [Run.star]
    to a configuration that then errors — so the [Run.star] is walked by
    the induction and its endpoint is one of those configurations.  At a
    halted endpoint there is no [Run.star] to walk and no [Run.sstep] to
    take at all. *)
Lemma must_exit_at_no_error : forall segs code c,
  must_exit_at segs code c -> ~ reaches_error segs c.
Proof.
  intros segs code c Hme.
  induction Hme as [c Hh | c Hnone Hprog Hnoerr Hnext IH]; intros Herr;
    destruct Herr as (tr & c2 & evs & Hstar & Hsserr).
  - assert (Hne : m_halted (cfg_model c) <> None) by (rewrite Hh; discriminate).
    destruct (star_from_halted _ _ _ _ Hstar Hne) as (_ & Heq); subst c2.
    pose proof (sstep_not_halted _ _ _ _ Hsserr) as Hnone. congruence.
  - destruct Hstar as [c0 | c0 evs0 c1 tr1 c3 Hss Hstar1].
    + exact (Hnoerr evs Hsserr).
    + apply (IH evs0 c1 Hss). exists tr1, c3, evs. split; assumption.
Qed.

(** The run-level image.  This is the clause that makes [must_exit_with]
    usable as a classifier verdict without a separate error-freedom
    conjunct: a binary that decides by exiting cannot also be allowed to
    fault. *)
Lemma must_exit_with_no_error : forall code img lim en inp,
  must_exit_with code img lim en inp -> ~ bh_errors (run img lim en inp).
Proof.
  intros code [segs pc ph] lim [sp brk0 mbase rnd] inp Hme.
  cbn [must_exit_with] in Hme. cbn [run bh_errors].
  exact (must_exit_at_no_error _ _ _ Hme).
Qed.

(** ... and therefore no execution runs off the edge of the model
    either, by [Run.no_error_no_unmodeled]: being uncovered is a special
    case of erroring ([Run.reaches_unmodeled_reaches_error]).  So a
    [must_exit_with] obligation subsumes [Equivalence.modeled] for the
    run it speaks about, exactly as [Equivalence.error_free] does. *)
Lemma must_exit_with_modeled : forall code img lim en inp,
  must_exit_with code img lim en inp -> ~ bh_unmodeled (run img lim en inp).
Proof.
  intros code img lim en inp Hme.
  pose proof (must_exit_with_no_error _ _ _ _ _ Hme) as Hnoerr.
  destruct img as [segs pc ph]; destruct en as [sp brk0 mbase rnd].
  cbn [run bh_errors bh_unmodeled] in *.
  exact (no_error_no_unmodeled _ _ Hnoerr).
Qed.

(* =========================================================================
   The code is unique
   ========================================================================= *)

(** One configuration cannot must-exit with two different codes.  This is
    what lets a classifier's two verdicts be read as a decision: from
    [must_exit_with verdict_accept] one may conclude
    [~ must_exit_with verdict_reject], so
    "exits 0" and "exits 1" are genuinely opposite answers rather than
    two claims that could both hold.

    The induction walks one proof and inverts the other at each step.
    Both base cases give [Some c1 = Some c2] directly; a base against a
    step contradicts on [State.m_halted]; step against step follows a
    successor supplied by the progress premise, which exists and is an
    [Run.SNext] because the [SError] branch is refuted. *)
Lemma must_exit_at_exclusive : forall segs code1 code2 c,
  must_exit_at segs code1 c -> must_exit_at segs code2 c -> code1 = code2.
Proof.
  intros segs code1 code2 c H1. revert code2.
  induction H1 as [c Hh | c Hnone Hprog Hnoerr Hnext IH]; intros code2 H2.
  - inversion H2; congruence.
  - inversion H2 as [c0 Hh2 Hc0 | c0 Hnone2 Hprog2 Hnoerr2 Hnext2 Hc0]; subst.
    + congruence.
    + destruct Hprog as (evs & st & Hss). destruct st as [c' |].
      * exact (IH evs c' Hss code2 (Hnext2 evs c' Hss)).
      * exfalso. exact (Hnoerr evs Hss).
Qed.

Lemma must_exit_with_exclusive : forall code1 code2 img lim en inp,
  must_exit_with code1 img lim en inp ->
  must_exit_with code2 img lim en inp ->
  code1 = code2.
Proof.
  intros code1 code2 [segs pc ph] lim [sp brk0 mbase rnd] inp H1 H2.
  cbn [must_exit_with] in H1, H2.
  exact (must_exit_at_exclusive _ _ _ _ H1 H2).
Qed.

(* =========================================================================
   Non-vacuity: the predicate really produces an exit event
   ========================================================================= *)

(** From a non-halted configuration satisfying the predicate there is an
    actual [Run.star] whose accumulated trace ENDS in
    [ExitEv code fs].

    The proof follows one successor at a time, chosen by the progress
    premise (and an [Run.SNext] one, because [SError] is refuted).  At
    each step either the successor is still running — recurse, and
    prepend this step's events, which is where the trace grows on the
    left — or the successor is halted, and then
    [sstep_next_halts_by_exit] says the transition just taken was
    [Run.sstep_exit] and its event list already ends in the
    [State.ExitEv].  The code carried by that event is [code] because the
    successor satisfies the predicate and is halted, so it satisfies it
    by the base case.

    The [m_halted (cfg_model c) = None] hypothesis is what the
    statement needs to be about an exit EVENT rather than an exit STATE:
    a configuration handed to us already halted satisfies the predicate
    without any transition having emitted anything.  Run-level, that
    hypothesis is discharged by computation on [Run.init_config]. *)
Lemma must_exit_at_realizes : forall segs code c,
  must_exit_at segs code c ->
  m_halted (cfg_model c) = None ->
  exists tr fs c',
    star segs c (tr ++ [ExitEv code fs]) c'
    /\ m_halted (cfg_model c') = Some code.
Proof.
  intros segs code c Hme.
  induction Hme as [c Hh Hk | c Hnone Hprog Hnoerr Hnext IH]; intros Hrun.
  - congruence.
  - destruct Hprog as (evs & st & Hss). destruct st as [c1 |];
      [| exfalso; exact (Hnoerr evs Hss)].
    pose proof (Hnext evs c1 Hss) as Hme1.
    destruct (m_halted (cfg_model c1)) as [k |] eqn:Hh1.
    + assert (Hk : k = code) by (inversion Hme1; congruence).
      subst k.
      (* The successor is halted and satisfies the predicate, so by the
         base case it is NOT killed -- which is what rules the kill
         transition out and leaves [Run.sstep_exit] as the only way in. *)
      assert (Hnk : m_killed (cfg_model c1) = None)
        by (inversion Hme1; congruence).
      destruct (sstep_next_halts_by_exit _ _ _ _ Hss)
        as [Hnone1 | [(evs0 & code0 & Hevs & Hcode0 & _)
                     | (evs0 & sig & Hevs & Hsig)]];
        [congruence | | congruence].
      assert (Hcc : code0 = code) by congruence. subst code0.
      exists evs0, (m_fs (cfg_model c1)), c1. split; [| exact Hh1].
      rewrite <- Hevs. exact (star_one _ _ _ _ Hss).
    + destruct (IH evs c1 Hss Hh1) as (tr & fs & c' & Hstar & Hh').
      exists (evs ++ tr), fs, c'. split; [| exact Hh'].
      rewrite <- app_assoc. exact (star_step _ _ _ _ _ _ Hss Hstar).
Qed.

(** The guard, at run level: a run that must exit with [code] has an
    observable trace ending in [ExitEv code fs].  This is the analogue of
    [Run.all_traces_error_reaches_error] — a universal predicate whose
    guard nobody can trip is a guard that guards nothing.  In particular
    [must_exit_with] cannot be satisfied by a run that produces no
    events, which is what a purely "never errors, never gets stuck"
    reading would have allowed. *)
Lemma must_exit_with_realizes : forall code img lim en inp,
  must_exit_with code img lim en inp ->
  exists tr fs, bh_traces (run img lim en inp) (tr ++ [ExitEv code fs]).
Proof.
  intros code [segs pc ph] lim [sp brk0 mbase rnd] inp Hme.
  cbn [must_exit_with] in Hme.
  assert (Hnone : m_halted
                    (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))
                  = None)
    by (cbn [init_config cfg_model]; reflexivity).
  destruct (must_exit_at_realizes _ _ _ Hme Hnone) as (tr & fs & c' & Hstar & _).
  exists tr, fs. cbn [run bh_traces]. unfold obs_trace.
  exists (tr ++ [ExitEv code fs]), c'. split; [exact Hstar | apply is_prefix_refl].
Qed.

(* =========================================================================
   The predicate bites: it can be established, and it can be refuted
   ========================================================================= *)

(** POSITIVE, one step.  A configuration whose every successor is already
    halted with [code] must exit with [code].  It is the introduction
    rule for the [ecall] that runs [Sys.Kernel.Exit.exit_spec], where
    the exit transition is the last one and [Run.sstep_exit]'s target
    carries [Some code].  Nothing uses it yet:
    [Checks.Examples.exits_c_must_exit_at], the one worked example, goes
    through [must_exit_at_running] and [must_exit_at_halted] directly.
    It is kept as the shape a caller reaching the exit in one step would
    want, and should be deleted if nothing claims it.
    ([must_exit_at_halted] is the other introduction rule, and is the
    constructor itself.) *)
Lemma must_exit_at_exit_now : forall segs code c,
  m_halted (cfg_model c) = None ->
  (exists evs st, sstep segs c evs st) ->
  (forall evs, ~ sstep segs c evs SError) ->
  (forall evs c', sstep segs c evs (SNext c') ->
                  m_halted (cfg_model c') = Some code
                  /\ m_killed (cfg_model c') = None) ->
  must_exit_at segs code c.
Proof.
  intros segs code c Hnone Hprog Hnoerr Hhalt.
  apply must_exit_at_running; try assumption.
  intros evs c' Hss. destruct (Hhalt evs c' Hss) as (Hh & Hk).
  exact (must_exit_at_halted _ _ _ Hh Hk).
Qed.

(** NEGATIVE, the error route.  A running configuration that can take the
    error transition refutes the predicate for EVERY code — the base case
    is out because the configuration is not halted, and the step case is
    out by its [SError]-refutation premise.  This is the definition-level
    form of [Checks.Examples.undecodable_image_refutes_must_exit], which
    runs it on a concrete image: one whose first fetch is unmodeled
    errors immediately, so it refutes [must_exit_with] at any code. *)
Lemma must_exit_at_refuted_by_error : forall segs code c evs,
  m_halted (cfg_model c) = None ->
  sstep segs c evs SError ->
  ~ must_exit_at segs code c.
Proof.
  intros segs code c evs Hnone Hsserr Hme.
  inversion Hme as [c0 Hh Hc0 | c0 Hnone0 Hprog Hnoerr Hnext Hc0]; subst.
  - congruence.
  - exact (Hnoerr evs Hsserr).
Qed.

(** NEGATIVE, the wrong-code route.  A configuration halted with one code
    refutes the predicate at every other code.  Without this the
    predicate could have been "terminates without erroring", with the
    code argument along for the ride; it is what makes [must_exit_with
    verdict_accept] and [must_exit_with verdict_reject] different statements. *)
Lemma must_exit_at_wrong_code : forall segs code code' c,
  m_halted (cfg_model c) = Some code ->
  code <> code' ->
  ~ must_exit_at segs code' c.
Proof.
  intros segs code code' c Hh Hne Hme.
  inversion Hme; congruence.
Qed.

(** The run-level refutation, packaged for the example side: any run that
    can error refutes [must_exit_with] at every code.  This is the
    contrapositive of [must_exit_with_no_error], and it is the shape the
    [Checks.Examples] witnesses use — those establish [bh_unmodeled] of a
    run, which [Equivalence.run_unmodeled_errors] turns into [bh_errors]. *)
Lemma must_exit_with_refuted_by_error : forall code img lim en inp,
  bh_errors (run img lim en inp) -> ~ must_exit_with code img lim en inp.
Proof.
  intros code img lim en inp Herr Hme.
  exact (must_exit_with_no_error _ _ _ _ _ Hme Herr).
Qed.

(* =========================================================================
   The verdict predicate under a spurious-failure configuration:
   [must_exit_at_cfg], [must_exit_with_scfg]
   =========================================================================

   [Run.run_scfg cfg] walks [Run.sstep_cfg cfg], the step relation with
   every avoidable refusal of a forced-only family removed.  The verdict
   predicate follows: [must_exit_at_cfg cfg] is [must_exit_at] over that
   relation, premise for premise, and [must_exit_with_scfg cfg] is its
   run-level form.  At [Run.may_fail_cfg] it is [must_exit_with] itself
   ([must_exit_with_scfg_may_fail]).

   This is the predicate the classifier layer pins its verdicts to, at
   [Run.forced_only_cfg] ([Classifier.decides_fo]), and the reason is
   this: a classifier that reads its input cannot decide anything
   under a reading where the open may be refused without cause, since
   the refused run reaches neither verdict.  Under forced-only the
   refusal is gone wherever the open could have succeeded, and what
   remains of the obligation is what a decision procedure should be
   asked — every execution the environment can FORCE ends in the right
   verdict.

   What the pin costs, stated once: the progress premise of
   [must_exit_at_cfg_running] is over the FILTERED relation, and
   filtering can only make it harder to meet.  It cannot make it
   impossible where the filter's question is answered — [Run.sstep_cfg_progress]
   — and that is what [must_exit_at_cfg_mono] below turns into the
   statement that a verdict under may-fail is a verdict under every
   configuration: the pin is a WEAKENING of the obligation, never a
   different one.  The premise it carries, [run_decided], is the KNOWN
   GAP of [Run.v]'s spurious-failure section, at the run. *)

Inductive must_exit_at_cfg (cfg : SpuriousCfg) (segs : list Segment) (code : word)
    : config -> Prop :=
| must_exit_at_cfg_halted : forall c,
    m_halted (cfg_model c) = Some code ->
    m_killed (cfg_model c) = None ->
    must_exit_at_cfg cfg segs code c
| must_exit_at_cfg_running : forall c,
    m_halted (cfg_model c) = None ->
    (exists evs st, sstep_cfg segs cfg c evs st) ->
    (forall evs, ~ sstep_cfg segs cfg c evs SError) ->
    (forall evs c', sstep_cfg segs cfg c evs (SNext c') -> must_exit_at_cfg cfg segs code c') ->
    must_exit_at_cfg cfg segs code c.

(** The three facts about [Run.sstep] the lemmas above rely on, carried
    to the filtered relation through [Run.sstep_cfg_sub]. *)
Lemma sstep_cfg_not_halted : forall segs cfg c evs st,
  sstep_cfg segs cfg c evs st -> m_halted (cfg_model c) = None.
Proof.
  intros segs cfg c evs st Hss.
  exact (sstep_not_halted _ _ _ _ (sstep_cfg_sub _ _ _ _ _ Hss)).
Qed.

Lemma star_cfg_from_halted : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' -> m_halted (cfg_model c) <> None -> tr = [] /\ c' = c.
Proof.
  intros segs cfg c tr c' Hstar Hh.
  destruct Hstar as [c0 | c0 evs c1 tr1 c2 Hss Hstar1].
  - split; reflexivity.
  - exfalso. apply Hh. exact (sstep_cfg_not_halted _ _ _ _ _ Hss).
Qed.

Lemma sstep_cfg_next_halts_by_exit : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  m_halted (cfg_model c') = None
  \/ (exists evs0 code,
        evs = evs0 ++ [ExitEv code (m_fs (cfg_model c'))]
        /\ m_halted (cfg_model c') = Some code
        /\ m_killed (cfg_model c') = None)
  \/ (exists evs0 sig,
        evs = evs0 ++ [KillEv sig (m_fs (cfg_model c'))]
        /\ m_killed (cfg_model c') = Some sig).
Proof.
  intros segs cfg c evs c' Hss.
  exact (sstep_next_halts_by_exit _ _ _ _ (sstep_cfg_sub _ _ _ _ _ Hss)).
Qed.

(* -------------------------------------------------------------------------
   The same five facts, for the filtered predicate
   ------------------------------------------------------------------------- *)

Lemma must_exit_at_cfg_no_error : forall cfg segs code c,
  must_exit_at_cfg cfg segs code c -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros cfg segs code c Hme.
  induction Hme as [c Hh | c Hnone Hprog Hnoerr Hnext IH]; intros Herr;
    destruct Herr as (tr & c2 & evs & Hstar & Hsserr).
  - assert (Hne : m_halted (cfg_model c) <> None) by (rewrite Hh; discriminate).
    destruct (star_cfg_from_halted _ _ _ _ _ Hstar Hne) as (_ & Heq); subst c2.
    pose proof (sstep_cfg_not_halted _ _ _ _ _ Hsserr) as Hnone. congruence.
  - destruct Hstar as [c0 | c0 evs0 c1 tr1 c3 Hss Hstar1].
    + exact (Hnoerr evs Hsserr).
    + apply (IH evs0 c1 Hss). exists tr1, c3, evs. split; assumption.
Qed.

Lemma must_exit_at_cfg_exclusive : forall cfg segs code1 code2 c,
  must_exit_at_cfg cfg segs code1 c -> must_exit_at_cfg cfg segs code2 c -> code1 = code2.
Proof.
  intros cfg segs code1 code2 c H1. revert code2.
  induction H1 as [c Hh | c Hnone Hprog Hnoerr Hnext IH]; intros code2 H2.
  - inversion H2; congruence.
  - inversion H2 as [c0 Hh2 Hc0 | c0 Hnone2 Hprog2 Hnoerr2 Hnext2 Hc0]; subst.
    + congruence.
    + destruct Hprog as (evs & st & Hss). destruct st as [c' |].
      * exact (IH evs c' Hss code2 (Hnext2 evs c' Hss)).
      * exfalso. exact (Hnoerr evs Hss).
Qed.

Lemma must_exit_at_cfg_realizes : forall cfg segs code c,
  must_exit_at_cfg cfg segs code c ->
  m_halted (cfg_model c) = None ->
  exists tr fs c',
    star_cfg segs cfg c (tr ++ [ExitEv code fs]) c'
    /\ m_halted (cfg_model c') = Some code.
Proof.
  intros cfg segs code c Hme.
  induction Hme as [c Hh Hk | c Hnone Hprog Hnoerr Hnext IH]; intros Hrun.
  - congruence.
  - destruct Hprog as (evs & st & Hss). destruct st as [c1 |];
      [| exfalso; exact (Hnoerr evs Hss)].
    pose proof (Hnext evs c1 Hss) as Hme1.
    destruct (m_halted (cfg_model c1)) as [k |] eqn:Hh1.
    + assert (Hk : k = code) by (inversion Hme1; congruence).
      subst k.
      assert (Hnk : m_killed (cfg_model c1) = None)
        by (inversion Hme1; congruence).
      destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ Hss)
        as [Hnone1 | [(evs0 & code0 & Hevs & Hcode0 & _)
                     | (evs0 & sig & Hevs & Hsig)]];
        [congruence | | congruence].
      assert (Hcc : code0 = code) by congruence. subst code0.
      exists evs0, (m_fs (cfg_model c1)), c1. split; [| exact Hh1].
      rewrite <- Hevs. rewrite <- (app_nil_r evs).
      eapply star_cfg_step; [exact Hss | apply star_cfg_refl].
    + destruct (IH evs c1 Hss Hh1) as (tr & fs & c' & Hstar & Hh').
      exists (evs ++ tr), fs, c'. split; [| exact Hh'].
      rewrite <- app_assoc. exact (star_cfg_step _ _ _ _ _ _ _ Hss Hstar).
Qed.

Lemma must_exit_at_cfg_refuted_by_error : forall cfg segs code c evs,
  m_halted (cfg_model c) = None ->
  sstep_cfg segs cfg c evs SError ->
  ~ must_exit_at_cfg cfg segs code c.
Proof.
  intros cfg segs code c evs Hnone Hsserr Hme.
  inversion Hme as [c0 Hh Hc0 | c0 Hnone0 Hprog Hnoerr Hnext Hc0]; subst.
  - congruence.
  - exact (Hnoerr evs Hsserr).
Qed.

Lemma must_exit_at_cfg_wrong_code : forall cfg segs code code' c,
  m_halted (cfg_model c) = Some code ->
  code <> code' ->
  ~ must_exit_at_cfg cfg segs code' c.
Proof.
  intros cfg segs code code' c Hh Hne Hme.
  inversion Hme; congruence.
Qed.

(* -------------------------------------------------------------------------
   Meaning at [may_fail_cfg], and monotonicity in the configuration
   ------------------------------------------------------------------------- *)

Lemma must_exit_at_cfg_may_fail : forall segs code c,
  must_exit_at_cfg may_fail_cfg segs code c <-> must_exit_at segs code c.
Proof.
  intros segs code c; split; intros H.
  - induction H as [c Hh Hk | c Hnone (evs & st & Hss) Hnoerr _ IH].
    + exact (must_exit_at_halted _ _ _ Hh Hk).
    + apply must_exit_at_running; [exact Hnone | | |].
      * exists evs, st. apply sstep_cfg_may_fail; exact Hss.
      * intros evs' Herr. apply (Hnoerr evs'). apply sstep_cfg_may_fail; exact Herr.
      * intros evs' c' Hss'. apply (IH evs' c'). apply sstep_cfg_may_fail; exact Hss'.
  - induction H as [c Hh Hk | c Hnone (evs & st & Hss) Hnoerr _ IH].
    + exact (must_exit_at_cfg_halted _ _ _ _ Hh Hk).
    + apply must_exit_at_cfg_running; [exact Hnone | | |].
      * exists evs, st. apply sstep_cfg_may_fail; exact Hss.
      * intros evs' Herr. apply (Hnoerr evs'). apply sstep_cfg_may_fail; exact Herr.
      * intros evs' c' Hss'. apply (IH evs' c'). apply sstep_cfg_may_fail; exact Hss'.
Qed.

(** The filter's question is answered at every configuration reachable
    from [c] — over the UNFILTERED star, which reaches everything any
    filtered star does.  See [Run.refusal_decided]. *)
Definition decided_from (cfg : SpuriousCfg) (segs : list Segment) (c : config) : Prop :=
  forall tr c' x8,
    star segs c tr c' ->
    ms_svc_pending (cfg_ms c') = Some x8 ->
    refusal_decided cfg (sys_input segs (cfg_ms c') x8) (cfg_model c').

Lemma decided_from_step : forall cfg cfg' segs c evs c',
  decided_from cfg segs c ->
  sstep_cfg segs cfg' c evs (SNext c') ->
  decided_from cfg segs c'.
Proof.
  intros cfg cfg' segs c evs c' Hdec Hss tr c'' x8 Hstar Hsvc.
  apply (Hdec (evs ++ tr) c'' x8); [| exact Hsvc].
  eapply star_step; [exact (sstep_cfg_sub _ _ _ _ _ Hss) | exact Hstar].
Qed.

(** A verdict under a configuration is a verdict under every SMALLER
    one, wherever the filter's question is answered along the way.
    Progress is [Run.sstep_cfg_progress]; the error premise and the
    successor premise go through [Run.sstep_cfg_mono], since every step
    of the smaller configuration is a step of the larger. *)
Lemma must_exit_at_cfg_mono : forall cfg1 cfg2 segs code c,
  cfg_le cfg1 cfg2 ->
  decided_from cfg1 segs c ->
  must_exit_at_cfg cfg2 segs code c ->
  must_exit_at_cfg cfg1 segs code c.
Proof.
  intros cfg1 cfg2 segs code c Hle Hdec H.
  induction H as [c Hh Hk | c Hnone (evs & st & Hss) Hnoerr _ IH]; intros.
  - exact (must_exit_at_cfg_halted _ _ _ _ Hh Hk).
  - apply must_exit_at_cfg_running; [exact Hnone | | |].
    + destruct c as [ms model].
      apply (sstep_cfg_progress segs cfg1 ms model evs st).
      * intros x8 Hsvc. exact (Hdec [] (mkCfg ms model) x8 (star_refl _ _) Hsvc).
      * exact (sstep_cfg_sub _ _ _ _ _ Hss).
    + intros evs' Herr. apply (Hnoerr evs'). exact (sstep_cfg_mono _ _ _ _ _ _ Hle Herr).
    + intros evs' c' Hss'.
      apply (IH evs' c' (sstep_cfg_mono _ _ _ _ _ _ Hle Hss')).
      exact (decided_from_step _ _ _ _ _ _ Hdec Hss').
Qed.

(** In particular a verdict under may-fail is a verdict under any
    configuration at all: the pin is a weakening. *)
Lemma must_exit_at_cfg_of_must_exit_at : forall cfg segs code c,
  decided_from cfg segs c ->
  must_exit_at segs code c ->
  must_exit_at_cfg cfg segs code c.
Proof.
  intros cfg segs code c Hdec H.
  apply (must_exit_at_cfg_mono cfg may_fail_cfg segs code c
           (may_fail_cfg_greatest cfg) Hdec).
  apply must_exit_at_cfg_may_fail; exact H.
Qed.

(* -------------------------------------------------------------------------
   The run-level statement
   ------------------------------------------------------------------------- *)

(** [must_exit_with] under a configuration: the same [match] on the
    image and the entry, the same initial configuration
    [Run.run_scfg cfg] starts from, so that
    [must_exit_with_scfg cfg code img lim en inp] and
    [Run.run_scfg cfg img lim en inp] always speak about the SAME run. *)
Definition must_exit_with_scfg (cfg : SpuriousCfg) (code : word) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      must_exit_at_cfg cfg segs code (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

(** The one-switch form, as a thin instance: [true] IS
    [must_exit_with] by an [if] on the literal, so every lemma above
    applies at [true] unchanged; [false] is the record form at
    [Run.alloc_only_cfg false]. *)
Definition must_exit_with_cfg (alloc_may_fail : bool) (code : word) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  if alloc_may_fail then must_exit_with code img lim en inp
  else must_exit_with_scfg (alloc_only_cfg false) code img lim en inp.

Lemma must_exit_with_cfg_true : forall code img lim en inp,
  must_exit_with_cfg true code img lim en inp = must_exit_with code img lim en inp.
Proof. reflexivity. Qed.

Lemma must_exit_with_cfg_false : forall code img lim en inp,
  must_exit_with_cfg false code img lim en inp
  = must_exit_with_scfg (alloc_only_cfg false) code img lim en inp.
Proof. reflexivity. Qed.

Lemma must_exit_with_scfg_may_fail : forall code img lim en inp,
  must_exit_with_scfg may_fail_cfg code img lim en inp <-> must_exit_with code img lim en inp.
Proof.
  intros code [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [must_exit_with_scfg must_exit_with]. apply must_exit_at_cfg_may_fail.
Qed.

Lemma must_exit_with_scfg_no_error : forall cfg code img lim en inp,
  must_exit_with_scfg cfg code img lim en inp -> ~ bh_errors (run_scfg cfg img lim en inp).
Proof.
  intros cfg code [segs pc ph] lim [sp brk0 mbase rnd] inp Hme.
  cbn [must_exit_with_scfg] in Hme. cbn [run_scfg bh_errors].
  exact (must_exit_at_cfg_no_error _ _ _ _ Hme).
Qed.

Lemma must_exit_with_scfg_modeled : forall cfg code img lim en inp,
  must_exit_with_scfg cfg code img lim en inp -> ~ bh_unmodeled (run_scfg cfg img lim en inp).
Proof.
  intros cfg code img lim en inp Hme Hun.
  exact (must_exit_with_scfg_no_error _ _ _ _ _ _ Hme
           (run_scfg_unmodeled_errors _ _ _ _ _ Hun)).
Qed.

Lemma must_exit_with_scfg_exclusive : forall cfg code1 code2 img lim en inp,
  must_exit_with_scfg cfg code1 img lim en inp ->
  must_exit_with_scfg cfg code2 img lim en inp ->
  code1 = code2.
Proof.
  intros cfg code1 code2 [segs pc ph] lim [sp brk0 mbase rnd] inp H1 H2.
  cbn [must_exit_with_scfg] in H1, H2.
  exact (must_exit_at_cfg_exclusive _ _ _ _ _ H1 H2).
Qed.

(** The guard, at run level and for the filtered run: a run that must
    exit with [code] under [cfg] has a trace ending in [ExitEv code fs]
    — a trace of the filtered run, and therefore of the unfiltered one
    ([must_exit_with_scfg_realizes_run]).  The second form is what
    [Classifier.accepts_fo_realizes] states: the classifier's verdict is
    an event the real program emits, not one a filter invented. *)
Lemma must_exit_with_scfg_realizes : forall cfg code img lim en inp,
  must_exit_with_scfg cfg code img lim en inp ->
  exists tr fs, bh_traces (run_scfg cfg img lim en inp) (tr ++ [ExitEv code fs]).
Proof.
  intros cfg code [segs pc ph] lim [sp brk0 mbase rnd] inp Hme.
  cbn [must_exit_with_scfg] in Hme.
  assert (Hnone : m_halted
                    (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))
                  = None)
    by (cbn [init_config cfg_model]; reflexivity).
  destruct (must_exit_at_cfg_realizes _ _ _ _ Hme Hnone) as (tr & fs & c' & Hstar & _).
  exists tr, fs. cbn [run_scfg bh_traces]. unfold obs_trace_cfg.
  exists (tr ++ [ExitEv code fs]), c'. split; [exact Hstar | apply is_prefix_refl].
Qed.

Lemma must_exit_with_scfg_realizes_run : forall cfg code img lim en inp,
  must_exit_with_scfg cfg code img lim en inp ->
  exists tr fs, bh_traces (run img lim en inp) (tr ++ [ExitEv code fs]).
Proof.
  intros cfg code img lim en inp Hme.
  destruct (must_exit_with_scfg_realizes _ _ _ _ _ _ Hme) as (tr & fs & Htr).
  exists tr, fs. exact (run_scfg_sub_traces _ _ _ _ _ _ Htr).
Qed.

Lemma must_exit_with_scfg_refuted_by_error : forall cfg code img lim en inp,
  bh_errors (run_scfg cfg img lim en inp) -> ~ must_exit_with_scfg cfg code img lim en inp.
Proof.
  intros cfg code img lim en inp Herr Hme.
  exact (must_exit_with_scfg_no_error _ _ _ _ _ _ Hme Herr).
Qed.

(** The filter's question is answered on every configuration THIS run
    reaches. *)
Definition run_decided (cfg : SpuriousCfg) (img : Image) (lim : Z) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      decided_from cfg segs (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

Lemma must_exit_with_scfg_mono : forall cfg1 cfg2 code img lim en inp,
  cfg_le cfg1 cfg2 ->
  run_decided cfg1 img lim en inp ->
  must_exit_with_scfg cfg2 code img lim en inp ->
  must_exit_with_scfg cfg1 code img lim en inp.
Proof.
  intros cfg1 cfg2 code [segs pc ph] lim [sp brk0 mbase rnd] inp Hle Hdec H.
  cbn [must_exit_with_scfg run_decided] in *.
  exact (must_exit_at_cfg_mono _ _ _ _ _ Hle Hdec H).
Qed.

Lemma must_exit_with_scfg_of_must_exit_with : forall cfg code img lim en inp,
  run_decided cfg img lim en inp ->
  must_exit_with code img lim en inp ->
  must_exit_with_scfg cfg code img lim en inp.
Proof.
  intros cfg code img lim en inp Hdec H.
  apply (must_exit_with_scfg_mono cfg may_fail_cfg _ _ _ _ _
           (may_fail_cfg_greatest cfg) Hdec).
  apply must_exit_with_scfg_may_fail; exact H.
Qed.

(* =========================================================================
   The SET form: halting with a status in an ALLOWED SET
   =========================================================================

   [must_exit_at] fixes ONE code, and that is the right shape for a
   classifier, whose whole point is that the code carries an answer.  It
   is the wrong shape for the other thing a caller wants to know about a
   single binary: that it TERMINATES CLEANLY, with a status the task
   declares acceptable, whatever the nondeterminism resolves to.  A
   program that exits 0 on one resolution and 1 on another satisfies
   [must_exit_at] at NEITHER code — [must_exit_at_exclusive] says so —
   and yet it halted through [exit_group] both times.

   So the set form replaces the equality at the halted leaf with a
   MEMBERSHIP.  Everything else is premise for premise the same
   predicate, which is what makes the two comparable: inductive for
   termination, progress against stuck configurations,
   [SError]-refutation against faulting ones, the [forall]-over-successors
   premise so no resolution is hidden, and [State.m_killed] clear at the
   leaf so a signal death is not an exit.

   WHAT DOES NOT CARRY OVER is uniqueness.  [must_exit_at_exclusive]
   has no analogue here and must not be written: two allowed sets can
   both contain the code a run exits with, and that is the point.  What
   replaces it is [must_exit_in_at_mono] — a bigger set is a weaker
   claim — and [must_exit_in_at_wrong_code], which is the refutation:
   halting OUTSIDE the set is what fails.

   The set is a [list word] rather than a [word -> Prop] so that a
   concrete instance is a closed term a [vm_compute] can decide, which
   is what the example side needs; [In] over that list is the
   membership.  A caller wanting an infinite or abstract set would want
   the predicate version, and this file does not offer one because
   nothing asks for it — an allowed-exit set is a handful of statuses a
   task writes down.

   The codes are compared the way [must_exit_at] compares them: PLAIN,
   with no [bv_and … 255] wrapper of this file's own.  The header above
   says why at length; in one line, [Sys.Kernel.Exit.exit_spec] applies
   the mask before the status reaches the model, so a set whose members
   are written as bare bytes is a set of statuses a waiting parent can
   really read. *)

Inductive must_exit_in_at (segs : list Segment) (S : list word) : config -> Prop :=
| must_exit_in_at_halted : forall c code,
    m_halted (cfg_model c) = Some code ->
    In code S ->
    m_killed (cfg_model c) = None ->
    must_exit_in_at segs S c
| must_exit_in_at_running : forall c,
    m_halted (cfg_model c) = None ->
    (exists evs st, sstep segs c evs st) ->
    (forall evs, ~ sstep segs c evs SError) ->
    (forall evs c', sstep segs c evs (SNext c') -> must_exit_in_at segs S c') ->
    must_exit_in_at segs S c.

(** The run-level statement, the same [match] on the image and the entry
    [must_exit_with] uses and for the same reason: so that
    [must_exit_in S img lim en inp] and [Run.run img lim en inp] always
    speak about the SAME configuration. *)
Definition must_exit_in (S : list word) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      must_exit_in_at segs S (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

(** What a halted configuration satisfying the predicate must look like.
    Stated once because three proofs below take the base case apart, and
    doing it by [inversion] at each of them is where a mistake about the
    kill conjunct would hide. *)
Lemma must_exit_in_at_halted_inv : forall segs S c code,
  must_exit_in_at segs S c ->
  m_halted (cfg_model c) = Some code ->
  In code S /\ m_killed (cfg_model c) = None.
Proof.
  intros segs S c code Hme Hh.
  inversion Hme as [c0 code0 Hh0 Hin0 Hk0 | c0 Hnone Hprog Hnoerr Hnext]; subst.
  - assert (Heq : code0 = code) by congruence. subst code0. split; assumption.
  - congruence.
Qed.

(* -------------------------------------------------------------------------
   What the set form rules out: errors, and hence unmodeled behavior
   ------------------------------------------------------------------------- *)

Lemma must_exit_in_at_no_error : forall segs S c,
  must_exit_in_at segs S c -> ~ reaches_error segs c.
Proof.
  intros segs S c Hme.
  induction Hme as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros Herr;
    destruct Herr as (tr & c2 & evs & Hstar & Hsserr).
  - assert (Hne : m_halted (cfg_model c) <> None) by (rewrite Hh; discriminate).
    destruct (star_from_halted _ _ _ _ Hstar Hne) as (_ & Heq); subst c2.
    pose proof (sstep_not_halted _ _ _ _ Hsserr) as Hnone. congruence.
  - destruct Hstar as [c0 | c0 evs0 c1 tr1 c3 Hss Hstar1].
    + exact (Hnoerr evs Hsserr).
    + apply (IH evs0 c1 Hss). exists tr1, c3, evs. split; assumption.
Qed.

Lemma must_exit_in_no_error : forall S img lim en inp,
  must_exit_in S img lim en inp -> ~ bh_errors (run img lim en inp).
Proof.
  intros S [segs pc ph] lim [sp brk0 mbase rnd] inp Hme.
  cbn [must_exit_in] in Hme. cbn [run bh_errors].
  exact (must_exit_in_at_no_error _ _ _ Hme).
Qed.

Lemma must_exit_in_modeled : forall S img lim en inp,
  must_exit_in S img lim en inp -> ~ bh_unmodeled (run img lim en inp).
Proof.
  intros S img lim en inp Hme.
  pose proof (must_exit_in_no_error _ _ _ _ _ Hme) as Hnoerr.
  destruct img as [segs pc ph]; destruct en as [sp brk0 mbase rnd].
  cbn [run bh_errors bh_unmodeled] in *.
  exact (no_error_no_unmodeled _ _ Hnoerr).
Qed.

(* -------------------------------------------------------------------------
   The single-code form is the singleton set, and a code in the set
   ------------------------------------------------------------------------- *)

(** A run that must exit with one code must exit with a status in any
    set containing it.  This is the direction a task takes: a binary
    proved to exit 0 satisfies "exits with something allowed" for every
    allowed set that admits 0. *)
Lemma must_exit_at_in : forall segs S code c,
  must_exit_at segs code c -> In code S -> must_exit_in_at segs S c.
Proof.
  intros segs S code c Hme Hin.
  induction Hme as [c Hh Hk | c Hnone Hprog Hnoerr Hnext IH].
  - exact (must_exit_in_at_halted _ _ _ _ Hh Hin Hk).
  - apply must_exit_in_at_running; assumption.
Qed.

Lemma must_exit_with_in : forall S code img lim en inp,
  must_exit_with code img lim en inp ->
  In code S ->
  must_exit_in S img lim en inp.
Proof.
  intros S code [segs pc ph] lim [sp brk0 mbase rnd] inp Hme Hin.
  cbn [must_exit_with] in Hme. cbn [must_exit_in].
  exact (must_exit_at_in _ _ _ _ Hme Hin).
Qed.

(** ... and at a ONE-ELEMENT set the two are the same statement.  This is
    the lemma that says the set form is a generalisation rather than a
    different predicate: everything [must_exit_at] concludes is available
    at a singleton, uniqueness included. *)
Lemma must_exit_in_at_singleton : forall segs code c,
  must_exit_in_at segs [code] c <-> must_exit_at segs code c.
Proof.
  intros segs code c; split; intros H.
  - induction H as [c code0 Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH].
    + cbn [In] in Hin. destruct Hin as [Heq | []]. subst code0.
      exact (must_exit_at_halted _ _ _ Hh Hk).
    + apply must_exit_at_running; assumption.
  - apply (must_exit_at_in _ _ _ _ H). cbn [In]. left; reflexivity.
Qed.

Lemma must_exit_in_singleton : forall code img lim en inp,
  must_exit_in [code] img lim en inp <-> must_exit_with code img lim en inp.
Proof.
  intros code [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [must_exit_in must_exit_with]. apply must_exit_in_at_singleton.
Qed.

(* -------------------------------------------------------------------------
   Monotone in the set: a wider allowance is a weaker claim
   ------------------------------------------------------------------------- *)

(** The direction that is sound, and only that one.  Widening the allowed
    set weakens the obligation; NARROWING it does not follow, and a task
    that wants the narrower statement has to prove it. *)
Lemma must_exit_in_at_mono : forall segs S1 S2 c,
  (forall code, In code S1 -> In code S2) ->
  must_exit_in_at segs S1 c ->
  must_exit_in_at segs S2 c.
Proof.
  intros segs S1 S2 c Hsub H.
  induction H as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH].
  - exact (must_exit_in_at_halted _ _ _ _ Hh (Hsub _ Hin) Hk).
  - apply must_exit_in_at_running; assumption.
Qed.

Lemma must_exit_in_mono : forall S1 S2 img lim en inp,
  (forall code, In code S1 -> In code S2) ->
  must_exit_in S1 img lim en inp ->
  must_exit_in S2 img lim en inp.
Proof.
  intros S1 S2 [segs pc ph] lim [sp brk0 mbase rnd] inp Hsub H.
  cbn [must_exit_in] in *.
  exact (must_exit_in_at_mono _ _ _ _ Hsub H).
Qed.

(* -------------------------------------------------------------------------
   The set form bites: it can be refuted three ways
   ------------------------------------------------------------------------- *)

(** NEGATIVE, the error route, as for the single-code form: a running
    configuration that can take the error transition refutes the
    predicate for EVERY allowed set. *)
Lemma must_exit_in_at_refuted_by_error : forall segs S c evs,
  m_halted (cfg_model c) = None ->
  sstep segs c evs SError ->
  ~ must_exit_in_at segs S c.
Proof.
  intros segs S c evs Hnone Hsserr Hme.
  inversion Hme as [c0 code Hh Hin Hk | c0 Hnone0 Hprog Hnoerr Hnext]; subst.
  - congruence.
  - exact (Hnoerr evs Hsserr).
Qed.

Lemma must_exit_in_refuted_by_error : forall S img lim en inp,
  bh_errors (run img lim en inp) -> ~ must_exit_in S img lim en inp.
Proof.
  intros S img lim en inp Herr Hme.
  exact (must_exit_in_no_error _ _ _ _ _ Hme Herr).
Qed.

(** NEGATIVE, the wrong-status route.  A configuration halted with a code
    the set does not contain refutes it.  This is what keeps the
    predicate from degenerating into "terminates without erroring" with
    the set along for the ride. *)
Lemma must_exit_in_at_wrong_code : forall segs S code c,
  m_halted (cfg_model c) = Some code ->
  ~ In code S ->
  ~ must_exit_in_at segs S c.
Proof.
  intros segs S code c Hh Hnin Hme.
  destruct (must_exit_in_at_halted_inv _ _ _ _ Hme Hh) as (Hin & _).
  exact (Hnin Hin).
Qed.

(** NEGATIVE, the SIGNAL route, and this one has no single-code analogue
    in this file because [must_exit_at]'s callers never needed it stated:
    a configuration whose [State.m_killed] is set refutes the predicate
    at every set, whatever [State.m_halted] holds.

    The base case is out by its own [State.m_killed] conjunct.  What
    rules the step case out is [State.m_killed_of_m_halted_none], the
    representation invariant that a model with no halt status has no kill
    status either — [State.with_killed] sets both — so a running
    configuration cannot be a killed one.  A death by signal is
    therefore not an allowed exit for ANY allowed set, which is the
    whole reason the statement this feeds is worth stating separately
    from error-freedom: a process that aborts errors nowhere. *)
Lemma must_exit_in_at_refuted_by_kill : forall segs S c sig,
  m_killed (cfg_model c) = Some sig ->
  ~ must_exit_in_at segs S c.
Proof.
  intros segs S c sig Hk Hme.
  inversion Hme as [c0 code Hh Hin Hk0 | c0 Hnone Hprog Hnoerr Hnext]; subst.
  - congruence.
  - pose proof (m_killed_of_m_halted_none _ Hnone) as Hk1. congruence.
Qed.

(** The predicate survives a [Run.star]: every configuration the run
    reaches satisfies it again.  A halted configuration takes no step at
    all ([sstep_not_halted]), so the walk can only be in the step case,
    where the [forall]-over-successors premise hands the next one over. *)
Lemma must_exit_in_at_star : forall segs S c tr c',
  must_exit_in_at segs S c ->
  star segs c tr c' ->
  must_exit_in_at segs S c'.
Proof.
  intros segs S c tr c' Hme Hstar. revert Hme.
  induction Hstar as [c0 | c0 evs c1 tr1 c2 Hss Hstar1 IH]; intros Hme.
  - exact Hme.
  - apply IH.
    inversion Hme as [c3 code Hh Hin Hk | c3 Hnone Hprog Hnoerr Hnext]; subst.
    + exfalso. pose proof (sstep_not_halted _ _ _ _ Hss) as Hn. congruence.
    + exact (Hnext evs c1 Hss).
Qed.

(** ... and therefore a run that can REACH a killed configuration refutes
    it.  This is the form the example side uses: a witness image supplies
    a [Run.star] to the configuration its [tkill] produced. *)
Lemma must_exit_in_at_refuted_by_reachable_kill : forall segs S c tr c' sig,
  star segs c tr c' ->
  m_killed (cfg_model c') = Some sig ->
  ~ must_exit_in_at segs S c.
Proof.
  intros segs S c tr c' sig Hstar Hk Hme.
  exact (must_exit_in_at_refuted_by_kill _ _ _ _ Hk
           (must_exit_in_at_star _ _ _ _ _ Hme Hstar)).
Qed.

(** "This run can die by a signal", at run level: some execution of it
    reaches a configuration whose [State.m_killed] is set.  Written as a
    [match] for the reason [run_decided] is, so that it and
    [must_exit_in] always speak about the same initial configuration.

    This is DELIBERATELY not [Equivalence.dies_by_signal], which is a
    statement about the trace SET: getting from a [State.KillEv] in a
    trace back to the configuration that emitted it would need to know
    that no other transition can emit one, and nothing in this file
    establishes that.  The reachability form is what a witness image
    actually hands over — a [Run.star] it built — so it is what the
    refutation takes. *)
Definition run_reaches_killed (img : Image) (lim : Z) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      exists tr c' sig,
        star segs (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c'
        /\ m_killed (cfg_model c') = Some sig
  end.

Lemma must_exit_in_refuted_by_kill : forall S img lim en inp,
  run_reaches_killed img lim en inp ->
  ~ must_exit_in S img lim en inp.
Proof.
  intros S [segs pc ph] lim [sp brk0 mbase rnd] inp Hk.
  cbn [must_exit_in run_reaches_killed] in *.
  destruct Hk as (tr & c' & sig & Hstar & Hkill).
  exact (must_exit_in_at_refuted_by_reachable_kill _ _ _ _ _ _ Hstar Hkill).
Qed.

(* -------------------------------------------------------------------------
   Non-vacuity: the set form really produces an exit event, carrying a
   status the set allows
   ------------------------------------------------------------------------- *)

(** The guard, and it is STRONGER than "some exit event happens": the
    code the emitted [State.ExitEv] carries is itself in [S].  Without
    the [In] conjunct the statement would be satisfied by a run that
    exits with anything at all, which is the reading the whole predicate
    exists to rule out. *)
Lemma must_exit_in_at_realizes : forall segs S c,
  must_exit_in_at segs S c ->
  m_halted (cfg_model c) = None ->
  exists tr code fs c',
    In code S
    /\ star segs c (tr ++ [ExitEv code fs]) c'
    /\ m_halted (cfg_model c') = Some code.
Proof.
  intros segs S c Hme.
  induction Hme as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros Hrun.
  - congruence.
  - destruct Hprog as (evs & st & Hss). destruct st as [c1 |];
      [| exfalso; exact (Hnoerr evs Hss)].
    pose proof (Hnext evs c1 Hss) as Hme1.
    destruct (m_halted (cfg_model c1)) as [k |] eqn:Hh1.
    + destruct (must_exit_in_at_halted_inv _ _ _ _ Hme1 Hh1) as (Hin1 & Hnk).
      destruct (sstep_next_halts_by_exit _ _ _ _ Hss)
        as [Hnone1 | [(evs0 & code0 & Hevs & Hcode0 & _)
                     | (evs0 & sig & Hevs & Hsig)]];
        [congruence | | congruence].
      assert (Hcc : code0 = k) by congruence. subst code0.
      exists evs0, k, (m_fs (cfg_model c1)), c1.
      split; [exact Hin1 | split; [| exact Hh1]].
      rewrite <- Hevs. exact (star_one _ _ _ _ Hss).
    + destruct (IH evs c1 Hss Hh1) as (tr & code & fs & c' & Hin' & Hstar & Hh').
      exists (evs ++ tr), code, fs, c'.
      split; [exact Hin' | split; [| exact Hh']].
      rewrite <- app_assoc. exact (star_step _ _ _ _ _ _ Hss Hstar).
Qed.

Lemma must_exit_in_realizes : forall S img lim en inp,
  must_exit_in S img lim en inp ->
  exists tr code fs,
    In code S /\ bh_traces (run img lim en inp) (tr ++ [ExitEv code fs]).
Proof.
  intros S [segs pc ph] lim [sp brk0 mbase rnd] inp Hme.
  cbn [must_exit_in] in Hme.
  assert (Hnone : m_halted
                    (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))
                  = None)
    by (cbn [init_config cfg_model]; reflexivity).
  destruct (must_exit_in_at_realizes _ _ _ Hme Hnone)
    as (tr & code & fs & c' & Hin & Hstar & _).
  exists tr, code, fs. split; [exact Hin |].
  cbn [run bh_traces]. unfold obs_trace.
  exists (tr ++ [ExitEv code fs]), c'. split; [exact Hstar | apply is_prefix_refl].
Qed.

(* =========================================================================
   The set form under a spurious-failure configuration
   =========================================================================

   The same relation to [must_exit_in_at] that [must_exit_at_cfg] has to
   [must_exit_at]: the predicate over [Run.sstep_cfg cfg], premise for
   premise.  It is what a task pinned to [Run.forced_only_cfg] states,
   for the reason that section's header gives — a binary that reads its
   input decides nothing under a reading where the open may be refused
   without cause — and the pin is a WEAKENING, which is
   [must_exit_in_at_cfg_mono]. *)

Inductive must_exit_in_at_cfg (cfg : SpuriousCfg) (segs : list Segment)
    (S : list word) : config -> Prop :=
| must_exit_in_at_cfg_halted : forall c code,
    m_halted (cfg_model c) = Some code ->
    In code S ->
    m_killed (cfg_model c) = None ->
    must_exit_in_at_cfg cfg segs S c
| must_exit_in_at_cfg_running : forall c,
    m_halted (cfg_model c) = None ->
    (exists evs st, sstep_cfg segs cfg c evs st) ->
    (forall evs, ~ sstep_cfg segs cfg c evs SError) ->
    (forall evs c', sstep_cfg segs cfg c evs (SNext c') ->
                    must_exit_in_at_cfg cfg segs S c') ->
    must_exit_in_at_cfg cfg segs S c.

Definition must_exit_in_scfg (cfg : SpuriousCfg) (S : list word) (img : Image)
    (lim : Z) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      must_exit_in_at_cfg cfg segs S (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

Lemma must_exit_in_at_cfg_halted_inv : forall cfg segs S c code,
  must_exit_in_at_cfg cfg segs S c ->
  m_halted (cfg_model c) = Some code ->
  In code S /\ m_killed (cfg_model c) = None.
Proof.
  intros cfg segs S c code Hme Hh.
  inversion Hme as [c0 code0 Hh0 Hin0 Hk0 | c0 Hnone Hprog Hnoerr Hnext]; subst.
  - assert (Heq : code0 = code) by congruence. subst code0. split; assumption.
  - congruence.
Qed.

Lemma must_exit_in_at_cfg_no_error : forall cfg segs S c,
  must_exit_in_at_cfg cfg segs S c -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros cfg segs S c Hme.
  induction Hme as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros Herr;
    destruct Herr as (tr & c2 & evs & Hstar & Hsserr).
  - assert (Hne : m_halted (cfg_model c) <> None) by (rewrite Hh; discriminate).
    destruct (star_cfg_from_halted _ _ _ _ _ Hstar Hne) as (_ & Heq); subst c2.
    pose proof (sstep_cfg_not_halted _ _ _ _ _ Hsserr) as Hnone. congruence.
  - destruct Hstar as [c0 | c0 evs0 c1 tr1 c3 Hss Hstar1].
    + exact (Hnoerr evs Hsserr).
    + apply (IH evs0 c1 Hss). exists tr1, c3, evs. split; assumption.
Qed.

Lemma must_exit_in_scfg_no_error : forall cfg S img lim en inp,
  must_exit_in_scfg cfg S img lim en inp ->
  ~ bh_errors (run_scfg cfg img lim en inp).
Proof.
  intros cfg S [segs pc ph] lim [sp brk0 mbase rnd] inp Hme.
  cbn [must_exit_in_scfg] in Hme. cbn [run_scfg bh_errors].
  exact (must_exit_in_at_cfg_no_error _ _ _ _ Hme).
Qed.

Lemma must_exit_in_scfg_modeled : forall cfg S img lim en inp,
  must_exit_in_scfg cfg S img lim en inp ->
  ~ bh_unmodeled (run_scfg cfg img lim en inp).
Proof.
  intros cfg S img lim en inp Hme Hun.
  exact (must_exit_in_scfg_no_error _ _ _ _ _ _ Hme
           (run_scfg_unmodeled_errors _ _ _ _ _ Hun)).
Qed.

Lemma must_exit_in_scfg_refuted_by_error : forall cfg S img lim en inp,
  bh_errors (run_scfg cfg img lim en inp) ->
  ~ must_exit_in_scfg cfg S img lim en inp.
Proof.
  intros cfg S img lim en inp Herr Hme.
  exact (must_exit_in_scfg_no_error _ _ _ _ _ _ Hme Herr).
Qed.

Lemma must_exit_in_at_cfg_refuted_by_kill : forall cfg segs S c sig,
  m_killed (cfg_model c) = Some sig ->
  ~ must_exit_in_at_cfg cfg segs S c.
Proof.
  intros cfg segs S c sig Hk Hme.
  inversion Hme as [c0 code Hh Hin Hk0 | c0 Hnone Hprog Hnoerr Hnext]; subst.
  - congruence.
  - pose proof (m_killed_of_m_halted_none _ Hnone) as Hk1. congruence.
Qed.

Lemma must_exit_in_at_cfg_star : forall cfg segs S c tr c',
  must_exit_in_at_cfg cfg segs S c ->
  star_cfg segs cfg c tr c' ->
  must_exit_in_at_cfg cfg segs S c'.
Proof.
  intros cfg segs S c tr c' Hme Hstar. revert Hme.
  induction Hstar as [c0 | c0 evs c1 tr1 c2 Hss Hstar1 IH]; intros Hme.
  - exact Hme.
  - apply IH.
    inversion Hme as [c3 code Hh Hin Hk | c3 Hnone Hprog Hnoerr Hnext]; subst.
    + exfalso. pose proof (sstep_cfg_not_halted _ _ _ _ _ Hss) as Hn. congruence.
    + exact (Hnext evs c1 Hss).
Qed.

Lemma must_exit_in_at_cfg_refuted_by_reachable_kill :
  forall cfg segs S c tr c' sig,
  star_cfg segs cfg c tr c' ->
  m_killed (cfg_model c') = Some sig ->
  ~ must_exit_in_at_cfg cfg segs S c.
Proof.
  intros cfg segs S c tr c' sig Hstar Hk Hme.
  exact (must_exit_in_at_cfg_refuted_by_kill _ _ _ _ _ Hk
           (must_exit_in_at_cfg_star _ _ _ _ _ _ Hme Hstar)).
Qed.

(** The configured twin, over [Run.star_cfg]. *)
Definition run_reaches_killed_cfg (cfg : SpuriousCfg) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      exists tr c' sig,
        star_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c'
        /\ m_killed (cfg_model c') = Some sig
  end.

Lemma must_exit_in_scfg_refuted_by_kill : forall cfg S img lim en inp,
  run_reaches_killed_cfg cfg img lim en inp ->
  ~ must_exit_in_scfg cfg S img lim en inp.
Proof.
  intros cfg S [segs pc ph] lim [sp brk0 mbase rnd] inp Hk.
  cbn [must_exit_in_scfg run_reaches_killed_cfg] in *.
  destruct Hk as (tr & c' & sig & Hstar & Hkill).
  exact (must_exit_in_at_cfg_refuted_by_reachable_kill _ _ _ _ _ _ _ Hstar Hkill).
Qed.

Lemma must_exit_in_at_cfg_wrong_code : forall cfg segs S code c,
  m_halted (cfg_model c) = Some code ->
  ~ In code S ->
  ~ must_exit_in_at_cfg cfg segs S c.
Proof.
  intros cfg segs S code c Hh Hnin Hme.
  destruct (must_exit_in_at_cfg_halted_inv _ _ _ _ _ Hme Hh) as (Hin & _).
  exact (Hnin Hin).
Qed.

Lemma must_exit_in_at_cfg_mono_set : forall cfg segs S1 S2 c,
  (forall code, In code S1 -> In code S2) ->
  must_exit_in_at_cfg cfg segs S1 c ->
  must_exit_in_at_cfg cfg segs S2 c.
Proof.
  intros cfg segs S1 S2 c Hsub H.
  induction H as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH].
  - exact (must_exit_in_at_cfg_halted _ _ _ _ _ Hh (Hsub _ Hin) Hk).
  - apply must_exit_in_at_cfg_running; assumption.
Qed.

Lemma must_exit_in_scfg_mono_set : forall cfg S1 S2 img lim en inp,
  (forall code, In code S1 -> In code S2) ->
  must_exit_in_scfg cfg S1 img lim en inp ->
  must_exit_in_scfg cfg S2 img lim en inp.
Proof.
  intros cfg S1 S2 [segs pc ph] lim [sp brk0 mbase rnd] inp Hsub H.
  cbn [must_exit_in_scfg] in *.
  exact (must_exit_in_at_cfg_mono_set _ _ _ _ _ Hsub H).
Qed.

(** Non-vacuity under the configuration, and then the same guard carried
    to the UNFILTERED run: the exit the filtered reading realizes is an
    event the real program emits, not one the filter invented. *)
Lemma must_exit_in_at_cfg_realizes : forall cfg segs S c,
  must_exit_in_at_cfg cfg segs S c ->
  m_halted (cfg_model c) = None ->
  exists tr code fs c',
    In code S
    /\ star_cfg segs cfg c (tr ++ [ExitEv code fs]) c'
    /\ m_halted (cfg_model c') = Some code.
Proof.
  intros cfg segs S c Hme.
  induction Hme as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros Hrun.
  - congruence.
  - destruct Hprog as (evs & st & Hss). destruct st as [c1 |];
      [| exfalso; exact (Hnoerr evs Hss)].
    pose proof (Hnext evs c1 Hss) as Hme1.
    destruct (m_halted (cfg_model c1)) as [k |] eqn:Hh1.
    + destruct (must_exit_in_at_cfg_halted_inv _ _ _ _ _ Hme1 Hh1) as (Hin1 & Hnk).
      destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ Hss)
        as [Hnone1 | [(evs0 & code0 & Hevs & Hcode0 & _)
                     | (evs0 & sig & Hevs & Hsig)]];
        [congruence | | congruence].
      assert (Hcc : code0 = k) by congruence. subst code0.
      exists evs0, k, (m_fs (cfg_model c1)), c1.
      split; [exact Hin1 | split; [| exact Hh1]].
      rewrite <- Hevs. rewrite <- (app_nil_r evs).
      eapply star_cfg_step; [exact Hss | apply star_cfg_refl].
    + destruct (IH evs c1 Hss Hh1) as (tr & code & fs & c' & Hin' & Hstar & Hh').
      exists (evs ++ tr), code, fs, c'.
      split; [exact Hin' | split; [| exact Hh']].
      rewrite <- app_assoc. exact (star_cfg_step _ _ _ _ _ _ _ Hss Hstar).
Qed.

Lemma must_exit_in_scfg_realizes : forall cfg S img lim en inp,
  must_exit_in_scfg cfg S img lim en inp ->
  exists tr code fs,
    In code S /\ bh_traces (run_scfg cfg img lim en inp) (tr ++ [ExitEv code fs]).
Proof.
  intros cfg S [segs pc ph] lim [sp brk0 mbase rnd] inp Hme.
  cbn [must_exit_in_scfg] in Hme.
  assert (Hnone : m_halted
                    (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))
                  = None)
    by (cbn [init_config cfg_model]; reflexivity).
  destruct (must_exit_in_at_cfg_realizes _ _ _ _ Hme Hnone)
    as (tr & code & fs & c' & Hin & Hstar & _).
  exists tr, code, fs. split; [exact Hin |].
  cbn [run_scfg bh_traces]. unfold obs_trace_cfg.
  exists (tr ++ [ExitEv code fs]), c'. split; [exact Hstar | apply is_prefix_refl].
Qed.

Lemma must_exit_in_scfg_realizes_run : forall cfg S img lim en inp,
  must_exit_in_scfg cfg S img lim en inp ->
  exists tr code fs,
    In code S /\ bh_traces (run img lim en inp) (tr ++ [ExitEv code fs]).
Proof.
  intros cfg S img lim en inp Hme.
  destruct (must_exit_in_scfg_realizes _ _ _ _ _ _ Hme) as (tr & code & fs & Hin & Htr).
  exists tr, code, fs. split; [exact Hin |].
  exact (run_scfg_sub_traces _ _ _ _ _ _ Htr).
Qed.

(* -------------------------------------------------------------------------
   Meaning at [may_fail_cfg], the singleton bridge, and monotonicity in
   the configuration
   ------------------------------------------------------------------------- *)

Lemma must_exit_in_at_cfg_may_fail : forall segs S c,
  must_exit_in_at_cfg may_fail_cfg segs S c <-> must_exit_in_at segs S c.
Proof.
  intros segs S c; split; intros H.
  - induction H as [c code Hh Hin Hk | c Hnone (evs & st & Hss) Hnoerr _ IH].
    + exact (must_exit_in_at_halted _ _ _ _ Hh Hin Hk).
    + apply must_exit_in_at_running; [exact Hnone | | |].
      * exists evs, st. apply sstep_cfg_may_fail; exact Hss.
      * intros evs' Herr. apply (Hnoerr evs'). apply sstep_cfg_may_fail; exact Herr.
      * intros evs' c' Hss'. apply (IH evs' c'). apply sstep_cfg_may_fail; exact Hss'.
  - induction H as [c code Hh Hin Hk | c Hnone (evs & st & Hss) Hnoerr _ IH].
    + exact (must_exit_in_at_cfg_halted _ _ _ _ _ Hh Hin Hk).
    + apply must_exit_in_at_cfg_running; [exact Hnone | | |].
      * exists evs, st. apply sstep_cfg_may_fail; exact Hss.
      * intros evs' Herr. apply (Hnoerr evs'). apply sstep_cfg_may_fail; exact Herr.
      * intros evs' c' Hss'. apply (IH evs' c'). apply sstep_cfg_may_fail; exact Hss'.
Qed.

Lemma must_exit_in_scfg_may_fail : forall S img lim en inp,
  must_exit_in_scfg may_fail_cfg S img lim en inp <-> must_exit_in S img lim en inp.
Proof.
  intros S [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [must_exit_in_scfg must_exit_in]. apply must_exit_in_at_cfg_may_fail.
Qed.

(** The configured singleton is the configured single-code form, the
    [_scfg] twin of [must_exit_in_at_singleton]. *)
Lemma must_exit_in_at_cfg_singleton : forall cfg segs code c,
  must_exit_in_at_cfg cfg segs [code] c <-> must_exit_at_cfg cfg segs code c.
Proof.
  intros cfg segs code c; split; intros H.
  - induction H as [c code0 Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH].
    + cbn [In] in Hin. destruct Hin as [Heq | []]. subst code0.
      exact (must_exit_at_cfg_halted _ _ _ _ Hh Hk).
    + apply must_exit_at_cfg_running; assumption.
  - induction H as [c Hh Hk | c Hnone Hprog Hnoerr Hnext IH].
    + apply (must_exit_in_at_cfg_halted _ _ _ _ code Hh); [| exact Hk].
      cbn [In]. left; reflexivity.
    + apply must_exit_in_at_cfg_running; assumption.
Qed.

Lemma must_exit_in_scfg_singleton : forall cfg code img lim en inp,
  must_exit_in_scfg cfg [code] img lim en inp
  <-> must_exit_with_scfg cfg code img lim en inp.
Proof.
  intros cfg code [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [must_exit_in_scfg must_exit_with_scfg]. apply must_exit_in_at_cfg_singleton.
Qed.

(** A verdict under a configuration is a verdict under every SMALLER one,
    wherever the filter's question is answered along the way — the set
    form of [must_exit_at_cfg_mono], with [decided_from] the same
    premise. *)
Lemma must_exit_in_at_cfg_mono : forall cfg1 cfg2 segs S c,
  cfg_le cfg1 cfg2 ->
  decided_from cfg1 segs c ->
  must_exit_in_at_cfg cfg2 segs S c ->
  must_exit_in_at_cfg cfg1 segs S c.
Proof.
  intros cfg1 cfg2 segs S c Hle Hdec H.
  induction H as [c code Hh Hin Hk | c Hnone (evs & st & Hss) Hnoerr _ IH]; intros.
  - exact (must_exit_in_at_cfg_halted _ _ _ _ _ Hh Hin Hk).
  - apply must_exit_in_at_cfg_running; [exact Hnone | | |].
    + destruct c as [ms model].
      apply (sstep_cfg_progress segs cfg1 ms model evs st).
      * intros x8 Hsvc. exact (Hdec [] (mkCfg ms model) x8 (star_refl _ _) Hsvc).
      * exact (sstep_cfg_sub _ _ _ _ _ Hss).
    + intros evs' Herr. apply (Hnoerr evs'). exact (sstep_cfg_mono _ _ _ _ _ _ Hle Herr).
    + intros evs' c' Hss'.
      apply (IH evs' c' (sstep_cfg_mono _ _ _ _ _ _ Hle Hss')).
      exact (decided_from_step _ _ _ _ _ _ Hdec Hss').
Qed.

Lemma must_exit_in_at_cfg_of_must_exit_in_at : forall cfg segs S c,
  decided_from cfg segs c ->
  must_exit_in_at segs S c ->
  must_exit_in_at_cfg cfg segs S c.
Proof.
  intros cfg segs S c Hdec H.
  apply (must_exit_in_at_cfg_mono cfg may_fail_cfg segs S c
           (may_fail_cfg_greatest cfg) Hdec).
  apply must_exit_in_at_cfg_may_fail; exact H.
Qed.

Lemma must_exit_in_scfg_mono : forall cfg1 cfg2 S img lim en inp,
  cfg_le cfg1 cfg2 ->
  run_decided cfg1 img lim en inp ->
  must_exit_in_scfg cfg2 S img lim en inp ->
  must_exit_in_scfg cfg1 S img lim en inp.
Proof.
  intros cfg1 cfg2 S [segs pc ph] lim [sp brk0 mbase rnd] inp Hle Hdec H.
  cbn [must_exit_in_scfg run_decided] in *.
  exact (must_exit_in_at_cfg_mono _ _ _ _ _ Hle Hdec H).
Qed.

Lemma must_exit_in_scfg_of_must_exit_in : forall cfg S img lim en inp,
  run_decided cfg img lim en inp ->
  must_exit_in S img lim en inp ->
  must_exit_in_scfg cfg S img lim en inp.
Proof.
  intros cfg S img lim en inp Hdec H.
  apply (must_exit_in_scfg_mono cfg may_fail_cfg _ _ _ _ _
           (may_fail_cfg_greatest cfg) Hdec).
  apply must_exit_in_scfg_may_fail; exact H.
Qed.

(** The configured bridge from the single-code form: a binary proved to
    exit with one code under [cfg] satisfies the set form there for every
    set containing it. *)
Lemma must_exit_with_scfg_in : forall cfg S code img lim en inp,
  must_exit_with_scfg cfg code img lim en inp ->
  In code S ->
  must_exit_in_scfg cfg S img lim en inp.
Proof.
  intros cfg S code img lim en inp Hme Hin.
  apply (must_exit_in_scfg_mono_set cfg [code] S img lim en inp).
  - intros code0 Hin0. cbn [In] in Hin0. destruct Hin0 as [Heq | []].
    subst code0. exact Hin.
  - apply must_exit_in_scfg_singleton; exact Hme.
Qed.
