(** * LinuxProcessSem.OmniRun — omni-big-step judgments over [Run.sstep]

    ADDITIVE, and a candidate for the trusted prefix: this file changes
    nothing in [Run] and redefines no existing name.  It adds three
    judgments over the one-step relation [Run.sstep] and proves each of
    [Run.run]'s observables equivalent to one of them, so a consumer may
    state an obligation in either form and move between the two through
    a proved [iff] ([bh_all_errors_iff], [bh_errors_iff],
    [bh_unmodeled_iff] and [bh_traces_iff] at the end of this file;
    [EquivalenceDefinition.OmniEquivalence] restates the theorem
    families the same way).

    ** The three judgments

    A maximal execution from a configuration [c] is a chain of
    [Run.sstep] transitions that either reaches a halted configuration,
    takes the error transition [Run.SError], or never ends.  The first
    two are the finite [outcome]s a postcondition sees, together with
    the accumulated event trace:

    - [exec c Q] (inductive): EVERY maximal execution from [c] is finite,
      and its trace and outcome satisfy [Q].  This is
      [Run.all_traces_error] and [MustExit.must_exit_at] generalised to
      an arbitrary postcondition; it delivers termination, the absence
      of errors and the shape of the trace in ONE induction.
    - [coexec c Q] (coinductive, the same constructors minus the
      progress premise): every maximal execution that ENDS satisfies
      [Q]; one that runs forever is unconstrained.  This is the safety
      reading, and it is what [Run.reaches_error] and
      [Run.reaches_unmodeled] turn into once negated ([bh_errors_iff],
      [bh_unmodeled_iff]).
    - [cosafe c P] (coinductive): every finite PREFIX of every
      execution satisfies [P].  This is what [Run.obs_trace] is, and it
      is the judgment trace equivalence lives in
      ([obs_equiv_iff_cosafe]).

    ** Why the pair [exec]/[coexec] alone cannot carry trace equivalence

    [exec] and [coexec] constrain only the executions that END: a
    diverging execution reaches no halted configuration and takes no
    error transition, so it contributes nothing to either judgment.
    Consequently "write a byte to stdout, then run forever" and "run
    forever" satisfy exactly the same [coexec] postconditions (both
    satisfy every one) and the same [exec] postconditions (neither
    satisfies any), although
    [Checks.Examples.write_then_diverge_vs_diverge] pins that
    [Equivalence.equiv] distinguishes them: the byte is observable as
    it happens.  Agreement on all [exec]/[coexec] postconditions is
    therefore STRICTLY WEAKER than [Equivalence.trace_equiv], and
    [Checks.Omni] pins that weakness on two concrete images
    ([Checks.Omni.loop_wloop_coexec_agree] against
    [Checks.Omni.loop_wloop_not_trace_equiv]).  Trace equivalence is
    agreement on all prefix-closed [cosafe] postconditions
    ([obs_equiv_iff_cosafe]); the other two judgments carry the
    exit-code, error and coverage facts.

    ** Outcomes carry the configuration

    [OHalt c'] is the halted configuration, whose exit code is
    [State.m_halted]; [OError c'] is the configuration FROM WHICH the
    error transition was taken.  Carrying [c'] is what lets a
    postcondition tell a modeled crash from the model giving up:
    [Run.unmodeled_at] is a predicate on that configuration, so
    [Equivalence.modeled] becomes the postcondition [covered] on the
    same judgment that [Equivalence.error_free] ([never_errors]) and
    [Run.all_traces_error] ([errors]) use.

    ** Stuck configurations read as silent

    [coexec] carries NO progress premise: a non-halted configuration
    with no transition at all satisfies [coexec c Q] for every [Q],
    exactly as a diverging one does ([stuck_coexec_any]).  This follows
    the tree's existing reading — [Run.reaches_error] holds of no stuck
    configuration and [Run.obs_trace] sees nothing after it, so today's
    [Equivalence.equiv] treats a run that stops without halting as
    invisible — and it is what makes [bh_errors_iff] and
    [bh_unmodeled_iff] unconditional: the left-to-right direction of
    each would otherwise need a proof that a non-halted configuration
    can always take a step, which lives above this file
    ([Checks.Progress.receptive]).  [exec] KEEPS the progress premise,
    as [MustExit.must_exit_at] does, so [MustExit.must_exit_with] still
    fails on a run that gets stuck ([stuck_no_exec]).  The
    progress-carrying variant of the coinductive judgment is kept as
    [coexec_progress], with [coexec_progress_implies] showing it is the
    stronger of the two and [stuck_not_coexec_progress] showing where
    they differ, so that reversing this choice is a local change.
    [Checks.Omni.coexec_progress_iff] proves that on this tree the two
    coincide, because no non-halted configuration is stuck
    ([Checks.Omni.sstep_receptive]).

    ** May-facts

    [Run.reaches_error] and [Run.reaches_unmodeled] are existential.
    Their omni form is [omni_may]: SOME maximal execution, as the
    relation [mexec], satisfies the postcondition.  [exec_realizes] and
    [exec_sound] relate the two sides: an [exec] judgment is realised by
    at least one maximal execution, and every maximal execution
    satisfies it.  The same relation is what turns an exact [exec]
    postcondition into the whole trace set ([exec_obs_iff]) — the
    "admits" half that an omni judgment does not deliver by itself. *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.

Variable segs : list Segment.

(** How a maximal finite execution ends: halted, or erroring FROM the
    carried configuration. *)
Inductive outcome :=
| OHalt (c : config)
| OError (c : config).

Definition post := list event -> outcome -> Prop.

Definition is_error (o : outcome) : Prop :=
  match o with OHalt _ => False | OError _ => True end.

(** The postconditions the existing statement families use. *)
Definition errors : post := fun _ o => is_error o.

Definition never_errors : post := fun _ o => ~ is_error o.

(** [Equivalence.modeled]'s postcondition: an error is allowed, but not
    one taken from a configuration the model declines to interpret. *)
Definition covered : post :=
  fun _ o => match o with
             | OHalt _ => True
             | OError c => ~ unmodeled_at segs c
             end.

(** Its existential dual, for [Run.reaches_unmodeled]. *)
Definition uncovered : post :=
  fun _ o => match o with
             | OHalt _ => False
             | OError c => unmodeled_at segs c
             end.

(** [MustExit.must_exit_at]'s postcondition.  A DEATH BY SIGNAL IS NOT AN
    EXIT, and the second conjunct is what says so: a process killed by
    SIGABRT carries the signal number in [State.m_halted] -- that field
    is the "process is over" marker, and [State.m_killed] is what says
    which of the two ways it got there -- so without the conjunct this
    postcondition would read an abort as a verdict of 6.  The same
    conjunct sits on [MustExit.must_exit_at_halted] for the same
    reason. *)
Definition exits_with (code : word) : post :=
  fun _ o => match o with
             | OHalt c => m_halted (cfg_model c) = Some code
                          /\ m_killed (cfg_model c) = None
             | OError _ => False
             end.

Lemma never_errors_covered : forall tr o, never_errors tr o -> covered tr o.
Proof. intros tr [c | c] H; [exact I | exact (fun _ => H I)]. Qed.

Lemma exits_with_never_errors : forall code tr o,
  exits_with code tr o -> never_errors tr o.
Proof. intros code tr [c | c] H; [exact (fun h => h) | exact (fun _ => H)]. Qed.

(** Every [Run.sstep] leaves a non-halted configuration (every
    constructor carries [m_halted model = None]); the same fact as
    [MustExit.sstep_not_halted], restated here because this file sits
    below [MustExit]. *)
Lemma sstep_from_running : forall c evs st,
  sstep segs c evs st -> m_halted (cfg_model c) = None.
Proof. intros c evs st H; inversion H; subst; cbn; assumption. Qed.

(* =========================================================================
   Maximal executions — the "may" side
   ========================================================================= *)

(** One maximal finite execution: its trace and how it ended. *)
Inductive mexec : config -> list event -> outcome -> Prop :=
| mexec_halt : forall c,
    m_halted (cfg_model c) <> None ->
    mexec c [] (OHalt c)
| mexec_error : forall c evs,
    sstep segs c evs SError ->
    mexec c evs (OError c)
| mexec_next : forall c evs c' tr o,
    sstep segs c evs (SNext c') ->
    mexec c' tr o ->
    mexec c (evs ++ tr) o.

Lemma star_mexec : forall c tr c' tr' o,
  star segs c tr c' -> mexec c' tr' o -> mexec c (tr ++ tr') o.
Proof.
  intros c tr c' tr' o Hstar; revert tr' o.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros tr' o Hm;
    [exact Hm |].
  rewrite <- app_assoc. exact (mexec_next _ _ _ _ _ Hss (IH _ _ Hm)).
Qed.

Lemma mexec_halt_star : forall c tr o,
  mexec c tr o ->
  forall c', o = OHalt c' -> star segs c tr c' /\ m_halted (cfg_model c') <> None.
Proof.
  intros c tr o Hm.
  induction Hm as [c Hh | c evs Hss | c evs c1 tr o Hss Hm IH]; intros c' Heq.
  - injection Heq as <-. split; [apply star_refl | exact Hh].
  - discriminate Heq.
  - destruct (IH _ Heq) as (Hstar & Hh).
    split; [exact (star_step _ _ _ _ _ _ Hss Hstar) | exact Hh].
Qed.

Lemma mexec_error_star : forall c tr o,
  mexec c tr o ->
  forall c', o = OError c' ->
  exists tr1 evs, tr = tr1 ++ evs /\ star segs c tr1 c' /\ sstep segs c' evs SError.
Proof.
  intros c tr o Hm.
  induction Hm as [c Hh | c evs Hss | c evs c1 tr o Hss Hm IH]; intros c' Heq.
  - discriminate Heq.
  - injection Heq as <-. exists [], evs.
    split; [reflexivity | split; [apply star_refl | exact Hss]].
  - destruct (IH _ Heq) as (tr1 & evs' & -> & Hstar & Hss').
    exists (evs ++ tr1), evs'.
    split; [apply app_assoc | split; [exact (star_step _ _ _ _ _ _ Hss Hstar) | exact Hss']].
Qed.

(** [Run.reaches_error] is "some maximal execution errors". *)
Lemma reaches_error_iff_may : forall c,
  reaches_error segs c <-> exists tr o, mexec c tr o /\ errors tr o.
Proof.
  intros c; split.
  - intros (tr & c2 & evs & Hstar & Hss).
    exists (tr ++ evs), (OError c2).
    split; [exact (star_mexec _ _ _ _ _ Hstar (mexec_error _ _ Hss)) | exact I].
  - intros (tr & [c' | c'] & Hm & He); [destruct He |].
    destruct (mexec_error_star _ _ _ Hm c' eq_refl) as (tr1 & evs & _ & Hstar & Hss).
    exists tr1, c', evs. split; assumption.
Qed.

(** [Run.reaches_unmodeled] is "some maximal execution errors from an
    uncovered configuration". *)
Lemma reaches_unmodeled_iff_may : forall c,
  reaches_unmodeled segs c <-> exists tr o, mexec c tr o /\ uncovered tr o.
Proof.
  intros c; split.
  - intros (tr & c' & Hstar & Hun).
    destruct (unmodeled_at_sstep_error _ _ Hun) as (evs & Hss).
    exists (tr ++ evs), (OError c').
    split; [exact (star_mexec _ _ _ _ _ Hstar (mexec_error _ _ Hss)) | exact Hun].
  - intros (tr & [c' | c'] & Hm & Hun); [destruct Hun |].
    destruct (mexec_error_star _ _ _ Hm c' eq_refl) as (tr1 & evs & _ & Hstar & _).
    exists tr1, c'. split; assumption.
Qed.

(* =========================================================================
   Terminating omni-exec (inductive)
   ========================================================================= *)

Inductive exec : config -> post -> Prop :=
| exec_halt : forall c Q,
    m_halted (cfg_model c) <> None ->
    Q [] (OHalt c) ->
    exec c Q
| exec_step : forall c Q,
    m_halted (cfg_model c) = None ->
    (exists evs st, sstep segs c evs st) ->
    (forall evs, sstep segs c evs SError -> Q evs (OError c)) ->
    (forall evs c', sstep segs c evs (SNext c') ->
                    exec c' (fun tr o => Q (evs ++ tr) o)) ->
    exec c Q.

(** Consequence: the postcondition may be weakened. *)
Lemma exec_conseq : forall c (Q Q' : post),
  exec c Q -> (forall tr o, Q tr o -> Q' tr o) -> exec c Q'.
Proof.
  intros c Q Q' H; revert Q'.
  induction H as [c Q Hh HQ | c Q Hh Hprog Herr Hnext IH]; intros Q' Himp.
  - apply exec_halt; [exact Hh | apply Himp, HQ].
  - apply exec_step; [exact Hh | exact Hprog | intros evs Hss; apply Himp, Herr, Hss |].
    intros evs c' Hss. apply (IH evs c' Hss). intros tr o; apply Himp.
Qed.

(** Halted configuration: the base case, as a lemma. *)
Lemma exec_halted : forall c (Q : post),
  m_halted (cfg_model c) <> None -> Q [] (OHalt c) -> exec c Q.
Proof. intros; apply exec_halt; assumption. Qed.

(** A configuration with exactly one transition: the shape a
    deterministic instruction step produces. *)
Lemma exec_step_only : forall c (Q : post) evs1 c1,
  sstep segs c evs1 (SNext c1) ->
  (forall evs st, sstep segs c evs st -> evs = evs1 /\ st = SNext c1) ->
  exec c1 (fun tr o => Q (evs1 ++ tr) o) ->
  exec c Q.
Proof.
  intros c Q evs1 c1 Hss Honly Hex.
  apply exec_step.
  - exact (sstep_from_running _ _ _ Hss).
  - exists evs1, (SNext c1); exact Hss.
  - intros evs Herr. destruct (Honly _ _ Herr) as (_ & Habs). discriminate Habs.
  - intros evs c' Hss'. destruct (Honly _ _ Hss') as (-> & Heq).
    injection Heq as ->. exact Hex.
Qed.

(** Step closure: an omni judgment survives any [Run.star] prefix, with
    the events already emitted prepended in the postcondition. *)
Lemma exec_star : forall c (Q : post) tr c',
  exec c Q -> star segs c tr c' -> exec c' (fun tr' o => Q (tr ++ tr') o).
Proof.
  intros c Q tr c' Hex Hstar. revert Q Hex.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros Q Hex.
  - eapply exec_conseq; [exact Hex |]. intros tr o; cbn [app]; exact (fun h => h).
  - inversion Hex as [c0 Q0 Hh HQ | c0 Q0 Hh Hprog Herr Hnext]; subst.
    + exfalso. apply Hh. exact (sstep_from_running _ _ _ Hss).
    + specialize (Hnext evs c2 Hss).
      eapply exec_conseq; [exact (IH _ Hnext) |].
      intros tr' o; cbn beta. rewrite app_assoc. exact (fun h => h).
Qed.

(** Soundness: every maximal execution of an [exec] judgment satisfies
    its postcondition ... *)
Lemma exec_sound : forall c (Q : post),
  exec c Q -> forall tr o, mexec c tr o -> Q tr o.
Proof.
  intros c Q H.
  induction H as [c Q Hh HQ | c Q Hh Hprog Herr Hnext IH]; intros tr o Hm;
    inversion Hm as [c0 Hh0 | c0 evs Hss | c0 evs c1 tr1 o1 Hss Hm']; subst.
  - exact HQ.
  - exfalso. apply Hh. exact (sstep_from_running _ _ _ Hss).
  - exfalso. apply Hh. exact (sstep_from_running _ _ _ Hss).
  - exfalso. apply Hh0. exact Hh.
  - exact (Herr _ Hss).
  - exact (IH _ _ Hss _ _ Hm').
Qed.

(** ... and at least one maximal execution exists: the progress
    premise is what keeps [exec] from holding vacuously. *)
Lemma exec_realizes : forall c (Q : post),
  exec c Q -> exists tr o, mexec c tr o /\ Q tr o.
Proof.
  intros c Q H.
  induction H as [c Q Hh HQ | c Q Hh Hprog Herr Hnext IH].
  - exists [], (OHalt c). split; [apply mexec_halt; exact Hh | exact HQ].
  - destruct Hprog as (evs & [c' |] & Hss).
    + destruct (IH _ _ Hss) as (tr & o & Hm & HQ).
      exists (evs ++ tr), o.
      split; [exact (mexec_next _ _ _ _ _ Hss Hm) | exact HQ].
    + exists evs, (OError c).
      split; [apply mexec_error; exact Hss | exact (Herr _ Hss)].
Qed.

(** A stuck non-halted configuration satisfies no [exec], whatever the
    postcondition: this is the reading [MustExit.must_exit_at] shares. *)
Lemma stuck_no_exec : forall c,
  m_halted (cfg_model c) = None ->
  (forall evs st, ~ sstep segs c evs st) ->
  forall Q, ~ exec c Q.
Proof.
  intros c Hh Hstuck Q Hex.
  inversion Hex as [c0 Q0 Hh0 HQ | c0 Q0 Hh0 (evs & st & Hss) Herr Hnext]; subst.
  - exact (Hh0 Hh).
  - exact (Hstuck _ _ Hss).
Qed.

(** The omni reading of [Run.all_traces_error].  The right-to-left
    direction is stated over an arbitrary postcondition entailing an
    error, because [induction] on an [exec] whose postcondition is a
    concrete lambda abstracts it away. *)
Lemma exec_errors_all_traces_error : forall c (Q : post),
  exec c Q -> (forall tr o, Q tr o -> is_error o) -> all_traces_error segs c.
Proof.
  intros c Q H. induction H as [c Q Hh HQ | c Q Hh Hprog Herr Hnext IH]; intros Himp.
  - exfalso. exact (Himp _ _ HQ).
  - constructor; [exact Hprog |].
    intros evs c' Hss. apply (IH evs c' Hss).
    intros tr o Hq. exact (Himp (evs ++ tr) o Hq).
Qed.

Lemma all_traces_error_iff : forall c,
  all_traces_error segs c <-> exec c errors.
Proof.
  intros c; split.
  - intros H. induction H as [c Hprog Hnext IH].
    destruct Hprog as (evs & st & Hss).
    apply exec_step.
    + exact (sstep_from_running _ _ _ Hss).
    + exists evs, st; exact Hss.
    + intros; exact I.
    + intros evs' c' Hss'. exact (IH evs' c' Hss').
  - intros H. exact (exec_errors_all_traces_error _ _ H (fun _ _ h => h)).
Qed.

(** No maximal execution errors: the [OError] outcome is refuted. *)
Lemma exec_no_error : forall c,
  exec c never_errors -> ~ reaches_error segs c.
Proof.
  intros c Hex (tr & c2 & evs & Hstar & Hss).
  exact (exec_sound _ _ Hex _ _
           (star_mexec _ _ _ _ _ Hstar (mexec_error _ _ Hss)) I).
Qed.

(** An exact trace postcondition characterises the whole trace set: the
    "only" half is [exec_sound] along the prefix ([exec_star]), the
    "admits" half is the realised execution ([exec_realizes]). *)
Lemma exec_obs_iff : forall c (full : list event),
  exec c (fun tr o => tr = full /\ ~ is_error o) ->
  forall tr, obs_trace segs c tr <-> is_prefix tr full.
Proof.
  intros c full Hex tr; split.
  - intros (tr' & c' & Hstar & Hp).
    destruct (exec_realizes _ _ (exec_star _ _ _ _ Hex Hstar))
      as (tr'' & o & _ & HQ).
    cbn beta in HQ. destruct HQ as (Heq & _). rewrite <- Heq.
    exact (is_prefix_trans _ _ _ Hp (is_prefix_app _ _)).
  - intros Hp.
    destruct (exec_realizes _ _ Hex) as (tr' & [c' | c'] & Hm & Heq & Hno);
      [| exfalso; exact (Hno I)].
    subst tr'. destruct (mexec_halt_star _ _ _ Hm c' eq_refl) as (Hstar & _).
    exists full, c'. split; [exact Hstar | exact Hp].
Qed.

(* =========================================================================
   Possibly-diverging omni-exec (coinductive) — no progress premise
   ========================================================================= *)

CoInductive coexec : config -> post -> Prop :=
| coexec_halt : forall c Q,
    m_halted (cfg_model c) <> None ->
    Q [] (OHalt c) ->
    coexec c Q
| coexec_step : forall c Q,
    m_halted (cfg_model c) = None ->
    (forall evs, sstep segs c evs SError -> Q evs (OError c)) ->
    (forall evs c', sstep segs c evs (SNext c') ->
                    coexec c' (fun tr o => Q (evs ++ tr) o)) ->
    coexec c Q.

Lemma exec_coexec : forall c Q, exec c Q -> coexec c Q.
Proof.
  intros c Q H.
  induction H as [c Q Hh HQ | c Q Hh Hprog Herr Hnext IH].
  - apply coexec_halt; assumption.
  - apply coexec_step; [exact Hh | exact Herr |].
    intros evs c' Hss; exact (IH evs c' Hss).
Qed.

Lemma coexec_conseq : forall c (Q Q' : post),
  coexec c Q -> (forall tr o, Q tr o -> Q' tr o) -> coexec c Q'.
Proof.
  cofix CH. intros c Q Q' H Himp.
  destruct H as [c Q Hh HQ | c Q Hh Herr Hnext].
  - apply coexec_halt; [exact Hh | apply Himp, HQ].
  - apply coexec_step; [exact Hh | intros evs Hss; apply Himp, Herr, Hss |].
    intros evs c' Hss. apply (CH _ _ _ (Hnext evs c' Hss)). intros tr o; apply Himp.
Qed.

(** The single-transition rule, as for [exec_step_only]. *)
Lemma coexec_step_only : forall c (Q : post) evs1 c1,
  sstep segs c evs1 (SNext c1) ->
  (forall evs st, sstep segs c evs st -> evs = evs1 /\ st = SNext c1) ->
  coexec c1 (fun tr o => Q (evs1 ++ tr) o) ->
  coexec c Q.
Proof.
  intros c Q evs1 c1 Hss Honly Hco.
  apply coexec_step.
  - exact (sstep_from_running _ _ _ Hss).
  - intros evs Herr. destruct (Honly _ _ Herr) as (_ & Habs). discriminate Habs.
  - intros evs c' Hss'. destruct (Honly _ _ Hss') as (-> & Heq).
    injection Heq as ->. exact Hco.
Qed.

Lemma coexec_star : forall c (Q : post) tr c',
  coexec c Q -> star segs c tr c' -> coexec c' (fun tr' o => Q (tr ++ tr') o).
Proof.
  intros c Q tr c' Hex Hstar. revert Q Hex.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros Q Hex.
  - eapply coexec_conseq; [exact Hex |]. intros tr o; cbn [app]; exact (fun h => h).
  - inversion Hex as [c0 Q0 Hh HQ | c0 Q0 Hh Herr Hnext]; subst.
    + exfalso. apply Hh. exact (sstep_from_running _ _ _ Hss).
    + specialize (Hnext evs c2 Hss).
      eapply coexec_conseq; [exact (IH _ Hnext) |].
      intros tr' o; cbn beta. rewrite app_assoc. exact (fun h => h).
Qed.

(** Soundness: every maximal execution that ends satisfies the
    postcondition.  There is no realisation lemma: without a progress
    premise, nothing forces an execution to exist. *)
Lemma coexec_sound : forall c tr o,
  mexec c tr o -> forall Q, coexec c Q -> Q tr o.
Proof.
  intros c tr o Hm.
  induction Hm as [c Hh | c evs Hss | c evs c1 tr o Hss Hm IH]; intros Q Hco;
    destruct Hco as [c0 Q0 Hh0 HQ | c0 Q0 Hh0 Herr Hnext].
  - exact HQ.
  - exfalso. exact (Hh Hh0).
  - exfalso. apply Hh0. exact (sstep_from_running _ _ _ Hss).
  - exact (Herr _ Hss).
  - exfalso. apply Hh0. exact (sstep_from_running _ _ _ Hss).
  - exact (IH _ (Hnext _ _ Hss)).
Qed.

(** The silent reading of a stuck configuration, both ways: it
    satisfies every [coexec] ... *)
Lemma stuck_coexec_any : forall c,
  m_halted (cfg_model c) = None ->
  (forall evs st, ~ sstep segs c evs st) ->
  forall Q, coexec c Q.
Proof.
  intros c Hh Hstuck Q.
  apply coexec_step; [exact Hh | |].
  - intros evs Hss. exfalso. exact (Hstuck _ _ Hss).
  - intros evs c' Hss. exfalso. exact (Hstuck _ _ Hss).
Qed.

(** Safety direction: [Equivalence.error_free] from the judgment ... *)
Lemma coexec_no_error : forall c,
  coexec c never_errors -> ~ reaches_error segs c.
Proof.
  intros c Hco (tr & c2 & evs & Hstar & Hss).
  exact (coexec_sound _ _ _
           (star_mexec _ _ _ _ _ Hstar (mexec_error _ _ Hss)) _ Hco I).
Qed.

(** ... and the converse, unconditional because a stuck configuration
    is silent on both sides. *)
Lemma no_error_coexec : forall c,
  ~ reaches_error segs c -> coexec c never_errors.
Proof.
  cofix CH. intros c Hnoerr.
  destruct (m_halted (cfg_model c)) as [code |] eqn:Hh.
  - apply coexec_halt; [rewrite Hh; discriminate | exact (fun h => h)].
  - apply coexec_step; [exact Hh | |].
    + intros evs Hss. exfalso. apply Hnoerr.
      exists [], c, evs. split; [apply star_refl | exact Hss].
    + intros evs c' Hss. apply CH.
      intros (tr & c2 & evs2 & Hstar & Hss2). apply Hnoerr.
      exists (evs ++ tr), c2, evs2. split; [| exact Hss2].
      exact (star_step _ _ _ _ _ _ Hss Hstar).
Qed.

Lemma never_errors_iff : forall c,
  ~ reaches_error segs c <-> coexec c never_errors.
Proof. intros c; split; [apply no_error_coexec | apply coexec_no_error]. Qed.

(** [Equivalence.modeled], the same way: [covered] refutes an error
    taken from an uncovered configuration and tolerates every other. *)
Lemma coexec_covered : forall c,
  coexec c covered -> ~ reaches_unmodeled segs c.
Proof.
  intros c Hco (tr & c' & Hstar & Hun).
  destruct (unmodeled_at_sstep_error _ _ Hun) as (evs & Hss).
  exact (coexec_sound _ _ _
           (star_mexec _ _ _ _ _ Hstar (mexec_error _ _ Hss)) _ Hco Hun).
Qed.

Lemma no_unmodeled_coexec : forall c,
  ~ reaches_unmodeled segs c -> coexec c covered.
Proof.
  cofix CH. intros c Hno.
  destruct (m_halted (cfg_model c)) as [code |] eqn:Hh.
  - apply coexec_halt; [rewrite Hh; discriminate | exact I].
  - apply coexec_step; [exact Hh | |].
    + intros evs Hss Hun. apply Hno.
      exists [], c. split; [apply star_refl | exact Hun].
    + intros evs c' Hss. apply CH.
      intros (tr & c2 & Hstar & Hun). apply Hno.
      exists (evs ++ tr), c2. split; [| exact Hun].
      exact (star_step _ _ _ _ _ _ Hss Hstar).
Qed.

Lemma covered_iff : forall c,
  ~ reaches_unmodeled segs c <-> coexec c covered.
Proof. intros c; split; [apply no_unmodeled_coexec | apply coexec_covered]. Qed.

(* =========================================================================
   The progress-carrying alternative, kept for a local reversal
   ========================================================================= *)

(** [coexec] with the progress premise of [exec] and
    [MustExit.must_exit_at]: a stuck configuration REFUTES it.  Not used
    by any compat lemma; see the header. *)
CoInductive coexec_progress : config -> post -> Prop :=
| coexec_progress_halt : forall c Q,
    m_halted (cfg_model c) <> None ->
    Q [] (OHalt c) ->
    coexec_progress c Q
| coexec_progress_step : forall c Q,
    m_halted (cfg_model c) = None ->
    (exists evs st, sstep segs c evs st) ->
    (forall evs, sstep segs c evs SError -> Q evs (OError c)) ->
    (forall evs c', sstep segs c evs (SNext c') ->
                    coexec_progress c' (fun tr o => Q (evs ++ tr) o)) ->
    coexec_progress c Q.

Lemma coexec_progress_implies : forall c Q,
  coexec_progress c Q -> coexec c Q.
Proof.
  cofix CH. intros c Q H.
  destruct H as [c Q Hh HQ | c Q Hh Hprog Herr Hnext].
  - apply coexec_halt; assumption.
  - apply coexec_step; [exact Hh | exact Herr |].
    intros evs c' Hss. exact (CH _ _ (Hnext evs c' Hss)).
Qed.

(** Where the two readings differ: a stuck configuration. *)
Lemma stuck_not_coexec_progress : forall c,
  m_halted (cfg_model c) = None ->
  (forall evs st, ~ sstep segs c evs st) ->
  forall Q, ~ coexec_progress c Q.
Proof.
  intros c Hh Hstuck Q Hco.
  destruct Hco as [c0 Q0 Hh0 HQ | c0 Q0 Hh0 (evs & st & Hss) Herr Hnext].
  - exact (Hh0 Hh).
  - exact (Hstuck _ _ Hss).
Qed.

(* =========================================================================
   Prefix safety (coinductive) — what [Run.obs_trace] is
   ========================================================================= *)

(** Every finite prefix of every execution satisfies [P].  No progress
    premise and no error clause: a prefix property is a pure safety
    property, and this is the judgment trace equivalence lives in. *)
CoInductive cosafe : config -> (list event -> Prop) -> Prop :=
| cosafe_intro : forall c P,
    P [] ->
    (forall evs c', sstep segs c evs (SNext c') ->
                    cosafe c' (fun tr => P (evs ++ tr))) ->
    cosafe c P.

Lemma cosafe_star : forall c P tr c',
  cosafe c P -> star segs c tr c' -> P tr.
Proof.
  intros c P tr c' Hsafe Hstar. revert P Hsafe.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros P Hsafe.
  - inversion Hsafe; assumption.
  - inversion Hsafe as [c0 P0 Hnil Hnext]; subst.
    exact (IH _ (Hnext evs c2 Hss)).
Qed.

Lemma star_cosafe : forall c P,
  (forall tr c', star segs c tr c' -> P tr) -> cosafe c P.
Proof.
  cofix CH. intros c P Hall.
  apply cosafe_intro.
  - exact (Hall [] c (star_refl _ _)).
  - intros evs c' Hss. apply CH. intros tr c'' Hstar.
    apply (Hall (evs ++ tr) c''). exact (star_step _ _ _ _ _ _ Hss Hstar).
Qed.

Definition prefix_closed (P : list event -> Prop) : Prop :=
  forall tr tr', P tr -> is_prefix tr' tr -> P tr'.

Lemma obs_trace_is_prefix_closed : forall c, prefix_closed (obs_trace segs c).
Proof. intros c t t' Ht Hp. exact (obs_trace_prefix_closed _ _ _ _ Ht Hp). Qed.

(** [Run.obs_trace]'s universal dual: on a prefix-closed [P], "every
    observable trace satisfies [P]" is exactly [cosafe]. *)
Lemma cosafe_obs_iff : forall c P,
  prefix_closed P ->
  (cosafe c P <-> (forall tr, obs_trace segs c tr -> P tr)).
Proof.
  intros c P Hpc; split.
  - intros Hsafe tr (tr' & c' & Hstar & Hp).
    exact (Hpc _ _ (cosafe_star _ _ _ _ Hsafe Hstar) Hp).
  - intros Hall. apply star_cosafe. intros tr c' Hstar.
    apply Hall. exists tr, c'. split; [exact Hstar | apply is_prefix_refl].
Qed.

End WithSegs.

(** The refinement pair: each side's trace set is a prefix
    postcondition the other side satisfies.  Stated for two images,
    since the two runs of an equivalence load different segments. *)
Lemma obs_equiv_iff_refinement : forall segs1 c1 segs2 c2,
  (forall tr, obs_trace segs1 c1 tr <-> obs_trace segs2 c2 tr)
  <-> (cosafe segs1 c1 (obs_trace segs2 c2) /\ cosafe segs2 c2 (obs_trace segs1 c1)).
Proof.
  intros segs1 c1 segs2 c2.
  rewrite (cosafe_obs_iff segs1 c1 _ (obs_trace_is_prefix_closed segs2 c2)).
  rewrite (cosafe_obs_iff segs2 c2 _ (obs_trace_is_prefix_closed segs1 c1)).
  split.
  - intros Heq. split; intros tr Ht; apply Heq, Ht.
  - intros (H12 & H21) tr. split; [apply H12 | apply H21].
Qed.

(** Trace-set equality is "the two configurations satisfy the same
    prefix postconditions" — the omni statement of
    [Equivalence.trace_equiv].  Both directions are constructive; the
    hard direction instantiates [P] with the other side's trace set. *)
Lemma obs_equiv_iff_cosafe : forall segs1 c1 segs2 c2,
  (forall tr, obs_trace segs1 c1 tr <-> obs_trace segs2 c2 tr)
  <-> (forall P, prefix_closed P -> (cosafe segs1 c1 P <-> cosafe segs2 c2 P)).
Proof.
  intros segs1 c1 segs2 c2; split.
  - intros Heq P Hpc.
    rewrite (cosafe_obs_iff segs1 c1 P Hpc), (cosafe_obs_iff segs2 c2 P Hpc).
    split; intros Hall tr Hobs; apply Hall, Heq, Hobs.
  - intros Hall. apply obs_equiv_iff_refinement. split.
    + apply (Hall _ (obs_trace_is_prefix_closed segs2 c2)).
      apply star_cosafe. intros tr c' Hstar.
      exists tr, c'. split; [exact Hstar | apply is_prefix_refl].
    + apply (Hall _ (obs_trace_is_prefix_closed segs1 c1)).
      apply star_cosafe. intros tr c' Hstar.
      exists tr, c'. split; [exact Hstar | apply is_prefix_refl].
Qed.

(* =========================================================================
   Run-level judgments: the three argument groups of [Run.run]
   ========================================================================= *)

(** Written as a MATCH on the image and the [execve] entry for the same
    reason [Run.run] and [MustExit.must_exit_with] are: a proof
    unfolding one with [cbn [omni_run …]] gets the underlying
    [Run.init_config] application back as soon as those two arguments
    are concrete records, and every one of them speaks about the SAME
    configuration [Run.run] does. *)
Definition omni_run (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput)
    (Q : post) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      let vsegs := run_segments segs inp sp mbase in
      exec vsegs (init_config vsegs pc ph sp brk0 mbase rnd lim inp) Q
  end.

Definition omni_corun (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput)
    (Q : post) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      let vsegs := run_segments segs inp sp mbase in
      coexec vsegs (init_config vsegs pc ph sp brk0 mbase rnd lim inp) Q
  end.

Definition omni_cosafe (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput)
    (P : list event -> Prop) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      let vsegs := run_segments segs inp sp mbase in
      cosafe vsegs (init_config vsegs pc ph sp brk0 mbase rnd lim inp) P
  end.

(** SOME maximal execution satisfies [Q]: the existential twin. *)
Definition omni_may (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput)
    (Q : post) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      let vsegs := run_segments segs inp sp mbase in
      exists tr o, mexec vsegs (init_config vsegs pc ph sp brk0 mbase rnd lim inp) tr o
                   /\ Q tr o
  end.

(* =========================================================================
   Compat: the four fields of [Run.run], each unconditional
   ========================================================================= *)

Lemma bh_all_errors_iff : forall img lim en inp,
  bh_all_errors (run img lim en inp) <-> omni_run img lim en inp errors.
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [run bh_all_errors omni_run]. apply all_traces_error_iff.
Qed.

Lemma bh_errors_iff : forall img lim en inp,
  ~ bh_errors (run img lim en inp) <-> omni_corun img lim en inp never_errors.
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [run bh_errors omni_corun]. apply never_errors_iff.
Qed.

Lemma bh_errors_may_iff : forall img lim en inp,
  bh_errors (run img lim en inp) <-> omni_may img lim en inp errors.
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [run bh_errors omni_may]. apply reaches_error_iff_may.
Qed.

Lemma bh_unmodeled_iff : forall img lim en inp,
  ~ bh_unmodeled (run img lim en inp)
  <-> omni_corun img lim en inp (covered (img_segments img)).
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [run bh_unmodeled omni_corun img_segments]. apply covered_iff.
Qed.

Lemma bh_unmodeled_may_iff : forall img lim en inp,
  bh_unmodeled (run img lim en inp)
  <-> omni_may img lim en inp (uncovered (img_segments img)).
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp.
  cbn [run bh_unmodeled omni_may img_segments]. apply reaches_unmodeled_iff_may.
Qed.

(** Trace-set equality of two runs is agreement on every prefix-closed
    postcondition; [OmniEquivalence.trace_equiv_iff_omni] restates it
    through [Equivalence.trace_equiv]. *)
Lemma bh_traces_iff : forall img1 lim1 en1 img2 lim2 en2 inp,
  (forall tr, bh_traces (run img1 lim1 en1 inp) tr
              <-> bh_traces (run img2 lim2 en2 inp) tr)
  <-> (forall P, prefix_closed P ->
         (omni_cosafe img1 lim1 en1 inp P <-> omni_cosafe img2 lim2 en2 inp P)).
Proof.
  intros [segs1 pc1 ph1] lim1 [sp1 brk1 mb1 rnd1] [segs2 pc2 ph2] lim2 [sp2 brk2 mb2 rnd2] inp.
  cbn [run bh_traces omni_cosafe]. apply obs_equiv_iff_cosafe.
Qed.
