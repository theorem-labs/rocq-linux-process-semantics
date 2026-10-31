(** * Examples.patchclassify_demo.Traces — the COMPLETE trace set of
      each demo program, at every valid entry and on every input

    DEMO FILE (not part of the trusted specification).  [Images] defines
    the demo's six images and [Verdicts] proves that each of them
    terminates with a known exit status wherever it is launched.  This
    file proves the sharper fact the three behavioral obligations
    actually need: what the trace set IS, exactly, rather than what it
    contains.

    ** Why the verdicts are not enough

    [MustExit.must_exit_with] is a claim about how every execution ENDS.
    [MustExit.must_exit_with_realizes] turns it into an existence
    statement — SOME observable trace ends in [State.ExitEv] carrying the
    code — and that is a lower bound on the trace set.  Every obligation
    below needs an UPPER bound as well:

    - [Equivalence.strong_universal_T] needs [Equivalence.trace_equiv],
      set EQUALITY of the two finite-prefix sets.  Two lower bounds do
      not make an equality: knowing that each of two programs emits its
      exit event says nothing about whether one of them also emits
      something the other does not.
    - Refuting [Classifier.agree] means showing a trace of one program is
      NOT a trace of the other, which is a claim about what the second
      one does not do.  [Verdicts]' four error/modeled facts close every
      other route: they make [Classifier.agree]'s second, third and
      fourth conjuncts HOLD of the pair ([O1], [P1]) — both sides fail
      all three antecedents — so the refutation has nowhere to go but the
      trace conjunct.
    - [Classifier.good_input] is [Equivalence.strong_equiv_error_free],
      which is error-freedom of both sides plus
      [Equivalence.trace_equiv].  Both originals here ARE error-free, so
      again only the trace conjunct can fail.

    ** The statement, and why it has the shape it has

    [exits_c_trace_characterization] below: the trace set of one of
    these runs is exactly

        [{ []; [ExitEv code (in_fs inp)] }]

    — an [iff], not an inclusion either way.  Three things about the
    shape are worth reading off it.

    The set is CLOSED UNDER PREFIX and contains the empty trace, because
    [Run.obs_trace] is defined that way ([Run.obs_trace_nil],
    [Run.obs_trace_prefix_closed]); the empty trace is therefore in the
    set of every run whatever, and a characterization that omitted it
    would be false.

    The exit event's payload is [State.in_fs inp] and not a variable:
    [Run.sstep_exit] emits [State.m_fs] of the POST-model, the exit spec
    changes the model only through [State.with_halted]
    ([State.m_fs_with_halted] carries the file system across it), and the
    initial model's file system is the input's
    ([State.m_fs_init_model]).  These programs issue no other syscall, so
    the file system a waiting parent would see is the one the process was
    launched with.  Naming it is what makes the two sides of a
    [Equivalence.trace_equiv] between two such runs literally the same
    set rather than two sets that would have to be related.

    Nothing else is emitted.  The run is four transitions: three
    [Run.sstep_instr]s, which emit [[]] by construction — the two
    [addi]s and the [ecall] INSTRUCTION, which only records the pending
    syscall number and does not advance the pc — and then the one
    [Run.sstep_exit].  That transition's own event list is forced empty
    by [Checks.Examples.exit_dispatch_forced], since the exit spec has
    no [Monad.choose] in it and its outcome triple is therefore unique.

    ** What the premise excludes, which is most programs

    The hypothesis is [Checks.Examples.exits_c] reaching [true] with the
    stack pointer, the writable memory and the read-only backing left as
    VARIABLES — the same premise [Verdicts.must_exit_everywhere_of_exits_c]
    takes, and the same class of programs.  Said the other way round:
    this characterization covers exactly the programs that IGNORE their
    input.  A program that READ its standard input would leave the
    reduction stuck on a variable, so the premise could not be
    discharged for it at all, and its trace set would not be a fixed
    two-element set in the first place — [State.in_fs inp] is the only
    way the input reaches the conclusion here.

    That is the demo's honest limit, and it is where the follow-up the
    demo's README names begins: an input-reading refinement needs a
    SIMULATION argument relating the program's reads to the stream,
    rather than a computation with the input abstracted away.
    [Verdicts]' header makes the same point about the verdicts; it is
    repeated here because this is the file where a reader meets the
    premise while checking the characterization.

    ** How it is proved, and the two hazards avoided

    The engine is [Checks.Examples.exits_c_star_trace]: an induction on
    the fuel of [Checks.Examples.exits_c], run in parallel with an
    inversion of the [Run.star], exactly as
    [Checks.Examples.exits_c_must_exit_at] runs the same induction against
    [MustExit.must_exit_at].  It reaches an upper bound on the accumulated
    trace of any [Run.star], which is the half [MustExit] cannot give.
    It lives in [Checks.Examples] beside that lemma because the checks
    layer needs the same upper bound for
    [Checks.Examples.exits_c_never_dies].

    The lower half is then FREE: [MustExit.must_exit_at_realizes] already
    produces a [Run.star] whose trace ends in the exit event, and the
    upper bound identifies that trace with the singleton.  So no
    execution is ever built by hand here.

    Two reduction hazards are deliberately avoided, and both are real.
    A successor machine state is never reduced INTO a goal: every step
    the proof takes lives inside [Checks.Examples.exits_c]'s own
    [bool] computation, which is why the six instantiations below cost
    milliseconds rather than the minute per image
    [Checks.Examples.exits_c]'s header warns about.  And no successor
    state is ever produced by an [eexists] whose value a later
    [vm_compute] is asked to find: chaining existential holes through
    the step function does not terminate, while the same reduction under
    a hypothesis finishes at once.  The proofs below have no [eexists]
    at all — [Checks.Examples.exit_step_forced] states the one-step fact
    as an equation between the events and lets inversion supply the
    successor. *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit Classifier.
From LinuxProcessSemantics.Examples.patchclassify_demo Require Import
  Images Verdicts.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Two shapes of list equation, once
   ========================================================================= *)

(** A singleton [State.ExitEv] trace determines its code.  Stated as a
    lemma rather than inlined at each use because it is where the
    refutations below actually bite: an [Classifier.agree] that survived
    would have to make [Classifier.verdict_accept] and
    [Classifier.verdict_reject] the same word, which
    [Classifier.verdict_accept_neq_reject] forbids. *)
Lemma exit_singleton_code : forall (c1 c2 : word) (fs1 fs2 : Fs.Fs),
  [ExitEv c1 fs1] = [ExitEv c2 fs2] -> c1 = c2.
Proof. intros c1 c2 fs1 fs2 H. inversion H. reflexivity. Qed.

(** [Run.is_prefix] of a singleton leaves only the two traces the
    characterization names.  [Run.obs_trace] is prefix-closed, so this
    is the step from "the maximal trace is the singleton" to "the trace
    SET is the two-element set". *)
Lemma is_prefix_singleton : forall (A : Type) (x : A) (l : list A),
  is_prefix l [x] -> l = [] \/ l = [x].
Proof.
  intros A x [| y [| z l]] Hp; cbn in Hp.
  - left. reflexivity.
  - right. destruct Hp as [-> _]. reflexivity.
  - destruct Hp as [_ []].
Qed.

(* =========================================================================
   The characterization
   ========================================================================= *)

(** THE lemma this file exists for, stated over the same class of
    programs [Verdicts.must_exit_everywhere_of_exits_c] is stated over:
    those whose [Checks.Examples.exits_c] reaches [true] with the stack
    pointer, the writable memory and the read-only backing left
    abstract.  For such a program the finite-prefix set is the
    two-element set named in this file's header, at EVERY allocation
    budget, from EVERY [Run.ExecEntry] and on EVERY [State.ProcInput] —
    no [Run.valid_entry] and no [Run.valid_input] hypothesis, for the
    same reason the verdicts need none.

    The two directions are proved by different means and it is worth
    seeing which is which.  Left to right is [exits_c_star_trace], the
    genuine upper bound.  Right to left is [Run.obs_trace_nil] for the
    empty trace and [MustExit.must_exit_at_realizes] for the singleton —
    the execution that realizes it is the one [MustExit] already
    produces, identified with the singleton by the upper bound rather
    than constructed again. *)
Lemma exits_c_trace_characterization :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo)
         (code : word) (fuel : nat),
    (forall sp mem rom,
        exits_c segs code fuel (demo_init_state pc sp mem rom) = true) ->
    forall lim en inp t,
      bh_traces (run (mkImage segs pc ph) lim en inp) t
      <-> (t = [] \/ t = [ExitEv code (in_fs inp)]).
Proof.
  intros segs pc ph code fuel Hc lim [sp brk0 mbase rnd] inp t.
  cbn [run bh_traces]. unfold init_config.
  (* the machine half: the premise holds at this run's initial state *)
  assert (Hms : exits_c segs code fuel
                  (init_machine_state segs pc ph sp rnd (in_argv inp)
                     (in_envp inp) (in_uid inp) (in_hwcap inp)) = true).
  { destruct (init_machine_state_abstracts segs pc ph sp rnd (in_argv inp)
                (in_envp inp) (in_uid inp) (in_hwcap inp)) as (mem & rom & Hshape).
    rewrite Hshape. apply Hc. }
  (* the model half, at this run's initial model *)
  pose proof (m_halted_init_model (segments_reserved segs) brk0 mbase sp lim inp)
    as Hh.
  pose proof (init_model_no_lazy (segments_reserved segs) brk0 mbase sp lim inp)
    as Hlazy.
  pose proof (m_fs_init_model (segments_reserved segs) brk0 mbase sp lim inp)
    as Hfs.
  split.
  - (* every observed prefix is one of the two *)
    intros (tr' & c & Hstar & Hp).
    destruct (exits_c_star_trace _ _ _ _ _ _ _ Hh Hlazy Hms Hstar)
      as [-> | ->].
    + left. destruct t; [reflexivity | destruct Hp].
    + rewrite Hfs in Hp. exact (is_prefix_singleton _ _ _ Hp).
  - (* ... and both really are observed *)
    intros [-> | ->]; [apply obs_trace_nil |].
    pose proof (must_exit_everywhere_of_exits_c segs pc ph code fuel Hc lim
                  (mkEntry sp brk0 mbase rnd) inp) as Hme.
    cbn [must_exit_with] in Hme. unfold init_config in Hme.
    destruct (must_exit_at_realizes _ _ _ Hme Hh) as (tr0 & fs & c' & Hstar & _).
    assert (Hshape : tr0 ++ [ExitEv code fs] = [ExitEv code (in_fs inp)]).
    { rewrite <- Hfs.
      destruct (exits_c_star_trace _ _ _ _ _ _ _ Hh Hlazy Hms Hstar)
        as [He | He]; [| exact He].
      exfalso. destruct tr0; discriminate. }
    exists (tr0 ++ [ExitEv code fs]), c'.
    split; [exact Hstar |]. rewrite Hshape. apply is_prefix_refl.
Qed.

(* =========================================================================
   The six programs, one line each
   ========================================================================= *)

(** Each of these instantiates the lemma above at the image's OWN
    [Checks.Examples.exits_c] fact, exactly as [Verdicts]' six verdicts
    do.  Three of the six images share a segment list with another and
    conversion sees through the sharing, so any of these would close a
    sibling's goal; that they do not is discipline and not enforcement,
    per [Images]' header.  Stating each from its own image is what keeps
    the file honest if the two classifiers are ever given different
    code. *)

Theorem O1_traces : forall lim en inp t,
  bh_traces (run O1_image lim en inp) t
  <-> (t = [] \/ t = [ExitEv verdict_reject (in_fs inp)]).
Proof.
  unfold O1_image.
  exact (exits_c_trace_characterization _ _ _ _ 8 O1_exits_c).
Qed.

Theorem O2_traces : forall lim en inp t,
  bh_traces (run O2_image lim en inp) t
  <-> (t = [] \/ t = [ExitEv verdict_accept (in_fs inp)]).
Proof.
  unfold O2_image.
  exact (exits_c_trace_characterization _ _ _ _ 8 O2_exits_c).
Qed.

Theorem P1_traces : forall lim en inp t,
  bh_traces (run P1_image lim en inp) t
  <-> (t = [] \/ t = [ExitEv verdict_accept (in_fs inp)]).
Proof.
  unfold P1_image.
  exact (exits_c_trace_characterization _ _ _ _ 8 P1_exits_c).
Qed.

Theorem P2_traces : forall lim en inp t,
  bh_traces (run P2_image lim en inp) t
  <-> (t = [] \/ t = [ExitEv verdict_accept (in_fs inp)]).
Proof.
  unfold P2_image.
  exact (exits_c_trace_characterization _ _ _ _ 8 P2_exits_c).
Qed.

Theorem C1_traces : forall lim en inp t,
  bh_traces (run C1_image lim en inp) t
  <-> (t = [] \/ t = [ExitEv verdict_reject (in_fs inp)]).
Proof.
  unfold C1_image.
  exact (exits_c_trace_characterization _ _ _ _ 8 C1_exits_c).
Qed.

Theorem C2_traces : forall lim en inp t,
  bh_traces (run C2_image lim en inp) t
  <-> (t = [] \/ t = [ExitEv verdict_reject (in_fs inp)]).
Proof.
  unfold C2_image.
  exact (exits_c_trace_characterization _ _ _ _ 8 C2_exits_c).
Qed.

(* =========================================================================
   The characterization bites
   ========================================================================= *)

(** The one-line consequence every refutation below runs through: a
    program that exits 0 never emits the exit-1 event.  Without a
    statement of this shape the characterization would be a description
    with nothing depending on it — and it is exactly the fact
    [MustExit.must_exit_with_realizes] cannot supply, since an existence
    statement about one program says nothing about a second. *)
Lemma no_exit_one_trace_of_exit_zero :
  forall (X : Image),
    (forall lim en inp t,
        bh_traces (run X lim en inp) t
        <-> (t = [] \/ t = [ExitEv verdict_accept (in_fs inp)])) ->
    forall lim en inp,
      ~ bh_traces (run X lim en inp) [ExitEv verdict_reject (in_fs inp)].
Proof.
  intros X HX lim en inp Ht.
  apply (proj1 (HX lim en inp _)) in Ht.
  destruct Ht as [He | He]; [discriminate |].
  exact (verdict_accept_neq_reject (eq_sym (exit_singleton_code _ _ _ _ He))).
Qed.

(** ... and its mirror, so that no refutation depends on which of the
    two codes the defective image happens to report. *)
Lemma no_exit_zero_trace_of_exit_one :
  forall (X : Image),
    (forall lim en inp t,
        bh_traces (run X lim en inp) t
        <-> (t = [] \/ t = [ExitEv verdict_reject (in_fs inp)])) ->
    forall lim en inp,
      ~ bh_traces (run X lim en inp) [ExitEv verdict_accept (in_fs inp)].
Proof.
  intros X HX lim en inp Ht.
  apply (proj1 (HX lim en inp _)) in Ht.
  destruct Ht as [He | He]; [discriminate |].
  exact (verdict_accept_neq_reject (exit_singleton_code _ _ _ _ He)).
Qed.

(** The positive half: the exit event really is emitted, so the
    characterization is not the trace set of a program that says
    nothing.  [Verdicts.O1_realizes_exit_one] makes the same point from
    [MustExit.must_exit_with_realizes]; this one pins the trace exactly,
    payload included. *)
Example O1_emits_exactly_exit_one : forall lim en inp,
  bh_traces (run O1_image lim en inp) [ExitEv verdict_reject (in_fs inp)].
Proof.
  intros lim en inp. apply (proj2 (O1_traces _ _ _ _)). right. reflexivity.
Qed.

Example P1_emits_exactly_exit_zero : forall lim en inp,
  bh_traces (run P1_image lim en inp) [ExitEv verdict_accept (in_fs inp)].
Proof.
  intros lim en inp. apply (proj2 (P1_traces _ _ _ _)). right. reflexivity.
Qed.

(** And the exclusion, on the demo's own images: the defect's exit-1
    trace is not a trace of its patch.  This is the single fact the
    [Classifier.agree] refutation is built from. *)
Example P1_never_emits_exit_one : forall lim en inp,
  ~ bh_traces (run P1_image lim en inp) [ExitEv verdict_reject (in_fs inp)].
Proof. exact (no_exit_one_trace_of_exit_zero P1_image P1_traces). Qed.

Example O2_never_emits_exit_one : forall lim en inp,
  ~ bh_traces (run O2_image lim en inp) [ExitEv verdict_reject (in_fs inp)].
Proof. exact (no_exit_one_trace_of_exit_zero O2_image O2_traces). Qed.

Example O1_never_emits_exit_zero : forall lim en inp,
  ~ bh_traces (run O1_image lim en inp) [ExitEv verdict_accept (in_fs inp)].
Proof. exact (no_exit_zero_trace_of_exit_one O1_image O1_traces). Qed.
