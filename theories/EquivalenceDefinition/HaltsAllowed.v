(** * EquivalenceDefinition.HaltsAllowed — one binary halts with an allowed status

    TRUST BOUNDARY: this file is part of the trusted specification.
    Proof files never edit it.  A top-level check that ascribes against
    [SPEC_HALTS_ALLOWED] and its siblings depends on the definitions
    here remaining fixed, exactly as the baseline check depends on
    [Equivalence].

    ** What the statement says

    For ONE binary, every trace the spec admits for it — at every
    [execve] placement the model allows, on every input
    [Run.valid_input] allows, and under the refusal premise the statement is
    issued with — HALTS, through the [exit_group] path, with a status in
    a set the task declares.  It is [MustExit.must_exit_in] quantified
    over the entries and the inputs, and nothing else.

    ** What it excludes, and this is the whole content

    - NON-TERMINATION.  [MustExit.must_exit_in_at] is inductive.  A
      binary with an infinite execution cannot satisfy it, however many
      of its other executions exit.
    - A STUCK EXECUTION.  The progress premise.  A configuration with no
      successor at all would otherwise pass vacuously.
    - THE ERROR TRANSITION, and therefore anything unmodeled
      ([MustExit.must_exit_in_no_error], [MustExit.must_exit_in_modeled]).
      A binary that runs off the edge of the model does not halt with an
      allowed status; it fails to have a meaning here at all.
    - DEATH BY SIGNAL.  [MustExit.must_exit_in_at]'s halted case carries
      [State.m_killed = None], and
      [MustExit.must_exit_in_at_refuted_by_kill] is the refutation.

    THERE IS NO ABORT STANCE IN THIS FILE, and that is a decision rather
    than an omission.  [Equivalence]'s statement families come in two
    cells, one under [Run.valid_input] and one under
    [Run.valid_input_abort], because for a RELATIONAL claim a declared
    abort is a behaviour two binaries may legitimately share.  Here it
    cannot be: a declared abort is a death by signal, which is the exact
    outcome this statement exists to forbid, so an abort-declared cell
    would be a statement no aborting binary could satisfy and every
    non-aborting one already does — the undeclared statement over again,
    with a premise that changes nothing.  A task that wants to allow an
    abort wants a different predicate, not a stance on this one.

    ** How it sits beside the statements that were already here

    [Equivalence.strong_universal_T] is RELATIONAL and COMPARATIVE: it
    says two binaries behave alike, and says nothing about what either
    one does.  A pair of binaries that both loop forever satisfies it.
    This statement is UNARY and ABSOLUTE: it is about one binary and it
    names an outcome.  Neither implies the other, and that is why this
    is a separate family rather than a corollary — carrying an absolute
    termination claim through an equivalence would need the claim on one
    side to start with.

    [Classifier.classifier_total_T] is the closest relative: the same
    [MustExit.must_exit_at] shape, on one binary, with the answer
    quantified as a disjunction over TWO codes
    ([Classifier.verdict_accept] and [Classifier.verdict_reject]) on
    FINITE inputs.  The difference is not only the arity of the code
    set.  A disjunction of two [must_exit_at]s asks each execution tree
    to be uniform — one code for the whole tree — and
    [MustExit.must_exit_in] does not: a binary that exits 0 on one
    resolution of the nondeterminism and 1 on another satisfies
    [halts_allowed_T [0; 1]] and satisfies [classifier_total_T] at
    neither verdict.  That is the right reading for a task that asks
    "does it terminate cleanly" and the wrong one for a task that asks
    "what is the answer", which is why both statements exist.

    ** The allowed set, and the shipped instance

    The set is a [list word] and membership is [In], so a concrete set is
    a closed term the example side can decide by computation
    ([status_allowed] is that decision, [status_allowed_In] its
    soundness).  [AnyExit] is the widest set the model can ever need:
    every status in [0 .. 255], as words.  It is the set a task picks
    when it cares only that the binary terminates cleanly and not what
    it says, and [any_exit_covers_masked_status] is why nothing wider is
    meaningful — the only writer of [State.m_halted] is
    [Sys.Kernel.Exit.exit_spec], which stores
    [bv_and code (Z_to_bv 64 255)], so every status the model can record
    is already a byte.

    The mask is the kernel's own, not this model's invention:
    [SYSCALL_DEFINE1(exit, int, error_code)] calls
    [do_exit((error_code&0xff)<<8)] and
    [SYSCALL_DEFINE1(exit_group, int, error_code)] calls
    [do_group_exit((error_code & 0xff) << 8)], so the seven high bytes
    of the argument are discarded before any status exists (kernel/exit.c).
    [MustExit]'s header carries the wait-side half and the argument that
    [Sys.Kernel.Exit.exit_spec] is the only arm that writes the field. *)

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The three readings of the statement
   ========================================================================= *)

(** THE UNCONFIGURED READING.  Every execution the unfiltered step
    relation admits, at the shipped source budget.  This is what a task
    gets by saying nothing about spurious refusals, and it is the
    STRONGEST of the three: [Run.may_fail_cfg] admits every execution any
    configuration does. *)
Definition halts_allowed_T (S : list word) (img : Image) : Prop :=
  forall en inp,
    valid_entry img en inp ->
    valid_input inp ->
    must_exit_in S img source_alloc_limit en inp.

(** THE CONFIGURED READING, pinned to a spurious-failure configuration
    the way [Equivalence.strong_universal_T_scfg] is.  The reason a task
    wants it is the one [Classifier]'s forced-only section gives,
    restated for this statement: under a
    reading where an [open] may be refused without cause, a binary that
    reads a file does not terminate cleanly on the refused execution —
    it gets an answer it was not written for — so an absolute
    termination claim about it is false for a reason that has nothing to
    do with the binary.  Under [Run.forced_only_cfg] the avoidable
    refusals are gone and what remains is the claim worth making. *)
Definition halts_allowed_T_scfg (cfg : SpuriousCfg) (S : list word)
    (img : Image) : Prop :=
  forall en inp,
    valid_entry img en inp ->
    valid_input inp ->
    must_exit_in_scfg cfg S img source_alloc_limit en inp.

(** THE BUDGET READING.  [Equivalence.SpecScfgBudgets] abstracts the two
    budgets and takes [Equivalence.source_within_budget_scfg] as a
    premise; this mirrors it FOR ONE IMAGE, so there is one budget and
    one premise rather than a pair.

    The premise is the same one and it is there for the same reason: a
    run the allocator refuses for want of budget reaches no exit at all,
    and holding a binary to an absolute termination claim on such an
    input would be holding it to the model's memory ceiling rather
    than to anything it does.  [Equivalence.source_within_budget_scfg]
    is the CONFIGURED form of the premise, which is the weaker one — an
    input refused only along an execution the configuration removes is
    an input this statement still covers.

    There is no [Equivalence.BUDGETS.headroom] obligation to discharge
    here, because headroom is a relation between a source budget and a
    target budget and this statement has one image.  The sealing surface
    below still takes a whole [Equivalence.BUDGETS] and reads
    [lim_source] off it, so that a one-image statement and the two-image
    statement a task states beside it are pinned to the SAME constant
    rather than to two that happen to agree. *)
Definition halts_allowed_T_scfg_budgets (cfg : SpuriousCfg) (lim : Z)
    (S : list word) (img : Image) : Prop :=
  forall en inp,
    valid_entry img en inp ->
    valid_input inp ->
    source_within_budget_scfg cfg lim img en inp ->
    must_exit_in_scfg cfg S img lim en inp.

(** THE BUDGET READING UNDER THE FINER PREMISE.  The same statement with
    [Equivalence.source_within_budget_scfg_only] in place of
    [Equivalence.source_within_budget_scfg]: an input on which a single
    request's charge alone exceeds [lim] ([Run.RefuseOversize]) stays in
    scope, so the binary must still halt with an allowed status after
    that request is refused.  The first-touch and the cumulative
    refusals are still excluded.  With one image there is no agreement
    part to keep under the released premise, so the whole conclusion
    moves to the finer one; it implies the released reading
    ([halts_allowed_T_scfg_budgets_only_subsumes]). *)
Definition halts_allowed_T_scfg_budgets_only (cfg : SpuriousCfg) (lim : Z)
    (S : list word) (img : Image) : Prop :=
  forall en inp,
    valid_entry img en inp ->
    valid_input inp ->
    source_within_budget_scfg_only cfg lim img en inp ->
    must_exit_in_scfg cfg S img lim en inp.

(* =========================================================================
   How the three readings relate
   ========================================================================= *)

(** At [Run.may_fail_cfg] the configured reading is the unconfigured
    one, exactly as [Equivalence.strong_universal_T_scfg] is
    [Equivalence.strong_universal_T] there.  The default a task gets by
    saying nothing about a configuration is therefore not a silent
    weakening. *)
Lemma halts_allowed_T_scfg_may_fail : forall S img,
  halts_allowed_T_scfg may_fail_cfg S img <-> halts_allowed_T S img.
Proof.
  intros S img; split; intros H en inp Hen Hinp.
  - apply must_exit_in_scfg_may_fail. exact (H en inp Hen Hinp).
  - apply must_exit_in_scfg_may_fail. exact (H en inp Hen Hinp).
Qed.

(** The configured reading is MONOTONE downward in the configuration,
    wherever the filter's question is answered: a claim under a bigger
    configuration is a claim under a smaller one.  The premise is
    [MustExit.run_decided], the known gap of [Run.v]'s spurious-failure
    section, at the run. *)
Lemma halts_allowed_T_scfg_mono : forall cfg1 cfg2 S img,
  cfg_le cfg1 cfg2 ->
  (forall en inp, valid_entry img en inp -> valid_input inp ->
                  run_decided cfg1 img source_alloc_limit en inp) ->
  halts_allowed_T_scfg cfg2 S img ->
  halts_allowed_T_scfg cfg1 S img.
Proof.
  intros cfg1 cfg2 S img Hle Hdec H en inp Hen Hinp.
  exact (must_exit_in_scfg_mono _ _ _ _ _ _ _ Hle (Hdec en inp Hen Hinp)
           (H en inp Hen Hinp)).
Qed.

(** The constant-pinned configured statement implies the budget one at
    the same constant, with the premise DROPPED — never the converse.
    This is [Equivalence.strong_universal_T_scfg_budgets_of_scfg]'s
    direction and it holds for the same reason: a statement that needs
    no premise implies the one that takes it. *)
Lemma halts_allowed_T_scfg_budgets_of_scfg : forall cfg S img,
  halts_allowed_T_scfg cfg S img ->
  halts_allowed_T_scfg_budgets cfg source_alloc_limit S img.
Proof.
  intros cfg S img H en inp Hen Hinp _. exact (H en inp Hen Hinp).
Qed.

(** The finer budget reading implies the released one at the same
    budget: the released premise implies the finer one. *)
Lemma halts_allowed_T_scfg_budgets_only_subsumes : forall cfg lim S img,
  halts_allowed_T_scfg_budgets_only cfg lim S img ->
  halts_allowed_T_scfg_budgets cfg lim S img.
Proof.
  intros cfg lim S img H en inp Hen Hinp Hb.
  exact (H en inp Hen Hinp
           (source_within_budget_scfg_only_of_source_within_budget_scfg cfg lim img en inp Hb)).
Qed.

(** It is refuted by an error, or by a reachable death, on a valid pair
    the finer premise admits. *)
Lemma halts_allowed_T_scfg_budgets_only_refuted_by_error : forall cfg lim S img en inp,
  valid_entry img en inp ->
  valid_input inp ->
  source_within_budget_scfg_only cfg lim img en inp ->
  bh_errors (run_scfg cfg img lim en inp) ->
  ~ halts_allowed_T_scfg_budgets_only cfg lim S img.
Proof.
  intros cfg lim S img en inp Hen Hinp Hb Herr H.
  exact (must_exit_in_scfg_refuted_by_error _ _ _ _ _ _ Herr (H en inp Hen Hinp Hb)).
Qed.

Lemma halts_allowed_T_scfg_budgets_only_refuted_by_kill : forall cfg lim S img en inp,
  valid_entry img en inp ->
  valid_input inp ->
  source_within_budget_scfg_only cfg lim img en inp ->
  run_reaches_killed_cfg cfg img lim en inp ->
  ~ halts_allowed_T_scfg_budgets_only cfg lim S img.
Proof.
  intros cfg lim S img en inp Hen Hinp Hb Hk H.
  exact (must_exit_in_scfg_refuted_by_kill _ _ _ _ _ _ Hk (H en inp Hen Hinp Hb)).
Qed.

(** Widening the allowed set weakens every reading.  Only this
    direction: a task that wants the narrower set has to prove it. *)
Lemma halts_allowed_T_mono : forall S1 S2 img,
  (forall code, In code S1 -> In code S2) ->
  halts_allowed_T S1 img ->
  halts_allowed_T S2 img.
Proof.
  intros S1 S2 img Hsub H en inp Hen Hinp.
  exact (must_exit_in_mono _ _ _ _ _ _ Hsub (H en inp Hen Hinp)).
Qed.

Lemma halts_allowed_T_scfg_mono_set : forall cfg S1 S2 img,
  (forall code, In code S1 -> In code S2) ->
  halts_allowed_T_scfg cfg S1 img ->
  halts_allowed_T_scfg cfg S2 img.
Proof.
  intros cfg S1 S2 img Hsub H en inp Hen Hinp.
  exact (must_exit_in_scfg_mono_set _ _ _ _ _ _ _ Hsub (H en inp Hen Hinp)).
Qed.

(** The single-code statement is the singleton set: a binary proved to
    exit with one status halts allowably for every set containing it. *)
Lemma halts_allowed_T_of_must_exit_with : forall S code img,
  (forall en inp, valid_entry img en inp -> valid_input inp ->
                  must_exit_with code img source_alloc_limit en inp) ->
  In code S ->
  halts_allowed_T S img.
Proof.
  intros S code img H Hin en inp Hen Hinp.
  exact (must_exit_with_in _ _ _ _ _ _ (H en inp Hen Hinp) Hin).
Qed.

(* =========================================================================
   What the statement buys, and how it is refuted
   ========================================================================= *)

Lemma halts_allowed_T_no_error : forall S img en inp,
  halts_allowed_T S img ->
  valid_entry img en inp ->
  valid_input inp ->
  ~ bh_errors (run img source_alloc_limit en inp).
Proof.
  intros S img en inp H Hen Hinp.
  exact (must_exit_in_no_error _ _ _ _ _ (H en inp Hen Hinp)).
Qed.

Lemma halts_allowed_T_modeled : forall S img en inp,
  halts_allowed_T S img ->
  valid_entry img en inp ->
  valid_input inp ->
  ~ bh_unmodeled (run img source_alloc_limit en inp).
Proof.
  intros S img en inp H Hen Hinp.
  exact (must_exit_in_modeled _ _ _ _ _ (H en inp Hen Hinp)).
Qed.

(** THE GUARD.  A statement nobody can trip is a statement that says
    nothing, so this is the analogue of
    [MustExit.must_exit_with_realizes]: whatever satisfies
    [halts_allowed_T] really emits an [State.ExitEv], and the status it
    carries is really in [S].  Both halves matter — without the [In]
    conjunct the guard would be tripped by a run that exits with
    anything at all. *)
Lemma halts_allowed_T_realizes : forall S img en inp,
  halts_allowed_T S img ->
  valid_entry img en inp ->
  valid_input inp ->
  exists tr code fs,
    In code S
    /\ bh_traces (run img source_alloc_limit en inp) (tr ++ [ExitEv code fs]).
Proof.
  intros S img en inp H Hen Hinp.
  exact (must_exit_in_realizes _ _ _ _ _ (H en inp Hen Hinp)).
Qed.

(** NEGATIVE, the error route. *)
Lemma halts_allowed_T_refuted_by_error : forall S img en inp,
  valid_entry img en inp ->
  valid_input inp ->
  bh_errors (run img source_alloc_limit en inp) ->
  ~ halts_allowed_T S img.
Proof.
  intros S img en inp Hen Hinp Herr H.
  exact (must_exit_in_refuted_by_error _ _ _ _ _ Herr (H en inp Hen Hinp)).
Qed.

(** NEGATIVE, the SIGNAL route, and it is the refutation that separates
    this statement from error-freedom: a run that aborts errors nowhere
    — the model follows it to the end — so
    [Equivalence.error_free] is satisfied by it and this is not. *)
Lemma halts_allowed_T_refuted_by_kill : forall S img en inp,
  valid_entry img en inp ->
  valid_input inp ->
  run_reaches_killed img source_alloc_limit en inp ->
  ~ halts_allowed_T S img.
Proof.
  intros S img en inp Hen Hinp Hk H.
  exact (must_exit_in_refuted_by_kill _ _ _ _ _ Hk (H en inp Hen Hinp)).
Qed.

(** NEGATIVE, the wrong-status route: a valid triple whose run REACHES a
    configuration halted with a status the set does not contain.  The
    budget is [State.source_alloc_limit] rather than a variable, because
    that is the one [halts_allowed_T] fixes and a variable would only
    have to be equated with it at every use. *)
Lemma halts_allowed_T_refuted_by_wrong_status : forall S img en inp tr c' code,
  valid_entry img en inp ->
  valid_input inp ->
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      star segs (init_config segs pc ph sp brk0 mbase rnd source_alloc_limit inp) tr c'
  end ->
  m_halted (cfg_model c') = Some code ->
  ~ In code S ->
  ~ halts_allowed_T S img.
Proof.
  intros S [segs pc ph] [sp brk0 mbase rnd] inp tr c' code Hen Hinp Hstar Hh Hnin H.
  pose proof (H _ _ Hen Hinp) as Hme. cbn [must_exit_in] in Hme.
  exact (must_exit_in_at_wrong_code _ _ _ _ Hh Hnin
           (must_exit_in_at_star _ _ _ _ _ Hme Hstar)).
Qed.

(* =========================================================================
   The allowed set as a module, and the shipped instance
   ========================================================================= *)

(** Membership decided by computation, for the example side: a concrete
    set is a closed list and a concrete status a closed word, so
    [vm_compute] answers.  [status_allowed_In] is the half a proof
    consumes; [In_status_allowed] is there so the two readings cannot
    drift. *)
Definition status_allowed (S : list word) (code : word) : bool :=
  existsb (fun c => bv_eqb c code) S.

Lemma status_allowed_In : forall S code,
  status_allowed S code = true -> In code S.
Proof.
  intros S code H. unfold status_allowed in H.
  apply existsb_exists in H. destruct H as (c & Hin & Heq).
  apply bv_eqb_eq in Heq. subst c. exact Hin.
Qed.

Lemma In_status_allowed : forall S code,
  In code S -> status_allowed S code = true.
Proof.
  intros S code H. unfold status_allowed. apply existsb_exists.
  exists code. split; [exact H | apply bv_eqb_eq; reflexivity].
Qed.

(** The allowed set a task is stated under, as a module so that it is a
    functor ARGUMENT of the sealing surface, the way
    [Equivalence.SPURIOUS_CFG] and [Equivalence.BUDGETS] are: the
    generated Checker instantiates it beside the image, and the
    ascription fails on a proof made at any other set. *)
Module Type ALLOWED_EXITS.
  Parameter codes : list word.
End ALLOWED_EXITS.

(** Every status in [0 .. 255], as words. *)
Definition byte_codes : list word :=
  map (fun n => Z_to_bv 64 (Z.of_nat n)) (seq 0 256).

Lemma in_byte_codes : forall z,
  (0 <= z < 256)%Z -> In (Z_to_bv 64 z) byte_codes.
Proof.
  intros z Hz. unfold byte_codes. apply in_map_iff.
  exists (Z.to_nat z). split.
  - rewrite Z2Nat.id by lia. reflexivity.
  - apply in_seq. lia.
Qed.

(** The status [Sys.Kernel.Exit.exit_spec] stores is the low byte of the
    argument, and the low byte of anything is a byte. *)
Lemma bv_and_255_range : forall a : word,
  (0 <= bv_unsigned (bv_and a (Z_to_bv 64 255)) < 256)%Z.
Proof.
  intros a.
  rewrite bv_and_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 255) with (Z.ones 8).
  rewrite Z.land_ones by lia.
  change (2 ^ 8)%Z with 256%Z.
  apply Z.mod_pos_bound. lia.
Qed.

(** THE COVERAGE CLAIM.  Every value [State.m_halted] can ever hold is in
    [byte_codes], so [AnyExit] below is not merely a wide set: it is the
    set no [exit_group] status can escape.  The argument that
    [Sys.Kernel.Exit.exit_spec] is the only writer of the field is
    [MustExit]'s header, which also names the dozen other call sites of
    [State.with_halted] and says why each of them preserves this. *)
Lemma any_exit_covers_masked_status : forall a : word,
  In (bv_and a (Z_to_bv 64 255)) byte_codes.
Proof.
  intros a.
  rewrite <- (Z_to_bv_bv_unsigned 64 (bv_and a (Z_to_bv 64 255))).
  apply in_byte_codes, bv_and_255_range.
Qed.

Module AnyExit <: ALLOWED_EXITS.
  Definition codes : list word := byte_codes.
End AnyExit.

Lemma any_exit_covers : forall a : word,
  In (bv_and a (Z_to_bv 64 255)) AnyExit.codes.
Proof. exact any_exit_covers_masked_status. Qed.

(* =========================================================================
   The sealed surfaces
   ========================================================================= *)

(** The unconfigured surface.  ONE image, unlike [Equivalence.SPEC]'s
    two, and an allowed set beside it. *)
Module Type SPEC_HALTS_ALLOWED (Codes : ALLOWED_EXITS) (Target : MemImage).
  Parameter halts_allowed :
    halts_allowed_T Codes.codes
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_HALTS_ALLOWED.

(** The configured surface, with the configuration a functor argument
    the way [Equivalence.SPEC_SCFG] has it. *)
Module Type SPEC_HALTS_ALLOWED_SCFG (Cfg : SPURIOUS_CFG) (Codes : ALLOWED_EXITS)
    (Target : MemImage).
  Parameter halts_allowed :
    halts_allowed_T_scfg Cfg.cfg Codes.codes
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_HALTS_ALLOWED_SCFG.

(** The configured, budget-abstracted surface.  It takes a whole
    [Equivalence.BUDGETS] and reads [lim_source] off it — see
    [halts_allowed_T_scfg_budgets]'s header for why the pair rather than
    a bare [Z]. *)
Module Type SPEC_HALTS_ALLOWED_SCFG_BUDGETS (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Codes : ALLOWED_EXITS) (Target : MemImage).
  Parameter halts_allowed :
    halts_allowed_T_scfg_budgets Cfg.cfg B.lim_source Codes.codes
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_HALTS_ALLOWED_SCFG_BUDGETS.
