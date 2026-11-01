(** * Examples.forkwait.Halts — composing the segments with the bridge

    [MustExitP.must_exit_in_p_at_by_measure] takes four premises, each
    quantified over the reachable set through an invariant the caller
    chooses.  This file chooses it, and the choice is the only interesting
    decision here.

    THE INVARIANT IS REACHABILITY ITSELF, not a disjunction over the
    shapes the run passes through.  A disjunction is the obvious choice for
    a 26-instruction program -- about eight cases, each pinned by the
    program counter, [ms_svc_pending], how many entries are live and whether
    the child is running, a zombie or reaped -- and it would work.  But it
    pays twice: once to write the cases, and again to prove that a step from
    each lands in another, which is exactly the first of the four premises.

    Taking [fw_reach] instead makes that premise FREE: "the invariant
    survives a step" is [fw_reach_step], a constructor.  The work does not
    vanish, it moves: the other three premises then need to know what a
    reachable configuration looks like, and that is [fw_reach_cases] below.
    The difference is that the characterisation is written ONCE, as a lemma
    with a proof, instead of twice -- once as a definition and once as a
    preservation argument.  It is the same trade as the measure's
    over-estimate: say the weakest thing that carries the proof. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit MustExitP.
From LinuxProcessSemantics.Examples.forkwait Require Import Measure.
Import ListNotations.
Open Scope bv_scope.

(** The configurations a run from [P0] can be in. *)
Inductive fw_reach (segs : list Segment) (cfg : SpuriousCfg) (P0 : pconfig)
  : pconfig -> Prop :=
| fw_reach_refl : fw_reach segs cfg P0 P0
| fw_reach_step : forall P evs P',
    fw_reach segs cfg P0 P ->
    pstep_cfg segs cfg P evs (PNext P') ->
    fw_reach segs cfg P0 P'.

(** PREMISE ONE, FREE.  This is the whole reason for choosing reachability
    over a disjunction: the first of the four premises is a constructor. *)
Lemma fw_reach_preserved : forall segs cfg P0 P evs P',
  fw_reach segs cfg P0 P ->
  pstep_cfg segs cfg P evs (PNext P') ->
  fw_reach segs cfg P0 P'.
Proof. intros. eapply fw_reach_step; eassumption. Qed.

(** And the entry point of any such argument. *)
Lemma fw_reach_init : forall segs cfg P0, fw_reach segs cfg P0 P0.
Proof. intros. apply fw_reach_refl. Qed.

(** The shape of the whole composition, with the one premise that is free
    already supplied.  What remains for a concrete program is the other
    three, each of which needs to know what a reachable configuration looks
    like. *)
Theorem halts_of_reachable : forall segs cfg S P0 (mu : pconfig -> nat),
  (forall P, fw_reach segs cfg P0 P -> terminal P ->
     exists c code, root_view P = Some c
                    /\ m_halted (cfg_model c) = Some code
                    /\ List.In code S
                    /\ m_killed (cfg_model c) = None) ->
  (forall P, fw_reach segs cfg P0 P -> terminalb P = false ->
     exists evs st, pstep_cfg segs cfg P evs st) ->
  (forall P evs, fw_reach segs cfg P0 P ->
     ~ pstep_cfg segs cfg P evs PError) ->
  (forall P evs P', fw_reach segs cfg P0 P ->
     pstep_cfg segs cfg P evs (PNext P') -> (mu P' < mu P)%nat) ->
  must_exit_in_p_at segs cfg S P0.
Proof.
  intros segs cfg S P0 mu Hleaf Hprog Hnoerr Hdec.
  apply (must_exit_in_p_at_by_measure segs cfg S (fw_reach segs cfg P0) mu).
  - intros P evs P' HI Hs. eapply fw_reach_step; eassumption.
  - exact Hleaf.
  - exact Hprog.
  - exact Hnoerr.
  - exact Hdec.
  - apply fw_reach_refl.
Qed.

(** WHAT REMAINS, written down rather than claimed, because this repository
    bans [Admitted] and [Axiom] in a proof file and a theorem nobody has
    proved is worth less than the note saying so.

    [halts_of_reachable] reduces [forkwait_halts] to three facts about a
    reachable configuration of [forkwait], all three of which go through one
    characterisation lemma:

      fw_reach_cases :
        forall P, fw_reach forkwait_segs forced_only_cfg (pinit_config …) P ->
          <P is one of the eight shapes>

    The eight are: the straight run to the clone (one entry, no call
    pending); the clone's [ecall] (one entry, 220 pending); the two-entry
    stretch with the child running; the two-entry stretch with the child a
    zombie holding status 7; the parent blocked at the [wait4] [ecall]; the
    parent's run after the reap (one entry again, the child dropped); the
    exit [ecall]; and the halted root.  Each is described by a segment
    lemma of [ForkwaitSteps] and carries exactly the facts the three
    premises need at that point.

    The ninth shape a reader might expect -- the injected-errno path through
    [0x1105c] -- is NOT reachable here, and that is a fact about the
    environment rather than about the program: [Run.injected_table] puts
    [clone] in [FamFd] (Run.v:1383), and at [Run.forced_only_cfg] every
    family is off, so [sstep_cfg]'s spurious-refusal premise removes those
    resolutions.  The program handles the path anyway ([fw_run_fail]), which
    is why the claim also stands at [may_fail_cfg], where it IS reachable
    and becomes a ninth shape.

    The measure premise is then [MustExitP.pmeasure_absorb_lt] against
    [Measure.fw_entry] at each shape, and the no-error premise is
    [MustExitP.pstep_error_cases] at each shape -- the two inversion lemmas
    existing for exactly this. *)
