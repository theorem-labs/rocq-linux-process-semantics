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

(* =========================================================================
   The eight shapes
   ========================================================================= *)

(** A reachable configuration of [forkwait], named by what the proof needs
    of it at that point.  Each shape is a conjunction of facts a segment
    lemma of [ForkwaitSteps] supplies.

    THE PREDICATE IS ON THE CONFIGURATION, not on a position in a trace:
    two different interleavings can arrive at the same shape, and that is
    the point -- nothing here records which schedule got there. *)

(** One entry, no call pending. *)
Definition fw_one_running (P : pconfig) (pc : Z) : Prop :=
  exists e, pcfg_procs P = [(pe_pid e, e)]
            /\ look P (pcfg_root P) = Some e
            /\ m_halted (pe_model e) = None
            /\ ms_svc_pending (pe_ms e) = None
            /\ bv_unsigned (ms_pc_val (pe_ms e)) = pc.

(** One entry with a call pending. *)
Definition fw_one_pending (P : pconfig) (pc : Z) (nr : Z) : Prop :=
  exists e x8, pcfg_procs P = [(pe_pid e, e)]
               /\ look P (pcfg_root P) = Some e
               /\ m_halted (pe_model e) = None
               /\ ms_svc_pending (pe_ms e) = Some x8
               /\ bv_unsigned x8 = nr
               /\ bv_unsigned (ms_pc_val (pe_ms e)) = pc.

(** The root halted on [code], and nothing else in the table. *)
Definition fw_one_halted (P : pconfig) (code : Z) : Prop :=
  exists e c, pcfg_procs P = [(pe_pid e, e)]
              /\ root_view P = Some c
              /\ m_halted (cfg_model c) = Some (Z_to_bv 64 code)
              /\ m_killed (cfg_model c) = None.

(** Two entries: the parent, and a child running or a zombie. *)
Definition fw_two (P : pconfig) : Prop :=
  exists ep ec,
    pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)]
    /\ look P (pcfg_root P) = Some ep
    /\ pe_parent ec = Some (pe_pid ep)
    /\ pe_parent ep = None
    /\ m_halted (pe_model ep) = None.

(** The eight shapes.  The ninth a reader expects -- the injected-errno
    path through [0x1105c] -- is NOT here, and that is a fact about the
    ENVIRONMENT rather than about the program: [Run.injected_table] puts
    [clone] in [FamFd] (Run.v:1383), and [Run.forced_only_cfg] has every
    family off, so [sstep_cfg]'s spurious-refusal premise deletes those
    resolutions.  At [Run.may_fail_cfg] the path IS reachable, becomes a
    ninth shape, and is covered by [ForkwaitSteps.fw_run_fail]: the same
    statement is harder there and still holds. *)
Definition fw_shape (P : pconfig) : Prop :=
  (exists pc, fw_one_running P pc)
  \/ fw_one_pending P 0x11018 220
  \/ fw_two P
  \/ fw_one_pending P 0x1103c 260
  \/ fw_one_pending P 0x1104c 94
  \/ fw_one_pending P 0x11058 94
  \/ fw_one_halted P 7.

(* =========================================================================
   The three remaining premises, against the shapes
   ========================================================================= *)

(** THE LEAF.  A terminal configuration of a shape has the root halted on
    an allowed code.  Only the last shape can be terminal, and showing the
    others cannot is the whole proof: each of the first six has an entry
    with [m_halted = None], and [terminal] says every entry is halted.

    This is the premise where a weaker statement would hide: if [terminal]
    could hold at a shape whose root is NOT halted on 7, the theorem would
    be about a different program.  So each case is discharged by producing
    the running entry and contradicting it, never by a default. *)
Lemma fw_shape_terminal_halted : forall P,
  fw_shape P -> terminal P ->
  exists c code, root_view P = Some c
                 /\ m_halted (cfg_model c) = Some code
                 /\ List.In code [Z_to_bv 64 7]
                 /\ m_killed (cfg_model c) = None.
Proof.
  intros P Hsh Ht.
  (* every shape but the last names a running entry; [terminal] says the
     entry at the head of the table is halted, so those six are absurd.
     [pe_zombie] is unfolded in the assertion itself: it is a definition,
     and [congruence] does not see through one. *)
  assert (Hhead : forall e r, pcfg_procs P = (pe_pid e, e) :: r ->
                              m_halted (pe_model e) <> None).
  { intros e r Hp. unfold terminal in Ht. rewrite Hp in Ht.
    inversion Ht as [|x l Hx Hr]; subst. unfold pe_zombie in Hx. exact Hx. }
  destruct Hsh as [[pc (e & Hp & _ & Hh & _)]
                  |[(e & x8 & Hp & _ & Hh & _)
                  |[(ep & ec & Hp & _ & _ & _ & Hh)
                  |[(e & x8 & Hp & _ & Hh & _)
                  |[(e & x8 & Hp & _ & Hh & _)
                  |[(e & x8 & Hp & _ & Hh & _)
                  |(e & c & Hp & Hrv & Hhc & Hk)]]]]]];
    try (exfalso; exact (Hhead _ _ Hp Hh)).
  - (* the halted shape, the one that can be terminal *)
    exists c, (Z_to_bv 64 7). split; [exact Hrv | split; [exact Hhc |]].
    split; [left; reflexivity | exact Hk].
Qed.

(** THE MEASURE PREMISE, for the shapes where one entry steps and is
    replaced.  [MustExitP.pmeasure_absorb_lt] does the arithmetic; what a
    shape supplies is that the stepping entry's own count falls, which is
    the measure table's business and not this file's. *)
Lemma fw_absorb_decreases : forall P e c',
  look P (pe_pid e) = Some e ->
  (fw_entry (pe_absorb e c') < fw_entry e)%nat ->
  (fw_measure (absorb P e c') < fw_measure P)%nat.
Proof.
  intros P e c' Hl Hlt. unfold fw_measure.
  apply pmeasure_absorb_lt; assumption.
Qed.
