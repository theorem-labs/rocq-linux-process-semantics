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

(** Two entries, and BOTH are pinned.  An earlier version of this named
    only the parent, and that is the "preserves itself for the wrong
    reason" failure: a step of the CHILD would have landed back in it with
    nothing said about where the child went, so the shape would have been
    preserved while the proof learned nothing.  Every target shape must pin
    both entries, not only the one that stepped.

    The child is in one of three states, the three the run passes through:
    running at a pc, with its [exit_group] pending, or a zombie holding
    status 7.  That disjunction is what makes the two-entry stretch a
    finite set of shapes rather than one shape with a hole in it. *)
Definition fw_child (ec : ProcessEntry) : Prop :=
  (m_halted (pe_model ec) = None
   /\ ms_svc_pending (pe_ms ec) = None
   /\ (bv_unsigned (ms_pc_val (pe_ms ec)) = 0x1101c%Z
       \/ bv_unsigned (ms_pc_val (pe_ms ec)) = 0x11020%Z
       \/ bv_unsigned (ms_pc_val (pe_ms ec)) = 0x11050%Z
       \/ bv_unsigned (ms_pc_val (pe_ms ec)) = 0x11054%Z))
  \/ (exists x8, m_halted (pe_model ec) = None
                 /\ ms_svc_pending (pe_ms ec) = Some x8
                 /\ bv_unsigned x8 = 94%Z
                 /\ bv_unsigned (ms_pc_val (pe_ms ec)) = 0x11058%Z)
  \/ (m_halted (pe_model ec) = Some (Z_to_bv 64 7)
      /\ m_killed (pe_model ec) = None).

(** The parent while two entries are live: on its way to the [wait4], or
    blocked at it. *)
Definition fw_parent (ep : ProcessEntry) : Prop :=
  m_halted (pe_model ep) = None
  /\ ((ms_svc_pending (pe_ms ep) = None
       /\ (0x1101c%Z <= bv_unsigned (ms_pc_val (pe_ms ep)) <= 0x11038%Z)%Z)
      \/ (exists x8, ms_svc_pending (pe_ms ep) = Some x8
                     /\ bv_unsigned x8 = 260%Z
                     /\ bv_unsigned (ms_pc_val (pe_ms ep)) = 0x1103c%Z)).

Definition fw_two (P : pconfig) : Prop :=
  exists ep ec,
    pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)]
    /\ look P (pcfg_root P) = Some ep
    /\ pe_parent ec = Some (pe_pid ep)
    /\ pe_parent ep = None
    /\ fw_parent ep
    /\ fw_child ec.

(** The eight shapes.  The ninth a reader expects -- the injected-errno
    path through [0x1105c] -- is NOT here, and that is a fact about the
    ENVIRONMENT rather than about the program: [Run.injected_table] puts
    [clone] in [FamFd] (Run.v:1383), and [Run.forced_only_cfg] has every
    family off, so [sstep_cfg]'s spurious-refusal premise deletes those
    resolutions.  At [Run.may_fail_cfg] the path IS reachable, becomes a
    ninth shape, and is covered by [ForkwaitSteps.fw_run_fail]: the same
    statement is harder there and still holds. *)
(** THE PROGRAM COUNTERS THE ONE-ENTRY SHAPES ADMIT, read off the
    committed snapshot's own binary as the segments are.

    An earlier [fw_shape] began [exists pc, fw_one_running P pc], which is
    the [fw_two] defect in the one-entry case: a shape satisfied by ANY
    program counter is preserved because it says almost nothing.  Pinning
    the counters is NARROWING, not widening -- the opposite of making a
    case close by weakening what is proved -- and the measure needs them
    anyway, since [fw_absorb_decreases] reads the pc to compute what is
    left.

    As lists rather than as a twenty-way disjunction, so preservation per
    segment is one decidable check: the successor of a member is a member
    or the segment's [ecall]. *)

(** The entry run into the clone, [0x11000] to the [ecall] at [0x11018]. *)
Definition fw_pcs_A : list Z :=
  [0x11000; 0x11004; 0x11008; 0x1100c; 0x11010; 0x11014; 0x11018]%Z.

(** The two branches both processes run, then the child's tail. *)
Definition fw_pcs_child : list Z :=
  [0x1101c; 0x11020; 0x11050; 0x11054; 0x11058]%Z.

(** The parent's prologue and its [wait4]. *)
Definition fw_pcs_parent : list Z :=
  [0x1101c; 0x11020; 0x11024; 0x11028; 0x1102c; 0x11030; 0x11034;
   0x11038; 0x1103c]%Z.

(** The parent's tail after the reap. *)
Definition fw_pcs_reap : list Z :=
  [0x11040; 0x11044; 0x11048; 0x1104c]%Z.

(** Every counter a single live entry of this program can be at. *)
Definition fw_pcs_one : list Z :=
  fw_pcs_A ++ fw_pcs_child ++ fw_pcs_parent ++ fw_pcs_reap.

Definition fw_shape (P : pconfig) : Prop :=
  (exists pc, List.In pc fw_pcs_one /\ fw_one_running P pc)
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
  destruct Hsh as [(pc & _ & e & Hp & _ & Hh & _ & _)
                  |[(e & x8 & Hp & _ & Hh & _)
                  |[(ep & ec & Hp & _ & _ & _ & (Hh & _) & _)
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

(** THE NO-ERROR PREMISE, reduced to one obligation per shape.

    [MustExitP.pstep_error_cases] says an error transition is one of the
    two refusing arms: a released [SError], or the surface guard firing.
    This turns "no shape errors" into exactly two things to rule out at
    each shape, and it is the lemma the inversion layer exists for -- a
    proof that inverted [pstep_at] here would name every constructor and
    would break when [ext] adds two.

    THE SURFACE GUARD IS FREE AT EVERY SHAPE OF THIS PROGRAM.
    [multiproc_allowed] is [true] whenever no call is pending, and
    whenever the pending number is one of 93, 94, 220, 260, 435 -- and
    [forkwait] issues only 220, 260 and 94.  So [pstep_outside] cannot
    fire anywhere in this run, and what is left at each shape is the
    released [SError] alone. *)
Lemma fw_guard_open : forall P c nr,
  (ms_svc_pending (cfg_ms c) = None
   \/ exists x8, ms_svc_pending (cfg_ms c) = Some x8
                 /\ bv_unsigned x8 = nr
                 /\ List.In nr multiproc_sysnos) ->
  multiproc_allowed P c = true.
Proof.
  intros P c nr [Hn | (x8 & Hs & Hv & Hin)]; unfold multiproc_allowed.
  - rewrite Hn. reflexivity.
  - rewrite Hs. rewrite Hv.
    apply orb_true_intro. right.
    apply List.existsb_exists. exists nr.
    split; [exact Hin | apply Z.eqb_refl].
Qed.

(** The three numbers this program issues are on the surface. *)
Lemma fw_sysnos_allowed :
  List.In 220%Z multiproc_sysnos
  /\ List.In 260%Z multiproc_sysnos
  /\ List.In 94%Z multiproc_sysnos.
Proof. cbn. repeat split; tauto. Qed.

(** THE PROGRESS PREMISE, and the one place it is not automatic.

    At seven of the eight shapes progress is a single machine step or a
    single syscall arm, so a step exists because a segment lemma produces
    one.  At the eighth -- the parent blocked at the [wait4] [ecall] with
    the child still running -- THE PARENT HAS NO STEP AT ALL, by design
    (§7.2): a blocked entry is one with no arm, not one with a flag.  So
    progress there is the CHILD's step, and the premise is met by the other
    entry.

    That is why the premise is stated over the system rather than over the
    root: a root-only progress condition would be false at that shape and
    the theorem would be unprovable for a program that blocks. *)
Lemma fw_progress_from_entry : forall segs cfg P p evs r,
  pstep_at segs cfg p P evs r ->
  exists evs' st, pstep_cfg segs cfg P evs' st.
Proof. intros segs cfg P p evs r H. exists evs, r. exists p. exact H. Qed.

(** WHY THE SIX NON-TERMINAL SHAPES ARE NOT [inversion]-AND-DONE.

    [fw_shape_terminal_halted] discharges each of the six by PRODUCING its
    running entry and contradicting [terminal]'s claim that every entry is
    halted.  A default case -- "the remaining shapes cannot be terminal" --
    would look the same and prove less: it would hold even if a shape had
    been written with its halt condition omitted, and the theorem would
    then be about a program that may stop somewhere this one does not.

    The leaf is the premise where a weaker statement hides, because it is
    the only one that says what the answer IS rather than what the run does
    next.  Every other premise is refutable by a wrong step; this one is
    satisfiable by a wrong shape. *)

(* =========================================================================
   fw_reach_cases: every reachable configuration is one of the eight
   ========================================================================= *)

(** THE BASE CASE.  [pinit_config] is [one_proc] over [Run.init_config], so
    the table is a single entry, the root is that entry, and the shape is
    the first: one entry running, at the image's entry point.  Stated over
    an arbitrary [c] because that is what makes it usable at the entry
    point of any program, not just this one. *)
Lemma fw_shape_one_proc : forall c,
  m_halted (cfg_model c) = None ->
  ms_svc_pending (cfg_ms c) = None ->
  (* the pc is now PINNED to the counters the program can be at, so the
     caller supplies it; at the entry point it is [0x11000], the head of
     [fw_pcs_A] *)
  List.In (bv_unsigned (ms_pc_val (cfg_ms c))) fw_pcs_one ->
  fw_shape (one_proc c).
Proof.
  intros c Hh Hs Hin. left.
  exists (bv_unsigned (ms_pc_val (cfg_ms c))).
  split; [exact Hin|].
  exists (one_entry c).
  split; [reflexivity|].
  split; [apply one_proc_entry|].
  split; [exact Hh|].
  split; [exact Hs|].
  reflexivity.
Qed.

(** And the same for a configuration with a call already pending, which is
    what each segment hands the next one. *)
Lemma fw_shape_one_proc_pending : forall c x8 nr pc,
  m_halted (cfg_model c) = None ->
  ms_svc_pending (cfg_ms c) = Some x8 ->
  bv_unsigned x8 = nr ->
  bv_unsigned (ms_pc_val (cfg_ms c)) = pc ->
  fw_one_pending (one_proc c) pc nr.
Proof.
  intros c x8 nr pc Hh Hs Hn Hp.
  exists (one_entry c), x8.
  split; [reflexivity|].
  split; [apply one_proc_entry|].
  split; [exact Hh|].
  split; [exact Hs|].
  split; [exact Hn | exact Hp].
Qed.

(** THE INDUCTIVE STEP, as a hypothesis on one transition.

    [fw_reach_cases] is then an induction over [fw_reach] with the base
    case above and this as the step, so it is stated separately: it is the
    whole of the remaining work, and separating it says exactly what that
    work is rather than burying it in a tactic. *)
Definition fw_shape_preserved (segs : list Segment) (cfg : SpuriousCfg)
    : Prop :=
  forall P evs P', fw_shape P -> pstep_cfg segs cfg P evs (PNext P') ->
                   fw_shape P'.

(** Given it, the characterisation is the induction. *)
Lemma fw_reach_cases : forall segs cfg P0 P,
  fw_shape_preserved segs cfg ->
  fw_shape P0 ->
  fw_reach segs cfg P0 P ->
  fw_shape P.
Proof.
  intros segs cfg P0 P Hpres H0 Hr.
  induction Hr as [|P1 evs P2 Hr IH Hs].
  - exact H0.
  - exact (Hpres P1 evs P2 IH Hs).
Qed.

(** And then the whole composition, with every premise named. *)
Theorem forkwait_halts_of_preserved : forall segs cfg S P0 mu,
  fw_shape_preserved segs cfg ->
  fw_shape P0 ->
  (forall P, fw_shape P -> terminal P ->
     exists c code, root_view P = Some c
                    /\ m_halted (cfg_model c) = Some code
                    /\ List.In code S
                    /\ m_killed (cfg_model c) = None) ->
  (forall P, fw_shape P -> terminalb P = false ->
     exists evs st, pstep_cfg segs cfg P evs st) ->
  (forall P evs, fw_shape P -> ~ pstep_cfg segs cfg P evs PError) ->
  (forall P evs P', fw_shape P -> pstep_cfg segs cfg P evs (PNext P') ->
     (mu P' < mu P)%nat) ->
  must_exit_in_p_at segs cfg S P0.
Proof.
  intros segs cfg S P0 mu Hpres H0 Hleaf Hprog Hnoerr Hdec.
  apply (must_exit_in_p_at_by_measure segs cfg S fw_shape mu).
  - exact (fun P evs P' HI Hs => Hpres P evs P' HI Hs).
  - exact Hleaf.
  - exact Hprog.
  - exact Hnoerr.
  - exact Hdec.
  - exact H0.
Qed.

(* =========================================================================
   Towards fw_shape_preserved
   ========================================================================= *)

(** A one-entry configuration's successor is one-entry, unless the step was
    the clone.  [absorb] replaces the stepping entry and rebuilds the
    shared state; it never adds or drops one, so the table's LENGTH is
    fixed by it. *)
Lemma absorb_procs_length : forall P e c',
  List.length (pcfg_procs (absorb P e c'))
  = List.length (pcfg_procs P).
Proof.
  intros P e c'. unfold absorb. cbn [pcfg_procs].
  apply replace_in_length.
Qed.

(** And a clone's successor has exactly one more entry: [clone_result]
    replaces the parent and appends the child. *)
Lemma clone_result_procs_length : forall P e c' q,
  List.length (pcfg_procs (clone_result P e c' q))
  = S (List.length (pcfg_procs P)).
Proof.
  intros P e c' q. unfold clone_result. cbn [pcfg_procs].
  rewrite List.length_app, replace_in_length. cbn [List.length]. lia.
Qed.

(** THE CLONE SHAPE IS THE ONLY ONE WHERE THE ENTRY COUNT CHANGES, which is
    why it is the only shape whose target is not determined by a program
    counter alone.  These two lemmas are what let the preservation proof
    tell the cases apart by counting, rather than by inspecting the
    successor's table: a step from a one-entry shape either keeps one entry
    (and the target is a one-entry shape at the successor's pc) or makes
    two (and the target is [fw_two]).  Nothing else can happen, because
    [pstep_next_cases] has exactly three producing arms and the reap needs
    a zombie, which a one-entry configuration of this program does not
    have. *)

(** The reap arm's successor has one FEWER entry. *)
Lemma drop_in_procs_length_lt : forall ps p e,
  look_in ps p = Some e ->
  (List.length (drop_in ps p) < List.length ps)%nat.
Proof.
  induction ps as [|kv r IH]; intros p e Hl; cbn in *; [discriminate|].
  destruct (bv_eqb (fst kv) p) eqn:Hb; cbn.
  - lia.
  - pose proof (IH p e Hl). lia.
Qed.

(** A FINDING, recorded here because it is about the RELATION and not
    about this program, and left UNPROVED rather than admitted.

    The natural next lemma is that the entry count decides which arm
    fired:

      same count  -> [pstep_other]      (one entry replaced)
      one more    -> [pstep_clone]      (a child appended)
      one fewer   -> [pstep_wait_reap]  (a zombie dropped)

    It would make the preservation proof a case analysis on three arms
    rather than on eight shapes times three.  The first two hold, by
    [absorb_procs_length] and [clone_result_procs_length] above.  THE
    THIRD DOES NOT FOLLOW FROM THE ARM AS WRITTEN, and the reason is a
    premise the arm is missing.

    [Procs.pstep_wait_reap] requires [look P q = Some ez] and
    [pe_parent ez = Some (pe_pid e)], but NEVER [q <> pe_pid e].  Nothing
    in the arm stops the reaping parent and the reaped child being the
    same entry: that would need [pe_parent e = Some (pe_pid e)], a
    process that is its own parent, which [Procs.pconfig_wf]'s
    parent-link clause excludes -- but [pconfig_wf] is NOT a premise of
    the arm.  So on a malformed configuration the arm can drop the entry
    it is also replacing, and the count argument cannot be completed
    without either that invariant or a new premise.

    THE PATHFINDER IS NOT AFFECTED.  Its configurations are well formed by
    construction: [pinit_config] gives [pconfig_wf]
    ([Procs.pconfig_wf_one_proc]) and no arm breaks it.  The count lemma
    is provable with [pconfig_wf P] as a premise.

    WHICH FIX IS RIGHT IS NOT MINE TO CHOOSE ALONE, because it changes a
    trusted specification.  Adding [q <> pe_pid e] to the arm makes the
    relation self-contained and costs existing uses nothing, since it is
    implied wherever [pconfig_wf] holds.  Threading [pconfig_wf] into the
    lemma instead leaves the relation able to express a self-reap and
    relies on every caller to exclude it.  Everything else in this
    development puts such conditions in the arm -- the surface guard, the
    clone's pid freshness, the reap's own [m_killed] premise -- so the
    first is what I would take, and it is reported before it is made. *)

(** Dropping an entry that survives a replacement at a DIFFERENT key
    shortens the table.  Stated without naming the replacement, so that a
    use can let unification take it from the goal: the reap arm builds its
    replacement inline, and every attempt to name that term picked the
    wrong one. *)
Lemma drop_replace_length_lt : forall ps p q e' ez,
  bv_eqb p q = false ->
  look_in ps q = Some ez ->
  (List.length (drop_in (replace_in ps p e') q) < List.length ps)%nat.
Proof.
  intros ps p q e' ez Hne Hl.
  pose proof (drop_in_procs_length_lt (replace_in ps p e') q ez) as Hlt.
  rewrite look_in_replace_other in Hlt by exact Hne.
  specialize (Hlt Hl). rewrite replace_in_length in Hlt. exact Hlt.
Qed.

(** THE LENGTH DECIDES WHICH ARM FIRED, now that the reap arm carries
    [q <> pe_pid e].  No two producing arms change the table's length the
    same way, so counting the successor is a decision procedure for the
    arm -- which is what makes a preservation proof a case analysis on
    three arms rather than on eight shapes times three.

    The reap case needed the new premise and nothing else: with it,
    [look_in_replace_other] carries the reaped entry's lookup through the
    parent's replacement, and [drop_in_procs_length_lt] then shortens the
    table. *)
Lemma pstep_length_cases : forall segs cfg p P evs P',
  pstep_at segs cfg p P evs (PNext P') ->
  List.length (pcfg_procs P') = List.length (pcfg_procs P)
  \/ List.length (pcfg_procs P') = S (List.length (pcfg_procs P))
  \/ (List.length (pcfg_procs P') < List.length (pcfg_procs P))%nat.
Proof.
  intros segs cfg p P evs P' Hp.
  (* FIVE branches, not three: [pstep_at] has the two error arms as well,
     and a disjunctive pattern must cover every constructor even where the
     conclusion rules most of them out.  Named rather than matched,
     because the reap arm has thirteen premises and an Ltac pattern over
     them is how the first attempt failed. *)
  inversion Hp as
    [ P1 e1 evs1 c1 Hl1 Hs1 Hc1 Hw1 Hm1 Heq1 Heq2 Heq3
    | P2 e2 evs2 c2 q2 Hl2 Hs2 Hc2 Hcp2 Hfr2 Hm2 Heq4 Heq5 Heq6
    | P3 e3 q3 ez3 x83 sa3 st3 eff3 mo3 du3
      Hl3 Hh3 Hsv3 Hwi3 Hwa3 Hlq3 Hne3 Hpar3 Hk3 Hst3 Hrd3 Heff3 Hmat3
      Heq7 Heq8 Heq9
    | P4 e4 evs4 Hl4 Hs4 Hw4 Heq10 Heq11 Heq12
    | P5 e5 Hl5 Hh5 Hm5 Heq13 Heq14 Heq15 ]; subst.
  - left. apply absorb_procs_length.
  - right; left. apply clone_result_procs_length.
  - right; right. cbn [pcfg_procs].
    (* [drop_replace_length_lt] does not mention the replacement entry, so
       unification takes it from the GOAL.  Naming it, and quantifying
       over it and instantiating, both picked the wrong term: the arm
       builds its entry inline and it is not [pe_absorb e3 _]. *)
    apply (drop_replace_length_lt _ _ _ _ ez3).
    + destruct (bv_eqb (pe_pid e3) q3) eqn:Hb; [| reflexivity ].
      apply bv_eqb_true_eq in Hb. congruence.
    + exact Hlq3.
Qed.

(** [absorb] keeps the table's shape at a one-entry configuration: the
    only entry is replaced by the absorbed one, and the root still names
    it.  This is the structural half of preservation for every shape with
    one entry; what the successor's pc is, is the segment lemmas' half. *)
Lemma absorb_one_entry : forall P e c',
  pcfg_procs P = [(pe_pid e, e)] ->
  pcfg_root P = pe_pid e ->
  pcfg_procs (absorb P e c') = [(pe_pid e, pe_absorb e c')]
  /\ pcfg_root (absorb P e c') = pe_pid e
  /\ look (absorb P e c') (pe_pid e) = Some (pe_absorb e c').
Proof.
  intros P e c' Hp Hr.
  unfold absorb, look. cbn [pcfg_procs pcfg_root].
  rewrite Hp. cbn [replace_in fst].
  rewrite bv_eqb_same.
  split; [reflexivity|]. split; [exact Hr|].
  cbn [look_in fst snd]. rewrite bv_eqb_same. reflexivity.
Qed.

(** [pe_absorb] keeps the pid and the parent link, which is what every
    shape's structural clauses are stated over. *)
Lemma pe_absorb_ids : forall e c',
  pe_pid (pe_absorb e c') = pe_pid e
  /\ pe_parent (pe_absorb e c') = pe_parent e.
Proof. intros e c'. split; reflexivity. Qed.

(** And it carries the successor's machine state and halt flag through, so
    a shape's pc and pending-call clauses can be read off [c'] directly. *)
Lemma pe_absorb_state : forall e c',
  pe_ms (pe_absorb e c') = cfg_ms c'
  /\ m_halted (pe_model (pe_absorb e c')) = m_halted (cfg_model c').
Proof. intros e c'. split; reflexivity. Qed.

(** THE CLONE'S STRUCTURAL SHAPE, which is the only case where the target
    is not determined by a program counter alone, because the entry count
    changes.  At a one-entry configuration the successor's table is
    exactly the parent followed by the child, so [fw_two]'s first four
    clauses are read off [clone_result] and only the two state clauses
    ([fw_parent], [fw_child]) remain for the segment lemmas. *)
Lemma clone_result_two : forall P e c' q,
  pcfg_procs P = [(pe_pid e, e)] ->
  pcfg_root P = pe_pid e ->
  pe_parent e = None ->
  pcfg_procs (clone_result P e c' q)
    = [(pe_pid e, pe_absorb e c');
       (q, child_entry e (pe_cfg (pcfg_shared P) e) c' q)]
  /\ pcfg_root (clone_result P e c' q) = pe_pid e
  /\ look (clone_result P e c' q) (pe_pid e) = Some (pe_absorb e c')
  /\ pe_parent (child_entry e (pe_cfg (pcfg_shared P) e) c' q)
     = Some (pe_pid e)
  /\ pe_parent (pe_absorb e c') = None.
Proof.
  intros P e c' q Hp Hr Hpar.
  unfold clone_result, look. cbn [pcfg_procs pcfg_root].
  (* [List.app] is NOT in the [cbn] list: reducing it alongside consumed
     the [bv_eqb] redex the rewrite needs, which is why the previous
     attempt reported no matching subterm. *)
  rewrite Hp. cbn [replace_in fst].
  rewrite bv_eqb_same. cbn [List.app].
  split; [reflexivity|].
  split; [exact Hr|].
  split; [cbn [look_in fst snd]; rewrite bv_eqb_same; reflexivity|].
  split; [reflexivity | exact Hpar].
Qed.

(** The child's pid is the one the clone returned, and its machine state
    has a0 = 0 -- the two facts a consumer reads off the new entry. *)
Lemma child_entry_ids : forall e c c' q,
  pe_pid (child_entry e c c' q) = q
  /\ entry_a0_zero (child_entry e c c' q).
Proof.
  intros e c c' q. split; [reflexivity | apply child_entry_a0_zero].
Qed.

(* =========================================================================
   The state half: successors of a pinned counter
   ========================================================================= *)

(** The counters a single step can move to, from each member of
    [fw_pcs_one].  Read off the committed snapshot's own binary: every
    instruction is 4 bytes, so the successor of a straight-line counter is
    the next one, and the two branches are the only places where it is not.

    [0x1101c] is [bltz] and [0x11020] is [beqz], so each has TWO
    successors, and both are in the list.  That is what makes this a
    membership check rather than a function: the relation does not decide
    which way a branch goes, and the shape does not have to. *)
Definition fw_next_pcs (pc : Z) : list Z :=
  match pc with
  | 0x11000%Z => [0x11004]%Z
  | 0x11004%Z => [0x11008]%Z
  | 0x11008%Z => [0x1100c]%Z
  | 0x1100c%Z => [0x11010]%Z
  | 0x11010%Z => [0x11014]%Z
  | 0x11014%Z => [0x11018]%Z     (* the ecall's own address *)
  | 0x11018%Z => []%Z            (* the clone: its successor is the arm's *)
  | 0x1101c%Z => [0x11020; 0x1105c]%Z   (* bltz: not taken, or taken *)
  | 0x11020%Z => [0x11024; 0x11050]%Z   (* beqz: parent, or child *)
  | 0x11024%Z => [0x11028]%Z
  | 0x11028%Z => [0x1102c]%Z
  | 0x1102c%Z => [0x11030]%Z
  | 0x11030%Z => [0x11034]%Z
  | 0x11034%Z => [0x11038]%Z
  | 0x11038%Z => [0x1103c]%Z
  | 0x1103c%Z => []%Z            (* the wait4: its successor is the reap *)
  | 0x11040%Z => [0x11044]%Z
  | 0x11044%Z => [0x11048]%Z
  | 0x11048%Z => [0x1104c]%Z
  | 0x1104c%Z => []%Z            (* exit_group *)
  | 0x11050%Z => [0x11054]%Z
  | 0x11054%Z => [0x11058]%Z
  | 0x11058%Z => []%Z            (* exit_group *)
  | _ => []%Z
  end.

(** THE DECIDABLE CHECK, and the reason the pc lists were worth taking as
    lists.  Every successor of a member of [fw_pcs_one] is itself a member,
    EXCEPT the three [ecall] addresses, whose successors belong to the
    syscall arms rather than to an instruction step.  One [vm_compute] over
    concrete addresses settles the whole of the straight-line case, where
    twenty hand-written cases would otherwise be.

    [0x1105c] is in the list of successors of [0x1101c] and NOT in
    [fw_pcs_one]: it is the injected-errno path, unreachable at
    [Run.forced_only_cfg] for the environment reason recorded at
    [fw_shape], so the check is stated over the counters the program
    reaches in THAT environment.  At [Run.may_fail_cfg] the list grows by
    the three addresses of that tail. *)
Definition fw_pcs_closed : bool :=
  List.forallb
    (fun pc => List.forallb (fun pc' => List.existsb (Z.eqb pc') fw_pcs_one)
                            (List.filter (fun x => negb (Z.eqb x 0x1105c))
                                         (fw_next_pcs pc)))
    fw_pcs_one.

Lemma fw_pcs_closed_ok : fw_pcs_closed = true.
Proof. vm_compute. reflexivity. Qed.
