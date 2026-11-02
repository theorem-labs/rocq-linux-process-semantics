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
(** [getr], [regupd] and [mkst] are [Common.PropExec]'s; [ecall_st] is
    [Common.ShapeNodes]'s.  The segment lemmas' statements are over all
    four. *)
From LinuxProcessSemantics.Common Require Import
  PropExec SeqExec StepTac ShapeNodes ExitSim StoreOk StreamSim.
(** The two system calls whose SPEC this file has to invert: [Exit] for
    [exit_spec], [Fork] for [clone_resolve] and the pid envelope, and
    [Dispatch] for the table lookup that routes a number to an arm.
    [Checks.ProcessCreation] is where the 220 lookup is already done
    ([clone_is_clone_spec]); [Common.ExitSim] is where the 94 one is,
    together with the unique outcome of [exit_spec]. *)
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Dispatch.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ProcessCreation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit MustExitP.
(** [ForkwaitSteps] for [machine_run] and the segment lemmas this file
    consumes; [ForkwaitMemImage] for the committed image's entry point,
    which the start shape is read off.  There is no measure table any
    more: the measure is the remainder's own length, below. *)
From LinuxProcessSemantics.Examples.forkwait Require Import
  ForkwaitMemImage ForkwaitSteps Statement.
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
   The four shapes
   ========================================================================= *)

(** A reachable configuration of [forkwait], named by what the proof needs
    of it at that point.

    THE PREDICATE IS ON THE CONFIGURATION, not on a position in a trace:
    two different interleavings can arrive at the same shape, and that is
    the point -- nothing here records which schedule got there.

    A SHAPE SAYS WHAT AN ENTRY HAS LEFT TO DO, NOT WHERE IT IS.  An
    earlier version of this file described a shape by the PROGRAM COUNTER
    its entry sits at and pinned beside it whichever registers the next
    instruction happened to read.  That does not survive preservation,
    and the reason is the form of the claim rather than a missing fact: a
    counter says where an entry IS, and a segment lemma of
    [ForkwaitSteps] says where a whole RUN goes, so every counter inside
    a segment needed its own register pinning, its own successor case,
    and its own proof that the pinning still holds.  Twenty-three
    counters, each with a different list of registers, and the pinning at
    one of them ([0x1101c], where [bltz] reads a0) decides whether the
    successor is a counter the shape admits at all.

    What a shape carries instead is the REMAINDER of the entry's run:
    "[k] ordinary instruction steps from here reach the state at which
    the program issues this system call with these arguments".
    Preservation across an ordinary step is then ONE lemma for every
    counter -- a [machine_run] of [S k] is a step and a [machine_run] of
    [k] ([machine_run_inv]), and [RiscvSemantics.step] is a function, so
    the successor the relation produces IS the one the remainder named --
    and the case analysis that is left is exactly the three system calls.

    IT IS A NARROWING.  Every state the counter-and-registers shapes
    admitted at an instruction boundary of this program is admitted here;
    the states it drops are the ones that merely sit at such a counter
    with registers the program never has there, which are exactly the
    states the old shapes could not carry forward. *)

(** The bound is what lets a MEASURE read the remainder back off a
    state: [fw_probe] below searches for the pending call with a fixed
    fuel, and without a bound a shape could not say the search
    terminates.  Sixteen, against a largest real remainder of nine. *)
Definition fw_rem (ms : machine_state) (Q : machine_state -> Prop) : Prop :=
  exists k msf, (k <= 16)%nat
                /\ machine_run forkwait_segs k ms = Some msf /\ Q msf.

(** The three calls this program makes, each described by the registers
    the arm that answers it reads, and by nothing else.

    [ms_resv] is [None] in each: a segment lemma is stated over
    [PropExec.mkst], and [ForkwaitSteps.mkst_eta] puts a state into that
    form only when the reservation is clear.  forkwait contains no
    [lr]/[sc], [State.init_machine_state] clears it, and every state this
    file builds preserves it, so the clause is a fact the state really
    has. *)

(** The clone's [ecall] at [0x11018]: [clone(SIGCHLD, 0, ...)].  The
    stack-pointer bound is the parent's, not the call's: the parent's
    prologue pushes a sixteen-byte frame for the status word, and
    [ForkwaitSteps.fw_run_parent] needs the subtraction not to wrap. *)
Definition fw_q_clone (ms : machine_state) : Prop :=
  ms_svc_pending ms = Some 220
  /\ bv_unsigned (ms_pc_val ms) = 0x11018%Z
  /\ ms_gpr ms 0 = 17
  /\ ms_gpr ms 1 = 0
  /\ ms_resv ms = None
  /\ (16 <= bv_unsigned (getr (ms_regs ms) 2))%Z
  /\ store_ok forkwait_segs (ms_mem ms)
       (fw_slot (getr (ms_regs ms) 2)) 4 = true.

(** Either [exit_group(7)]: the child's, the parent's after the reap, and
    the one the injected-errno tail makes.  The counter is NOT pinned,
    and that is what lets one shape carry all three -- the arm reads a0
    and the number, and nothing else. *)
Definition fw_q_exit7 (ms : machine_state) : Prop :=
  ms_svc_pending ms = Some 94
  /\ ms_gpr ms 0 = 7.

(** The parent's [wait4(-1, &status, 0, NULL)] at [0x1103c].  [a1] is the
    stack slot the prologue made, which is why it is named as the stack
    pointer rather than as a value: the reap writes the status there and
    the tail reads it back from [sp]. *)
Definition fw_q_wait4 (ms : machine_state) : Prop :=
  ms_svc_pending ms = Some 260
  /\ bv_unsigned (ms_pc_val ms) = 0x1103c%Z
  /\ ms_gpr ms 0 = 0xffffffffffffffff
  /\ ms_gpr ms 1 = getr (ms_regs ms) 2
  /\ ms_gpr ms 2 = 0
  /\ ms_gpr ms 3 = 0
  /\ ms_resv ms = None
  /\ (bv_unsigned (ms_gpr ms 1) + 4 <= 2 ^ 64)%Z
  /\ store_ok forkwait_segs (ms_mem ms) (ms_gpr ms 1) 4 = true.

(** WHAT A SHAPE SAYS ABOUT THE MODEL, as opposed to the machine.

    [m_halted] is the running clause.  [m_killed] is NOT one:
    [State.m_killed] answers [None] whenever [m_halted] does
    (State.v:3521), so the halt clause already gives it.

    The other two are the no-error premise's, and they are facts this
    program really has rather than conditions on it.  NO LAZY MAPPING:
    [State.init_model] makes none and [forkwait] calls no [mmap], and
    with the list empty [State.materialize_model_accesses_no_lazy]
    makes materialising the identity -- so
    [Run.mi_account_step_no_lazy] turns the accounted step into
    [RiscvSemantics.step], which the segment lemmas prove is
    [MachineOk].  That closes [Run.sstep_cfg_instr_fault], its
    unmodeled twin and [Run.sstep_cfg_syscall_materialization_fault]
    from the state the remainder already carries, with no appeal to the
    statement's budget premise.  NO SHARED FILE: the clone's own gate
    ([Fork.clone_no_shared_file_b]) is what decides whether
    [Fork.clone_resolve] answers [unmodeled], and [State.init_model]
    opens only the three channels, which the gate admits. *)
Definition fw_model_ok (m : Model) : Prop :=
  m_halted m = None
  /\ m_vm_lazy m = []
  /\ clone_no_shared_file_b (m_fds m) = true
  /\ m_tid m = None.

Lemma fw_model_ok_halted : forall m, fw_model_ok m -> m_halted m = None.
Proof. intros m (H & _ & _ & _). exact H. Qed.

(** The three components it reads are the three an instruction step, a
    [clear_shared] and a materialisation all leave alone. *)
Lemma fw_model_ok_frame : forall m m',
  m_proc m' = m_proc m ->
  m_vm_lazy m' = m_vm_lazy m ->
  m_fd m' = m_fd m ->
  fw_model_ok m -> fw_model_ok m'.
Proof.
  intros m m' Hp Hv Hf (Hh & Hl & Hc & Ht).
  split; [unfold m_halted; rewrite Hp; exact Hh|].
  split; [rewrite Hv; exact Hl|].
  split; [unfold m_fds in *; rewrite Hf; exact Hc|].
  unfold m_tid. rewrite Hp. exact Ht.
Qed.

Lemma fw_model_ok_clear_shared : forall m,
  fw_model_ok m -> fw_model_ok (clear_shared m).
Proof. intros m H. apply (fw_model_ok_frame m); try reflexivity; exact H. Qed.

Lemma fw_model_ok_pe_cfg : forall S e,
  fw_model_ok (pe_model e) -> fw_model_ok (cfg_model (pe_cfg S e)).
Proof.
  intros S e H. apply (fw_model_ok_frame (pe_model e));
    try reflexivity; exact H.
Qed.

(** A running entry with a remainder. *)
Definition fw_live (e : ProcessEntry) (Q : machine_state -> Prop) : Prop :=
  fw_model_ok (pe_model e) /\ fw_rem (pe_ms e) Q.

(** One entry, which is the root and has no parent. *)
Definition fw_one (P : pconfig) (Q : machine_state -> Prop) : Prop :=
  exists e, pcfg_procs P = [(pe_pid e, e)]
            /\ pcfg_root P = pe_pid e
            /\ pe_parent e = None
            /\ fw_live e Q.

(** The root halted on [code], and nothing else in the table. *)
Definition fw_one_halted (P : pconfig) (code : Z) : Prop :=
  exists e c, pcfg_procs P = [(pe_pid e, e)]
              /\ root_view P = Some c
              /\ m_halted (cfg_model c) = Some (Z_to_bv 64 code)
              /\ m_killed (cfg_model c) = None.

(** THE CHILD, in the two states the two-entry stretch passes through: on
    its way to [exit_group(7)], or the zombie that call left.  BOTH
    ENTRIES ARE PINNED in [fw_two] below, and that is the point: a shape
    that named only the parent would be preserved by a step of the CHILD
    while saying nothing about where the child went, which is "preserved
    for the wrong reason". *)
Definition fw_child_st (ec : ProcessEntry) : Prop :=
  fw_live ec fw_q_exit7
  \/ (m_halted (pe_model ec) = Some (Z_to_bv 64 7)
      /\ m_killed (pe_model ec) = None).

Definition fw_two (P : pconfig) : Prop :=
  exists ep ec,
    pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)]
    /\ pcfg_root P = pe_pid ep
    /\ bv_eqb (pe_pid ep) (pe_pid ec) = false
    /\ pe_parent ec = Some (pe_pid ep)
    /\ pe_parent ep = None
    /\ fw_live ep fw_q_wait4
    /\ fw_child_st ec.

(** FOUR SHAPES, NOT EIGHT, and the reduction is the remainder's doing:
    every counter inside a straight run is now the same shape as the
    [ecall] it ends at, with a larger [k].

    The shape a reader expects and does not find is the injected-errno
    path through [0x1105c].  It is not missing: that tail also ends at
    [exit_group(7)] ([ForkwaitSteps.fw_run_fail]), so it IS the third
    shape, with [k = 4].  At [Run.forced_only_cfg] the path is
    unreachable -- [Run.injected_table] puts clone in [FamFd]
    (Run.v:1383) and that environment has every family off, so
    [sstep_cfg]'s spurious-refusal premise deletes those resolutions --
    but preservation is a statement about the SHAPES rather than about
    reachability, so the case is discharged rather than excluded, and the
    same proof then stands at [Run.may_fail_cfg]. *)
Definition fw_shape (P : pconfig) : Prop :=
  fw_one P fw_q_clone
  \/ fw_two P
  \/ fw_one P fw_q_exit7
  \/ fw_one_halted P 7.

(* =========================================================================
   The three remaining premises, against the shapes
   ========================================================================= *)

(** THE LEAF.  A terminal configuration of a shape has the root halted on
    an allowed code.  Only the last shape can be terminal, and showing the
    others cannot is the whole proof: each of the first three has a
    RUNNING entry at the head of its table, and [terminal] says every
    entry is halted.

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
  (* every shape but the last names a running entry at the head of the
     table; [terminal] says that entry is halted, so those three are
     absurd.  [pe_zombie] is unfolded in the assertion itself: it is a
     definition, and [congruence] does not see through one. *)
  assert (Hhead : forall e r, pcfg_procs P = (pe_pid e, e) :: r ->
                              m_halted (pe_model e) <> None).
  { intros e r Hp. unfold terminal in Ht. rewrite Hp in Ht.
    inversion Ht as [|x l Hx Hr]; subst. unfold pe_zombie in Hx. exact Hx. }
  destruct Hsh as [(e & Hp & _ & _ & Hh & _)
                  |[(ep & ec & Hp & _ & _ & _ & _ & (Hh & _) & _)
                  |[(e & Hp & _ & _ & Hh & _)
                  |(e & c & Hp & Hrv & Hhc & Hk)]]];
    try (exfalso; exact (Hhead _ _ Hp (fw_model_ok_halted _ Hh))).
  - (* the halted shape, the one that can be terminal *)
    exists c, (Z_to_bv 64 7). split; [exact Hrv | split; [exact Hhc |]].
    split; [left; reflexivity | exact Hk].
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

(** WHY THE THREE NON-TERMINAL SHAPES ARE NOT [inversion]-AND-DONE.

    [fw_shape_terminal_halted] discharges each of the three by PRODUCING
    its running entry and contradicting [terminal]'s claim that every
    entry is halted.  A default case -- "the remaining shapes cannot be
    terminal" -- would look the same and prove less: it would hold even
    if a shape had been written with its halt condition omitted, and the
    theorem would then be about a program that may stop somewhere this
    one does not.

    The leaf is the premise where a weaker statement hides, because it is
    the only one that says what the answer IS rather than what the run does
    next.  Every other premise is refutable by a wrong step; this one is
    satisfiable by a wrong shape. *)

(* =========================================================================
   fw_reach_cases: every reachable configuration is one of the four
   ========================================================================= *)

(** THE BASE CASE.  [pinit_config] is [one_proc] over [Run.init_config],
    so the table is a single entry, the root is that entry, and what a
    caller supplies is the entry's remainder -- at the entry point, the
    seven steps of [ForkwaitSteps.fw_run_A] to the clone's [ecall].
    Stated over an arbitrary [c] and an arbitrary remainder because that
    is what makes it usable at every one-entry shape rather than only at
    the entry point. *)
Lemma fw_shape_one_proc : forall c Q,
  fw_model_ok (cfg_model c) ->
  fw_rem (cfg_ms c) Q ->
  fw_one (one_proc c) Q.
Proof.
  intros c Q Hh Hrem.
  exists (one_entry c).
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact (fw_model_ok_clear_shared _ Hh) | exact Hrem].
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
  rewrite orphan_at_exit_length. apply replace_in_length.
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
    the reaps of [pstep_next_cases] need a zombie, which a one-entry
    configuration of this program does not have, and its two WNOHANG arms
    need a pending WNOHANG [wait4], which this program never issues. *)

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
    ([Procs.pconfig_wf_one_proc]) and every producing arm keeps it
    ([Checks.ProcsWellFormed.pstep_at_preserves_wf]).  The count lemma
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

(** THE LENGTH SORTS THE ARMS INTO THREE KINDS, now that the reap arms
    carry [q <> pe_pid e]: an entry replaced ([pstep_other], and the
    [wait4] gate's WNOHANG zero), a child appended ([pstep_clone]), a
    zombie dropped (the blocking and the WNOHANG reap).  Counting the
    successor therefore decides which kind fired -- which is what makes a
    preservation proof a case analysis on three kinds rather than on eight
    shapes times every arm.

    The reap cases needed the new premise and nothing else: with it,
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
  (* EIGHT branches: [pstep_at] has three error arms as well, and a
     disjunctive pattern must cover every constructor even where the
     conclusion rules most of them out.  Named rather than matched,
     because the reap arms have thirteen premises and more, and an Ltac
     pattern over them is how the first attempt failed. *)
  inversion Hp as
    [ P1 e1 evs1 c1 Hl1 Hs1 Hc1 Hw1 Hm1 Hwo1 Heq1 Heq2 Heq3
    | P2 e2 evs2 c2 q2 Hl2 Hs2 Hc2 Hcp2 Hfr2 Hm2 Heq4 Heq5 Heq6
    | P3 e3 q3 ez3 x83 sa3 st3 eff3 mo3 du3
      Hl3 Hh3 Hsv3 Hwi3 Hwa3 Hlq3 Hne3 Hpar3 Hk3 Hst3 Hrd3 Heff3 Hmat3
      Heq7 Heq8 Heq9
    | P4 e4 evs4 Hl4 Hs4 Hw4 Hwo4
    | P5 e5 Hl5 Hh5 Hm5
    | P6 e6 q6 ez6 x86 sa6 ru6 rb6 st6 eff6 mo6 du6
      Hl6 Hh6 Hsv6 Hwo6 Hna6 Hru6 Hlq6 Hne6 Hpar6 Hk6 Hst6 Hrd6 Hlen6 Heff6 Hmat6
    | P7 e7 x87 sa7 ru7 Hl7 Hh7 Hsv7 Hwo7 Hna7 Hru7 Hz7
    | P8 e8 Hl8 Hh8 Hrf8 ]; subst.
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
  - (* the WNOHANG reap drops a child, as the blocking one does *)
    right; right. unfold wait4_reap_result. cbn [pcfg_procs].
    apply (drop_replace_length_lt _ _ _ _ ez6).
    + destruct (bv_eqb (pe_pid e6) q6) eqn:Hb; [| reflexivity ].
      apply bv_eqb_true_eq in Hb. congruence.
    + exact Hlq6.
  - (* the WNOHANG zero replaces the caller's entry and nothing else *)
    left. unfold wait4_zero_result. apply absorb_procs_length.
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
  rewrite bv_eqb_same, orphan_at_exit_single.
  split; [reflexivity|]. split; [exact Hr|].
  cbn [look_in fst snd]. rewrite bv_eqb_same. reflexivity.
Qed.

(** At a two-entry table whose first entry is parentless, the orphaning
    at the second entry's exit changes nothing: the only other entry is
    nobody's child. *)
Lemma fw_orphan_two_child : forall m p ep x,
  pe_parent ep = None ->
  orphan_at_exit m p [(pe_pid ep, ep); (p, x)] = [(pe_pid ep, ep); (p, x)].
Proof.
  intros m p ep x Hpar. unfold orphan_at_exit.
  destruct (m_halted m); [|reflexivity].
  unfold orphan_children, orphan_one. cbn [List.map fst snd].
  rewrite Hpar, bv_eqb_same. cbv beta iota. rewrite andb_false_r. reflexivity.
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
   The state half: what one step does to an entry's remainder
   ========================================================================= *)

(** THE COUNTER CLOSURE IS GONE, and so is the per-counter register
    pinning it needed.  An earlier version of this file carried the
    successor counters of each of the twenty-three instruction
    boundaries as a table [fw_next_pcs], checked by [vm_compute] that
    the table closes over the counters the shapes admit, and then had to
    exclude the one edge that check could not see -- the [bltz] at
    [0x1101c] to the errno tail -- by a register fact the shapes had to
    be widened to carry.

    The remainder shapes make all of it unnecessary: no counter is
    named, the branch is not a case, and the errno tail is the same
    shape as the other two exits rather than an edge to exclude.  What
    takes its place is [machine_run_inv] below and the fact that
    [RiscvSemantics.step] is a function.

    The determinism boundaries ([fw_det_at], [fw_clone_step],
    [fw_exit_step]) went with it: they were named for the route through
    [MustExitP.mepa_det_step], which preservation does not take. *)

(** THE THREE PER-STEP OBLIGATIONS ARE GONE, deliberately.  An earlier
    version of this file named [fw_owes_other], [fw_owes_clone] and
    [fw_owes_reap], and assembled them into the statement.  They were
    true statements, but once the route changed to consuming whole
    deterministic stretches they stopped being on the proof path, and a
    stated-but-unused definition beside a real proof invites a reader to
    think it is used.  What the per-step route would have cost is
    recorded in the design, not here. *)
(* =========================================================================
   An interface mismatch, and the way through it
   ========================================================================= *)

(** THE THREE ARM OBLIGATIONS ABOVE CANNOT BE DISCHARGED FROM THE SEGMENT
    LEMMAS AS THEY STAND, and the reason is a shape mismatch rather than a
    missing fact.  It is worth stating precisely, because the obvious
    reading -- "connect each counter to its successor through the segment
    lemmas" -- does not typecheck.

    [fw_owes_other] is about ONE transition of [pstep_at], whose
    instruction arm is one [Run.mi_account_step].  The segment lemmas are
    about [ForkwaitSteps.machine_run segs k ms], a run of [k] steps:
    [fw_run_A] is seven, [fw_run_parent] nine.  To use a segment lemma for
    a single step one must DECOMPOSE a [machine_run], and the segment file
    exports no decomposition: [mrun_step] builds a run FROM a step, and
    the per-instruction fetch and decode facts live in the generated
    [forkwait_code], which this file does not import.

    So the per-step obligations would need either a [machine_run]
    inversion lemma -- "a run of [S k] steps from [ms] is a step to some
    [ms'] and a run of [k] from it" -- or the generated per-instruction
    lemmas in scope here.

    THE BETTER ROUTE DOES NOT NEED EITHER, and it is the one
    [MustExitP.mepa_det_step] was proved for.  A straight-line stretch of
    this program is DETERMINISTIC: one live entry, no branch whose
    direction is open, so the successor of each configuration is unique.
    [mepa_det_step] consumes such a stretch WHOLE -- it asks for the
    successor, not for an invariant at every intermediate state -- so a
    segment lemma is applied exactly as it is stated, at the [k] it has.
    The measure argument is then needed only for the two-entry stretch,
    where the successor really is not unique, which is what the note
    beside [mepa_det_step] says it is for.

    That makes the shape invariant unnecessary for the straight-line
    parts, and [fw_shape] earns its keep only across the clone and the
    reap.  It is a change of route within this file: no shape is widened,
    no premise is added to [forkwait_halts], and nothing in [Procs.v]
    moves.  The three obligations above stay as the record of what the
    per-step route would have cost. *)

(* =========================================================================
   The run, assembled
   ========================================================================= *)

(** THE DETERMINISTIC-STRETCH ROUTE IS GONE.  An earlier version of this
    file carried the run as three stretches and two steps -- the entry
    run and the parent's tail whole, through [MustExitP.det_run], with
    the measure only across the two-entry stretch -- and named
    [fw_done], [fw_halts_at_done], [fw_det_link] and
    [forkwait_halts_of_stretches] for it.

    The remainder shapes made the split unnecessary: the measure now
    falls at EVERY step, the straight-line parts included, so
    [MustExitP.must_exit_in_p_at_by_measure] carries the whole run and
    a second route beside it would be stated and unused.  What the
    stretch route would have cost is recorded in the design, not
    here. *)

(* =========================================================================
   Discharging the four facts
   ========================================================================= *)

(** FACT ONE: the clone's successor is a [fw_two] shape.

    The structural half is [clone_result_two]: four of the six clauses
    come from the shape of [clone_result] alone.  What is left is the
    two remainders -- the parent's nine steps to its [wait4]
    ([ForkwaitSteps.fw_run_parent]) and the child's five to its
    [exit_group] ([ForkwaitSteps.fw_run_child]) -- and both are supplied
    by the caller, because what they need of the clone (the pid it
    returned, and that the child's a0 is zero) comes from the clone ARM,
    which this file reasons about through [Procs], not from a segment
    lemma.

    The two pids differ because the arm required the child's to be FREE:
    [look P q = None] against the parent's own entry. *)
(** The child's model is the parent's with a fresh [State.ProcState]
    that keeps the halt flag, so all three clauses come through. *)
Lemma fw_model_ok_child : forall e c c' q,
  fw_model_ok (pe_model e) ->
  fw_model_ok (pe_model (child_entry e c c' q)).
Proof.
  intros e c c' q (Hh & Hl & Hc & Ht).
  split; [exact Hh|]. split; [exact Hl|].
  split; [exact Hc | reflexivity].
Qed.

Lemma fw_clone_target : forall P e c' q,
  pcfg_procs P = [(pe_pid e, e)] ->
  pcfg_root P = pe_pid e ->
  pe_parent e = None ->
  look P q = None ->
  (* the parent, after the clone, is running and has its wait4 ahead *)
  fw_model_ok (cfg_model c') ->
  fw_rem (cfg_ms c') fw_q_wait4 ->
  (* the child is running -- its model is the parent's pre-clone one --
     and has its exit_group ahead *)
  fw_model_ok (pe_model e) ->
  fw_rem (pe_ms (child_entry e (pe_cfg (pcfg_shared P) e) c' q)) fw_q_exit7 ->
  fw_two (clone_result P e c' q).
Proof.
  intros P e c' q Hp Hr Hpar Hfree Hh Hpw Hhe Hcw.
  destruct (clone_result_two P e c' q Hp Hr Hpar)
    as (Hprocs & Hroot & Hlook & Hcpar & Hppar).
  assert (Hne : bv_eqb (pe_pid e) q = false).
  { destruct (bv_eqb (pe_pid e) q) eqn:Hb; [|reflexivity].
    apply bv_eqb_true_eq in Hb. rewrite <- Hb in Hfree.
    unfold look in Hfree. rewrite Hp in Hfree.
    cbn [look_in fst snd] in Hfree. rewrite bv_eqb_same in Hfree.
    discriminate. }
  exists (pe_absorb e c'),
         (child_entry e (pe_cfg (pcfg_shared P) e) c' q).
  split; [exact Hprocs|].
  split; [exact Hroot|].
  split; [exact Hne|].
  split; [exact Hcpar|].
  split; [exact Hppar|].
  split.
  - split; [exact (fw_model_ok_clear_shared _ Hh) | exact Hpw].
  - left. split; [exact (fw_model_ok_child e _ c' q Hhe) | exact Hcw].
Qed.

(** FACT TWO: the reap's successor is a one-entry shape at [0x11040].

    The zombie leaves the table, so what is left is the parent alone, at
    the counter [advance_past_svc] reaches from the [wait4] [ecall] at
    [0x1103c].  That counter heads [fw_pcs_reap], so the membership the
    pinned shape needs is immediate.

    The table clause is the interesting one: [drop_in] of the reaped
    child from a two-entry table whose other entry is the parent leaves
    exactly the parent, and that needs the two pids to differ -- which is
    the premise the reap arm now carries, and the reason it was added. *)
Lemma fw_reap_target_table : forall ep ec ep' q,
  bv_eqb (pe_pid ep) q = false ->
  pe_pid ec = q ->
  drop_in (replace_in [(pe_pid ep, ep); (pe_pid ec, ec)] (pe_pid ep) ep') q
  = [(pe_pid ep, ep')].
Proof.
  intros ep ec ep' q Hne Hq.
  cbn [replace_in fst]. rewrite bv_eqb_same.
  cbn [drop_in fst]. rewrite Hne.
  cbn [drop_in fst]. rewrite Hq, bv_eqb_same. reflexivity.
Qed.

(** And the shape itself: the parent alone, with the four steps of
    [ForkwaitSteps.fw_run_reap_at] left to its own [exit_group]. *)
Lemma fw_reap_target : forall P ep',
  pcfg_procs P = [(pe_pid ep', ep')] ->
  pcfg_root P = pe_pid ep' ->
  pe_parent ep' = None ->
  fw_model_ok (pe_model ep') ->
  fw_rem (pe_ms ep') fw_q_exit7 ->
  fw_shape P.
Proof.
  intros P ep' Hp Hr Hpar Hh Hrem. right; right; left.
  exists ep'.
  split; [exact Hp|]. split; [exact Hr|]. split; [exact Hpar|].
  split; [exact Hh | exact Hrem].
Qed.

(* =========================================================================
   The instantiation
   ========================================================================= *)

(** [Statement.forkwait_halts] is [pholts_within_budget] over the
    committed image at the shipped budget with allowed exits [[7]].
    Unfolding it gives, for every [execve] draw and every valid input, a
    [must_exit_in_p_at] at [pinit_config] -- and [pinit_config] is
    [one_proc] over [Run.init_config], which [forkwait_halts_of_stretches]
    takes as its [P0].

    So the statement reduces to the five hypotheses of that theorem at
    [segs := forkwait_segs] and [cfg := forced_only_cfg], and this lemma
    is that reduction: everything above the segment lemmas is now
    discharged, and what a caller must still supply is exactly the list
    below. *)
Lemma forkwait_halts_reduces :
  forall (lim : Z) (segs : list Segment) (pc : N) (ph : PhdrInfo),
  (forall sp brk0 mbase rnd inp,
     valid_entry (mkImage segs pc ph) (Run.mkEntry sp brk0 mbase rnd) inp ->
     valid_input inp ->
     ~ run_scfg_budget_refused forced_only_cfg (mkImage segs pc ph) lim
         (Run.mkEntry sp brk0 mbase rnd) inp ->
     must_exit_in_p_at segs forced_only_cfg [Z_to_bv 64 7]
       (pinit_config segs pc ph sp brk0 mbase rnd lim inp)) ->
  pholts_within_budget lim [Z_to_bv 64 7] (mkImage segs pc ph).
Proof.
  intros lim segs pc ph H en inp Hve Hvi Hb.
  destruct en as [sp brk0 mbase rnd].
  unfold must_exit_in_p.
  exact (H sp brk0 mbase rnd inp Hve Hvi Hb).
Qed.

(** WHAT IS LEFT, after this reduction, and it is now a short list of
    facts about the PROGRAM rather than about the relation:

      1. [det_run forkwait_segs forced_only_cfg P0 Pclone] -- the entry
         run, from [ForkwaitSteps.fw_run_A] through
         [MustExitP.pstep_entry_of_account] and [det_trans], with
         [Run.mi_account_step_no_lazy] discharging the model side at each
         step and [State.init_model]'s empty [m_vm_lazy] discharging its
         premise.
      2. [fw_shape Pclone] -- immediate from [fw_shape_one_proc], since
         [Pclone] is one entry whose remainder is the clone's [ecall].
      3. the leaf, progress, no-error and measure premises at the
         [fw_two] shapes -- the first is [fw_shape_terminal_halted],
         proved; the measure at the two shape-changing steps is
         [fw_measure_clone] and [fw_measure_reap], proved; progress and
         no-error reduce through [fw_progress_from_entry] and
         [pstep_error_cases] with [fw_guard_open].
      4. the tail [det_run] to the final exit, from
         [ForkwaitSteps.fw_run_reap] the same way as (1).

    Each of (1) and (4) is one segment lemma plus the lifting layer; (2)
    is proved; (3) is proved except for the per-shape case analysis that
    consumes the segment lemmas for the child's and the parent's runs.

    [forkwait_halts] is NOT proved, and this file asserts nothing that it
    has not proved: there is no [Admitted] and no [Axiom] here, and the
    remaining obligations are this comment rather than a stated-but-unused
    definition, for the reason the per-step obligations were deleted. *)

(** ITEM (2): the shape at the clone's [ecall].

    [Pclone] is one entry whose remainder is EMPTY -- the call is
    already pending -- so [fw_rem] holds at [k = 0] and the first
    disjunct of [fw_shape] applies directly. *)
Lemma fw_shape_at_clone : forall c,
  fw_model_ok (cfg_model c) ->
  fw_q_clone (cfg_ms c) ->
  fw_shape (one_proc c).
Proof.
  intros c Hh Hq. left. apply fw_shape_one_proc; [exact Hh|].
  exists 0%nat, (cfg_ms c).
  split; [lia|]. split; [reflexivity | exact Hq].
Qed.


(** ITEM (3): the no-error premise at the shapes.

    [MustExitP.pstep_error_cases] splits an error transition into the
    three refusing arms: a released [SError], the surface guard firing,
    or the [wait4] gate's refusal.  The guard is impossible everywhere in
    this program -- [fw_guard_open] with [fw_sysnos_allowed], since the
    only numbers it issues are 220, 260 and 94 -- and so is the refusal:
    its gate needs a pending 260, and the one 260 this program issues has
    the blocking shape, which the refusal excludes ([fw_not_owned_of_rem],
    [Procs.wait4_refused_intercept]).  What a shape has to rule out is the
    released [SError] alone; [fw_no_error] below does that, shape by
    shape. *)

(** And the guard really is open at every entry of this program, because
    the only system calls it issues are on the multi-process surface.
    [fw_sysnos_allowed] is the membership; this applies it. *)
Lemma fw_guard_open_at : forall P c nr,
  (ms_svc_pending (cfg_ms c) = None
   \/ (exists x8, ms_svc_pending (cfg_ms c) = Some x8
                  /\ bv_unsigned x8 = nr
                  /\ (nr = 220%Z \/ nr = 260%Z \/ nr = 94%Z))) ->
  multiproc_allowed P c = true.
Proof.
  intros P c nr [Hn | (x8 & Hs & Hv & Hnr)].
  - apply (fw_guard_open P c nr). left. exact Hn.
  - apply (fw_guard_open P c nr). right. exists x8.
    split; [exact Hs|]. split; [exact Hv|].
    destruct Hnr as [-> | [-> | ->]]; cbn; tauto.
Qed.

(** THE TWO-ENTRY CASE ANALYSIS, enumerated.

    At a [fw_two] shape the live entries are the parent and the child,
    and which of them has an arm is decided by the shape, not searched
    for:

      child running          both have an arm
      child at its ecall     both: the child's exit_group, the parent's
                             next instruction
      child a zombie, parent not yet at wait4   both
      child a zombie, parent AT wait4           the parent reaps
      child running, parent AT wait4            ONLY THE CHILD, because a
                                                blocked parent has no arm

    The last row is 7.2 paying for itself again, and the progress fact
    for it is [fw_progress_from_entry], already proved: the premise is
    met by the child's step.  It is not reproved here.

    What every row needs first is that the entry that did NOT step is
    unchanged, which is the pair of frame lemmas below. *)

(** The other entry's RECORD survives, from the table lemmas -- unless the
    step ended the stepping entry and the other is its child, whose parent
    the exit clears ([Procs.orphan_at_exit]). *)
Lemma fw_two_other_record : forall P e c' q eq,
  bv_eqb (pe_pid e) q = false ->
  look P q = Some eq ->
  (m_halted (cfg_model c') = None \/ pe_parent eq <> Some (pe_pid e)) ->
  look (absorb P e c') q = Some eq.
Proof.
  intros P e c' q eq Hne Hl Hcase.
  rewrite look_absorb_other; [exact Hl | exact Hne |].
  rewrite Hl. exact Hcase.
Qed.

(** And its VIEW survives, provided the step left the shared file system
    and I/O alone -- which the two arms this program steps with do, since
    [with_halted] and [with_children] rebuild the model around the same
    [m_fsys] and [m_io].  That is [view_frame_absorb]'s hypothesis and
    the reason it is a hypothesis: a general version would be false. *)
Lemma fw_two_other_view : forall P e c' q eq,
  look (absorb P e c') q = Some eq ->
  m_fsys (cfg_model c') = sh_fsys (pcfg_shared P) ->
  m_io (cfg_model c') = sh_io (pcfg_shared P) ->
  pe_cfg (pcfg_shared (absorb P e c')) eq = pe_cfg (pcfg_shared P) eq.
Proof.
  intros P e c' q eq Hl Hfs Hio.
  exact (view_frame_absorb P e c' q eq Hl Hfs Hio).
Qed.

(** An instruction step leaves both alone, which is what makes the two
    frame lemmas usable at every row but the two syscall ones:
    [Run.mi_account_step_model_frame] fixes every model component, so the
    hypotheses of [fw_two_other_view] are discharged by it rather than
    supplied. *)
Lemma fw_instr_frames_shared : forall segs ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') ->
  m_fsys model' = m_fsys model /\ m_io model' = m_io model.
Proof.
  intros segs ms model ms' model' Hm.
  pose proof (mi_account_step_model_frame segs ms model ms' model' Hm)
    as (_ & _ & _ & Hio & Hfs & _).
  split; [exact Hfs | exact Hio].
Qed.

(** THE INVERSION, which is what was missing all along.

    [machine_run] is a [Fixpoint] on [k], so a run of [S k] steps is a
    step and a run of [k], and the proof is [simpl] plus destructing the
    step.  It is the converse of [ForkwaitSteps.mrun_step] and it is
    three lines.

    It belongs here rather than beside [mrun_step] only because that is
    where it was needed; moving it is a follow-up, not a prerequisite. *)
Lemma machine_run_inv : forall segs k ms ms'',
  machine_run segs (S k) ms = Some ms'' ->
  exists ms', ms_svc_pending ms = None
              /\ RiscvSemantics.step segs ms = MachineOk ms'
              /\ machine_run segs k ms' = Some ms''.
Proof.
  intros segs k ms ms'' H. simpl in H.
  destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate|].
  destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
    try discriminate.
  exists ms'. split; [reflexivity | split; [reflexivity | exact H]].
Qed.

(* =========================================================================
   What a remainder does under one step
   ========================================================================= *)

(** Each of the three calls is pending at the state its remainder ends
    at, which is what makes "the remainder is empty" and "a call is
    pending" the same case. *)
Definition fw_q_pending (Q : machine_state -> Prop) : Prop :=
  forall ms, Q ms -> ms_svc_pending ms <> None.

Lemma fw_q_clone_pending : fw_q_pending fw_q_clone.
Proof. intros ms (H & _). rewrite H. discriminate. Qed.

Lemma fw_q_exit7_pending : fw_q_pending fw_q_exit7.
Proof. intros ms (H & _). rewrite H. discriminate. Qed.

Lemma fw_q_wait4_pending : fw_q_pending fw_q_wait4.
Proof. intros ms (H & _). rewrite H. discriminate. Qed.

(** A call IS pending exactly when the remainder has run out, and then
    the shape's own description of the call holds of the state itself. *)
Lemma fw_rem_now : forall ms Q,
  fw_rem ms Q -> ms_svc_pending ms <> None -> Q ms.
Proof.
  intros ms Q (k & msf & Hk & Hrun & HQ) Hs.
  destruct k as [|k]; cbn [machine_run] in Hrun.
  - injection Hrun as <-. exact HQ.
  - destruct (ms_svc_pending ms) as [x|] eqn:E;
      [discriminate Hrun | congruence].
Qed.

(** AND THE WHOLE OF PRESERVATION FOR AN ORDINARY STEP.  With no call
    pending the remainder has a step left, [machine_run_inv] names it,
    and [RiscvSemantics.step] is a FUNCTION -- so the state the relation
    stepped to is the one the remainder already named, and what is left
    of the run is the remainder of the successor.  One lemma, for every
    instruction boundary of the program. *)
Lemma fw_rem_step : forall ms Q ms1,
  fw_q_pending Q ->
  fw_rem ms Q ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step forkwait_segs ms = MachineOk ms1 ->
  fw_rem ms1 Q.
Proof.
  intros ms Q ms1 HQp (k & msf & Hk & Hrun & HQ) Hs Hstep.
  destruct k as [|k].
  - cbn [machine_run] in Hrun. injection Hrun as <-.
    exfalso. exact (HQp _ HQ Hs).
  - destruct (machine_run_inv _ _ _ _ Hrun) as (ms' & _ & Hs' & Hr').
    rewrite Hstep in Hs'. injection Hs' as <-.
    exists k, msf. split; [lia|]. split; [exact Hr' | exact HQ].
Qed.

(* =========================================================================
   Which entry stepped
   ========================================================================= *)

(** In a one-entry table the entry a step names is the only one there. *)
Lemma fw_look_one : forall P e p e0,
  pcfg_procs P = [(pe_pid e, e)] ->
  look P p = Some e0 ->
  e0 = e /\ p = pe_pid e.
Proof.
  intros P e p e0 Hp Hl. unfold look in Hl. rewrite Hp in Hl.
  cbn [look_in fst snd] in Hl.
  destruct (bv_eqb (pe_pid e) p) eqn:Hb; [|discriminate].
  apply bv_eqb_true_eq in Hb. injection Hl as <-.
  split; [reflexivity | symmetry; exact Hb].
Qed.

(** And in the two-entry table it is one of the two. *)
Lemma fw_look_two : forall P ep ec p e0,
  pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)] ->
  look P p = Some e0 ->
  (e0 = ep /\ p = pe_pid ep) \/ (e0 = ec /\ p = pe_pid ec).
Proof.
  intros P ep ec p e0 Hp Hl. unfold look in Hl. rewrite Hp in Hl.
  cbn [look_in fst snd] in Hl.
  destruct (bv_eqb (pe_pid ep) p) eqn:Hb.
  - apply bv_eqb_true_eq in Hb. injection Hl as <-.
    left. split; [reflexivity | symmetry; exact Hb].
  - destruct (bv_eqb (pe_pid ec) p) eqn:Hb2; [|discriminate].
    apply bv_eqb_true_eq in Hb2. injection Hl as <-.
    right. split; [reflexivity | symmetry; exact Hb2].
Qed.

(** The one-entry table finds its own entry. *)
Lemma fw_look_one_self : forall P e,
  pcfg_procs P = [(pe_pid e, e)] -> look P (pe_pid e) = Some e.
Proof.
  intros P e Hp. unfold look. rewrite Hp.
  cbn [look_in fst snd]. rewrite bv_eqb_same. reflexivity.
Qed.

(** The two entries of the two-entry table are each found at their own
    pid, which is what the frame lemmas are stated over. *)
Lemma fw_look_two_parent : forall P ep ec,
  pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)] ->
  look P (pe_pid ep) = Some ep.
Proof.
  intros P ep ec Hp. unfold look. rewrite Hp.
  cbn [look_in fst snd]. rewrite bv_eqb_same. reflexivity.
Qed.

Lemma fw_look_two_child : forall P ep ec,
  pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)] ->
  bv_eqb (pe_pid ep) (pe_pid ec) = false ->
  look P (pe_pid ec) = Some ec.
Proof.
  intros P ep ec Hp Hne. unfold look. rewrite Hp.
  cbn [look_in fst snd]. rewrite Hne, bv_eqb_same. reflexivity.
Qed.

(* =========================================================================
   Which arm of the released step fired
   ========================================================================= *)

(** With no call pending only the instruction arm of [Run.sstep_cfg] can
    produce a successor: the four syscall arms all require
    [ms_svc_pending ms = Some x8]. *)
Lemma fw_sstep_instr_inv : forall segs cfg ms model evs c',
  ms_svc_pending ms = None ->
  sstep_cfg segs cfg (mkCfg ms model) evs (SNext c') ->
  exists ms' model',
    mi_account_step segs ms model = MachineOk (ms', model')
    /\ c' = mkCfg ms' model'.
Proof.
  intros segs cfg ms model evs c' Hs H.
  inversion H; subst; try congruence.
  eexists _, _. split; [eassumption | reflexivity].
Qed.

(** The two facts about [State.with_halted] the exit arms turn on. *)
Lemma fw_m_halted_with_halted : forall code m,
  m_halted (with_halted code m) = Some code.
Proof. reflexivity. Qed.

Lemma fw_m_killed_with_halted : forall code m,
  m_killed (with_halted code m) = None.
Proof. reflexivity. Qed.

(** [exit_group]'s post-model, from [Common.ExitSim]'s characterisation
    of the only outcome [Exit.exit_spec] admits. *)
Lemma fw_exit_post : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 94%Z ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  model' = with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model.
Proof.
  intros segs ms x8 model eff model' evs H94 Hspec.
  assert (Hno : is_exit_no (in_sysno (sys_input segs ms x8)))
    by (right; rewrite in_sysno_sys_input; exact H94).
  destruct (exit_dispatch_ok_inv _ _ _ _ _ Hno Hspec) as (_ & Hm & _).
  rewrite in_arg0_sys_input in Hm. exact Hm.
Qed.

(** AND THE ARM IT FORCES.  At a pending 94 the released step has only
    one successor: the terminal one.  The ordinary syscall arm is
    excluded because it requires the post-model to be RUNNING and
    [exit_spec] halts it; the killed arm because [with_halted] clears
    [procst_killed], so the post-model is halted but not killed. *)
Lemma fw_sstep_exit_inv : forall segs cfg ms model evs c' x8,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 94%Z ->
  sstep_cfg segs cfg (mkCfg ms model) evs (SNext c') ->
  c' = mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model).
Proof.
  intros segs cfg ms model evs c' x8 Hs H94 H.
  assert (Hx : forall y, ms_svc_pending ms = Some y -> y = x8)
    by (intros y Hy; rewrite Hs in Hy; injection Hy; auto).
  assert (Hnone : ms_svc_pending ms <> None) by (rewrite Hs; discriminate).
  clear Hs.
  inversion H; subst;
    try (exfalso; apply Hnone; assumption);
    match goal with
    | [ Hsv : ms_svc_pending ms = Some ?y,
        Hsp : syscall_spec (sys_input ?sg ms ?y) ?mm (Ok ?ef ?m1 ?ev) |- _ ] =>
        let Hy := fresh "Hy" in
        pose proof (Hx _ Hsv) as Hy; subst y;
        pose proof (fw_exit_post sg ms x8 mm ef m1 ev H94 Hsp) as Hm1
    end.
  - (* the ordinary syscall arm: its post-model would have to be running *)
    exfalso.
    match goal with
    | [ Hr : m_halted ?m1 = None |- _ ] =>
        rewrite Hm1 in Hr; rewrite fw_m_halted_with_halted in Hr; discriminate
    end.
  - (* the exit arm, the one that fires *)
    rewrite Hm1. reflexivity.
  - (* the killed arm: [with_halted] leaves nothing killed *)
    exfalso.
    match goal with
    | [ Hk : m_killed ?m1 = Some _ |- _ ] =>
        rewrite Hm1 in Hk; rewrite fw_m_killed_with_halted in Hk; discriminate
    end.
Qed.

(** [Fork.clone_resolve]'s TWO outcomes, read off the monad rather than
    taken from a checker.  [Checks.ProcessCreation] already proves that
    the resolution either declines with an errno or sets
    [State.m_has_children]; what the parent's own next run needs is more
    than that -- the pid ENVELOPE, because
    [ForkwaitSteps.fw_run_parent] reads a0 at the [bltz] and the [beqz]
    -- so the alternative is taken apart here.

    Neither outcome writes memory and neither halts: the clone's effect
    is a return value and, on the pid side, [State.with_children]. *)
Lemma fw_clone_resolve_inv : forall i m eff m' evs,
  clone_resolve i m (Ok eff m' evs) ->
  evs = []
  /\ eff_writes eff = [] /\ eff_zeros eff = []
  /\ eff_unmaps eff = [] /\ eff_copies eff = []
  /\ m_halted m' = m_halted m
  /\ (fw_model_ok m -> fw_model_ok m')
  /\ ( ret_in_errnos clone_errnos (eff_ret eff) = true
       \/ ( (0 < bv_unsigned (eff_ret eff))%Z
            /\ (bv_unsigned (eff_ret eff) < PID_MAX_ENVELOPE)%Z ) ).
Proof.
  intros i m eff m' evs H.
  unfold clone_resolve, bind in H. cbv beta iota in H.
  destruct H as (x & m1 & evs1 & evs2 & Hg & Hk & Hevs).
  unfold get_model in Hg. injection Hg as Hx Hm1 He1. subst x m1 evs1.
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg2.
  - unfold unmodeled in Hk. discriminate.
  - destruct Hk as [Herr | Hpid].
    + (* the declining alternative: an errno from [Fork.clone_errnos] *)
      unfold bind in Herr. cbv beta iota in Herr.
      destruct Herr as (e & m2 & evsA & evsB & He & Her & HevsE).
      unfold errno_from, choose in He.
      destruct He as (e0 & Hin & He0).
      injection He0 as Hee Hm2 HeA. subst e m2 evsA.
      unfold err_ret, ret_only, pure in Her.
      injection Her as Hef Hm' HeB. subst eff m' evsB.
      cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
      split; [subst evs2 evs; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [intros Hok; exact Hok|].
      left. unfold ret_in_errnos. apply List.existsb_exists.
      exists e0. split; [exact Hin | apply bv_eqb_same].
    + (* the admitting alternative: a pid inside the envelope *)
      unfold bind in Hpid. cbv beta iota in Hpid.
      destruct Hpid as (p & m2 & evsA & evsB & Hc & Hrest & HevsP).
      unfold choose in Hc.
      destruct Hc as (p0 & Hok & Hc0).
      injection Hc0 as Hpp Hm2 HeA. subst p m2 evsA.
      unfold bind in Hrest. cbv beta iota in Hrest.
      destruct Hrest as (u & m3 & evsC & evsD & Hmod & Hret & HevsQ).
      unfold modify in Hmod. injection Hmod as Hu Hm3 HeC. subst u m3 evsC.
      unfold ret_only, pure in Hret.
      injection Hret as Hef Hm' HeD. subst eff m' evsD.
      cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
      split; [subst evsB evs2 evs; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [intros (Hh & Hl & Hc & Ht);
              split; [exact Hh|]; split; [exact Hl|];
              split; [exact Hc | exact Ht]|].
      unfold clone_pid_ok_b in Hok.
      apply andb_true_iff in Hok as [Hok _].
      apply andb_true_iff in Hok as [Hlo Hhi].
      right. split; [apply Z.ltb_lt; exact Hlo | apply Z.ltb_lt; exact Hhi].
Qed.

(** And the same at the dispatcher: 220 routes to [Fork.clone_spec], and
    the flag word this program passes is [SIGCHLD], the one word
    [Fork.clone_fork_flags_b] admits. *)
Lemma fw_clone_post : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 220%Z ->
  ms_gpr ms 0 = 17 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = []
  /\ eff_writes eff = [] /\ eff_zeros eff = []
  /\ eff_unmaps eff = [] /\ eff_copies eff = []
  /\ m_halted model' = m_halted model
  /\ (fw_model_ok model -> fw_model_ok model')
  /\ ( ret_in_errnos clone_errnos (eff_ret eff) = true
       \/ ( (0 < bv_unsigned (eff_ret eff))%Z
            /\ (bv_unsigned (eff_ret eff) < PID_MAX_ENVELOPE)%Z ) ).
Proof.
  intros segs ms x8 model eff model' evs H220 Ha0 Hspec.
  assert (Hno : bv_unsigned (in_sysno (sys_input segs ms x8)) = 220%Z)
    by (rewrite in_sysno_sys_input; exact H220).
  apply (proj1 (clone_is_clone_spec _ _ _ Hno)) in Hspec.
  rewrite in_arg0_sys_input, Ha0 in Hspec.
  unfold clone_spec in Hspec.
  replace (clone_fork_flags_b 17) with true in Hspec
    by (vm_compute; reflexivity).
  exact (fw_clone_resolve_inv _ _ _ _ _ Hspec).
Qed.

(* =========================================================================
   Which arm of the SYSTEM's step fired, at the three states a shape has
   ========================================================================= *)

(** NO CALL PENDING: an ordinary step of the entry named, and the clone
    and reap arms cannot fire because both need one.  What the caller
    gets is the MACHINE step, [Run.mi_account_step_projects] having
    dropped the accounting, which is what a segment lemma speaks. *)
Lemma fw_entry_instr_step : forall segs cfg p P evs P' e,
  look P p = Some e ->
  ms_svc_pending (pe_ms e) = None ->
  pstep_at segs cfg p P evs (PNext P') ->
  exists ms' model',
    RiscvSemantics.step segs (pe_ms e) = MachineOk ms'
    /\ m_halted model' = m_halted (pe_model e)
    /\ (fw_model_ok (pe_model e) -> fw_model_ok model')
    /\ P' = absorb P e (mkCfg ms' model').
Proof.
  intros segs cfg p P evs P' e Hl Hs Hp.
  inversion Hp; subst;
    match goal with
    | [ Hl0 : look P (pe_pid ?e0) = Some ?e0 |- _ ] =>
        let Heq := fresh "Heq" in
        assert (Heq : e0 = e)
          by (rewrite Hl0 in Hl; injection Hl as Hl; exact Hl);
        subst e0
    end.
  - (* pstep_other: the instruction arm is the only released one left *)
    match goal with
    | [ Hss : sstep_cfg segs cfg _ evs (SNext ?c') |- _ ] =>
        destruct (fw_sstep_instr_inv segs cfg (pe_ms e)
                    (cfg_model (pe_cfg (pcfg_shared P) e)) evs c' Hs Hss)
          as (ms' & model' & Hacc & Hc')
    end.
    destruct (mi_account_step_model_frame _ _ _ _ _ Hacc)
      as (Hfd & _ & Hlz & _ & _ & Hproc & _).
    exists ms', model'.
    split; [exact (mi_account_step_projects _ _ _ _ _ Hacc)|].
    split; [unfold m_halted; rewrite Hproc; reflexivity|].
    split.
    + intros Hok. apply (fw_model_ok_frame (pe_model e));
        [exact Hproc | exact Hlz | exact Hfd | exact Hok].
    + rewrite Hc'. reflexivity.
  - (* pstep_clone: a successful clone needs a pending call *)
    exfalso.
    match goal with
    | [ Hcs : clone_success_b _ ?c' = true |- _ ] =>
        rewrite (clone_success_b_instr (pe_cfg (pcfg_shared P) e) c' Hs) in Hcs;
        discriminate
    end.
  - (* pstep_wait_reap: so does a reap *)
    exfalso. congruence.
  - (* pstep_wait_nohang_reap: and the gate's WNOHANG reap *)
    exfalso. congruence.
  - (* pstep_wait_nohang_zero: and its WNOHANG zero *)
    exfalso. congruence.
Qed.

(** A PENDING 94: the exit arm, and only it.  The clone arm needs
    [Procs.clone_sysno] and the reap arm needs 260, so both are decided
    by the number alone. *)
Lemma fw_entry_exit_step : forall segs cfg p P evs P' e x8,
  look P p = Some e ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 94%Z ->
  pstep_at segs cfg p P evs (PNext P') ->
  P' = absorb P e
         (mkCfg (pe_ms e)
            (with_halted (bv_and (ms_gpr (pe_ms e) 0) (Z_to_bv 64 255))
               (cfg_model (pe_cfg (pcfg_shared P) e)))).
Proof.
  intros segs cfg p P evs P' e x8 Hl Hs H94 Hp.
  inversion Hp; subst;
    match goal with
    | [ Hl0 : look P (pe_pid ?e0) = Some ?e0 |- _ ] =>
        let Heq := fresh "Heq" in
        assert (Heq : e0 = e)
          by (rewrite Hl0 in Hl; injection Hl as Hl; exact Hl);
        subst e0
    end.
  - (* pstep_other *)
    match goal with
    | [ Hss : sstep_cfg segs cfg _ evs (SNext ?c') |- _ ] =>
        rewrite (fw_sstep_exit_inv segs cfg (pe_ms e)
                   (cfg_model (pe_cfg (pcfg_shared P) e)) evs c' x8 Hs H94 Hss)
    end.
    reflexivity.
  - (* pstep_clone: 94 is not a clone number *)
    exfalso.
    match goal with
    | [ Hcs : clone_success_b _ _ = true |- _ ] =>
        unfold clone_success_b in Hcs; cbn [cfg_ms pe_cfg] in Hcs;
        rewrite Hs, H94 in Hcs; cbn in Hcs; discriminate
    end.
  - (* pstep_wait_reap: nor a wait4 one *)
    exfalso.
    match goal with
    | [ Hwi : wait4_intercept_b _ = true |- _ ] =>
        unfold wait4_intercept_b in Hwi; cbn [cfg_ms pe_cfg] in Hwi;
        rewrite Hs, H94 in Hwi; cbn in Hwi; discriminate
    end.
  - (* pstep_wait_nohang_reap: the [wait4] gate needs 260 *)
    exfalso.
    match goal with
    | [ Hwo : wait4_owned_b _ _ = true |- _ ] =>
        rewrite (wait4_owned_not_260 _ _ x8 Hs) in Hwo;
          [discriminate Hwo | rewrite H94; discriminate]
    end.
  - (* pstep_wait_nohang_zero: likewise *)
    exfalso.
    match goal with
    | [ Hwo : wait4_owned_b _ _ = true |- _ ] =>
        rewrite (wait4_owned_not_260 _ _ x8 Hs) in Hwo;
          [discriminate Hwo | rewrite H94; discriminate]
    end.
Qed.

(** The guard the reap arm is behind, and which the other two arms at
    this state are behind the negation of. *)
Lemma fw_wait4_intercept_true : forall S e x8 a,
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 260%Z ->
  wait4_blocking_args (pe_ms e) = Some a ->
  wait4_intercept_b (pe_cfg S e) = true.
Proof.
  intros S e x8 a Hs H260 Hwa.
  unfold wait4_intercept_b. cbn [cfg_ms pe_cfg].
  rewrite Hs, H260, Hwa. reflexivity.
Qed.

(** A PENDING 260 WITH THE BLOCKING ARGUMENT SHAPE: the reap arm, and
    only it.  [Procs.pstep_other] and [Procs.pstep_error] both require
    the intercept guard to be OFF -- that exclusion is what lets the
    parent sleep instead of erroring (Procs.v, the note on the error
    transition) -- the clone arm is decided by the number, and the
    [wait4] gate's two WNOHANG arms by the option word, which is 0 here.

    So this is the one state where a shape has exactly one successor
    and no released step of its own. *)
Lemma fw_entry_reap_step : forall segs cfg p P evs P' e x8 a,
  look P p = Some e ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 260%Z ->
  wait4_blocking_args (pe_ms e) = Some a ->
  pstep_at segs cfg p P evs (PNext P') ->
  exists q ez status model'' dumped,
    look P q = Some ez
    /\ q <> pe_pid e
    /\ pe_parent ez = Some (pe_pid e)
    /\ m_killed (pe_model ez) = None
    /\ pe_status dumped ez = Some status
    /\ materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
         (syscall_effect_accesses
            (mkEffect q [(a, Z_to_le_bytes 4 (bv_unsigned status))] []))
       = Some model''
    /\ P' = mkPCfg
              (drop_in
                 (replace_in (pcfg_procs P) (pe_pid e)
                    (mkEntry (pe_pid e) (pe_parent e)
                       (advance_past_svc
                          (apply_effect (pe_ms e)
                             (mkEffect q
                                [(a, Z_to_le_bytes 4 (bv_unsigned status))] [])))
                       (clear_shared model'') (pe_ofd e) (pe_nsctx e)))
                 q)
              (pcfg_root P)
              (shared_absorb (pcfg_shared P) (mkCfg (pe_ms e) model'')).
Proof.
  intros segs cfg p P evs P' e x8 a Hl Hs H260 Hwa Hp.
  inversion Hp; subst;
    match goal with
    | [ Hl0 : look P (pe_pid ?e0) = Some ?e0 |- _ ] =>
        let Heq := fresh "Heq" in
        assert (Heq : e0 = e)
          by (rewrite Hl0 in Hl; injection Hl as Hl; exact Hl);
        subst e0
    end.
  - (* pstep_other is behind the negated guard *)
    exfalso.
    match goal with
    | [ Hwi : wait4_intercept_b _ = false |- _ ] =>
        rewrite (fw_wait4_intercept_true (pcfg_shared P) e x8 a Hs H260 Hwa)
          in Hwi; discriminate
    end.
  - (* pstep_clone: 260 is not a clone number *)
    exfalso.
    match goal with
    | [ Hcs : clone_success_b _ _ = true |- _ ] =>
        unfold clone_success_b in Hcs; cbn [cfg_ms pe_cfg] in Hcs;
        rewrite Hs, H260 in Hcs; cbn in Hcs; discriminate
    end.
  - (* pstep_wait_reap, the arm that fires *)
    match goal with
    | [ Hwa0 : wait4_blocking_args (pe_ms e) = Some ?sa |- _ ] =>
        assert (Hsa : sa = a)
          by (rewrite Hwa0 in Hwa; injection Hwa as Hwa; exact Hwa);
        subst sa
    end.
    do 5 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|].
    split; [eassumption | reflexivity].
  - (* pstep_wait_nohang_reap: the option word is 0, not WNOHANG *)
    exfalso.
    match goal with
    | [ Hna : wait4_nohang_args (pe_ms e) = Some _ |- _ ] =>
        rewrite (wait4_blocking_not_nohang _ _ Hwa) in Hna; discriminate Hna
    end.
  - (* pstep_wait_nohang_zero: likewise *)
    exfalso.
    match goal with
    | [ Hna : wait4_nohang_args (pe_ms e) = Some _ |- _ ] =>
        rewrite (wait4_blocking_not_nohang _ _ Hwa) in Hna; discriminate Hna
    end.
Qed.

(** A model that is not halted is not killed either: [State.m_killed]
    reads the halt field through the kill flag (State.v:3521). *)
Lemma fw_killed_none_of_halted : forall m,
  m_halted m = None -> m_killed m = None.
Proof.
  intros m H. unfold m_killed. unfold m_halted in H.
  destruct (procst_killed (m_proc m)); [exact H | reflexivity].
Qed.

(** Materialising a syscall's accesses charges pages; it does not touch
    [State.ProcState], so the halt flag comes through. *)
Lemma fw_halted_materialize : forall m acc m',
  materialize_model_accesses m acc = Some m' -> m_halted m' = m_halted m.
Proof.
  intros m acc m' H.
  destruct (materialize_model_accesses_frame _ _ _ H)
    as (_ & _ & _ & _ & _ & Hproc & _).
  unfold m_halted. rewrite Hproc. reflexivity.
Qed.

(** a0 after a syscall is the effect's return: [Run.apply_effect] writes
    it with [set_reg _ 10] and [Run.advance_past_svc] touches only the
    program counter and the pending slot. *)
Lemma fw_a0_after_effect : forall ms eff,
  ms_gpr (advance_past_svc (apply_effect ms eff)) 0 = eff_ret eff.
Proof. intros ms eff. exact (ms_gpr_set_reg_a0 ms (eff_ret eff)). Qed.

(** A SYSCALL WHOSE SPEC LEAVES THE PROCESS RUNNING has exactly one
    released arm.  Stated with the non-halting fact as a HYPOTHESIS so
    that the clone and any later call can share it: the two terminal
    arms of [Run.sstep_cfg] both read the post-model, and a spec that
    never writes the halt flag closes both. *)
Lemma fw_sstep_running_syscall_inv : forall segs cfg ms model evs c' x8,
  ms_svc_pending ms = Some x8 ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
                     m_halted m' = None) ->
  sstep_cfg segs cfg (mkCfg ms model) evs (SNext c') ->
  exists eff model' model'' evs0,
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs0)
    /\ m_halted model' = None
    /\ materialize_model_accesses model' (syscall_effect_accesses eff)
       = Some model''
    /\ c' = mkCfg (advance_past_svc (apply_effect ms eff)) model''.
Proof.
  intros segs cfg ms model evs c' x8 Hs Hrun H.
  assert (Hx : forall y, ms_svc_pending ms = Some y -> y = x8)
    by (intros y Hy; rewrite Hs in Hy; injection Hy; auto).
  assert (Hnone : ms_svc_pending ms <> None) by (rewrite Hs; discriminate).
  clear Hs.
  inversion H; subst;
    try (exfalso; apply Hnone; assumption);
    match goal with
    | [ Hsv : ms_svc_pending ms = Some ?y |- _ ] =>
        let Hy := fresh "Hy" in pose proof (Hx _ Hsv) as Hy; subst y
    end.
  - (* the ordinary syscall arm, the one that fires *)
    do 4 eexists.
    split; [eassumption|]. split; [eassumption|].
    split; [eassumption | reflexivity].
  - (* the exit arm: the spec would have had to halt the model *)
    exfalso.
    match goal with
    | [ Hsp : syscall_spec _ _ (Ok _ ?m1 _), Hhc : m_halted ?m1 = Some _ |- _ ] =>
        rewrite (Hrun _ _ _ Hsp) in Hhc; discriminate
    end.
  - (* the killed arm: nor kill it *)
    exfalso.
    match goal with
    | [ Hsp : syscall_spec _ _ (Ok _ ?m1 _), Hk : m_killed ?m1 = Some _ |- _ ] =>
        rewrite (fw_killed_none_of_halted _ (Hrun _ _ _ Hsp)) in Hk; discriminate
    end.
Qed.

(** A PENDING 220 WITH SIGCHLD IN a0: the clone, which either declined
    with one of [Fork.clone_errnos] -- and then the caller carries on
    alone, down the errno tail -- or created the child.  Which of the
    two is decided by [Procs.clone_success_b], the same reading of a0
    the relation itself uses, so the two cases cannot drift. *)
(** Materialising preserves the three clauses for the same reason an
    instruction step does: it rebuilds neither the descriptor table nor
    [State.ProcState]. *)
Lemma fw_model_ok_materialize : forall m acc m',
  materialize_model_accesses m acc = Some m' ->
  fw_model_ok m -> fw_model_ok m'.
Proof.
  intros m acc m' Hm Hok.
  destruct (materialize_model_accesses_frame _ _ _ Hm)
    as (Hfd & _ & Hlz & _ & _ & Hproc & _).
  apply (fw_model_ok_frame m); assumption.
Qed.

(** The two readings of a clone's answer agree on the answers this
    program's clone can give ([fw_clone_post]): each of
    [Fork.clone_errnos] is error-encoded, and a pid inside the envelope is
    not. *)
Lemma fw_errno_error_encoded : forall r : word,
  ret_in_errnos clone_errnos r = true -> addr_is_error_b r = true.
Proof.
  intros r H. unfold ret_in_errnos, clone_errnos in H.
  cbn [List.existsb] in H.
  repeat (apply orb_true_iff in H; destruct H as [H|H]);
    try discriminate;
    apply bv_eqb_true_eq in H; subst r; vm_compute; reflexivity.
Qed.

Lemma fw_envelope_not_error : forall r : word,
  (0 < bv_unsigned r)%Z -> (bv_unsigned r < PID_MAX_ENVELOPE)%Z ->
  addr_is_error_b r = false.
Proof.
  intros r _ Hhi. unfold addr_is_error_b, two_pow_64.
  unfold PID_MAX_ENVELOPE in Hhi.
  apply Z.ltb_ge. change (2 ^ 22)%Z with 4194304%Z in Hhi.
  change (2 ^ 64 - 4096)%Z with 18446744073709547520%Z. lia.
Qed.

Lemma fw_entry_clone_step : forall segs cfg p P evs P' e x8,
  look P p = Some e ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 220%Z ->
  ms_gpr (pe_ms e) 0 = 17 ->
  fw_model_ok (pe_model e) ->
  pstep_at segs cfg p P evs (PNext P') ->
  exists eff model'',
    fw_model_ok model''
    /\ eff_writes eff = [] /\ eff_zeros eff = []
    /\ eff_unmaps eff = [] /\ eff_copies eff = []
    /\ ( (ret_in_errnos clone_errnos (eff_ret eff) = true
          /\ P' = absorb P e
                    (mkCfg (advance_past_svc (apply_effect (pe_ms e) eff))
                           model''))
         \/ ( (0 < bv_unsigned (eff_ret eff))%Z
              /\ (bv_unsigned (eff_ret eff) < PID_MAX_ENVELOPE)%Z
              /\ look P (eff_ret eff) = None
              /\ P' = clone_result P e
                        (mkCfg (advance_past_svc (apply_effect (pe_ms e) eff))
                               model'')
                        (eff_ret eff) ) ).
Proof.
  intros segs cfg p P evs P' e x8 Hl Hs H220 Ha0 Hh Hp.
  assert (Hrun : forall eff m' ev,
            syscall_spec (sys_input segs (pe_ms e) x8)
              (cfg_model (pe_cfg (pcfg_shared P) e)) (Ok eff m' ev) ->
            m_halted m' = None).
  { intros eff m' ev Hsp.
    destruct (fw_clone_post segs (pe_ms e) x8 _ eff m' ev H220 Ha0 Hsp)
      as (_ & _ & _ & _ & _ & Hhm & _ & _).
    rewrite Hhm. exact (fw_model_ok_halted _ Hh). }
  (* NAMED rather than matched: the reap arms have thirteen premises and
     more, and an Ltac pattern over them is how the first attempt failed
     -- [pstep_length_cases] above records the same lesson. *)
  inversion Hp as
    [ P1 e1 evs1 c1 Hl1 Hss1 Hcs1 Hwi1 Hma1 Hwo1 Heq1 Heq2 Heq3
    | P2 e2 evs2 c2 q2 Hl2 Hss2 Hcs2 Hcp2 Hfr2 Hma2 Heq4 Heq5 Heq6
    | P3 e3 q3 ez3 x83 sa3 st3 eff3 mo3 du3
      Hl3 Hh3 Hsv3 Hwi3 Hwa3 Hlq3 Hne3 Hpar3 Hk3 Hst3 Hrd3 Heff3 Hmat3
      Heq7 Heq8 Heq9
    | P4 e4 evs4 Hl4 Hs4 Hw4 Hwo4
    | P5 e5 Hl5 Hh5 Hm5
    | P6 e6 q6 ez6 x86 sa6 ru6 rb6 st6 eff6 mo6 du6
      Hl6 Hh6 Hsv6 Hwo6 Hna6 Hru6 Hlq6 Hne6 Hpar6 Hk6 Hst6 Hrd6 Hlen6 Heff6 Hmat6
    | P7 e7 x87 sa7 ru7 Hl7 Hh7 Hsv7 Hwo7 Hna7 Hru7 Hz7
    | P8 e8 Hl8 Hh8 Hrf8 ]; subst.
  - (* pstep_other: the clone declined, so a0 is in the errno list *)
    assert (He1 : e1 = e)
      by (rewrite Hl1 in Hl; injection Hl as Hl; exact Hl).
    subst e1.
    destruct (fw_sstep_running_syscall_inv segs cfg (pe_ms e)
                (cfg_model (pe_cfg (pcfg_shared P) e)) evs c1 x8 Hs Hrun Hss1)
      as (eff & model' & model'' & evs0 & Hsp & Hh' & Hmat & Hc0).
    destruct (fw_clone_post segs (pe_ms e) x8 _ eff model' evs0 H220 Ha0 Hsp)
      as (_ & Hw & Hz & Hu & Hcp & _ & Hokm & Hdisj1).
    exists eff, model''.
    split; [exact (fw_model_ok_materialize _ _ _ Hmat
                     (Hokm (fw_model_ok_pe_cfg _ e Hh)))|].
    split; [exact Hw|]. split; [exact Hz|].
    split; [exact Hu|]. split; [exact Hcp|].
    left. split.
    + (* the two readings agree on this program's answers: an envelope pid
         is not error-encoded, so a declined clone answered an errno *)
      destruct Hdisj1 as [Herr | (Hlo & Hhi)]; [exact Herr|].
      exfalso.
      unfold clone_success_b in Hcs1. cbn [cfg_ms pe_cfg] in Hcs1.
      rewrite Hs, H220 in Hcs1. cbn [clone_sysno] in Hcs1.
      rewrite Hc0 in Hcs1. cbn [cfg_ms] in Hcs1.
      rewrite fw_a0_after_effect in Hcs1.
      rewrite (fw_envelope_not_error _ Hlo Hhi) in Hcs1.
      cbn in Hcs1; discriminate.
    + rewrite Hc0. reflexivity.
  - (* pstep_clone: the pid branch, inside the envelope *)
    assert (He2 : e2 = e)
      by (rewrite Hl2 in Hl; injection Hl as Hl; exact Hl).
    subst e2.
    destruct (fw_sstep_running_syscall_inv segs cfg (pe_ms e)
                (cfg_model (pe_cfg (pcfg_shared P) e)) evs c2 x8 Hs Hrun Hss2)
      as (eff & model' & model'' & evs0 & Hsp & Hh' & Hmat & Hc0).
    destruct (fw_clone_post segs (pe_ms e) x8 _ eff model' evs0 H220 Ha0 Hsp)
      as (_ & Hw & Hz & Hu & Hcp & _ & Hokm & Hdisj).
    assert (Hnerr : ret_in_errnos clone_errnos (eff_ret eff) = false).
    { unfold clone_success_b in Hcs2. cbn [cfg_ms pe_cfg] in Hcs2.
      rewrite Hs, H220 in Hcs2. cbn [clone_sysno] in Hcs2.
      rewrite Hc0 in Hcs2. cbn [cfg_ms] in Hcs2.
      rewrite fw_a0_after_effect in Hcs2.
      destruct (ret_in_errnos clone_errnos (eff_ret eff)) eqn:Hre; [|reflexivity].
      rewrite (fw_errno_error_encoded _ Hre) in Hcs2.
      cbn in Hcs2; discriminate. }
    (* the child's pid IS the return, which is what [child_pid_core] says *)
    destruct Hcp2 as (Hqa & _).
    rewrite Hc0 in Hqa. cbn [cfg_ms] in Hqa.
    rewrite fw_a0_after_effect in Hqa.
    rewrite <- Hqa in Hfr2.
    exists eff, model''.
    split; [exact (fw_model_ok_materialize _ _ _ Hmat
                     (Hokm (fw_model_ok_pe_cfg _ e Hh)))|].
    split; [exact Hw|]. split; [exact Hz|].
    split; [exact Hu|]. split; [exact Hcp|].
    right.
    destruct Hdisj as [Herr | (Hlo & Hhi)];
      [rewrite Herr in Hnerr; discriminate|].
    split; [exact Hlo|]. split; [exact Hhi|].
    split; [exact Hfr2|].
    rewrite Hc0, Hqa. reflexivity.
  - (* pstep_wait_reap: 220 is not a wait4 *)
    exfalso.
    assert (He3 : e3 = e)
      by (rewrite Hl3 in Hl; injection Hl as Hl; exact Hl).
    subst e3.
    unfold wait4_intercept_b in Hwi3. cbn [cfg_ms pe_cfg] in Hwi3.
    rewrite Hs, H220 in Hwi3. cbn in Hwi3. discriminate.
  - (* pstep_wait_nohang_reap: nor is it the [wait4] gate's *)
    exfalso.
    assert (He6 : e6 = e)
      by (rewrite Hl6 in Hl; injection Hl as Hl; exact Hl).
    subst e6.
    rewrite (wait4_owned_not_260 _ _ x8 Hs) in Hwo6;
      [discriminate Hwo6 | rewrite H220; discriminate].
  - (* pstep_wait_nohang_zero: likewise *)
    exfalso.
    assert (He7 : e7 = e)
      by (rewrite Hl7 in Hl; injection Hl as Hl; exact Hl).
    subst e7.
    rewrite (wait4_owned_not_260 _ _ x8 Hs) in Hwo7;
      [discriminate Hwo7 | rewrite H220; discriminate].
Qed.

(* =========================================================================
   The remainders the segment lemmas supply
   ========================================================================= *)

(** THE INSTANCE COMES FROM THE STATE.  Every segment lemma is stated
    over [PropExec.mkst], which fixes the float registers and the
    control word from an [FPState] instance.  The states this proof
    holds were built by the relation, not by [mkst], so the instance is
    read back off the state -- which is what [ForkwaitSteps.mkst_eta]
    does, and why each of these four takes the entry's machine state
    apart rather than rewriting with it. *)

(** The entry run: seven steps from the image's entry point to the
    clone's [ecall], with the clone's arguments in place.  The stack
    pointer bound travels with it because the parent's prologue, nine
    steps later, is what needs it. *)
Lemma fw_start_rem : forall ms,
  ms_svc_pending ms = None ->
  ms_resv ms = None ->
  bv_unsigned (ms_pc_val ms) = 0x11000%Z ->
  (16 <= bv_unsigned (getr (ms_regs ms) 2))%Z ->
  store_ok forkwait_segs (ms_mem ms)
    (fw_slot (getr (ms_regs ms) 2)) 4 = true ->
  fw_rem ms fw_q_clone.
Proof.
  intros ms Hsv Hrv Hpc Hsp Hst.
  assert (Hpcw : ms_pc_val ms = 0x11000)
    by (apply bv_eq; rewrite Hpc; vm_compute; reflexivity).
  destruct ms as [regs fregs pc svc resv fcsr mem rom].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr
       ms_mem ms_rom] in *.
  subst svc resv pc.
  exists 7%nat,
    (@ecall_st (mkFP fregs fcsr) (fw_regs_A regs) 0x11018 mem rom).
  split; [lia|]. split.
  - exact (@fw_run_A (mkFP fregs fcsr) regs mem rom).
  - unfold fw_q_clone.
    split; [apply fw_A_svc|].
    split; [vm_compute; reflexivity|].
    split; [apply fw_A_a0|].
    split; [apply fw_A_a1|].
    split; [reflexivity|].
    split.
    + cbn [ms_regs ecall_st]. unfold fw_regs_A. getr_resolve. exact Hsp.
    + cbn [ms_mem ms_regs ecall_st]. unfold fw_regs_A. getr_resolve.
      exact Hst.
Qed.

(** The parent's nine steps from the clone's resume point to its
    [wait4], with a0 the pid the clone returned.  The slot stays
    writable across them because the prologue stores nothing: it moves
    the stack pointer and leaves memory alone. *)
Lemma fw_parent_rem : forall ms (q : word),
  ms_svc_pending ms = None ->
  ms_resv ms = None ->
  bv_unsigned (ms_pc_val ms) = 0x1101c%Z ->
  ms_gpr ms 0 = q ->
  (0 < bv_unsigned q)%Z ->
  (bv_unsigned q < 2 ^ 22)%Z ->
  (16 <= bv_unsigned (getr (ms_regs ms) 2))%Z ->
  store_ok forkwait_segs (ms_mem ms)
    (fw_slot (getr (ms_regs ms) 2)) 4 = true ->
  fw_rem ms fw_q_wait4.
Proof.
  intros ms q Hsv Hrv Hpc Ha0 Hq0 Hq1 Hsp Hst.
  assert (Ha0' : getr (ms_regs ms) 10 = q).
  { rewrite <- Ha0. symmetry.
    apply (ms_gpr_getr ms 0 (10 : reg));
      first [bveq | vm_compute; reflexivity]. }
  assert (Hpcw : ms_pc_val ms = 0x1101c)
    by (apply bv_eq; rewrite Hpc; vm_compute; reflexivity).
  destruct ms as [regs fregs pc svc resv fcsr mem rom].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr
       ms_mem ms_rom] in *.
  subst svc resv pc.
  exists 9%nat,
    (@ecall_st (mkFP fregs fcsr) (fw_regs_P regs (getr regs 2))
       0x1103c mem rom).
  split; [lia|]. split.
  - exact (@fw_run_parent (mkFP fregs fcsr) regs mem rom q (getr regs 2)
             Ha0' eq_refl Hq0 Hq1 Hsp).
  - unfold fw_q_wait4.
    split; [apply fw_P_svc|].
    split; [vm_compute; reflexivity|].
    split; [apply fw_P_a0|].
    split.
    + rewrite (fw_P_a1 regs (getr regs 2) 0x1103c mem rom).
      cbn [ms_regs ecall_st]. unfold fw_regs_P. getr_resolve. reflexivity.
    + split; [apply fw_P_a2|].
      split; [apply fw_P_a3|].
      split; [reflexivity|].
      split.
      * rewrite (fw_P_a1 regs (getr regs 2) 0x1103c mem rom).
        rewrite fw_slot_addr by exact Hsp.
        pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr.
        change (bv_modulus 64) with (2 ^ 64)%Z in Hr. lia.
      * rewrite (fw_P_a1 regs (getr regs 2) 0x1103c mem rom).
        cbn [ms_mem ecall_st]. exact Hst.
Qed.

(** The child's five steps from the same resume point, with a0 zero. *)
Lemma fw_child_rem : forall ms,
  ms_svc_pending ms = None ->
  ms_resv ms = None ->
  bv_unsigned (ms_pc_val ms) = 0x1101c%Z ->
  ms_gpr ms 0 = 0 ->
  fw_rem ms fw_q_exit7.
Proof.
  intros ms Hsv Hrv Hpc Ha0.
  assert (Ha0' : getr (ms_regs ms) 10 = 0).
  { rewrite <- Ha0. symmetry.
    apply (ms_gpr_getr ms 0 (10 : reg));
      first [bveq | vm_compute; reflexivity]. }
  assert (Hpcw : ms_pc_val ms = 0x1101c)
    by (apply bv_eq; rewrite Hpc; vm_compute; reflexivity).
  destruct ms as [regs fregs pc svc resv fcsr mem rom].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr
       ms_mem ms_rom] in *.
  subst svc resv pc.
  exists 5%nat,
    (@ecall_st (mkFP fregs fcsr) (fw_regs_exit7 regs) 0x11058 mem rom).
  split; [lia|]. split.
  - exact (@fw_run_child (mkFP fregs fcsr) regs mem rom Ha0').
  - split; [apply fw_exit7_svc | apply fw_exit7_a0].
Qed.

(** And the tail the injected errno takes, which ends at the same call.
    It is unreachable at [Run.forced_only_cfg]; it is discharged rather
    than excluded, so the same proof stands at [Run.may_fail_cfg]. *)
Lemma fw_fail_rem : forall ms,
  ms_svc_pending ms = None ->
  ms_resv ms = None ->
  bv_unsigned (ms_pc_val ms) = 0x1101c%Z ->
  (bv_signed (ms_gpr ms 0) < 0)%Z ->
  fw_rem ms fw_q_exit7.
Proof.
  intros ms Hsv Hrv Hpc Ha0.
  assert (Ha0' : (bv_signed (getr (ms_regs ms) 10) < 0)%Z).
  { rewrite <- (ms_gpr_getr ms 0 (10 : reg));
      [exact Ha0
      |first [bveq | vm_compute; reflexivity]
      |first [bveq | vm_compute; reflexivity]]. }
  assert (Hpcw : ms_pc_val ms = 0x1101c)
    by (apply bv_eq; rewrite Hpc; vm_compute; reflexivity).
  destruct ms as [regs fregs pc svc resv fcsr mem rom].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr
       ms_mem ms_rom] in *.
  subst svc resv pc.
  exists 4%nat,
    (@ecall_st (mkFP fregs fcsr) (fw_regs_exit7 regs) 0x11064 mem rom).
  split; [lia|]. split.
  - exact (@fw_run_fail (mkFP fregs fcsr) regs mem rom Ha0').
  - split; [apply fw_exit7_svc | apply fw_exit7_a0].
Qed.

(** The parent's four steps after the reap, which read the status back
    out of the slot the reap wrote. *)
Lemma fw_reap_rem : forall ms (a : word),
  ms_svc_pending ms = None ->
  ms_resv ms = None ->
  bv_unsigned (ms_pc_val ms) = 0x11040%Z ->
  getr (ms_regs ms) 2 = a ->
  rdn forkwait_segs (ms_mem ms) a 4 = Some (Z_to_le_bytes 4 1792) ->
  fw_rem ms fw_q_exit7.
Proof.
  intros ms a Hsv Hrv Hpc Hsp Hrd.
  assert (Hpcw : ms_pc_val ms = 0x11040)
    by (apply bv_eq; rewrite Hpc; vm_compute; reflexivity).
  destruct ms as [regs fregs pc svc resv fcsr mem rom].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr
       ms_mem ms_rom] in *.
  subst svc resv pc.
  exists 4%nat,
    (@ecall_st (mkFP fregs fcsr) (fw_regs_C regs) 0x1104c mem rom).
  split; [lia|]. split.
  - exact (@fw_run_reap_at (mkFP fregs fcsr) regs mem rom a Hsp Hrd).
  - split; [apply fw_C_svc | apply fw_C_a0].
Qed.

(** [Procs.clear_shared] blanks the two slots the shared state owns; it
    does not touch [State.ProcState]. *)
Lemma fw_halted_clear_shared : forall m, m_halted (clear_shared m) = m_halted m.
Proof. reflexivity. Qed.

(* =========================================================================
   The measure, read off the remainder
   ========================================================================= *)

(** [Measure.fw_entry] counted PROGRAM COUNTERS, which the shapes no
    longer name, so it is gone and this is what takes its place: the
    remainder's own length, plus a constant for the call it ends at and
    for everything that call still leads to.

    THE CONSTANTS ARE DELIBERATELY SLACK.  An exact count would have to
    name the length of each segment -- seven, nine, five, four -- at
    every arithmetic step.  The bound [fw_rem] carries (sixteen) is
    enough instead: whatever an entry's remainder is, its weight is at
    most sixteen above its constant, so each constant only has to
    exceed what the call it names leads to.  [exit_group] leads to
    nothing, so 1; [wait4] reaps and leaves a tail worth at most
    16 + 1, so 18; [clone] leaves a parent worth at most 16 + 18 and a
    child worth at most 16 + 1, so 52.  Each of the three inequalities
    below is then [lia] over those numbers. *)
Fixpoint fw_probe (f : nat) (ms : machine_state) : option (nat * word) :=
  match f with
  | O => match ms_svc_pending ms with
         | Some x8 => Some (0%nat, x8)
         | None => None
         end
  | S f' =>
      match ms_svc_pending ms with
      | Some x8 => Some (0%nat, x8)
      | None =>
          match RiscvSemantics.step forkwait_segs ms with
          | MachineOk ms' =>
              match fw_probe f' ms' with
              | Some (k, x8) => Some (S k, x8)
              | None => None
              end
          | _ => None
          end
      end
  end.

(** The search finds exactly the remainder the shape names: the run has
    no pending call at any intermediate state, so the search cannot
    stop early, and it has one at the end, so it cannot run past. *)
Lemma fw_probe_exact : forall k f ms msf x8,
  (k <= f)%nat ->
  machine_run forkwait_segs k ms = Some msf ->
  ms_svc_pending msf = Some x8 ->
  fw_probe f ms = Some (k, x8).
Proof.
  induction k as [|k IH]; intros f ms msf x8 Hk Hrun Hsv.
  - cbn [machine_run] in Hrun. injection Hrun as <-.
    destruct f; cbn [fw_probe]; rewrite Hsv; reflexivity.
  - destruct f as [|f]; [exfalso; lia|].
    destruct (machine_run_inv _ _ _ _ Hrun) as (ms' & Hp & Hs & Hr).
    cbn [fw_probe]. rewrite Hp, Hs.
    rewrite (IH f ms' msf x8 ltac:(lia) Hr Hsv). reflexivity.
Qed.

Definition fw_const (nr : Z) : nat :=
  if Z.eqb nr 220 then 52%nat
  else if Z.eqb nr 260 then 18%nat
  else 1%nat.

Definition fw_ms_left (ms : machine_state) : nat :=
  match fw_probe 16 ms with
  | Some (k, x8) => (k + fw_const (bv_unsigned x8))%nat
  | None => 0%nat
  end.

(** A halted entry is worth nothing: it cannot step, and the reap drops
    it, so charging it would make the reap fail to decrease. *)
Definition fw_entry_left (e : ProcessEntry) : nat :=
  match m_halted (pe_model e) with
  | Some _ => 0%nat
  | None => fw_ms_left (pe_ms e)
  end.

(** The count reads the halt flag and the machine state, never the parent
    link, so the orphaning at an exit leaves it alone
    ([MustExitP.pmeasure_absorb_lt]'s premise). *)
Lemma fw_entry_left_parent_blind : forall x,
  fw_entry_left (with_parent x None) = fw_entry_left x.
Proof. intros x. reflexivity. Qed.

Definition fw_mu (P : pconfig) : nat := pmeasure fw_entry_left P.

Lemma fw_ms_left_of : forall ms k msf x8,
  (k <= 16)%nat ->
  machine_run forkwait_segs k ms = Some msf ->
  ms_svc_pending msf = Some x8 ->
  fw_ms_left ms = (k + fw_const (bv_unsigned x8))%nat.
Proof.
  intros ms k msf x8 Hk Hrun Hsv. unfold fw_ms_left.
  rewrite (fw_probe_exact k 16 ms msf x8 Hk Hrun Hsv). reflexivity.
Qed.

Lemma fw_entry_left_halted : forall e,
  m_halted (pe_model e) <> None -> fw_entry_left e = 0%nat.
Proof.
  intros e H. unfold fw_entry_left.
  destruct (m_halted (pe_model e)); [reflexivity | congruence].
Qed.

(** At a pending call the remainder is empty, so the weight is the
    call's own constant -- which is the exact value the two
    shape-changing steps need on their larger side. *)
Lemma fw_entry_left_pending : forall e x8,
  m_halted (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  fw_entry_left e = fw_const (bv_unsigned x8).
Proof.
  intros e x8 Hh Hsv. unfold fw_entry_left. rewrite Hh.
  rewrite (fw_ms_left_of (pe_ms e) 0%nat (pe_ms e) x8
             (Nat.le_0_l 16) eq_refl Hsv).
  reflexivity.
Qed.

(** And anywhere in a remainder it is at most sixteen above it, which
    is the smaller side. *)
Lemma fw_entry_left_bound : forall e Q nr,
  (forall ms, Q ms -> exists x8, ms_svc_pending ms = Some x8
                                 /\ bv_unsigned x8 = nr) ->
  fw_rem (pe_ms e) Q ->
  (fw_entry_left e <= 16 + fw_const nr)%nat.
Proof.
  intros e Q nr Hnr (k & msf & Hk & Hrun & HQ).
  unfold fw_entry_left. destruct (m_halted (pe_model e)); [lia|].
  destruct (Hnr _ HQ) as (x8 & Hsv & Hx).
  rewrite (fw_ms_left_of (pe_ms e) k msf x8 Hk Hrun Hsv), Hx. lia.
Qed.

(** The three shapes' calls, as the number each pins. *)
Lemma fw_q_clone_nr : forall ms, fw_q_clone ms ->
  exists x8, ms_svc_pending ms = Some x8 /\ bv_unsigned x8 = 220%Z.
Proof.
  intros ms (H & _). exists 220.
  split; [exact H | vm_compute; reflexivity].
Qed.

Lemma fw_q_wait4_nr : forall ms, fw_q_wait4 ms ->
  exists x8, ms_svc_pending ms = Some x8 /\ bv_unsigned x8 = 260%Z.
Proof.
  intros ms (H & _). exists 260.
  split; [exact H | vm_compute; reflexivity].
Qed.

Lemma fw_q_exit7_nr : forall ms, fw_q_exit7 ms ->
  exists x8, ms_svc_pending ms = Some x8 /\ bv_unsigned x8 = 94%Z.
Proof.
  intros ms (H & _). exists 94.
  split; [exact H | vm_compute; reflexivity].
Qed.

(** AN ORDINARY STEP TAKES ONE OFF, whichever call the remainder ends
    at: the constant is the same before and after and the length falls
    by one.  This is the measure half of [fw_rem_step]. *)
Lemma fw_entry_left_lt_step : forall e Q ms' model',
  fw_q_pending Q ->
  m_halted (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = None ->
  fw_rem (pe_ms e) Q ->
  RiscvSemantics.step forkwait_segs (pe_ms e) = MachineOk ms' ->
  m_halted model' = m_halted (pe_model e) ->
  (fw_entry_left (pe_absorb e (mkCfg ms' model')) < fw_entry_left e)%nat.
Proof.
  intros e Q ms' model' HQp Hh Hsv (k & msf & Hk & Hrun & HQ) Hstep Hhal.
  destruct k as [|k].
  { cbn [machine_run] in Hrun. injection Hrun as <-.
    exfalso. exact (HQp _ HQ Hsv). }
  destruct (machine_run_inv _ _ _ _ Hrun) as (ms1 & _ & Hs1 & Hr1).
  rewrite Hstep in Hs1. injection Hs1 as <-.
  destruct (ms_svc_pending msf) as [x8|] eqn:Ex;
    [|exfalso; exact (HQp _ HQ Ex)].
  unfold fw_entry_left.
  cbn [pe_model pe_absorb cfg_model pe_ms cfg_ms].
  rewrite fw_halted_clear_shared, Hhal, Hh.
  rewrite (fw_ms_left_of (pe_ms e) (S k) msf x8 Hk Hrun Ex).
  rewrite (fw_ms_left_of ms' k msf x8 ltac:(lia) Hr1 Ex).
  lia.
Qed.

(** A one-entry replacement: the only entry's weight is the sum. *)
Lemma fw_mu_absorb_one_lt : forall P e c' n,
  pcfg_procs P = [(pe_pid e, e)] ->
  (fw_entry_left (pe_absorb e c') <= n)%nat ->
  (n < fw_entry_left e)%nat ->
  (fw_mu (absorb P e c') < fw_mu P)%nat.
Proof.
  intros P e c' n Hp Ha Hn. unfold fw_mu. apply (pmeasure_absorb_lt _ _ _ _ fw_entry_left_parent_blind).
  - unfold look. rewrite Hp. cbn [look_in fst snd].
    rewrite bv_eqb_same. reflexivity.
  - lia.
Qed.

(** THE CLONE'S ARITHMETIC, the step the constants were chosen for: one
    entry worth 52 becomes two, worth at most 34 and at most 17. *)
Lemma fw_mu_clone_lt : forall P e c' q,
  pcfg_procs P = [(pe_pid e, e)] ->
  fw_entry_left e = 52%nat ->
  (fw_entry_left (pe_absorb e c') <= 34)%nat ->
  (fw_entry_left (child_entry e (pe_cfg (pcfg_shared P) e) c' q) <= 17)%nat ->
  (fw_mu (clone_result P e c' q) < fw_mu P)%nat.
Proof.
  intros P e c' q Hp He Ha Hb.
  unfold fw_mu, pmeasure, clone_result. cbn [pcfg_procs].
  rewrite !Hp. cbn [replace_in fst]. rewrite bv_eqb_same.
  cbn [List.app msum List.fold_right snd].
  rewrite He. lia.
Qed.

(** AND THE REAP'S: the parent falls from 18 to at most 17 and the
    zombie, worth nothing, leaves the table. *)
Lemma fw_mu_reap_lt : forall P ep ec ep' q,
  pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)] ->
  bv_eqb (pe_pid ep) q = false ->
  pe_pid ec = q ->
  fw_entry_left ep = 18%nat ->
  fw_entry_left ec = 0%nat ->
  (fw_entry_left ep' <= 17)%nat ->
  (msum fw_entry_left
     (drop_in (replace_in (pcfg_procs P) (pe_pid ep) ep') q) < fw_mu P)%nat.
Proof.
  intros P ep ec ep' q Hp Hne Hq Hep Hec Hep'.
  unfold fw_mu, pmeasure. rewrite Hp.
  rewrite (fw_reap_target_table ep ec ep' q Hne Hq).
  cbn [msum List.fold_right snd]. rewrite Hep, Hec. lia.
Qed.

(* =========================================================================
   Preservation, one (shape, arm, stepping entry) at a time
   ========================================================================= *)

(** The two-entry table under a replacement at each of its keys. *)
Lemma fw_two_replace_parent : forall ep ec ep',
  replace_in [(pe_pid ep, ep); (pe_pid ec, ec)] (pe_pid ep) ep'
  = [(pe_pid ep, ep'); (pe_pid ec, ec)].
Proof.
  intros ep ec ep'. cbn [replace_in fst]. rewrite bv_eqb_same. reflexivity.
Qed.

Lemma fw_two_replace_child : forall ep ec ec',
  bv_eqb (pe_pid ep) (pe_pid ec) = false ->
  replace_in [(pe_pid ep, ep); (pe_pid ec, ec)] (pe_pid ec) ec'
  = [(pe_pid ep, ep); (pe_pid ec, ec')].
Proof.
  intros ep ec ec' Hne. cbn [replace_in fst]. rewrite Hne.
  cbn [replace_in fst]. rewrite bv_eqb_same. reflexivity.
Qed.

(** ONE ENTRY, NOT YET AT ITS CALL.  The remainder loses a step and
    everything else is [absorb]'s doing.  Quantified over the call the
    remainder ends at, so the entry run, the two tails and the errno
    tail are one lemma. *)
Lemma fw_one_rem_step : forall cfg P evs P' Q e,
  fw_q_pending Q ->
  pcfg_procs P = [(pe_pid e, e)] ->
  pcfg_root P = pe_pid e ->
  pe_parent e = None ->
  fw_model_ok (pe_model e) ->
  fw_rem (pe_ms e) Q ->
  ms_svc_pending (pe_ms e) = None ->
  pstep_cfg forkwait_segs cfg P evs (PNext P') ->
  fw_one P' Q /\ (fw_mu P' < fw_mu P)%nat.
Proof.
  intros cfg P evs P' Q e HQp Hp Hr Hpar Hh Hrem Hsv Hstep.
  destruct Hstep as (p & Hstep).
  destruct (pstep_at_not_halted _ _ _ _ _ _ Hstep) as (e0 & Hl0 & _).
  destruct (fw_look_one P e p e0 Hp Hl0) as (He0 & _). subst e0.
  destruct (fw_entry_instr_step forkwait_segs cfg p P evs P' e Hl0 Hsv Hstep)
    as (ms' & model' & Hmstep & Hhal & Hfrm & HP').
  destruct (absorb_one_entry P e (mkCfg ms' model') Hp Hr)
    as (Hp' & Hr' & _).
  subst P'.
  assert (Hlook : look P (pe_pid e) = Some e)
    by (unfold look; rewrite Hp; cbn [look_in fst snd];
        rewrite bv_eqb_same; reflexivity).
  split;
    [| unfold fw_mu; apply (pmeasure_absorb_lt _ _ _ _ fw_entry_left_parent_blind);
       [ exact Hlook
       | exact (fw_entry_left_lt_step e Q ms' model' HQp
                  (fw_model_ok_halted _ Hh) Hsv Hrem Hmstep Hhal) ] ].
  exists (pe_absorb e (mkCfg ms' model')).
  split; [exact Hp'|].
  split; [exact Hr'|].
  split; [exact Hpar|].
  split.
  - cbn [pe_model pe_absorb cfg_model].
    exact (fw_model_ok_clear_shared _ (Hfrm Hh)).
  - cbn [pe_ms pe_absorb cfg_ms].
    exact (fw_rem_step (pe_ms e) Q ms' HQp Hrem Hsv Hmstep).
Qed.

(** TWO ENTRIES, THE PARENT STEPPING.  The child's record is at another
    key, so [replace_in] leaves it alone -- and a shape clause reads the
    RECORD, not the view, so nothing has to be said about the shared
    state. *)
Lemma fw_two_parent_step : forall cfg P evs P' ep ec,
  pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)] ->
  pcfg_root P = pe_pid ep ->
  bv_eqb (pe_pid ep) (pe_pid ec) = false ->
  pe_parent ec = Some (pe_pid ep) ->
  pe_parent ep = None ->
  fw_model_ok (pe_model ep) ->
  fw_rem (pe_ms ep) fw_q_wait4 ->
  ms_svc_pending (pe_ms ep) = None ->
  fw_child_st ec ->
  pstep_at forkwait_segs cfg (pe_pid ep) P evs (PNext P') ->
  fw_two P' /\ (fw_mu P' < fw_mu P)%nat.
Proof.
  intros cfg P evs P' ep ec Hp Hr Hne Hcpar Hppar Hh Hrem Hsv Hch Hstep.
  pose proof (fw_look_two_parent P ep ec Hp) as Hl.
  destruct (fw_entry_instr_step forkwait_segs cfg (pe_pid ep) P evs P' ep
              Hl Hsv Hstep) as (ms' & model' & Hmstep & Hhal & Hfrm & HP').
  subst P'.
  split;
    [| unfold fw_mu; apply (pmeasure_absorb_lt _ _ _ _ fw_entry_left_parent_blind);
       [ exact Hl
       | exact (fw_entry_left_lt_step ep fw_q_wait4 ms' model'
                  fw_q_wait4_pending (fw_model_ok_halted _ Hh) Hsv Hrem
                  Hmstep Hhal) ] ].
  exists (pe_absorb ep (mkCfg ms' model')), ec.
  unfold absorb. cbn [pcfg_procs pcfg_root].
  rewrite Hp, fw_two_replace_parent.
  rewrite orphan_at_exit_running
    by (cbn [cfg_model]; rewrite Hhal; exact (fw_model_ok_halted _ Hh)).
  split; [reflexivity|].
  split; [exact Hr|].
  split; [exact Hne|].
  split; [exact Hcpar|].
  split; [exact Hppar|].
  split; [|exact Hch].
  split.
  - cbn [pe_model pe_absorb cfg_model].
    exact (fw_model_ok_clear_shared _ (Hfrm Hh)).
  - cbn [pe_ms pe_absorb cfg_ms].
    exact (fw_rem_step (pe_ms ep) fw_q_wait4 ms' fw_q_wait4_pending
             Hrem Hsv Hmstep).
Qed.

(** TWO ENTRIES, THE CHILD STEPPING.  The same lemma with the roles
    swapped, which is what quantifying the frame over the stepping entry
    bought. *)
Lemma fw_two_child_step : forall cfg P evs P' ep ec,
  pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)] ->
  pcfg_root P = pe_pid ep ->
  bv_eqb (pe_pid ep) (pe_pid ec) = false ->
  pe_parent ec = Some (pe_pid ep) ->
  pe_parent ep = None ->
  fw_live ep fw_q_wait4 ->
  fw_model_ok (pe_model ec) ->
  fw_rem (pe_ms ec) fw_q_exit7 ->
  ms_svc_pending (pe_ms ec) = None ->
  pstep_at forkwait_segs cfg (pe_pid ec) P evs (PNext P') ->
  fw_two P' /\ (fw_mu P' < fw_mu P)%nat.
Proof.
  intros cfg P evs P' ep ec Hp Hr Hne Hcpar Hppar Hpar Hh Hrem Hsv Hstep.
  pose proof (fw_look_two_child P ep ec Hp Hne) as Hl.
  destruct (fw_entry_instr_step forkwait_segs cfg (pe_pid ec) P evs P' ec
              Hl Hsv Hstep) as (ms' & model' & Hmstep & Hhal & Hfrm & HP').
  subst P'.
  split;
    [| unfold fw_mu; apply (pmeasure_absorb_lt _ _ _ _ fw_entry_left_parent_blind);
       [ exact Hl
       | exact (fw_entry_left_lt_step ec fw_q_exit7 ms' model'
                  fw_q_exit7_pending (fw_model_ok_halted _ Hh) Hsv Hrem
                  Hmstep Hhal) ] ].
  exists ep, (pe_absorb ec (mkCfg ms' model')).
  unfold absorb. cbn [pcfg_procs pcfg_root].
  rewrite Hp, (fw_two_replace_child ep ec _ Hne).
  rewrite fw_orphan_two_child by exact Hppar.
  split; [reflexivity|].
  split; [exact Hr|].
  split; [exact Hne|].
  split; [exact Hcpar|].
  split; [exact Hppar|].
  split; [exact Hpar|].
  left. split.
  - cbn [pe_model pe_absorb cfg_model].
    exact (fw_model_ok_clear_shared _ (Hfrm Hh)).
  - cbn [pe_ms pe_absorb cfg_ms].
    exact (fw_rem_step (pe_ms ec) fw_q_exit7 ms' fw_q_exit7_pending
             Hrem Hsv Hmstep).
Qed.

(** The two readings of a killed flag the halted shape needs. *)
Lemma fw_killed_clear_shared : forall m,
  m_killed (clear_shared m) = m_killed m.
Proof. reflexivity. Qed.

Lemma fw_killed_pe_cfg : forall S e,
  m_killed (cfg_model (pe_cfg S e)) = m_killed (pe_model e).
Proof. reflexivity. Qed.

(** The exit code this program passes: [exit_spec] masks with 255 and 7
    survives it. *)
Lemma fw_and_seven : bv_and (7 : word) (Z_to_bv 64 255) = Z_to_bv 64 7.
Proof. bveq. Qed.

Lemma fw_ninety_four : bv_unsigned (94 : word) = 94%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma fw_two_sixty : bv_unsigned (260 : word) = 260%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma fw_two_twenty : bv_unsigned (220 : word) = 220%Z.
Proof. vm_compute. reflexivity. Qed.

(** ONE ENTRY AT ITS [exit_group]: the root halts on 7 and the table
    still has only it. *)
Lemma fw_one_exit_step : forall cfg P evs P' e,
  pcfg_procs P = [(pe_pid e, e)] ->
  pcfg_root P = pe_pid e ->
  m_halted (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = Some 94 ->
  ms_gpr (pe_ms e) 0 = 7 ->
  pstep_cfg forkwait_segs cfg P evs (PNext P') ->
  fw_one_halted P' 7 /\ (fw_mu P' < fw_mu P)%nat.
Proof.
  intros cfg P evs P' e Hp Hr Hh Hsv Ha0 Hstep.
  destruct Hstep as (p & Hstep).
  destruct (pstep_at_not_halted _ _ _ _ _ _ Hstep) as (e0 & Hl0 & _).
  destruct (fw_look_one P e p e0 Hp Hl0) as (He0 & _). subst e0.
  rewrite (fw_entry_exit_step forkwait_segs cfg p P evs P' e 94
             Hl0 Hsv fw_ninety_four Hstep).
  rewrite Ha0, fw_and_seven.
  set (cex := mkCfg (pe_ms e)
                (with_halted (Z_to_bv 64 7)
                   (cfg_model (pe_cfg (pcfg_shared P) e)))).
  destruct (absorb_one_entry P e cex Hp Hr) as (Hp' & Hr' & Hl').
  assert (Hlook : look P (pe_pid e) = Some e)
    by (unfold look; rewrite Hp; cbn [look_in fst snd];
        rewrite bv_eqb_same; reflexivity).
  split;
    [| unfold fw_mu; apply (pmeasure_absorb_lt _ _ _ _ fw_entry_left_parent_blind);
       [ exact Hlook
       | rewrite (fw_entry_left_halted (pe_absorb e cex))
           by (cbn [pe_model pe_absorb cfg_model];
               unfold cex; cbn [cfg_model];
               rewrite fw_halted_clear_shared, fw_m_halted_with_halted;
               discriminate);
         rewrite (fw_entry_left_pending e 94 Hh Hsv);
         unfold fw_const; rewrite fw_ninety_four; cbn; lia ] ].
  exists (pe_absorb e cex),
         (pe_cfg (pcfg_shared (absorb P e cex)) (pe_absorb e cex)).
  split; [exact Hp'|].
  split.
  - unfold root_view. rewrite Hr', Hl'. reflexivity.
  - split.
    + rewrite m_halted_pe_cfg. cbn [pe_model pe_absorb cfg_model].
      rewrite fw_halted_clear_shared. apply fw_m_halted_with_halted.
    + rewrite fw_killed_pe_cfg. cbn [pe_model pe_absorb cfg_model].
      rewrite fw_killed_clear_shared. apply fw_m_killed_with_halted.
Qed.

(** THE CHILD AT ITS [exit_group]: it becomes the zombie the parent
    will reap, holding status 7 and not killed. *)
Lemma fw_two_child_exit : forall cfg P evs P' ep ec,
  pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)] ->
  pcfg_root P = pe_pid ep ->
  bv_eqb (pe_pid ep) (pe_pid ec) = false ->
  pe_parent ec = Some (pe_pid ep) ->
  pe_parent ep = None ->
  fw_live ep fw_q_wait4 ->
  m_halted (pe_model ec) = None ->
  ms_svc_pending (pe_ms ec) = Some 94 ->
  ms_gpr (pe_ms ec) 0 = 7 ->
  pstep_at forkwait_segs cfg (pe_pid ec) P evs (PNext P') ->
  fw_two P' /\ (fw_mu P' < fw_mu P)%nat.
Proof.
  intros cfg P evs P' ep ec Hp Hr Hne Hcpar Hppar Hpar Hhc Hsv Ha0 Hstep.
  pose proof (fw_look_two_child P ep ec Hp Hne) as Hl.
  rewrite (fw_entry_exit_step forkwait_segs cfg (pe_pid ec) P evs P' ec 94
             Hl Hsv fw_ninety_four Hstep).
  rewrite Ha0, fw_and_seven.
  split;
    [| unfold fw_mu; apply (pmeasure_absorb_lt _ _ _ _ fw_entry_left_parent_blind);
       [ exact Hl
       | rewrite (fw_entry_left_halted
                    (pe_absorb ec (mkCfg (pe_ms ec)
                       (with_halted (Z_to_bv 64 7)
                          (cfg_model (pe_cfg (pcfg_shared P) ec))))))
           by (cbn [pe_model pe_absorb cfg_model];
               rewrite fw_halted_clear_shared, fw_m_halted_with_halted;
               discriminate);
         rewrite (fw_entry_left_pending ec 94 Hhc Hsv);
         unfold fw_const; rewrite fw_ninety_four; cbn; lia ] ].
  exists ep,
    (pe_absorb ec
       (mkCfg (pe_ms ec)
          (with_halted (Z_to_bv 64 7)
             (cfg_model (pe_cfg (pcfg_shared P) ec))))).
  unfold absorb. cbn [pcfg_procs pcfg_root].
  rewrite Hp, (fw_two_replace_child ep ec _ Hne).
  rewrite fw_orphan_two_child by exact Hppar.
  split; [reflexivity|].
  split; [exact Hr|].
  split; [exact Hne|].
  split; [exact Hcpar|].
  split; [exact Hppar|].
  split; [exact Hpar|].
  right. split.
  - cbn [pe_model pe_absorb cfg_model].
    rewrite fw_halted_clear_shared. apply fw_m_halted_with_halted.
  - cbn [pe_model pe_absorb cfg_model].
    rewrite fw_killed_clear_shared. apply fw_m_killed_with_halted.
Qed.

(** The blocking argument shape, read off the pinned registers. *)
Lemma fw_wait4_args : forall ms,
  ms_gpr ms 0 = 0xffffffffffffffff ->
  ms_gpr ms 2 = 0 ->
  ms_gpr ms 3 = 0 ->
  wait4_blocking_args ms = Some (ms_gpr ms 1).
Proof.
  intros ms H0 H2 H3. unfold wait4_blocking_args.
  rewrite H0, H2, H3.
  vm_compute (negb (Z.eqb (bv_unsigned (pid32 0xffffffffffffffff))
                          WAIT_ANY32)).
  vm_compute (negb (w_is0 (waitopts32 0))).
  vm_compute (negb (w_is0 (0 : word))).
  reflexivity.
Qed.

(** THE GUARD [Run.set_reg] IS BEHIND, as a lemma rather than as a
    [vm_compute] inside a goal.  Reducing the guard in place leaves the
    whole conclusion under a VM cast, and the kernel then re-runs the
    machine over a statement that mentions the memory function; the
    first version of [fw_pc_after_effect] did that and its [Qed] did not
    return.  A rewrite with a closed boolean fact costs nothing. *)
Lemma fw_x10_not_x0 : bv_eqb (10 : reg) 0 = false.
Proof. vm_compute. reflexivity. Qed.

(** The fields a write to a0 leaves alone. *)
Lemma fw_set_reg10_frame : forall ms v,
  ms_svc_pending (set_reg ms 10 v) = ms_svc_pending ms
  /\ ms_resv (set_reg ms 10 v) = ms_resv ms
  /\ ms_pc_val (set_reg ms 10 v) = ms_pc_val ms
  /\ ms_mem (set_reg ms 10 v) = ms_mem ms
  /\ ms_regs (set_reg ms 10 v) = regupd (ms_regs ms) 10 v.
Proof.
  intros ms v. unfold set_reg. rewrite fw_x10_not_x0.
  repeat split.
Qed.

(** The parent's register file after the copy-out: only a0 moved. *)
Lemma fw_sp_after_effect : forall ms eff,
  getr (ms_regs (advance_past_svc (apply_effect ms eff))) 2
  = getr (ms_regs ms) 2.
Proof.
  intros ms eff.
  cbn [ms_regs advance_past_svc apply_effect].
  destruct (fw_set_reg10_frame ms (eff_ret eff)) as (_ & _ & _ & _ & Hr).
  rewrite Hr. apply getr_other. reg_neq_tac.
Qed.

(** And its memory: the reap declares exactly one write, so the other
    three ledgers of [Run.apply_effect] are empty and the slot is the
    only byte range that moved. *)
Lemma fw_mem_after_write : forall ms q a bs,
  ms_mem (advance_past_svc (apply_effect ms (mkEffect q [(a, bs)] [])))
  = apply_writes (ms_mem ms) [(a, bs)].
Proof. reflexivity. Qed.

(** And when a call declares NO change to memory at all -- which the
    clone does not, either way it resolves -- the parent's view comes
    through untouched, which is what keeps the status slot writable
    across the call. *)
Lemma fw_mem_after_no_write : forall ms eff,
  eff_writes eff = [] -> eff_zeros eff = [] ->
  eff_unmaps eff = [] -> eff_copies eff = [] ->
  ms_mem (advance_past_svc (apply_effect ms eff)) = ms_mem ms.
Proof.
  intros ms eff Hw Hz Hu Hc.
  cbn [ms_mem advance_past_svc apply_effect].
  rewrite Hw, Hz, Hu, Hc.
  cbn [apply_writes apply_zeros apply_unmaps apply_copies].
  destruct (fw_set_reg10_frame ms (eff_ret eff)) as (_ & _ & _ & Hm & _).
  exact Hm.
Qed.

(** The program counter after a syscall: [Run.advance_past_svc] adds
    four, and the effect's own write to a0 does not touch it. *)
Lemma fw_pc_after_effect : forall ms eff,
  ms_pc_val (advance_past_svc (apply_effect ms eff))
  = ms_pc_val ms + Z_to_bv 64 4.
Proof.
  intros ms eff.
  cbn [ms_pc_val advance_past_svc apply_effect ms_pc].
  destruct (fw_set_reg10_frame ms (eff_ret eff)) as (_ & _ & Hpc & _).
  rewrite Hpc. reflexivity.
Qed.

Lemma fw_svc_after_effect : forall ms eff,
  ms_svc_pending (advance_past_svc (apply_effect ms eff)) = None.
Proof. reflexivity. Qed.

(** THE RESERVATION IS CLEARED, NOT CARRIED, across a system call:
    [Run.advance_past_svc] sets [ms_resv := None], as Linux drops an
    LR/SC reservation on a trap.  It used to carry the caller's, and
    this lemma used to say so; nothing in this file wanted that -- both
    its users are proving [= None] for the next segment lemma's
    [ForkwaitSteps.mkst_eta] -- so the clearing makes them shorter
    rather than harder. *)
Lemma fw_resv_after_effect : forall ms eff,
  ms_resv (advance_past_svc (apply_effect ms eff)) = None.
Proof. reflexivity. Qed.

Lemma fw_zero_word : Z_to_bv 64 0 = (0 : word).
Proof. bveq. Qed.

Lemma fw_w_is0_zero : w_is0 (0 : word) = true.
Proof. vm_compute. reflexivity. Qed.

(** With [newsp] zero -- which is what this program passes -- the child
    inherits the parent's stack and differs from it only in a0
    ([Procs.clone_child_sp] moves it only for a [clone] with a non-zero
    [newsp]). *)
Lemma fw_child_ms_eq : forall c c',
  ms_gpr (cfg_ms c) 1 = 0 ->
  child_ms c c' = set_reg (cfg_ms c') 10 (Z_to_bv 64 0).
Proof.
  intros c c' H1. unfold child_ms, clone_child_sp. cbv zeta.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; [|reflexivity].
  destruct (Z.eqb (bv_unsigned x8) 220%Z); [|reflexivity].
  rewrite H1, fw_w_is0_zero. reflexivity.
Qed.

(** An errno return is negative as a signed word, which is what sends
    the errno tail down [ForkwaitSteps.fw_run_fail]. *)
Lemma fw_errno_negative : forall r : word,
  ret_in_errnos clone_errnos r = true -> (bv_signed r < 0)%Z.
Proof.
  intros r H. unfold ret_in_errnos, clone_errnos in H.
  cbn [List.existsb] in H.
  repeat (apply orb_true_iff in H; destruct H as [H|H]);
    try discriminate;
    apply bv_eqb_true_eq in H; subst r; vm_compute; reflexivity.
Qed.

(** THE CLONE.  Either the environment declined -- and the one entry
    left carries the errno tail's remainder -- or the child exists and
    the successor is the two-entry shape. *)
Lemma fw_one_clone_step : forall cfg P evs P' e,
  pcfg_procs P = [(pe_pid e, e)] ->
  pcfg_root P = pe_pid e ->
  pe_parent e = None ->
  fw_model_ok (pe_model e) ->
  fw_q_clone (pe_ms e) ->
  pstep_cfg forkwait_segs cfg P evs (PNext P') ->
  fw_shape P' /\ (fw_mu P' < fw_mu P)%nat.
Proof.
  intros cfg P evs P' e Hp Hr Hpar Hh Hq Hstep.
  destruct Hq as (Hsv & Hpc & Ha0 & Ha1 & Hrv & Hsp & Hst).
  destruct Hstep as (p & Hstep).
  destruct (pstep_at_not_halted _ _ _ _ _ _ Hstep) as (e0 & Hl0 & _).
  destruct (fw_look_one P e p e0 Hp Hl0) as (He0 & _). subst e0.
  destruct (fw_entry_clone_step forkwait_segs cfg p P evs P' e 220
              Hl0 Hsv fw_two_twenty Ha0 Hh Hstep)
    as (eff & model'' & Hh'' & Hw & Hz & Hu & Hcp & Hdisj).
  set (cc := mkCfg (advance_past_svc (apply_effect (pe_ms e) eff)) model'').
  (* the four facts about the successor state both branches share *)
  assert (Hsv' : ms_svc_pending (cfg_ms cc) = None)
    by (unfold cc; apply fw_svc_after_effect).
  assert (Hrv' : ms_resv (cfg_ms cc) = None)
    by (unfold cc; apply fw_resv_after_effect).
  assert (Hpc' : bv_unsigned (ms_pc_val (cfg_ms cc)) = 0x1101c%Z).
  { unfold cc. cbn [cfg_ms]. rewrite fw_pc_after_effect.
    assert (Hpcw : ms_pc_val (pe_ms e) = 0x11018)
      by (apply bv_eq; rewrite Hpc; vm_compute; reflexivity).
    rewrite Hpcw. vm_compute. reflexivity. }
  assert (Hsp' : (16 <= bv_unsigned (getr (ms_regs (cfg_ms cc)) 2))%Z)
    by (unfold cc; cbn [cfg_ms]; rewrite fw_sp_after_effect; exact Hsp).
  assert (Ha0' : ms_gpr (cfg_ms cc) 0 = eff_ret eff)
    by (unfold cc; apply fw_a0_after_effect).
  assert (Hst' : store_ok forkwait_segs (ms_mem (cfg_ms cc))
                   (fw_slot (getr (ms_regs (cfg_ms cc)) 2)) 4 = true).
  { unfold cc. cbn [cfg_ms].
    rewrite (fw_mem_after_no_write (pe_ms e) eff Hw Hz Hu Hcp).
    rewrite fw_sp_after_effect. exact Hst. }
  assert (Hold : fw_entry_left e = 52%nat).
  { rewrite (fw_entry_left_pending e 220 (fw_model_ok_halted _ Hh) Hsv).
    unfold fw_const. rewrite fw_two_twenty. reflexivity. }
  destruct Hdisj as [(Herr & HP') | (Hlo & Hhi & Hfree & HP')]; subst P'.
  - (* declined: the one entry runs the errno tail to exit_group(7) *)
    assert (Hrem7 : fw_rem (pe_ms (pe_absorb e cc)) fw_q_exit7).
    { cbn [pe_ms pe_absorb].
      apply fw_fail_rem; [exact Hsv' | exact Hrv' | exact Hpc' |].
      rewrite Ha0'. apply fw_errno_negative. exact Herr. }
    destruct (absorb_one_entry P e cc Hp Hr) as (Hp' & Hr' & _).
    split.
    + right; right; left.
      exists (pe_absorb e cc).
      split; [exact Hp'|]. split; [exact Hr'|]. split; [exact Hpar|].
      split; [|exact Hrem7].
      cbn [pe_model pe_absorb cfg_model].
      exact (fw_model_ok_clear_shared _ Hh'').
    + apply (fw_mu_absorb_one_lt P e cc 17);
        [exact Hp | | rewrite Hold; lia].
      pose proof (fw_entry_left_bound (pe_absorb e cc) fw_q_exit7 94%Z
                    fw_q_exit7_nr Hrem7) as Hb.
      unfold fw_const in Hb. cbn in Hb. lia.
  - (* created: the two-entry shape, with both remainders *)
    assert (Hremw : fw_rem (cfg_ms cc) fw_q_wait4).
    { apply (fw_parent_rem (cfg_ms cc) (eff_ret eff));
        [exact Hsv' | exact Hrv' | exact Hpc' | exact Ha0'
         | exact Hlo | exact Hhi | exact Hsp' | exact Hst']. }
    assert (Hremc : fw_rem (pe_ms (child_entry e (pe_cfg (pcfg_shared P) e)
                                     cc (eff_ret eff))) fw_q_exit7).
    { unfold child_entry. cbn [pe_ms].
      rewrite (fw_child_ms_eq (pe_cfg (pcfg_shared P) e) cc Ha1).
      destruct (fw_set_reg10_frame (cfg_ms cc) (Z_to_bv 64 0))
        as (Hf1 & Hf2 & Hf3 & _ & _).
      apply fw_child_rem.
      - rewrite Hf1. exact Hsv'.
      - rewrite Hf2. exact Hrv'.
      - rewrite Hf3. exact Hpc'.
      - rewrite ms_gpr_set_reg_a0. apply fw_zero_word. }
    split.
    + right; left.
      apply (fw_clone_target P e cc (eff_ret eff));
        [exact Hp | exact Hr | exact Hpar | exact Hfree
         | exact Hh'' | exact Hremw | exact Hh | exact Hremc].
    + apply (fw_mu_clone_lt P e cc (eff_ret eff));
        [exact Hp | exact Hold | |].
      * pose proof (fw_entry_left_bound (pe_absorb e cc) fw_q_wait4 260%Z
                      fw_q_wait4_nr Hremw) as Hb.
        unfold fw_const in Hb. cbn in Hb. lia.
      * pose proof (fw_entry_left_bound
                      (child_entry e (pe_cfg (pcfg_shared P) e) cc
                         (eff_ret eff))
                      fw_q_exit7 94%Z fw_q_exit7_nr Hremc) as Hb.
        unfold fw_const in Hb. cbn in Hb. lia.
Qed.

(** THE REAP.  The zombie leaves the table and the parent is alone
    again, four steps from its own [exit_group].

    Two things are decided here rather than assumed.  WHICH ENTRY IS
    REAPED: the arm picks a [q] with a parent link to the waiter, and
    in a two-entry table whose other key is the parent's own that can
    only be the child.  AND THAT THE CHILD IS A ZOMBIE: [Procs.pe_status]
    answers [None] for a running entry, so the arm's own premise
    excludes the live half of [fw_child_st] -- the shape does not have
    to say which half it is in. *)
Lemma fw_two_reap : forall cfg P evs P' ep ec,
  pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)] ->
  pcfg_root P = pe_pid ep ->
  bv_eqb (pe_pid ep) (pe_pid ec) = false ->
  pe_parent ec = Some (pe_pid ep) ->
  pe_parent ep = None ->
  fw_model_ok (pe_model ep) ->
  fw_q_wait4 (pe_ms ep) ->
  fw_child_st ec ->
  pstep_at forkwait_segs cfg (pe_pid ep) P evs (PNext P') ->
  fw_shape P' /\ (fw_mu P' < fw_mu P)%nat.
Proof.
  intros cfg P evs P' ep ec Hp Hr Hne Hcpar Hppar Hh Hq Hch Hstep.
  destruct Hq as (Hsv & Hpc & Ha0 & Ha1 & Ha2 & Ha3 & Hrv & Hnw & Hslot).
  pose proof (fw_look_two_parent P ep ec Hp) as Hl.
  pose proof (fw_wait4_args (pe_ms ep) Ha0 Ha2 Ha3) as Hwa.
  destruct (fw_entry_reap_step forkwait_segs cfg (pe_pid ep) P evs P' ep
              260 (ms_gpr (pe_ms ep) 1) Hl Hsv fw_two_sixty Hwa Hstep)
    as (q & ez & status & model'' & dumped
        & Hlq & Hqne & Hpar' & Hkz & Hst & Hmat & HP').
  (* the reaped entry is the child, because the parent is excluded *)
  destruct (fw_look_two P ep ec q ez Hp Hlq) as [(Hez & Hqp) | (Hez & Hqc)].
  { exfalso. apply Hqne. exact Hqp. }
  subst ez q.
  (* and it is the zombie half of the child's shape *)
  assert (Hz : m_halted (pe_model ec) = Some (Z_to_bv 64 7)).
  { destruct Hch as [(Hhl & _) | (Hz0 & _)]; [|exact Hz0].
    unfold pe_status in Hst.
    rewrite (fw_model_ok_halted _ Hhl) in Hst. discriminate. }
  assert (Hstv : bv_unsigned status = 1792%Z).
  { unfold pe_status in Hst. rewrite Hz, Hkz in Hst.
    injection Hst as Hst. rewrite <- Hst. vm_compute. reflexivity. }
  subst P'.
  assert (Hrem7 : fw_rem
     (pe_ms (mkEntry (pe_pid ep) (pe_parent ep)
               (advance_past_svc
                  (apply_effect (pe_ms ep)
                     (mkEffect (pe_pid ec)
                        [(ms_gpr (pe_ms ep) 1,
                          Z_to_le_bytes 4 (bv_unsigned status))] [])))
               (clear_shared model'') (pe_ofd ep) (pe_nsctx ep)))
     fw_q_exit7).
  { cbn [pe_ms].
    apply (fw_reap_rem _ (ms_gpr (pe_ms ep) 1)).
    - apply fw_svc_after_effect.
    - apply fw_resv_after_effect.
    - rewrite fw_pc_after_effect.
      assert (Hpcw : ms_pc_val (pe_ms ep) = 0x1103c)
        by (apply bv_eq; rewrite Hpc; vm_compute; reflexivity).
      rewrite Hpcw. vm_compute. reflexivity.
    - rewrite fw_sp_after_effect. symmetry. exact Ha1.
    - rewrite fw_mem_after_write.
      apply fw_slot_read; [| rewrite Hstv; reflexivity].
      exact Hnw. }
  split.
  { apply (fw_reap_target _
           (mkEntry (pe_pid ep) (pe_parent ep)
              (advance_past_svc
                 (apply_effect (pe_ms ep)
                    (mkEffect (pe_pid ec)
                       [(ms_gpr (pe_ms ep) 1,
                         Z_to_le_bytes 4 (bv_unsigned status))] [])))
              (clear_shared model'') (pe_ofd ep) (pe_nsctx ep))).
    - cbn [pcfg_procs]. rewrite Hp.
      exact (fw_reap_target_table ep ec _ (pe_pid ec) Hne eq_refl).
    - cbn [pcfg_root]. exact Hr.
    - cbn [pe_parent]. exact Hppar.
    - cbn [pe_model].
      exact (fw_model_ok_clear_shared _
               (fw_model_ok_materialize _ _ _ Hmat
                  (fw_model_ok_pe_cfg _ ep Hh))).
    - exact Hrem7. }
  unfold fw_mu at 1. unfold pmeasure. cbn [pcfg_procs].
  apply (fw_mu_reap_lt P ep ec _ (pe_pid ec) Hp Hne eq_refl).
  - rewrite (fw_entry_left_pending ep 260 (fw_model_ok_halted _ Hh) Hsv).
    unfold fw_const. rewrite fw_two_sixty. reflexivity.
  - apply fw_entry_left_halted. rewrite Hz. discriminate.
  - pose proof (fw_entry_left_bound _ fw_q_exit7 94%Z fw_q_exit7_nr Hrem7)
      as Hb.
    apply (Nat.le_trans _ _ _ Hb). unfold fw_const. cbn. lia.
Qed.

(* =========================================================================
   No error: the refusing arms of the released step
   ========================================================================= *)

(** WITH NO CALL PENDING the two instruction refusals are decided by
    the remainder.  [Run.mi_account_step_no_lazy] says that with no
    lazy mapping the accounted step IS [RiscvSemantics.step], and the
    segment lemma behind the remainder proves that step is
    [MachineOk] -- so neither [MachineFault] nor [MachineUnmodeled] is
    reachable, and the statement's budget premise is not needed for
    this. *)
Lemma fw_no_sstep_error_instr : forall cfg S e ms1,
  m_vm_lazy (pe_model e) = [] ->
  ms_svc_pending (pe_ms e) = None ->
  RiscvSemantics.step forkwait_segs (pe_ms e) = MachineOk ms1 ->
  forall evs, ~ sstep_cfg forkwait_segs cfg (pe_cfg S e) evs SError.
Proof.
  intros cfg S e ms1 Hlz Hsv Hstep evs H.
  assert (Hacc : mi_account_step forkwait_segs (pe_ms e)
                   (cfg_model (pe_cfg S e))
                 = MachineOk (ms1, cfg_model (pe_cfg S e))).
  { rewrite (mi_account_step_no_lazy forkwait_segs (pe_ms e)
               (cfg_model (pe_cfg S e)) Hlz).
    rewrite Hstep. reflexivity. }
  cbn [pe_cfg cfg_model cfg_ms] in Hacc.
  inversion H; subst; cbn [pe_cfg cfg_model cfg_ms] in *; try congruence.
Qed.

(** WITH A CALL PENDING the two instruction arms are out by the number,
    the materialisation fault is out because materialising with no lazy
    mapping is the identity, and what is left is the spec answering
    [Unmodeled] -- which each of this program's two calls refuses for
    its own reason. *)
Lemma fw_no_sstep_error_call : forall cfg S e x8,
  ms_svc_pending (pe_ms e) = Some x8 ->
  (forall eff m' evs0,
     syscall_spec (sys_input forkwait_segs (pe_ms e) x8)
       (cfg_model (pe_cfg S e)) (Ok eff m' evs0) -> m_vm_lazy m' = []) ->
  ~ syscall_spec (sys_input forkwait_segs (pe_ms e) x8)
      (cfg_model (pe_cfg S e)) Unmodeled ->
  forall evs, ~ sstep_cfg forkwait_segs cfg (pe_cfg S e) evs SError.
Proof.
  intros cfg S e x8 Hsv Hlz Hum evs H.
  assert (Hx : forall y, ms_svc_pending (pe_ms e) = Some y -> y = x8)
    by (intros y Hy; rewrite Hsv in Hy; injection Hy; auto).
  inversion H; subst; try congruence.
  - (* the materialisation fault: with no lazy mapping it is the
       identity, so it cannot answer [None] *)
    match goal with
    | [ Hsv0 : ms_svc_pending (pe_ms e) = Some ?y,
        Hsp : syscall_spec _ _ (Ok ?ef ?m1 ?ev),
        Hmf : materialize_model_accesses ?m1 _ = None |- _ ] =>
        let Hy := fresh "Hy" in
        pose proof (Hx _ Hsv0) as Hy; subst y;
        rewrite (materialize_model_accesses_no_lazy m1 _ (Hlz _ _ _ Hsp))
          in Hmf; discriminate
    end.
  - (* the spec answering [Unmodeled] *)
    match goal with
    | [ Hsv0 : ms_svc_pending (pe_ms e) = Some ?y,
        Hsp : syscall_spec _ _ Unmodeled |- _ ] =>
        let Hy := fresh "Hy" in
        pose proof (Hx _ Hsv0) as Hy; subst y; exact (Hum Hsp)
    end.
Qed.

(** [Fork.clone_resolve] answers [Unmodeled] for ONE reason, its own
    gate, and the shape carries the gate open. *)
Lemma fw_clone_no_unmodeled : forall i m,
  clone_no_shared_file_b (m_fds m) = true ->
  ~ clone_resolve i m Unmodeled.
Proof.
  intros i m Hgate H.
  unfold clone_resolve, bind in H. cbv beta iota in H.
  destruct H as [Hg | (x & m1 & evs1 & Hg & Hk)].
  - unfold get_model in Hg. discriminate.
  - unfold get_model in Hg. injection Hg as Hx Hm1 He1. subst x m1.
    rewrite Hgate in Hk. cbn [negb] in Hk.
    destruct Hk as [Herr | Hpid].
    + unfold bind in Herr. cbv beta iota in Herr.
      destruct Herr as [He | (e0 & m2 & evsA & He & Her)].
      * unfold errno_from, choose in He.
        destruct He as (y & _ & Hy). discriminate.
      * unfold err_ret, ret_only, pure in Her. discriminate.
    + unfold bind in Hpid. cbv beta iota in Hpid.
      destruct Hpid as [Hc | (p & m2 & evsA & Hc & Hrest)].
      * unfold choose in Hc. destruct Hc as (y & _ & Hy). discriminate.
      * unfold bind in Hrest. cbv beta iota in Hrest.
        destruct Hrest as [Hmod | (u & m3 & evsC & Hmod & Hret)].
        -- unfold modify in Hmod. discriminate.
        -- unfold ret_only, pure in Hret. discriminate.
Qed.

Lemma fw_clone_spec_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 220%Z ->
  ms_gpr ms 0 = 17 ->
  clone_no_shared_file_b (m_fds model) = true ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model H220 Ha0 Hgate H.
  assert (Hno : bv_unsigned (in_sysno (sys_input segs ms x8)) = 220%Z)
    by (rewrite in_sysno_sys_input; exact H220).
  apply (proj1 (clone_is_clone_spec _ _ _ Hno)) in H.
  rewrite in_arg0_sys_input, Ha0 in H.
  unfold clone_spec in H.
  replace (clone_fork_flags_b 17) with true in H
    by (vm_compute; reflexivity).
  exact (fw_clone_no_unmodeled _ _ Hgate H).
Qed.

(** And [Exit.exit_spec] answers it never, which [Common.ExitSim]
    already proves. *)
Lemma fw_exit_spec_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 94%Z ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model H94.
  apply exit_dispatch_no_unmodeled.
  right. rewrite in_sysno_sys_input. exact H94.
Qed.

(** A remainder with steps left has a first step, which is what the
    instruction refusals are excluded against. *)
Lemma fw_rem_step_exists : forall ms Q,
  fw_q_pending Q -> fw_rem ms Q -> ms_svc_pending ms = None ->
  exists ms1, RiscvSemantics.step forkwait_segs ms = MachineOk ms1.
Proof.
  intros ms Q HQp (k & msf & Hk & Hrun & HQ) Hsv.
  destruct k as [|k].
  { cbn [machine_run] in Hrun. injection Hrun as <-.
    exfalso. exact (HQp _ HQ Hsv). }
  destruct (machine_run_inv _ _ _ _ Hrun) as (ms1 & _ & Hs1 & _).
  exists ms1. exact Hs1.
Qed.

(** THE ENTRY HEADING FOR THE CLONE cannot take the error transition:
    before the call the remainder's step excludes the two instruction
    refusals, and at the call the gate excludes [Unmodeled] and the
    empty lazy list excludes the materialisation fault. *)
Lemma fw_no_error_clone_entry : forall cfg S e,
  fw_model_ok (pe_model e) ->
  fw_rem (pe_ms e) fw_q_clone ->
  forall evs, ~ sstep_cfg forkwait_segs cfg (pe_cfg S e) evs SError.
Proof.
  intros cfg S e Hok Hrem evs.
  destruct Hok as (Hh & Hlz & Hgate & Htid).
  destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hsv.
  - assert (Hq : fw_q_clone (pe_ms e))
      by (apply (fw_rem_now _ _ Hrem); rewrite Hsv; discriminate).
    destruct Hq as (Hsv220 & _ & Ha0 & _).
    rewrite Hsv in Hsv220. injection Hsv220 as Hx8. subst x8.
    apply (fw_no_sstep_error_call cfg S e 220 Hsv).
    + intros eff m' evs0 Hsp.
      destruct (fw_clone_post forkwait_segs (pe_ms e) 220 _ eff m' evs0
                  fw_two_twenty Ha0 Hsp)
        as (_ & _ & _ & _ & _ & _ & Hokm & _).
      destruct (Hokm (conj Hh (conj Hlz (conj Hgate Htid))))
        as (_ & Hl' & _).
      exact Hl'.
    + apply (fw_clone_spec_no_unmodeled forkwait_segs (pe_ms e) 220);
        [apply fw_two_twenty | exact Ha0 | exact Hgate].
  - destruct (fw_rem_step_exists (pe_ms e) fw_q_clone fw_q_clone_pending
                Hrem Hsv) as (ms1 & Hs1).
    exact (fw_no_sstep_error_instr cfg S e ms1 Hlz Hsv Hs1 evs).
Qed.

(** AND THE ENTRY HEADING FOR ITS [exit_group], for the same two
    reasons, with [Common.ExitSim] supplying the refusal. *)
Lemma fw_no_error_exit7_entry : forall cfg S e,
  fw_model_ok (pe_model e) ->
  fw_rem (pe_ms e) fw_q_exit7 ->
  forall evs, ~ sstep_cfg forkwait_segs cfg (pe_cfg S e) evs SError.
Proof.
  intros cfg S e Hok Hrem evs.
  destruct Hok as (Hh & Hlz & Hgate & Htid).
  destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hsv.
  - assert (Hq : fw_q_exit7 (pe_ms e))
      by (apply (fw_rem_now _ _ Hrem); rewrite Hsv; discriminate).
    destruct Hq as (Hsv94 & _).
    rewrite Hsv in Hsv94. injection Hsv94 as Hx8. subst x8.
    apply (fw_no_sstep_error_call cfg S e 94 Hsv).
    + intros eff m' evs0 Hsp.
      rewrite (fw_exit_post forkwait_segs (pe_ms e) 94 _ eff m' evs0
                 fw_ninety_four Hsp).
      exact Hlz.
    + apply (fw_exit_spec_no_unmodeled forkwait_segs (pe_ms e) 94).
      apply fw_ninety_four.
  - destruct (fw_rem_step_exists (pe_ms e) fw_q_exit7 fw_q_exit7_pending
                Hrem Hsv) as (ms1 & Hs1).
    exact (fw_no_sstep_error_instr cfg S e ms1 Hlz Hsv Hs1 evs).
Qed.

(** THE SURFACE GUARD IS OPEN at every entry of this program, because
    the only numbers it issues are on the multi-process surface. *)
Lemma fw_guard_of_rem : forall P S e Q nr,
  (forall ms, Q ms -> exists x8, ms_svc_pending ms = Some x8
                                 /\ bv_unsigned x8 = nr) ->
  (nr = 220%Z \/ nr = 260%Z \/ nr = 94%Z) ->
  fw_rem (pe_ms e) Q ->
  multiproc_allowed P (pe_cfg S e) = true.
Proof.
  intros P S e Q nr Hnr Hin Hrem.
  destruct (ms_svc_pending (pe_ms e)) eqn:Hsv.
  - assert (HQ : Q (pe_ms e))
      by (apply (fw_rem_now _ _ Hrem); rewrite Hsv; discriminate).
    destruct (Hnr _ HQ) as (x8 & Hs & Hv).
    apply (fw_guard_open_at P _ nr). right.
    exists x8. split; [exact Hs|]. split; [exact Hv | exact Hin].
  - apply (fw_guard_open_at P _ nr). left. exact Hsv.
Qed.

(** THE [wait4] GATE IS CLOSED at an entry heading for any call but 260,
    because the gate needs a pending 260. *)
Lemma fw_not_owned_of_rem : forall P e Q nr,
  (forall ms, Q ms -> exists x8, ms_svc_pending ms = Some x8
                                 /\ bv_unsigned x8 = nr) ->
  nr <> 260%Z ->
  fw_rem (pe_ms e) Q ->
  wait4_owned_b P e = false.
Proof.
  intros P e Q nr Hnr Hne Hrem.
  destruct (ms_svc_pending (pe_ms e)) eqn:Hsv.
  - assert (HQ : Q (pe_ms e))
      by (apply (fw_rem_now _ _ Hrem); rewrite Hsv; discriminate).
    destruct (Hnr _ HQ) as (x8 & Hs & Hv).
    apply (wait4_owned_not_260 P e x8 Hs). rewrite Hv. exact Hne.
  - apply wait4_owned_instr. exact Hsv.
Qed.

(** THE NO-ERROR PREMISE.  Every shape's live entries are heading for
    one of the three calls; the guard is open at each, the two
    instruction refusals are excluded by the remainder, and the
    [Unmodeled] answers by the two spec facts above.  The one entry
    that could error is the parent parked at its [wait4], and both the
    released error arm and the [wait4] gate's refusal are behind the
    negation of the intercept guard that parks it -- which is 7.2 paying
    for itself a third time.  Every other entry is heading for 220 or 94,
    where the gate is closed.

    IT DOES NOT USE THE STATEMENT'S BUDGET PREMISE, and that is worth
    recording rather than leaving to be noticed.
    [Procs.pholts_within_budget] hands a caller
    [~ run_scfg_budget_refused ...], and the obvious route to the two
    fault arms is through it.  This proof takes another: with no lazy
    mapping the accounted step IS [RiscvSemantics.step]
    ([Run.mi_account_step_no_lazy]) and materialising IS the identity
    ([State.materialize_model_accesses_no_lazy]), so both faults are
    decided by the remainder and by [fw_model_ok], which are facts
    about the STATE.  The budget premise is still in the statement,
    where it belongs -- it is what the released shape carries -- but
    nothing here spends it, and a reader comparing this file with a
    single-process halting proof should not go looking for where it
    was used. *)
Theorem fw_no_error : forall cfg P evs,
  fw_shape P -> ~ pstep_cfg forkwait_segs cfg P evs PError.
Proof.
  intros cfg P evs Hsh (p & Hp).
  destruct (pstep_at_not_halted _ _ _ _ _ _ Hp) as (eh & Hlh & Hhh).
  destruct (pstep_error_cases _ _ _ _ _ Hp) as (e & Hl & Hpid & Hcase).
  destruct Hsh as [Hone | [Htwo | [Hex | Hhalt]]].
  - (* one entry heading for the clone *)
    destruct Hone as (e0 & Hp0 & Hr & Hpar & Hok & Hrem).
    destruct (fw_look_one P e0 p e Hp0 Hl) as (He & _). subst e.
    destruct Hcase as [(Hss & _) | [(Hg & _) | (Hrf & _)]].
    + exact (fw_no_error_clone_entry cfg (pcfg_shared P) e0 Hok Hrem evs Hss).
    + rewrite (fw_guard_of_rem P (pcfg_shared P) e0 fw_q_clone 220%Z
                 fw_q_clone_nr (or_introl eq_refl) Hrem) in Hg.
      discriminate.
    + rewrite (wait4_refused_not_owned _ _ _
                 (fw_not_owned_of_rem P e0 fw_q_clone 220%Z fw_q_clone_nr
                    ltac:(discriminate) Hrem)) in Hrf.
      discriminate.
  - (* two entries *)
    destruct Htwo as (ep & ec & Hp0 & Hr & Hne & Hcpar & Hppar & Hlp & Hch).
    destruct Hlp as (Hokp & Hremp).
    destruct (fw_look_two P ep ec p e Hp0 Hl) as [(He & _) | (He & _)];
      subst e.
    + (* the parent: at the wait4 the error arm is behind the guard *)
      destruct (ms_svc_pending (pe_ms ep)) as [x8|] eqn:Hsv.
      * assert (Hq : fw_q_wait4 (pe_ms ep))
          by (apply (fw_rem_now _ _ Hremp); rewrite Hsv; discriminate).
        destruct Hq as (Hsv260 & _ & Ha0 & _ & Ha2 & Ha3 & _).
        pose proof (fw_wait4_args (pe_ms ep) Ha0 Ha2 Ha3) as Hwa.
        assert (Hx : x8 = 260) by congruence.
        subst x8.
        destruct Hcase as [(_ & Hwi) | [(Hg & _) | (Hrf & _)]].
        -- rewrite (fw_wait4_intercept_true (pcfg_shared P) ep 260
                      (ms_gpr (pe_ms ep) 1) Hsv fw_two_sixty Hwa) in Hwi.
           discriminate.
        -- rewrite (fw_guard_of_rem P (pcfg_shared P) ep fw_q_wait4 260%Z
                      fw_q_wait4_nr (or_intror (or_introl eq_refl)) Hremp)
             in Hg.
           discriminate.
        -- rewrite (wait4_refused_intercept _ _ _
                      (fw_wait4_intercept_true (pcfg_shared P) ep 260
                         (ms_gpr (pe_ms ep) 1) Hsv fw_two_sixty Hwa)) in Hrf.
           discriminate.
      * destruct Hcase as [(Hss & _) | [(Hg & _) | (Hrf & _)]].
        -- destruct Hokp as (Hh & Hlz & Hgate & Htid).
           destruct (fw_rem_step_exists (pe_ms ep) fw_q_wait4
                       fw_q_wait4_pending Hremp Hsv) as (ms1 & Hs1).
           exact (fw_no_sstep_error_instr cfg (pcfg_shared P) ep ms1
                    Hlz Hsv Hs1 evs Hss).
        -- rewrite (fw_guard_of_rem P (pcfg_shared P) ep fw_q_wait4 260%Z
                      fw_q_wait4_nr (or_intror (or_introl eq_refl)) Hremp)
             in Hg.
           discriminate.
        -- rewrite (wait4_refused_not_owned _ _ _ (wait4_owned_instr P ep Hsv))
             in Hrf.
           discriminate.
    + (* the child: a zombie cannot step at all *)
      destruct Hch as [(Hokc & Hremc) | (Hz & _)].
      * destruct Hcase as [(Hss & _) | [(Hg & _) | (Hrf & _)]].
        -- exact (fw_no_error_exit7_entry cfg (pcfg_shared P) ec
                    Hokc Hremc evs Hss).
        -- rewrite (fw_guard_of_rem P (pcfg_shared P) ec fw_q_exit7 94%Z
                      fw_q_exit7_nr (or_intror (or_intror eq_refl)) Hremc)
             in Hg.
           discriminate.
        -- rewrite (wait4_refused_not_owned _ _ _
                      (fw_not_owned_of_rem P ec fw_q_exit7 94%Z fw_q_exit7_nr
                         ltac:(discriminate) Hremc)) in Hrf.
           discriminate.
      * rewrite Hl in Hlh. injection Hlh as Hlh. subst eh. congruence.
  - (* one entry heading for its exit_group *)
    destruct Hex as (e0 & Hp0 & Hr & Hpar & Hok & Hrem).
    destruct (fw_look_one P e0 p e Hp0 Hl) as (He & _). subst e.
    destruct Hcase as [(Hss & _) | [(Hg & _) | (Hrf & _)]].
    + exact (fw_no_error_exit7_entry cfg (pcfg_shared P) e0 Hok Hrem evs Hss).
    + rewrite (fw_guard_of_rem P (pcfg_shared P) e0 fw_q_exit7 94%Z
                 fw_q_exit7_nr (or_intror (or_intror eq_refl)) Hrem) in Hg.
      discriminate.
    + rewrite (wait4_refused_not_owned _ _ _
                 (fw_not_owned_of_rem P e0 fw_q_exit7 94%Z fw_q_exit7_nr
                    ltac:(discriminate) Hrem)) in Hrf.
      discriminate.
  - (* halted: the entry that stepped would have to be running *)
    destruct Hhalt as (e0 & c & Hp0 & Hrv & Hhc & _).
    destruct (fw_look_one P e0 p eh Hp0 Hlh) as (He & _). subst eh.
    unfold root_view in Hrv.
    destruct (look P (pcfg_root P)) as [er|] eqn:Hlr; [|discriminate Hrv].
    destruct (fw_look_one P e0 (pcfg_root P) er Hp0 Hlr) as (Her & _).
    subst er. injection Hrv as Hrv. subst c.
    rewrite m_halted_pe_cfg in Hhc. rewrite Hhh in Hhc. discriminate.
Qed.

(** The segment lemmas live inside [ForkwaitSteps]' [Section Forkwait]
    with [Context {fx : FPState}], so each takes the instance as its
    first implicit argument.  A consumer must supply it, and the way to
    supply it is the same section.  Without it the elaborator reports
    unresolved [?fx : FPState] holes and names neither the section nor
    the instance. *)
Section ForkwaitConsumers.
Context {fx : FPState}.

(** And the first fact in this file that CONSUMES a segment lemma.

    [ForkwaitSteps.fw_run_child] is a five-step run from [0x1101c] to the
    child's [exit_group] [ecall] at [0x11058].  Inverted once, it gives
    the child's FIRST step -- the [bltz] at [0x1101c], not taken because
    a0 is zero -- and a four-step run from wherever that lands.

    That is the shape the two-entry case analysis needs: one step for
    [fw_det_link], and the remainder to carry forward. *)
Lemma fw_child_first_step : forall regs mem rom,
  getr regs 10 = 0 ->
  exists ms',
    ms_svc_pending (mkst regs 0x1101c mem rom) = None
    /\ RiscvSemantics.step forkwait_segs (mkst regs 0x1101c mem rom)
       = MachineOk ms'
    /\ machine_run forkwait_segs 4 ms'
       = Some (ecall_st (fw_regs_exit7 regs) 0x11058 mem rom).
Proof.
  intros regs mem rom Ha0.
  apply machine_run_inv.
  exact (fw_run_child regs mem rom Ha0).
Qed.

(** PAIR ONE: the child steps, at every counter of its run.

    Inverting [fw_run_child] once gave the first step; inverting the
    remainder repeatedly gives the rest.  Each is an ordinary
    instruction, so each is one [fw_det_link] at the child's entry, with
    the parent carried across unchanged by [fw_two_other_record] and
    [fw_two_other_view] -- whose hypotheses [fw_instr_frames_shared]
    discharges, because an accounted instruction step fixes every model
    component.

    Stated as the existence of the run's steps rather than as a fold,
    for the reason [fw_det_link] is a link: the child's run and the
    parent's have different lengths. *)
Lemma fw_child_steps_exist : forall regs mem rom,
  getr regs 10 = 0 ->
  exists ms1 ms2 ms3 ms4,
    RiscvSemantics.step forkwait_segs (mkst regs 0x1101c mem rom)
      = MachineOk ms1
    /\ RiscvSemantics.step forkwait_segs ms1 = MachineOk ms2
    /\ RiscvSemantics.step forkwait_segs ms2 = MachineOk ms3
    /\ RiscvSemantics.step forkwait_segs ms3 = MachineOk ms4
    /\ machine_run forkwait_segs 1 ms4
       = Some (ecall_st (fw_regs_exit7 regs) 0x11058 mem rom).
Proof.
  intros regs mem rom Ha0.
  destruct (fw_child_first_step regs mem rom Ha0) as (ms1 & _ & Hs1 & Hr1).
  destruct (machine_run_inv _ _ _ _ Hr1) as (ms2 & _ & Hs2 & Hr2).
  destruct (machine_run_inv _ _ _ _ Hr2) as (ms3 & _ & Hs3 & Hr3).
  destruct (machine_run_inv _ _ _ _ Hr3) as (ms4 & _ & Hs4 & Hr4).
  exists ms1, ms2, ms3, ms4.
  split; [exact Hs1|]. split; [exact Hs2|]. split; [exact Hs3|].
  split; [exact Hs4 | exact Hr4].
Qed.

(** PAIR TWO: the parent steps, through its prologue to the [wait4].

    Nine steps, decomposed the same way.  Its hypotheses are the ones
    [ForkwaitSteps.fw_run_parent] asks for: a0 is the returned pid,
    bounded strictly between 0 and 2^22 by [Fork.clone_pid_ok_b], and
    the stack pointer is far enough above zero that the frame push does
    not wrap.  Both are what the [fw_two] shape carries at this counter,
    which is why pinning a0 was worth doing.

    Only the first step is named here: the rest follow by inverting the
    remainder, exactly as the child's did, and naming all nine would
    state nothing the inversion does not give. *)
Lemma fw_parent_first_step : forall regs mem rom (q sp : word),
  getr regs 10 = q ->
  getr regs 2 = sp ->
  (0 < bv_unsigned q)%Z ->
  (bv_unsigned q < 2 ^ 22)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  exists ms',
    ms_svc_pending (mkst regs 0x1101c mem rom) = None
    /\ RiscvSemantics.step forkwait_segs (mkst regs 0x1101c mem rom)
       = MachineOk ms'
    /\ machine_run forkwait_segs 8 ms'
       = Some (ecall_st (fw_regs_P regs sp) 0x1103c mem rom).
Proof.
  intros regs mem rom q sp Ha0 Hsp Hq0 Hq1 Hsp16.
  apply machine_run_inv.
  exact (fw_run_parent regs mem rom q sp Ha0 Hsp Hq0 Hq1 Hsp16).
Qed.

(** PAIR THREE: the parent's tail after the reap, four steps to the
    final [exit_group].  This is the deterministic stretch C, and its
    hypotheses are the reap's own output: the stack slot holds the
    status word the reap wrote, which [ForkwaitSteps.fw_slot_read]
    supplies from the write [Run.apply_effect] made. *)
Lemma fw_reap_tail_first_step : forall regs mem rom (sp : word),
  getr regs 2 = fw_slot sp ->
  rdn forkwait_segs mem (fw_slot sp) 4 = Some (Z_to_le_bytes 4 1792) ->
  exists ms',
    ms_svc_pending (mkst regs 0x11040 mem rom) = None
    /\ RiscvSemantics.step forkwait_segs (mkst regs 0x11040 mem rom)
       = MachineOk ms'
    /\ machine_run forkwait_segs 3 ms'
       = Some (ecall_st (fw_regs_C regs) 0x1104c mem rom).
Proof.
  intros regs mem rom sp Hsp Hrd.
  apply machine_run_inv.
  exact (fw_run_reap regs mem rom sp Hsp Hrd).
Qed.

(** THE TWO-ENTRY STEP, stated once for either entry.

    The first genuinely two-entry step lemma in this file.  Every other
    step lemma here is over [one_proc c], a singleton table, and none of
    them applies when two entries are live -- [pstep_single_next_bwd] is
    actually FALSE there, since with two entries the successor is not
    unique, which is why that stretch uses the measure rather than
    determinism.

    It is quantified over WHICH entry steps, so the child's case and the
    parent's case are instances rather than two copies.  [e] is the one
    that steps and [eo] the one that does not; nothing here says which
    is the parent.

    The frame half is the point: [eo]'s record survives by
    [fw_two_other_record] and its view by [fw_two_other_view], whose
    hypotheses [fw_instr_frames_shared] discharges out of
    [Run.mi_account_step_model_frame].  An instruction step of one entry
    is invisible to the other, which is what makes the interleaving
    finite to reason about. *)
Lemma fw_two_entry_step : forall segs cfg P e eo qo ms' model',
  look P (pe_pid e) = Some e ->
  look P qo = Some eo ->
  bv_eqb (pe_pid e) qo = false ->
  m_halted (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = None ->
  mi_account_step segs (pe_ms e) (cfg_model (pe_cfg (pcfg_shared P) e))
    = MachineOk (ms', model') ->
  (* the step happens, at the entry that stepped *)
  pstep_at segs cfg (pe_pid e) P []
    (PNext (absorb P e (mkCfg ms' model')))
  (* and the other entry is untouched, in both senses *)
  /\ look (absorb P e (mkCfg ms' model')) qo = Some eo
  /\ pe_cfg (pcfg_shared (absorb P e (mkCfg ms' model'))) eo
     = pe_cfg (pcfg_shared P) eo.
Proof.
  intros segs cfg P e eo qo ms' model' Hl Hlo Hne Hh Hs Hm.
  split; [exact (pstep_instr_entry segs cfg P e ms' model' Hl Hh Hs Hm)|].
  assert (Hrun : m_halted (cfg_model (mkCfg ms' model')) = None).
  { destruct (mi_account_step_model_frame _ _ _ _ _ Hm)
      as (_ & _ & _ & _ & _ & Hproc & _).
    cbn [cfg_model]. unfold m_halted in *. rewrite Hproc. exact Hh. }
  assert (Hlo' : look (absorb P e (mkCfg ms' model')) qo = Some eo)
    by exact (fw_two_other_record P e (mkCfg ms' model') qo eo Hne Hlo
                (or_introl Hrun)).
  split; [exact Hlo'|].
  (* the view: an accounted instruction step fixes every model
     component, so the shared file system and I/O are unchanged and
     [view_frame_absorb]'s hypotheses hold *)
  destruct (fw_instr_frames_shared segs (pe_ms e)
              (cfg_model (pe_cfg (pcfg_shared P) e)) ms' model' Hm)
    as (Hfs & Hio).
  apply (fw_two_other_view P e (mkCfg ms' model') qo eo Hlo').
  - cbn [cfg_model]. rewrite Hfs. reflexivity.
  - cbn [cfg_model]. rewrite Hio. reflexivity.
Qed.

(** THE PAIR THAT WAS BLOCKED: the child steps while the parent waits.

    This is the row where only one entry has an arm, and the reason is
    7.2: a parent parked at the [wait4] [ecall] with no eligible zombie
    has no arm at all, not a blocked flag.  So the system's progress
    here is the CHILD's step, and [fw_two_entry_step] supplies both
    halves of it -- the transition, and the parent coming through
    untouched.

    Instantiated with [e] the child and [eo] the parent, which is the
    other order from the rows where the parent runs; that the same
    lemma serves both is what quantifying over the stepping entry
    bought. *)
Lemma fw_child_steps_parent_waits :
  forall segs cfg P ec ep qp ms' model',
  look P (pe_pid ec) = Some ec ->
  look P qp = Some ep ->
  bv_eqb (pe_pid ec) qp = false ->
  (* the child is running, with no call pending *)
  m_halted (pe_model ec) = None ->
  ms_svc_pending (pe_ms ec) = None ->
  mi_account_step segs (pe_ms ec) (cfg_model (pe_cfg (pcfg_shared P) ec))
    = MachineOk (ms', model') ->
  (* then the system steps, and the waiting parent is exactly as it was *)
  pstep_cfg segs cfg P [] (PNext (absorb P ec (mkCfg ms' model')))
  /\ look (absorb P ec (mkCfg ms' model')) qp = Some ep
  /\ pe_cfg (pcfg_shared (absorb P ec (mkCfg ms' model'))) ep
     = pe_cfg (pcfg_shared P) ep.
Proof.
  intros segs cfg P ec ep qp ms' model' Hlc Hlp Hne Hh Hs Hm.
  destruct (fw_two_entry_step segs cfg P ec ep qp ms' model'
              Hlc Hlp Hne Hh Hs Hm) as (Hstep & Hrec & Hview).
  split; [exact (pstep_at_sub _ _ _ _ _ _ Hstep)|].
  split; [exact Hrec | exact Hview].
Qed.

(** And its progress consequence, which is the premise
    [must_exit_in_p_at_by_measure] asks for at this shape: the system
    can step, supplied by the entry that is not blocked.  Proved through
    [fw_progress_from_entry] rather than reproved. *)
Lemma fw_progress_parent_waits :
  forall segs cfg P ec ms' model',
  look P (pe_pid ec) = Some ec ->
  m_halted (pe_model ec) = None ->
  ms_svc_pending (pe_ms ec) = None ->
  mi_account_step segs (pe_ms ec) (cfg_model (pe_cfg (pcfg_shared P) ec))
    = MachineOk (ms', model') ->
  exists evs st, pstep_cfg segs cfg P evs st.
Proof.
  intros segs cfg P ec ms' model' Hl Hh Hs Hm.
  exact (fw_progress_from_entry segs cfg P (pe_pid ec) []
           (PNext (absorb P ec (mkCfg ms' model')))
           (pstep_instr_entry segs cfg P ec ms' model' Hl Hh Hs Hm)).
Qed.

(** THE ASSEMBLY.

    Each shape is split by whether its entry's remainder has run out.
    While it has not, the step is an ordinary one and
    [fw_one_rem_step], [fw_two_parent_step] or [fw_two_child_step]
    carries the remainder across.  When it has, the shape itself says
    which call is pending, and the arm that call admits is forced:
    [fw_one_clone_step] at 220, [fw_one_exit_step] and
    [fw_two_child_exit] at 94, [fw_two_reap] at 260.  The halted shape
    cannot step at all.

    Nine cases, and no case analysis on the twenty-three program
    counters: that is what the remainder shapes bought. *)
Definition fw_lands_in_shape (segs : list Segment) (cfg : SpuriousCfg)
    : Prop :=
  forall P evs P',
    fw_shape P ->
    pstep_cfg segs cfg P evs (PNext P') ->
    fw_shape P'.

(** The two premises travel together because they are decided by the
    same nine cases: one case analysis, two conclusions. *)
Theorem fw_lands_and_mu : forall cfg P evs P',
  fw_shape P ->
  pstep_cfg forkwait_segs cfg P evs (PNext P') ->
  fw_shape P' /\ (fw_mu P' < fw_mu P)%nat.
Proof.
  intros cfg P evs P' Hsh Hstep.
  destruct Hsh as [Hone | [Htwo | [Hex | Hhalt]]].
  - (* one entry, the clone's [ecall] ahead of it *)
    destruct Hone as (e & Hp & Hr & Hpar & Hh & Hrem).
    destruct (ms_svc_pending (pe_ms e)) eqn:Hsv.
    + assert (Hq : fw_q_clone (pe_ms e))
        by (apply (fw_rem_now _ _ Hrem); rewrite Hsv; discriminate).
      exact (fw_one_clone_step cfg P evs P' e Hp Hr Hpar Hh Hq Hstep).
    + destruct (fw_one_rem_step cfg P evs P' fw_q_clone e
                  fw_q_clone_pending Hp Hr Hpar Hh Hrem Hsv Hstep)
        as (Hs & Hm).
      split; [left; exact Hs | exact Hm].
  - (* two entries *)
    destruct Htwo as (ep & ec & Hp & Hr & Hne & Hcpar & Hppar & Hlp & Hch).
    destruct Hstep as (p & Hstep).
    destruct (pstep_at_not_halted _ _ _ _ _ _ Hstep) as (e0 & Hl0 & Hh0).
    destruct (fw_look_two P ep ec p e0 Hp Hl0) as [(He & Hq) | (He & Hq)];
      subst e0 p.
    + (* the parent stepped *)
      destruct Hlp as (Hhp & Hremp).
      destruct (ms_svc_pending (pe_ms ep)) eqn:Hsv.
      * assert (Hq4 : fw_q_wait4 (pe_ms ep))
          by (apply (fw_rem_now _ _ Hremp); rewrite Hsv; discriminate).
        exact (fw_two_reap cfg P evs P' ep ec Hp Hr Hne Hcpar Hppar
                 Hhp Hq4 Hch Hstep).
      * destruct (fw_two_parent_step cfg P evs P' ep ec Hp Hr Hne Hcpar
                    Hppar Hhp Hremp Hsv Hch Hstep) as (Hs & Hm).
        split; [right; left; exact Hs | exact Hm].
    + (* the child stepped; the zombie half cannot, by 7.2 *)
      destruct Hch as [Hlive | (Hz & _)];
        [| exfalso; rewrite Hz in Hh0; discriminate].
      destruct Hlive as (Hhc & Hremc).
      destruct (ms_svc_pending (pe_ms ec)) eqn:Hsv.
      * assert (Hq7 : fw_q_exit7 (pe_ms ec))
          by (apply (fw_rem_now _ _ Hremc); rewrite Hsv; discriminate).
        destruct Hq7 as (Hsv7 & Ha07).
        destruct (fw_two_child_exit cfg P evs P' ep ec Hp Hr Hne Hcpar
                    Hppar Hlp (fw_model_ok_halted _ Hhc) Hsv7 Ha07 Hstep)
          as (Hs & Hm).
        split; [right; left; exact Hs | exact Hm].
      * destruct (fw_two_child_step cfg P evs P' ep ec Hp Hr Hne Hcpar
                    Hppar Hlp Hhc Hremc Hsv Hstep) as (Hs & Hm).
        split; [right; left; exact Hs | exact Hm].
  - (* one entry, its own [exit_group] ahead of it *)
    destruct Hex as (e & Hp & Hr & Hpar & Hh & Hrem).
    destruct (ms_svc_pending (pe_ms e)) eqn:Hsv.
    + assert (Hq : fw_q_exit7 (pe_ms e))
        by (apply (fw_rem_now _ _ Hrem); rewrite Hsv; discriminate).
      destruct Hq as (Hsv7 & Ha07).
      destruct (fw_one_exit_step cfg P evs P' e Hp Hr
                  (fw_model_ok_halted _ Hh) Hsv7 Ha07 Hstep)
        as (Hs & Hm).
      split; [right; right; right; exact Hs | exact Hm].
    + destruct (fw_one_rem_step cfg P evs P' fw_q_exit7 e
                  fw_q_exit7_pending Hp Hr Hpar Hh Hrem Hsv Hstep)
        as (Hs & Hm).
      split; [right; right; left; exact Hs | exact Hm].
  - (* halted: every arm needs a running entry *)
    exfalso.
    destruct Hhalt as (e & c & Hp & Hrv & Hhc & _).
    destruct Hstep as (p & Hstep).
    destruct (pstep_at_not_halted _ _ _ _ _ _ Hstep) as (e0 & Hl0 & Hh0).
    destruct (fw_look_one P e p e0 Hp Hl0) as (He0 & _). subst e0.
    unfold root_view in Hrv.
    destruct (look P (pcfg_root P)) as [er|] eqn:Hlr; [|discriminate Hrv].
    destruct (fw_look_one P e (pcfg_root P) er Hp Hlr) as (Her & _).
    subst er. injection Hrv as Hrv. subst c.
    rewrite m_halted_pe_cfg in Hhc. rewrite Hh0 in Hhc. discriminate.
Qed.

Theorem fw_lands : forall cfg, fw_lands_in_shape forkwait_segs cfg.
Proof.
  intros cfg P evs P' Hsh Hstep.
  exact (proj1 (fw_lands_and_mu cfg P evs P' Hsh Hstep)).
Qed.

Theorem fw_mu_decreases : forall cfg P evs P',
  fw_shape P ->
  pstep_cfg forkwait_segs cfg P evs (PNext P') ->
  (fw_mu P' < fw_mu P)%nat.
Proof.
  intros cfg P evs P' Hsh Hstep.
  exact (proj2 (fw_lands_and_mu cfg P evs P' Hsh Hstep)).
Qed.
(* =========================================================================
   The start state
   ========================================================================= *)

(** THE STACK POINTER IS FAR ABOVE SIXTEEN, under every address-space
    declaration the model admits: the window's floor is
    [State.va_sp_window_lo], two gigabytes below the stack top, and the
    smallest of the three tops is Sv39's.  So the no-wrap side
    condition [ForkwaitSteps.fw_run_parent] needs for the frame push is
    a fact about the ENTRY WINDOW rather than about the program. *)
Lemma fw_va_window_lo_16 : forall v, (16 <= va_sp_window_lo v)%Z.
Proof. intros v. destruct v; vm_compute; discriminate. Qed.

Lemma fw_sp_at_least_16 : forall v sp,
  valid_sp_va v sp -> (16 <= bv_unsigned sp)%Z.
Proof.
  intros v sp (Hlo & _ & _). pose proof (fw_va_window_lo_16 v). lia.
Qed.

(** AND THE SHAPE AT [execve].  [MustExitP.pinit_config] is [one_proc]
    over [Run.init_config], so the table is a single entry; the entry
    point is the image's own [0x11000], no call is pending, the
    reservation is clear because [Run.init_machine_state] sets it so,
    and what is left is the seven steps of [ForkwaitSteps.fw_run_A].

    THE WINDOW BELOW THE STACK POINTER IS NOT SIMPLY [sp - 8 MiB].
    [Run.stack_window_lo] counts RLIMIT_STACK from the stack VMA's end
    [StackLayout.ed_top] and takes the HIGHER of that and the guard gap
    above the mmap base, so a bound on [sp] alone does not reach it.
    [Common.StoreOk.stack_window_lo_valid] is what does: under an
    admissible launch the floor is at or below [sp - 6144513], which is
    well under the sixteen bytes the status slot sits at.  That lemma
    wants [Run.valid_launch] and [Sv48], which is why this takes
    [Run.valid_input] -- the statement's second premise, until now
    unused. *)
Lemma fw_shape_at_pinit : forall sp brk0 mbase rnd lim inp,
  valid_entry (mkImage ForkwaitMemImage_loaded_segments
                       ForkwaitMemImage_init_pc ForkwaitMemImage_phdrs)
              (Run.mkEntry sp brk0 mbase rnd) inp ->
  valid_input inp ->
  fw_shape (pinit_config ForkwaitMemImage_loaded_segments
              ForkwaitMemImage_init_pc ForkwaitMemImage_phdrs
              sp brk0 mbase rnd lim inp).
Proof.
  intros sp brk0 mbase rnd lim inp Hve Hvi.
  assert (Hva : in_va_size inp = Sv48)
    by (destruct Hvi as (_&_&_&_&_&_&_&_&_&_&_&_& H &_); exact H).
  assert (Hvl : valid_launch inp)
    by (destruct Hvi as (_&_&_&_&_&_&_&_&_&_&_&_&_&_& H); exact H).
  unfold valid_entry, valid_entry_va in Hve. rewrite Hva in Hve.
  destruct Hve as (Hsp & _ & _ & _ & Hlau).
  unfold pinit_config. left.
  apply fw_shape_one_proc;
    [split; [reflexivity|]; split; [reflexivity|];
     split; [reflexivity | reflexivity]|].
  assert (Hsp16 : (16 <= bv_unsigned sp)%Z)
    by exact (fw_sp_at_least_16 _ sp Hsp).
  assert (Hwlo : (stack_window_lo (in_kernel inp) mbase rnd
                  <= bv_unsigned sp + stack_window_reach - stack_max_size)%Z)
    by exact (stack_window_lo_valid inp sp brk0 mbase rnd Hvl Hlau).
  assert (Hregs : getr (ms_regs (cfg_ms
                     (init_config ForkwaitMemImage_loaded_segments
                        ForkwaitMemImage_init_pc ForkwaitMemImage_phdrs
                        sp brk0 mbase rnd lim inp))) 2 = sp).
  { cbn [cfg_ms init_config init_machine_state ms_regs].
    change (bvmap_set 2 sp (bvmap_set 10 (Z_to_bv 64 0) bvmap_empty))
      with (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp).
    getr_resolve. reflexivity. }
  apply fw_start_rem.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - rewrite Hregs. exact Hsp16.
  - (* THE STATUS SLOT IS WRITABLE: the launch zero-maps the window
       below the entry stack pointer, and the slot is sixteen bytes
       below it. *)
    rewrite Hregs.
    apply store_ok_of_all.
    + rewrite fw_slot_addr by exact Hsp16.
      pose proof (bv_unsigned_in_range 64 sp) as Hr.
      change (bv_modulus 64) with (2 ^ 64)%Z in Hr. lia.
    + intros x Hx. rewrite fw_slot_addr in Hx by exact Hsp16.
      cbn [cfg_ms init_config init_machine_state ms_mem] in *.
      unfold wview.
      match goal with
      | [ |- context[stack_to_mem ?a ?b x] ] =>
          destruct (stack_to_mem a b x) as [bb|] eqn:Estk; [discriminate|]
      end.
      rewrite (proj2 (Z.leb_le _ _))
        by (unfold stack_window_reach, stack_max_size in Hwlo; lia).
      rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      cbn. discriminate.
Qed.

(** Given it, preservation is immediate -- it IS it.  Stated as its own
    name so the dependency is visible rather than buried. *)
Theorem fw_shape_preserved_of_lands : forall segs cfg,
  fw_lands_in_shape segs cfg -> fw_shape_preserved segs cfg.
Proof. intros segs cfg H P evs P' Hsh Hs. exact (H P evs P' Hsh Hs). Qed.

(** And the whole chain, with that as the single remaining hypothesis.

    Everything else is discharged: the base case by
    [fw_shape_one_proc], the leaf by [fw_shape_terminal_halted], the
    measure at the two shape-changing steps by [fw_measure_clone] and
    [fw_measure_reap], no-error by [fw_no_error], and progress by
    [fw_progress_from_entry]. *)
Theorem forkwait_halts_of_lands : forall segs cfg P0 mu,
  fw_lands_in_shape segs cfg ->
  fw_shape P0 ->
  (forall P, fw_shape P -> terminal P ->
     exists c code, root_view P = Some c
                    /\ m_halted (cfg_model c) = Some code
                    /\ List.In code [Z_to_bv 64 7]
                    /\ m_killed (cfg_model c) = None) ->
  (forall P, fw_shape P -> terminalb P = false ->
     exists evs st, pstep_cfg segs cfg P evs st) ->
  (forall P evs, fw_shape P -> ~ pstep_cfg segs cfg P evs PError) ->
  (forall P evs P', fw_shape P -> pstep_cfg segs cfg P evs (PNext P') ->
     (mu P' < mu P)%nat) ->
  must_exit_in_p_at segs cfg [Z_to_bv 64 7] P0.
Proof.
  intros segs cfg P0 mu Hlands H0 Hleaf Hprog Hnoerr Hdec.
  apply (forkwait_halts_of_preserved segs cfg [Z_to_bv 64 7] P0 mu);
    [ apply fw_shape_preserved_of_lands; exact Hlands
    | exact H0 | exact Hleaf | exact Hprog | exact Hnoerr | exact Hdec ].
Qed.

(* =========================================================================
   Progress: the step each state admits, BUILT rather than inverted
   ========================================================================= *)

(** WITH NO CALL PENDING the instruction arm fires, and the remainder
    supplies its result. *)
Lemma fw_progress_instr : forall cfg P e ms1,
  look P (pe_pid e) = Some e ->
  m_halted (pe_model e) = None ->
  m_vm_lazy (pe_model e) = [] ->
  ms_svc_pending (pe_ms e) = None ->
  RiscvSemantics.step forkwait_segs (pe_ms e) = MachineOk ms1 ->
  exists evs st, pstep_cfg forkwait_segs cfg P evs st.
Proof.
  intros cfg P e ms1 Hl Hh Hlz Hsv Hstep.
  assert (Hacc : mi_account_step forkwait_segs (pe_ms e)
                   (cfg_model (pe_cfg (pcfg_shared P) e))
                 = MachineOk (ms1, cfg_model (pe_cfg (pcfg_shared P) e))).
  { rewrite (mi_account_step_no_lazy forkwait_segs (pe_ms e)
               (cfg_model (pe_cfg (pcfg_shared P) e)) Hlz).
    rewrite Hstep. reflexivity. }
  exact (fw_progress_from_entry forkwait_segs cfg P (pe_pid e) []
           (PNext (absorb P e (mkCfg ms1
                     (cfg_model (pe_cfg (pcfg_shared P) e)))))
           (pstep_instr_entry forkwait_segs cfg P e ms1 _ Hl Hh Hsv Hacc)).
Qed.

(** AT AN [exit_group] the terminal arm fires, and the outcome is the
    one [Common.ExitSim] names: [exit_spec] has no other. *)
Lemma fw_progress_exit : forall cfg P e,
  look P (pe_pid e) = Some e ->
  m_halted (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = Some 94 ->
  multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
  exists evs st, pstep_cfg forkwait_segs cfg P evs st.
Proof.
  intros cfg P e Hl Hh Hsv Hma.
  set (m := cfg_model (pe_cfg (pcfg_shared P) e)).
  set (code := bv_and (ms_gpr (pe_ms e) 0) (Z_to_bv 64 255)).
  assert (Hspec : syscall_spec (sys_input forkwait_segs (pe_ms e) 94) m
                    (Ok (mkEffect (Z_to_bv 64 0) [] [])
                        (with_halted code m) [])).
  { apply exit_dispatch_ok.
    right. rewrite in_sysno_sys_input. apply fw_ninety_four. }
  assert (Hss : sstep_cfg forkwait_segs cfg (pe_cfg (pcfg_shared P) e)
                  ([] ++ [ExitEv code (m_fs (with_halted code m))])
                  (SNext (mkCfg (pe_ms e) (with_halted code m)))).
  { apply (sstep_cfg_exit forkwait_segs cfg (pe_ms e) m 94
             (mkEffect (Z_to_bv 64 0) [] []) (with_halted code m) [] code);
      [exact Hh | exact Hsv | exact Hspec
       | apply fw_m_halted_with_halted | apply fw_m_killed_with_halted]. }
  exists ([] ++ [ExitEv code (m_fs (with_halted code m))]),
         (PNext (absorb P e (mkCfg (pe_ms e) (with_halted code m)))).
  exists (pe_pid e).
  apply (pstep_other forkwait_segs cfg P e _
           (mkCfg (pe_ms e) (with_halted code m)));
    [exact Hl | exact Hss | | | exact Hma | ].
  - unfold clone_success_b. cbn [cfg_ms pe_cfg]. rewrite Hsv.
    rewrite fw_ninety_four. reflexivity.
  - unfold wait4_intercept_b. cbn [cfg_ms pe_cfg]. rewrite Hsv.
    rewrite fw_ninety_four. reflexivity.
  - apply (wait4_owned_not_260 P e 94 Hsv). rewrite fw_ninety_four. discriminate.
Qed.

(** A FRESH PID EXISTS, and it is chosen rather than searched for: the
    table a clone fires at has ONE entry, and [m_tid] is [None] by the
    shape, so the envelope's first two values cannot both be taken. *)
Lemma fw_neq_of_eqb : forall x y : word, bv_eqb x y = false -> x <> y.
Proof.
  intros x y H E. subst y. rewrite bv_eqb_same in H. discriminate.
Qed.

Lemma fw_fresh_pid : forall a : word,
  exists p : word,
    (0 < bv_unsigned p)%Z /\ (bv_unsigned p < PID_MAX_ENVELOPE)%Z /\ p <> a.
Proof.
  intros a. destruct (bv_eqb (1 : word) a) eqn:E.
  - apply bv_eqb_true_eq in E. exists 2.
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    rewrite <- E. apply fw_neq_of_eqb. vm_compute. reflexivity.
  - exists 1.
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    apply fw_neq_of_eqb. exact E.
Qed.

(** A PID IS NOT AN ERRNO.  Every member of [Fork.clone_errnos] encodes
    just under 2^64 and the envelope stops at 2^22, so the two readings
    can never collide ([Run.refusal_b] reads this one;
    [Procs.clone_success_b] reads the error encoding,
    [fw_envelope_not_error]). *)
Lemma fw_pid_not_errno : forall r : word,
  (bv_unsigned r < PID_MAX_ENVELOPE)%Z ->
  ret_in_errnos clone_errnos r = false.
Proof.
  intros r Hr.
  destruct (ret_in_errnos clone_errnos r) eqn:E; [|reflexivity].
  exfalso. unfold ret_in_errnos in E.
  apply List.existsb_exists in E. destruct E as (e & He & Hb).
  apply bv_eqb_true_eq in Hb. subst r.
  unfold clone_errnos in He. cbn [List.In] in He.
  destruct He as [<-|[<-|[<-|[<-|[]]]]]; vm_compute in Hr; discriminate.
Qed.

(** The pid gate, with the tid clause the shape carries. *)
Lemma fw_clone_pid_ok : forall m (p : word),
  m_tid m = None ->
  (0 < bv_unsigned p)%Z -> (bv_unsigned p < PID_MAX_ENVELOPE)%Z ->
  clone_pid_ok_b m p = true.
Proof.
  intros m p Ht Hlo Hhi. unfold clone_pid_ok_b. rewrite Ht.
  rewrite Bool.andb_true_r. apply andb_true_iff.
  split; [apply Z.ltb_lt; exact Hlo | apply Z.ltb_lt; exact Hhi].
Qed.

(** THE OUTCOME THE CLONE ADMITS, built out of the monad rather than
    inverted out of it: [Fork.clone_resolve]'s admitting alternative,
    at a pid the gate accepts. *)
Lemma fw_clone_resolve_ok : forall i m (p : word),
  clone_no_shared_file_b (m_fds m) = true ->
  clone_pid_ok_b m p = true ->
  clone_resolve i m (Ok (mkEffect p [] []) (with_children m) []).
Proof.
  intros i m p Hgate Hok.
  unfold clone_resolve, bind. cbv beta iota.
  exists m, m, [], []. split; [reflexivity|]. split; [|reflexivity].
  rewrite Hgate. cbn [negb]. right.
  unfold bind. cbv beta iota.
  exists p, m, [], [].
  split; [exists p; split; [exact Hok | reflexivity]|].
  split; [|reflexivity].
  unfold bind. cbv beta iota.
  exists tt, (with_children m), [], [].
  split; [reflexivity|]. split; [reflexivity | reflexivity].
Qed.

Lemma fw_clone_spec_ok : forall segs ms x8 model (p : word),
  bv_unsigned x8 = 220%Z ->
  ms_gpr ms 0 = 17 ->
  clone_no_shared_file_b (m_fds model) = true ->
  clone_pid_ok_b model p = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect p [] []) (with_children model) []).
Proof.
  intros segs ms x8 model p H220 Ha0 Hgate Hok.
  assert (Hno : bv_unsigned (in_sysno (sys_input segs ms x8)) = 220%Z)
    by (rewrite in_sysno_sys_input; exact H220).
  apply (proj2 (clone_is_clone_spec _ _ _ Hno)).
  rewrite in_arg0_sys_input, Ha0. unfold clone_spec.
  replace (clone_fork_flags_b 17) with true by (vm_compute; reflexivity).
  apply fw_clone_resolve_ok; assumption.
Qed.

(** AND THE OUTCOME IS NOT A SPURIOUS REFUSAL, which is what
    [Run.sstep_cfg_syscall] asks at [Run.forced_only_cfg].  A pid is
    not one of [Fork.clone_errnos], so [Run.refusal_b] answers [false],
    and [Run.spurious_refusal_not_refusal] closes it whatever the
    environment says about the family. *)
Lemma fw_refusal_b_pid : forall i m (r : word),
  bv_unsigned (in_sysno i) = 220%Z ->
  (bv_unsigned r < PID_MAX_ENVELOPE)%Z ->
  refusal_b i m r = false.
Proof.
  intros i m r Hno Hr. unfold refusal_b. cbv zeta. rewrite Hno.
  change (Z.eqb 220 214) with false. cbv iota.
  destruct (injected_arm 220%Z) as [a|] eqn:Ea; [|reflexivity].
  vm_compute in Ea. injection Ea as Ea. subst a. cbn [ia_errnos].
  apply fw_pid_not_errno. exact Hr.
Qed.

(** AT THE CLONE the admitting alternative fires: a fresh pid inside
    the envelope, an outcome the environment does not refuse, and a
    materialisation that is the identity. *)
Lemma fw_progress_clone : forall cfg P e,
  pcfg_procs P = [(pe_pid e, e)] ->
  look P (pe_pid e) = Some e ->
  fw_model_ok (pe_model e) ->
  ms_svc_pending (pe_ms e) = Some 220 ->
  ms_gpr (pe_ms e) 0 = 17 ->
  multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
  exists evs st, pstep_cfg forkwait_segs cfg P evs st.
Proof.
  intros cfg P e Hp Hl Hok Hsv Ha0 Hma.
  destruct Hok as (Hh & Hlz & Hgate & Htid).
  destruct (fw_fresh_pid (pe_pid e)) as (q & Hlo & Hhi & Hne).
  set (m := cfg_model (pe_cfg (pcfg_shared P) e)).
  assert (Hpid : clone_pid_ok_b m q = true)
    by (apply fw_clone_pid_ok; [exact Htid | exact Hlo | exact Hhi]).
  assert (Hspec : syscall_spec (sys_input forkwait_segs (pe_ms e) 220) m
                    (Ok (mkEffect q [] []) (with_children m) []))
    by (apply fw_clone_spec_ok;
        [apply fw_two_twenty | exact Ha0 | exact Hgate | exact Hpid]).
  assert (Hnr : ~ spurious_refusal_cfg cfg
                   (sys_input forkwait_segs (pe_ms e) 220) m
                   (mkEffect q [] [])).
  { apply spurious_refusal_not_refusal. cbn [eff_ret].
    apply fw_refusal_b_pid;
      [rewrite in_sysno_sys_input; apply fw_two_twenty | exact Hhi]. }
  assert (Hmat : materialize_model_accesses (with_children m)
                   (syscall_effect_accesses (mkEffect q [] []))
                 = Some (with_children m))
    by (apply materialize_model_accesses_no_lazy; exact Hlz).
  assert (Hss : sstep_cfg forkwait_segs cfg (pe_cfg (pcfg_shared P) e) []
                  (SNext (mkCfg (advance_past_svc
                                   (apply_effect (pe_ms e) (mkEffect q [] [])))
                                (with_children m)))).
  { apply (sstep_cfg_syscall forkwait_segs cfg (pe_ms e) m 220
             (mkEffect q [] []) (with_children m) (with_children m) []);
      [exact Hh | exact Hsv | exact Hspec | exact Hnr | exact Hh | exact Hmat]. }
  set (c' := mkCfg (advance_past_svc
                      (apply_effect (pe_ms e) (mkEffect q [] [])))
                   (with_children m)).
  assert (Ha0' : ms_gpr (cfg_ms c') 0 = q)
    by (unfold c'; apply fw_a0_after_effect).
  exists [], (PNext (clone_result P e c' q)). exists (pe_pid e).
  apply (pstep_clone forkwait_segs cfg P e [] c' q);
    [exact Hl | exact Hss | | split; [exact Ha0' | exact I] | | exact Hma].
  - unfold clone_success_b. cbn [cfg_ms pe_cfg]. rewrite Hsv, fw_two_twenty.
    cbn [clone_sysno]. rewrite Ha0', (fw_envelope_not_error q Hlo Hhi). reflexivity.
  - unfold look. rewrite Hp. cbn [look_in fst snd].
    destruct (bv_eqb (pe_pid e) q) eqn:Eb; [|reflexivity].
    exfalso. apply Hne. symmetry. exact (bv_eqb_true_eq _ _ _ Eb).
Qed.

(** AT THE [wait4] WITH THE ZOMBIE PRESENT the reap arm fires, and it
    is the only state whose step needs anything of MEMORY: the arm
    copies the status out, so the slot has to be writable.  That is
    the clause [fw_q_wait4] carries, and [Common.StoreOk.store_ok_wbuf]
    turns it into the arm's own [read_bytes_map] premise. *)
Lemma fw_progress_reap : forall cfg P ep ec,
  pcfg_procs P = [(pe_pid ep, ep); (pe_pid ec, ec)] ->
  bv_eqb (pe_pid ep) (pe_pid ec) = false ->
  pe_parent ec = Some (pe_pid ep) ->
  fw_model_ok (pe_model ep) ->
  fw_q_wait4 (pe_ms ep) ->
  m_halted (pe_model ec) = Some (Z_to_bv 64 7) ->
  m_killed (pe_model ec) = None ->
  exists evs st, pstep_cfg forkwait_segs cfg P evs st.
Proof.
  intros cfg P ep ec Hp Hne Hcpar Hok Hq Hz Hk.
  destruct Hq as (Hsv & Hpc & Ha0 & Ha1 & Ha2 & Ha3 & Hrv & Hnw & Hslot).
  destruct Hok as (Hh & Hlz & Hgate & Htid).
  pose proof (fw_look_two_parent P ep ec Hp) as Hl.
  pose proof (fw_look_two_child P ep ec Hp Hne) as Hlc.
  pose proof (fw_wait4_args (pe_ms ep) Ha0 Ha2 Ha3) as Hwa.
  pose proof (fw_wait4_intercept_true (pcfg_shared P) ep 260
                (ms_gpr (pe_ms ep) 1) Hsv fw_two_sixty Hwa) as Hwi.
  assert (Hqne : pe_pid ec <> pe_pid ep).
  { intro E. rewrite E in Hne. rewrite bv_eqb_same in Hne. discriminate. }
  assert (Hst : pe_status false ec
                = Some (bv_mul (bv_and (Z_to_bv 64 7) (Z_to_bv 64 255))
                               (Z_to_bv 64 256)))
    by (unfold pe_status; rewrite Hz, Hk; reflexivity).
  assert (Hwm : read_bytes_map
                  (in_wmem (sys_input forkwait_segs (pe_ms ep) 260))
                  (ms_gpr (pe_ms ep) 1) (Z_to_bv 64 4) <> None).
  { rewrite in_wmem_sys_input.
    destruct (store_ok_wbuf forkwait_segs (pe_ms ep) (ms_gpr (pe_ms ep) 1)
                (Z_to_bv 64 4)) as (w & Hw).
    - replace (word_to_nat (Z_to_bv 64 4)) with 4%nat
        by (vm_compute; reflexivity).
      exact Hslot.
    - rewrite Hw. discriminate. }
  assert (Hmat : materialize_model_accesses
                   (cfg_model (pe_cfg (pcfg_shared P) ep))
                   (syscall_effect_accesses
                      (mkEffect (pe_pid ec)
                         [(ms_gpr (pe_ms ep) 1,
                           Z_to_le_bytes 4
                             (bv_unsigned
                                (bv_mul (bv_and (Z_to_bv 64 7)
                                                (Z_to_bv 64 255))
                                        (Z_to_bv 64 256))))] []))
                 = Some (cfg_model (pe_cfg (pcfg_shared P) ep)))
    by (apply materialize_model_accesses_no_lazy; exact Hlz).
  eexists. eexists. exists (pe_pid ep).
  eapply pstep_wait_reap;
    [exact Hl | exact Hh | exact Hsv | exact Hwi | exact Hwa | exact Hlc
     | exact Hqne | exact Hcpar | exact Hk | exact Hst | exact Hwm
     | reflexivity | exact Hmat].
Qed.

(** THE PROGRESS PREMISE.  Below terminal, some entry can step, and
    which one is decided by the shape: a running entry steps by its
    instruction, an entry at a call by that call's arm, and the only
    state where the entry the shape names CANNOT step is the parent
    parked at its [wait4] with the child still running -- where the
    child steps instead. *)
Theorem fw_progress : forall cfg P,
  fw_shape P -> terminalb P = false ->
  exists evs st, pstep_cfg forkwait_segs cfg P evs st.
Proof.
  intros cfg P Hsh Ht.
  destruct Hsh as [Hone | [Htwo | [Hex | Hhalt]]].
  - (* one entry, the clone ahead of it *)
    destruct Hone as (e & Hp & Hr & Hpar & Hok & Hrem).
    pose proof (fw_look_one_self P e Hp) as Hl.
    destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hsv.
    + assert (Hq : fw_q_clone (pe_ms e))
        by (apply (fw_rem_now _ _ Hrem); rewrite Hsv; discriminate).
      destruct Hq as (Hsv220 & _ & Ha0 & _).
      apply (fw_progress_clone cfg P e Hp Hl Hok Hsv220 Ha0).
      exact (fw_guard_of_rem P (pcfg_shared P) e fw_q_clone 220%Z
               fw_q_clone_nr (or_introl eq_refl) Hrem).
    + destruct (fw_rem_step_exists (pe_ms e) fw_q_clone fw_q_clone_pending
                  Hrem Hsv) as (ms1 & Hs1).
      destruct Hok as (Hh & Hlz & _ & _).
      exact (fw_progress_instr cfg P e ms1 Hl Hh Hlz Hsv Hs1).
  - (* two entries: the child moves unless it is the zombie *)
    destruct Htwo as (ep & ec & Hp & Hr & Hne & Hcpar & Hppar & Hlp & Hch).
    destruct Hch as [(Hokc & Hremc) | (Hz & Hkz)].
    + pose proof (fw_look_two_child P ep ec Hp Hne) as Hlc.
      destruct (ms_svc_pending (pe_ms ec)) as [x8|] eqn:Hsv.
      * assert (Hq : fw_q_exit7 (pe_ms ec))
          by (apply (fw_rem_now _ _ Hremc); rewrite Hsv; discriminate).
        destruct Hq as (Hsv94 & _).
        apply (fw_progress_exit cfg P ec Hlc
                 (fw_model_ok_halted _ Hokc) Hsv94).
        exact (fw_guard_of_rem P (pcfg_shared P) ec fw_q_exit7 94%Z
                 fw_q_exit7_nr (or_intror (or_intror eq_refl)) Hremc).
      * destruct (fw_rem_step_exists (pe_ms ec) fw_q_exit7
                    fw_q_exit7_pending Hremc Hsv) as (ms1 & Hs1).
        destruct Hokc as (Hh & Hlz & _ & _).
        exact (fw_progress_instr cfg P ec ms1 Hlc Hh Hlz Hsv Hs1).
    + destruct Hlp as (Hokp & Hremp).
      pose proof (fw_look_two_parent P ep ec Hp) as Hl.
      destruct (ms_svc_pending (pe_ms ep)) as [x8|] eqn:Hsv.
      * assert (Hq : fw_q_wait4 (pe_ms ep))
          by (apply (fw_rem_now _ _ Hremp); rewrite Hsv; discriminate).
        exact (fw_progress_reap cfg P ep ec Hp Hne Hcpar Hokp Hq Hz Hkz).
      * destruct (fw_rem_step_exists (pe_ms ep) fw_q_wait4
                    fw_q_wait4_pending Hremp Hsv) as (ms1 & Hs1).
        destruct Hokp as (Hh & Hlz & _ & _).
        exact (fw_progress_instr cfg P ep ms1 Hl Hh Hlz Hsv Hs1).
  - (* one entry, its own exit_group ahead of it *)
    destruct Hex as (e & Hp & Hr & Hpar & Hok & Hrem).
    pose proof (fw_look_one_self P e Hp) as Hl.
    destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hsv.
    + assert (Hq : fw_q_exit7 (pe_ms e))
        by (apply (fw_rem_now _ _ Hrem); rewrite Hsv; discriminate).
      destruct Hq as (Hsv94 & _).
      apply (fw_progress_exit cfg P e Hl (fw_model_ok_halted _ Hok) Hsv94).
      exact (fw_guard_of_rem P (pcfg_shared P) e fw_q_exit7 94%Z
               fw_q_exit7_nr (or_intror (or_intror eq_refl)) Hrem).
    + destruct (fw_rem_step_exists (pe_ms e) fw_q_exit7 fw_q_exit7_pending
                  Hrem Hsv) as (ms1 & Hs1).
      destruct Hok as (Hh & Hlz & _ & _).
      exact (fw_progress_instr cfg P e ms1 Hl Hh Hlz Hsv Hs1).
  - (* halted: the configuration IS terminal, so there is nothing to
       show -- the premise is below terminal *)
    exfalso.
    destruct Hhalt as (e & c & Hp & Hrv & Hhc & _).
    unfold root_view in Hrv.
    destruct (look P (pcfg_root P)) as [er|] eqn:Hlr; [|discriminate Hrv].
    destruct (fw_look_one P e (pcfg_root P) er Hp Hlr) as (Her & _).
    subst er. injection Hrv as Hrv. subst c.
    rewrite m_halted_pe_cfg in Hhc.
    unfold terminalb in Ht. rewrite Hp in Ht.
    cbn [List.forallb snd] in Ht. unfold pe_zombie in Ht.
    rewrite Hhc in Ht. discriminate.
Qed.

(* =========================================================================
   The chain, with every premise discharged
   ========================================================================= *)

(** [fw_lands] is preservation, [fw_shape_terminal_halted] the leaf,
    [fw_progress] progress, [fw_no_error] no error and
    [fw_mu_decreases] the measure.  Nothing is left for a caller to
    supply but the shape at the start, and [fw_shape_at_pinit] gives
    that from the entry window. *)
Theorem forkwait_halts_at : forall cfg P0,
  fw_shape P0 ->
  must_exit_in_p_at forkwait_segs cfg [Z_to_bv 64 7] P0.
Proof.
  intros cfg P0 H0.
  apply (forkwait_halts_of_lands forkwait_segs cfg P0 fw_mu);
    [ apply fw_lands | exact H0 | exact fw_shape_terminal_halted
    | intros P Hsh Ht; exact (fw_progress cfg P Hsh Ht)
    | intros P evs Hsh; exact (fw_no_error cfg P evs Hsh)
    | intros P evs P' Hsh Hs; exact (fw_mu_decreases cfg P evs P' Hsh Hs) ].
Qed.

End ForkwaitConsumers.

(* =========================================================================
   The statement
   ========================================================================= *)

(** THE CLAIM [Statement.forkwait_halts] MAKES, PROVED.

    THE BUDGET PREMISE IS NOT USED.  The two fault arms it is there for
    are closed by the state instead -- see the note at [fw_no_error] --
    and it stays in the statement because the statement is the RELEASED
    shape, and one that drops a premise is no longer comparable with
    the one-process halting claims it is meant to sit beside.

    [Run.valid_input] IS used, for one thing: the stack window below
    the entry pointer, whose floor needs [Run.valid_launch] and [Sv48]
    ([fw_shape_at_pinit]). *)
Theorem forkwait_halts_proved : forkwait_halts.
Proof.
  intros en inp Hve Hvi _.
  destruct en as [sp brk0 mbase rnd].
  apply forkwait_halts_at.
  apply fw_shape_at_pinit; [exact Hve | exact Hvi].
Qed.
