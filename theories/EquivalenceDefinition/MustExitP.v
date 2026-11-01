(** * EquivalenceDefinition.MustExitP — halting, for a system of processes

    PROOF-SIDE SIBLING OF [MustExit].  [MustExit.must_exit_in_at] says every
    maximal execution of ONE process halts on an allowed code; this file says
    the same of a whole system of them, over [Procs.pstep_at].

    WHY IT IS HERE AND NOT IN [LinuxProcessSem.Procs], where it was first
    written: the useful theorems about it relate it to the released
    one-process predicate, and [MustExit] lives in this directory while
    [Procs] lives in the one this directory depends on.  A predicate stated
    beside the relation but PROVED beside the released predicate has to be in
    the directory that can see both, and that is this one.  Nothing else
    moved with it. *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   Termination of the whole system
   ========================================================================= *)

(** The system is over: every entry still in the table is halted.  A reaped
    entry is not in the table at all. *)
Definition terminal (P : pconfig) : Prop :=
  List.Forall (fun kv => pe_zombie (snd kv) <> None) (pcfg_procs P).

(** Every maximal execution halts, after finitely many steps, with the ROOT
    halted on a code in [S] and nothing still running.

    The recursive arm fires whenever the system is NOT TERMINAL -- not merely
    while the root runs.  Requiring the root to run there would reject a
    family that terminates cleanly: if the root exits normally while a child
    still has an instruction and an exit to go, the leaf's condition is not
    yet met and the root is no longer running, so neither arm could fire.

    The scheduler is not a new quantifier.  It is the entry each step picks,
    and the fourth premise ranges over every pick, so EVERY INTERLEAVING is
    covered and no fairness is assumed.  What carries the induction is this
    predicate's own well-founded derivation tree, exactly as for
    [MustExit.must_exit_in_at].  A program whose child loops forever gives an
    infinite chain and is refuted rather than excused; that is the right
    answer for a program with no way to stop the child, and a kill arm is
    what a program that does have one will need. *)
Inductive must_exit_in_p_at (segs : list Segment) (cfg : SpuriousCfg)
    (S : list word) : pconfig -> Prop :=
| mepa_halted : forall P c code,
    root_view P = Some c ->
    m_halted (cfg_model c) = Some code ->
    List.In code S ->
    m_killed (cfg_model c) = None ->
    terminal P ->
    must_exit_in_p_at segs cfg S P
| mepa_running : forall P,
    ~ terminal P ->
    (exists evs st, pstep_cfg segs cfg P evs st) ->
    (forall evs, ~ pstep_cfg segs cfg P evs PError) ->
    (forall evs P', pstep_cfg segs cfg P evs (PNext P') ->
                    must_exit_in_p_at segs cfg S P') ->
    must_exit_in_p_at segs cfg S P.

Lemma terminal_one_proc : forall c,
  terminal (one_proc c) <-> m_halted (cfg_model c) <> None.
Proof.
  intros c. unfold terminal, one_proc, one_entry, pe_zombie. cbn. split.
  - intros H. inversion H as [|x l Hx Hr]; subst. exact Hx.
  - intros H. constructor; [exact H | constructor].
Qed.

(* =========================================================================
   What a consumer's lineage restriction needs
   ========================================================================= *)

(** Two facts about the table operations, proved here because nothing else
    states them: replacing keeps the length, dropping does not raise it. *)
Lemma replace_in_length : forall ps p e,
  List.length (replace_in ps p e) = List.length ps.
Proof.
  induction ps as [|kv r IH]; intros p e; cbn; [reflexivity|].
  destruct (bv_eqb (fst kv) p); cbn; [reflexivity | f_equal; apply IH].
Qed.

Lemma drop_in_length_le : forall ps p,
  (List.length (drop_in ps p) <= List.length ps)%nat.
Proof.
  induction ps as [|kv r IH]; intros p; cbn; [apply Nat.le_refl|].
  destruct (bv_eqb (fst kv) p); cbn.
  - apply Nat.le_succ_diag_r.
  - apply le_n_S. apply IH.
Qed.

(** The lineage this core offers a consumer: the LAST entry of the table.
    [clone_result] appends the child, so "the lineage" is "the most recently
    created process", which is what a child-lineage walk follows.  A
    one-process system has only its one entry, [one_pid]. *)
Definition lineage_pick (P : pconfig) (p : Pid) : Prop :=
  p = List.last (List.map fst (pcfg_procs P)) (pcfg_root P).

(** L9. *)
Lemma lineage_pick_one : forall c p,
  lineage_pick (one_proc c) p <-> p = one_pid.
Proof.
  intros c p. unfold lineage_pick, one_proc. cbn.
  split; intros H; exact H.
Qed.

(** L11: a successful clone with a free child pid is a step of the system. *)
Theorem pstep_clone_law : forall segs cfg P e evs c' q,
  look P (pe_pid e) = Some e ->
  sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
  clone_success_b (pe_cfg (pcfg_shared P) e) c' = true ->
  child_pid_core c' q ->
  look P q = None ->
  multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
  pstep_cfg segs cfg P evs (PNext (clone_result P e c' q)).
Proof.
  intros segs cfg P e evs c' q H1 H2 H3 H4 H5 H6.
  apply pstep_at_sub with (p := pe_pid e).
  apply pstep_clone; assumption.
Qed.

(** The child a clone appends has a0 = 0: that is what [child_ms] writes,
    with [set_reg]'s PHYSICAL register 10, which is a0, read back at
    [ms_gpr]'s ARGUMENT index 0, which is the same register. *)
(** Reading argument index 0 after writing physical register 10 gives the
    value written: the two numberings meet at a0, and [cbn] does not see it
    because the register file is a trie over an abstract map. *)
(** [ms_gpr]'s key is [Z_to_bv 5 (10 + Z.of_nat i)] and [set_reg]'s is the
    literal, and the two are convertible but not syntactically equal, so
    [rewrite] cannot match [bvmap_get_set_same] against them.  These two
    variants take the key equality as a side goal, which [reflexivity]
    discharges by conversion. *)
Lemma bvmap_get_set_same' {n A} (k k' : bv n) (x : A) m :
  k = k' -> bvmap_get k' (bvmap_set k x m) = Some x.
Proof. intros ->. apply bvmap_get_set_same. Qed.

Lemma bvmap_get_set_other' {n A} (k k' : bv n) (x : A) m :
  k <> k' -> bvmap_get k' (bvmap_set k x m) = bvmap_get k' m.
Proof. intros Hne. apply bvmap_get_set_other. exact Hne. Qed.

Lemma ms_gpr_set_reg_a0 : forall ms v, ms_gpr (set_reg ms 10 v) 0 = v.
Proof.
  intros ms v. unfold ms_gpr, set_reg, reg_get. simpl.
  (* the two key spellings are equal but NOT convertible: a [bv] numeral is
     not [Z_to_bv], so the equality goes through [bv_eq], which is equality
     of the unsigned readings. *)
  erewrite bvmap_get_set_same' by (apply bv_eq; reflexivity). reflexivity.
Qed.

(** And writing the stack pointer afterwards does not disturb it: x2 is not
    x10. *)
Lemma ms_gpr_set_reg_sp_a0 : forall ms v w,
  ms_gpr (set_reg (set_reg ms 10 v) 2 w) 0 = v.
Proof.
  intros ms v w. unfold ms_gpr, set_reg, reg_get. simpl.
  erewrite bvmap_get_set_other'
    by (intros Hk; apply (f_equal bv_unsigned) in Hk; discriminate).
  erewrite bvmap_get_set_same' by (apply bv_eq; reflexivity). reflexivity.
Qed.

Lemma child_entry_a0_zero : forall e c c' q,
  entry_a0_zero (child_entry e c c' q).
Proof.
  intros e c c' q.
  unfold entry_a0_zero, child_entry, child_ms. cbn [pe_ms].
  destruct (w_is0 (ms_gpr (cfg_ms c) 1)).
  - apply ms_gpr_set_reg_a0.
  - apply ms_gpr_set_reg_sp_a0.
Qed.

(* =========================================================================
   The run-level statement
   ========================================================================= *)

(** The system a released [execve] starts: one process, pid [one_pid]. *)
Definition pinit_config (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (sp brk0 mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput)
    : pconfig :=
  one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp).

(** The same MATCH on the image and the entry that [MustExit.must_exit_in]
    and [Run.run] use, so that all three always speak about the same run.
    [Run.mkEntry] is qualified because this file's own [mkEntry] builds a
    [ProcessEntry]. *)
Definition must_exit_in_p (cfg : SpuriousCfg) (S : list word) (img : Image)
    (lim : Z) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, Run.mkEntry sp brk0 mbase rnd =>
      must_exit_in_p_at segs cfg S
        (pinit_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

(** The multi-process reading of the shape the released halting statements
    use -- [HaltsAllowed.halts_allowed_T_scfg_budgets] at
    [Run.forced_only_cfg] -- with the whole-system predicate in place of the
    one-process one.  Same quantifier, same environment, same budget
    premise; only the predicate moves. *)
Definition pholts_within_budget (lim : Z) (allowed : list word) (img : Image)
    : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry img en inp ->
    valid_input inp ->
    ~ run_scfg_budget_refused forced_only_cfg img lim en inp ->
    must_exit_in_p forced_only_cfg allowed img lim en inp.

(* =========================================================================
   Carrying a released one-process proof onto the system
   ========================================================================= *)

(** THE BRIDGE THIS FILE EXISTS FOR, and the operational form of the claim
    that this development leaves every published statement alone.

    A released halting proof is about [MustExit.must_exit_in_at_cfg] over
    [Run.sstep_cfg].  This says that such a proof carries, unchanged, to the
    whole-system predicate over [Procs.pstep_at] — so a one-process program
    that halts in the released model halts in this one, with no new work and
    no new axiom.

    THE TWO HYPOTHESES ARE THE TWO PLACES THE RELATIONS DIFFER, and they are
    the same two [Procs.pstep_single_next] names: a successful clone, and the
    blocking [wait4] the released model answers [unmodeled].  A program that
    does neither is covered; a program that does either is what the rest of
    this file is for.  They are hypotheses rather than a side condition
    because they are decidable facts about the configurations the run
    reaches, not assumptions about the world. *)

(** The two configurations at which this relation and the released one
    differ, as one decidable test: a step that is a successful clone, and a
    pending blocking [wait4].  Named here because the bridge below will
    quantify it over the reachable set, and because it is the same pair
    [Procs.pstep_single_next] carries. *)
Definition quiet_at (c : config) : Prop :=
  (forall segs cfg evs c', sstep_cfg segs cfg c evs (SNext c') ->
     clone_success_b c c' = false)
  /\ wait4_intercept_b c = false.

(** A one-entry system is terminal exactly when its process is halted. *)
Lemma terminal_one_proc_iff : forall c,
  terminal (one_proc c) <-> m_halted (cfg_model c) <> None.
Proof. exact terminal_one_proc. Qed.

(** The root of a one-entry system is the configuration it was built from. *)
Lemma root_view_one_proc : forall c, root_view (one_proc c) = Some c.
Proof.
  intros c. unfold root_view.
  rewrite one_proc_entry. rewrite one_proc_view. reflexivity.
Qed.

(** NOT YET PROVED, and deliberately neither axiomatised nor left
    [Admitted]: this repository bans both (tools/gen_checker.py rejects
    [Admitted], [Axiom] and [Parameter] in a proof file), and a theorem
    nobody has proved is worth less than the note saying so.

    The bridge this file exists for is

      (every configuration the run reaches satisfies [quiet_at]) ->
      must_exit_in_at_cfg cfg segs S c ->
      must_exit_in_p_at segs cfg S (one_proc c)

    the operational form of the claim that this development leaves every
    published one-process statement alone: a released halting proof would
    carry to the whole-system predicate with no new work and no new axiom.

    Its halted case is already discharged by [root_view_one_proc] and
    [terminal_one_proc_iff] above.  What is open is the running case's three
    premises -- progress, error-freedom, and every successor -- each of
    which needs the released step transported through
    [Procs.pstep_single_next] and [Procs.pstep_single_err] under a
    reachability hypothesis this file does not yet define.  Written down
    unproved and clearly marked, rather than claimed. *)
