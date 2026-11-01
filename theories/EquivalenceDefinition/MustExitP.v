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

From Stdlib Require Import ZArith NArith List Bool Lia.
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

(* =========================================================================
   Non-interference: what one entry's step leaves alone
   ========================================================================= *)

(** THE FOUNDATION OF THE TWO-ENTRY ARGUMENT.  After the clone there are two
    live entries, and the reason their interleaving does not explode is that
    a step of one leaves the other's entry untouched.  Everything else in
    that argument -- the measure, the commutation -- rests on these three
    lemmas, which are about the table alone and need no invariant: replacing
    or dropping the entry at one key leaves every other key's lookup exactly
    as it was.

    Note what is NOT needed: key uniqueness.  [drop_in] removes the first
    entry at its key, and a lookup at a different key cannot be affected by
    that whether or not the table repeats a key.  Uniqueness is in
    [Procs.pconfig_wf] for other reasons, and this argument does not spend
    it. *)

Lemma look_in_replace_other : forall ps p q e',
  bv_eqb p q = false ->
  look_in (replace_in ps p e') q = look_in ps q.
Proof.
  induction ps as [|kv r IH]; intros p q e' Hne; cbn; [reflexivity|].
  destruct (bv_eqb (fst kv) p) eqn:H1; cbn.
  - apply bv_eqb_true_eq in H1. subst p. rewrite Hne. reflexivity.
  - destruct (bv_eqb (fst kv) q); [reflexivity | apply IH; exact Hne].
Qed.

Lemma look_in_drop_other : forall ps p q,
  bv_eqb p q = false ->
  look_in (drop_in ps p) q = look_in ps q.
Proof.
  induction ps as [|kv r IH]; intros p q Hne; cbn; [reflexivity|].
  destruct (bv_eqb (fst kv) p) eqn:H1; cbn.
  - apply bv_eqb_true_eq in H1. subst p. rewrite Hne. reflexivity.
  - destruct (bv_eqb (fst kv) q); [reflexivity | apply IH; exact Hne].
Qed.

(** An ordinary step of one entry leaves every other entry's lookup alone.
    [absorb] replaces exactly the stepping entry and rebuilds the shared
    state; the table is untouched at every other key. *)
Lemma look_absorb_other : forall P e c' q,
  bv_eqb (pe_pid e) q = false ->
  look (absorb P e c') q = look P q.
Proof.
  intros P e c' q Hne. unfold look, absorb. cbn.
  apply look_in_replace_other. exact Hne.
Qed.

(** A clone leaves every entry but the parent and the new child alone: it
    replaces the parent and appends, and an append is invisible to a lookup
    that already succeeds. *)
Lemma look_in_app_hit : forall ps ps' q e,
  look_in ps q = Some e -> look_in (ps ++ ps') q = Some e.
Proof.
  induction ps as [|kv r IH]; intros ps' q e H; cbn in *; [discriminate|].
  destruct (bv_eqb (fst kv) q); [exact H | apply IH; exact H].
Qed.

(* =========================================================================
   The shared-state half of non-interference
   ========================================================================= *)

(** The table lemmas above say the OTHER entry's record survives a step.
    They do not yet say its VIEW survives, and those are different claims:
    [absorb] rebuilds [sh_fsys] and [sh_io] from the stepping entry's
    successor, and every other entry reads exactly those through [pe_cfg].

    SO THE LEMMA IS ABOUT THE ARM, NOT ABOUT [absorb].  An arm that leaves
    the file system and the I/O state alone leaves every other entry's view
    alone; an arm that does not, does not, and no amount of reasoning about
    the table will rescue it.  The non-touching is a HYPOTHESIS here and the
    instances below discharge it by computation.

    A general "every step preserves every other view" is a different theorem
    and a false one, which is the point: a shared file system is shared.
    When the pipe syscalls arrive this is the lemma they will have to fail. *)
Lemma view_frame_absorb : forall P e c' q eq,
  look (absorb P e c') q = Some eq ->
  m_fsys (cfg_model c') = sh_fsys (pcfg_shared P) ->
  m_io (cfg_model c') = sh_io (pcfg_shared P) ->
  pe_cfg (pcfg_shared (absorb P e c')) eq = pe_cfg (pcfg_shared P) eq.
Proof.
  intros P e c' q eq _ Hfs Hio.
  unfold pe_cfg, absorb, shared_absorb. cbn [pcfg_shared sh_fsys sh_io].
  rewrite Hfs, Hio. reflexivity.
Qed.

(** The two arms [forkwait] steps with, and why each satisfies it.  Both
    model setters rebuild [State.Model] around the same [m_fsys] and
    [m_io], so each is a [reflexivity]. *)
Lemma m_fsys_with_halted : forall v m, m_fsys (with_halted v m) = m_fsys m.
Proof. reflexivity. Qed.

Lemma m_io_with_halted : forall v m, m_io (with_halted v m) = m_io m.
Proof. reflexivity. Qed.

Lemma m_fsys_with_children : forall m, m_fsys (with_children m) = m_fsys m.
Proof. reflexivity. Qed.

Lemma m_io_with_children : forall m, m_io (with_children m) = m_io m.
Proof. reflexivity. Qed.

(** And the splice puts the shared pair into the view, so a step that starts
    from [pe_cfg S e] starts from a model whose [m_fsys] IS [sh_fsys S].
    That is what turns the two lemmas above into the hypothesis
    [view_frame_absorb] wants. *)
Lemma m_fsys_pe_cfg : forall S e, m_fsys (cfg_model (pe_cfg S e)) = sh_fsys S.
Proof. reflexivity. Qed.

Lemma m_io_pe_cfg : forall S e, m_io (cfg_model (pe_cfg S e)) = sh_io S.
Proof. reflexivity. Qed.

(* =========================================================================
   The keystone: halting from a measure
   ========================================================================= *)

(** THE MULTI-PROCESS ANALOGUE OF [Checks.Examples.exits_c_must_exit_at],
    and the reason the schedule space does not have to be enumerated.

    [must_exit_in_p_at]'s successor premise ranges over EVERY interleaving,
    and for a program with two live entries the number of paths is
    exponential in their lengths.  None of them has to be walked.  What has
    to be true is only that every step, whichever entry takes it, makes a
    measure go down -- and for straight-line code that measure is the total
    instructions remaining, which every step reduces by one because every
    step belongs to exactly one entry.

    So the schedule disappears from the proof obligation, and what is left
    is four facts about ONE step, each quantified over the reachable set
    through an invariant [I] the caller chooses.  A blocked [wait4] needs no
    case of its own: it is an entry with no arm (Procs, [pstep_at]), so it
    contributes no successor and nothing to discharge.

    No axiom is used.  Terminality is decided by [terminalb] rather than by
    excluded middle, which is why that boolean exists. *)

Definition terminalb (P : pconfig) : bool :=
  List.forallb (fun kv => match pe_zombie (snd kv) with
                          | Some _ => true
                          | None => false
                          end)
               (pcfg_procs P).

Lemma terminalb_spec : forall P, terminalb P = true <-> terminal P.
Proof.
  intros P. unfold terminalb, terminal. rewrite List.forallb_forall. split.
  - intros H. apply List.Forall_forall. intros kv Hin.
    specialize (H kv Hin). destruct (pe_zombie (snd kv)); discriminate.
  - intros H kv Hin. rewrite List.Forall_forall in H. specialize (H kv Hin).
    destruct (pe_zombie (snd kv)); [reflexivity | congruence].
Qed.

Theorem must_exit_in_p_at_by_measure :
  forall segs cfg S (I : pconfig -> Prop) (mu : pconfig -> nat),
  (* [I] survives a step *)
  (forall P evs P', I P -> pstep_cfg segs cfg P evs (PNext P') -> I P') ->
  (* a terminal [I]-configuration has the root halted on an allowed code *)
  (forall P, I P -> terminal P ->
     exists c code, root_view P = Some c
                    /\ m_halted (cfg_model c) = Some code
                    /\ List.In code S
                    /\ m_killed (cfg_model c) = None) ->
  (* progress, below terminal *)
  (forall P, I P -> terminalb P = false ->
     exists evs st, pstep_cfg segs cfg P evs st) ->
  (* no execution errors *)
  (forall P evs, I P -> ~ pstep_cfg segs cfg P evs PError) ->
  (* and every step, by whichever entry, makes the measure go down *)
  (forall P evs P', I P -> pstep_cfg segs cfg P evs (PNext P') ->
     (mu P' < mu P)%nat) ->
  forall P, I P -> must_exit_in_p_at segs cfg S P.
Proof.
  intros segs cfg S I mu Hpres Hleaf Hprog Hnoerr Hdec.
  assert (Hgen : forall n P, I P -> (mu P <= n)%nat ->
                             must_exit_in_p_at segs cfg S P).
  { induction n as [|n IHn]; intros P HI Hle; destruct (terminalb P) eqn:Ht.
    - apply terminalb_spec in Ht.
      destruct (Hleaf P HI Ht) as (c & code & H1 & H2 & H3 & H4).
      eapply mepa_halted; eassumption.
    - (* measure 0 and not terminal is impossible: a step would go below it *)
      exfalso. destruct (Hprog P HI Ht) as (evs & st & Hss).
      destruct st as [P'|].
      + pose proof (Hdec P evs P' HI Hss). lia.
      + exact (Hnoerr P evs HI Hss).
    - apply terminalb_spec in Ht.
      destruct (Hleaf P HI Ht) as (c & code & H1 & H2 & H3 & H4).
      eapply mepa_halted; eassumption.
    - apply mepa_running.
      + intros Hterm. apply terminalb_spec in Hterm. congruence.
      + exact (Hprog P HI Ht).
      + intros evs. exact (Hnoerr P evs HI).
      + intros evs P' Hss. apply IHn.
        * exact (Hpres P evs P' HI Hss).
        * pose proof (Hdec P evs P' HI Hss). lia. }
  intros P HI. exact (Hgen (mu P) P HI (Nat.le_refl _)).
Qed.

(* =========================================================================
   Measure arithmetic over the process table
   ========================================================================= *)

(** [must_exit_in_p_at_by_measure] takes the measure as a parameter, and for
    straight-line code the measure a caller wants is a SUM over the live
    entries of a per-entry count -- the instructions that entry has left.
    These three lemmas are the arithmetic of that sum under the three things
    an arm does to the table, and they are what turn "this entry made
    progress" into "the system's measure went down".

    Each is stated WITHOUT SUBTRACTION, as [lhs + f e = rhs + f e'] rather
    than [lhs = rhs - f e + f e'], because truncated subtraction on [nat]
    turns a true statement about the sum into a false one as soon as the
    caller's [f] is not monotone, and that is a trap worth not setting.

    None needs key uniqueness, for the same reason the frame lemmas above do
    not: [look_in], [replace_in] and [drop_in] all act on the FIRST entry at
    a key, so they agree about which entry they mean whether or not the
    table repeats a key. *)

Definition msum (f : ProcessEntry -> nat) (ps : list (Pid * ProcessEntry))
    : nat :=
  List.fold_right (fun kv acc => (f (snd kv) + acc)%nat) 0%nat ps.

(** One step of the sum, as an equation rather than by reduction.  Needed
    because [cbn] unfolds [msum] in the GOAL while an induction hypothesis
    still says [msum], and [lia] then sees two different atoms for the same
    quantity and reports that it cannot find a witness. *)
Lemma msum_cons : forall f kv ps,
  msum f (kv :: ps) = (f (snd kv) + msum f ps)%nat.
Proof. reflexivity. Qed.

(** An ordinary step, and a clone's effect on the parent: one entry is
    replaced by another at the same key. *)
Lemma msum_replace : forall f ps p e e',
  look_in ps p = Some e ->
  (msum f (replace_in ps p e') + f e = msum f ps + f e')%nat.
Proof.
  induction ps as [|kv r IH]; intros p e e' Hl;
    [cbn in Hl; discriminate|].
  cbn [look_in replace_in] in *.
  destruct (bv_eqb (fst kv) p) eqn:Hb.
  - injection Hl as <-. rewrite !msum_cons. cbn [snd]. lia.
  - rewrite !msum_cons. pose proof (IH p e e' Hl). lia.
Qed.

(** A reap: one entry leaves the table. *)
Lemma msum_drop : forall f ps p e,
  look_in ps p = Some e ->
  (msum f (drop_in ps p) + f e = msum f ps)%nat.
Proof.
  induction ps as [|kv r IH]; intros p e Hl; [cbn in Hl; discriminate|].
  cbn [look_in drop_in] in *.
  destruct (bv_eqb (fst kv) p) eqn:Hb.
  - injection Hl as <-. rewrite !msum_cons. lia.
  - rewrite !msum_cons. pose proof (IH p e Hl). lia.
Qed.

(** A clone: the child is appended. *)
Lemma msum_app : forall f ps ps',
  (msum f (ps ++ ps') = msum f ps + msum f ps')%nat.
Proof.
  induction ps as [|kv r IH]; intros ps'; [reflexivity|].
  cbn [app]. rewrite !msum_cons, IH. lia.
Qed.

(** The measure a caller builds from a per-entry count. *)
Definition pmeasure (f : ProcessEntry -> nat) (P : pconfig) : nat :=
  msum f (pcfg_procs P).

(** An ordinary step decreases it exactly when the stepping entry's own
    count decreases.  This is the whole of the two-entry argument: the
    schedule cannot matter, because whichever entry steps, the sum falls by
    that entry's own decrease and nothing else moves. *)
Lemma pmeasure_absorb_lt : forall f P e c',
  look P (pe_pid e) = Some e ->
  (f (pe_absorb e c') < f e)%nat ->
  (pmeasure f (absorb P e c') < pmeasure f P)%nat.
Proof.
  intros f P e c' Hl Hlt. unfold pmeasure, absorb. cbn [pcfg_procs].
  pose proof (msum_replace f (pcfg_procs P) (pe_pid e) e (pe_absorb e c') Hl).
  lia.
Qed.
