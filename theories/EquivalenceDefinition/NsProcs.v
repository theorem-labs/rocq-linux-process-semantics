(** * EquivalenceDefinition.NsProcs — the multi-process core with the namespace model, as a [PROCS_CORE]

    [ProcsCore] gives each name of [Ns.ProcsIface.PROCS_CORE] as the
    core's own, with the namespace model plugged in: its step is
    [Procs.pstep_x_at] at [Ns.Spec.ns_ext].  The step context is what the
    core's step takes: the run's clone environment ([Ns.Ext.CloneEnv]),
    the loaded segments and the spurious-failure configuration.
    L1-L5 and L7 are the core's lemmas ([Procs]), L6 is
    [MustExitP]'s lineage lemma, and L8 and L9 are proved here
    ([pstep_x_at_grows]: the one step that lengthens the table is a clone,
    and it appends the child).  [NsProcs] is the namespace layer on this
    core.  It is in this directory because the lineage and its lemmas are
    ([MustExitP]).

    [ns_flat_iff] is the namespace model's answer to the question a reader
    of the plug-in asks first: in a system whose processes are all in the
    released world, with no pending clone that makes a namespace, the
    extended step IS the core's own step, claimed calls included.

    [pholts_x_within_budget] is PROCS's whole-system halting statement over
    the extended step, with the clone environment as an explicit argument;
    [lholts_ns_within_budget] is the halting statement of the lineage (the
    newest process), which a program whose parent makes calls while a
    child lives needs on this core. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Clone Spec ProcsIface Step.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExitP.
Import ListNotations.

(* =========================================================================
   The namespace model on the core
   ========================================================================= *)

(** [ns_ext] leaves both clone calls and the wait to the core. *)
Lemma ns_clone_unclaimed : forall segs c,
  clone_pending_b c = true -> claimed_at ns_ext segs c = false.
Proof.
  intros segs c. unfold clone_pending_b, claimed_at, pending_input.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; cbv beta iota; [|intros _; reflexivity].
  intros H. unfold clone_sysno in H. change (ext_claims ns_ext) with ns_claims.
  unfold ns_claims, ns_sysno. cbn [sys_input in_sysno].
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; rewrite H; reflexivity.
Qed.

Lemma ns_wait_unclaimed : forall segs c,
  wait4_intercept_b c = true -> claimed_at ns_ext segs c = false.
Proof.
  intros segs c. unfold wait4_intercept_b, claimed_at, pending_input.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; cbv beta iota; [|intros _; reflexivity].
  intros H. apply andb_true_iff in H as [H _]. apply Z.eqb_eq in H.
  change (ext_claims ns_ext) with ns_claims.
  unfold ns_claims, ns_sysno. cbn [sys_input in_sysno]. rewrite H. reflexivity.
Qed.

(** A clone environment that admits every failure of the released clone
    (a task in the released world, a word with no namespace bit). *)
Definition cenv_flat_ok (cenv : CloneEnv) : Prop :=
  forall f m ctx st hq e st',
    flat_view ctx st = true -> has_ns_bits f = false -> cenv f m ctx st hq e st'.

Lemma any_clone_failure_flat_ok : cenv_flat_ok any_clone_failure.
Proof. intros f m ctx st hq e st' _ _. exact I. Qed.

Lemma clone_tables_failures_flat_ok : cenv_flat_ok clone_tables_failures.
Proof. intros f m ctx st hq e st'. apply clone_tables_failures_flat. Qed.

(** IN THE RELEASED WORLD THE NAMESPACE MODEL CHANGES NO STEP: every
    process in the released world, and no pending clone that makes a
    namespace, and the extended step is the core's own, in any clone
    environment that keeps the released clone's failures. *)
Theorem ns_flat_iff : forall cenv segs cfg p P evs r,
  cenv_flat_ok cenv ->
  (forall e, look P (pe_pid e) = Some e ->
     flat_view (pe_nsctx e) (sh_ns (pcfg_shared P)) = true
     /\ has_ns_bits (clone_flags_of (pe_cfg (pcfg_shared P) e)) = false) ->
  (pstep_x_at ns_ext cenv segs cfg p P evs r <-> pstep_at segs cfg p P evs r).
Proof.
  intros cenv segs cfg p P evs r Hce H. apply pstep_x_at_flat_iff.
  intros e Hl. destruct (H e Hl) as [Hf Hns].
  split; [exact Hf | split; [exact Hns | split; [|split]]].
  - apply ns_clone_unclaimed.
  - apply ns_wait_unclaimed.
  - intros _ hq en st'. apply Hce; assumption.
Qed.

(* =========================================================================
   Clones on the extended core
   ========================================================================= *)

Lemma last_map_app_single : forall (A B : Type) (f : A -> B) (l : list A) (x : A) (d : B),
  List.last (List.map f (l ++ [x])) d = f x.
Proof. intros A B f l x d. rewrite List.map_app. cbn [List.map]. apply List.last_last. Qed.

(** A step that lengthens the table is a successful clone: [px_other] and
    [px_clone_fail] replace an entry, the reap drops one, and the rest end
    in [PError]. *)
Lemma pstep_x_at_grows : forall ext cenv segs cfg p P evs P',
  pstep_x_at ext cenv segs cfg p P evs (PNext P') ->
  (List.length (pcfg_procs P) < List.length (pcfg_procs P'))%nat ->
  exists e c' q child st', P' = clone_result_x P e c' q child st'.
Proof.
  intros ext cenv segs cfg p P evs P' H Hlt.
  inversion H; subst.
  - exfalso. unfold absorb_x in Hlt. simpl pcfg_procs in Hlt.
    rewrite replace_in_length in Hlt. lia.
  - do 5 eexists. reflexivity.
  - exfalso. unfold absorb_x in Hlt. simpl pcfg_procs in Hlt.
    rewrite replace_in_length in Hlt. lia.
  - exfalso. simpl pcfg_procs in Hlt.
    match type of Hlt with
    | (_ < List.length (drop_in ?l ?q0))%nat =>
        pose proof (drop_in_length_le l q0) as Hle
    end.
    rewrite replace_in_length in Hle. lia.
Qed.

Lemma child_projection_clone_result_x : forall P e c' q child st',
  child_projection P (clone_result_x P e c' q child st')
  = Some (with_nsctx (child_entry e (pe_cfg (pcfg_shared P) e) c' q) child,
          pcfg_shared (clone_result_x P e c' q child st')).
Proof.
  intros P e c' q child st'. unfold child_projection.
  replace (Nat.ltb (List.length (pcfg_procs P))
                   (List.length (pcfg_procs (clone_result_x P e c' q child st')))) with true.
  - unfold clone_result_x. simpl pcfg_procs. rewrite last_map_app_single. reflexivity.
  - symmetry. apply Nat.ltb_lt. unfold clone_result_x. simpl pcfg_procs.
    rewrite length_app, replace_in_length. simpl. lia.
Qed.

Lemma child_projection_grows : forall P P' x,
  child_projection P P' = Some x ->
  (List.length (pcfg_procs P) < List.length (pcfg_procs P'))%nat.
Proof.
  intros P P' x H. unfold child_projection in H.
  destruct (Nat.ltb (List.length (pcfg_procs P)) (List.length (pcfg_procs P'))) eqn:E.
  - apply Nat.ltb_lt. exact E.
  - discriminate H.
Qed.

(** L8 on the extended core. *)
Theorem child_projection_of_clone_x : forall ext cenv segs cfg P evs P',
  pstep_x_cfg ext cenv segs cfg P evs (PNext P') ->
  (List.length (pcfg_procs P) < List.length (pcfg_procs P'))%nat ->
  exists e sh, child_projection P P' = Some (e, sh) /\ entry_a0_zero e
               /\ sh = pcfg_shared P'.
Proof.
  intros ext cenv segs cfg P evs P' [p Hp] Hlt.
  destruct (pstep_x_at_grows ext cenv segs cfg p P evs P' Hp Hlt) as (e & c' & q & child & st' & ->).
  exists (with_nsctx (child_entry e (pe_cfg (pcfg_shared P) e) c' q) child),
         (pcfg_shared (clone_result_x P e c' q child st')).
  split; [apply child_projection_clone_result_x|].
  split; [exact (child_entry_a0_zero e (pe_cfg (pcfg_shared P) e) c' q) | reflexivity].
Qed.

(** L9 on the extended core. *)
Theorem lineage_pick_clone_x : forall ext cenv segs cfg P p evs P' e sh,
  lineage_pick P p ->
  pstep_x_at ext cenv segs cfg p P evs (PNext P') ->
  child_projection P P' = Some (e, sh) ->
  lineage_pick P' (pe_pid e).
Proof.
  intros ext cenv segs cfg P p evs P' e sh _ Hp Hc.
  destruct (pstep_x_at_grows ext cenv segs cfg p P evs P' Hp (child_projection_grows P P' _ Hc))
    as (e0 & c' & q & child & st' & ->).
  rewrite child_projection_clone_result_x in Hc.
  injection Hc as He Hsh. subst e.
  unfold lineage_pick, clone_result_x. simpl pcfg_procs.
  rewrite last_map_app_single. reflexivity.
Qed.

(* =========================================================================
   Halting of the system with an extension
   ========================================================================= *)

(** The one-process system of [c] in the host's namespaces [st]: the
    process has [init_nsctx], and [st] is the shared namespace state. *)
Definition one_proc_in (c : config) (st : NsState) : pconfig :=
  mkPCfg (pcfg_procs (one_proc c)) (pcfg_root (one_proc c)) (with_sh_ns (pcfg_shared (one_proc c)) st).

Lemma one_proc_in_empty : forall c, one_proc_in c empty_nsstate = one_proc c.
Proof. reflexivity. Qed.

(** [MustExitP.must_exit_in_p_at] over the extended step: every maximal
    execution of the system halts, the root on a code in [S] and nothing
    still running, with no step to the model's error on the way. *)
Inductive must_exit_in_px_at (ext : ExtSpec) (cenv : CloneEnv) (segs : list Segment)
    (cfg : SpuriousCfg) (S : list word) : pconfig -> Prop :=
| mepxa_halted : forall P c code,
    root_view P = Some c ->
    m_halted (cfg_model c) = Some code ->
    List.In code S ->
    m_killed (cfg_model c) = None ->
    terminal P ->
    must_exit_in_px_at ext cenv segs cfg S P
| mepxa_running : forall P,
    ~ terminal P ->
    (exists evs st, pstep_x_cfg ext cenv segs cfg P evs st) ->
    (forall evs, ~ pstep_x_cfg ext cenv segs cfg P evs PError) ->
    (forall evs P', pstep_x_cfg ext cenv segs cfg P evs (PNext P') ->
                    must_exit_in_px_at ext cenv segs cfg S P') ->
    must_exit_in_px_at ext cenv segs cfg S P.

(** At [no_ext] and [any_clone_failure] it is [MustExitP.must_exit_in_p_at]. *)
Theorem must_exit_in_px_at_no_ext : forall segs cfg S P,
  must_exit_in_px_at no_ext any_clone_failure segs cfg S P <-> must_exit_in_p_at segs cfg S P.
Proof.
  intros segs cfg S P. split.
  - intros H. induction H as [P c code Hr Hh Hin Hk Ht | P Ht Hex Hne Hall IH].
    + eapply mepa_halted; eassumption.
    + apply mepa_running.
      * exact Ht.
      * destruct Hex as (evs & st & Hs). exists evs, st. apply pstep_x_cfg_no_ext_iff. exact Hs.
      * intros evs Hs. apply (Hne evs). apply pstep_x_cfg_no_ext_iff. exact Hs.
      * intros evs P' Hs. apply (IH evs P'). apply pstep_x_cfg_no_ext_iff. exact Hs.
  - intros H. induction H as [P c code Hr Hh Hin Hk Ht | P Ht Hex Hne Hall IH].
    + eapply mepxa_halted; eassumption.
    + apply mepxa_running.
      * exact Ht.
      * destruct Hex as (evs & st & Hs). exists evs, st. apply pstep_x_cfg_no_ext_iff. exact Hs.
      * intros evs Hs. apply (Hne evs). apply pstep_x_cfg_no_ext_iff. exact Hs.
      * intros evs P' Hs. apply (IH evs P'). apply pstep_x_cfg_no_ext_iff. exact Hs.
Qed.

(** The same match on the image and the entry as [MustExitP.must_exit_in_p],
    from the host's namespaces [st]. *)
Definition must_exit_in_px (ext : ExtSpec) (cenv : CloneEnv) (cfg : SpuriousCfg) (S : list word)
    (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (st : NsState) : Prop :=
  match img, en with
  | mkImage segs pc ph, Run.mkEntry sp brk0 mbase rnd =>
      must_exit_in_px_at ext cenv segs cfg S
        (one_proc_in (init_config segs pc ph sp brk0 mbase rnd lim inp) st)
  end.

(** [MustExitP.pholts_within_budget] over the extended step, on the inputs
    [pre] admits and from each host namespace state [host] admits.  Same
    quantifier, same environment, same budget premise.

    The clone environment [cenv] is an explicit argument, so that the
    statement shows which clone failures its runs admit.
    [Ns.Ext.any_clone_failure] admits every failure the released clone and
    the extension give ([pholts_x_within_budget_no_ext]: at [no_ext] the
    statement is PROCS's own).  A narrower one, such as
    [Ns.Clone.clone_tables_failures] (only the failures the namespace
    tables give, for a clone that makes a namespace), is an ENVIRONMENT
    PREMISE of the statement: a run in which the host refuses to make the
    namespaces (an allocation, a namespace count, a cgroup controller,
    RLIMIT_NPROC, a security module) is outside it, and the statement's
    header must say so.  The released arm ([Fork.clone_ns_resolve]) cannot
    make that cut itself: without the namespace tables it cannot tell a
    forced EPERM from a security module's (the LPS owner's decision,
    2026-11-01).

    ON THIS CORE the whole-system form holds only for programs whose
    processes in the released world make no call but exit, exit_group,
    clone, clone3 and wait4 while another process lives
    ([Procs.multiproc_allowed]; a process outside the released world also
    gets the calls [Ext.ext_multiproc] admits): any other call in that state
    is the model's error.  A program whose parent goes on making calls after
    a clone needs [lholts_ns_within_budget], below. *)
Definition pholts_x_within_budget (ext : ExtSpec) (cenv : CloneEnv) (pre : ProcInput -> Prop)
    (host : NsState -> Prop) (lim : Z) (allowed : list word) (img : Image) : Prop :=
  forall (en : ExecEntry) (inp : ProcInput) (st : NsState),
    valid_entry img en inp ->
    valid_input inp ->
    pre inp ->
    host st ->
    ~ run_scfg_budget_refused forced_only_cfg img lim en inp ->
    must_exit_in_px ext cenv forced_only_cfg allowed img lim en inp st.

(** At [no_ext] and [any_clone_failure], on every input and from the empty
    namespace state, it is [MustExitP.pholts_within_budget]. *)
Theorem pholts_x_within_budget_no_ext : forall lim allowed img,
  pholts_x_within_budget no_ext any_clone_failure (fun _ => True) (fun st => st = empty_nsstate)
    lim allowed img
  <-> pholts_within_budget lim allowed img.
Proof.
  intros lim allowed img. unfold pholts_x_within_budget, pholts_within_budget.
  split.
  - intros H en inp Hv Hi Hb. specialize (H en inp empty_nsstate Hv Hi I eq_refl Hb).
    destruct img as [segs pc ph], en as [sp brk0 mbase rnd].
    unfold must_exit_in_px in H. unfold must_exit_in_p, pinit_config.
    cbv beta iota in H |- *.
    rewrite one_proc_in_empty in H.
    apply must_exit_in_px_at_no_ext. exact H.
  - intros H en inp st Hv Hi _ Hst Hb. subst st. specialize (H en inp Hv Hi Hb).
    destruct img as [segs pc ph], en as [sp brk0 mbase rnd].
    unfold must_exit_in_p, pinit_config in H. unfold must_exit_in_px.
    cbv beta iota in H |- *.
    rewrite one_proc_in_empty.
    apply must_exit_in_px_at_no_ext. exact H.
Qed.

Module ProcsCore <: PROCS_CORE.

  Definition Pid : Type := Procs.Pid.

  (* ---- The released single-process step ---- *)
  (** The step context: the run's clone environment, the loaded segments
      and the spurious-failure configuration. *)
  Definition StepCtx : Type := (CloneEnv * (list Segment * SpuriousCfg))%type.
  Definition ctx_cenv (ctx : StepCtx) : CloneEnv := fst ctx.
  Definition ctx_segs (ctx : StepCtx) : list Segment := fst (snd ctx).
  Definition ctx_cfg (ctx : StepCtx) : SpuriousCfg := snd (snd ctx).
  Definition config : Type := Run.config.
  Definition event : Type := State.event.
  Definition step_to : Type := Run.step_to.
  Definition SNext : config -> step_to := Run.SNext.
  Definition SError : step_to := Run.SError.
  Definition sstep_cfg (ctx : StepCtx) (c : config) (evs : list event) (r : step_to) : Prop :=
    Run.sstep_cfg (ctx_segs ctx) (ctx_cfg ctx) c evs r.
  Definition at_instruction : config -> Prop := Procs.at_instruction.

  (* ---- The multi-process core, with the namespace model ---- *)
  Definition OfdId : Type := Procs.OfdId.
  Definition ofd_eq_dec (a b : OfdId) : {a = b} + {a <> b}.
  Proof.
    destruct (bv_eqb a b) eqn:E.
    - left. exact (bv_eqb_true_eq _ a b E).
    - right. intros H. subst b. rewrite bv_eqb_same in E. discriminate E.
  Defined.
  Definition Fd : Type := word.
  Definition ProcessEntry : Type := Procs.ProcessEntry.
  Definition shared : Type := Procs.shared.
  Definition pconfig : Type := Procs.pconfig.
  Definition pe_pid : ProcessEntry -> Pid := Procs.pe_pid.
  Definition pe_parent : ProcessEntry -> option Pid := Procs.pe_parent.
  Definition pe_ofd : ProcessEntry -> list (Fd * OfdId) := Procs.pe_ofd.
  Definition pe_nsctx : ProcessEntry -> NsCtx := Procs.pe_nsctx.
  Definition sh_nsstate : shared -> NsState := Procs.sh_ns.
  Definition pcfg_procs : pconfig -> list (Pid * ProcessEntry) := Procs.pcfg_procs.
  Definition pcfg_root : pconfig -> Pid := Procs.pcfg_root.
  Definition pcfg_shared : pconfig -> shared := Procs.pcfg_shared.
  Definition look : pconfig -> Pid -> option ProcessEntry := Procs.look.
  Definition one_pid : Pid := Procs.one_pid.
  Definition one_proc : config -> pconfig := Procs.one_proc.

  Definition pstep_to : Type := Procs.pstep_to.
  Definition PNext : pconfig -> pstep_to := Procs.PNext.
  Definition PError : pstep_to := Procs.PError.
  Definition pstep_cfg (ctx : StepCtx) : pconfig -> list event -> pstep_to -> Prop :=
    Procs.pstep_x_cfg ns_ext (ctx_cenv ctx) (ctx_segs ctx) (ctx_cfg ctx).
  Definition pstep_at (ctx : StepCtx) : Pid -> pconfig -> list event -> pstep_to -> Prop :=
    Procs.pstep_x_at ns_ext (ctx_cenv ctx) (ctx_segs ctx) (ctx_cfg ctx).
  Definition lineage_pick : pconfig -> Pid -> Prop := MustExitP.lineage_pick.
  Definition child_projection : pconfig -> pconfig -> option (ProcessEntry * shared) :=
    Procs.child_projection.
  Definition entry_a0_zero : ProcessEntry -> Prop := Procs.entry_a0_zero.

  (* ---- The laws ---- *)

  (** L1 *)
  Lemma pstep_to_cases : forall r, (exists P, r = PNext P) \/ r = PError.
  Proof. exact Procs.pstep_to_cases. Qed.

  (** L2 *)
  Lemma pstep_instr_single_next : forall ctx c evs P', at_instruction c ->
    (pstep_cfg ctx (one_proc c) evs (PNext P')
     <-> exists c', P' = one_proc c' /\ sstep_cfg ctx c evs (SNext c')).
  Proof.
    intros ctx c evs P'.
    exact (Procs.pstep_x_instr_single_next ns_ext (ctx_cenv ctx) (ctx_segs ctx) (ctx_cfg ctx) c evs P').
  Qed.

  (** L3 *)
  Lemma pstep_instr_single_err : forall ctx c evs, at_instruction c ->
    (pstep_cfg ctx (one_proc c) evs PError <-> sstep_cfg ctx c evs SError).
  Proof.
    intros ctx c evs.
    exact (Procs.pstep_x_instr_single_err ns_ext (ctx_cenv ctx) (ctx_segs ctx) (ctx_cfg ctx) c evs).
  Qed.

  (** L4 *)
  Lemma pstep_at_sub : forall ctx p P evs r,
    pstep_at ctx p P evs r -> pstep_cfg ctx P evs r.
  Proof. intros ctx p P evs r H. exists p. exact H. Qed.

  (** L5 *)
  Lemma pstep_cfg_has_actor : forall ctx P evs r,
    pstep_cfg ctx P evs r -> exists p, pstep_at ctx p P evs r.
  Proof. intros ctx P evs r H. exact H. Qed.

  (** L6 *)
  Lemma lineage_pick_one : forall c p, lineage_pick (one_proc c) p <-> p = one_pid.
  Proof. exact MustExitP.lineage_pick_one. Qed.

  (** L7 *)
  Lemma pstep_at_one : forall ctx c evs r,
    pstep_at ctx one_pid (one_proc c) evs r <-> pstep_cfg ctx (one_proc c) evs r.
  Proof.
    intros ctx c evs r.
    exact (Procs.pstep_x_at_one ns_ext (ctx_cenv ctx) (ctx_segs ctx) (ctx_cfg ctx) c evs r).
  Qed.

  (** L8 *)
  Lemma child_projection_of_clone : forall ctx P evs P',
    pstep_cfg ctx P evs (PNext P') ->
    length (pcfg_procs P') > length (pcfg_procs P) ->
    exists e sh, child_projection P P' = Some (e, sh) /\ entry_a0_zero e
                 /\ sh = pcfg_shared P'.
  Proof.
    intros ctx P evs P'.
    exact (child_projection_of_clone_x ns_ext (ctx_cenv ctx) (ctx_segs ctx) (ctx_cfg ctx) P evs P').
  Qed.

  (** L9 *)
  Lemma lineage_pick_clone : forall ctx P p evs P' e sh,
    lineage_pick P p ->
    pstep_at ctx p P evs (PNext P') ->
    child_projection P P' = Some (e, sh) ->
    lineage_pick P' (pe_pid e).
  Proof.
    intros ctx P p evs P' e sh.
    exact (lineage_pick_clone_x ns_ext (ctx_cenv ctx) (ctx_segs ctx) (ctx_cfg ctx) P p evs P' e sh).
  Qed.

End ProcsCore.

Module NsProcs := NsStep ProcsCore.

(* =========================================================================
   What a focused process reads, on this core
   ========================================================================= *)

(** Everything process [f] can read: its own entry (registers, model,
    descriptor table, namespace context); each open file description its
    descriptors name, with its content (what, offset, flags and the count
    of references, whose fall to zero a reader of a pipe sees as end of
    file); the file system and I/O state; the pipe buffers; and the
    namespace state.  A per-process descriptor that is not a shared
    description (an eventfd, a signalfd) is part of [f]'s own model. *)
Record FocusView := mkFocusView {
  fv_entry : option ProcessEntry;
  fv_ofds  : list (OfdId * option Ofd);
  fv_fsys  : FsState;
  fv_io    : IoState;
  fv_pipes : list (word * PipeBuf);
  fv_ns    : NsState
}.

Fixpoint ofd_get (l : list (OfdId * Ofd)) (o : OfdId) : option Ofd :=
  match l with
  | [] => None
  | (k, d) :: r => if bv_eqb k o then Some d else ofd_get r o
  end.

Definition focus_view (P : pconfig) (f : Pid) : FocusView :=
  let S := pcfg_shared P in
  let e := look P f in
  mkFocusView e
    (match e with
     | Some x => map (fun fo => (snd fo, ofd_get (sh_ofd S) (snd fo))) (pe_ofd x)
     | None => []
     end)
    (sh_fsys S) (sh_io S) (sh_pipes S) (sh_ns S).

Fixpoint view_get (l : list (OfdId * option Ofd)) (o : OfdId) : option (option Ofd) :=
  match l with
  | [] => None
  | (k, d) :: r => if bv_eqb k o then Some d else view_get r o
  end.

(** Two views are the same for [f] up to the exchange descriptions [xs]:
    every part equal, except the content of a description in [xs]. *)
Definition focus_eq (xs : list OfdId) (a b : FocusView) : Prop :=
  fv_entry a = fv_entry b /\ fv_fsys a = fv_fsys b /\ fv_io a = fv_io b
  /\ fv_pipes a = fv_pipes b /\ fv_ns a = fv_ns b
  /\ map fst (fv_ofds a) = map fst (fv_ofds b)
  /\ forall o, ~ In o xs -> view_get (fv_ofds a) o = view_get (fv_ofds b) o.

Lemma focus_eq_refl : forall xs v, focus_eq xs v v.
Proof. intros xs v. repeat split; intros; reflexivity. Qed.

(** With no exchange description, the same view is the same in every
    part. *)
Lemma focus_eq_nil_eq_parts : forall a b,
  focus_eq [] a b -> fv_entry a = fv_entry b /\ fv_ns a = fv_ns b /\ fv_fsys a = fv_fsys b.
Proof.
  intros a b (He & Hf & _ & _ & Hn & _ & _). split; [exact He | split; [exact Hn | exact Hf]].
Qed.

(** The focus's subtree does not see the other processes, except through
    the exchange descriptions [xs], until the cut. *)
Definition focus_noninterfering (xs : pconfig -> Pid -> list OfdId)
    (cut_at : Pid -> pconfig -> Prop) (ctx : ProcsCore.StepCtx) (f : Pid) (P : pconfig) : Prop :=
  NsProcs.parents_noninterfering FocusView focus_view focus_eq xs cut_at ctx f P.

(* =========================================================================
   Halting of the lineage
   ========================================================================= *)

(** The lineage's entry: the newest process ([MustExitP.lineage_pick]). *)
Definition lineage_entry (P : pconfig) : option ProcessEntry :=
  look P (List.last (List.map fst (pcfg_procs P)) (pcfg_root P)).

(** Every maximal run OF THE LINEAGE ([NsProcs.nstep]: the steps of the
    newest process, which after a clone is the child) halts with that
    process exited on a code in [S], not killed, and with no step of it to
    the model's error.  The other processes do not step here; what they do
    to the lineage is the premise a statement names
    ([lholts_ns_within_budget]).  So the code read is the lineage's own:
    after a clone, the child's. *)
Inductive must_exit_lineage_at (ctx : ProcsCore.StepCtx) (S : list word) : pconfig -> Prop :=
| mela_halted : forall P e code,
    lineage_entry P = Some e ->
    m_halted (cfg_model (pe_cfg (pcfg_shared P) e)) = Some code ->
    List.In code S ->
    m_killed (cfg_model (pe_cfg (pcfg_shared P) e)) = None ->
    must_exit_lineage_at ctx S P
| mela_running : forall P e,
    lineage_entry P = Some e ->
    m_halted (cfg_model (pe_cfg (pcfg_shared P) e)) = None ->
    (exists evs r, NsProcs.nstep ctx P evs r) ->
    (forall evs, ~ NsProcs.nstep ctx P evs PError) ->
    (forall evs P', NsProcs.nstep ctx P evs (PNext P') -> must_exit_lineage_at ctx S P') ->
    must_exit_lineage_at ctx S P.

(** THE LINEAGE HALTING STATEMENT over the namespace model.

    WHY THE LINEAGE.  The whole-system form ([pholts_x_within_budget]) is
    unavailable for a program whose parent goes on making calls after a
    clone, because this core restricts a released-world process while
    another process lives ([Procs.multiproc_allowed]: only exit,
    exit_group, clone, clone3 and wait4).  WHEN THAT GUARD IS WIDENED, the
    whole-system form becomes available and the statements of this shape
    are to be revisited.

    WHAT IT IS ABOUT.  A statement of this shape is about the lineage
    process (after a clone, the child) and ITS exit status: every maximal
    run of the lineage ends with it exited on a code in [allowed].  The
    parent's exit is out of scope here.

    It is [pholts_x_within_budget] for the lineage's run instead of the
    whole system's, from each host namespace state [host] admits, on the
    inputs [pre] admits, with two named hypotheses:
    - [cenv], the clone failures the run admits: an ENVIRONMENT PREMISE
      when narrower than [any_clone_failure] (for example
      [Ns.Clone.clone_tables_failures]: the host can make the namespaces
      and the processes);
    - [lineage_quiet xs cut_at], A HYPOTHESIS ON THE PARENTS' BEHAVIOUR:
      the layer's own [NsProcs.parents_noninterfering] (through
      [focus_noninterfering]), at every system state reachable from the
      start, with the lineage of that state as the focus: until the cut
      [cut_at], the processes outside the lineage's subtree do not change
      what it reads, except the contents of the exchange descriptions
      [xs].  It is not an assumption about the environment: it is about
      the program's other processes, the same binary, and is to be proved
      of them (by the parent-side proofs) or shown satisfiable by a
      recorded run.  The child's own proof cannot discharge it.  The
      statement's header must say which of the parent's calls after the
      clone it covers.
    The budget premise is [MustExitP.pholts_within_budget]'s: the released
    one-process run of the image.  It says nothing about the memory a child
    asks for; a statement whose child may be refused memory must exclude
    that itself. *)
Inductive preach (ctx : ProcsCore.StepCtx) : pconfig -> pconfig -> Prop :=
| preach_refl : forall P, preach ctx P P
| preach_step : forall P evs P' P'',
    ProcsCore.pstep_cfg ctx P evs (PNext P') -> preach ctx P' P'' -> preach ctx P P''.

(** [NsProcs.parents_noninterfering] for the focused view, at every state
    reachable from [P0], with that state's lineage as the focus. *)
Definition lineage_quiet (xs : pconfig -> Pid -> list OfdId) (cut_at : Pid -> pconfig -> Prop)
    (ctx : ProcsCore.StepCtx) (P0 : pconfig) : Prop :=
  forall P f, preach ctx P0 P -> MustExitP.lineage_pick P f -> focus_noninterfering xs cut_at ctx f P.

Definition lholts_ns_within_budget (cenv : CloneEnv) (pre : ProcInput -> Prop)
    (host : NsState -> Prop) (xs : pconfig -> Pid -> list OfdId) (cut_at : Pid -> pconfig -> Prop)
    (lim : Z) (allowed : list word) (img : Image) : Prop :=
  forall (en : ExecEntry) (inp : ProcInput) (st : NsState),
    valid_entry img en inp ->
    valid_input inp ->
    pre inp ->
    host st ->
    ~ run_scfg_budget_refused forced_only_cfg img lim en inp ->
    match img, en with
    | mkImage segs pc ph, Run.mkEntry sp brk0 mbase rnd =>
        lineage_quiet xs cut_at (cenv, (segs, forced_only_cfg))
          (one_proc_in (init_config segs pc ph sp brk0 mbase rnd lim inp) st) ->
        must_exit_lineage_at (cenv, (segs, forced_only_cfg)) allowed
          (one_proc_in (init_config segs pc ph sp brk0 mbase rnd lim inp) st)
    end.

(** Before any clone the lineage is the one process: in a one-process
    system the lineage's steps are all the system's steps. *)
Lemma nstep_one_proc_iff : forall ctx c evs r,
  NsProcs.nstep ctx (one_proc c) evs r <-> ProcsCore.pstep_cfg ctx (one_proc c) evs r.
Proof.
  intros ctx c evs r. split.
  - apply NsProcs.nstep_sub.
  - intros H. exists ProcsCore.one_pid. split.
    + apply ProcsCore.lineage_pick_one. reflexivity.
    + apply ProcsCore.pstep_at_one. exact H.
Qed.
