(** * EquivalenceDefinition.NsProcs — the multi-process core [Procs] as a [PROCS_CORE]

    [ProcsCore] gives each name of [Ns.ProcsIface.PROCS_CORE] as the
    core's own.  The step context is the pair the core's step takes: the
    loaded segments and the spurious-failure configuration.  L1-L9 are the
    core's lemmas ([Procs], and [MustExitP] for the lineage); L10 to L12
    are proved here from the core's step (L10 from the indexed clone step;
    [pstep_at_grows]: the one step that lengthens the table is a clone, and
    it appends the child).  [NsProcs] is the namespace layer on this core.
    It is in this directory because the lineage and its lemmas are
    ([MustExitP]). *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables ProcsIface Step.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExitP.
Import ListNotations.

Lemma last_map_app_single : forall (A B : Type) (f : A -> B) (l : list A) (x : A) (d : B),
  List.last (List.map f (l ++ [x])) d = f x.
Proof. intros A B f l x d. rewrite List.map_app. cbn [List.map]. apply List.last_last. Qed.

(** A step of the core that lengthens the table is a clone: [pstep_other]
    replaces an entry, the reap drops one, and the rest end in [PError]. *)
Lemma pstep_at_grows : forall segs cfg p P evs P',
  pstep_at segs cfg p P evs (PNext P') ->
  (List.length (pcfg_procs P) < List.length (pcfg_procs P'))%nat ->
  exists e c' q, P' = clone_result P e c' q.
Proof.
  intros segs cfg p P evs P' H Hlt.
  inversion H; subst.
  - exfalso. unfold absorb in Hlt. simpl pcfg_procs in Hlt.
    rewrite replace_in_length in Hlt. lia.
  - do 3 eexists. reflexivity.
  - exfalso. simpl pcfg_procs in Hlt.
    match type of Hlt with
    | (_ < List.length (drop_in ?l ?q0))%nat =>
        pose proof (drop_in_length_le l q0) as Hle
    end.
    rewrite replace_in_length in Hle. lia.
Qed.

Lemma child_projection_clone_result : forall P e c' q,
  child_projection P (clone_result P e c' q)
  = Some (child_entry e (pe_cfg (pcfg_shared P) e) c' q, pcfg_shared (clone_result P e c' q)).
Proof.
  intros P e c' q. unfold child_projection.
  replace (Nat.ltb (List.length (pcfg_procs P))
                   (List.length (pcfg_procs (clone_result P e c' q)))) with true.
  - unfold clone_result. simpl pcfg_procs. rewrite last_map_app_single. reflexivity.
  - symmetry. apply Nat.ltb_lt. unfold clone_result. simpl pcfg_procs.
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

(** L11 on the core. *)
Theorem child_projection_of_clone_core : forall segs cfg P evs P',
  Procs.pstep_cfg segs cfg P evs (PNext P') ->
  (List.length (pcfg_procs P) < List.length (pcfg_procs P'))%nat ->
  exists e sh, child_projection P P' = Some (e, sh) /\ entry_a0_zero e
               /\ sh = pcfg_shared P'.
Proof.
  intros segs cfg P evs P' Hs Hlt. unfold Procs.pstep_cfg in Hs. destruct Hs as [p Hp].
  destruct (pstep_at_grows segs cfg p P evs P' Hp Hlt) as (e & c' & q & ->).
  exists (child_entry e (pe_cfg (pcfg_shared P) e) c' q), (pcfg_shared (clone_result P e c' q)).
  split; [apply child_projection_clone_result|].
  split; [apply child_entry_a0_zero | reflexivity].
Qed.

(** L12 on the core. *)
Theorem lineage_pick_clone_core : forall segs cfg P p evs P' e sh,
  lineage_pick P p ->
  pstep_at segs cfg p P evs (PNext P') ->
  child_projection P P' = Some (e, sh) ->
  lineage_pick P' (pe_pid e).
Proof.
  intros segs cfg P p evs P' e sh _ Hp Hc.
  destruct (pstep_at_grows segs cfg p P evs P' Hp (child_projection_grows P P' _ Hc))
    as (e0 & c' & q & ->).
  rewrite child_projection_clone_result in Hc.
  injection Hc as He Hsh. subst e.
  unfold lineage_pick, clone_result. simpl pcfg_procs.
  rewrite last_map_app_single. reflexivity.
Qed.

Module ProcsCore <: PROCS_CORE.

  Definition Pid : Type := Procs.Pid.

  (* ---- The released single-process step ---- *)
  Definition StepCtx : Type := (list Segment * SpuriousCfg)%type.
  Definition config : Type := Run.config.
  Definition event : Type := State.event.
  Definition step_to : Type := Run.step_to.
  Definition SNext : config -> step_to := Run.SNext.
  Definition SError : step_to := Run.SError.
  Definition sstep_cfg (ctx : StepCtx) (c : config) (evs : list event) (r : step_to) : Prop :=
    Run.sstep_cfg (fst ctx) (snd ctx) c evs r.
  Definition at_instruction : config -> Prop := Procs.at_instruction.
  Definition clone_success : config -> config -> bool := Procs.clone_success_b.
  Definition wait4_intercept : config -> bool := Procs.wait4_intercept_b.
  Definition child_pid : config -> Pid -> Prop := Procs.child_pid_core.

  (* ---- The multi-process core ---- *)
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
  Definition pe_cfg : shared -> ProcessEntry -> config := Procs.pe_cfg.
  Definition one_pid : Pid := Procs.one_pid.
  Definition one_proc : config -> pconfig := Procs.one_proc.
  Definition multiproc_allowed : pconfig -> config -> bool := Procs.multiproc_allowed.

  Definition pstep_to : Type := Procs.pstep_to.
  Definition PNext : pconfig -> pstep_to := Procs.PNext.
  Definition PError : pstep_to := Procs.PError.
  Definition pstep_cfg (ctx : StepCtx) : pconfig -> list event -> pstep_to -> Prop :=
    Procs.pstep_cfg (fst ctx) (snd ctx).
  Definition pstep_at (ctx : StepCtx) : Pid -> pconfig -> list event -> pstep_to -> Prop :=
    Procs.pstep_at (fst ctx) (snd ctx).
  Definition lineage_pick : pconfig -> Pid -> Prop := MustExitP.lineage_pick.
  Definition clone_result : pconfig -> ProcessEntry -> config -> Pid -> pconfig :=
    Procs.clone_result.
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
    intros ctx c evs P'. exact (Procs.pstep_instr_single_next (fst ctx) (snd ctx) c evs P').
  Qed.

  (** L3 *)
  Lemma pstep_instr_single_err : forall ctx c evs, at_instruction c ->
    (pstep_cfg ctx (one_proc c) evs PError <-> sstep_cfg ctx c evs SError).
  Proof.
    intros ctx c evs. exact (Procs.pstep_instr_single_err (fst ctx) (snd ctx) c evs).
  Qed.

  (** L4 *)
  Lemma pstep_single_next : forall ctx c evs P',
    (forall c', sstep_cfg ctx c evs (SNext c') -> clone_success c c' = false) ->
    wait4_intercept c = false ->
    (pstep_cfg ctx (one_proc c) evs (PNext P')
     <-> exists c', P' = one_proc c' /\ sstep_cfg ctx c evs (SNext c')).
  Proof.
    intros ctx c evs P'. exact (Procs.pstep_single_next (fst ctx) (snd ctx) c evs P').
  Qed.

  (** L5 *)
  Lemma pstep_single_err : forall ctx c evs, wait4_intercept c = false ->
    (pstep_cfg ctx (one_proc c) evs PError <-> sstep_cfg ctx c evs SError).
  Proof.
    intros ctx c evs. exact (Procs.pstep_single_err (fst ctx) (snd ctx) c evs).
  Qed.

  (** L6 *)
  Lemma pstep_at_sub : forall ctx p P evs r,
    pstep_at ctx p P evs r -> pstep_cfg ctx P evs r.
  Proof. intros ctx p P evs r. exact (Procs.pstep_at_sub (fst ctx) (snd ctx) p P evs r). Qed.

  (** L7 *)
  Lemma pstep_cfg_has_actor : forall ctx P evs r,
    pstep_cfg ctx P evs r -> exists p, pstep_at ctx p P evs r.
  Proof.
    intros ctx P evs r. exact (Procs.pstep_cfg_has_actor (fst ctx) (snd ctx) P evs r).
  Qed.

  (** L8 *)
  Lemma lineage_pick_one : forall c p, lineage_pick (one_proc c) p <-> p = one_pid.
  Proof. exact MustExitP.lineage_pick_one. Qed.

  (** L9 *)
  Lemma pstep_at_one : forall ctx c evs r,
    pstep_at ctx one_pid (one_proc c) evs r <-> pstep_cfg ctx (one_proc c) evs r.
  Proof. intros ctx c evs r. exact (Procs.pstep_at_one (fst ctx) (snd ctx) c evs r). Qed.

  (** L10 *)
  Lemma pstep_clone_law : forall ctx P e evs c' q,
    look P (pe_pid e) = Some e ->
    sstep_cfg ctx (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    clone_success (pe_cfg (pcfg_shared P) e) c' = true ->
    child_pid c' q ->
    look P q = None ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    pstep_cfg ctx P evs (PNext (clone_result P e c' q)).
  Proof.
    intros ctx P e evs c' q H1 H2 H3 H4 H5 H6. unfold pstep_cfg, Procs.pstep_cfg.
    exists (pe_pid e). exact (Procs.pstep_clone (fst ctx) (snd ctx) P e evs c' q H1 H2 H3 H4 H5 H6).
  Qed.

  (** L11 *)
  Lemma child_projection_of_clone : forall ctx P evs P',
    pstep_cfg ctx P evs (PNext P') ->
    length (pcfg_procs P') > length (pcfg_procs P) ->
    exists e sh, child_projection P P' = Some (e, sh) /\ entry_a0_zero e
                 /\ sh = pcfg_shared P'.
  Proof.
    intros ctx P evs P'. exact (child_projection_of_clone_core (fst ctx) (snd ctx) P evs P').
  Qed.

  (** L12 *)
  Lemma lineage_pick_clone : forall ctx P p evs P' e sh,
    lineage_pick P p ->
    pstep_at ctx p P evs (PNext P') ->
    child_projection P P' = Some (e, sh) ->
    lineage_pick P' (pe_pid e).
  Proof.
    intros ctx P p evs P' e sh.
    exact (lineage_pick_clone_core (fst ctx) (snd ctx) P p evs P' e sh).
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
