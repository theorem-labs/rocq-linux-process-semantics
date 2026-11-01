(** * LinuxProcessSem.Ns.Step — the namespace layer's step, derived from a core

    [NsStep] takes any core that satisfies [Ns.ProcsIface.PROCS_CORE] and
    defines the layer's step relation from it, with no relation of its own:
    [nstep] is the core's step restricted to the process the lineage picks.
    The theorems below are what a statement about one process's run needs:

    - at an instruction of a one-process system, [nstep] is the released
      single-process step ([nstep_instr_iff_next], [nstep_instr_iff_err]);
    - a lineage step that adds an entry gives the new child, with a0 = 0 and
      the successor's shared state, and moves the lineage to it
      ([nstep_clone_moves_lineage]);
    - while the parents are non-interfering, a step a process outside the
      focus's subtree takes leaves the focus's namespace view unchanged
      ([pni_parent_step_preserves_view]), and the predicate holds again
      after any step ([pni_after_step]).

    [parents_noninterfering] and [descendant_or_self] are the layer's own,
    defined from the core's step, process table and parent links. *)

From Stdlib Require Import List PArith.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables ProcsIface.
Import ListNotations.

Module NsStep (Import C : PROCS_CORE).

  Definition nstep (ctx : StepCtx) (P : pconfig) (evs : list event) (r : pstep_to) : Prop :=
    exists p, lineage_pick P p /\ pstep_at ctx p P evs r.

  Lemma nstep_sub : forall ctx P evs r, nstep ctx P evs r -> pstep_cfg ctx P evs r.
  Proof. intros ctx P evs r (p & _ & H). exact (pstep_at_sub ctx p P evs r H). Qed.

  Theorem nstep_instr_iff_next : forall ctx c evs P', at_instruction c ->
    (nstep ctx (one_proc c) evs (PNext P')
     <-> exists c', P' = one_proc c' /\ sstep_cfg ctx c evs (SNext c')).
  Proof.
    intros ctx c evs P' Hi. split.
    - intros (p & Hl & Ha).
      apply (proj1 (lineage_pick_one c p)) in Hl. subst p.
      apply (proj1 (pstep_at_one ctx c evs (PNext P'))) in Ha.
      exact (proj1 (pstep_instr_single_next ctx c evs P' Hi) Ha).
    - intros H. exists one_pid. split.
      + exact (proj2 (lineage_pick_one c one_pid) eq_refl).
      + apply (proj2 (pstep_at_one ctx c evs (PNext P'))).
        exact (proj2 (pstep_instr_single_next ctx c evs P' Hi) H).
  Qed.

  Theorem nstep_instr_iff_err : forall ctx c evs, at_instruction c ->
    (nstep ctx (one_proc c) evs PError <-> sstep_cfg ctx c evs SError).
  Proof.
    intros ctx c evs Hi. split.
    - intros (p & Hl & Ha).
      apply (proj1 (lineage_pick_one c p)) in Hl. subst p.
      apply (proj1 (pstep_at_one ctx c evs PError)) in Ha.
      exact (proj1 (pstep_instr_single_err ctx c evs Hi) Ha).
    - intros H. exists one_pid. split.
      + exact (proj2 (lineage_pick_one c one_pid) eq_refl).
      + apply (proj2 (pstep_at_one ctx c evs PError)).
        exact (proj2 (pstep_instr_single_err ctx c evs Hi) H).
  Qed.

  Theorem nstep_clone_moves_lineage : forall ctx P evs P',
    nstep ctx P evs (PNext P') ->
    length (pcfg_procs P') > length (pcfg_procs P) ->
    exists e sh, child_projection P P' = Some (e, sh) /\ entry_a0_zero e
                 /\ sh = pcfg_shared P' /\ lineage_pick P' (pe_pid e).
  Proof.
    intros ctx P evs P' (p & Hl & Ha) Hlen.
    destruct (child_projection_of_clone ctx P evs P'
                (pstep_at_sub ctx p P evs (PNext P') Ha) Hlen) as (e & sh & Hc & Ha0 & Hsh).
    exists e, sh. split; [exact Hc|]. split; [exact Ha0|]. split; [exact Hsh|].
    exact (lineage_pick_clone ctx P p evs P' e sh Hl Ha Hc).
  Qed.

  (** [q] is [f] or a descendant of [f]: parent links of [P] lead from [q]
      to [f]. *)
  Inductive descendant_or_self (P : pconfig) (f : Pid) : Pid -> Prop :=
  | dos_self : descendant_or_self P f f
  | dos_child : forall p q e,
      descendant_or_self P f p -> look P q = Some e -> pe_parent e = Some p ->
      descendant_or_self P f q.

  (** The processes outside the subtree of the focus [f] do not change what
      [f] reads, until [cut_at f] holds: after every step of the system, a
      step taken by a process outside that subtree keeps the read projection
      [rp] of [f] the same up to [eqm], which may ignore the exchange objects
      [xs] names, and the predicate holds again.  Coinductive: a run that
      never reaches the cut is held to it forever. *)
  CoInductive parents_noninterfering (RV : Type) (rp : pconfig -> Pid -> RV)
      (eqm : list OfdId -> RV -> RV -> Prop) (xs : pconfig -> Pid -> list OfdId)
      (cut_at : Pid -> pconfig -> Prop) (ctx : StepCtx) (f : Pid) : pconfig -> Prop :=
  | pni_cut : forall P, cut_at f P -> parents_noninterfering RV rp eqm xs cut_at ctx f P
  | pni_steps : forall P,
      (forall evs P' p, pstep_at ctx p P evs (PNext P') ->
         (~ descendant_or_self P f p -> eqm (xs P f) (rp P' f) (rp P f))
         /\ parents_noninterfering RV rp eqm xs cut_at ctx f P') ->
      parents_noninterfering RV rp eqm xs cut_at ctx f P.

  Lemma pni_unfold : forall RV rp eqm xs cut_at ctx f P,
    parents_noninterfering RV rp eqm xs cut_at ctx f P
    <-> cut_at f P
        \/ (forall evs P' p, pstep_at ctx p P evs (PNext P') ->
              (~ descendant_or_self P f p -> eqm (xs P f) (rp P' f) (rp P f))
              /\ parents_noninterfering RV rp eqm xs cut_at ctx f P').
  Proof.
    intros RV rp eqm xs cut_at ctx f P. split.
    - intros H. destruct H as [P0 Hc | P0 Hs]; [left; exact Hc | right; exact Hs].
    - intros [Hc | Hs]; [apply pni_cut; exact Hc | apply pni_steps; exact Hs].
  Qed.

  Lemma pni_after_step : forall RV rp eqm xs cut_at ctx f P evs P' p,
    parents_noninterfering RV rp eqm xs cut_at ctx f P -> ~ cut_at f P ->
    pstep_at ctx p P evs (PNext P') ->
    parents_noninterfering RV rp eqm xs cut_at ctx f P'.
  Proof.
    intros RV rp eqm xs cut_at ctx f P evs P' p Hpni Hcut Hs.
    apply (proj1 (pni_unfold RV rp eqm xs cut_at ctx f P)) in Hpni.
    destruct Hpni as [Hc | Hall]; [contradiction|].
    exact (proj2 (Hall evs P' p Hs)).
  Qed.

  (** The generic view of a focused process: its namespace context and the
      shared namespace state.  A consumer that needs a narrower view (only
      the objects the process can reach, less the exchange objects) passes
      its own to [parents_noninterfering]; this one is the coarsest that
      still names everything the layer reads. *)
  Definition ns_view (P : pconfig) (f : Pid) : option (NsCtx * NsState) :=
    match look P f with
    | Some e => Some (pe_nsctx e, sh_nsstate (pcfg_shared P))
    | None => None
    end.

  Definition ns_view_eq (_ : list OfdId) (a b : option (NsCtx * NsState)) : Prop := a = b.

  Theorem pni_parent_step_preserves_view : forall xs cut_at ctx f P evs P' p,
    parents_noninterfering (option (NsCtx * NsState)) ns_view ns_view_eq xs cut_at ctx f P ->
    ~ cut_at f P ->
    pstep_at ctx p P evs (PNext P') ->
    ~ descendant_or_self P f p ->
    ns_view P' f = ns_view P f.
  Proof.
    intros xs cut_at ctx f P evs P' p Hpni Hcut Hs Hd.
    apply (proj1 (pni_unfold _ ns_view ns_view_eq xs cut_at ctx f P)) in Hpni.
    destruct Hpni as [Hc | Hall]; [contradiction|].
    exact (proj1 (Hall evs P' p Hs) Hd).
  Qed.

End NsStep.
