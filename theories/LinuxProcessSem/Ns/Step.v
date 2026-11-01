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
      ([pni_parent_step_preserves_view]). *)

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

  Theorem pni_parent_step_preserves_view : forall xs ctx f P evs P' p,
    parents_noninterfering (option (NsCtx * NsState)) ns_view ns_view_eq xs ctx f P ->
    ~ cut_reached f P ->
    pstep_cfg ctx P evs (PNext P') ->
    stepped_by P evs (PNext P') p ->
    ~ descendant_or_self P f p ->
    ns_view P' f = ns_view P f.
  Proof.
    intros xs ctx f P evs P' p Hpni Hcut Hs Hb Hd.
    apply (proj1 (pni_unfold _ ns_view ns_view_eq xs ctx f P)) in Hpni.
    destruct Hpni as [Hc | Hall]; [contradiction|].
    destruct (Hall evs P' Hs) as [Hpres _].
    exact (Hpres p Hb Hd).
  Qed.

End NsStep.
