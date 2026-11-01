(** * LinuxProcessSem.Checks.Cases.Ns.ProcsIfaceCases — the core interface can be instantiated

    [Ns.ProcsIface.PROCS_CORE] states the multi-process core's names and the
    laws the namespace layer relies on.  This file gives one module that
    satisfies all of them and applies [Ns.Step.NsStep] to it, so that a law
    set that could not hold together, or a functor that does not type-check
    against the interface, fails this build.  The instance is deliberately
    small: no step exists, so every law about a step holds vacuously. *)

From Stdlib Require Import List PArith.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables ProcsIface Step.
Import ListNotations.

Module ToyCore <: PROCS_CORE.
  Definition Pid := positive.
  Definition StepCtx := unit.
  Definition config := unit.
  Definition event := unit.
  Definition step_to := option unit.
  Definition SNext (c : config) : step_to := Some c.
  Definition SError : step_to := None.
  Definition sstep_cfg (_ : StepCtx) (_ : config) (_ : list event) (_ : step_to) : Prop := False.
  Definition at_instruction (_ : config) : Prop := True.
  Definition clone_success (_ _ : config) : bool := false.
  Definition wait4_intercept (_ : config) : bool := false.
  Definition child_pid (_ : config) (_ : positive) : Prop := False.

  Definition OfdId := positive.
  Definition ofd_eq_dec : forall a b : OfdId, {a = b} + {a <> b} := Pos.eq_dec.
  Definition Fd := positive.
  Definition ProcessEntry := unit.
  Definition shared := unit.
  Definition pconfig := unit.
  Definition pe_pid (_ : ProcessEntry) : positive := 1%positive.
  Definition pe_parent (_ : ProcessEntry) : option positive := None.
  Definition pe_ofd (_ : ProcessEntry) : list (Fd * OfdId) := [].
  Definition pe_nsctx (_ : ProcessEntry) : NsCtx :=
    mkNsCtx 1%positive 1%positive (1%positive, 1%positive) (1%positive, 1%positive).
  Definition sh_nsstate (_ : shared) : NsState := mkNsState [] [].
  Definition pcfg_procs (_ : pconfig) : list (Pid * ProcessEntry) := [(1%positive, tt)].
  Definition pcfg_root (_ : pconfig) : positive := 1%positive.
  Definition pcfg_shared (_ : pconfig) : shared := tt.
  Definition look (_ : pconfig) (p : positive) : option ProcessEntry :=
    if Pos.eqb p 1 then Some tt else None.
  Definition pe_cfg (_ : shared) (_ : ProcessEntry) : config := tt.
  Definition one_pid : positive := 1%positive.
  Definition one_proc (_ : config) : pconfig := tt.
  Definition multiproc_allowed (_ : pconfig) (_ : config) : bool := true.

  Definition pstep_to := option unit.
  Definition PNext (P : pconfig) : pstep_to := Some P.
  Definition PError : pstep_to := None.
  Definition pstep_cfg (_ : StepCtx) (_ : pconfig) (_ : list event) (_ : pstep_to) : Prop := False.
  Definition pstep_at (_ : StepCtx) (_ : positive) (_ : pconfig) (_ : list event) (_ : pstep_to) : Prop :=
    False.
  Definition lineage_pick (_ : pconfig) (p : positive) : Prop := p = 1%positive.
  Definition clone_result (P : pconfig) (_ : ProcessEntry) (_ : config) (_ : positive) : pconfig := P.
  Definition child_projection (_ _ : pconfig) : option (ProcessEntry * shared) := None.
  Definition entry_a0_zero (_ : ProcessEntry) : Prop := True.

  Lemma pstep_to_cases : forall r, (exists P, r = PNext P) \/ r = PError.
  Proof. intros [[]|]; [left; exists tt; reflexivity | right; reflexivity]. Qed.

  Lemma pstep_instr_single_next : forall ctx c evs P', at_instruction c ->
    (pstep_cfg ctx (one_proc c) evs (PNext P')
     <-> exists c', P' = one_proc c' /\ sstep_cfg ctx c evs (SNext c')).
  Proof.
    intros ctx c evs P' _. cbv [pstep_cfg sstep_cfg].
    split; [intros [] | intros (c' & _ & [])].
  Qed.

  Lemma pstep_instr_single_err : forall ctx c evs, at_instruction c ->
    (pstep_cfg ctx (one_proc c) evs PError <-> sstep_cfg ctx c evs SError).
  Proof. intros ctx c evs _. cbv [pstep_cfg sstep_cfg]. split; intros H; exact H. Qed.

  Lemma pstep_single_next : forall ctx c evs P',
    (forall c', sstep_cfg ctx c evs (SNext c') -> clone_success c c' = false) ->
    wait4_intercept c = false ->
    (pstep_cfg ctx (one_proc c) evs (PNext P')
     <-> exists c', P' = one_proc c' /\ sstep_cfg ctx c evs (SNext c')).
  Proof.
    intros ctx c evs P' _ _. cbv [pstep_cfg sstep_cfg].
    split; [intros [] | intros (c' & _ & [])].
  Qed.

  Lemma pstep_single_err : forall ctx c evs, wait4_intercept c = false ->
    (pstep_cfg ctx (one_proc c) evs PError <-> sstep_cfg ctx c evs SError).
  Proof. intros ctx c evs _. cbv [pstep_cfg sstep_cfg]. split; intros H; exact H. Qed.

  Lemma pstep_at_sub : forall ctx p P evs r, pstep_at ctx p P evs r -> pstep_cfg ctx P evs r.
  Proof. intros ctx p P evs r H. destruct H. Qed.

  Lemma pstep_cfg_has_actor : forall ctx P evs r,
    pstep_cfg ctx P evs r -> exists p, pstep_at ctx p P evs r.
  Proof. intros ctx P evs r H. destruct H. Qed.

  Lemma lineage_pick_one : forall c p, lineage_pick (one_proc c) p <-> p = one_pid.
  Proof. intros c p. cbv [lineage_pick one_pid]. split; intros H; exact H. Qed.

  Lemma pstep_at_one : forall ctx c evs r,
    pstep_at ctx one_pid (one_proc c) evs r <-> pstep_cfg ctx (one_proc c) evs r.
  Proof. intros ctx c evs r. cbv [pstep_at pstep_cfg]. split; intros H; exact H. Qed.

  Lemma pstep_clone_law : forall ctx P e evs c' q,
    look P (pe_pid e) = Some e ->
    sstep_cfg ctx (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    clone_success (pe_cfg (pcfg_shared P) e) c' = true ->
    child_pid c' q ->
    look P q = None ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    pstep_cfg ctx P evs (PNext (clone_result P e c' q)).
  Proof. intros ctx P e evs c' q _ H. destruct H. Qed.

  Lemma child_projection_of_clone : forall ctx P evs P',
    pstep_cfg ctx P evs (PNext P') ->
    length (pcfg_procs P') > length (pcfg_procs P) ->
    exists e sh, child_projection P P' = Some (e, sh) /\ entry_a0_zero e /\ sh = pcfg_shared P'.
  Proof. intros ctx P evs P' H. destruct H. Qed.

  Lemma lineage_pick_clone : forall ctx P p evs P' e sh,
    lineage_pick P p ->
    pstep_at ctx p P evs (PNext P') ->
    child_projection P P' = Some (e, sh) ->
    lineage_pick P' (pe_pid e).
  Proof. intros ctx P p evs P' e sh _ H. destruct H. Qed.
End ToyCore.

Module ToyStep := NsStep ToyCore.

Check ToyStep.nstep.
Check ToyStep.nstep_instr_iff_next.
Check ToyStep.nstep_instr_iff_err.
Check ToyStep.nstep_clone_moves_lineage.
Check ToyStep.pni_parent_step_preserves_view.
Check ToyStep.pni_after_step.
