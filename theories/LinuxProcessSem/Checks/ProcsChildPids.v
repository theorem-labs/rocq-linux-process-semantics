(** * LinuxProcessSem.Checks.ProcsChildPids — each entry's list of unreaped children is the table's

    Not part of the trusted specification: QA on the multi-process core
    and [State.procst_child_pids], in the sense of [Checks.Examples]'s
    header, under its first reason: the statements are universally
    quantified over configurations and steps.

    ** What this pins

    [State.procst_child_pids] is the pids a process's clones returned and
    no [wait4] has reaped, oldest first: the kernel's [task->children].
    The released clone appends ([State.with_child]); the core's reap arms
    remove ([Procs.reap_model]).  This file proves the list is the table.

    - [Checks.ProcsChildPidsFrame]: a released step that is not a
      successful clone keeps the list; a successful clone appends the pid
      it returned.
    - [pstep_at_preserves_child_pids]: in a well-formed table, if every
      RUNNING entry's list is the keys of its children in the table, in
      table order, a step keeps that so.  A halted entry is out of the
      invariant: when it exits, [Procs.absorb] orphans its children (their
      parent becomes [None]), and its list keeps the pids it had, which
      nothing reads again, since a halted entry takes no step.
      [child_pids_ok_one_proc] is the launch; [child_pids_reachable] the
      two together over any run.
    - [owned_wait4_answers_child]: a caller with a child in the table is
      never answered by the released [wait4]; the core's arms answer it,
      and a reap returns a pid of its own list. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ProcsWellFormed ProcsPrivateFrame ProcsClockSync ProcsSyncOnce ProcsPeerGates
  ProcsWait4Gate ProcsChildPidsFrame.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   The table side
   ========================================================================= *)

(** [kv] is a child of [p]. *)
Definition is_child_of (p : Pid) (kv : Pid * ProcessEntry) : bool :=
  match pe_parent (snd kv) with Some q => bv_eqb q p | None => false end.

(** The keys of [p]'s children, in table order. *)
Definition children_keys (ps : list (Pid * ProcessEntry)) (p : Pid) : list Pid :=
  List.map fst (List.filter (is_child_of p) ps).

(** No child in the table: no key either. *)
Lemma children_keys_nil_of_no_child : forall P p,
  has_child_b P p = false -> children_keys (pcfg_procs P) p = [].
Proof.
  intros P p H. unfold children_keys.
  destruct (List.filter (is_child_of p) (pcfg_procs P)) as [|kv l] eqn:E;
    [reflexivity|].
  exfalso.
  assert (Hin : List.In kv (List.filter (is_child_of p) (pcfg_procs P)))
    by (rewrite E; left; reflexivity).
  apply List.filter_In in Hin as [Hin Hc].
  unfold has_child_b, children_of in H.
  match type of H with
  | context [List.map snd ?t] =>
      destruct (List.map snd t) as [|y ys] eqn:Em; [|cbn in H; discriminate H];
      apply List.map_eq_nil in Em;
      assert (Hin' : List.In kv t)
        by (apply List.filter_In; split; [exact Hin | exact Hc]);
      rewrite Em in Hin'; exact Hin'
  end.
Qed.

(** THE INVARIANT: every running entry's list is its children's keys. *)
Definition child_pids_ok (P : pconfig) : Prop :=
  forall k f, look P k = Some f -> m_halted (pe_model f) = None ->
    m_child_pids (pe_model f) = children_keys (pcfg_procs P) k.

Lemma children_keys_replace : forall ps p e' k,
  (forall x, List.In (p, x) ps -> pe_parent e' = pe_parent x) ->
  children_keys (replace_in ps p e') k = children_keys ps k.
Proof.
  induction ps as [|[a x] r IH]; intros p e' k H; [reflexivity|].
  cbn [replace_in fst]. destruct (bv_eqb a p) eqn:E.
  - apply bv_eqb_true_eq in E. subst a.
    assert (Hc : is_child_of k (p, e') = is_child_of k (p, x))
      by (unfold is_child_of; cbn [snd]; rewrite (H x (or_introl eq_refl)); reflexivity).
    unfold children_keys. cbn [List.filter]. rewrite Hc.
    destruct (is_child_of k (p, x)); reflexivity.
  - specialize (IH p e' k (fun y Hy => H y (or_intror Hy))).
    unfold children_keys in IH |- *. cbn [List.filter].
    destruct (is_child_of k (a, x)); cbn [List.map fst]; rewrite IH; reflexivity.
Qed.

Lemma root_child_ppid_one_child : forall root t k kv,
  is_child_of k (root_child_ppid_one root t kv) = is_child_of k kv.
Proof.
  intros root t k [q f]. unfold is_child_of.
  pose proof (root_child_ppid_one_fields root t q f) as (_ & Hp & _).
  rewrite Hp. reflexivity.
Qed.

Lemma children_keys_root_children_ppid : forall root t ps k,
  children_keys (root_children_ppid root t ps) k = children_keys ps k.
Proof.
  intros root t ps k. unfold root_children_ppid.
  induction ps as [|kv ps IH]; [reflexivity|].
  unfold children_keys in IH |- *. cbn [List.map List.filter].
  rewrite root_child_ppid_one_child.
  destruct (is_child_of k kv); cbn [List.map];
    rewrite ?root_child_ppid_one_fst, IH; reflexivity.
Qed.

Lemma child_pids_ok_root_children_ppid : forall P root t,
  child_pids_ok P ->
  child_pids_ok (mkPCfg (root_children_ppid root t (pcfg_procs P))
    (pcfg_root P) (pcfg_shared P)).
Proof.
  intros P root t Hok k f Hk Hfh.
  unfold look in Hk. cbn [pcfg_procs] in Hk |- *.
  rewrite look_in_root_children_ppid in Hk.
  destruct (look_in (pcfg_procs P) k) as [g|] eqn:Hg;
    cbn [option_map] in Hk; [|discriminate Hk].
  injection Hk as <-.
  pose proof (root_child_ppid_one_fields root t k g)
    as (_ & _ & _ & _ & _ & Hhalt & Hcp).
  rewrite Hhalt in Hfh. rewrite Hcp, children_keys_root_children_ppid.
  exact (Hok _ _ Hg Hfh).
Qed.

Lemma child_pids_ok_first_root_pin : forall P e m',
  child_pids_ok P ->
  child_pids_ok (mkPCfg
    (first_root_pin_children P e m' (pcfg_procs P))
    (pcfg_root P) (pcfg_shared P)).
Proof.
  intros P e m' Hok. unfold first_root_pin_children.
  destruct (bv_eqb (pe_pid e) (pcfg_root P)),
    (m_tid (pe_model e)), (m_tid m'); try exact Hok;
    apply child_pids_ok_root_children_ppid; exact Hok.
Qed.

Lemma orphan_one_fst : forall p kv, fst (orphan_one p kv) = fst kv.
Proof.
  intros p [a x]. unfold orphan_one. cbn [fst snd].
  destruct (_ && _); reflexivity.
Qed.

Lemma orphan_one_child : forall p k kv,
  k <> p -> is_child_of k (orphan_one p kv) = is_child_of k kv.
Proof.
  intros p k [a x] Hne. unfold orphan_one. cbn [fst snd].
  destruct (negb (bv_eqb a p) && match pe_parent x with Some q => bv_eqb q p | None => false end)
    eqn:Eo; [|reflexivity].
  apply andb_true_iff in Eo as [_ Eo].
  unfold is_child_of. cbn [snd with_parent pe_parent].
  destruct (pe_parent x) as [q|]; [|discriminate Eo].
  apply bv_eqb_true_eq in Eo. subst q.
  symmetry. apply (pid_neq_eqb p k (fun E => Hne (eq_sym E))).
Qed.

Lemma children_keys_orphan : forall m p ps k,
  k <> p -> children_keys (orphan_at_exit m p ps) k = children_keys ps k.
Proof.
  intros m p ps k Hne. unfold orphan_at_exit.
  destruct (m_halted m); [|reflexivity].
  unfold orphan_children. induction ps as [|kv r IH]; [reflexivity|].
  unfold children_keys in IH |- *. cbn [List.map List.filter].
  rewrite (orphan_one_child p k kv Hne).
  destruct (is_child_of k kv); cbn [List.map]; rewrite ?orphan_one_fst, IH; reflexivity.
Qed.

Lemma children_keys_app : forall ps q c k,
  children_keys (ps ++ [(q, c)]) k
  = children_keys ps k ++ (if is_child_of k (q, c) then [q] else []).
Proof.
  intros ps q c k. unfold children_keys. rewrite List.filter_app, List.map_app.
  cbn [List.filter]. destruct (is_child_of k (q, c)); reflexivity.
Qed.

Lemma children_keys_drop : forall ps q k,
  List.NoDup (List.map fst ps) ->
  children_keys (drop_in ps q) k
  = List.filter (fun x => negb (bv_eqb x q)) (children_keys ps k).
Proof.
  induction ps as [|[a x] r IH]; intros q k Hnd; [reflexivity|].
  cbn [List.map fst] in Hnd. apply NoDup_cons_iff in Hnd as [Hna Hnd].
  cbn [drop_in fst]. destruct (bv_eqb a q) eqn:E.
  - apply bv_eqb_true_eq in E. subst a.
    assert (Hr : children_keys r k
                 = List.filter (fun x0 => negb (bv_eqb x0 q)) (children_keys r k)).
    { symmetry. apply List.forallb_filter_id.
      apply List.forallb_forall. intros y Hy.
      unfold children_keys in Hy. apply List.in_map_iff in Hy as ([y' z] & Hyy & Hy).
      cbn [fst] in Hyy. subst y'.
      apply List.filter_In in Hy as [Hy _].
      apply negb_true_iff. destruct (bv_eqb y q) eqn:Ey; [|reflexivity].
      apply bv_eqb_true_eq in Ey. subst y. exfalso. apply Hna.
      apply List.in_map_iff. exists (q, z). split; [reflexivity | exact Hy]. }
    unfold children_keys at 2. cbn [List.filter].
    destruct (is_child_of k (q, x)); cbn [List.map fst List.filter];
      [rewrite bv_eqb_same; cbn [negb]|]; exact Hr.
  - specialize (IH q k Hnd).
    unfold children_keys in IH |- *. cbn [List.filter].
    destruct (is_child_of k (a, x)); cbn [List.map fst List.filter];
      [rewrite E; cbn [negb]; f_equal|]; exact IH.
Qed.

Lemma look_in_app_l : forall (l1 l2 : list (Pid * ProcessEntry)) p x,
  look_in l1 p = Some x -> look_in (l1 ++ l2) p = Some x.
Proof. intros l1 l2 p x H. rewrite look_in_app, H. reflexivity. Qed.

Lemma look_in_None_notin' : forall ps p x, look_in ps p = None -> ~ List.In (p, x) ps.
Proof.
  induction ps as [|[a y] r IH]; intros p x H Hin; [destruct Hin|].
  cbn [look_in fst snd] in H. destruct (bv_eqb a p) eqn:E; [discriminate H|].
  destruct Hin as [Hh | Hin].
  - injection Hh as -> ->. rewrite bv_eqb_same in E. discriminate E.
  - exact (IH p x H Hin).
Qed.

Lemma look_in_replace_keys_none : forall ps p e' q,
  look_in ps q = None -> look_in (replace_in ps p e') q = None \/ q = p.
Proof.
  induction ps as [|[a y] r IH]; intros p e' q H; [left; reflexivity|].
  cbn [look_in fst snd] in H. destruct (bv_eqb a q) eqn:E; [discriminate H|].
  cbn [replace_in fst]. destruct (bv_eqb a p) eqn:Ep.
  - apply bv_eqb_true_eq in Ep. subst a. cbn [look_in fst snd].
    destruct (bv_eqb p q) eqn:Epq; [right; apply bv_eqb_true_eq in Epq; symmetry; exact Epq|].
    left. exact H.
  - cbn [look_in fst snd]. rewrite E. exact (IH p e' q H).
Qed.

Lemma look_in_drop_same : forall ps q,
  List.NoDup (List.map fst ps) -> look_in (drop_in ps q) q = None.
Proof.
  induction ps as [|[a y] r IH]; intros q Hnd; [reflexivity|].
  cbn [List.map fst] in Hnd. apply NoDup_cons_iff in Hnd as [Hna Hnd].
  cbn [drop_in fst]. destruct (bv_eqb a q) eqn:E.
  - apply bv_eqb_true_eq in E. subst a.
    destruct (look_in r q) eqn:Hl; [|reflexivity].
    exfalso. apply Hna. apply List.in_map_iff. exists (q, p).
    split; [reflexivity | exact (look_in_In _ _ _ Hl)].
  - cbn [look_in fst snd]. rewrite E. exact (IH q Hnd).
Qed.

Lemma NoDup_replace_keys : forall ps p e',
  List.map fst (replace_in ps p e') = List.map fst ps.
Proof.
  induction ps as [|[a y] r IH]; intros p e'; [reflexivity|].
  cbn [replace_in fst]. destruct (bv_eqb a p) eqn:E.
  - apply bv_eqb_true_eq in E. subst a. reflexivity.
  - cbn [List.map fst]. rewrite IH. reflexivity.
Qed.


(* =========================================================================
   Every producing arm keeps the invariant
   ========================================================================= *)

Lemma wf_parts : forall P, pconfig_wf P ->
  (forall kv, List.In kv (pcfg_procs P) -> fst kv = pe_pid (snd kv))
  /\ (forall kv q, List.In kv (pcfg_procs P) -> pe_parent (snd kv) = Some q ->
        q <> fst kv /\ exists f, List.In (q, f) (pcfg_procs P) /\ m_halted (pe_model f) = None)
  /\ List.NoDup (List.map fst (pcfg_procs P)).
Proof. intros P H. apply wf_iff in H as [Htbl _]. exact Htbl. Qed.

(** The entry a key finds is the only one with that key. *)
Lemma same_key : forall P p x y,
  pconfig_wf P -> look P p = Some x -> List.In (p, y) (pcfg_procs P) -> y = x.
Proof.
  intros P p x y Hwf Hl Hin. destruct (wf_parts P Hwf) as (_ & _ & Hnd).
  exact (In_unique _ _ _ _ Hnd Hin (look_in_In _ _ _ Hl)).
Qed.

(** No entry is a child of a key the table does not hold. *)
Lemma children_keys_absent : forall P q,
  pconfig_wf P -> look P q = None -> children_keys (pcfg_procs P) q = [].
Proof.
  intros P q Hwf Hq. destruct (wf_parts P Hwf) as (_ & Hpar & _).
  destruct (children_keys (pcfg_procs P) q) as [|y l] eqn:Hc; [reflexivity|].
  exfalso. assert (Hy : List.In y (children_keys (pcfg_procs P) q)) by (rewrite Hc; left; reflexivity).
  unfold children_keys in Hy. apply List.in_map_iff in Hy as ([k x] & _ & Hy).
  apply List.filter_In in Hy as [Hin Hch]. unfold is_child_of in Hch. cbn [snd] in Hch.
  destruct (pe_parent x) as [q'|] eqn:Hp; [|discriminate Hch].
  apply bv_eqb_true_eq in Hch. subst q'.
  destruct (Hpar _ _ Hin Hp) as (_ & f & Hf & _).
  exact (look_in_None_notin' _ _ _ Hq Hf).
Qed.

(** [absorb] keeps the invariant when the stepping entry's list is kept. *)
Lemma child_pids_ok_absorb : forall P e c',
  pconfig_wf P -> child_pids_ok P ->
  look P (pe_pid e) = Some e -> m_halted (pe_model e) = None ->
  cp_of (cfg_model c') = cp_of (pe_model e) ->
  child_pids_ok (absorb P e c').
Proof.
  intros P e c' Hwf Hok Hl Hh Hcp k f Hk Hfh.
  set (Q := mkPCfg
    (first_root_pin_children P e (cfg_model c') (pcfg_procs P))
    (pcfg_root P) (pcfg_shared P)).
  assert (HQwf : pconfig_wf Q)
    by exact (pconfig_wf_first_root_pin P e (cfg_model c') Hwf).
  assert (HQok : child_pids_ok Q)
    by exact (child_pids_ok_first_root_pin P e (cfg_model c') Hok).
  assert (HQl : look Q (pe_pid e) = Some e).
  { unfold Q, look. cbn [pcfg_procs].
    apply look_in_first_root_pin_children_self. exact Hl. }
  assert (Hkeys : forall k', children_keys (pcfg_procs Q) k'
    = children_keys (pcfg_procs P) k').
  { intros k'. unfold Q. cbn [pcfg_procs]. unfold first_root_pin_children.
    destruct (bv_eqb (pe_pid e) (pcfg_root P)),
      (m_tid (pe_model e)), (m_tid (cfg_model c')); try reflexivity;
      apply children_keys_root_children_ppid. }
  assert (Hrep : forall k', children_keys (replace_in (pcfg_procs Q) (pe_pid e) (pe_absorb e c')) k'
                            = children_keys (pcfg_procs P) k').
  { intros k'. transitivity (children_keys (pcfg_procs Q) k'); [|apply Hkeys].
    apply children_keys_replace. intros x Hx.
    rewrite (same_key Q _ _ _ HQwf HQl Hx). reflexivity. }
  destruct (bv_eqb k (pe_pid e)) eqn:Ek.
  - apply bv_eqb_true_eq in Ek. subst k.
    rewrite (look_absorb_self P e c' Hl) in Hk. injection Hk as <-.
    change (m_halted (cfg_model c') = None) in Hfh.
    change (m_child_pids (cfg_model c') = children_keys
      (orphan_at_exit (cfg_model c') (pe_pid e)
        (replace_in (pcfg_procs Q) (pe_pid e) (pe_absorb e c'))) (pe_pid e)).
    rewrite orphan_at_exit_running by exact Hfh. rewrite Hrep.
    change (cp_of (cfg_model c') = children_keys (pcfg_procs P) (pe_pid e)).
    rewrite Hcp. exact (Hok _ _ Hl Hh).
  - assert (Hne : k <> pe_pid e) by (intros E; subst; rewrite bv_eqb_same in Ek; discriminate Ek).
    change (look_in (orphan_at_exit (cfg_model c') (pe_pid e)
      (replace_in (pcfg_procs Q) (pe_pid e) (pe_absorb e c'))) k = Some f) in Hk.
    rewrite orphan_at_exit_map, look_in_orphan, look_in_replace_other in Hk by exact Hne.
    destruct (look_in (pcfg_procs Q) k) as [f0|] eqn:Hf0; cbn [option_map] in Hk; [|discriminate Hk].
    injection Hk as Hk.
    assert (Hm : pe_model f = pe_model f0)
      by (destruct (orphan_slot_orphaned (cfg_model c') (pe_pid e) k f0) as [E | (_ & E)];
          rewrite <- Hk, E; reflexivity).
    rewrite Hm in Hfh |- *.
    change (m_child_pids (pe_model f0) = children_keys
      (orphan_at_exit (cfg_model c') (pe_pid e)
        (replace_in (pcfg_procs Q) (pe_pid e) (pe_absorb e c'))) k).
    rewrite children_keys_orphan by exact Hne. rewrite Hrep.
    rewrite (HQok _ _ Hf0 Hfh). apply Hkeys.
Qed.

(** Replacing an entry by one with the same parent, list and halt state
    keeps the invariant: the sync and the root pin. *)
Lemma child_pids_ok_replace : forall P p x x' root' S',
  pconfig_wf P -> child_pids_ok P -> look P p = Some x ->
  pe_parent x' = pe_parent x ->
  m_child_pids (pe_model x') = m_child_pids (pe_model x) ->
  m_halted (pe_model x') = m_halted (pe_model x) ->
  child_pids_ok (mkPCfg (replace_in (pcfg_procs P) p x') root' S').
Proof.
  intros P p x x' root' S' Hwf Hok Hl Hpar Hcp Hh k f Hk Hfh.
  unfold look in Hk. cbn [pcfg_procs] in Hk |- *.
  rewrite children_keys_replace
    by (intros y Hy; rewrite (same_key P _ _ _ Hwf Hl Hy); exact Hpar).
  destruct (bv_eqb k p) eqn:Ek.
  - apply bv_eqb_true_eq in Ek. subst k.
    rewrite look_in_replace_same in Hk by (unfold look in Hl; rewrite Hl; discriminate).
    injection Hk as <-. rewrite Hh in Hfh. rewrite Hcp. exact (Hok _ _ Hl Hfh).
  - assert (Hne : k <> p) by (intros E; subst; rewrite bv_eqb_same in Ek; discriminate Ek).
    rewrite look_in_replace_other in Hk by exact Hne. exact (Hok _ _ Hk Hfh).
Qed.

Lemma child_pids_ok_pin_root : forall P r t,
  pconfig_wf P -> child_pids_ok P -> look P (pcfg_root P) = Some r ->
  child_pids_ok (pin_root P r t).
Proof.
  intros P r t Hwf Hok Hl. unfold pin_root.
  destruct (m_tid (pe_model r)).
  - apply (child_pids_ok_replace P (pcfg_root P) r); try assumption; reflexivity.
  - set (Q := mkPCfg (root_children_ppid (pcfg_root P) t (pcfg_procs P))
      (pcfg_root P) (pcfg_shared P)).
    assert (HQwf : pconfig_wf Q).
    { unfold Q. apply wf_iff. cbn [pcfg_procs pcfg_root].
      apply tbl_root_children_ppid; apply wf_iff in Hwf; tauto. }
    assert (HQok : child_pids_ok Q)
      by (apply child_pids_ok_root_children_ppid; exact Hok).
    assert (HQl : look Q (pcfg_root P) = Some r).
    { unfold Q, look. cbn [pcfg_procs].
      rewrite look_in_root_children_ppid_root. exact Hl. }
    change (child_pids_ok (mkPCfg (replace_in (pcfg_procs Q) (pcfg_root P)
      (mkEntry (pe_pid r) (pe_parent r) (pe_ms r) (with_tid t (pe_model r))
        (pe_ofd r) (pe_nsctx r))) (pcfg_root P) (pcfg_shared P))).
    apply (child_pids_ok_replace Q (pcfg_root P) r); try assumption; reflexivity.
Qed.

Lemma cp_sync_entry : forall P e,
  m_child_pids (pe_model (sync_entry P e)) = m_child_pids (pe_model e).
Proof.
  intros P e. unfold sync_entry, uts_fill, pin_fill. cbn [pe_model].
  destruct (fstat_path e) as [p|]; [destruct (statpin_lookup _ p); [|destruct (pin_any _ p)]|];
    destruct (m_utsname _); try destruct (uts_any _); reflexivity.
Qed.

(** A successful clone appends the child at the table's end and its pid at
    the end of the parent's list; the child's own list is empty. *)
Lemma child_pids_ok_clone : forall P e c' q,
  pconfig_wf P -> child_pids_ok P ->
  look P (pe_pid e) = Some e -> m_halted (pe_model e) = None ->
  look P q = None ->
  cp_of (cfg_model c') = cp_of (pe_model e) ++ [q] ->
  child_pids_ok (clone_result P e c' q).
Proof.
  intros P e c' q Hwf Hok Hl Hh Hq Hcp k f Hk Hfh.
  assert (Hqe : q <> pe_pid e) by (intros E; subst; rewrite Hl in Hq; discriminate Hq).
  set (A := replace_in (pcfg_procs P) (pe_pid e) (pe_absorb e c')).
  set (C := child_entry e (pe_cfg (pcfg_shared P) e) c' q).
  assert (Hrep : forall k', children_keys A k' = children_keys (pcfg_procs P) k')
    by (intros k'; apply children_keys_replace; intros x Hx;
        rewrite (same_key P _ _ _ Hwf Hl Hx); reflexivity).
  assert (Hch : forall k', is_child_of k' (q, C) = bv_eqb (pe_pid e) k') by reflexivity.
  unfold look in Hk. unfold clone_result in Hk |- *. cbn [pcfg_procs] in Hk |- *.
  fold A C in Hk |- *.
  rewrite children_keys_app, Hrep, Hch.
  rewrite look_in_app in Hk.
  destruct (bv_eqb k (pe_pid e)) eqn:Ek.
  - apply bv_eqb_true_eq in Ek. subst k.
    unfold A in Hk. rewrite look_in_replace_same in Hk
      by (unfold look in Hl; rewrite Hl; discriminate).
    injection Hk as <-. rewrite bv_eqb_same.
    change (cp_of (cfg_model c') = children_keys (pcfg_procs P) (pe_pid e) ++ [q]).
    rewrite Hcp. unfold cp_of. rewrite (Hok _ _ Hl Hh). reflexivity.
  - assert (Hne : k <> pe_pid e) by (intros E; subst; rewrite bv_eqb_same in Ek; discriminate Ek).
    rewrite (pid_neq_eqb (pe_pid e) k (fun E => Hne (eq_sym E))), List.app_nil_r.
    unfold A in Hk. rewrite look_in_replace_other in Hk by exact Hne.
    destruct (look_in (pcfg_procs P) k) as [f0|] eqn:Hf0.
    + injection Hk as <-. exact (Hok _ _ Hf0 Hfh).
    + cbn [look_in fst snd] in Hk.
      destruct (bv_eqb q k) eqn:Eq; [|discriminate Hk].
      apply bv_eqb_true_eq in Eq. subst k. injection Hk as <-.
      rewrite (children_keys_absent P q Hwf Hq). reflexivity.
Qed.

(** A reap removes the child from the table and its pid from the list. *)
Lemma child_pids_ok_reap : forall P e q ez eff model'',
  pconfig_wf P -> child_pids_ok P ->
  look P (pe_pid e) = Some e -> m_halted (pe_model e) = None ->
  look P q = Some ez -> q <> pe_pid e -> pe_parent ez = Some (pe_pid e) ->
  materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
    (syscall_effect_accesses eff) = Some model'' ->
  child_pids_ok (wait4_reap_result P e q eff model'').
Proof.
  intros P e q ez eff model'' Hwf Hok Hl Hh Hq Hqe Hpar Hmat k f Hk Hfh.
  destruct (wf_parts P Hwf) as (_ & _ & Hnd).
  set (E' := mkEntry (pe_pid e) (pe_parent e) (advance_past_svc (apply_effect (pe_ms e) eff))
               (clear_shared (reap_model q model'')) (pe_ofd e) (pe_nsctx e)).
  set (L := replace_in (pcfg_procs P) (pe_pid e) E').
  assert (HndL : List.NoDup (List.map fst L))
    by (unfold L; rewrite NoDup_replace_keys; exact Hnd).
  assert (Hrep : forall k', children_keys L k' = children_keys (pcfg_procs P) k')
    by (intros k'; apply children_keys_replace; intros x Hx;
        rewrite (same_key P _ _ _ Hwf Hl Hx); reflexivity).
  unfold look in Hk. unfold wait4_reap_result in Hk |- *. cbn [pcfg_procs] in Hk |- *.
  fold E' L in Hk |- *.
  rewrite children_keys_drop by exact HndL. rewrite Hrep.
  destruct (bv_eqb k q) eqn:Ekq.
  - apply bv_eqb_true_eq in Ekq. subst k.
    rewrite look_in_drop_same in Hk by exact HndL. discriminate Hk.
  - assert (Hkq : k <> q) by (intros E; subst; rewrite bv_eqb_same in Ekq; discriminate Ekq).
    rewrite look_in_drop_other in Hk by (intros E; apply Hkq; symmetry; exact E).
    destruct (bv_eqb k (pe_pid e)) eqn:Ek.
    + apply bv_eqb_true_eq in Ek. subst k.
      unfold L in Hk. rewrite look_in_replace_same in Hk
        by (unfold look in Hl; rewrite Hl; discriminate).
      injection Hk as <-. cbn [pe_model].
      change (List.filter (fun x => negb (bv_eqb x q)) (cp_of model'')
              = List.filter (fun x => negb (bv_eqb x q))
                  (children_keys (pcfg_procs P) (pe_pid e))).
      rewrite (cp_materialize _ _ _ Hmat). unfold cp_of. rewrite <- (Hok _ _ Hl Hh).
      reflexivity.
    + assert (Hne : k <> pe_pid e) by (intros E; subst; rewrite bv_eqb_same in Ek; discriminate Ek).
      unfold L in Hk. rewrite look_in_replace_other in Hk by exact Hne.
      rewrite (Hok _ _ Hk Hfh).
      symmetry. apply List.forallb_filter_id. apply List.forallb_forall. intros y Hy.
      apply negb_true_iff. destruct (bv_eqb y q) eqn:Ey; [|reflexivity].
      apply bv_eqb_true_eq in Ey. subst y. exfalso.
      unfold children_keys in Hy. apply List.in_map_iff in Hy as ([y z] & Hyq & Hy).
      cbn [fst] in Hyq. subst y.
      apply List.filter_In in Hy as [Hin Hc].
      rewrite (same_key P _ _ _ Hwf Hq Hin) in Hc.
      unfold is_child_of in Hc. cbn [snd] in Hc. rewrite Hpar in Hc.
      apply bv_eqb_true_eq in Hc. exact (Hne (eq_sym Hc)).
Qed.

(** THE PRESERVATION. *)
Theorem pstep_at_preserves_child_pids : forall segs cfg p P evs P',
  pconfig_wf P -> child_pids_ok P ->
  pstep_at segs cfg p P evs (PNext P') -> child_pids_ok P'.
Proof.
  intros segs cfg p P evs P' Hwf Hok Hp.
  destruct (pstep_at_not_halted _ _ _ _ _ _ Hp) as (eh & Hlh & Hhh).
  inversion Hp; subst.
  all: match goal with
       | Hl0 : look _ (pe_pid ?e0) = Some ?e0 |- _ =>
           assert (eh = e0) by congruence; subst eh
       end.
  - (* the released step: not a successful clone, and at a [wait4] the
       caller has no child in the table, so (by the invariant) no recorded
       pid for the released [wait4] to reap *)
    apply child_pids_ok_absorb; try assumption.
    match goal with
    | Hss : sstep_cfg _ _ _ _ (SNext ?c1), Hcs : clone_success_b _ ?c1 = false,
      Hwo : wait4_owned_b _ ?e0 = false |- _ =>
        refine (sstep_child_pids_kept _ _ _ _ _ Hss Hcs _);
        intros x8 Hs H260;
        unfold wait4_owned_b in Hwo; cbn [pe_cfg cfg_ms] in Hs;
        rewrite Hs in Hwo; cbv beta iota in Hwo;
        rewrite H260, Z.eqb_refl, andb_true_l in Hwo;
        transitivity (m_child_pids (pe_model e0)); [reflexivity|];
        rewrite (Hok _ _ Hlh Hhh);
        exact (children_keys_nil_of_no_child _ _ Hwo)
    end.
  - (* the clone *)
    match goal with
    | Hss : sstep_cfg _ _ _ _ (SNext ?c1), Hcs : clone_success_b _ ?c1 = true,
      Hcp : child_pid_core ?c1 ?q, Hfr : look _ ?q = None |- _ =>
        apply child_pids_ok_clone; try assumption;
        destruct Hcp as (Ha0 & _);
        rewrite (sstep_child_pids_clone _ _ _ _ _ Hss Hcs), Ha0; reflexivity
    end.
  - (* the blocking reap *)
    eapply child_pids_ok_reap; try eassumption.
  - (* the WNOHANG reap *)
    eapply child_pids_ok_reap; try eassumption.
  - (* the WNOHANG zero *)
    unfold wait4_zero_result. apply child_pids_ok_absorb; try assumption. reflexivity.
  - (* the sync *)
    unfold sync_result.
    match goal with
    | Hl0 : look ?Q (pe_pid ?e0) = Some ?e0 |- _ =>
        apply (child_pids_ok_replace Q (pe_pid e0) e0); try assumption;
        [reflexivity | apply cp_sync_entry | apply sync_entry_halted]
    end.
  - (* the root pin *)
    eapply child_pids_ok_pin_root; eassumption.
Qed.

(** THE LAUNCH: one entry, whose list is its model's. *)
Lemma child_pids_ok_one_proc : forall c,
  m_child_pids (cfg_model c) = [] -> child_pids_ok (one_proc c).
Proof.
  intros c H k f Hk _. unfold look in Hk. cbn [one_proc pcfg_procs look_in fst snd] in Hk.
  destruct (bv_eqb one_pid k) eqn:E; [|discriminate Hk].
  injection Hk as <-. cbn [one_proc pcfg_procs].
  exact H.
Qed.

(** Any run of the core from a launch whose list is empty. *)
Inductive pruns (segs : list Segment) (cfg : SpuriousCfg) : pconfig -> pconfig -> Prop :=
| pruns_refl : forall P, pruns segs cfg P P
| pruns_step : forall P evs P' P'',
    pstep_cfg segs cfg P evs (PNext P') -> pruns segs cfg P' P'' -> pruns segs cfg P P''.

Theorem child_pids_reachable : forall segs cfg c P,
  m_child_pids (cfg_model c) = [] ->
  pruns segs cfg (one_proc c) P -> child_pids_ok P.
Proof.
  intros segs cfg c P H0 Hr.
  pose proof (pconfig_wf_one_proc c) as Hwf.
  pose proof (child_pids_ok_one_proc c H0) as Hok.
  remember (one_proc c) as Q eqn:HQ. clear HQ.
  revert Hwf Hok.
  induction Hr as [Q | Q evs Q' Q'' Hs _ IH]; intros Hwf Hok; [exact Hok|].
  destruct Hs as (p & Hs).
  apply IH; [exact (pstep_at_preserves_wf _ _ _ _ _ _ Hwf Hs)
            | exact (pstep_at_preserves_child_pids _ _ _ _ _ _ Hwf Hok Hs)].
Qed.

(* =========================================================================
   wait4 of a caller with a child in the table
   ========================================================================= *)

(** THE WAIT4 CHECK.  A caller with a child in the table is never answered
    by the released [wait4] ([Checks.ProcsWait4Gate]); the core's arms
    refuse it, answer the WNOHANG zero, or reap a child whose pid is in
    the caller's own list and is what the call returns. *)
Theorem owned_wait4_answers_child : forall segs cfg P e evs r,
  pconfig_wf P -> child_pids_ok P ->
  look P (pe_pid e) = Some e -> m_halted (pe_model e) = None ->
  wait4_owned_b P e = true ->
  pstep_at segs cfg (pe_pid e) P evs r ->
  r = PError
  \/ r = PNext (wait4_zero_result P e)
  \/ exists q ez eff model'',
       List.In q (m_child_pids (pe_model e)) /\ eff_ret eff = q
       /\ look P q = Some ez /\ pe_zombie ez <> None
       /\ r = PNext (wait4_reap_result P e q eff model'').
Proof.
  intros segs cfg P e evs r Hwf Hok Hl Hh Hwo Hp.
  destruct (owned_wait4_never_released segs cfg (pe_pid e) P e evs r Hl Hwo Hp)
    as (_ & [ (q & ez & eff & model'' & Hq & Hne & Hpar & Hz & Hret & ->)
            | [ (_ & ->) | (_ & ->) ] ]).
  - right; right. exists q, ez, eff, model''.
    split; [|split; [exact Hret | split; [exact Hq | split; [exact Hz | reflexivity]]]].
    rewrite (Hok _ _ Hl Hh). unfold children_keys. apply List.in_map_iff.
    exists (q, ez). split; [reflexivity|]. apply List.filter_In. split.
    + exact (look_in_In _ _ _ Hq).
    + unfold is_child_of. cbn [snd]. rewrite Hpar. apply bv_eqb_same.
  - right; left. reflexivity.
  - left. reflexivity.
Qed.
