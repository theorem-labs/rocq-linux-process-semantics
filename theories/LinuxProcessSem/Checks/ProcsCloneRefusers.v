(** * LinuxProcessSem.Checks.ProcsCloneRefusers — every entry of the multi-process core keeps the host's clone refusers

    Not part of the trusted specification: QA on
    [State.procst_clone_refusers] across the multi-process core, in the
    sense of [Checks.Examples]'s header, under its first reason.

    The host's clone refusers are read AT CLONE ([Kernel.Fork.clone_refusable]),
    and in a run of the core every clone is a step of one entry of the
    table, a child's own clone included.  So the fact a statement needs is
    that EVERY entry, the children the core made included, carries the
    launch's value: [refusers_all r P].  It holds at the launch
    ([refusers_all_one_proc]), and every producing arm of [Procs.pstep_at]
    keeps it ([pstep_at_preserves_clone_refusers]): the released step and
    its absorption, the orphaning at exit, the clone and its child entry
    ([Procs.child_proc] copies the field), the three [wait4] arms (the reap
    drops the child), the clock sync and the root pin.  The same holds for
    [Procs.pstep_x_at] under every extension whose own answers keep the
    field ([ext_keeps_clone_refusers]), which [Ns.Ext.no_ext] does
    ([no_ext_keeps_clone_refusers]).  [clone_refusers_reachable] and
    [pinit_clone_refusers_reachable] are the reachability corollaries,
    in the shape of [Checks.ProcsChildPids.child_pids_reachable]. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Ext.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ProcsChildPids CloneRefusersKept.
Import ListNotations.

(** Every slot of a table carries [r]. *)
Definition refusers_in (r : CloneRefusers) (ps : list (Pid * ProcessEntry)) : Prop :=
  Forall (fun kv => m_clone_refusers (pe_model (snd kv)) = r) ps.

(** THE INVARIANT: every entry of the table carries [r]. *)
Definition refusers_all (r : CloneRefusers) (P : pconfig) : Prop :=
  refusers_in r (pcfg_procs P).

(** The form a statement reads: every entry a key finds carries [r]. *)
Lemma entry_r : forall r P k f,
  refusers_all r P -> look P k = Some f -> m_clone_refusers (pe_model f) = r.
Proof.
  intros r P k f. unfold refusers_all, refusers_in, look.
  generalize (pcfg_procs P) as ps.
  induction ps as [|kv ps IH]; intros Hall Hl; [discriminate Hl|].
  apply Forall_cons_iff in Hall as [Hkv Hps].
  cbn [look_in] in Hl. destruct (bv_eqb (fst kv) k).
  - injection Hl as <-. exact Hkv.
  - exact (IH Hps Hl).
Qed.

Lemma refusers_in_replace : forall r ps p e',
  refusers_in r ps -> m_clone_refusers (pe_model e') = r ->
  refusers_in r (replace_in ps p e').
Proof.
  intros r ps p e' Hps He. unfold refusers_in in *.
  revert Hps. induction ps as [|kv ps IH]; intros Hps; [constructor|].
  apply Forall_cons_iff in Hps as [Hkv Hrest].
  cbn [replace_in]. destruct (bv_eqb (fst kv) p).
  - constructor; [exact He | exact Hrest].
  - constructor; [exact Hkv | exact (IH Hrest)].
Qed.

Lemma refusers_in_drop : forall r ps p,
  refusers_in r ps -> refusers_in r (drop_in ps p).
Proof.
  intros r ps p Hps. unfold refusers_in in *.
  revert Hps. induction ps as [|kv ps IH]; intros Hps; [constructor|].
  apply Forall_cons_iff in Hps as [Hkv Hrest].
  cbn [drop_in]. destruct (bv_eqb (fst kv) p).
  - exact Hrest.
  - constructor; [exact Hkv | exact (IH Hrest)].
Qed.

(** The orphaning changes a slot's parent and nothing else. *)
Lemma refusers_in_orphan : forall r m p ps,
  refusers_in r ps -> refusers_in r (orphan_at_exit m p ps).
Proof.
  intros r m p ps Hps. unfold orphan_at_exit.
  destruct (m_halted m); [|exact Hps].
  unfold orphan_children, refusers_in in *.
  revert Hps. induction ps as [|kv ps IH]; intros Hps; [constructor|].
  apply Forall_cons_iff in Hps as [Hkv Hrest].
  cbn [List.map]. constructor; [|exact (IH Hrest)].
  unfold orphan_one. cbv beta.
  destruct (negb (bv_eqb (fst kv) p)
            && match pe_parent (snd kv) with Some q => bv_eqb q p | None => false end);
    exact Hkv.
Qed.

(** A first root-tid pin resolves the root's children's parent pid
    ([Procs.root_children_ppid], [State.with_ppid]) and nothing else. *)
Lemma refusers_in_root_children : forall r root t ps,
  refusers_in r ps -> refusers_in r (root_children_ppid root t ps).
Proof.
  intros r root t ps Hps. unfold root_children_ppid, refusers_in in *.
  revert Hps. induction ps as [|kv ps IH]; intros Hps; [constructor|].
  apply Forall_cons_iff in Hps as [Hkv Hrest].
  cbn [List.map]. constructor; [|exact (IH Hrest)].
  unfold root_child_ppid_one.
  match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [snd pe_model];
    first [exact Hkv | etransitivity; [|exact Hkv]; reflexivity].
Qed.

Lemma refusers_in_first_root_pin : forall r P e m' ps,
  refusers_in r ps -> refusers_in r (first_root_pin_children P e m' ps).
Proof.
  intros r P e m' ps Hps. unfold first_root_pin_children.
  destruct (bv_eqb (pe_pid e) (pcfg_root P)); [|exact Hps].
  destruct (m_tid (pe_model e)), (m_tid m');
    first [exact Hps | apply refusers_in_root_children; exact Hps].
Qed.

(** The table an arm replaces into: the one it started from, or that table
    after a first root-tid pin resolved the root's children. *)
Ltac rr_tab Hall :=
  first
  [ exact Hall
  | apply refusers_in_first_root_pin; exact Hall
  | match goal with
    | |- refusers_in _ (match ?x with _ => _ end) =>
        destruct x; first [exact Hall | apply refusers_in_root_children; exact Hall]
    end ].

(** The clock sync raises the clock and fills the UTS name and a stat pin,
    and keeps the field. *)
Lemma sync_entry_clone_refusers : forall P e,
  m_clone_refusers (pe_model (sync_entry P e)) = m_clone_refusers (pe_model e).
Proof.
  intros P e. unfold sync_entry, uts_fill, pin_fill. cbn [pe_model].
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x
         end;
    reflexivity.
Qed.

Lemma cfg_model_with_ret : forall c ret, cfg_model (with_ret c ret) = cfg_model c.
Proof. intros c [v|]; reflexivity. Qed.

(** The equation a new slot owes, from what the arm knows of its model:
    an entry of the table it is built from (conversion through the setters
    and [Procs.child_proc]), a released step's successor, or a
    materialised model. *)
Ltac rr_eq Hall :=
  first
  [ match goal with
    | Hs : sstep_cfg _ _ _ _ (SNext ?c'), Hl : look _ (pe_pid ?e) = Some ?e |- _ =>
        transitivity (m_clone_refusers (cfg_model c')); [reflexivity|];
        rewrite (sstep_cfg_clone_refusers_kept _ _ _ _ _ Hs);
        exact (entry_r _ _ _ _ Hall Hl)
    end
  | match goal with
    | Hm : materialize_model_accesses _ _ = Some ?m2, Hl : look _ (pe_pid ?e) = Some ?e |- _ =>
        transitivity (m_clone_refusers m2); [reflexivity|];
        rewrite (clone_refusers_materialize _ _ _ Hm);
        exact (entry_r _ _ _ _ Hall Hl)
    end
  | match goal with
    | Hl : look _ _ = Some ?f |- _ =>
        transitivity (m_clone_refusers (pe_model f));
        [reflexivity | exact (entry_r _ _ _ _ Hall Hl)]
    end ].

(** THE PRESERVATION, for every producing arm of the core. *)
Theorem pstep_at_preserves_clone_refusers : forall r segs cfg p P evs P',
  refusers_all r P -> pstep_at segs cfg p P evs (PNext P') -> refusers_all r P'.
Proof.
  intros r segs cfg p P evs P' Hall H.
  inversion H; subst.
  - (* pstep_other: the released step, absorbed, with the orphaning *)
    unfold refusers_all, absorb; cbn [pcfg_procs].
    apply refusers_in_orphan. apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
  - (* pstep_clone: the parent absorbed, and the child entry *)
    unfold refusers_all, clone_result; cbn [pcfg_procs].
    apply Forall_app. split.
    + apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
    + constructor; [cbn [snd]; rr_eq Hall | constructor].
  - (* pstep_wait_reap: the parent reaps, the child is dropped *)
    unfold refusers_all; cbn [pcfg_procs].
    apply refusers_in_drop. apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
  - (* pstep_wait_nohang_reap *)
    unfold refusers_all, wait4_reap_result; cbn [pcfg_procs].
    apply refusers_in_drop. apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
  - (* pstep_wait_nohang_zero *)
    unfold refusers_all, wait4_zero_result, absorb; cbn [pcfg_procs].
    apply refusers_in_orphan. apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
  - (* pstep_sync *)
    unfold refusers_all, sync_result; cbn [pcfg_procs].
    apply refusers_in_replace; [rr_tab Hall|].
    rewrite sync_entry_clone_refusers. rr_eq Hall.
  - (* pstep_pin_root *)
    unfold refusers_all, pin_root; cbn [pcfg_procs].
    apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
Qed.

Corollary pstep_cfg_preserves_clone_refusers : forall r segs cfg P evs P',
  refusers_all r P -> pstep_cfg segs cfg P evs (PNext P') -> refusers_all r P'.
Proof.
  intros r segs cfg P evs P' Hall (p & H).
  exact (pstep_at_preserves_clone_refusers r segs cfg p P evs P' Hall H).
Qed.

(** THE LAUNCH: one entry, whose model is the launch's. *)
Lemma refusers_all_one_proc : forall c,
  refusers_all (m_clone_refusers (cfg_model c)) (one_proc c).
Proof.
  intros c. unfold refusers_all, one_proc; cbn [pcfg_procs].
  constructor; [reflexivity | constructor].
Qed.

(** Every state of every run of the core from a launch carries the
    launch's value, in every entry. *)
Theorem clone_refusers_reachable : forall segs cfg c P,
  pruns segs cfg (one_proc c) P -> refusers_all (m_clone_refusers (cfg_model c)) P.
Proof.
  intros segs cfg c P Hr.
  pose proof (refusers_all_one_proc c) as Hok.
  remember (one_proc c) as Q eqn:HQ. clear HQ.
  revert Hok.
  induction Hr as [Q | Q evs Q' Q'' Hs _ IH]; intros Hok; [exact Hok|].
  apply IH. exact (pstep_cfg_preserves_clone_refusers _ _ _ _ _ _ Hok Hs).
Qed.

(** From a launch that declares [r]: every entry of every reachable state
    carries [r], so every clone of the run, a child's included, meets
    exactly the refusers the launch declared. *)
Corollary pinit_clone_refusers_reachable :
  forall segs cfg pc ph sp brk0 mbase rnd lim inp P,
  pruns segs cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P ->
  refusers_all (in_clone_refusers inp) P.
Proof.
  intros segs cfg pc ph sp brk0 mbase rnd lim inp P Hr.
  rewrite <- (init_config_clone_refusers segs pc ph sp brk0 mbase rnd lim inp).
  exact (clone_refusers_reachable _ _ _ _ Hr).
Qed.

(* =========================================================================
   Under an extension
   ========================================================================= *)

(** An extension whose own answers keep the field.  The core's arms keep
    it by the lemmas above; what an extension answers for a call it
    claims is the extension's, so this is its obligation. *)
Definition ext_keeps_clone_refusers (ext : ExtSpec) : Prop :=
  forall i m ctx st eff m' ctx' st' evs,
    ext_spec ext i m ctx st (EOk eff m' ctx' st' evs) ->
    m_clone_refusers m' = m_clone_refusers m.

Lemma no_ext_keeps_clone_refusers : ext_keeps_clone_refusers no_ext.
Proof. intros i m ctx st eff m' ctx' st' evs H. hnf in H. destruct H. Qed.

Lemma xsstep_clone_refusers_kept : forall ext segs cfg ctx st c evs c' ctx' st',
  ext_keeps_clone_refusers ext ->
  xsstep ext segs cfg ctx st c evs (SNext c') ctx' st' ->
  m_clone_refusers (cfg_model c') = m_clone_refusers (cfg_model c).
Proof.
  intros ext segs cfg ctx st c evs c' ctx' st' Hext H.
  inversion H; subst; cbn [cfg_model].
  - match goal with Hs : sstep_cfg _ _ _ _ _ |- _ =>
      exact (sstep_cfg_clone_refusers_kept _ _ _ _ _ Hs) end.
  - match goal with
    | He : ext_spec _ _ _ _ _ (EOk _ ?m1 _ _ _),
      Hm : materialize_model_accesses ?m1 _ = Some _ |- _ =>
        rewrite (clone_refusers_materialize _ _ _ Hm); exact (Hext _ _ _ _ _ _ _ _ _ He)
    end.
  - match goal with He : ext_spec _ _ _ _ _ (EOk _ _ _ _ _) |- _ =>
      exact (Hext _ _ _ _ _ _ _ _ _ He) end.
  - match goal with He : ext_spec _ _ _ _ _ (EOk _ _ _ _ _) |- _ =>
      exact (Hext _ _ _ _ _ _ _ _ _ He) end.
Qed.

(** The equation a new slot owes under an extension: the extension step's
    successor, or one of [rr_eq]'s. *)
Ltac rr_eq_x Hall Hext :=
  first
  [ match goal with
    | Hx : xsstep _ _ _ _ _ _ _ (SNext ?c') _ _, Hl : look _ (pe_pid ?e) = Some ?e |- _ =>
        transitivity (m_clone_refusers (cfg_model c')); [reflexivity|];
        rewrite (xsstep_clone_refusers_kept _ _ _ _ _ _ _ _ _ _ Hext Hx);
        exact (entry_r _ _ _ _ Hall Hl)
    end
  | rr_eq Hall ].

Theorem pstep_x_at_preserves_clone_refusers : forall r ext cenv segs cfg p P evs P',
  ext_keeps_clone_refusers ext ->
  refusers_all r P -> pstep_x_at ext cenv segs cfg p P evs (PNext P') -> refusers_all r P'.
Proof.
  intros r ext cenv segs cfg p P evs P' Hext Hall H.
  inversion H; subst.
  - (* px_other *)
    unfold refusers_all, absorb_x; cbn [pcfg_procs].
    apply refusers_in_orphan. apply refusers_in_replace; [rr_tab Hall | rr_eq_x Hall Hext].
  - (* px_clone *)
    unfold refusers_all, clone_result_x; cbn [pcfg_procs].
    apply Forall_app. split.
    + apply refusers_in_replace; [rr_tab Hall|].
      match goal with
      | Hs : sstep_cfg _ _ _ _ (SNext ?c'), Hl : look _ (pe_pid ?e) = Some ?e
        |- m_clone_refusers (pe_model (pe_absorb _ (with_ret ?c' ?ret))) = _ =>
          transitivity (m_clone_refusers (cfg_model (with_ret c' ret))); [reflexivity|];
          rewrite cfg_model_with_ret, (sstep_cfg_clone_refusers_kept _ _ _ _ _ Hs);
          exact (entry_r _ _ _ _ Hall Hl)
      end.
    + constructor; [cbn [snd]; rr_eq Hall | constructor].
  - (* px_clone_fail: the released step under the filter *)
    unfold refusers_all, absorb_x; cbn [pcfg_procs].
    apply refusers_in_orphan. apply refusers_in_replace; [rr_tab Hall|].
    match goal with
    | Hf : clone_fail_step _ _ _ _ _ _ _ _ _ ?c', Hl : look _ (pe_pid ?e) = Some ?e |- _ =>
        unfold clone_fail_step in Hf;
        transitivity (m_clone_refusers (cfg_model c')); [reflexivity|];
        destruct Hf as [Hs | (Hs & _)];
        rewrite (sstep_cfg_clone_refusers_kept _ _ _ _ _ Hs);
        exact (entry_r _ _ _ _ Hall Hl)
    end.
  - (* px_wait_reap *)
    unfold refusers_all; cbn [pcfg_procs].
    apply refusers_in_drop. apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
  - (* px_wait_nohang_reap *)
    unfold refusers_all, wait4_reap_result; cbn [pcfg_procs].
    apply refusers_in_drop. apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
  - (* px_wait_nohang_zero *)
    unfold refusers_all, wait4_zero_result, absorb; cbn [pcfg_procs].
    apply refusers_in_orphan. apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
  - (* px_sync *)
    unfold refusers_all, sync_result; cbn [pcfg_procs].
    apply refusers_in_replace; [rr_tab Hall|].
    rewrite sync_entry_clone_refusers. rr_eq Hall.
  - (* px_pin_root *)
    unfold refusers_all, pin_root; cbn [pcfg_procs].
    apply refusers_in_replace; [rr_tab Hall | rr_eq Hall].
Qed.

Corollary pstep_x_cfg_preserves_clone_refusers : forall r ext cenv segs cfg P evs P',
  ext_keeps_clone_refusers ext ->
  refusers_all r P -> pstep_x_cfg ext cenv segs cfg P evs (PNext P') -> refusers_all r P'.
Proof.
  intros r ext cenv segs cfg P evs P' Hext Hall (p & H).
  exact (pstep_x_at_preserves_clone_refusers r ext cenv segs cfg p P evs P' Hext Hall H).
Qed.

Print Assumptions clone_refusers_reachable.
Print Assumptions pinit_clone_refusers_reachable.
Print Assumptions pstep_x_at_preserves_clone_refusers.
