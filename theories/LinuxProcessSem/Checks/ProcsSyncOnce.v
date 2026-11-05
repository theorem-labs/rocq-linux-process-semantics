(** * LinuxProcessSem.Checks.ProcsSyncOnce — how often the silent sync can fire

    Not part of the trusted specification: QA on [Procs.pstep_sync], in
    the sense of [Checks.Examples]'s header, under its first reason.

    [Procs.pstep_sync] is SILENT: it does not move the program counter, so
    a halting proof must know it cannot repeat without bound.  Three facts
    give the bound a measure needs.

    - (1) [sync_clears]: right after [pstep_sync] on an entry, its sync gate
      is closed, for every synced number (80, 101, 113, 160).
    - (2) [other_step_keeps_entry], with [uts_lag_pinned] and
      [pin_lag_pinned]: a step of ANOTHER entry leaves a running entry's
      machine state unchanged; the model may only acquire a root tid or
      a resolved parent pid. The uname and fstat gates
      read only the entry's own pin once it has one.  So for 160 and 80 the
      gate, once closed by a pin, stays closed until the entry itself
      steps: at most one sync per call.
    - (3) [sync_keeps_max]: a sync never raises the table's largest clock
      copy.  The clock gate of an entry that has synced reopens only when
      another step raises that maximum above its copy, and that step is
      not a sync, so it is a counted step: at most one re-sync per such
      step, which is finite in any measure that counts steps. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ProcsWellFormed ProcsPrivateFrame ProcsClockSync.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   What the sync writes
   ========================================================================= *)

Lemma m_utsname_pin_fill : forall ps e m,
  m_utsname (pin_fill ps e m) = m_utsname m.
Proof.
  intros ps e m. unfold pin_fill.
  destruct (fstat_path e) as [p|]; [|reflexivity].
  destruct (statpin_lookup _ p); [reflexivity|].
  destruct (pin_any ps p); reflexivity.
Qed.

Lemma m_statpins_uts_fill : forall ps m,
  m_statpins (uts_fill ps m) = m_statpins m.
Proof.
  intros ps m. unfold uts_fill.
  destruct (m_utsname m); [reflexivity|]. destruct (uts_any ps); reflexivity.
Qed.

Lemma m_fds_uts_fill : forall ps m, m_fds (uts_fill ps m) = m_fds m.
Proof.
  intros ps m. unfold uts_fill.
  destruct (m_utsname m); [reflexivity|]. destruct (uts_any ps); reflexivity.
Qed.

Lemma m_fds_pin_fill : forall ps e m, m_fds (pin_fill ps e m) = m_fds m.
Proof.
  intros ps e m. unfold pin_fill.
  destruct (fstat_path e) as [p|]; [|reflexivity].
  destruct (statpin_lookup _ p); [reflexivity|].
  destruct (pin_any ps p); reflexivity.
Qed.

Lemma uts_of_sync : forall P e,
  m_utsname (pe_model (sync_entry P e))
  = match m_utsname (pe_model e) with
    | Some u => Some u
    | None => uts_any (pcfg_procs P)
    end.
Proof.
  intros P e. unfold sync_entry. cbn [pe_model].
  change (m_utsname (with_clock ?t ?X)) with (m_utsname X).
  unfold uts_fill. rewrite m_utsname_pin_fill.
  destruct (m_utsname (pe_model e)) eqn:Hu.
  - rewrite m_utsname_pin_fill. exact Hu.
  - destruct (uts_any (pcfg_procs P)); [reflexivity|].
    rewrite m_utsname_pin_fill. exact Hu.
Qed.

Lemma fstat_path_sync : forall P e, fstat_path (sync_entry P e) = fstat_path e.
Proof.
  intros P e. unfold fstat_path. cbn [pe_ms].
  change (m_fds (pe_model (sync_entry P e)))
    with (m_fds (uts_fill (pcfg_procs P) (pin_fill (pcfg_procs P) e (pe_model e)))).
  rewrite m_fds_uts_fill, m_fds_pin_fill. reflexivity.
Qed.

Lemma pin_of_sync : forall P e p,
  fstat_path e = Some p ->
  statpin_lookup (m_statpins (pe_model (sync_entry P e))) p
  = match statpin_lookup (m_statpins (pe_model e)) p with
    | Some b => Some b
    | None => pin_any (pcfg_procs P) p
    end.
Proof.
  intros P e p Hf. unfold sync_entry. cbn [pe_model].
  change (m_statpins (with_clock ?t ?X)) with (m_statpins X).
  rewrite m_statpins_uts_fill. unfold pin_fill. rewrite Hf.
  destruct (statpin_lookup (m_statpins (pe_model e)) p) eqn:Hp; [exact Hp|].
  destruct (pin_any (pcfg_procs P) p) eqn:Ha; [|exact Hp].
  change (m_statpins (with_statpin p l (pe_model e)))
    with ((p, l) :: m_statpins (pe_model e)).
  cbn [statpin_lookup]. rewrite Fs.path_eqb_refl. reflexivity.
Qed.

(* =========================================================================
   (1) The sync closes its own gate
   ========================================================================= *)

Lemma clock_max_replace_le : forall ps p e',
  (clock_max (replace_in ps p e')
   <= Z.max (clock_max ps) (bv_unsigned (m_clock (pe_model e'))))%Z.
Proof.
  induction ps as [|[k x] r IH]; intros p e'; cbn [replace_in]; [cbn; lia|].
  pose proof (bv_unsigned_in_range _ (m_clock (pe_model e'))).
  destruct (bv_eqb (fst (k, x)) p).
  - unfold clock_max. cbn [List.fold_right snd]. fold (clock_max r). lia.
  - unfold clock_max. cbn [List.fold_right snd]. fold (clock_max r).
    fold (clock_max (replace_in r p e')). specialize (IH p e'). lia.
Qed.

Lemma uts_any_replace_none : forall ps p e',
  uts_any ps = None -> m_utsname (pe_model e') = None ->
  uts_any (replace_in ps p e') = None.
Proof.
  induction ps as [|[k x] r IH]; intros p e' H He; [reflexivity|].
  cbn [uts_any snd] in H. destruct (m_utsname (pe_model x)) eqn:Hx; [discriminate H|].
  cbn [replace_in fst]. destruct (bv_eqb k p).
  - cbn [uts_any snd]. rewrite He. exact H.
  - cbn [uts_any snd]. rewrite Hx. exact (IH p e' H He).
Qed.

Lemma pin_any_replace_none : forall ps p e' q,
  pin_any ps q = None -> statpin_lookup (m_statpins (pe_model e')) q = None ->
  pin_any (replace_in ps p e') q = None.
Proof.
  induction ps as [|[k x] r IH]; intros p e' q H He; [reflexivity|].
  cbn [pin_any snd] in H.
  destruct (statpin_lookup (m_statpins (pe_model x)) q) eqn:Hx; [discriminate H|].
  cbn [replace_in fst]. destruct (bv_eqb k p).
  - cbn [pin_any snd]. rewrite He. exact H.
  - cbn [pin_any snd]. rewrite Hx. exact (IH p e' q H He).
Qed.

(** (1) Right after the sync, the entry's gate is closed. *)
Theorem sync_clears : forall P e,
  sync_pending_b (sync_result P e) (sync_entry P e) = false.
Proof.
  intros P e. unfold sync_pending_b. cbn [sync_entry pe_ms].
  destruct (ms_svc_pending (pe_ms e)) as [x8|]; [|reflexivity].
  (* the clock: the copy is the old maximum, and the new maximum is no more *)
  assert (Hclk : (bv_unsigned (m_clock (pe_model (sync_entry P e)))
                  <? clock_max (pcfg_procs (sync_result P e)))%Z = false).
  { apply Z.ltb_ge.
    change (m_clock (pe_model (sync_entry P e)))
      with (Z_to_bv 64 (clock_max (pcfg_procs P))).
    rewrite word_small by exact (clock_max_range _).
    unfold sync_result. cbn [pcfg_procs].
    pose proof (clock_max_replace_le (pcfg_procs P) (pe_pid e) (sync_entry P e)) as H.
    change (m_clock (pe_model (sync_entry P e)))
      with (Z_to_bv 64 (clock_max (pcfg_procs P))) in H.
    rewrite word_small in H by exact (clock_max_range _). lia. }
  assert (Huts : uts_lag_b (sync_result P e) (sync_entry P e) = false).
  { unfold uts_lag_b. rewrite uts_of_sync.
    destruct (m_utsname (pe_model e)) eqn:Hu0; [reflexivity|].
    destruct (uts_any (pcfg_procs P)) eqn:Ha; [reflexivity|].
    unfold sync_result. cbn [pcfg_procs].
    rewrite (uts_any_replace_none _ _ _ Ha); [reflexivity|].
    rewrite uts_of_sync, Hu0. exact Ha. }
  assert (Hpin : pin_lag_b (sync_result P e) (sync_entry P e) = false).
  { unfold pin_lag_b. rewrite fstat_path_sync.
    destruct (fstat_path e) as [p|] eqn:Hf; [|reflexivity].
    rewrite (pin_of_sync P e p Hf).
    destruct (statpin_lookup (m_statpins (pe_model e)) p) eqn:Hp; [reflexivity|].
    destruct (pin_any (pcfg_procs P) p) eqn:Ha; [reflexivity|].
    unfold sync_result. cbn [pcfg_procs].
    rewrite (pin_any_replace_none _ _ _ _ Ha); [reflexivity|].
    rewrite (pin_of_sync P e p Hf), Hp. exact Ha. }
  rewrite Hclk, Huts, Hpin, !andb_false_r. reflexivity.
Qed.

(* =========================================================================
   (2) Another entry's step leaves a running entry alone
   ========================================================================= *)

Lemma look_in_app : forall (l1 l2 : list (Pid * ProcessEntry)) p,
  look_in (l1 ++ l2) p = match look_in l1 p with Some f => Some f | None => look_in l2 p end.
Proof.
  induction l1 as [|[k x] r IH]; intros l2 p; [reflexivity|].
  cbn [app look_in fst snd]. destruct (bv_eqb k p); [reflexivity|]. apply IH.
Qed.

Lemma look_in_drop_other : forall ps q p,
  q <> p -> look_in (drop_in ps q) p = look_in ps p.
Proof.
  induction ps as [|[k x] r IH]; intros q p Hne; [reflexivity|].
  cbn [drop_in fst]. destruct (bv_eqb k q) eqn:Ekq.
  - apply bv_eqb_true_eq in Ekq. subst k. cbn [look_in fst snd].
    rewrite (pid_neq_eqb q p Hne). reflexivity.
  - cbn [look_in fst snd]. destruct (bv_eqb k p); [reflexivity|]. apply IH. exact Hne.
Qed.

Lemma absorb_keeps_other_tid_stable : forall P e c' p f,
  pe_pid e <> p -> look P p = Some f ->
  m_tid (cfg_model c') = m_tid (pe_model e) ->
  exists f', look (absorb P e c') p = Some f' /\ pe_model f' = pe_model f
             /\ pe_ms f' = pe_ms f.
Proof.
  intros P e c' p f Hne Hf Htid. unfold look, absorb. cbn [pcfg_procs].
  rewrite first_root_pin_children_same_tid by exact Htid.
  rewrite orphan_at_exit_map, look_in_orphan, look_in_replace_other
    by (intros E; apply Hne; symmetry; exact E).
  unfold look in Hf. rewrite Hf. cbn [option_map].
  eexists. split; [reflexivity|].
  destruct (orphan_slot_orphaned (cfg_model c') (pe_pid e) p f) as [-> | (_ & ->)];
    split; reflexivity.
Qed.

Lemma absorb_keeps_other_state : forall P e c' p f,
  pe_pid e <> p -> look P p = Some f ->
  exists f', look (absorb P e c') p = Some f' /\ pe_ms f' = pe_ms f
    /\ (pe_model f' = pe_model f \/ exists t, pe_model f' = with_ppid t (pe_model f)).
Proof.
  intros P e c' p f Hne Hf. unfold look in Hf.
  assert (Hfirst : exists g,
    look_in (first_root_pin_children P e (cfg_model c') (pcfg_procs P)) p = Some g
    /\ pe_ms g = pe_ms f
    /\ (pe_model g = pe_model f \/ exists t, pe_model g = with_ppid t (pe_model f))).
  { unfold first_root_pin_children.
    destruct (bv_eqb (pe_pid e) (pcfg_root P));
      destruct (m_tid (pe_model e)) as [old|];
      destruct (m_tid (cfg_model c')) as [t|];
      try (exists f; split; [exact Hf|split; [reflexivity|left; reflexivity]]).
    exists (snd (root_child_ppid_one (pcfg_root P) t (p, f))). split.
    - rewrite look_in_root_children_ppid, Hf. reflexivity.
    - pose proof (root_child_ppid_one_fields (pcfg_root P) t p f) as (_ & _ & Hms & _).
      split; [exact Hms|].
      destruct (root_child_ppid_one_model (pcfg_root P) t p f) as [Hm|Hm];
        [left; exact Hm|right; exists t; exact Hm]. }
  destruct Hfirst as (g & Hg & Hms & Hmodel).
  unfold look, absorb. cbn [pcfg_procs].
  rewrite orphan_at_exit_map, look_in_orphan, look_in_replace_other
    by (intros E; apply Hne; symmetry; exact E).
  rewrite Hg. cbn [option_map]. eexists. split; [reflexivity|].
  destruct (orphan_slot_orphaned (cfg_model c') (pe_pid e) p g) as [-> | (_ & ->)];
    split; assumption.
Qed.

(** Another entry's step preserves a running entry's machine state. It
    may pin the root's tid or resolve a child's parent pid; an exit may
    clear the parent link. Neither pid bookkeeping consumes a reparent move. *)
Theorem other_step_keeps_entry : forall segs cfg q P evs P' p f,
  pstep_at segs cfg q P evs (PNext P') ->
  q <> p -> look P p = Some f -> m_halted (pe_model f) = None ->
  exists f', look P' p = Some f' /\ pe_ms f' = pe_ms f
    /\ (pe_model f' = pe_model f
        \/ (exists t, pe_model f' = with_tid t (pe_model f))
        \/ exists t, pe_model f' = with_ppid t (pe_model f)).
Proof.
  intros segs cfg q P evs P' p f H Hne Hf Hh.
  assert (Hab : forall e c', pe_pid e <> p ->
            exists f', look (absorb P e c') p = Some f' /\ pe_ms f' = pe_ms f
              /\ (pe_model f' = pe_model f
                  \/ (exists t, pe_model f' = with_tid t (pe_model f))
                  \/ exists t, pe_model f' = with_ppid t (pe_model f))).
  { intros e c' Hep.
    destruct (absorb_keeps_other_state P e c' p f Hep Hf) as (f' & H1 & Hms & Hmodel).
    exists f'. split; [exact H1|]. split; [exact Hms|].
    destruct Hmodel as [Hm|[t Hm]];
      [left; exact Hm|right; right; exists t; exact Hm]. }
  inversion H; subst.
  - (* pstep_other *) apply Hab; assumption.
  - (* pstep_clone *)
    exists f. split; [|split; [reflexivity | left; reflexivity]].
    unfold look, clone_result. cbn [pcfg_procs].
    rewrite look_in_app, look_in_replace_other
      by (intros E; apply Hne; symmetry; exact E).
    unfold look in Hf. rewrite Hf. reflexivity.
  - (* pstep_wait_reap: the reaped child is halted, so it is not [p] *)
    exists f. split; [|split; [reflexivity | left; reflexivity]].
    unfold look. cbn [pcfg_procs].
    match goal with
    | Hq : look P ?q0 = Some ?ez, Hst : pe_status _ ?ez = Some _ |- _ =>
        assert (Hq0 : q0 <> p)
          by (intros E; subst q0; rewrite Hf in Hq; injection Hq as <-;
              exact (pe_status_halted _ _ _ Hst Hh));
        rewrite (look_in_drop_other _ q0 p Hq0)
    end.
    rewrite look_in_replace_other by (intros E; apply Hne; symmetry; exact E).
    unfold look in Hf. exact Hf.
  - (* pstep_wait_nohang_reap *)
    exists f. split; [|split; [reflexivity | left; reflexivity]].
    unfold look, wait4_reap_result. cbn [pcfg_procs].
    match goal with
    | Hq : look P ?q0 = Some ?ez, Hst : pe_status _ ?ez = Some _ |- _ =>
        assert (Hq0 : q0 <> p)
          by (intros E; subst q0; rewrite Hf in Hq; injection Hq as <-;
              exact (pe_status_halted _ _ _ Hst Hh));
        rewrite (look_in_drop_other _ q0 p Hq0)
    end.
    rewrite look_in_replace_other by (intros E; apply Hne; symmetry; exact E).
    unfold look in Hf. exact Hf.
  - (* pstep_wait_nohang_zero: an absorb *)
    unfold wait4_zero_result. apply Hab; assumption.
  - (* pstep_sync *)
    exists f. split; [|split; [reflexivity | left; reflexivity]].
    unfold look, sync_result. cbn [pcfg_procs].
    rewrite look_in_replace_other by (intros E; apply Hne; symmetry; exact E).
    unfold look in Hf. exact Hf.
  - (* pstep_pin_root: pin the root and resolve its running children's parent pid *)
    match goal with
    | Hlr : look P (pcfg_root P) = Some ?r |- context [pin_root P r ?t] =>
      destruct (bv_eqb (pcfg_root P) p) eqn:Erp
    end.
    + apply bv_eqb_true_eq in Erp.
      match goal with Hlr : look P (pcfg_root P) = Some ?r |- _ =>
        rewrite Erp in Hlr; rewrite Hf in Hlr; injection Hlr as <-
      end.
      eexists. split.
      * unfold look, pin_root. cbn [pcfg_procs]. rewrite <- Erp.
        apply look_in_replace_same.
        destruct (m_tid (pe_model f)); [|rewrite look_in_root_children_ppid_root];
          unfold look in Hf; rewrite <- Erp in Hf; rewrite Hf; discriminate.
      * split; [reflexivity|right; left; eexists; reflexivity].
    + lazymatch goal with
      | Hlr : look P (pcfg_root P) = Some ?r |- context [pin_root P r ?t] =>
        destruct (m_tid (pe_model r)) eqn:Et;
        [ exists f; split; [|split; [reflexivity|left; reflexivity]];
          unfold look, pin_root; cbn [pcfg_procs]; rewrite Et;
          rewrite look_in_replace_other
            by (intros E; rewrite E, bv_eqb_same in Erp; discriminate Erp);
          exact Hf
        | exists (snd (root_child_ppid_one (pcfg_root P) t (p, f))); split;
          [ unfold look, pin_root; cbn [pcfg_procs]; rewrite Et;
            rewrite look_in_replace_other
              by (intros E; rewrite E, bv_eqb_same in Erp; discriminate Erp);
            rewrite look_in_root_children_ppid;
            unfold look in Hf; rewrite Hf; reflexivity
          | pose proof (root_child_ppid_one_fields (pcfg_root P) t p f)
              as (_ & _ & Hms & _);
            split; [exact Hms|];
            destruct (root_child_ppid_one_model (pcfg_root P) t p f) as [Hm|Hm];
              [left; exact Hm|right; right; exists t; exact Hm] ] ]
      end.
Qed.

(** And once pinned, the uname and fstat gates read only the entry's own
    pin, which another entry's step leaves alone. *)
Lemma uts_lag_pinned : forall P e,
  m_utsname (pe_model e) <> None -> uts_lag_b P e = false.
Proof.
  intros P e H. unfold uts_lag_b. destruct (m_utsname (pe_model e)); [reflexivity|].
  contradiction.
Qed.

Lemma pin_lag_pinned : forall P e p,
  fstat_path e = Some p -> statpin_lookup (m_statpins (pe_model e)) p <> None ->
  pin_lag_b P e = false.
Proof.
  intros P e p Hf H. unfold pin_lag_b. rewrite Hf.
  destruct (statpin_lookup (m_statpins (pe_model e)) p); [reflexivity|]. contradiction.
Qed.

(* =========================================================================
   (3) A sync never raises the largest clock copy
   ========================================================================= *)

(** (3) The table's largest clock copy is the same after a sync.  So a
    synced entry's clock gate reopens only after a step that is not a sync
    raises it: a counted step, one re-sync per such step. *)
Theorem sync_keeps_max : forall P e,
  look P (pe_pid e) = Some e ->
  clock_max (pcfg_procs (sync_result P e)) = clock_max (pcfg_procs P).
Proof.
  intros P e Hl. unfold sync_result. cbn [pcfg_procs].
  pose proof (clock_max_replace_le (pcfg_procs P) (pe_pid e) (sync_entry P e)) as Hle.
  assert (Hin : look_in (replace_in (pcfg_procs P) (pe_pid e) (sync_entry P e)) (pe_pid e)
                = Some (sync_entry P e))
    by (apply look_in_replace_same; unfold look in Hl; rewrite Hl; discriminate).
  pose proof (clock_max_ge _ _ _ Hin) as Hge.
  unfold clk in Hge.
  change (m_clock (pe_model (sync_entry P e)))
    with (Z_to_bv 64 (clock_max (pcfg_procs P))) in Hle, Hge.
  rewrite word_small in Hle, Hge by exact (clock_max_range _).
  lia.
Qed.
