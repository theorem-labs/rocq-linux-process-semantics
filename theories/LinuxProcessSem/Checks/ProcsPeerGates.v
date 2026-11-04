(** * LinuxProcessSem.Checks.ProcsPeerGates — flock, unlinkat and the parent-death signal while a peer lives

    Not part of the trusted specification: QA on [Procs.peer_refused_b]'s
    flock part and on [Procs.step_refused_b], in the sense of
    [Checks.Examples]'s header, under its first reason: the statements are
    universally quantified over configurations and steps.

    ** What this pins

    - [flock_conflict_refused]: flock (32) of an entry whose descriptor
      names a file another entry has open takes [pstep_peer_refuse] (an
      error) and has no successor.  The released flock checks only the
      caller's own table, and no lock state exists, so it would grant a
      lock the peer may hold.
    - [unlink_keeps_peer_names]: after a step at unlinkat (35), every
      other entry still has every path its file descriptors and stat pins
      named: the released unlinkat checks only the caller's own table, and
      the step gate refuses a removal a peer names.
    - [pdeath_never_lost]: a step that halts an entry while a peer lives,
      other than a clone or a [wait4] the core answers, leaves no running
      child of it holding a nonzero parent-death signal: the step gate
      refuses that halt, since Linux would signal the child and the exit
      arm does not. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ProcsWellFormed ProcsPrivateFrame ProcsSharedFrame ProcsClockSync ProcsSyncOnce.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(** The producing arms, with what this file needs of each. *)
Lemma pstep_next_gate_cases : forall segs cfg p P evs P',
  pstep_at segs cfg p P evs (PNext P') ->
  exists e, look P p = Some e /\ pe_pid e = p /\
    ( (exists c', sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c')
                  /\ peer_refused_b P e = false
                  /\ step_refused_b P e c' = false /\ P' = absorb P e c')
      \/ clone_pending_b (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_owned_b P e = true
      \/ (sync_pending_b P e = true /\ P' = sync_result P e)
      \/ (root_pin_pending_b P e = true
          /\ exists r t, look P (pcfg_root P) = Some r /\ P' = pin_root P r t) ).
Proof.
  intros segs cfg p P evs P' H. inversion H; subst;
    (eexists; split; [eassumption | split; [reflexivity|]]).
  all: first
    [ left; eexists; split; [eassumption | split; [assumption | split; [assumption | reflexivity]]]
    | right; left; eapply clone_success_pending; eassumption
    | right; right; left; assumption
    | right; right; right; left; assumption
    | right; right; right; right; left; split; [assumption | reflexivity]
    | right; right; right; right; right; split;
      [assumption | do 2 eexists; split; [eassumption | reflexivity]] ].
Qed.

Lemma look_absorb_self : forall P e c',
  look P (pe_pid e) = Some e ->
  look (absorb P e c') (pe_pid e) = Some (pe_absorb e c').
Proof.
  intros P e c' Hl.
  pose proof (look_in_first_root_pin_children_self P e (cfg_model c')
    (pcfg_procs P) e Hl) as Hl'.
  unfold look, absorb. cbn [pcfg_procs].
  rewrite orphan_at_exit_map, look_in_orphan.
  rewrite look_in_replace_same by (rewrite Hl'; discriminate).
  cbn [option_map]. unfold orphan_slot.
  destruct (m_halted _); [|reflexivity].
  unfold orphan_one. cbn [fst snd]. rewrite bv_eqb_same. reflexivity.
Qed.

(** Two different keys found in the table: it has two entries. *)
Lemma look_in_two : forall ps p q e f,
  look_in ps p = Some e -> look_in ps q = Some f -> p <> q ->
  (1 < List.length ps)%nat.
Proof.
  induction ps as [|[k x] r IH]; intros p q e f Hp Hq Hne; [discriminate Hp|].
  cbn [look_in fst snd] in Hp, Hq. cbn [List.length].
  destruct r as [|kv r']; [|cbn [List.length]; lia].
  cbn [look_in] in Hp, Hq.
  destruct (bv_eqb k p) eqn:Ep; [|discriminate Hp].
  destruct (bv_eqb k q) eqn:Eq; [|discriminate Hq].
  apply bv_eqb_true_eq in Ep, Eq. subst. contradiction.
Qed.

(* =========================================================================
   flock
   ========================================================================= *)

(** THE FLOCK PIN.  flock with a descriptor naming a file another entry
    has open is refused and has no successor. *)
Theorem flock_conflict_refused : forall segs cfg P e x8,
  look P (pe_pid e) = Some e ->
  m_halted (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 32%Z ->
  (1 < List.length (pcfg_procs P))%nat ->
  flock_conflict_b P e = true ->
  pstep_at segs cfg (pe_pid e) P [] PError
  /\ (forall evs P', ~ pstep_at segs cfg (pe_pid e) P evs (PNext P')).
Proof.
  intros segs cfg P e x8 Hl Hh Hs H32 Hlen Hc.
  assert (Hpr : peer_refused_b P e = true).
  { unfold peer_refused_b. rewrite Hs, H32, Hc.
    apply Nat.ltb_lt in Hlen. rewrite Hlen. rewrite !orb_true_r. reflexivity. }
  split; [apply pstep_peer_refuse; assumption|].
  intros evs P' Hp.
  destruct (pstep_next_gate_cases _ _ _ _ _ _ Hp) as (e1 & Hl1 & _ & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hcases as [ (c' & _ & Hpr' & _) | [ Hcp | [ Hwt | [ Hwo | [ (Hsy & _) | (Hrp & _) ] ] ] ] ].
  - congruence.
  - unfold clone_pending_b, clone_sysno in Hcp. cbn [cfg_ms pe_cfg] in Hcp.
    rewrite Hs, H32 in Hcp. discriminate Hcp.
  - unfold wait4_intercept_b in Hwt. cbn [cfg_ms pe_cfg] in Hwt.
    rewrite Hs, H32 in Hwt. discriminate Hwt.
  - destruct (wait4_owned_260 _ _ Hwo) as (y & Hy & Hy260).
    rewrite Hs in Hy. injection Hy as <-. lia.
  - rewrite (sync_of_sysno P e x8 Hs) in Hsy; [discriminate Hsy|].
    rewrite H32. reflexivity.
  - unfold root_pin_pending_b in Hrp. rewrite Hs, H32 in Hrp. discriminate Hrp.
Qed.

(* =========================================================================
   unlinkat
   ========================================================================= *)

(** Every path [f]'s file descriptors and stat pins name is a path of
    [img]. *)
Definition peer_names_in (img : Fs.Fs) (f : ProcessEntry) : Prop :=
  (forall kv p, List.In kv (m_fds (pe_model f)) -> fd_named_path (snd kv) = Some p ->
     exists d, fs_lookup img p = Some d)
  /\ (forall kv, List.In kv (m_statpins (pe_model f)) ->
        exists d, fs_lookup img (fst kv) = Some d).

Lemma names_removed_false : forall old new f,
  entry_names_removed old new f = false ->
  peer_names_in old f -> peer_names_in new f.
Proof.
  intros old new f H (Hfd & Hpin).
  unfold entry_names_removed in H. apply orb_false_iff in H as [Hf Hp].
  split.
  - intros kv p Hin Hn. destruct (Hfd kv p Hin Hn) as (d & Hd).
    assert (Hr : removed_b old new p = false).
    { apply Bool.not_true_iff_false. intros Hr.
      apply Bool.not_true_iff_false in Hf. apply Hf.
      apply List.existsb_exists. exists kv. split; [exact Hin|]. rewrite Hn. exact Hr. }
    unfold removed_b in Hr. rewrite Hd in Hr.
    destruct (fs_lookup new p) as [d'|]; [exists d'; reflexivity | discriminate Hr].
  - intros kv Hin. destruct (Hpin kv Hin) as (d & Hd).
    assert (Hr : removed_b old new (fst kv) = false).
    { apply Bool.not_true_iff_false. intros Hr.
      apply Bool.not_true_iff_false in Hp. apply Hp.
      apply List.existsb_exists. exists kv. split; [exact Hin | exact Hr]. }
    unfold removed_b in Hr. rewrite Hd in Hr.
    destruct (fs_lookup new (fst kv)) as [d'|]; [exists d'; reflexivity | discriminate Hr].
Qed.

(** THE UNLINKAT CONSISTENCY.  After a step at 35, another entry keeps
    its model, and every path its descriptors and pins named before is
    still a path of the file system. *)
Theorem unlink_keeps_peer_names : forall segs cfg P evs P' e x8 q f,
  look P (pe_pid e) = Some e ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 35%Z ->
  pstep_at segs cfg (pe_pid e) P evs (PNext P') ->
  q <> pe_pid e -> look P q = Some f ->
  peer_names_in (fsst_image (sh_fsys (pcfg_shared P))) f ->
  exists f', look P' q = Some f' /\ pe_model f' = pe_model f
    /\ peer_names_in (fsst_image (sh_fsys (pcfg_shared P'))) f'.
Proof.
  intros segs cfg P evs P' e x8 q f Hl Hs H35 Hp Hne Hf Hin.
  destruct (pstep_next_gate_cases _ _ _ _ _ _ Hp) as (e1 & Hl1 & _ & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hcases as [ (c' & Hstep & _ & Hst & ->) | [ Hcp | [ Hwt | [ Hwo | [ (Hsy & _) | (Hrp & _) ] ] ] ] ].
  - assert (Hshared : multiproc_shared (pe_cfg (pcfg_shared P) e) = true).
    { unfold multiproc_shared. cbn [cfg_ms pe_cfg]. rewrite Hs, H35. reflexivity. }
    pose proof (sstep_shared_frame _ _ _ _ _ Hshared Hstep) as (_ & Htid).
    change (m_tid (cfg_model c') = m_tid (pe_model e)) in Htid.
    destruct (absorb_keeps_other_tid_stable P e c' q f (fun E => Hne (eq_sym E)) Hf Htid)
      as (f' & Hf' & Hm & _).
    exists f'. split; [exact Hf'|]. split; [exact Hm|].
    assert (Hlen : (1 < List.length (pcfg_procs P))%nat)
      by exact (look_in_two _ _ _ _ _ Hl Hf (fun E => Hne (eq_sym E))).
    unfold step_refused_b in Hst. apply Nat.ltb_lt in Hlen. rewrite Hlen, Hs, H35 in Hst.
    cbn [andb] in Hst. apply orb_false_iff in Hst as [_ Hst]. cbn [Z.eqb andb] in Hst.
    unfold other_entry_b in Hst.
    assert (Hr : entry_names_removed (fsst_image (sh_fsys (pcfg_shared P)))
                   (m_fs (cfg_model c')) f = false).
    { apply Bool.not_true_iff_false. intros Hr.
      apply Bool.not_true_iff_false in Hst. apply Hst.
      apply List.existsb_exists. exists (q, f). split.
      - exact (look_in_In _ _ _ Hf).
      - cbn [fst snd]. rewrite (pid_neq_eqb q (pe_pid e) Hne). exact Hr. }
    pose proof (names_removed_false _ _ _ Hr Hin) as Hn.
    unfold peer_names_in in *. rewrite Hm. exact Hn.
  - exfalso. unfold clone_pending_b, clone_sysno in Hcp. cbn [cfg_ms pe_cfg] in Hcp.
    rewrite Hs, H35 in Hcp. discriminate Hcp.
  - exfalso. unfold wait4_intercept_b in Hwt. cbn [cfg_ms pe_cfg] in Hwt.
    rewrite Hs, H35 in Hwt. discriminate Hwt.
  - exfalso. destruct (wait4_owned_260 _ _ Hwo) as (y & Hy & Hy260).
    rewrite Hs in Hy. injection Hy as <-. lia.
  - exfalso. rewrite (sync_of_sysno P e x8 Hs) in Hsy; [discriminate Hsy|].
    rewrite H35. reflexivity.
  - exfalso. unfold root_pin_pending_b in Hrp. rewrite Hs, H35 in Hrp. discriminate Hrp.
Qed.

(* =========================================================================
   The parent-death signal
   ========================================================================= *)

(** THE PARENT-DEATH PIN.  While a peer lives, a step that halts an entry
    (other than a clone or a [wait4] the core answers, whose arms are
    their own) leaves no running child of it holding a nonzero
    parent-death signal. *)
Theorem pdeath_never_lost : forall segs cfg P evs P' e e',
  look P (pe_pid e) = Some e ->
  m_halted (pe_model e) = None ->
  (1 < List.length (pcfg_procs P))%nat ->
  clone_pending_b (pe_cfg (pcfg_shared P) e) = false ->
  wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
  wait4_owned_b P e = false ->
  pstep_at segs cfg (pe_pid e) P evs (PNext P') ->
  look P' (pe_pid e) = Some e' ->
  m_halted (pe_model e') <> None ->
  pdeath_child_b P e = false.
Proof.
  intros segs cfg P evs P' e e' Hl Hh Hlen Hcp Hwi Hwo Hp Hl' Hh'.
  destruct (pstep_next_gate_cases _ _ _ _ _ _ Hp) as (e1 & Hl1 & _ & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hcases as [ (c' & _ & _ & Hst & ->) | [ Hcp' | [ Hwt | [ Hwo' | [ (Hsy & ->) | (Hrp & r & t & Hlr & ->) ] ] ] ] ].
  - rewrite (look_absorb_self P e c' Hl) in Hl'. injection Hl' as <-.
    change (m_halted (pe_model (pe_absorb e c'))) with (m_halted (cfg_model c')) in Hh'.
    unfold step_refused_b in Hst. apply Nat.ltb_lt in Hlen. rewrite Hlen in Hst.
    cbn [andb] in Hst.
    destruct (m_halted (cfg_model c')) as [w|]; [|contradiction].
    unfold clone_pending_b in Hcp. cbn [cfg_ms pe_cfg] in Hcp.
    destruct (ms_svc_pending (pe_ms e)) as [x8|].
    + rewrite Hcp in Hst. cbn [negb andb] in Hst.
      apply orb_false_iff in Hst as [Hst _]. exact Hst.
    + exact Hst.
  - congruence.
  - congruence.
  - congruence.
  - exfalso. unfold look, sync_result in Hl'. cbn [pcfg_procs] in Hl'.
    rewrite look_in_replace_same in Hl' by (unfold look in Hl; rewrite Hl; discriminate).
    injection Hl' as <-. rewrite sync_entry_halted in Hh'. contradiction.
  - (* the root pin writes the root, and the caller is not the root *)
    exfalso. unfold root_pin_pending_b, is_root_b in Hrp.
    destruct (ms_svc_pending (pe_ms e)); [|discriminate Hrp].
    destruct (bv_eqb (pe_pid e) (pcfg_root P)) eqn:Er;
      [cbn [negb] in Hrp; rewrite andb_false_r in Hrp; discriminate Hrp|].
    unfold look, pin_root in Hl'. cbn [pcfg_procs] in Hl'.
    rewrite look_in_replace_other in Hl'
      by (intros E; rewrite E, bv_eqb_same in Er; discriminate Er).
    unfold look in Hl. rewrite Hl in Hl'. injection Hl' as <-. contradiction.
Qed.
