(** * LinuxProcessSem.Checks.ProcsPidAnswers — a pid answered while a peer lives is the table's

    Not part of the trusted specification: QA on [Procs.answer_ok_b],
    [Procs.pstep_pin_root] and the pid part of [Procs.peer_refused_b], in
    the sense of [Checks.Examples]'s header, under its first reason: the
    statements are universally quantified over configurations and steps.

    ** What this pins

    - [child_tid_is_key]: a non-root entry whose tid is unpinned, stepping
      at set_tid_address, getpid, gettid or setsid, pins its key (the pid
      its parent's clone returned) or nothing.
    - [root_tid_not_key]: the root, likewise, pins a value no other
      entry's key holds.
    - [getppid_answers_parent]: getppid of a non-root entry whose parent
      is another non-root entry answers the parent's key.
    - [getppid_answers_root]: getppid of a child of the root answers the
      root's pinned tid; while it is unpinned the only step is the root
      pin ([getppid_root_unpinned_pins]).
    - [pid_collision_refused]: while two entries would answer one pid, a
      pid call is an error and has no successor. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ProcsWellFormed ProcsPrivateFrame ProcsClockSync ProcsSyncOnce ProcsPeerGates.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(** The producing arms, with what this file needs of each. *)
Lemma pstep_next_pid_cases : forall segs cfg p P evs P',
  pstep_at segs cfg p P evs (PNext P') ->
  exists e, look P p = Some e /\ pe_pid e = p /\
    ( (exists c', peer_refused_b P e = false /\ answer_ok_b P e c' = true
                  /\ P' = absorb P e c')
      \/ clone_pending_b (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_owned_b P e = true
      \/ sync_pending_b P e = true
      \/ (root_pin_pending_b P e = true
          /\ exists r t, look P (pcfg_root P) = Some r /\ P' = pin_root P r t) ).
Proof.
  intros segs cfg p P evs P' H. inversion H; subst;
    (eexists; split; [eassumption | split; [reflexivity|]]).
  all: first
    [ left; eexists; split; [eassumption | split; [eassumption | reflexivity]]
    | right; left; eapply clone_success_pending; eassumption
    | right; right; left; assumption
    | right; right; right; left; assumption
    | right; right; right; right; left; assumption
    | right; right; right; right; right; split;
      [assumption | do 2 eexists; split; [eassumption | reflexivity]] ].
Qed.

(** None of the core's own arms answers a pid number but the root pin,
    which answers only getppid. *)
Lemma pid_number_not_core : forall P e x8,
  ms_svc_pending (pe_ms e) = Some x8 ->
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_pid_sysnos = true ->
  clone_pending_b (pe_cfg (pcfg_shared P) e) = false
  /\ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false
  /\ wait4_owned_b P e = false
  /\ sync_pending_b P e = false.
Proof.
  intros P e x8 Hs Hin.
  cbn [multiproc_pid_sysnos List.existsb] in Hin.
  assert (Hn : bv_unsigned x8 = 96%Z \/ bv_unsigned x8 = 156%Z \/ bv_unsigned x8 = 157%Z
               \/ bv_unsigned x8 = 172%Z \/ bv_unsigned x8 = 173%Z
               \/ bv_unsigned x8 = 178%Z).
  { repeat (apply orb_true_iff in Hin as [Hin|Hin];
            [apply Z.eqb_eq in Hin; tauto|]). discriminate Hin. }
  assert (Hwo : wait4_owned_b P e = false).
  { destruct (wait4_owned_b P e) eqn:Hw; [|reflexivity].
    destruct (wait4_owned_260 _ _ Hw) as (y & Hy & Hy260).
    rewrite Hs in Hy. injection Hy as <-. lia. }
  unfold clone_pending_b, clone_sysno, wait4_intercept_b. cbn [cfg_ms pe_cfg].
  rewrite Hs.
  split; [|split; [|split; [exact Hwo|]]].
  - destruct Hn as [E|[E|[E|[E|[E|E]]]]]; rewrite E; reflexivity.
  - destruct Hn as [E|[E|[E|[E|[E|E]]]]]; rewrite E; reflexivity.
  - apply (sync_of_sysno P e x8 Hs).
    destruct Hn as [E|[E|[E|[E|[E|E]]]]]; rewrite E; reflexivity.
Qed.

Lemma tid_number_pid : forall x8 : word,
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_tid_sysnos = true ->
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_pid_sysnos = true
  /\ bv_unsigned x8 <> 173%Z.
Proof.
  intros x8 Hin. cbn [multiproc_tid_sysnos List.existsb] in Hin.
  repeat (apply orb_true_iff in Hin as [Hin|Hin];
          [apply Z.eqb_eq in Hin; rewrite Hin; split; [reflexivity | discriminate]|]).
  discriminate Hin.
Qed.

(** The released step's successor entry is the absorbed one. *)
Lemma absorb_self_view : forall P e c',
  look P (pe_pid e) = Some e ->
  exists e', look (absorb P e c') (pe_pid e) = Some e'
    /\ pe_ms e' = cfg_ms c' /\ m_tid (pe_model e') = m_tid (cfg_model c').
Proof.
  intros P e c' Hl. exists (pe_absorb e c').
  split; [exact (look_absorb_self P e c' Hl) | split; reflexivity].
Qed.

(* =========================================================================
   The tid
   ========================================================================= *)

(** THE CHILD'S TID IS ITS KEY. *)
Theorem child_tid_is_key : forall segs cfg P evs P' e x8 e',
  look P (pe_pid e) = Some e ->
  is_root_b P e = false ->
  m_tid (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_tid_sysnos = true ->
  pstep_at segs cfg (pe_pid e) P evs (PNext P') ->
  look P' (pe_pid e) = Some e' ->
  m_tid (pe_model e') = None \/ m_tid (pe_model e') = Some (pe_pid e).
Proof.
  intros segs cfg P evs P' e x8 e' Hl Hr Ht Hs Hin Hp Hl'.
  destruct (tid_number_pid x8 Hin) as (Hpid & H173).
  destruct (pid_number_not_core P e x8 Hs Hpid) as (Hcp & Hwi & Hwo & Hsy).
  destruct (pstep_next_pid_cases _ _ _ _ _ _ Hp) as (e1 & Hl1 & _ & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hcases as
    [ (c' & _ & Han & ->) | [ H | [ H | [ H | [ H | (Hrp & _) ] ] ] ] ];
    [ | congruence | congruence | congruence | congruence | ].
  - destruct (absorb_self_view P e c' Hl) as (e2 & Hl2 & _ & Ht2).
    rewrite Hl2 in Hl'. injection Hl' as <-. rewrite Ht2.
    unfold answer_ok_b in Han. rewrite Hs, Hin, Ht, Hr in Han.
    destruct (m_tid (cfg_model c')) as [t|]; [|left; reflexivity].
    right. apply bv_eqb_true_eq in Han. rewrite Han. reflexivity.
  - exfalso. unfold root_pin_pending_b in Hrp. rewrite Hs in Hrp.
    apply Z.eqb_neq in H173. rewrite H173 in Hrp. discriminate Hrp.
Qed.

(** THE ROOT'S TID IS NO OTHER ENTRY'S KEY. *)
Theorem root_tid_not_key : forall segs cfg P evs P' e x8 e',
  look P (pe_pid e) = Some e ->
  is_root_b P e = true ->
  m_tid (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_tid_sysnos = true ->
  pstep_at segs cfg (pe_pid e) P evs (PNext P') ->
  look P' (pe_pid e) = Some e' ->
  m_tid (pe_model e') = None
  \/ exists t, m_tid (pe_model e') = Some t /\ key_taken_b P t = false.
Proof.
  intros segs cfg P evs P' e x8 e' Hl Hr Ht Hs Hin Hp Hl'.
  destruct (tid_number_pid x8 Hin) as (Hpid & H173).
  destruct (pid_number_not_core P e x8 Hs Hpid) as (Hcp & Hwi & Hwo & Hsy).
  destruct (pstep_next_pid_cases _ _ _ _ _ _ Hp) as (e1 & Hl1 & _ & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hcases as
    [ (c' & _ & Han & ->) | [ H | [ H | [ H | [ H | (Hrp & _) ] ] ] ] ];
    [ | congruence | congruence | congruence | congruence | ].
  - destruct (absorb_self_view P e c' Hl) as (e2 & Hl2 & _ & Ht2).
    rewrite Hl2 in Hl'. injection Hl' as <-. rewrite Ht2.
    unfold answer_ok_b in Han. rewrite Hs, Hin, Ht, Hr in Han.
    destruct (m_tid (cfg_model c')) as [t|]; [|left; reflexivity].
    right. exists t. split; [reflexivity|]. apply negb_true_iff. exact Han.
  - exfalso. unfold root_pin_pending_b in Hrp. rewrite Hs in Hrp.
    apply Z.eqb_neq in H173. rewrite H173 in Hrp. discriminate Hrp.
Qed.

(* =========================================================================
   getppid
   ========================================================================= *)

(** GETPPID ANSWERS THE PARENT'S KEY. *)
Theorem getppid_answers_parent : forall segs cfg P evs P' e x8 par e',
  look P (pe_pid e) = Some e ->
  is_root_b P e = false ->
  pe_parent e = Some par ->
  bv_eqb par (pcfg_root P) = false ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 173%Z ->
  pstep_at segs cfg (pe_pid e) P evs (PNext P') ->
  look P' (pe_pid e) = Some e' ->
  ms_gpr (pe_ms e') 0 = par.
Proof.
  intros segs cfg P evs P' e x8 par e' Hl Hr Hpar Hpr Hs H173 Hp Hl'.
  assert (Hpid : List.existsb (Z.eqb (bv_unsigned x8)) multiproc_pid_sysnos = true)
    by (rewrite H173; reflexivity).
  destruct (pid_number_not_core P e x8 Hs Hpid) as (Hcp & Hwi & Hwo & Hsy).
  destruct (pstep_next_pid_cases _ _ _ _ _ _ Hp) as (e1 & Hl1 & _ & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hcases as
    [ (c' & _ & Han & ->) | [ H | [ H | [ H | [ H | (Hrp & _) ] ] ] ] ];
    [ | congruence | congruence | congruence | congruence | ].
  - destruct (absorb_self_view P e c' Hl) as (e2 & Hl2 & Hms & _).
    rewrite Hl2 in Hl'. injection Hl' as <-. rewrite Hms.
    unfold answer_ok_b in Han. rewrite Hs, H173 in Han. cbn [List.existsb
      multiproc_tid_sysnos Z.eqb] in Han.
    rewrite Hr, Hpar, Hpr in Han. apply bv_eqb_true_eq in Han. exact Han.
  - exfalso. unfold root_pin_pending_b in Hrp. rewrite Hs, H173, Hpar, Hpr in Hrp.
    rewrite !andb_false_r in Hrp. discriminate Hrp.
Qed.

(** GETPPID OF A CHILD OF THE ROOT ANSWERS THE ROOT'S TID. *)
Theorem getppid_answers_root : forall segs cfg P evs P' e x8 t e',
  look P (pe_pid e) = Some e ->
  is_root_b P e = false ->
  pe_parent e = Some (pcfg_root P) ->
  root_tid P = Some t ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 173%Z ->
  pstep_at segs cfg (pe_pid e) P evs (PNext P') ->
  look P' (pe_pid e) = Some e' ->
  ms_gpr (pe_ms e') 0 = t.
Proof.
  intros segs cfg P evs P' e x8 t e' Hl Hr Hpar Hrt Hs H173 Hp Hl'.
  assert (Hpid : List.existsb (Z.eqb (bv_unsigned x8)) multiproc_pid_sysnos = true)
    by (rewrite H173; reflexivity).
  destruct (pid_number_not_core P e x8 Hs Hpid) as (Hcp & Hwi & Hwo & Hsy).
  destruct (pstep_next_pid_cases _ _ _ _ _ _ Hp) as (e1 & Hl1 & _ & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hcases as
    [ (c' & _ & Han & ->) | [ H | [ H | [ H | [ H | (Hrp & _) ] ] ] ] ];
    [ | congruence | congruence | congruence | congruence | ].
  - destruct (absorb_self_view P e c' Hl) as (e2 & Hl2 & Hms & _).
    rewrite Hl2 in Hl'. injection Hl' as <-. rewrite Hms.
    unfold answer_ok_b in Han. rewrite Hs, H173 in Han. cbn [List.existsb
      multiproc_tid_sysnos Z.eqb] in Han.
    rewrite Hr, Hpar, bv_eqb_same, Hrt in Han. apply bv_eqb_true_eq in Han. exact Han.
  - exfalso. unfold root_pin_pending_b in Hrp. unfold root_tid in Hrt.
    destruct (look P (pcfg_root P)) as [r|]; [|discriminate Hrt].
    rewrite Hs, Hrt in Hrp. cbv beta iota in Hrp.
    rewrite !andb_false_r in Hrp. discriminate Hrp.
Qed.

(** While the root's tid is unpinned, a child of the root at getppid has
    the root pin as its only successor. *)
Theorem getppid_root_unpinned_pins : forall segs cfg P evs P' e x8,
  look P (pe_pid e) = Some e ->
  is_root_b P e = false ->
  pe_parent e = Some (pcfg_root P) ->
  root_tid P = None ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 173%Z ->
  pstep_at segs cfg (pe_pid e) P evs (PNext P') ->
  exists r t, look P (pcfg_root P) = Some r /\ P' = pin_root P r t.
Proof.
  intros segs cfg P evs P' e x8 Hl Hr Hpar Hrt Hs H173 Hp.
  assert (Hpid : List.existsb (Z.eqb (bv_unsigned x8)) multiproc_pid_sysnos = true)
    by (rewrite H173; reflexivity).
  destruct (pid_number_not_core P e x8 Hs Hpid) as (Hcp & Hwi & Hwo & Hsy).
  destruct (pstep_next_pid_cases _ _ _ _ _ _ Hp) as (e1 & Hl1 & _ & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hcases as
    [ (c' & _ & Han & ->) | [ H | [ H | [ H | [ H | (_ & Hpin) ] ] ] ] ];
    [ | congruence | congruence | congruence | congruence | exact Hpin ].
  exfalso. unfold answer_ok_b in Han. rewrite Hs, H173 in Han.
  cbn [List.existsb multiproc_tid_sysnos Z.eqb] in Han.
  rewrite Hr, Hpar, bv_eqb_same, Hrt in Han. discriminate Han.
Qed.

(* =========================================================================
   The collision
   ========================================================================= *)

(** THE COLLISION PIN.  While the root's tid is another entry's key, a pid
    call is an error and has no successor. *)
Theorem pid_collision_refused : forall segs cfg P e x8,
  look P (pe_pid e) = Some e ->
  m_halted (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_pid_sysnos = true ->
  (1 < List.length (pcfg_procs P))%nat ->
  pid_collision_b P = true ->
  pstep_at segs cfg (pe_pid e) P [] PError
  /\ (forall evs P', ~ pstep_at segs cfg (pe_pid e) P evs (PNext P')).
Proof.
  intros segs cfg P e x8 Hl Hh Hs Hpid Hlen Hc.
  assert (Hpr : peer_refused_b P e = true).
  { unfold peer_refused_b. rewrite Hs, Hpid, Hc.
    apply Nat.ltb_lt in Hlen. rewrite Hlen. rewrite !orb_true_r. reflexivity. }
  split; [apply pstep_peer_refuse; assumption|].
  intros evs P' Hp.
  destruct (pid_number_not_core P e x8 Hs Hpid) as (Hcp & Hwi & Hwo & Hsy).
  destruct (pstep_next_pid_cases _ _ _ _ _ _ Hp) as (e1 & Hl1 & _ & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hcases as
    [ (c' & Hpr' & _ & _) | [ H | [ H | [ H | [ H | (Hrp & _) ] ] ] ] ];
    [ congruence | congruence | congruence | congruence | congruence | ].
  unfold pid_collision_b, root_tid in Hc. unfold root_pin_pending_b in Hrp.
  destruct (look P (pcfg_root P)) as [r|]; [|discriminate Hc].
  destruct (m_tid (pe_model r)); [|discriminate Hc].
  destruct (ms_svc_pending (pe_ms e)); [|discriminate Hrp].
  cbv beta iota in Hrp. rewrite !andb_false_r in Hrp. discriminate Hrp.
Qed.
