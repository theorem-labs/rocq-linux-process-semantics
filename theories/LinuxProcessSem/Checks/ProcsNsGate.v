(** * LinuxProcessSem.Checks.ProcsNsGate — a namespace child never gets its parent's answer

    Not part of the trusted specification: QA on [Procs.ns_refused_b], in
    the sense of [Checks.Examples]'s header, under its first reason: the
    statements are universally quantified over configurations and steps.

    ** What this pins

    Under no extension a clone with namespace bits gives the child the
    parent's model and the parent's namespace context.  In a new user
    namespace with no [uid_map] Linux answers getuid with the overflow id
    65534; the released spec would answer the parent's id.  The exact
    behaviour belongs to the namespace extension ([Ns.Ext.ext_clone]
    builds the child's context); the core only stops answering wrongly.

    - [clone_result_userns_stale]: a clone (no extension) whose flag word
      asks for a new user namespace records the child's user namespace as
      stale ([Procs.pm_ns_stale]).
    - [userns_getuid_refused]: an entry whose user namespace is stale, with
      getuid (174) pending, takes [pstep_ns_refuse] (an error, never the
      absence of an arm) and no step of it has a successor.  So the
      class-(A) arm cannot answer it, and losing the gate fails this
      Check. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(** A clone that asks for a new user namespace leaves the child's user
    namespace stale. *)
Theorem clone_result_userns_stale : forall P e c' q,
  Z.land (clone_flags_of (pe_cfg (pcfg_shared P) e)) CLONE_NEWUSER <> 0%Z ->
  Z.land (pm_ns_stale (meta_look (sh_meta (pcfg_shared (clone_result P e c' q))) q))
    CLONE_NEWUSER <> 0%Z.
Proof.
  intros P e c' q Hf.
  unfold clone_result, with_meta. cbn [pcfg_shared sh_meta meta_look].
  rewrite bv_eqb_same. cbv beta iota. unfold child_meta, ns_stale_child.
  cbn [pm_ns_stale]. rewrite !Pos.eqb_refl. cbv beta iota.
  intros H.
  rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [_ H].
  rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [H _].
  rewrite <- Z.land_assoc, Z.land_diag in H. exact (Hf H).
Qed.

(** A step to a successor passes the namespace gate, or is a clone or one
    of the [wait4] arms. *)
Lemma pstep_next_ns : forall segs cfg p P evs P',
  pstep_at segs cfg p P evs (PNext P') ->
  exists e, look P p = Some e /\
    ( ns_refused_b P e = false
      \/ clone_pending_b (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_owned_b P e = true
      \/ sync_pending_b P e = true ).
Proof.
  intros segs cfg p P evs P' H. inversion H; subst;
    (eexists; split; [eassumption|]).
  all: first
    [ left; assumption
    | right; left; eapply clone_success_pending; eassumption
    | right; right; left; assumption
    | right; right; right; left; assumption
    | right; right; right; right; assumption ].
Qed.

Lemma intercept_260_ns : forall c,
  wait4_intercept_b c = true ->
  exists x8, ms_svc_pending (cfg_ms c) = Some x8 /\ bv_unsigned x8 = 260%Z.
Proof.
  intros c H. unfold wait4_intercept_b in H.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; [|discriminate H].
  apply andb_true_iff in H as [H _]. apply Z.eqb_eq in H.
  exists x8. split; [reflexivity | exact H].
Qed.

(** THE PIN.  getuid of an entry whose user namespace is stale is refused
    with an error and has no successor. *)
Theorem userns_getuid_refused : forall segs cfg P e x8,
  look P (pe_pid e) = Some e ->
  m_halted (pe_model e) = None ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  bv_unsigned x8 = 174%Z ->
  Z.land (pm_ns_stale (meta_look (sh_meta (pcfg_shared P)) (pe_pid e))) CLONE_NEWUSER
    <> 0%Z ->
  pstep_at segs cfg (pe_pid e) P [] PError
  /\ (forall evs P', ~ pstep_at segs cfg (pe_pid e) P evs (PNext P')).
Proof.
  intros segs cfg P e x8 Hl Hh Hs H174 Hst.
  assert (Hns : ns_refused_b P e = true).
  { unfold ns_refused_b. rewrite Hs, H174.
    apply Z.eqb_neq in Hst. rewrite Hst. reflexivity. }
  split; [apply pstep_ns_refuse; assumption|].
  intros evs P' Hp.
  destruct (pstep_next_ns _ _ _ _ _ _ Hp) as (e1 & Hl1 & Hor).
  rewrite Hl in Hl1. injection Hl1 as <-.
  destruct Hor as [Hn | [Hcp | [Hwt | [Hwo | Hsy]]]].
  - congruence.
  - unfold clone_pending_b, clone_sysno in Hcp. cbn [cfg_ms pe_cfg] in Hcp.
    rewrite Hs, H174 in Hcp. discriminate Hcp.
  - destruct (intercept_260_ns _ Hwt) as (y & Hy & Hy260).
    cbn [cfg_ms pe_cfg] in Hy. rewrite Hs in Hy. injection Hy as <-. lia.
  - destruct (wait4_owned_260 _ _ Hwo) as (y & Hy & Hy260).
    rewrite Hs in Hy. injection Hy as <-. lia.
  - unfold sync_pending_b in Hsy. rewrite Hs, H174 in Hsy. discriminate Hsy.
Qed.
