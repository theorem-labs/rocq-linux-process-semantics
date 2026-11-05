(** * LinuxProcessSem.Checks.ProcsSigchldRule — no step sets the SIGCHLD bit of an entry with a child in the table

    Not part of the trusted specification: QA on the multi-process core's
    keeping of the rule [Kernel.Signal.sigchld_install_model] states for
    one process: the bit [State.procst_sigchld_dfl] is set only if every
    child the process has was cloned while SIGCHLD was SIG_DFL.  Linux
    decides at a child's exit whether to reap it itself, from the parent's
    disposition then ([do_notify_parent], kernel/signal.c:2241-2259, and
    [exit_notify], kernel/exit.c:763-785, Linux v6.18.46), so an install
    made after a clone cannot vouch for that child.

    In the core a child is an entry of the table.  The rule at this level:
    no step turns an entry's bit from clear to set while that entry has a
    child in the table ([pstep_at_sigchld_no_set_with_child], with its
    [pstep_cfg] and [pstep_x_at] forms).  The released half is
    [Checks.ProcsSigchldFrame.sstep_sigchld_no_set_with_children]: a
    released step never sets the bit of a model whose [m_has_children] is
    set.  What ties the two is [hc_all]: every entry whose list of
    unreaped children ([State.m_child_pids]) is not empty has
    [m_has_children] set, and [Checks.ProcsChildPids.child_pids_ok] makes
    that list the entry's children in the table.  A clone's child starts
    with an empty list and a clear [m_has_children] ([Procs.child_proc])
    and copies its parent's bit, which is what the rule asks of a new
    process.

    [sigchld_rule_reachable] gives every premise from any launch. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ProcsWellFormed ProcsWait4Gate ProcsChildPids ProcsSigchldFrame ProcsSigchld.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   The model invariant, over the table
   ========================================================================= *)

(** Every entry with an unreaped child on its list has [m_has_children]. *)
Definition hc_all (P : pconfig) : Prop :=
  List.Forall (fun kv => hc_ok (pe_model (snd kv))) (pcfg_procs P).

Lemma hc_all_look : forall P k f, hc_all P -> look P k = Some f -> hc_ok (pe_model f).
Proof.
  intros P k f H Hl. unfold look in Hl. apply look_in_In in Hl.
  unfold hc_all in H. rewrite List.Forall_forall in H. exact (H _ Hl).
Qed.

Lemma hc_orphan_at_exit : forall m p ps,
  List.Forall (fun kv => hc_ok (pe_model (snd kv))) ps ->
  List.Forall (fun kv => hc_ok (pe_model (snd kv))) (orphan_at_exit m p ps).
Proof.
  intros m p ps H. unfold orphan_at_exit. destruct (m_halted m); cbv iota; [|exact H].
  unfold orphan_children. apply List.Forall_map.
  eapply List.Forall_impl; [|exact H].
  intros kv Hkv. cbv beta. unfold orphan_one.
  match goal with |- context [if ?b then _ else _] => destruct b end; exact Hkv.
Qed.

(** A first root-tid pin resolves the root's running children's parent
    pid ([Procs.root_children_ppid], [State.with_ppid]), which carries the
    list and [m_has_children]. *)
Lemma hc_root_children : forall root t ps,
  List.Forall (fun kv => hc_ok (pe_model (snd kv))) ps ->
  List.Forall (fun kv => hc_ok (pe_model (snd kv))) (root_children_ppid root t ps).
Proof.
  intros root t ps H. unfold root_children_ppid. apply List.Forall_map.
  eapply List.Forall_impl; [|exact H].
  intros [q f] Hkv. cbv beta in *.
  destruct (root_child_ppid_one_model root t q f) as [E | E]; rewrite E; exact Hkv.
Qed.

Lemma hc_first_root_pin : forall P e m' ps,
  List.Forall (fun kv => hc_ok (pe_model (snd kv))) ps ->
  List.Forall (fun kv => hc_ok (pe_model (snd kv))) (first_root_pin_children P e m' ps).
Proof.
  intros P e m' ps H. unfold first_root_pin_children.
  destruct (bv_eqb (pe_pid e) (pcfg_root P)); [|exact H].
  destruct (m_tid (pe_model e)), (m_tid m');
    first [exact H | apply hc_root_children; exact H].
Qed.

Lemma hc_absorb : forall P e c',
  hc_all P -> hc_ok (cfg_model c') -> hc_all (absorb P e c').
Proof.
  intros P e c' H Hc. unfold hc_all, absorb. cbn [pcfg_procs].
  apply hc_orphan_at_exit. apply Forall_replace_in; [apply hc_first_root_pin; exact H|].
  exact Hc.
Qed.

Lemma hc_of_proc : forall m m', m_proc m' = m_proc m -> hc_ok m -> hc_ok m'.
Proof.
  intros m m' Hp H. unfold hc_ok, m_child_pids, m_has_children in *.
  rewrite Hp. exact H.
Qed.

Lemma hc_sync_entry : forall P e,
  m_child_pids (pe_model (sync_entry P e)) = m_child_pids (pe_model e)
  /\ m_has_children (pe_model (sync_entry P e)) = m_has_children (pe_model e).
Proof.
  intros P e. unfold sync_entry, uts_fill, pin_fill. cbn [pe_model].
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
    split; reflexivity.
Qed.

Lemma filter_nonnil : forall {A} (f : A -> bool) l, List.filter f l <> [] -> l <> [].
Proof. intros A f l H E. subst l. apply H. reflexivity. Qed.

(** A reap's entry: its list shrinks, its [m_has_children] stays. *)
Lemma hc_reap_entry : forall P e q eff model'',
  materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
    (syscall_effect_accesses eff) = Some model'' ->
  hc_ok (pe_model e) -> hc_ok (clear_shared (reap_model q model'')).
Proof.
  intros P e q eff model'' Hm H.
  destruct (materialize_model_accesses_frame _ _ _ Hm) as (_ & _ & _ & _ & _ & Hp & _).
  intros Hn.
  change (m_child_pids (clear_shared (reap_model q model'')))
    with (List.filter (fun x => negb (bv_eqb x q)) (m_child_pids model'')) in Hn.
  apply filter_nonnil in Hn.
  change (m_has_children (clear_shared (reap_model q model''))) with (m_has_children model'').
  exact (hc_of_proc (cfg_model (pe_cfg (pcfg_shared P) e)) model'' Hp H Hn).
Qed.

(** Every step of the core keeps [hc_all]. *)
Theorem pstep_at_preserves_hc : forall segs cfg p P evs P',
  hc_all P -> pstep_at segs cfg p P evs (PNext P') -> hc_all P'.
Proof.
  intros segs cfg p P evs P' H Hs.
  inversion Hs; subst.
  - (* pstep_other *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e, Hss : sstep_cfg _ _ _ _ (SNext ?c') |- _ =>
        apply hc_absorb; [exact H|];
        exact (sstep_hc_ok _ _ _ _ _ Hss (hc_all_look _ _ _ H Hl))
    end.
  - (* pstep_clone: the child's list is empty *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e, Hss : sstep_cfg _ _ _ _ (SNext ?c') |- _ =>
        unfold clone_result, hc_all; cbn [pcfg_procs];
        apply List.Forall_app; split;
        [ apply Forall_replace_in; [exact H|];
          exact (sstep_hc_ok _ _ _ _ _ Hss (hc_all_look _ _ _ H Hl))
        | constructor; [intros Hn; exfalso; apply Hn; reflexivity | constructor] ]
    end.
  - (* pstep_wait_reap *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e,
      Hm : materialize_model_accesses _ _ = Some ?model'' |- _ =>
        unfold hc_all; cbn [pcfg_procs];
        apply Forall_drop_in; apply Forall_replace_in; [exact H|];
        cbv beta; cbn [snd pe_model];
        exact (hc_reap_entry _ _ _ _ _ Hm (hc_all_look _ _ _ H Hl))
    end.
  - (* pstep_wait_nohang_reap *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e,
      Hm : materialize_model_accesses _ _ = Some ?model'' |- _ =>
        unfold wait4_reap_result, hc_all; cbn [pcfg_procs];
        apply Forall_drop_in; apply Forall_replace_in; [exact H|];
        cbv beta; cbn [snd pe_model];
        exact (hc_reap_entry _ _ _ _ _ Hm (hc_all_look _ _ _ H Hl))
    end.
  - (* pstep_wait_nohang_zero *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e |- _ =>
        unfold wait4_zero_result; apply hc_absorb; [exact H|];
        exact (hc_all_look _ _ _ H Hl)
    end.
  - (* pstep_sync *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e |- _ =>
        unfold sync_result, hc_all; cbn [pcfg_procs];
        apply Forall_replace_in; [exact H|];
        cbv beta; cbn [snd];
        destruct (hc_sync_entry Q e) as (E1 & E2);
        intros Hn; rewrite E1 in Hn; rewrite E2;
        exact (hc_all_look _ _ _ H Hl Hn)
    end.
  - (* pstep_pin_root: the root's children's parent pid resolved, if
       this is the first pin *)
    match goal with
    | Hr : look ?Q (pcfg_root ?Q) = Some ?r |- _ =>
        unfold pin_root, hc_all; cbn [pcfg_procs];
        apply Forall_replace_in;
        [ first
          [ exact H
          | match goal with
            | |- List.Forall _ (match ?x with _ => _ end) =>
                destruct x; first [exact H | apply hc_root_children; exact H]
            end ]
        | exact (hc_all_look _ _ _ H Hr) ]
    end.
Qed.

Lemma hc_all_one_proc : forall c, hc_ok (cfg_model c) -> hc_all (one_proc c).
Proof.
  intros c H. unfold hc_all, one_proc. cbn [pcfg_procs].
  constructor; [exact H | constructor].
Qed.

(** From a launch with no recorded child, every reachable table is well
    formed, lists each running entry's children ([child_pids_ok]), and
    keeps [hc_all]. *)
Theorem sigchld_rule_invariants : forall segs cfg c P,
  m_child_pids (cfg_model c) = [] ->
  pruns segs cfg (one_proc c) P ->
  pconfig_wf P /\ child_pids_ok P /\ hc_all P.
Proof.
  intros segs cfg c P H0 Hr.
  pose proof (pconfig_wf_one_proc c) as Hwf.
  pose proof (child_pids_ok_one_proc c H0) as Hok.
  assert (Hhc : hc_all (one_proc c))
    by (apply hc_all_one_proc; intros Hn; exfalso; exact (Hn H0)).
  remember (one_proc c) as Q eqn:HQ. clear HQ.
  revert Hwf Hok Hhc.
  induction Hr as [Q | Q evs Q' Q'' Hs _ IH]; intros Hwf Hok Hhc;
    [split; [exact Hwf | split; [exact Hok | exact Hhc]]|].
  destruct Hs as (p & Hs).
  apply IH.
  - exact (pstep_at_preserves_wf _ _ _ _ _ _ Hwf Hs).
  - exact (pstep_at_preserves_child_pids _ _ _ _ _ _ Hwf Hok Hs).
  - exact (pstep_at_preserves_hc _ _ _ _ _ _ Hhc Hs).
Qed.

(* =========================================================================
   The rule
   ========================================================================= *)

Lemma In_replace_in : forall ps p e' kv,
  List.In kv (replace_in ps p e') -> List.In kv ps \/ kv = (p, e').
Proof.
  induction ps as [|kv0 r IH]; intros p e' kv H; cbn [replace_in] in H; [contradiction|].
  destruct (bv_eqb (fst kv0) p).
  - destruct H as [<- | H]; [right; reflexivity | left; right; exact H].
  - destruct H as [<- | H]; [left; left; reflexivity|].
    destruct (IH p e' kv H) as [H1 | H1]; [left; right; exact H1 | right; exact H1].
Qed.

Lemma In_drop_in : forall ps p kv, List.In kv (drop_in ps p) -> List.In kv ps.
Proof.
  induction ps as [|kv0 r IH]; intros p kv H; cbn [drop_in] in H; [contradiction|].
  destruct (bv_eqb (fst kv0) p).
  - right. exact H.
  - destruct H as [<- | H]; [left; reflexivity | right; exact (IH p kv H)].
Qed.

Lemma In_orphan_at_exit : forall m p ps k f',
  List.In (k, f') (orphan_at_exit m p ps) ->
  exists f, List.In (k, f) ps /\ pe_model f' = pe_model f.
Proof.
  intros m p ps k f' H. unfold orphan_at_exit in H.
  destruct (m_halted m); cbv iota in H; [|exists f'; split; [exact H | reflexivity]].
  unfold orphan_children in H. apply List.in_map_iff in H as ([k0 f0] & E & Hin).
  unfold orphan_one in E. cbn [fst snd] in E.
  match type of E with context [if ?b then _ else _] => destruct b end;
    injection E as <- <-; exists f0; (split; [exact Hin | reflexivity]).
Qed.

(** An entry of the replaced table is the replacement or the old entry. *)
Lemma replace_origin : forall P k f f' p e',
  pconfig_wf P -> look P k = Some f ->
  List.In (k, f') (replace_in (pcfg_procs P) p e') ->
  (k = p /\ f' = e') \/ f' = f.
Proof.
  intros P k f f' p e' Hwf Hl Hin.
  destruct (In_replace_in _ _ _ _ Hin) as [H | H].
  - right. exact (same_key P k f f' Hwf Hl H).
  - injection H as -> ->. left. split; reflexivity.
Qed.

(** An entry of a first root-tid pin's table is an entry of the table it
    came from, perhaps with its parent pid resolved, so with the same bit. *)
Lemma In_root_children : forall root t ps k g,
  List.In (k, g) (root_children_ppid root t ps) ->
  exists g0, List.In (k, g0) ps /\ m_sigchld_dfl (pe_model g) = m_sigchld_dfl (pe_model g0).
Proof.
  intros root t ps k g H. unfold root_children_ppid in H.
  apply List.in_map_iff in H as ([k0 g0] & E & Hin).
  assert (Hk : k0 = k).
  { pose proof (root_child_ppid_one_fst root t (k0, g0)) as Hf.
    rewrite E in Hf. cbn [fst] in Hf. symmetry. exact Hf. }
  rewrite Hk in Hin. exists g0. split; [exact Hin|].
  destruct (root_child_ppid_one_model root t k0 g0) as [M | M];
    rewrite E in M; cbn [snd] in M; rewrite M; reflexivity.
Qed.

Lemma In_first_root_pin : forall P e m' ps k g,
  List.In (k, g) (first_root_pin_children P e m' ps) ->
  exists g0, List.In (k, g0) ps /\ m_sigchld_dfl (pe_model g) = m_sigchld_dfl (pe_model g0).
Proof.
  intros P e m' ps k g H. unfold first_root_pin_children in H.
  destruct (bv_eqb (pe_pid e) (pcfg_root P));
    [|exists g; split; [exact H | reflexivity]].
  destruct (m_tid (pe_model e)), (m_tid m');
    first [exists g; split; [exact H | reflexivity] | exact (In_root_children _ _ _ _ _ H)].
Qed.

(** [replace_origin] over a table whose entries come from [pcfg_procs P]
    with their bit kept: the replacement, or an entry with the old one's
    bit. *)
Lemma replace_origin_bit : forall P ps k f f' p e',
  pconfig_wf P -> look P k = Some f ->
  List.In (k, f') (replace_in ps p e') ->
  (forall g, List.In (k, g) ps ->
     exists g0, List.In (k, g0) (pcfg_procs P)
                /\ m_sigchld_dfl (pe_model g) = m_sigchld_dfl (pe_model g0)) ->
  (k = p /\ f' = e') \/ m_sigchld_dfl (pe_model f') = m_sigchld_dfl (pe_model f).
Proof.
  intros P ps k f f' p e' Hwf Hl Hin Hps.
  destruct (In_replace_in _ _ _ _ Hin) as [H | H].
  - right. destruct (Hps _ H) as (g0 & Hg0 & E). rewrite E.
    rewrite (same_key P k f g0 Hwf Hl Hg0). reflexivity.
  - injection H as -> ->. left. split; reflexivity.
Qed.

(** A child in the table: a non-empty list of children's keys. *)
Lemma has_child_keys : forall P k,
  has_child_b P k = true -> children_keys (pcfg_procs P) k <> [].
Proof.
  intros P k H Hn. unfold children_keys in Hn. apply List.map_eq_nil in Hn.
  unfold is_child_of in Hn. unfold has_child_b, children_of in H.
  rewrite Hn in H. discriminate H.
Qed.

Lemma sstep_running : forall segs cfg c evs r,
  sstep_cfg segs cfg c evs r -> m_halted (cfg_model c) = None.
Proof. intros segs cfg c evs r H. destruct H; assumption. Qed.

(** The stepping entry, at a released step: with a child in the table its
    [m_has_children] is set, so the step keeps a clear bit clear. *)
Lemma released_no_set : forall segs cfg P e evs c',
  child_pids_ok P -> hc_all P ->
  look P (pe_pid e) = Some e ->
  has_child_b P (pe_pid e) = true ->
  sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
  m_sigchld_dfl (pe_model e) = false ->
  m_sigchld_dfl (cfg_model c') = false.
Proof.
  intros segs cfg P e evs c' Hok Hhc Hl Hch Hs Hd.
  pose proof (sstep_running _ _ _ _ _ Hs) as Hrun.
  assert (Hrun' : m_halted (pe_model e) = None) by exact Hrun.
  pose proof (Hok _ _ Hl Hrun') as Hcp.
  assert (Hn : m_child_pids (pe_model e) <> [])
    by (rewrite Hcp; exact (has_child_keys _ _ Hch)).
  pose proof (hc_all_look _ _ _ Hhc Hl Hn) as Hhc'.
  exact (sstep_sigchld_no_set_with_children _ _ _ _ _ Hs Hhc' Hd).
Qed.

(** THE RULE: no step of the core turns an entry's bit from clear to set
    while that entry has a child in the table. *)
Theorem pstep_at_sigchld_no_set_with_child : forall segs cfg p P evs P' k f f',
  pconfig_wf P -> child_pids_ok P -> hc_all P ->
  pstep_at segs cfg p P evs (PNext P') ->
  look P k = Some f -> look P' k = Some f' ->
  has_child_b P k = true ->
  m_sigchld_dfl (pe_model f) = false ->
  m_sigchld_dfl (pe_model f') = false.
Proof.
  intros segs cfg p P evs P' k f f' Hwf Hok Hhc Hs Hl Hl' Hch Hd.
  unfold look in Hl'. apply look_in_In in Hl'.
  inversion Hs; subst.
  - (* pstep_other *)
    match goal with
    | He : look ?Q (pe_pid ?e) = Some ?e, Hss : sstep_cfg _ _ _ _ (SNext ?c') |- _ =>
        unfold absorb in Hl'; cbn [pcfg_procs] in Hl';
        destruct (In_orphan_at_exit _ _ _ _ _ Hl') as (g & Hg & Hm);
        rewrite Hm;
        destruct (replace_origin_bit _ _ _ _ _ _ _ Hwf Hl Hg
                    (fun g1 Hg1 => In_first_root_pin _ _ _ _ _ _ Hg1)) as [(-> & ->) | Hbit];
        [ assert (f = e) by congruence; subst f;
          exact (released_no_set _ _ _ _ _ _ Hok Hhc He Hch Hss Hd)
        | rewrite Hbit; exact Hd ]
    end.
  - (* pstep_clone *)
    match goal with
    | He : look ?Q (pe_pid ?e) = Some ?e, Hss : sstep_cfg _ _ _ _ (SNext ?c'),
      Hfree : look ?Q ?q = None |- _ =>
        unfold clone_result in Hl'; cbn [pcfg_procs] in Hl';
        apply List.in_app_or in Hl'; destruct Hl' as [Hg | [Hq | []]];
        [ destruct (replace_origin _ _ _ _ _ _ Hwf Hl Hg) as [(-> & ->) | ->];
          [ assert (f = e) by congruence; subst f;
            exact (released_no_set _ _ _ _ _ _ Hok Hhc He Hch Hss Hd)
          | exact Hd ]
        | injection Hq as -> _; congruence ]
    end.
  - (* pstep_wait_reap *)
    match goal with
    | He : look ?Q (pe_pid ?e) = Some ?e,
      Hm : materialize_model_accesses _ _ = Some ?model'' |- _ =>
        cbn [pcfg_procs] in Hl'; apply In_drop_in in Hl';
        destruct (replace_origin _ _ _ _ _ _ Hwf Hl Hl') as [(-> & ->) | ->];
        [ assert (f = e) by congruence; subst f; cbn [pe_model];
          rewrite (sigchld_reap_entry _ _ _ _ _ Hm); exact Hd
        | exact Hd ]
    end.
  - (* pstep_wait_nohang_reap *)
    match goal with
    | He : look ?Q (pe_pid ?e) = Some ?e,
      Hm : materialize_model_accesses _ _ = Some ?model'' |- _ =>
        unfold wait4_reap_result in Hl'; cbn [pcfg_procs] in Hl'; apply In_drop_in in Hl';
        destruct (replace_origin _ _ _ _ _ _ Hwf Hl Hl') as [(-> & ->) | ->];
        [ assert (f = e) by congruence; subst f; cbn [pe_model];
          rewrite (sigchld_reap_entry _ _ _ _ _ Hm); exact Hd
        | exact Hd ]
    end.
  - (* pstep_wait_nohang_zero *)
    match goal with
    | He : look ?Q (pe_pid ?e) = Some ?e |- _ =>
        unfold wait4_zero_result, absorb in Hl'; cbn [pcfg_procs] in Hl';
        destruct (In_orphan_at_exit _ _ _ _ _ Hl') as (g & Hg & Hm);
        rewrite Hm;
        destruct (replace_origin_bit _ _ _ _ _ _ _ Hwf Hl Hg
                    (fun g1 Hg1 => In_first_root_pin _ _ _ _ _ _ Hg1)) as [(-> & ->) | Hbit];
        [ assert (f = e) by congruence; subst f; exact Hd | rewrite Hbit; exact Hd ]
    end.
  - (* pstep_sync *)
    match goal with
    | He : look ?Q (pe_pid ?e) = Some ?e |- _ =>
        unfold sync_result in Hl'; cbn [pcfg_procs] in Hl';
        destruct (replace_origin _ _ _ _ _ _ Hwf Hl Hl') as [(-> & ->) | ->];
        [ assert (f = e) by congruence; subst f;
          rewrite sigchld_sync_entry; exact Hd
        | exact Hd ]
    end.
  - (* pstep_pin_root: the table it replaces into is [pcfg_procs P], or
       that table after the first pin resolved the root's children *)
    match goal with
    | Hr : look ?Q (pcfg_root ?Q) = Some ?r |- _ =>
        unfold pin_root in Hl'; cbn [pcfg_procs] in Hl'; revert Hl';
        match goal with
        | |- List.In _ (replace_in (match ?x with _ => _ end) _ _) -> _ =>
            destruct x; intros Hl'
        end;
        first
        [ destruct (replace_origin _ _ _ _ _ _ Hwf Hl Hl') as [(-> & ->) | ->];
          [ assert (f = r) by congruence; subst f; exact Hd | exact Hd ]
        | destruct (replace_origin_bit _ _ _ _ _ _ _ Hwf Hl Hl'
                      (fun g1 Hg1 => In_root_children _ _ _ _ _ Hg1)) as [(-> & ->) | Hbit];
          [ assert (f = r) by congruence; subst f; exact Hd | rewrite Hbit; exact Hd ] ]
    end.
Qed.

Corollary pstep_cfg_sigchld_no_set_with_child : forall segs cfg P evs P' k f f',
  pconfig_wf P -> child_pids_ok P -> hc_all P ->
  pstep_cfg segs cfg P evs (PNext P') ->
  look P k = Some f -> look P' k = Some f' ->
  has_child_b P k = true ->
  m_sigchld_dfl (pe_model f) = false ->
  m_sigchld_dfl (pe_model f') = false.
Proof.
  intros segs cfg P evs P' k f f' Hwf Hok Hhc (p & Hs).
  exact (pstep_at_sigchld_no_set_with_child _ _ _ _ _ _ _ _ _ Hwf Hok Hhc Hs).
Qed.

(** The extended relation, wherever it agrees with the core's. *)
Corollary pstep_x_at_sigchld_no_set_with_child : forall ext cenv segs cfg p P evs P' k f f',
  ext_agrees ext cenv segs P ->
  pconfig_wf P -> child_pids_ok P -> hc_all P ->
  pstep_x_at ext cenv segs cfg p P evs (PNext P') ->
  look P k = Some f -> look P' k = Some f' ->
  has_child_b P k = true ->
  m_sigchld_dfl (pe_model f) = false ->
  m_sigchld_dfl (pe_model f') = false.
Proof.
  intros ext cenv segs cfg p P evs P' k f f' Hag Hwf Hok Hhc Hs.
  apply (pstep_at_sigchld_no_set_with_child segs cfg p P evs P' k f f' Hwf Hok Hhc).
  exact (proj1 (pstep_x_at_agree_iff ext cenv segs cfg p P evs (PNext P') Hag) Hs).
Qed.

(** From any launch, with no premise left: every step of every run keeps
    the rule.  (The launch's list of children is empty by construction,
    so this needs no fact about the launch input.) *)
Theorem sigchld_rule_reachable : forall segs pc ph sp brk0 mbase rnd lim inp
    segs' cfg P evs P' k f f',
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P ->
  pstep_cfg segs' cfg P evs (PNext P') ->
  look P k = Some f -> look P' k = Some f' ->
  has_child_b P k = true ->
  m_sigchld_dfl (pe_model f) = false ->
  m_sigchld_dfl (pe_model f') = false.
Proof.
  intros segs pc ph sp brk0 mbase rnd lim inp segs' cfg P evs P' k f f' Hr.
  destruct (sigchld_rule_invariants segs' cfg
              (init_config segs pc ph sp brk0 mbase rnd lim inp) P eq_refl Hr)
    as (Hwf & Hok & Hhc).
  exact (pstep_cfg_sigchld_no_set_with_child _ _ _ _ _ _ _ _ Hwf Hok Hhc).
Qed.

Print Assumptions sigchld_rule_reachable.
