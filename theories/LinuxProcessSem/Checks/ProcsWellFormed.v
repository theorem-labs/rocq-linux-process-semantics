(** * LinuxProcessSem.Checks.ProcsWellFormed — every step keeps the table well formed

    Not part of the trusted specification: this file is QA on the
    definitions, in the sense of [Checks.Examples]'s header, and it earns
    its place under that file's FIRST reason: the statement is UNIVERSALLY
    QUANTIFIED over configurations and steps.

    ** What this pins

    [Procs.pconfig_wf] is the structural invariant of the process table:
    keys are pids, the root is present and parentless, every parent link
    resolves to another entry, no key repeats, and every parent is running.
    [pstep_at_preserves_wf] says every producing arm of [Procs.pstep_at]
    keeps it, and with [Procs.pconfig_wf_one_proc] that makes it hold at
    every configuration a run reaches from a released [execve].

    Two of its clauses are what the reap arms silently relied on.  Clause
    5 (parents run) is why a reap never drops an entry another entry still
    names as parent: an entry stops running only at its exit, where
    [Procs.absorb] orphans its children.  Clause 4 (keys unique) is why
    [look], [replace_in] and [drop_in], which act on the FIRST entry with a
    key, see every entry there is.

    ** The one fact from outside the table

    The clone arm hands its child the parent's SUCCESSOR as parent, so the
    successor must run.  The released step for 220 and 435 never halts the
    caller: [clone_spec_keeps_halted] reads it off the executable checker,
    whose answers are the model unchanged or [State.with_child] of it. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel Require Import Fork.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   Pids
   ========================================================================= *)

Lemma pid_eqb_false : forall a b : Pid, bv_eqb a b = false -> a <> b.
Proof. intros a b H ->. rewrite bv_eqb_same in H. discriminate H. Qed.

Lemma pid_neq_eqb : forall a b : Pid, a <> b -> bv_eqb a b = false.
Proof.
  intros a b H. destruct (bv_eqb a b) eqn:E; [|reflexivity].
  apply bv_eqb_true_eq in E. contradiction.
Qed.

(* =========================================================================
   The table operations, read as membership
   ========================================================================= *)

Lemma look_in_In : forall ps p e, look_in ps p = Some e -> List.In (p, e) ps.
Proof.
  induction ps as [|[k x] r IH]; intros p e H; cbn [look_in fst snd] in H;
    [discriminate H|].
  destruct (bv_eqb k p) eqn:E.
  - injection H as <-. apply bv_eqb_true_eq in E. subst k. left. reflexivity.
  - right. apply IH. exact H.
Qed.

Lemma In_look_in : forall ps p e,
  List.NoDup (List.map fst ps) -> List.In (p, e) ps -> look_in ps p = Some e.
Proof.
  induction ps as [|[k x] r IH]; intros p e Hnd Hin; [destruct Hin|].
  cbn [List.map fst] in Hnd. inversion Hnd as [|? ? Hnot Hnd']; subst.
  cbn [look_in fst snd].
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. rewrite bv_eqb_same. reflexivity.
  - destruct (bv_eqb k p) eqn:E.
    + apply bv_eqb_true_eq in E. subst k. exfalso. apply Hnot.
      exact (List.in_map fst r (p, e) Hin).
    + apply IH; assumption.
Qed.

Lemma look_in_None_notin : forall ps q, look_in ps q = None -> ~ List.In q (List.map fst ps).
Proof.
  induction ps as [|[k x] r IH]; intros q H Hin; [destruct Hin|].
  cbn [look_in fst snd] in H. cbn [List.map fst] in Hin.
  destruct (bv_eqb k q) eqn:E; [discriminate H|].
  destruct Hin as [->|Hin];
    [rewrite bv_eqb_same in E; discriminate E | exact (IH q H Hin)].
Qed.

Lemma In_keys : forall (ps : list (Pid * ProcessEntry)) p e,
  List.In (p, e) ps -> List.In p (List.map fst ps).
Proof. intros ps p e H. exact (List.in_map fst ps (p, e) H). Qed.

Lemma In_unique : forall (ps : list (Pid * ProcessEntry)) p e1 e2,
  List.NoDup (List.map fst ps) -> List.In (p, e1) ps -> List.In (p, e2) ps -> e1 = e2.
Proof.
  intros ps p e1 e2 Hnd H1 H2.
  pose proof (In_look_in ps p e1 Hnd H1) as L1.
  pose proof (In_look_in ps p e2 Hnd H2) as L2.
  congruence.
Qed.

Lemma replace_in_keys : forall ps p e',
  List.map fst (replace_in ps p e') = List.map fst ps.
Proof.
  induction ps as [|[k x] r IH]; intros p e'; [reflexivity|].
  cbn [replace_in fst]. destruct (bv_eqb k p) eqn:E; cbn [List.map fst].
  - apply bv_eqb_true_eq in E. subst k. reflexivity.
  - f_equal. apply IH.
Qed.

Lemma replace_in_In_inv : forall ps p e' kv,
  List.NoDup (List.map fst ps) -> List.In kv (replace_in ps p e') ->
  kv = (p, e') \/ (List.In kv ps /\ fst kv <> p).
Proof.
  induction ps as [|[k x] r IH]; intros p e' kv Hnd Hin; [destruct Hin|].
  cbn [List.map fst] in Hnd. inversion Hnd as [|? ? Hnot Hnd']; subst.
  cbn [replace_in fst] in Hin. destruct (bv_eqb k p) eqn:E.
  - apply bv_eqb_true_eq in E. subst k.
    destruct Hin as [<-|Hin]; [left; reflexivity|].
    right. split; [right; exact Hin|]. intros Hk. apply Hnot.
    rewrite <- Hk. exact (List.in_map fst r kv Hin).
  - destruct Hin as [<-|Hin].
    + right. split; [left; reflexivity|]. cbn [fst]. apply pid_eqb_false. exact E.
    + destruct (IH p e' kv Hnd' Hin) as [H|[H1 H2]];
        [left; exact H | right; split; [right; exact H1 | exact H2]].
Qed.

Lemma replace_in_In_new : forall ps p e',
  List.In p (List.map fst ps) -> List.In (p, e') (replace_in ps p e').
Proof.
  induction ps as [|[k x] r IH]; intros p e' Hin; [destruct Hin|].
  cbn [replace_in fst]. destruct (bv_eqb k p) eqn:E; [left; reflexivity|].
  right. apply IH. cbn [List.map fst] in Hin.
  destruct Hin as [->|Hin]; [rewrite bv_eqb_same in E; discriminate E | exact Hin].
Qed.

Lemma replace_in_In_old : forall ps p e' kv,
  List.In kv ps -> fst kv <> p -> List.In kv (replace_in ps p e').
Proof.
  induction ps as [|[k x] r IH]; intros p e' kv Hin Hne; [destruct Hin|].
  cbn [replace_in fst]. destruct (bv_eqb k p) eqn:E.
  - destruct Hin as [<-|Hin].
    + apply bv_eqb_true_eq in E. cbn [fst] in Hne. contradiction.
    + right. exact Hin.
  - destruct Hin as [<-|Hin]; [left; reflexivity | right; apply IH; assumption].
Qed.

Lemma drop_in_sub : forall ps q kv, List.In kv (drop_in ps q) -> List.In kv ps.
Proof.
  induction ps as [|[k x] r IH]; intros q kv Hin; [destruct Hin|].
  cbn [drop_in fst] in Hin. destruct (bv_eqb k q).
  - right. exact Hin.
  - destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH q kv Hin)].
Qed.

Lemma drop_in_keep : forall ps q kv,
  List.In kv ps -> fst kv <> q -> List.In kv (drop_in ps q).
Proof.
  induction ps as [|[k x] r IH]; intros q kv Hin Hne; [destruct Hin|].
  cbn [drop_in fst]. destruct (bv_eqb k q) eqn:E.
  - destruct Hin as [<-|Hin].
    + apply bv_eqb_true_eq in E. cbn [fst] in Hne. contradiction.
    + exact Hin.
  - destruct Hin as [<-|Hin]; [left; reflexivity | right; apply IH; assumption].
Qed.

Lemma drop_in_NoDup : forall ps q,
  List.NoDup (List.map fst ps) -> List.NoDup (List.map fst (drop_in ps q)).
Proof.
  induction ps as [|[k x] r IH]; intros q Hnd; [constructor|].
  cbn [List.map fst] in Hnd. inversion Hnd as [|? ? Hnot Hnd']; subst.
  cbn [drop_in fst]. destruct (bv_eqb k q); [exact Hnd'|].
  cbn [List.map fst]. constructor; [|exact (IH q Hnd')].
  intros Hin. apply Hnot. apply List.in_map_iff in Hin as (kv & Hk & Hkv).
  rewrite <- Hk. exact (List.in_map fst r kv (drop_in_sub r q kv Hkv)).
Qed.

Lemma NoDup_snoc : forall (A : Type) (l : list A) x,
  List.NoDup l -> ~ List.In x l -> List.NoDup (l ++ [x]).
Proof.
  induction l as [|a l IH]; intros x Hnd Hx; cbn [app].
  - constructor; [intros []|constructor].
  - inversion Hnd as [|? ? Hnot Hnd']; subst. constructor.
    + intros Hin. apply List.in_app_or in Hin as [H|[H|[]]];
        [contradiction | subst; apply Hx; left; reflexivity].
    + apply IH; [exact Hnd'|]. intros H. apply Hx. right. exact H.
Qed.

(* =========================================================================
   The orphaning, slot by slot
   ========================================================================= *)

Definition orphan_slot (m : Model) (p : Pid) (kv : Pid * ProcessEntry)
    : Pid * ProcessEntry :=
  match m_halted m with
  | Some _ => orphan_one p kv
  | None => kv
  end.

Lemma orphan_at_exit_map : forall m p ps,
  orphan_at_exit m p ps = List.map (orphan_slot m p) ps.
Proof.
  intros m p ps. unfold orphan_at_exit, orphan_slot, orphan_children.
  destruct (m_halted m); [reflexivity|].
  induction ps as [|kv r IH]; [reflexivity|]. cbn [List.map]. f_equal. exact IH.
Qed.

Lemma orphan_slot_fst : forall m p kv, fst (orphan_slot m p kv) = fst kv.
Proof.
  intros m p kv. unfold orphan_slot, orphan_one.
  destruct (m_halted m); [|reflexivity].
  match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma orphan_slot_model : forall m p kv,
  pe_model (snd (orphan_slot m p kv)) = pe_model (snd kv).
Proof.
  intros m p kv. unfold orphan_slot, orphan_one.
  destruct (m_halted m); [|reflexivity].
  match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma orphan_slot_pid : forall m p kv,
  pe_pid (snd (orphan_slot m p kv)) = pe_pid (snd kv).
Proof.
  intros m p kv. unfold orphan_slot, orphan_one.
  destruct (m_halted m); [|reflexivity].
  match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(** A slot is orphaned exactly when the exiting entry's model is over, the
    slot is not the exiting entry, and the slot names it as parent. *)
Lemma orphan_slot_cases : forall m p kv,
  orphan_slot m p kv = kv
  \/ (m_halted m <> None /\ fst kv <> p /\ pe_parent (snd kv) = Some p
      /\ pe_parent (snd (orphan_slot m p kv)) = None).
Proof.
  intros m p kv. unfold orphan_slot.
  destruct (m_halted m) as [c|] eqn:Hm; [|left; reflexivity].
  unfold orphan_one.
  destruct (bv_eqb (fst kv) p) eqn:E1; cbn [negb andb]; [left; reflexivity|].
  destruct (pe_parent (snd kv)) as [q|] eqn:E2; [|left; reflexivity].
  destruct (bv_eqb q p) eqn:E3; [|left; reflexivity].
  right. apply bv_eqb_true_eq in E3. subst q.
  split; [discriminate|]. split; [apply pid_eqb_false; exact E1|].
  split; reflexivity.
Qed.

Lemma orphan_slot_keep : forall m p kv,
  ~ (m_halted m <> None /\ fst kv <> p /\ pe_parent (snd kv) = Some p) ->
  orphan_slot m p kv = kv.
Proof.
  intros m p kv Hn.
  destruct (orphan_slot_cases m p kv) as [H|(H1 & H2 & H3 & _)]; [exact H|].
  exfalso. apply Hn. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma In_orphan_slot : forall m p ps q f,
  List.In (q, f) ps ->
  List.In (q, snd (orphan_slot m p (q, f))) (List.map (orphan_slot m p) ps).
Proof.
  intros m p ps q f H.
  pose proof (List.in_map (orphan_slot m p) ps (q, f) H) as H'.
  rewrite (surjective_pairing (orphan_slot m p (q, f))) in H'.
  rewrite orphan_slot_fst in H'. exact H'.
Qed.

(* =========================================================================
   The invariant on a list, and its equivalence with [pconfig_wf]
   ========================================================================= *)

Definition tbl_wf (ps : list (Pid * ProcessEntry)) : Prop :=
  (forall kv, List.In kv ps -> fst kv = pe_pid (snd kv))
  /\ (forall kv q, List.In kv ps -> pe_parent (snd kv) = Some q ->
        q <> fst kv /\ exists f, List.In (q, f) ps /\ m_halted (pe_model f) = None)
  /\ List.NoDup (List.map fst ps).

Definition root_ok (ps : list (Pid * ProcessEntry)) (r : Pid) : Prop :=
  exists e, List.In (r, e) ps /\ pe_parent e = None.

Lemma wf_iff : forall P,
  pconfig_wf P <-> tbl_wf (pcfg_procs P) /\ root_ok (pcfg_procs P) (pcfg_root P).
Proof.
  intros P. unfold pconfig_wf, look. split.
  - intros (Hk & (er & Hr & Hrp) & Hln & Hnd & Hlv).
    split; [split; [exact Hk | split; [|exact Hnd]]|].
    + intros kv q Hin Hq. destruct (Hln kv q Hin Hq) as (Hne & f & Hf).
      split; [exact Hne|]. exists f.
      split; [exact (look_in_In _ _ _ Hf) | exact (Hlv kv q f Hin Hq Hf)].
    + exists er. split; [exact (look_in_In _ _ _ Hr) | exact Hrp].
  - intros [(Hk & Hln & Hnd) (er & Hr & Hrp)].
    split; [exact Hk|].
    split; [exists er; split; [exact (In_look_in _ _ _ Hnd Hr) | exact Hrp]|].
    split; [|split; [exact Hnd|]].
    + intros kv q Hin Hq. destruct (Hln kv q Hin Hq) as (Hne & f & Hf & _).
      split; [exact Hne|]. exists f. exact (In_look_in _ _ _ Hnd Hf).
    + intros kv q f Hin Hq Hf. destruct (Hln kv q Hin Hq) as (_ & f' & Hf' & Hr').
      rewrite (In_unique _ _ _ _ Hnd (look_in_In _ _ _ Hf) Hf'). exact Hr'.
Qed.

(* =========================================================================
   The three table shapes a producing arm builds
   ========================================================================= *)

(** The root keeps its slot through a replacement that keeps the replaced
    entry's parent, through the orphaning, through an append, and through
    a drop at another key. *)
Lemma root_replace : forall ps p e e1 r,
  List.NoDup (List.map fst ps) -> List.In (p, e) ps -> pe_parent e1 = pe_parent e ->
  root_ok ps r -> root_ok (replace_in ps p e1) r.
Proof.
  intros ps p e e1 r Hnd He Hpar (er & Hr & Hrp).
  destruct (bv_eqb r p) eqn:E.
  - apply bv_eqb_true_eq in E. subst r.
    pose proof (In_unique _ _ _ _ Hnd He Hr) as <-.
    exists e1. split; [|rewrite Hpar; exact Hrp].
    apply replace_in_In_new. exact (In_keys _ _ _ He).
  - apply pid_eqb_false in E. exists er. split; [|exact Hrp].
    apply replace_in_In_old; [exact Hr | exact E].
Qed.

Lemma root_orphan : forall m p ps r,
  root_ok ps r -> root_ok (orphan_at_exit m p ps) r.
Proof.
  intros m p ps r (er & Hr & Hrp). rewrite orphan_at_exit_map.
  exists er. split; [|exact Hrp].
  assert (Hkeep : orphan_slot m p (r, er) = (r, er)).
  { apply orphan_slot_keep. intros (_ & _ & Hc). cbn [snd] in Hc.
    rewrite Hrp in Hc. discriminate Hc. }
  rewrite <- Hkeep. apply List.in_map. exact Hr.
Qed.

Lemma root_app : forall ps ps' r, root_ok ps r -> root_ok (ps ++ ps') r.
Proof.
  intros ps ps' r (er & Hr & Hrp). exists er.
  split; [apply List.in_or_app; left; exact Hr | exact Hrp].
Qed.

Lemma root_drop : forall ps q r, r <> q -> root_ok ps r -> root_ok (drop_in ps q) r.
Proof.
  intros ps q r Hne (er & Hr & Hrp). exists er.
  split; [apply drop_in_keep; [exact Hr | exact Hne] | exact Hrp].
Qed.

(** THE ABSORB SHAPE: the stepping entry replaced, and, when its model is
    over, its children orphaned. *)
Lemma tbl_absorb : forall ps p e e1 m,
  tbl_wf ps -> List.In (p, e) ps ->
  pe_pid e1 = p -> pe_parent e1 = pe_parent e -> m_halted (pe_model e1) = m_halted m ->
  tbl_wf (orphan_at_exit m p (replace_in ps p e1)).
Proof.
  intros ps p e e1 m (Hk & Hln & Hnd) He Hpid Hpar Hhalt.
  rewrite orphan_at_exit_map.
  assert (Hnd1 : List.NoDup (List.map fst (replace_in ps p e1)))
    by (rewrite replace_in_keys; exact Hnd).
  assert (Hat_p : List.In (p, e1) (List.map (orphan_slot m p) (replace_in ps p e1))).
  { assert (Hkeep : orphan_slot m p (p, e1) = (p, e1)).
    { apply orphan_slot_keep. intros (_ & Hc & _). apply Hc. reflexivity. }
    rewrite <- Hkeep. apply List.in_map. apply replace_in_In_new.
    exact (In_keys _ _ _ He). }
  split; [|split].
  - intros kv Hin. apply List.in_map_iff in Hin as (kv0 & <- & Hin0).
    rewrite orphan_slot_fst, orphan_slot_pid.
    destruct (replace_in_In_inv ps p e1 kv0 Hnd Hin0) as [->|[Hin1 _]];
      [cbn [fst snd]; symmetry; exact Hpid | exact (Hk kv0 Hin1)].
  - intros kv q Hin Hq. apply List.in_map_iff in Hin as (kv0 & <- & Hin0).
    rewrite orphan_slot_fst.
    destruct (orphan_slot_cases m p kv0) as [Hs|(_ & _ & _ & Hnone)];
      [|rewrite Hnone in Hq; discriminate Hq].
    rewrite Hs in Hq.
    destruct (replace_in_In_inv ps p e1 kv0 Hnd Hin0) as [->|[Hin1 Hne1]].
    + (* the stepping entry itself: its parent is the old one's *)
      cbn [fst snd] in Hq |- *. rewrite Hpar in Hq.
      destruct (Hln (p, e) q He Hq) as (Hqp & f & Hf & Hfr). cbn [fst] in Hqp.
      split; [exact Hqp|].
      exists (snd (orphan_slot m p (q, f))). split.
      * apply In_orphan_slot. apply replace_in_In_old; [exact Hf | exact Hqp].
      * rewrite orphan_slot_model. exact Hfr.
    + (* another entry, which the orphaning kept *)
      destruct (Hln kv0 q Hin1 Hq) as (Hqk & f & Hf & Hfr).
      split; [exact Hqk|].
      destruct (bv_eqb q p) eqn:Eqp.
      * apply bv_eqb_true_eq in Eqp. subst q.
        exists e1. split; [exact Hat_p|]. rewrite Hhalt.
        destruct (m_halted m) as [c|] eqn:Hm; [|reflexivity].
        exfalso.
        destruct (orphan_slot_cases m p kv0) as [_|(_ & _ & _ & Hnone)].
        -- (* kept, yet a child of the exiting entry under a halted model *)
           assert (Hcase : orphan_slot m p kv0 <> kv0).
           { unfold orphan_slot. rewrite Hm. unfold orphan_one.
             rewrite (pid_neq_eqb _ _ Hne1), Hq, bv_eqb_same. cbn [negb andb].
             intros Heq. apply (f_equal (fun kv => pe_parent (snd kv))) in Heq.
             cbn [snd with_parent pe_parent] in Heq. rewrite Hq in Heq. discriminate Heq. }
           exact (Hcase Hs).
        -- rewrite Hs, Hq in Hnone. discriminate Hnone.
      * apply pid_eqb_false in Eqp.
        exists (snd (orphan_slot m p (q, f))). split.
        -- apply In_orphan_slot. apply replace_in_In_old; [exact Hf | exact Eqp].
        -- rewrite orphan_slot_model. exact Hfr.
  - rewrite List.map_map.
    rewrite (List.map_ext _ fst (orphan_slot_fst m p)). exact Hnd1.
Qed.

(** THE CLONE SHAPE: the parent replaced by its running successor, and a
    fresh child appended under it. *)
Lemma tbl_clone : forall ps p e e1 q ch,
  tbl_wf ps -> List.In (p, e) ps ->
  pe_pid e1 = p -> pe_parent e1 = pe_parent e -> m_halted (pe_model e1) = None ->
  ~ List.In q (List.map fst ps) -> pe_pid ch = q -> pe_parent ch = Some p ->
  tbl_wf (replace_in ps p e1 ++ [(q, ch)]).
Proof.
  intros ps p e e1 q ch (Hk & Hln & Hnd) He Hpid Hpar Hrun Hfresh Hcq Hcp.
  assert (Hpq : q <> p) by (intros ->; exact (Hfresh (In_keys _ _ _ He))).
  assert (Hat_p : List.In (p, e1) (replace_in ps p e1 ++ [(q, ch)])).
  { apply List.in_or_app. left. apply replace_in_In_new. exact (In_keys _ _ _ He). }
  assert (Hold : forall r f, List.In (r, f) ps -> r <> p ->
            List.In (r, f) (replace_in ps p e1 ++ [(q, ch)])).
  { intros r f Hf Hr. apply List.in_or_app. left. apply replace_in_In_old; assumption. }
  split; [|split].
  - intros kv Hin. apply List.in_app_or in Hin as [Hin|[<-|[]]].
    + destruct (replace_in_In_inv ps p e1 kv Hnd Hin) as [->|[Hin1 _]];
        [cbn [fst snd]; symmetry; exact Hpid | exact (Hk kv Hin1)].
    + cbn [fst snd]. symmetry. exact Hcq.
  - intros kv r Hin Hr. apply List.in_app_or in Hin as [Hin|[<-|[]]].
    + destruct (replace_in_In_inv ps p e1 kv Hnd Hin) as [->|[Hin1 Hne1]].
      * cbn [fst snd] in Hr |- *. rewrite Hpar in Hr.
        destruct (Hln (p, e) r He Hr) as (Hrp & f & Hf & Hfr). cbn [fst] in Hrp.
        split; [exact Hrp|]. exists f. split; [exact (Hold r f Hf Hrp) | exact Hfr].
      * destruct (Hln kv r Hin1 Hr) as (Hrk & f & Hf & Hfr).
        split; [exact Hrk|].
        destruct (bv_eqb r p) eqn:Erp.
        -- apply bv_eqb_true_eq in Erp. subst r.
           exists e1. split; [exact Hat_p | exact Hrun].
        -- apply pid_eqb_false in Erp.
           exists f. split; [exact (Hold r f Hf Erp) | exact Hfr].
    + cbn [fst snd] in Hr |- *. rewrite Hcp in Hr. injection Hr as <-.
      split; [intros Hc; apply Hpq; symmetry; exact Hc|].
      exists e1. split; [exact Hat_p | exact Hrun].
  - rewrite List.map_app, replace_in_keys. cbn [List.map fst].
    apply NoDup_snoc; [exact Hnd | exact Hfresh].
Qed.

(** THE REAP SHAPE: the caller replaced by its running successor, and the
    zombie child dropped.  Nobody names the zombie as parent, because every
    parent runs. *)
Lemma tbl_reap : forall ps p e e1 q ez,
  tbl_wf ps -> List.In (p, e) ps -> List.In (q, ez) ps ->
  pe_pid e1 = p -> pe_parent e1 = pe_parent e -> m_halted (pe_model e1) = None ->
  q <> p -> m_halted (pe_model ez) <> None ->
  tbl_wf (drop_in (replace_in ps p e1) q).
Proof.
  intros ps p e e1 q ez (Hk & Hln & Hnd) He Hez Hpid Hpar Hrun Hqp Hzz.
  assert (Hnd1 : List.NoDup (List.map fst (replace_in ps p e1)))
    by (rewrite replace_in_keys; exact Hnd).
  (* a running entry is not at the zombie's key *)
  assert (Hnotq : forall r f, List.In (r, f) ps -> m_halted (pe_model f) = None -> r <> q).
  { intros r f Hf Hfr ->. rewrite (In_unique _ _ _ _ Hnd Hf Hez) in Hfr.
    exact (Hzz Hfr). }
  assert (Hkeep : forall r f, List.In (r, f) ps -> m_halted (pe_model f) = None -> r <> p ->
            List.In (r, f) (drop_in (replace_in ps p e1) q)).
  { intros r f Hf Hfr Hrp. apply drop_in_keep; [|exact (Hnotq r f Hf Hfr)].
    apply replace_in_In_old; assumption. }
  assert (Hat_p : List.In (p, e1) (drop_in (replace_in ps p e1) q)).
  { apply drop_in_keep; [|intros Hc; apply Hqp; symmetry; exact Hc].
    apply replace_in_In_new. exact (In_keys _ _ _ He). }
  split; [|split].
  - intros kv Hin. apply drop_in_sub in Hin.
    destruct (replace_in_In_inv ps p e1 kv Hnd Hin) as [->|[Hin1 _]];
      [cbn [fst snd]; symmetry; exact Hpid | exact (Hk kv Hin1)].
  - intros kv r Hin Hr. apply drop_in_sub in Hin.
    destruct (replace_in_In_inv ps p e1 kv Hnd Hin) as [->|[Hin1 Hne1]].
    + cbn [fst snd] in Hr |- *. rewrite Hpar in Hr.
      destruct (Hln (p, e) r He Hr) as (Hrp & f & Hf & Hfr). cbn [fst] in Hrp.
      split; [exact Hrp|]. exists f. split; [exact (Hkeep r f Hf Hfr Hrp) | exact Hfr].
    + destruct (Hln kv r Hin1 Hr) as (Hrk & f & Hf & Hfr).
      split; [exact Hrk|].
      destruct (bv_eqb r p) eqn:Erp.
      * apply bv_eqb_true_eq in Erp. subst r.
        exists e1. split; [exact Hat_p | exact Hrun].
      * apply pid_eqb_false in Erp.
        exists f. split; [exact (Hkeep r f Hf Hfr Erp) | exact Hfr].
  - apply drop_in_NoDup. exact Hnd1.
Qed.

(* =========================================================================
   The released clone never halts its caller
   ========================================================================= *)

(** Case on the first BOOLEAN test in [H].  The type check matters: Ltac's
    [if] pattern also matches a match on any two-constructor type, such as
    a list. *)
Local Ltac dif H :=
  match type of H with
  | context [if ?b then _ else _] =>
      match type of b with
      | bool => destruct b; cbv beta iota in H
      end
  end.

Lemma check_clone_answer_halted : forall ret m m' evs,
  check_clone_answer ret m = CheckOk m' evs -> m_halted m' = m_halted m.
Proof.
  intros ret m m' evs H. unfold check_clone_answer in H.
  repeat dif H; first [discriminate H | injection H as <- _; reflexivity].
Qed.

Lemma check_clone_ns_answer_halted : forall ret m m' evs,
  check_clone_ns_answer ret m = CheckOk m' evs -> m_halted m' = m_halted m.
Proof.
  intros ret m m' evs H. unfold check_clone_ns_answer in H.
  repeat dif H; first [discriminate H | injection H as <- _; reflexivity].
Qed.

Lemma check_clone_einval_halted : forall eff m m' evs,
  check_clone_einval eff m = CheckOk m' evs -> m_halted m' = m_halted m.
Proof.
  intros eff m m' evs H. unfold check_clone_einval in H.
  destruct (clone_no_shared_file_b (forfeit_inherited (m_fds m)));
    cbv iota in H; [|discriminate H].
  apply check_ret_only_ok_iff in H as (_ & -> & _). reflexivity.
Qed.

Lemma check_clone3_einval_halted : forall uargs eff m m' evs,
  check_clone3_einval uargs eff m = CheckOk m' evs -> m_halted m' = m_halted m.
Proof.
  intros uargs eff m m' evs H. unfold check_clone3_einval in H.
  apply check_ret_only_copyins_ok_iff in H as (_ & -> & _). reflexivity.
Qed.

Lemma check_clone_resolve_halted : forall eff m m' evs,
  check_clone_resolve eff m = CheckOk m' evs -> m_halted m' = m_halted m.
Proof.
  intros [ret ws zs us cs ins] m m' evs H. unfold check_clone_resolve in H.
  destruct ws as [|? ?], zs as [|? ?], us as [|? ?], cs as [|? ?], ins as [|? ?];
    cbv beta iota in H; repeat dif H; try discriminate H.
  exact (check_clone_answer_halted _ _ _ _ H).
Qed.

Lemma check_clone_ns_resolve_halted : forall eff m m' evs,
  check_clone_ns_resolve eff m = CheckOk m' evs -> m_halted m' = m_halted m.
Proof.
  intros [ret ws zs us cs ins] m m' evs H. unfold check_clone_ns_resolve in H.
  destruct ws as [|? ?], zs as [|? ?], us as [|? ?], cs as [|? ?], ins as [|? ?];
    cbv beta iota in H; repeat dif H; try discriminate H.
  exact (check_clone_ns_answer_halted _ _ _ _ H).
Qed.

Lemma check_clone_ns_refused_halted : forall eff m m' evs,
  check_clone_ns_refused eff m = CheckOk m' evs -> m_halted m' = m_halted m.
Proof.
  intros [ret ws zs us cs ins] m m' evs H. unfold check_clone_ns_refused in H.
  destruct ws as [|? ?], zs as [|? ?], us as [|? ?], cs as [|? ?], ins as [|? ?];
    cbv beta iota in H; repeat dif H; try discriminate H.
  injection H as <- _. reflexivity.
Qed.

Lemma check_clone3_resolve_halted : forall uargs eff m m' evs,
  check_clone3_resolve uargs eff m = CheckOk m' evs -> m_halted m' = m_halted m.
Proof.
  intros uargs [ret ws zs us cs ins] m m' evs H. unfold check_clone3_resolve in H.
  destruct ws as [|? ?], zs as [|? ?], us as [|? ?], cs as [|? ?];
    cbv beta iota in H; repeat dif H; try discriminate H.
  exact (check_clone_answer_halted _ _ _ _ H).
Qed.

(** Every answer the released spec gives [clone] (220) and [clone3] (435)
    leaves the caller's halt flag as it was: the model comes back
    unchanged, or with the child recorded ([State.with_child]). *)
Lemma clone_spec_keeps_halted : forall i m eff m' evs,
  (bv_unsigned (in_sysno i) = 220%Z \/ bv_unsigned (in_sysno i) = 435%Z) ->
  syscall_spec i m (Ok eff m' evs) -> m_halted m' = m_halted m.
Proof.
  intros i m eff m' evs Hno H. apply check_syscall_complete_ok in H.
  destruct Hno as [Hno|Hno].
  - rewrite (check_syscall_clone i _ m Hno) in H.
    destruct (check_clone_ok_inv _ _ _ _ _ _ H) as [(e & He & _)|[(e & He & _)|[He|He]]].
    + exact (check_clone_resolve_halted _ _ _ _ He).
    + exact (check_clone_ns_resolve_halted _ _ _ _ He).
    + exact (check_clone_einval_halted _ _ _ _ He).
    + exact (check_clone_ns_refused_halted _ _ _ _ He).
  - rewrite (check_syscall_clone3 i _ m Hno) in H.
    destruct (check_clone3_ok_inv _ _ _ _ _ _ _ H)
      as [(reads & He)|[(reads & en & _ & He)|(e & He & _)]].
    + exact (check_clone3_resolve_halted _ _ _ _ _ He).
    + apply check_ret_only_copyins_ok_iff in He as (_ & -> & _). reflexivity.
    + exact (check_clone_resolve_halted _ _ _ _ He).
Qed.

(** So a released step that is a successful clone leaves its caller
    running: the instruction and vDSO arms have no pending call, the
    syscall arm keeps the halt flag through the materialization, and the
    two arms that end a process would need the clone spec to halt its
    caller, which it never does. *)
Lemma clone_step_running : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  clone_success_b c c' = true ->
  m_halted (cfg_model c') = None.
Proof.
  intros segs cfg c evs c' Hss Hcs.
  pose proof (clone_success_pending c c' Hcs) as Hcp.
  unfold clone_pending_b in Hcp.
  inversion Hss as
    [ ms model ms' model' Hh Hsv Hacc
    | |
    | ms model fn n eff model' model'' evs0 Hh Hsv Hacc Hfn Hn Hsp Hne Hh' Hmat
    | |
    | ms model x8 eff model' model'' evs0 Hh Hsv Hsp Hrf Hh' Hmat
    |
    | ms model x8 eff model' evs0 code Hh Hsv Hsp Hh' Hk'
    | ms model x8 eff model' evs0 sig Hh Hsv Hsp Hk'
    | ]; subst; cbn [cfg_model cfg_ms] in *.
  - (* an instruction: nothing is pending *)
    rewrite Hsv in Hcp. discriminate Hcp.
  - (* a vDSO call: nothing is pending either *)
    rewrite Hsv in Hcp. discriminate Hcp.
  - (* a syscall: the materialization keeps the process record *)
    destruct (materialize_model_accesses_frame _ _ _ Hmat)
      as (_ & _ & _ & _ & _ & Hproc & _).
    unfold m_halted in *. rewrite Hproc. exact Hh'.
  - (* an exit: the clone spec would have halted its caller *)
    exfalso.
    rewrite Hsv in Hcp. cbv beta iota in Hcp. unfold clone_sysno in Hcp.
    assert (Hn : bv_unsigned x8 = 220%Z \/ bv_unsigned x8 = 435%Z)
      by (apply orb_true_iff in Hcp as [Hc|Hc]; apply Z.eqb_eq in Hc;
          [left | right]; exact Hc).
    pose proof (clone_spec_keeps_halted (sys_input segs ms x8) _ _ _ _ Hn Hsp) as Hk.
    rewrite Hh', Hh in Hk. discriminate Hk.
  - (* a death by signal: likewise, since a killed model is halted *)
    exfalso.
    rewrite Hsv in Hcp. cbv beta iota in Hcp. unfold clone_sysno in Hcp.
    assert (Hn : bv_unsigned x8 = 220%Z \/ bv_unsigned x8 = 435%Z)
      by (apply orb_true_iff in Hcp as [Hc|Hc]; apply Z.eqb_eq in Hc;
          [left | right]; exact Hc).
    pose proof (clone_spec_keeps_halted (sys_input segs ms x8) _ _ _ _ Hn Hsp) as Hk.
    unfold m_killed in Hk'. unfold m_halted in Hk, Hh.
    destruct (procst_killed (m_proc model')); cbv beta iota in Hk';
      [|discriminate Hk'].
    rewrite Hk', Hh in Hk. discriminate Hk.
Qed.

(** A slot all four of whose bytes are backed has no byte unbacked. *)
Local Lemma all_none_backed : forall b bs,
  all_backed (b :: bs) = true -> none_backed (b :: bs) = false.
Proof. intros [x|] bs H; [reflexivity | discriminate H]. Qed.

(** The stores the released step admitted ([Kernel.Fork.clone_stores_ok])
    include the accounting of the child's store, when the child makes
    one. *)
Local Lemma stores_ok_accounted : forall i m r p,
  clone_stores_ok i m r = true -> clone_child_tid r = Some p ->
  access_okb p 4 && all_backed (tid_bytes (in_mem i) p) = true ->
  exists m', materialize_model_accesses m [(p, 4%nat)] = Some m'.
Proof.
  intros i m r p Hok Hp Hrd.
  unfold clone_stores_ok in Hok. apply andb_true_iff in Hok as [_ Hok].
  unfold child_tid_ok in Hok. rewrite Hp in Hok.
  apply andb_true_iff in Hok as [_ Hok].
  apply andb_true_iff in Hrd as [Hacc Hall].
  rewrite Hacc in Hok. cbn [negb orb] in Hok.
  destruct (tid_store_case (in_wmem i) p).
  - unfold tid_bytes in Hall, Hok. cbn [map] in Hall, Hok.
    rewrite (all_none_backed _ _ Hall) in Hok. discriminate Hok.
  - apply andb_true_iff in Hok as [_ Hok].
    destruct (materialize_model_accesses m [(p, 4%nat)]) as [m'|]; [|discriminate Hok].
    exists m'. reflexivity.
  - discriminate Hok.
Qed.

Local Lemma check_with_stores_ok_stores : forall i r inner eff m m' evs,
  check_with_stores i r inner eff m = CheckOk m' evs -> clone_stores_ok i m r = true.
Proof.
  intros i r inner eff m m' evs H. unfold check_with_stores in H.
  destruct (clone_stores_ok i m r); [reflexivity | discriminate H].
Qed.

(** THE CHILD'S STORE IS ACCOUNTED.  Whenever the released step answers a
    clone, the child's [CLONE_CHILD_SETTID] store ([Procs.child_tid_store])
    is empty or its accounting on the caller's model as the call began
    succeeds, because the released spec admits the word only when it does
    ([Kernel.Fork.child_tid_ok]).  So [Procs.child_model]'s [None] arm is
    not reached from a step of the core. *)
Lemma child_tid_store_accounted : forall segs cfg c evs c' c1,
  sstep_cfg segs cfg c evs (SNext c') ->
  clone_success_b c c' = true ->
  child_tid_store c c1 = []
  \/ exists m', materialize_model_accesses (cfg_model c)
                  (write_accesses (child_tid_store c c1)) = Some m'.
Proof.
  intros segs cfg c evs c' c1 Hss Hcs.
  pose proof (clone_success_pending c c' Hcs) as Hcp.
  unfold clone_pending_b in Hcp.
  assert (Hspec : exists x8 eff m' evs',
             ms_svc_pending (cfg_ms c) = Some x8
             /\ syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff m' evs')).
  { inversion Hss as
      [ ms model ms' model' Hh Hsv Hacc
      | |
      | ms model fn n eff model' model'' evs0 Hh Hsv Hacc Hfn Hn Hsp Hne Hh' Hmat
      | |
      | ms model x8 eff model' model'' evs0 Hh Hsv Hsp Hrf Hh' Hmat
      |
      | ms model x8 eff model' evs0 code Hh Hsv Hsp Hh' Hk'
      | ms model x8 eff model' evs0 sig Hh Hsv Hsp Hk'
      | ]; subst; cbn [cfg_model cfg_ms] in *.
    - rewrite Hsv in Hcp. discriminate Hcp.
    - rewrite Hsv in Hcp. discriminate Hcp.
    - do 4 eexists. split; eassumption.
    - do 4 eexists. split; eassumption.
    - do 4 eexists. split; eassumption. }
  destruct Hspec as (x8 & eff & m' & evs' & Hsv & Hsp).
  rewrite Hsv in Hcp. cbv beta iota in Hcp. unfold clone_sysno in Hcp.
  assert (Hn : bv_unsigned x8 = 220%Z \/ bv_unsigned x8 = 435%Z)
    by (apply orb_true_iff in Hcp as [Hc|Hc]; apply Z.eqb_eq in Hc; [left | right]; exact Hc).
  clear Hcp.
  apply check_syscall_complete_ok in Hsp.
  destruct c as [ms m]. cbn [cfg_ms cfg_model] in *.
  unfold child_tid_store, clone_args_of_cfg. cbn [cfg_ms]. cbv zeta.
  rewrite Hsv. cbv beta iota.
  destruct (Z.eqb (bv_unsigned x8) 220%Z) eqn:H220.
  - (* clone (220): the record of the registers *)
    apply Z.eqb_eq in H220.
    rewrite (check_syscall_clone (sys_input segs ms x8) _ _ H220) in Hsp.
    destruct (clone_args_of_clone (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
                (ms_gpr ms 4)) as [r|] eqn:Hr; [|left; reflexivity].
    destruct (clone_record_admitted r) eqn:Had; [|left; reflexivity].
    destruct (clone_child_tid r) as [p|] eqn:Hp; [|left; reflexivity].
    destruct (access_okb p 4 && all_backed (tid_bytes (ms_read_byte ms) p)) eqn:Hrd;
      [|left; reflexivity].
    right. unfold check_clone in Hsp.
    destruct (clone_fork_flags_b (in_arg (sys_input segs ms x8) 0)) eqn:Hf.
    { exfalso. unfold clone_fork_flags_b in Hf. apply bv_eqb_eq in Hf.
      change (ms_gpr ms 0 = Z_to_bv 64 SIGCHLD) in Hf.
      rewrite Hf in Hr. vm_compute in Hr. injection Hr as <-.
      vm_compute in Hp. discriminate Hp. }
    destruct (clone_ns_flags_b (in_arg (sys_input segs ms x8) 0)) eqn:Hns.
    { exfalso.
      unfold clone_args_of_clone in Hr.
      destruct (bv_unsigned (ms_gpr ms 0) <? 2 ^ 32)%Z; [|discriminate Hr].
      injection Hr as <-. unfold clone_child_tid, clone_has in Hp. cbn [cla_flags] in Hp.
      (* the bit is read off [Hp], so its name in this file's scope is irrelevant *)
      match type of Hp with
      | context [Z.land (Z.land ?a ?X) ?C] =>
          pose proof (clone_ns_flags_disjoint _ C Hns
                        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as Hd;
          change (Z.land a C = 0%Z) in Hd;
          replace (Z.land (Z.land a X) C) with 0%Z in Hp
            by (rewrite <- Z.land_assoc, (Z.land_comm X C), Z.land_assoc, Hd;
                symmetry; apply Z.land_0_l)
      end.
      discriminate Hp. }
    replace (clone_args_of_clone (in_arg (sys_input segs ms x8) 0)
               (in_arg (sys_input segs ms x8) 1) (in_arg (sys_input segs ms x8) 2)
               (in_arg (sys_input segs ms x8) 3) (in_arg (sys_input segs ms x8) 4))
      with (Some r) in Hsp by (rewrite <- Hr; reflexivity).
    unfold clone_record_admitted in Had.
    destruct (clone_arg_checks r); [discriminate Had|]. cbn [negb andb] in Had.
    destruct (clone_class r); try discriminate Had; cbv iota in Hsp.
    + exact (stores_ok_accounted _ _ _ _ (check_with_stores_ok_stores _ _ _ _ _ _ _ Hsp)
               Hp Hrd).
    + exact (stores_ok_accounted _ _ _ _ (check_with_stores_ok_stores _ _ _ _ _ _ _ Hsp)
               Hp Hrd).
  - (* clone3 (435): the record of the struct *)
    destruct Hn as [Hn|Hcp]; [rewrite Hn in H220; discriminate H220|].
    rewrite (check_syscall_clone3 (sys_input segs ms x8) _ _ Hcp) in Hsp.
    rewrite Hcp. cbn [Z.eqb Pos.eqb].
    destruct (clone3_copy (ms_read_byte ms) (ms_gpr ms 0) (bv_unsigned (ms_gpr ms 1)))
      as [reads en| |reads short bs] eqn:Hbs; try (left; reflexivity).
    destruct (clone3_pre_sz short bs) as [| |r] eqn:Hp3; try (left; reflexivity).
    destruct (clone_record_admitted r) eqn:Had; [|left; reflexivity].
    destruct (clone_child_tid r) as [p|] eqn:Hp; [|left; reflexivity].
    destruct (access_okb p 4 && all_backed (tid_bytes (ms_read_byte ms) p)) eqn:Hrd;
      [|left; reflexivity].
    right. unfold check_clone3 in Hsp.
    replace (clone3_copy (in_mem (sys_input segs ms x8)) (in_arg (sys_input segs ms x8) 0)
               (bv_unsigned (in_arg (sys_input segs ms x8) 1)))
      with (C3Struct reads short bs) in Hsp by (rewrite <- Hbs; reflexivity).
    cbv iota in Hsp. unfold check_clone3_on_struct in Hsp.
    destruct (clone3_fork_args_b bs) eqn:Ha.
    { exfalso. pose proof (clone3_pre_sz_flags short bs r Hp3) as Hfl.
      unfold clone3_fork_args_b, w_is0 in Ha.
      repeat (apply andb_true_iff in Ha as [Ha ?]).
      apply bv_eqb_eq in Ha. rewrite Ha in Hfl.
      unfold clone_child_tid, clone_has in Hp. rewrite Hfl in Hp.
      vm_compute in Hp. discriminate Hp. }
    unfold clone_record_admitted in Had.
    destruct (clone_arg_checks r) eqn:Hck; [discriminate Had|]. cbn [negb andb] in Had.
    destruct (clone3_einval_sz short bs) eqn:He.
    { unfold clone3_einval_sz in He. rewrite Hp3 in He. cbv iota in He.
      rewrite Hck in He. discriminate He. }
    cbv iota in Hsp. rewrite Hp3 in Hsp. cbv iota in Hsp.
    destruct (clone_class r); try discriminate Had; try discriminate Hsp.
    unfold check_clone3_stores in Hsp.
    apply check_copyins_after_ok_iff in Hsp as [_ Hsp].
    exact (stores_ok_accounted _ _ _ _ (check_with_stores_ok_stores _ _ _ _ _ _ _ Hsp) Hp Hrd).
Qed.

(** The clone words the gates admitted before [CLONE_SYSVSEM] and the tid
    bits: [clone]'s fork word and namespace words, and [clone3]'s fork
    image at the one size the arm answered then, [CLONE_ARGS_SIZE]. *)
Definition clone_word_admitted_before (c : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | Some x8 =>
      if Z.eqb (bv_unsigned x8) 220%Z then
        clone_fork_flags_b (ms_gpr (cfg_ms c) 0) || clone_ns_flags_b (ms_gpr (cfg_ms c) 0)
      else if Z.eqb (bv_unsigned x8) 435%Z then
        bv_eqb (ms_gpr (cfg_ms c) 1) (Z_to_bv 64 CLONE_ARGS_SIZE)
        && match copy_bytes_map (ms_read_byte (cfg_ms c)) (ms_gpr (cfg_ms c) 0)
                   CLONE_ARGS_SIZE with
           | Some bs => clone3_fork_args_b bs
           | None => false
           end
      else false
  | None => false
  end.

(** A namespace word is below 2^32: its bits outside the namespace mask
    are [SIGCHLD]'s. *)
Local Lemma ns_word_below : forall a,
  Z.land a (Z.lnot clone_ns_mask) = SIGCHLD -> (0 <= a)%Z -> (a < 2 ^ 32)%Z.
Proof.
  intros a Hns Ha.
  assert (He : a = Z.land a (Z.lor clone_ns_mask SIGCHLD)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec.
    destruct (Z.testbit clone_ns_mask n) eqn:HM.
    - rewrite orb_true_l, andb_true_r. reflexivity.
    - pose proof (f_equal (fun z => Z.testbit z n) Hns) as Ht. cbv beta in Ht.
      rewrite Z.land_spec, Z.lnot_spec, HM in Ht by exact Hn.
      cbn [negb] in Ht. rewrite andb_true_r in Ht.
      rewrite orb_false_l, <- Ht. destruct (Z.testbit a n); reflexivity. }
  rewrite He.
  replace (Z.lor clone_ns_mask SIGCHLD)
    with (Z.land (Z.lor clone_ns_mask SIGCHLD) (Z.ones 32)) by (vm_compute; reflexivity).
  rewrite Z.land_assoc, Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

(** A machine state given back the memory it already has, whatever its
    registers. *)
Local Lemma ms_with_mem_regs : forall ms ms',
  ms_mem ms' = ms_mem ms -> ms_with_mem ms' (ms_mem ms) = ms'.
Proof. intros ms ms' H. destruct ms'. simpl in H. subst. reflexivity. Qed.

Local Lemma ms_mem_set_reg : forall ms k v, ms_mem (set_reg ms k v) = ms_mem ms.
Proof. intros ms k v. unfold set_reg. destruct (bv_eqb k 0); reflexivity. Qed.

(** The four memory ledgers of an accepted fork, namespace or fork-image
    answer are empty. *)
Local Lemma resolve_no_memory : forall eff m m' evs,
  check_clone_resolve eff m = CheckOk m' evs \/ check_clone_ns_resolve eff m = CheckOk m' evs ->
  eff_writes eff = [] /\ eff_zeros eff = [] /\ eff_unmaps eff = [] /\ eff_copies eff = [].
Proof.
  intros [ret ws zs us cs ci] m m' evs [H|H];
    [unfold check_clone_resolve in H | unfold check_clone_ns_resolve in H];
    destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); try discriminate H;
    destruct ws, zs, us, cs, ci; try discriminate H; repeat split.
Qed.

Local Lemma resolve3_no_memory : forall uargs eff m m' evs,
  check_clone3_resolve uargs eff m = CheckOk m' evs ->
  eff_writes eff = [] /\ eff_zeros eff = [] /\ eff_unmaps eff = [] /\ eff_copies eff = [].
Proof.
  intros uargs [ret ws zs us cs ci] m m' evs H. unfold check_clone3_resolve in H.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); try discriminate H.
  destruct ws, zs, us, cs; try discriminate H. repeat split.
Qed.

(** A successful step of one of those words leaves the caller's memory as
    it was: its answer writes nothing. *)
Local Lemma admitted_before_memory : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  clone_success_b c c' = true ->
  clone_word_admitted_before c = true ->
  ms_mem (cfg_ms c') = ms_mem (cfg_ms c).
Proof.
  intros segs cfg c evs c' Hss Hcs Hpre.
  pose proof (clone_success_pending c c' Hcs) as Hcp.
  unfold clone_pending_b in Hcp.
  inversion Hss as
    [ ms model ms' model' Hh Hsv Hacc
    | |
    | ms model fn n eff model' model'' evs0 Hh Hsv Hacc Hfn Hn Hsp Hne Hh' Hmat
    | |
    | ms model x8 eff model' model'' evs0 Hh Hsv Hsp Hrf Hh' Hmat
    |
    | ms model x8 eff model' evs0 code Hh Hsv Hsp Hh' Hk'
    | ms model x8 eff model' evs0 sig Hh Hsv Hsp Hk'
    | ]; subst; cbn [cfg_model cfg_ms] in *.
  - rewrite Hsv in Hcp. discriminate Hcp.
  - rewrite Hsv in Hcp. discriminate Hcp.
  - (* a syscall *)
    unfold clone_word_admitted_before in Hpre. cbn [cfg_ms] in Hpre. rewrite Hsv in Hpre.
    apply check_syscall_complete_ok in Hsp.
    assert (Hz : eff_writes eff = [] /\ eff_zeros eff = [] /\ eff_unmaps eff = []
                 /\ eff_copies eff = []).
    { destruct (Z.eqb (bv_unsigned x8) 220%Z) eqn:H220.
      - apply Z.eqb_eq in H220.
        rewrite (check_syscall_clone (sys_input segs ms x8) _ _ H220) in Hsp.
        unfold check_clone in Hsp.
        change (clone_fork_flags_b (in_arg (sys_input segs ms x8) 0)
                || clone_ns_flags_b (in_arg (sys_input segs ms x8) 0) = true) in Hpre.
        destruct (clone_fork_flags_b (in_arg (sys_input segs ms x8) 0)); cbv iota in Hsp.
        + apply (resolve_no_memory _ _ _ _ (or_introl Hsp)).
        + cbn [orb] in Hpre. rewrite Hpre in Hsp. cbv iota in Hsp.
          apply (resolve_no_memory _ _ _ _ (or_intror Hsp)).
      - destruct (Z.eqb (bv_unsigned x8) 435%Z) eqn:H435; [|discriminate Hpre].
        apply Z.eqb_eq in H435.
        rewrite (check_syscall_clone3 (sys_input segs ms x8) _ _ H435) in Hsp.
        unfold check_clone3 in Hsp.
        change ((bv_eqb (in_arg (sys_input segs ms x8) 1) (Z_to_bv 64 CLONE_ARGS_SIZE)
                 && match copy_bytes_map (in_mem (sys_input segs ms x8))
                            (in_arg (sys_input segs ms x8) 0) CLONE_ARGS_SIZE with
                    | Some bs => clone3_fork_args_b bs
                    | None => false
                    end) = true) in Hpre.
        apply andb_true_iff in Hpre as [Hsz Hpre]. apply bv_eqb_eq in Hsz.
        rewrite Hsz, clone3_size_88_unsigned, clone3_copy_88 in Hsp.
        unfold clone3_copy_full in Hsp.
        destruct (copy_bytes_map (in_mem (sys_input segs ms x8))
                    (in_arg (sys_input segs ms x8) 0) CLONE_ARGS_SIZE) as [bs|];
          [|discriminate Hpre].
        cbv iota in Hsp, Hpre. unfold check_clone3_on_struct in Hsp.
        rewrite Hpre in Hsp. cbv iota in Hsp.
        exact (resolve3_no_memory _ _ _ _ _ Hsp). }
    destruct eff as [ret ws zs us cs ci]. cbn [eff_writes eff_zeros eff_unmaps eff_copies] in Hz.
    destruct Hz as (-> & -> & -> & ->). reflexivity.
  - exfalso.
    rewrite Hsv in Hcp. cbv beta iota in Hcp. unfold clone_sysno in Hcp.
    assert (Hn : bv_unsigned x8 = 220%Z \/ bv_unsigned x8 = 435%Z)
      by (apply orb_true_iff in Hcp as [Hc|Hc]; apply Z.eqb_eq in Hc;
          [left | right]; exact Hc).
    pose proof (clone_spec_keeps_halted (sys_input segs ms x8) _ _ _ _ Hn Hsp) as Hk.
    rewrite Hh', Hh in Hk. discriminate Hk.
  - exfalso.
    rewrite Hsv in Hcp. cbv beta iota in Hcp. unfold clone_sysno in Hcp.
    assert (Hn : bv_unsigned x8 = 220%Z \/ bv_unsigned x8 = 435%Z)
      by (apply orb_true_iff in Hcp as [Hc|Hc]; apply Z.eqb_eq in Hc;
          [left | right]; exact Hc).
    pose proof (clone_spec_keeps_halted (sys_input segs ms x8) _ _ _ _ Hn Hsp) as Hk.
    unfold m_killed in Hk'. unfold m_halted in Hk, Hh.
    destruct (procst_killed (m_proc model')); cbv beta iota in Hk';
      [|discriminate Hk'].
    rewrite Hk', Hh in Hk. discriminate Hk.
Qed.

(** [Procs.child_ms] and [Procs.child_entry] as they were before
    [CLONE_SYSVSEM] and the tid bits were admitted, verbatim: the
    caller's successor with a0 = 0 and, for [clone] with a non-zero a1,
    sp = a1 (the earlier [clone_child_sp] inlined), and the caller's own
    record as the child's model. *)
Definition child_ms_before (c c' : config) : machine_state :=
  let base := set_reg (cfg_ms c') 10 (Z_to_bv 64 0) in
  match match ms_svc_pending (cfg_ms c) with
        | Some x8 =>
            if Z.eqb (bv_unsigned x8) 220%Z then
              if w_is0 (ms_gpr (cfg_ms c) 1) then None else Some (ms_gpr (cfg_ms c) 1)
            else None
        | None => None
        end with
  | None => base
  | Some sp => set_reg base 2 sp
  end.

Definition child_entry_before (e : ProcessEntry) (c c' : config) (q : Pid)
    : ProcessEntry :=
  mkEntry q (Some (pe_pid e)) (child_ms_before c c')
          (clear_shared (with_proc (child_proc (pe_pid e) (m_proc (pe_model e)))
                                   (pe_model e)))
          (pe_ofd e) (pe_nsctx e).

(** THE WORDS ADMITTED BEFORE [CLONE_SYSVSEM] AND THE TID BITS KEEP THEIR
    CLONE RELATION.  For a successful released step of [clone]'s fork or
    namespace word or of [clone3]'s fork image, and whatever return value
    [ret] the namespace extension gives, [px_clone]'s new premise
    [Procs.clone_parent_rewrite] holds with the successor [with_ret c'
    ret] unchanged, the child makes no store, and the child entry the
    rule builds is the earlier one ([child_entry_before]).  So [px_clone]
    relates exactly what it related before, and [px_clone_store_refuse],
    whose premise is that [clone_parent_rewrite] gives [None], never fires
    for those words.  Their released answers are unchanged too, outcome
    for outcome ([Kernel.Fork.clone_admitted_words_unchanged]). *)
Lemma clone_admitted_words_child_unchanged : forall segs cfg c evs c' ret e q,
  sstep_cfg segs cfg c evs (SNext c') ->
  clone_success_b c c' = true ->
  clone_word_admitted_before c = true ->
  clone_parent_rewrite segs c (with_ret c' ret) ret = Some (with_ret c' ret)
  /\ child_tid_store c (with_ret c' ret) = []
  /\ child_entry e c (with_ret c' ret) q = child_entry_before e c (with_ret c' ret) q.
Proof.
  intros segs cfg c evs c' ret e q Hss Hcs Hpre.
  pose proof (admitted_before_memory _ _ _ _ _ Hss Hcs Hpre) as Hmem.
  assert (Hmem1 : ms_mem (cfg_ms (with_ret c' ret)) = ms_mem (cfg_ms c)).
  { destruct ret as [v|]; cbn [with_ret cfg_ms]; [rewrite ms_mem_set_reg|]; exact Hmem. }
  assert (Hr : exists r, clone_args_of_cfg c = Some r
                         /\ Z.land (cla_flags r) clone_extra_bits = 0%Z
                         /\ cla_stack r = match ms_svc_pending (cfg_ms c) with
                                          | Some x8 =>
                                              if Z.eqb (bv_unsigned x8) 220%Z
                                              then ms_gpr (cfg_ms c) 1 else Z_to_bv 64 0
                                          | None => Z_to_bv 64 0
                                          end).
  { unfold clone_word_admitted_before in Hpre. unfold clone_args_of_cfg. cbv zeta.
    destruct (ms_svc_pending (cfg_ms c)) as [x8|]; [|discriminate Hpre].
    destruct (Z.eqb (bv_unsigned x8) 220%Z); cbv beta iota in Hpre |- *.
    - destruct (clone_args_of_clone (ms_gpr (cfg_ms c) 0) (ms_gpr (cfg_ms c) 1)
                  (ms_gpr (cfg_ms c) 2) (ms_gpr (cfg_ms c) 3) (ms_gpr (cfg_ms c) 4))
        as [r|] eqn:Hr.
      + exists r. split; [reflexivity|]. split.
        * exact (clone_admitted_no_extra_bits _ _ _ _ _ r
                   (proj1 (orb_true_iff _ _) Hpre) Hr).
        * unfold clone_args_of_clone in Hr.
          destruct (bv_unsigned (ms_gpr (cfg_ms c) 0) <? 2 ^ 32)%Z; [|discriminate Hr].
          injection Hr as <-. reflexivity.
      + exfalso. unfold clone_args_of_clone in Hr.
        destruct (bv_unsigned (ms_gpr (cfg_ms c) 0) <? 2 ^ 32)%Z eqn:Hlt; [discriminate Hr|].
        apply Z.ltb_ge in Hlt.
        apply orb_true_iff in Hpre as [Hf|Hns].
        * unfold clone_fork_flags_b in Hf. apply bv_eqb_eq in Hf. rewrite Hf in Hlt.
          vm_compute in Hlt. apply Hlt. reflexivity.
        * unfold clone_ns_flags_b in Hns. apply andb_true_iff in Hns as [Hns _].
          apply Z.eqb_eq in Hns.
          pose proof (ns_word_below _ Hns
                        (proj1 (bv_unsigned_in_range _ (ms_gpr (cfg_ms c) 0)))) as Hb.
          lia.
    - destruct (Z.eqb (bv_unsigned x8) 435%Z); cbv beta iota in Hpre |- *; [|discriminate Hpre].
      apply andb_true_iff in Hpre as [Hsz Hpre]. apply bv_eqb_eq in Hsz.
      rewrite Hsz, clone3_size_88_unsigned, clone3_copy_88. unfold clone3_copy_full.
      destruct (copy_bytes_map (ms_read_byte (cfg_ms c)) (ms_gpr (cfg_ms c) 0) CLONE_ARGS_SIZE)
        as [bs|]; cbv beta iota in Hpre |- *; [|discriminate Hpre].
      unfold clone3_fork_args_b, w_is0 in Hpre.
      repeat (apply andb_true_iff in Hpre as [Hpre ?]).
      repeat match goal with Hb : bv_eqb _ _ = true |- _ => apply bv_eqb_eq in Hb end.
      unfold clone3_pre_sz. cbv iota. unfold clone3_pre. cbv zeta.
      repeat match goal with Hb : clone_args_field bs _ = _ |- _ => rewrite Hb; clear Hb end.
      lazymatch goal with
      | |- exists r, ?L = Some r /\ _ =>
          let v := eval vm_compute in L in
          lazymatch v with Some ?r0 => exists r0 end
      end.
      split; [vm_compute; reflexivity|].
      split; vm_compute; reflexivity. }
  destruct Hr as (r & Hr & H0 & Hst).
  destruct (clone_no_extra_bits_unchanged segs c (with_ret c' ret) (with_ret c' ret) ret r Hr H0)
    as (Hts & Hrw & Hms & Hs).
  split; [exact Hrw|]. split; [exact Hts|].
  unfold child_entry, child_entry_before. rewrite Hts. cbn [child_model].
  f_equal.
  rewrite Hms. cbn [child_regs]. rewrite Hs, Hst.
  unfold child_ms_before. cbv zeta.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; cbv beta iota.
  - destruct (Z.eqb (bv_unsigned x8) 220%Z); cbv beta iota.
    + destruct (w_is0 (ms_gpr (cfg_ms c) 1)); cbv beta iota;
        apply ms_with_mem_regs; rewrite ?ms_mem_set_reg; exact Hmem1.
    + replace (w_is0 (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
      cbv beta iota. apply ms_with_mem_regs. rewrite ?ms_mem_set_reg. exact Hmem1.
  - replace (w_is0 (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
    cbv beta iota. apply ms_with_mem_regs. rewrite ?ms_mem_set_reg. exact Hmem1.
Qed.

(* =========================================================================
   Every producing arm keeps the invariant
   ========================================================================= *)

(** A reaped child is over: [pe_status] answers only for a halted entry. *)
Lemma pe_status_halted : forall dumped ez status,
  pe_status dumped ez = Some status -> m_halted (pe_model ez) <> None.
Proof.
  intros dumped ez status H Hz. unfold pe_status in H. rewrite Hz in H. discriminate H.
Qed.

Lemma tbl_root_absorb : forall P e c',
  tbl_wf (pcfg_procs P) -> root_ok (pcfg_procs P) (pcfg_root P) ->
  look P (pe_pid e) = Some e ->
  tbl_wf (pcfg_procs (absorb P e c')) /\ root_ok (pcfg_procs (absorb P e c')) (pcfg_root (absorb P e c')).
Proof.
  intros P e c' Htbl Hroot Hl. pose proof (look_in_In _ _ _ Hl) as He.
  pose proof Htbl as (_ & _ & Hnd).
  unfold absorb. cbn [pcfg_procs pcfg_root]. split.
  - apply (tbl_absorb _ _ e); [exact Htbl | exact He | reflexivity | reflexivity | reflexivity].
  - apply root_orphan. apply (root_replace _ _ e); [exact Hnd | exact He | reflexivity | exact Hroot].
Qed.

(** The clock sync replaces one entry by one with the same pid, parent and
    halt state. *)
Lemma tbl_root_sync : forall P e,
  tbl_wf (pcfg_procs P) -> root_ok (pcfg_procs P) (pcfg_root P) ->
  look P (pe_pid e) = Some e -> m_halted (pe_model e) = None ->
  tbl_wf (pcfg_procs (sync_result P e))
  /\ root_ok (pcfg_procs (sync_result P e)) (pcfg_root (sync_result P e)).
Proof.
  intros P e Htbl Hroot Hl Hh. pose proof (look_in_In _ _ _ Hl) as He.
  pose proof Htbl as (_ & _ & Hnd).
  unfold sync_result. cbn [pcfg_procs pcfg_root]. split.
  - rewrite <- (orphan_at_exit_running (pe_model (sync_entry P e)) (pe_pid e)
                  (replace_in (pcfg_procs P) (pe_pid e) (sync_entry P e)))
      by (rewrite sync_entry_halted; exact Hh).
    apply (tbl_absorb _ _ e); [exact Htbl | exact He | reflexivity | reflexivity | reflexivity].
  - apply (root_replace _ _ e); [exact Hnd | exact He | reflexivity | exact Hroot].
Qed.

(** The root pin replaces the root's entry by one with the same pid,
    parent and halt state; the root is running, since the caller is its
    child and a parent in the table is running. *)
Lemma tbl_root_pin : forall P e r t,
  tbl_wf (pcfg_procs P) -> root_ok (pcfg_procs P) (pcfg_root P) ->
  look P (pe_pid e) = Some e -> root_pin_pending_b P e = true ->
  look P (pcfg_root P) = Some r ->
  tbl_wf (pcfg_procs (pin_root P r t))
  /\ root_ok (pcfg_procs (pin_root P r t)) (pcfg_root (pin_root P r t)).
Proof.
  intros P e r t Htbl Hroot Hl Hpin Hlr.
  pose proof (look_in_In _ _ _ Hl) as He.
  pose proof (look_in_In _ _ _ Hlr) as Hr.
  pose proof Htbl as (Hkey & Hpar & Hnd).
  unfold root_pin_pending_b in Hpin.
  destruct (ms_svc_pending (pe_ms e)); [|discriminate Hpin].
  apply andb_true_iff in Hpin as [Hpin _]. apply andb_true_iff in Hpin as [_ Hpe].
  destruct (pe_parent e) as [par|] eqn:Hpe'; [|discriminate Hpe].
  apply bv_eqb_true_eq in Hpe. subst par.
  destruct (Hpar _ _ He Hpe') as (_ & f & Hf & Hfrun).
  rewrite (In_unique _ _ _ _ Hnd Hf Hr) in Hfrun.
  pose proof (Hkey _ Hr) as Hkr. cbn [fst snd] in Hkr.
  unfold pin_root. cbn [pcfg_procs pcfg_root]. split.
  - rewrite <- (orphan_at_exit_running (with_tid t (pe_model r)) (pcfg_root P)
                  (replace_in (pcfg_procs P) (pcfg_root P)
                     (mkEntry (pe_pid r) (pe_parent r) (pe_ms r) (with_tid t (pe_model r))
                              (pe_ofd r) (pe_nsctx r))))
      by exact Hfrun.
    apply (tbl_absorb _ _ r);
      [exact Htbl | exact Hr | cbn [pe_pid]; symmetry; exact Hkr | reflexivity | reflexivity].
  - apply (root_replace _ _ r); [exact Hnd | exact Hr | reflexivity | exact Hroot].
Qed.

Lemma tbl_root_reap : forall P e q ez eff model'',
  tbl_wf (pcfg_procs P) -> root_ok (pcfg_procs P) (pcfg_root P) ->
  look P (pe_pid e) = Some e -> m_halted (pe_model e) = None ->
  look P q = Some ez -> q <> pe_pid e -> pe_parent ez = Some (pe_pid e) ->
  m_halted (pe_model ez) <> None ->
  materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
    (syscall_effect_accesses eff) = Some model'' ->
  let P' := wait4_reap_result P e q eff model'' in
  tbl_wf (pcfg_procs P') /\ root_ok (pcfg_procs P') (pcfg_root P').
Proof.
  intros P e q ez eff model'' Htbl Hroot Hl Hh Hlq Hne Hpar Hzz Hmat P'.
  subst P'. pose proof (look_in_In _ _ _ Hl) as He.
  pose proof (look_in_In _ _ _ Hlq) as Hez.
  pose proof Htbl as (_ & _ & Hnd).
  assert (Hrun : m_halted (clear_shared model'') = None).
  { destruct (materialize_model_accesses_frame _ _ _ Hmat)
      as (_ & _ & _ & _ & _ & Hproc & _).
    change (m_halted model'' = None). unfold m_halted in *. rewrite Hproc. exact Hh. }
  unfold wait4_reap_result. cbn [pcfg_procs pcfg_root]. split.
  - apply (tbl_reap _ _ e _ _ ez);
      [exact Htbl | exact He | exact Hez | reflexivity | reflexivity | exact Hrun
      | exact Hne | exact Hzz].
  - apply root_drop.
    + intros Hrq. destruct Hroot as (er & Hr & Hrp). rewrite Hrq in Hr.
      rewrite (In_unique _ _ _ _ Hnd Hr Hez) in Hrp. rewrite Hpar in Hrp.
      discriminate Hrp.
    + apply (root_replace _ _ e); [exact Hnd | exact He | reflexivity | exact Hroot].
Qed.

(** EVERY PRODUCING ARM KEEPS THE TABLE WELL FORMED.  With
    [Procs.pconfig_wf_one_proc], [pconfig_wf] holds at every configuration
    reachable from a released [execve]. *)
Theorem pstep_at_preserves_wf : forall segs cfg p P evs P',
  pconfig_wf P -> pstep_at segs cfg p P evs (PNext P') -> pconfig_wf P'.
Proof.
  intros segs cfg p P evs P' Hwf Hp.
  apply wf_iff in Hwf as [Htbl Hroot]. apply wf_iff.
  inversion Hp as
    [ P1 e1 evs1 c1 Hl1 Hs1 Hc1 Hw1 Hm1 Hwo1 Hns1 Hsy1 Hst1 Han1
    | P2 e2 evs2 c2 q2 Hl2 Hs2 Hc2 Hcp2 Hfr2 Hm2
    | P3 e3 q3 ez3 x83 sa3 st3 eff3 mo3 du3
        Hl3 Hh3 Hsv3 Hwi3 Hwa3 Hlq3 Hne3 Hpar3 Hk3 Hst3 Hrd3 Heff3 Hmat3
    | P4 e4 evs4 Hl4 Hs4 Hw4 Hwo4
    | P5 e5 Hl5 Hh5 Hm5
    | P6 e6 q6 ez6 x86 sa6 ru6 rb6 st6 eff6 mo6 du6
        Hl6 Hh6 Hsv6 Hwo6 Hna6 Hru6 Hlq6 Hne6 Hpar6 Hk6 Hst6 Hrd6 Hlen6 Heff6 Hmat6
    | P7 e7 x87 sa7 ru7 Hl7 Hh7 Hsv7 Hwo7 Hna7 Hru7 Hz7
    | P8 e8 Hl8 Hh8 Hrf8
    | P9 e9 Hl9 Hh9 Hns9
    | P10 e10 Hl10 Hh10 Hsy10
    | P11 e11 evs11 c11 Hl11 Hs11 Hc11 Hw11 Hm11 Hwo11 Hns11 Hsy11 Hst11 Han11
    | P12 e12 r12 t12 Hl12 Hh12 Hpin12 Hlr12 Ht12 Hkt12 ]; subst.
  - (* pstep_other *)
    exact (tbl_root_absorb _ e1 c1 Htbl Hroot Hl1).
  - (* pstep_clone *)
    pose proof (look_in_In _ _ _ Hl2) as He.
    pose proof Htbl as (_ & _ & Hnd).
    unfold clone_result. cbn [pcfg_procs pcfg_root]. split.
    + apply (tbl_clone _ _ e2);
        [ exact Htbl | exact He | reflexivity | reflexivity
        | exact (clone_step_running _ _ _ _ _ Hs2 Hc2)
        | exact (look_in_None_notin _ _ Hfr2) | reflexivity | reflexivity ].
    + apply root_app. apply (root_replace _ _ e2);
        [exact Hnd | exact He | reflexivity | exact Hroot].
  - (* pstep_wait_reap: its successor is [wait4_reap_result] written out *)
    exact (tbl_root_reap _ e3 q3 ez3 _ mo3 Htbl Hroot Hl3 Hh3 Hlq3 Hne3 Hpar3
             (pe_status_halted _ _ _ Hst3) Hmat3).
  - (* pstep_wait_nohang_reap *)
    exact (tbl_root_reap _ e6 q6 ez6 _ mo6 Htbl Hroot Hl6 Hh6 Hlq6 Hne6 Hpar6
             (pe_status_halted _ _ _ Hst6) Hmat6).
  - (* pstep_wait_nohang_zero: an absorb *)
    exact (tbl_root_absorb _ e7 _ Htbl Hroot Hl7).
  - (* pstep_sync: one entry's clock copy, nothing structural *)
    exact (tbl_root_sync _ e10 Htbl Hroot Hl10 Hh10).
  - (* pstep_pin_root: the root's tid, nothing structural *)
    exact (tbl_root_pin _ e12 r12 t12 Htbl Hroot Hl12 Hpin12 Hlr12).
Qed.
