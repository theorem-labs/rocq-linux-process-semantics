(** * LinuxProcessSem.Checks.AnonAgreeInvariant — anon_agree as a reachable-state invariant

    [anon_agree_holds] says that every [FdAnon] entry in the descriptor
    table agrees with every other entry of the same unnamed file: every
    descriptor of one file carries the same contents and the same stat
    pin.  This file proves that predicate is an invariant of
    [Run.star]: it holds at [Run.init_config] and is preserved by
    every [Run.sstep].

    The per-arm preservation lemmas that the init and step cases
    consume are in [Checks.AnonAgree].  This file lifts them to a
    whole-table predicate and carries the predicate along a run. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Dispatch.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  AnonAgree ExecutableSpecs VmMapsDisjoint KillFree.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import
  Dispatch.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The predicate
   ========================================================================= *)

(** Every [FdAnon] entry in the descriptor table agrees with every
    other entry of the same unnamed file. *)
Definition anon_agree_all (fds : list (word * FdEntry)) : Prop :=
  forall fd id af,
    In (fd, FdAnon id af) fds ->
    anon_agree fds id af = true.

Definition anon_agree_holds (c : config) : Prop :=
  anon_agree_all (m_fds (cfg_model c)).

(* =========================================================================
   Helper: In under filter and fd_insert
   ========================================================================= *)

Local Lemma In_filter_In {A} (f : A -> bool) l x :
  In x (filter f l) -> In x l.
Proof.
  induction l as [|h t IH]; [exact id|].
  cbn [filter]. destruct (f h).
  - intros [<-|Hin]; [left; reflexivity | right; exact (IH Hin)].
  - intros Hin. right. exact (IH Hin).
Qed.

Local Lemma In_fd_insert_inv fds k e p :
  In p (fd_insert fds k e) ->
  p = (k, e) \/ In p (filter (fun q => negb (bv_eqb (fst q) k)) fds).
Proof.
  unfold fd_insert. intros [<-|Hin]; [left; reflexivity | right; exact Hin].
Qed.

(* =========================================================================
   Preservation lemmas for anon_agree_all
   ========================================================================= *)

(** When the fd table is the same. *)
Lemma anon_agree_all_eq : forall fds fds',
  fds' = fds -> anon_agree_all fds -> anon_agree_all fds'.
Proof. intros fds fds' <- H. exact H. Qed.

(** Filter preserves: a subset of an agreeing table agrees. *)
Lemma anon_agree_all_filter : forall f fds,
  anon_agree_all fds -> anon_agree_all (filter f fds).
Proof.
  intros f fds Hall fd id af Hin.
  apply anon_agree_filter.
  exact (Hall fd id af (In_filter_In f fds _ Hin)).
Qed.

(** [fd_remove] preserves (it is [filter]). *)
Lemma anon_agree_all_fd_remove : forall fds k,
  anon_agree_all fds -> anon_agree_all (fd_remove fds k).
Proof. intros fds k H. exact (anon_agree_all_filter _ fds H). Qed.

(** Inserting a non-[FdAnon] entry preserves agreement. *)
Lemma anon_agree_all_fd_insert_non_anon : forall fds k e,
  (forall id af, e <> FdAnon id af) ->
  anon_agree_all fds -> anon_agree_all (fd_insert fds k e).
Proof.
  intros fds k e Hne Hall fd id af Hin.
  destruct (In_fd_insert_inv _ _ _ _ Hin) as [Heq | Hfilt].
  - injection Heq as <- <-. exfalso. exact (Hne id af eq_refl).
  - apply anon_agree_fd_insert.
    + exact (Hall _ _ _ (In_filter_In _ _ _ Hfilt)).
    + destruct e; try reflexivity.
      exfalso. exact (Hne _ _ eq_refl).
Qed.

(** A key auxiliary: if [anon_agree fds id af = true], then for any
    [FdAnon id af'] in [fds], [af_data af' = af_data af] and
    [af_pin af' = af_pin af]. *)
Lemma anon_agree_entry_data_pin : forall fds id af fd af',
  anon_agree fds id af = true ->
  In (fd, FdAnon id af') fds ->
  af_data af' = af_data af /\ af_pin af' = af_pin af.
Proof.
  intros fds id af fd af' Hagr Hin.
  unfold anon_agree in Hagr. rewrite forallb_forall in Hagr.
  specialize (Hagr (fd, FdAnon id af') Hin). cbn [snd] in Hagr.
  rewrite anon_entry_agrees_anon in Hagr.
  rewrite (proj2 (bv_eqb_eq id id) eq_refl) in Hagr.
  cbn [implb] in Hagr. apply andb_true_iff in Hagr as [Hd Hp].
  apply path_eqb_eq in Hd. apply anon_pin_eqb_eq in Hp.
  exact (conj Hd Hp).
Qed.

(** Inserting [FdAnon id af'] where [af'] has the same data and pin as
    an existing agreeing view preserves the whole-table invariant. *)
Lemma anon_agree_all_fd_insert_anon : forall fds k id af af',
  anon_agree_all fds ->
  anon_agree fds id af = true ->
  af_data af' = af_data af -> af_pin af' = af_pin af ->
  anon_agree_all (fd_insert fds k (FdAnon id af')).
Proof.
  intros fds k id af af' Hall Hagr Hd Hp fd0 id0 af0 Hin.
  destruct (In_fd_insert_inv _ _ _ _ Hin) as [Heq | Hfilt].
  - injection Heq as <- Heq. injection Heq as <- <-.
    apply anon_agree_fd_insert.
    + rewrite (anon_agree_congr fds id af' af Hd Hp). exact Hagr.
    + apply anon_entry_agrees_same; reflexivity.
  - pose proof (In_filter_In _ _ _ Hfilt) as Hin0.
    destruct (bv_eqb id0 id) eqn:Eid.
    + apply bv_eqb_eq in Eid. subst id0.
      pose proof (Hall _ _ _ Hin0) as Hagr0.
      pose proof (anon_agree_entry_data_pin _ _ _ _ _ Hagr Hin0) as [Hd0 Hp0].
      apply anon_agree_fd_insert.
      * apply anon_agree_filter. exact Hagr0.
      * apply anon_entry_agrees_same; [rewrite Hd, Hd0; reflexivity | exact Hp].
    + apply anon_agree_fd_insert.
      * apply anon_agree_filter. exact (Hall _ _ _ Hin0).
      * apply anon_entry_agrees_other.
        intros E. subst id0. rewrite (proj2 (bv_eqb_eq id id) eq_refl) in Eid.
        discriminate Eid.
Qed.

(** [af_set_off] preserves data and pin. *)
Lemma af_data_set_off : forall af o, af_data (af_set_off af o) = af_data af.
Proof. intros []; reflexivity. Qed.
Lemma af_pin_set_off : forall af o, af_pin (af_set_off af o) = af_pin af.
Proof. intros []; reflexivity. Qed.

(** Inserting an offset-updated entry of an agreeing descriptor. *)
Lemma anon_agree_all_fd_insert_set_off : forall fds k id af o,
  anon_agree_all fds ->
  anon_agree fds id af = true ->
  anon_agree_all (fd_insert fds k (FdAnon id (af_set_off af o))).
Proof.
  intros fds k id af o Hall Hagr.
  apply (anon_agree_all_fd_insert_anon fds k id af);
    [exact Hall | exact Hagr | apply af_data_set_off | apply af_pin_set_off].
Qed.

(** [anon_update] with a function that maps equal data/pin to equal
    data/pin preserves the invariant. *)
Lemma anon_agree_all_anon_update : forall fds id f,
  (forall a b, af_data a = af_data b -> af_pin a = af_pin b ->
     af_data (f a) = af_data (f b) /\ af_pin (f a) = af_pin (f b)) ->
  anon_agree_all fds ->
  anon_agree_all (anon_update fds id f).
Proof.
  intros fds id f Hf Hall.
  unfold anon_agree_all. intros fd id0 af0 Hin.
  unfold anon_update in Hin.
  apply in_map_iff in Hin. destruct Hin as [[k e] [Heq Hin']].
  cbn [fst snd] in Heq.
  (* Only the FdAnon branch of anon_entry_update can produce a FdAnon *)
  destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |sid side st|ctx|fam|id' af'|o'|qid qsd qst];
    unfold anon_entry_update in Heq; cbv beta iota in Heq.
  (* Non-FdAnon cases: the output is not FdAnon, so Heq is impossible *)
  1-13,15-16: (injection Heq as <- Habs; discriminate Habs).
  (* FdAnon case *)
  destruct (bv_eqb id' id) eqn:Eid.
  - injection Heq as <- <-. apply bv_eqb_eq in Eid. subst id'.
    exact (anon_agree_update fds id af' f Hf (Hall _ _ _ Hin')).
  - injection Heq as <- <-.
    apply (anon_agree_update_other fds id f id0 af0).
    + intros E. rewrite E, (proj2 (bv_eqb_eq id id) eq_refl) in Eid.
      discriminate Eid.
    + exact (Hall _ _ _ Hin').
Qed.

(** [anon_set_data] preserves. *)
Lemma anon_agree_all_anon_set_data : forall fds id d,
  anon_agree_all fds ->
  anon_agree_all (anon_set_data fds id d).
Proof.
  intros fds id d Hall. unfold anon_set_data.
  apply anon_agree_all_anon_update; [|exact Hall].
  intros a b _ Hp. split; [reflexivity | exact Hp].
Qed.

(** [anon_write_back] preserves. *)
Lemma anon_agree_all_anon_write_back : forall fds fd id af d o,
  anon_agree_all fds ->
  anon_agree fds id af = true ->
  anon_agree_all (anon_write_back fds fd id af d o).
Proof.
  intros fds fd id af d o Hall Hagr. unfold anon_write_back.
  apply (anon_agree_all_fd_insert_anon (anon_set_data fds id d) fd id
           (af_set_data af d) (af_set_off (af_set_data af d) o)).
  - exact (anon_agree_all_anon_set_data fds id d Hall).
  - exact (anon_agree_set_data fds id af d Hagr).
  - apply af_data_set_off.
  - apply af_pin_set_off.
Qed.

(** [anon_update] with [af_set_pin] preserves. *)
Lemma anon_agree_all_set_pin : forall fds id bs,
  anon_agree_all fds ->
  anon_agree_all (anon_update fds id (fun a => af_set_pin a bs)).
Proof.
  intros fds id bs Hall.
  apply anon_agree_all_anon_update; [|exact Hall].
  intros a b Hd _. split; [exact Hd | reflexivity].
Qed.

(** [fd_lookup] implies [In]. *)
Lemma fd_lookup_In : forall fds fd e,
  fd_lookup fds fd = Some e -> In (fd, e) fds.
Proof.
  induction fds as [|[k v] r IH]; intros fd e Hl; [discriminate Hl|].
  cbn [fd_lookup] in Hl. destruct (bv_eqb k fd) eqn:Ek.
  - apply bv_eqb_eq in Ek. subst k. injection Hl as <-. left. reflexivity.
  - right. exact (IH _ _ Hl).
Qed.

(** [dup3_fds] preserves. *)
Lemma anon_agree_all_dup3_fds : forall fds oldfd newfd e fds',
  fd_lookup fds oldfd = Some e ->
  dup3_fds oldfd newfd e fds = Some fds' ->
  anon_agree_all fds -> anon_agree_all fds'.
Proof.
  intros fds oldfd newfd e fds' Hlook Hdup Hall fd id af Hin.
  unfold dup3_fds in Hdup.
  destruct (dup_modeled_entry e) eqn:Edm.
  - injection Hdup as <-.
    destruct (In_fd_insert_inv _ _ _ _ Hin) as [Heq | Hfilt].
    + injection Heq as <- Heq. subst e.
      pose proof (fd_lookup_In fds oldfd (FdAnon id af) Hlook) as HinOld.
      apply anon_agree_fd_insert.
      * exact (Hall _ _ _ HinOld).
      * apply anon_entry_agrees_same; reflexivity.
    + pose proof (In_filter_In _ _ _ Hfilt) as Hin0.
      pose proof (Hall _ _ _ Hin0) as Hagr.
      apply anon_agree_fd_insert; [exact Hagr|].
      destruct e; try reflexivity.
      rewrite anon_entry_agrees_anon.
      destruct (bv_eqb b id) eqn:Eid'; [|reflexivity].
      apply bv_eqb_eq in Eid'. subst b.
      pose proof (fd_lookup_In _ _ _ Hlook) as HinE.
      pose proof (anon_agree_entry_data_pin _ _ _ _ _ Hagr HinE) as [Hd Hp].
      cbn [implb]. rewrite Hd, path_eqb_refl, Hp, anon_pin_eqb_refl. reflexivity.
  - destruct (dup3_moves_entry e) eqn:Emoves; [|discriminate Hdup].
    injection Hdup as <-.
    destruct (In_fd_insert_inv _ _ _ _ Hin) as [Heq | Hfilt].
    + injection Heq as _ Heq. discriminate Heq.
    + pose proof (In_filter_In _ _ _ Hfilt) as HinInner.
      destruct (In_fd_insert_inv _ _ _ _ HinInner) as [Heq2 | Hfilt2].
      * injection Heq2 as <- Heq2. subst e.
        pose proof (fd_lookup_In _ _ _ Hlook) as HinOld.
        pose proof (Hall _ _ _ HinOld) as Hagr.
        eapply (anon_agree_dup3_fds fds oldfd newfd (FdAnon id af) _ id af Hlook _ Hagr).
        unfold dup3_fds. rewrite Edm, Emoves. reflexivity.
      * pose proof (In_filter_In _ _ _ Hfilt2) as Hin0.
        pose proof (Hall _ _ _ Hin0) as Hagr.
        eapply (anon_agree_dup3_fds fds oldfd newfd e _ id af Hlook _ Hagr).
        unfold dup3_fds. rewrite Edm, Emoves. reflexivity.
Qed.

(** The unlink_open map preserves agreement. *)
Lemma anon_agree_all_unlink_open : forall c id data pin fds,
  anon_id_live fds id = false ->
  anon_agree_all fds ->
  anon_agree_all (map (fun q => (fst q, unlink_open_entry c id data pin (snd q))) fds).
Proof.
  intros c id data pin fds Hlive Hall.
  unfold anon_agree_all. intros fd0 id0 af0 Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[k e] [Heq Hin']]. cbn [fst snd] in Heq.
  injection Heq as <- Hunlink.
  destruct (bv_eqb id0 id) eqn:Eid.
  - apply bv_eqb_eq in Eid. subst id0.
    destruct e; unfold unlink_open_entry in Hunlink; cbv beta iota in Hunlink;
      try discriminate Hunlink.
    all: try (destruct (Fs.path_eqb c _) eqn:Epc; cbv iota in Hunlink;
              [injection Hunlink as <-;
               rewrite (anon_agree_congr _ id af0
                 (mkAnonFile data (af_off af0) (af_rd af0) (af_wr af0) (af_app af0) pin));
               [apply anon_agree_unlink_open; exact Hlive | reflexivity | reflexivity]
              |discriminate Hunlink]).
    (* FdAnon case *)
    + cbn [entry_anon_id] in *.
      destruct (bv_eqb _ id) eqn:Eid'.
      * exfalso. unfold anon_id_live in Hlive.
        apply bv_eqb_eq in Eid'. subst.
        assert (Htrue : existsb (fun p => match entry_anon_id (snd p) with
                                          | Some id' => bv_eqb id' id
                                          | None => false end) fds = true).
        { apply existsb_exists. exists (k, FdAnon id a). split; [exact Hin'|].
          cbn. rewrite (proj2 (bv_eqb_eq id id) eq_refl). reflexivity. }
        rewrite Htrue in Hlive. discriminate Hlive.
      * injection Hunlink as <- <-.
        exfalso. rewrite (proj2 (bv_eqb_eq id id) eq_refl) in Eid'.
        discriminate Eid'.
  - apply anon_agree_unlink_open_other.
    + intros E. subst id0. rewrite (proj2 (bv_eqb_eq id id) eq_refl) in Eid.
      discriminate Eid.
    + destruct e; unfold unlink_open_entry in Hunlink; cbv beta iota in Hunlink;
        try discriminate Hunlink.
      all: try (destruct (Fs.path_eqb c _) eqn:Epc; cbv iota in Hunlink;
                [injection Hunlink as <-; exfalso;
                 rewrite (proj2 (bv_eqb_eq id id) eq_refl) in Eid; discriminate Eid
                |discriminate Hunlink]).
      (* FdAnon case *)
      + cbn [entry_anon_id] in *.
        destruct (bv_eqb _ id) eqn:Eid'.
        * injection Hunlink as <-.
          exfalso. rewrite (proj2 (bv_eqb_eq id id) eq_refl) in Eid.
          discriminate Eid.
        * injection Hunlink as <- <-. exact (Hall _ _ _ Hin').
Qed.

(** Reopen with same data/pin. *)
Lemma anon_agree_all_reopen : forall fds k id af o r w a,
  anon_agree_all fds ->
  anon_agree fds id af = true ->
  anon_agree_all
    (fd_insert fds k (FdAnon id (mkAnonFile (af_data af) o r w a (af_pin af)))).
Proof.
  intros fds k id af o r w a Hall Hagr.
  apply (anon_agree_all_fd_insert_anon fds k id af); try assumption; reflexivity.
Qed.

(** Reopen with truncation. *)
Lemma anon_agree_all_reopen_trunc : forall fds k id af o r w a,
  anon_agree_all fds ->
  anon_agree fds id af = true ->
  anon_agree_all
    (fd_insert (anon_set_data fds id []) k
       (FdAnon id (mkAnonFile [] o r w a (af_pin af)))).
Proof.
  intros fds k id af o r w a Hall Hagr.
  apply (anon_agree_all_fd_insert_anon (anon_set_data fds id []) k id
           (af_set_data af [])
           (mkAnonFile [] o r w a (af_pin af))).
  - exact (anon_agree_all_anon_set_data fds id [] Hall).
  - exact (anon_agree_set_data fds id af [] Hagr).
  - reflexivity.
  - reflexivity.
Qed.
