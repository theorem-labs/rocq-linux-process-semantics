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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad MemImageType StackLayout.
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
    List.In (fd, FdAnon id af) fds ->
    anon_agree fds id af = true.

Definition anon_agree_holds (c : config) : Prop :=
  anon_agree_all (m_fds (cfg_model c)).

(* =========================================================================
   Helper: In under filter and fd_insert
   ========================================================================= *)

Local Lemma In_filter_In (f : word * FdEntry -> bool) (l : list (word * FdEntry)) x :
  List.In x (List.filter f l) -> List.In x l.
Proof.
  induction l as [|h t IH]; [intros []|].
  cbn [List.filter]. destruct (f h).
  - intros [<-|Hin]; [left; reflexivity | right; exact (IH Hin)].
  - intros Hin. right. exact (IH Hin).
Qed.

Local Lemma In_fd_insert_inv fds k e p :
  List.In p (fd_insert fds k e) ->
  p = (k, e) \/ List.In p (List.filter (fun q => negb (bv_eqb (fst q) k)) fds).
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
Lemma anon_agree_all_filter : forall (f : word * FdEntry -> bool) fds,
  anon_agree_all fds -> anon_agree_all (List.filter f fds).
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
  List.In (fd, FdAnon id af') fds ->
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
  - (* Heq : (fd0, FdAnon id0 af0) = (k, FdAnon id af') *)
    assert (fd0 = k) by (congruence). subst fd0.
    assert (id0 = id) by (congruence). subst id0.
    assert (af0 = af') by (congruence). subst af0.
    apply anon_agree_fd_insert.
    + rewrite (anon_agree_congr fds id af' af Hd Hp). exact Hagr.
    + apply anon_entry_agrees_same; reflexivity.
  - pose proof (In_filter_In _ _ _ Hfilt) as Hin0.
    destruct (bv_eqb id0 id) eqn:Eid.
    + apply bv_eqb_eq in Eid. subst id0.
      pose proof (Hall _ _ _ Hin0) as Hagr0.
      pose proof (anon_agree_entry_data_pin _ _ _ _ _ Hagr Hin0) as [Hd0 Hp0].
      apply anon_agree_fd_insert.
      * exact Hagr0.
      * apply anon_entry_agrees_same; congruence.
    + apply anon_agree_fd_insert.
      * exact (Hall _ _ _ Hin0).
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
  - assert (id' = id) by (apply bv_eqb_eq; exact Eid). subst id'.
    assert (fd = k) by congruence. subst fd.
    assert (id0 = id) by congruence. subst id0.
    assert (af0 = f af') by congruence. subst af0.
    apply (anon_agree_update fds id af' f (fun a Ha1 Ha2 => Hf a af' Ha1 Ha2)).
    exact (Hall _ _ _ Hin').
  - assert (fd = k) by congruence. subst fd.
    assert (id0 = id') by congruence. subst id0.
    assert (af0 = af') by congruence. subst af0.
    apply (anon_agree_update_other fds id f id' af').
    + intros E. subst id'. rewrite (proj2 (bv_eqb_eq id id) eq_refl) in Eid.
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
  fd_lookup fds fd = Some e -> List.In (fd, e) fds.
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
      destruct e as [|?? |?? |?? |?? | |?|?? |?? | |??? |?|?|eid eaf|?|???]; try reflexivity.
      rewrite anon_entry_agrees_anon.
      destruct (bv_eqb eid id) eqn:Eid'; [|reflexivity].
      apply bv_eqb_eq in Eid'. subst eid.
      pose proof (fd_lookup_In _ _ _ Hlook) as HinE.
      pose proof (anon_agree_entry_data_pin _ _ _ _ _ Hagr HinE) as [Hd Hp].
      cbn [implb]. rewrite Hd, path_eqb_refl, Hp, anon_pin_eqb_refl. reflexivity.
  - destruct (dup3_moves_entry e) eqn:Emoves; [|discriminate Hdup].
    injection Hdup as <-.
    destruct (In_fd_insert_inv _ _ _ _ Hin) as [Heq | Hfilt].
    + injection Heq as _ Heq. discriminate Heq.
    + pose proof (In_filter_In _ _ _ Hfilt) as HinInner.
      destruct (In_fd_insert_inv _ _ _ _ HinInner) as [Heq2 | Hfilt2].
      * assert (e = FdAnon id af) by congruence. subst e.
        pose proof (fd_lookup_In _ _ _ Hlook) as HinOld.
        pose proof (Hall _ _ _ HinOld) as Hagr.
        eapply anon_agree_dup3_fds; [exact Hlook | | exact Hagr].
        unfold dup3_fds. rewrite Edm, Emoves. reflexivity.
      * pose proof (In_filter_In _ _ _ Hfilt2) as Hin0.
        pose proof (Hall _ _ _ Hin0) as Hagr.
        eapply anon_agree_dup3_fds; [exact Hlook | | exact Hagr].
        unfold dup3_fds. rewrite Edm, Emoves. reflexivity.
Qed.

(** The unlink_open map preserves agreement. *)
Lemma anon_agree_all_unlink_open : forall c fid data pin fds,
  anon_id_live fds fid = false ->
  anon_agree_all fds ->
  anon_agree_all (map (fun q => (fst q, unlink_open_entry c fid data pin (snd q))) fds).
Proof.
  intros c fid data pin fds Hlive Hall.
  unfold anon_agree_all. intros fd0 id0 af0 Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[k e] [Heq Hin']]. cbn [fst snd] in Heq.
  injection Heq as <- Hunlink.
  destruct e; unfold unlink_open_entry in Hunlink; cbv beta iota in Hunlink;
    try discriminate Hunlink.
  (* Named file cases: path_eqb conditional *)
  1-4: (match type of Hunlink with
         | context [path_eqb ?a ?b] =>
           destruct (path_eqb a b) eqn:Epc; cbv iota in Hunlink;
           [ (* converted to FdAnon fid <record> = FdAnon id0 af0 *)
             let Hid := fresh in assert (Hid : id0 = fid) by congruence;
             rewrite Hid in *; clear Hid;
             let Haf := fresh in
             match type of Hunlink with FdAnon _ ?lhs = FdAnon _ ?rhs =>
               assert (Haf : rhs = lhs) by congruence
             end;
             rewrite Haf;
             apply anon_agree_unlink_open; exact Hlive
           | discriminate Hunlink ]
         end; fail).
  (* FdAnon case: unlink_open_entry returns the entry unchanged *)
  - destruct (bv_eqb id0 fid) eqn:Eid0.
    + apply bv_eqb_eq in Eid0. subst id0. exfalso.
      unfold anon_id_live in Hlive.
      assert (existsb (fun p0 => match entry_anon_id (snd p0) with
                                 | Some xid => bv_eqb xid fid
                                 | None => false end) fds = true) as Htrue.
      { apply existsb_exists.
        match type of Hunlink with FdAnon ?x _ = _ =>
          assert (Hx : x = fid) by congruence;
          rewrite Hx in Hin'
        end.
        eexists; split; [exact Hin'|]; cbn.
        rewrite (proj2 (bv_eqb_eq fid fid) eq_refl); reflexivity. }
      rewrite Htrue in Hlive. discriminate Hlive.
    + apply anon_agree_unlink_open_other.
      * intro Habs. exfalso.
        assert (bv_eqb id0 id0 = false) by (rewrite Habs in Eid0 at 1; exact Eid0).
        rewrite (proj2 (bv_eqb_eq id0 id0) eq_refl) in *. discriminate.
      * match type of Hunlink with FdAnon ?x ?y = FdAnon id0 af0 =>
          replace id0 with x by congruence;
          replace af0 with y by congruence
        end.
        exact (Hall _ _ _ Hin').
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

(* =========================================================================
   Syscall preservation
   ========================================================================= *)

Definition arm_preserves_aa (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs ->
    anon_agree_all (m_fds m) ->
    anon_agree_all (m_fds m').

Local Lemma negb_false (b : bool) : negb b = false -> b = true.
Proof. destruct b; [reflexivity | discriminate]. Qed.

Local Ltac find_anon_agree_hyp :=
  match goal with
  | H : negb (anon_agree _ _ _) = false |- _ =>
    apply negb_false in H; exact H
  | H : anon_agree _ _ _ = true |- _ => exact H
  end.

Local Ltac aa_close :=
  match goal with
  | Hinv : anon_agree_all (m_fds ?m) |- anon_agree_all ?g =>
    first
    [ exact Hinv
    | change g with (m_fds m); exact Hinv
    | autorewrite with model; exact Hinv
    | rewrite m_fds_with_fds; exact Hinv
    | rewrite m_fds_with_fds;
      first
      [ apply anon_agree_all_fd_insert_non_anon;
          [intros ?? [=] | exact Hinv ]
      | apply anon_agree_all_fd_remove; exact Hinv
      | apply anon_agree_all_filter; exact Hinv
      | apply anon_agree_all_anon_set_data; exact Hinv
      | apply anon_agree_all_fd_insert_set_off;
          [ exact Hinv | find_anon_agree_hyp ]
      | eapply anon_agree_all_anon_write_back;
          [ exact Hinv | find_anon_agree_hyp ]
      | apply anon_agree_all_set_pin; exact Hinv
      | eapply anon_agree_all_dup3_fds;
          [ eassumption | reflexivity | exact Hinv ]
      | eapply anon_agree_all_reopen;
          [ exact Hinv | find_anon_agree_hyp ]
      | eapply anon_agree_all_reopen_trunc;
          [ exact Hinv | find_anon_agree_hyp ]
      | apply anon_agree_all_fd_insert_non_anon;
          [intros ?? [=] | apply anon_agree_all_fd_insert_non_anon;
            [intros ?? [=] | exact Hinv ] ]
      | apply anon_agree_all_fd_insert_non_anon;
          [intros ?? [=] | apply anon_agree_all_fd_remove; exact Hinv ]
      | apply anon_agree_all_fd_insert_non_anon;
          [intros ?? [=] | apply anon_agree_all_filter; exact Hinv ]
      | apply anon_agree_all_fd_insert_non_anon;
          [intros ?? [=] | apply anon_agree_all_anon_set_data; exact Hinv ]
      ]
    ]
  end.

(* Sub-checker handling: when kf_step gets stuck on a sub-checker call,
   unfold it and let kf_step + aa_close handle the result. *)
Local Ltac aa_done H :=
  match type of H with
  | context [check_efault_or] => unfold check_efault_or in H
  | context [check_sigpipe_write] => unfold check_sigpipe_write in H
  | context [check_sigpipe_writev] => unfold check_sigpipe_writev in H
  | context [check_stream_read] =>
      unfold check_stream_read, check_stream_read_empty, check_stream_read_reset in H
  | context [check_stream_write] => unfold check_stream_write, check_stream_send in H
  | context [check_stream_send] => unfold check_stream_send in H
  | context [check_stream_read_empty] =>
      unfold check_stream_read_empty, check_stream_read_reset in H
  | context [check_eventfd_read] => unfold check_eventfd_read in H
  | context [check_eventfd_write] => unfold check_eventfd_write in H
  | context [check_open_result] => unfold check_open_result, check_new_fd_result in H
  | context [check_new_fd_result] => unfold check_new_fd_result in H
  | context [check_readv_imported] => unfold check_readv_imported in H
  | context [check_read_file_data] => unfold check_read_file_data in H
  | context [check_read_proc] => unfold check_read_proc, check_read_proc_bare in H
  | context [check_read_opaque] => unfold check_read_opaque in H
  | context [check_write_opaque] => unfold check_write_opaque in H
  | context [check_recv_fd_answer] => unfold check_recv_fd_answer in H
  | context [check_access_ok_zero] => unfold check_access_ok_zero in H
  | context [check_socket_pending_error] =>
      unfold check_socket_pending_error, check_access_ok_zero in H
  | context [check_read_urandom] => unfold check_read_urandom in H
  | context [check_anon_write_fault] => unfold check_anon_write_fault in H
  | context [check_anon_fault_extend] => unfold check_anon_fault_extend in H
  | context [check_write_fault_extend] => unfold check_write_fault_extend in H
  | context [check_write_oset] => unfold check_write_oset in H
  | context [check_write_oset_copyins] => unfold check_write_oset_copyins in H
  | context [pipe2_model] => unfold pipe2_model in H
  | context [check_fstat_deliver_by] => unfold check_fstat_deliver_by in H
  | context [check_fstat_deliver] => unfold check_fstat_deliver in H
  | context [check_fstat_anon_deliver] => unfold check_fstat_anon_deliver in H
  | context [check_fstat_file] => unfold check_fstat_file in H
  | context [check_fstat_anon] => unfold check_fstat_anon in H
  | context [check_fstat_opaque] => unfold check_fstat_opaque in H
  | context [check_fstat_chrdev] => unfold check_fstat_chrdev in H
  | context [check_fstat_devnull] => unfold check_fstat_devnull in H
  | context [check_fstat_urandom] => unfold check_fstat_urandom in H
  | context [check_fstat_procfd_dir] => unfold check_fstat_procfd_dir in H
  | context [check_ifreq_writeback] => unfold check_ifreq_writeback in H
  | context [check_siocgifindex] => unfold check_siocgifindex, check_ifreq_writeback in H
  | context [check_errno_or_list] => unfold check_errno_or_list in H
  | context [check_errno_or_success] => unfold check_errno_or_success in H
  | context [check_errno_only] => unfold check_errno_only in H
  | context [check_ret_writes] => unfold check_ret_writes in H
  | context [check_ret_writes_copyins] => unfold check_ret_writes_copyins in H
  | context [check_getrandom_zero] => unfold check_getrandom_zero in H
  | context [check_pid_choice] => unfold check_pid_choice in H
  | context [check_uname_copy] => unfold check_uname_copy in H
  | context [check_rlim64_read] => unfold check_rlim64_read in H
  | context [check_pselect_answer] => unfold check_pselect_answer in H
  | context [check_procfd_getdents] => unfold check_procfd_getdents in H
  | context [check_getdents64_opaque] => unfold check_getdents64_opaque in H
  | context [check_send_on_socket] => unfold check_send_on_socket in H
  | context [check_clone_ns_resolve] =>
      unfold check_clone_ns_resolve, check_clone_ns_answer, check_clone_einval in H
  | context [check_clone3_einval] => unfold check_clone3_einval in H
  | context [check_clone_lists] =>
      unfold check_clone_lists, check_clone_resolve, check_clone_einval in H
  | context [check_clone3_lists] =>
      unfold check_clone3_lists, check_clone3_resolve, check_clone3_einval in H
  | context [check_clone_resolve] => unfold check_clone_resolve in H
  | context [check_clone3_resolve] => unfold check_clone3_resolve in H
  | context [check_clone_answer] => unfold check_clone_answer in H
  | context [check_refusable] => unfold check_refusable in H
  | context [check_setid_result] => unfold check_setid_result in H
  | context [check_tkill_self] => unfold check_tkill_self, check_send_sigabrt in H
  | context [check_kill_self] => unfold check_kill_self in H
  | context [check_shutdown_core] =>
      unfold check_shutdown_core, check_stream_shutdown in H
  | context [check_setsockopt_core] =>
      unfold check_setsockopt_core, check_stream_setsockopt, check_seqpacket_setsockopt in H
  | context [check_getsockopt_core] =>
      unfold check_getsockopt_core, check_stream_getsockopt in H
  | context [check_getsockname_core] =>
      unfold check_getsockname_core, check_stream_getname in H
  | context [check_getpeername_core] =>
      unfold check_getpeername_core, check_stream_getname in H
  | context [check_stream_getname] => unfold check_stream_getname in H
  | context [check_stream_getsockopt] => unfold check_stream_getsockopt in H
  | context [Open.check_openat_read] => unfold Open.check_openat_read in H
  | context [Open.check_openat_create] => unfold Open.check_openat_create in H
  | context [Open.check_openat_dir] => unfold Open.check_openat_dir in H
  | context [Open.check_openat_localtime] => unfold Open.check_openat_localtime in H
  | context [Open.check_open_devnull] => unfold Open.check_open_devnull in H
  | context [Open.check_openat_devnull] => unfold Open.check_openat_devnull in H
  | context [Open.check_open_urandom] => unfold Open.check_open_urandom in H
  | context [Open.check_openat_urandom] => unfold Open.check_openat_urandom in H
  | context [Open.check_proc_open_result] => unfold Open.check_proc_open_result in H
  | context [Open.check_openat_procfd] => unfold Open.check_openat_procfd in H
  | context [Open.check_openat_proc] => unfold Open.check_openat_proc in H
  | context [check_openat_table] => unfold check_openat_table in H
  | context [check_create_wronly] => unfold check_create_wronly in H
  | context [check_open_append] => unfold check_open_append in H
  | context [check_open_rdwr] => unfold check_open_rdwr in H
  | context [check_mmap_fixed_overflow] => unfold check_mmap_fixed_overflow in H
  | context [Namei.check_unlink_open_tmp] =>
      unfold Namei.check_unlink_open_tmp, check_unlink_open_result, check_unlink_type_result in H
  | context [check_dup_result] => unfold check_dup_result in H
  | context [check_newfstatat_proc_errno] => unfold check_newfstatat_proc_errno in H
  | context [check_newfstatat_proc] => unfold check_newfstatat_proc in H
  | context [check_capget_copy] => unfold check_capget_copy in H
  | context [check_futex_wake_private] =>
      unfold check_futex_wake_private, check_futex_wait_private in H
  | context [Prelude.check_copyins_after] => apply check_copyins_after_model in H
  | context [check_copyin_prefix] => apply check_copyin_prefix_model in H
  | context [check_copyins] => apply check_copyins_model in H
  | context [check_access_exists] => unfold check_access_exists in H
  | context [Open.check_faccessat_body] => unfold Open.check_faccessat_body, check_access_exists in H
  | context [share_eventfds] => unfold share_eventfds in H
  | context [check_seqpacket_setsockopt] => unfold check_seqpacket_setsockopt in H
  | context [check_seqpacket_recvmsg] => unfold check_seqpacket_recvmsg in H
  | context [check_recvmsg_eof_writes] => unfold check_recvmsg_eof_writes in H
  | context [check_rt_sigaction_sigpipe] =>
      unfold check_rt_sigaction_sigpipe, check_sigpipe_oact_write in H
  | context [check_sigpipe_oact_write] => unfold check_sigpipe_oact_write in H
  | context [check_one_write] => unfold check_one_write in H
  | context [check_clock_getres_result] => unfold check_clock_getres_result in H
  | context [anon_place_fds] => unfold anon_place_fds in H
  | context [check_wait4_store] => unfold check_wait4_store in H
  | context [open_cloexec_model] => unfold open_cloexec_model in H
  end.

(* Unfold the top-level check function in H so that kf_step can see
   the match/if structure.  We add the top-level names to aa_done
   so that the repeat loop handles both levels of unfolding. *)
Local Ltac aa_done_or_unfold H :=
  first
  [ aa_done H
  | (* Top-level check functions: unfold when kf_step gets stuck *)
    match type of H with
    | context [check_getcwd] => unfold check_getcwd in H
    | context [check_eventfd2] => unfold check_eventfd2 in H
    | context [check_epoll_create1] => unfold check_epoll_create1 in H
    | context [check_epoll_ctl] => unfold check_epoll_ctl in H
    | context [check_epoll_pwait] => unfold check_epoll_pwait in H
    | context [check_dup] => unfold check_dup in H
    | context [check_dup3] => unfold check_dup3 in H
    | context [check_fcntl] => unfold check_fcntl in H
    | context [check_ioctl] => unfold check_ioctl in H
    | context [check_flock] => unfold check_flock in H
    | context [check_unlinkat] => unfold check_unlinkat in H
    | context [check_ftruncate] => unfold check_ftruncate in H
    | context [check_faccessat] => unfold check_faccessat in H
    | context [check_openat] => unfold check_openat in H
    | context [check_close] => unfold check_close in H
    | context [check_pipe2] => unfold check_pipe2 in H
    | context [check_getdents64] => unfold check_getdents64 in H
    | context [check_lseek] => unfold check_lseek in H
    | context [check_read] => unfold check_read in H
    | context [check_write] => unfold check_write in H
    | context [check_readv] => unfold check_readv in H
    | context [check_writev] => unfold check_writev in H
    | context [check_pread64] => unfold check_pread64 in H
    | context [check_pwrite64] => unfold check_pwrite64 in H
    | context [check_pselect6] => unfold check_pselect6 in H
    | context [check_ppoll] => unfold check_ppoll in H
    | context [check_signalfd4] => unfold check_signalfd4 in H
    | context [check_readlinkat] => unfold check_readlinkat in H
    | context [check_newfstatat] => unfold check_newfstatat in H
    | context [check_fstat] => unfold check_fstat in H
    | context [check_fsync] => unfold check_fsync in H
    | context [check_timerfd_create] => unfold check_timerfd_create in H
    | context [check_capget] => unfold check_capget in H
    | context [check_capset] => unfold check_capset in H
    | context [check_exit] => unfold check_exit in H
    | context [check_set_tid_address] => unfold check_set_tid_address in H
    | context [check_futex] => unfold check_futex in H
    | context [check_set_robust_list] => unfold check_set_robust_list in H
    | context [check_nanosleep] => unfold check_nanosleep in H
    | context [check_clock_gettime] => unfold check_clock_gettime in H
    | context [check_clock_getres] => unfold check_clock_getres in H
    | context [check_sched_setscheduler] => unfold check_sched_setscheduler in H
    | context [check_sched_getaffinity] => unfold check_sched_getaffinity in H
    | context [check_sched_yield] => unfold check_sched_yield in H
    | context [check_kill] => unfold check_kill in H
    | context [check_tkill] => unfold check_tkill in H
    | context [check_tgkill] => unfold check_tgkill in H
    | context [check_sigaltstack] => unfold check_sigaltstack in H
    | context [check_rt_sigaction] => unfold check_rt_sigaction in H
    | context [check_rt_sigprocmask] => unfold check_rt_sigprocmask in H
    | context [check_setsid] => unfold check_setsid in H
    | context [check_setid] => unfold check_setid in H
    | context [check_setresid] => unfold check_setresid in H
    | context [check_getresid] => unfold check_getresid in H
    | context [check_getsid] => unfold check_getsid in H
    | context [check_getgroups] => unfold check_getgroups in H
    | context [check_setgroups] => unfold check_setgroups in H
    | context [check_uname] => unfold check_uname in H
    | context [check_prctl] => unfold check_prctl in H
    | context [check_gettimeofday] => unfold check_gettimeofday in H
    | context [check_getpid] => unfold check_getpid in H
    | context [check_getppid] => unfold check_getppid in H
    | context [check_getid] => unfold check_getid in H
    | context [check_gettid] => unfold check_gettid in H
    | context [check_socket] => unfold check_socket in H
    | context [check_socketpair] => unfold check_socketpair in H
    | context [check_bind] => unfold check_bind in H
    | context [check_listen] => unfold check_listen in H
    | context [check_accept4] => unfold check_accept4 in H
    | context [check_connect] => unfold check_connect in H
    | context [check_getsockname] => unfold check_getsockname in H
    | context [check_getpeername] => unfold check_getpeername in H
    | context [check_sendto] => unfold check_sendto in H
    | context [check_recvfrom] => unfold check_recvfrom in H
    | context [check_setsockopt] => unfold check_setsockopt in H
    | context [check_getsockopt] => unfold check_getsockopt in H
    | context [check_shutdown] => unfold check_shutdown in H
    | context [check_sendmsg] => unfold check_sendmsg in H
    | context [check_recvmsg] => unfold check_recvmsg in H
    | context [check_brk] => unfold check_brk in H
    | context [check_munmap] => unfold check_munmap in H
    | context [check_mremap] => unfold check_mremap in H
    | context [check_clone] => unfold check_clone in H
    | context [check_mmap] => unfold check_mmap in H
    | context [check_mprotect] => unfold check_mprotect in H
    | context [check_madvise] => unfold check_madvise in H
    | context [check_wait4] => unfold check_wait4 in H
    | context [check_prlimit64] => unfold check_prlimit64 in H
    | context [check_setns] => unfold check_setns in H
    | context [check_getrandom] => unfold check_getrandom in H
    | context [check_pwritev2] => unfold check_pwritev2 in H
    | context [check_clone3] => unfold check_clone3 in H
    | context [check_close_range] => unfold check_close_range in H
    | context [check_faccessat2] => unfold check_faccessat2 in H
    end
  ].

Local Ltac aa_frame H :=
  cbv beta iota zeta in H;
  repeat (kf_step H || aa_done_or_unfold H || (aa_close; fail 2));
  aa_close.

(* Test: single arm to verify the tactic works *)
Lemma check_getcwd_preserves_aa : arm_preserves_aa arm_getcwd.
Proof.
  unfold arm_preserves_aa. intros i eff m m' evs H Hinv.
  autorewrite with arm_unfold in H.
  unfold check_getcwd in H. cbv beta iota zeta in H.
  repeat (kf_step H || aa_done H || (aa_close; fail 2)).
  aa_close.
Qed.

Lemma check_close_preserves_aa : arm_preserves_aa arm_close.
Proof.
  unfold arm_preserves_aa. intros i eff m m' evs H Hinv.
  autorewrite with arm_unfold in H.
  unfold check_close in H. cbv beta iota zeta in H.
  repeat (kf_step H || aa_done H || (aa_close; fail 2)).
  aa_close.
Qed.

Lemma check_write_preserves_aa : arm_preserves_aa arm_write.
Proof.
  unfold arm_preserves_aa. intros i eff m m' evs H Hinv.
  autorewrite with arm_unfold in H.
  unfold check_write in H. cbv beta iota zeta in H.
  repeat (kf_step H || aa_done H || (aa_close; fail 2)).
  aa_close.
Qed.

Lemma checked_table_preserves_aa : Forall arm_preserves_aa checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_preserves_aa).
  all: unfold arm_preserves_aa; intros i eff m m' evs H Hinv;
       autorewrite with arm_unfold in H.
  all: try (aa_frame H; fail).
  all: fail 1
    "checked_table_preserves_aa has no case for this dispatcher arm".
Qed.

Corollary syscall_spec_preserves_anon_agree : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  anon_agree_all (m_fds m) -> anon_agree_all (m_fds m').
Proof.
  intros i m eff m' evs H Hinv.
  apply check_syscall_ok_iff in H.
  unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_preserves_aa as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H Hinv).
Qed.

(* =========================================================================
   The initial configuration, sstep and star
   ========================================================================= *)

(** The initial model has no [FdAnon] entries. *)
Theorem anon_agree_init : forall segs pc ph sp brk0 mb draw lim inp,
  anon_agree_holds (init_config segs pc ph sp brk0 mb draw lim inp).
Proof.
  intros. unfold anon_agree_holds, anon_agree_all, init_config. cbn [cfg_model].
  intros fd id af Hin.
  exact (anon_agree_init_model (segments_reserved segs)
           brk0 mb sp lim inp id af).
Qed.

(** One transition preserves [anon_agree_holds]. *)
Lemma sstep_preserves_anon_agree : forall segs c evs c',
  anon_agree_holds c -> sstep segs c evs (SNext c') -> anon_agree_holds c'.
Proof.
  intros segs [ms model] evs c' Hinv Hstep.
  unfold anon_agree_holds in *. cbn [cfg_model] in *.
  inversion Hstep; subst; cbn [cfg_model].
  - (* sstep_instr *)
    match goal with
    | [ H : mi_account_step _ _ _ = RiscvSemantics.MachineOk (_, _) |- _ ] =>
        destruct (mi_account_step_model_frame _ _ _ _ _ H) as (Hfd & _)
    end.
    unfold anon_agree_all in *. intros fd id af Hin.
    assert (Hfds : m_fds model' = m_fds model)
      by (unfold m_fds; rewrite Hfd; reflexivity).
    rewrite Hfds in Hin |- *. exact (Hinv fd id af Hin).
  - (* sstep_vdso_call *)
    match goal with
    | [ Hs : syscall_spec _ _ (Ok _ ?m1 _),
        Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ ] =>
        destruct (materialize_model_accesses_frame _ _ _ Hm) as (Hfd2 & _);
        assert (Hfds : m_fds (with_vdso_bump m2) = m_fds m1);
        [ unfold m_fds; unfold with_vdso_bump, with_vdso; rewrite Hfd2; reflexivity |];
        unfold anon_agree_all in *; intros fd id af Hin;
        rewrite Hfds in Hin |- *;
        exact (syscall_spec_preserves_anon_agree _ _ _ _ _ Hs Hinv fd id af Hin)
    end.
  - (* sstep_syscall *)
    match goal with
    | [ Hs : syscall_spec _ _ (Ok _ ?m1 _),
        Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ ] =>
        destruct (materialize_model_accesses_frame _ _ _ Hm) as (Hfd2 & _);
        assert (Hfds : m_fds m2 = m_fds m1)
          by (unfold m_fds; rewrite Hfd2; reflexivity);
        unfold anon_agree_all in *; intros fd id af Hin;
        rewrite Hfds in Hin |- *;
        exact (syscall_spec_preserves_anon_agree _ _ _ _ _ Hs Hinv fd id af Hin)
    end.
  - (* sstep_exit *)
    match goal with
    | [ Hs : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        exact (syscall_spec_preserves_anon_agree _ _ _ _ _ Hs Hinv)
    end.
  - (* sstep_killed *)
    match goal with
    | [ Hs : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        exact (syscall_spec_preserves_anon_agree _ _ _ _ _ Hs Hinv)
    end.
Qed.

(** A whole execution preserves the invariant. *)
Theorem star_preserves_anon_agree : forall segs c tr c',
  star segs c tr c' -> anon_agree_holds c -> anon_agree_holds c'.
Proof.
  intros segs.
  exact (star_invariant segs anon_agree_holds (sstep_preserves_anon_agree segs)).
Qed.

(** The invariant holds at every reachable configuration. *)
Theorem anon_agree_reachable : forall segs pc ph sp brk0 mb draw lim inp tr c,
  star segs (init_config segs pc ph sp brk0 mb draw lim inp) tr c ->
  anon_agree_holds c.
Proof.
  intros segs pc ph sp brk0 mb draw lim inp tr c Hstar.
  exact (star_preserves_anon_agree segs _ _ _ Hstar
           (anon_agree_init segs pc ph sp brk0 mb draw lim inp)).
Qed.
