(** * LinuxProcessSem.Checks.Sys.Fs.Select — the pselect6 (72) and ppoll (73) checkers, and their proofs

    Mirrors [Sys/Fs/Select.v], which answers to Linux [fs/select.c]: this
    file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

(** pselect6: deterministic throughout the modeled band, so the acceptor
    is the spec's own computation plus one equality, on the return, the
    writes and the copy-from-user ledger [Select.pselect6_reads].
    Everything that makes this syscall hard -- readiness, the timeout
    write-back, the [fdt->max_fds] clamp, a real signal mask -- is decided
    by [Select.pselect6_outcome] answering [None], which is
    [CheckUnmodeled] here. *)
Definition check_pselect6 (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | None => CheckUnmodeled
  | Some (r, ws) =>
      match eff with
      | mkEffectU r' ws' [] [] [] ks =>
          if bv_eqb r' r && writes_eqb ws' ws
             && access_ranges_eqb ks (pselect6_reads i n32 inp outp exp tsp sig)
          then CheckOk m [] else CheckReject
      | _ => CheckReject
      end
  end.

Lemma check_pselect6_sound_ok :
  forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs ->
  pselect6_spec n32 inp outp exp tsp sig i m (Ok eff m' evs).
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold check_pselect6 in H. unfold pselect6_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [[r ws]|] eqn:Ho;
    cbv iota; [|discriminate].
  destruct eff as [r' ws' zs us cs ks].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r' r && writes_eqb ws' ws
            && access_ranges_eqb ks (pselect6_reads i n32 inp outp exp tsp sig))
    eqn:Hg; [|discriminate].
  apply Bool.andb_true_iff in Hg. destruct Hg as [Hg Hk].
  apply Bool.andb_true_iff in Hg. destruct Hg as [Hr Hw].
  apply bv_eqb_eq in Hr. apply writes_eqb_eq in Hw.
  apply access_ranges_eqb_eq in Hk. subst r' ws' ks.
  injection H as <- <-. apply pure_ok.
Qed.

Lemma check_pselect6_sound_unmodeled :
  forall i n32 inp outp exp tsp sig eff m,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckUnmodeled ->
  pselect6_spec n32 inp outp exp tsp sig i m Unmodeled.
Proof.
  intros i n32 inp outp exp tsp sig eff m H.
  unfold check_pselect6 in H. unfold pselect6_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [[r ws]|] eqn:Ho;
    cbv iota; [|apply unmodeled_intro].
  destruct eff as [r' ws' zs us cs ks].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r' r && writes_eqb ws' ws
            && access_ranges_eqb ks (pselect6_reads i n32 inp outp exp tsp sig));
    discriminate.
Qed.

Lemma check_pselect6_complete_ok :
  forall i n32 inp outp exp tsp sig eff m m' evs,
  pselect6_spec n32 inp outp exp tsp sig i m (Ok eff m' evs) ->
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold pselect6_spec in H. unfold check_pselect6. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [[r ws]|] eqn:Ho;
    hall Ho; inv_ok.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
  rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl),
    access_ranges_eqb_refl.
  reflexivity.
Qed.

Lemma check_pselect6_complete_unmodeled :
  forall i n32 inp outp exp tsp sig m eff,
  pselect6_spec n32 inp outp exp tsp sig i m Unmodeled ->
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckUnmodeled.
Proof.
  intros i n32 inp outp exp tsp sig m eff H.
  unfold pselect6_spec in H. unfold check_pselect6. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [[r ws]|] eqn:Ho;
    hall Ho; inv_ok; reflexivity.
Qed.

(* -------------------------------------------------------------------------
   ppoll (73)
   ------------------------------------------------------------------------- *)

(** Where the plan is decided, the acceptor is the spec's own answer
    plus one equality, the ledger [Select.ppoll_reads] included, exactly
    as for pselect6.  Where it reaches [do_poll], the acceptor reads the
    observed [revents] off the effect's writes ([ppoll_pick]), requires
    each to be admitted by its entry, and compares the whole effect with
    [Select.ppoll_finish]'s answer for that choice.  The gate
    [Select.ppoll_all_answered] is the spec's own, so a call the spec
    declines is [CheckUnmodeled] here. *)

(** The effect is [r] and [ws] under the ledger [reads], and nothing
    else. *)
Definition check_ppoll_eff (reads : list (word * nat)) (r : word)
    (ws : list (word * list byte)) (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU r' ws' [] [] [] ks =>
      if bv_eqb r' r && writes_eqb ws' ws && access_ranges_eqb ks reads
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

Local Lemma check_ppoll_eff_ok : forall reads r ws eff m m' evs,
  check_ppoll_eff reads r ws eff m = CheckOk m' evs ->
  eff = with_copyins reads (mkEffect r ws []) /\ m' = m /\ evs = [].
Proof.
  intros reads r ws eff m m' evs H. unfold check_ppoll_eff in H.
  destruct eff as [r' ws' zs us cs ks].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r' r && writes_eqb ws' ws && access_ranges_eqb ks reads)
    eqn:Hg; [|discriminate].
  apply Bool.andb_true_iff in Hg. destruct Hg as [Hg Hk].
  apply Bool.andb_true_iff in Hg. destruct Hg as [Hr Hw].
  apply bv_eqb_eq in Hr. apply writes_eqb_eq in Hw.
  apply access_ranges_eqb_eq in Hk. subst r' ws' ks.
  injection H as <- <-. split; [reflexivity | split; reflexivity].
Qed.

Local Lemma check_ppoll_eff_no_unmodeled : forall reads r ws eff m,
  check_ppoll_eff reads r ws eff m <> CheckUnmodeled.
Proof.
  intros reads r ws [r' ws' zs us cs ks] m. unfold check_ppoll_eff.
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r' r && writes_eqb ws' ws && access_ranges_eqb ks reads);
    discriminate.
Qed.

Local Lemma check_ppoll_eff_refl : forall reads r ws m,
  check_ppoll_eff reads r ws (with_copyins reads (mkEffect r ws [])) m = CheckOk m [].
Proof.
  intros reads r ws m. unfold check_ppoll_eff, with_copyins.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
  rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl),
    access_ranges_eqb_refl.
  reflexivity.
Qed.

(** The [revents] value the 2-byte write [b] stores, among the entry's
    admissible ones [s]. *)
Definition ppoll_pick_one (s : list Z) (b : list byte) : option Z :=
  find (fun r => listN_eqb (word_le2 (Z_to_bv 64 r)) b) s.

(** The observed choice: one value per entry, read off the writes in
    entry order, or [None] where a write stores no admissible value. *)
Fixpoint ppoll_pick (sets : list (list Z)) (ws : list (word * list byte))
    : option (list Z) :=
  match sets with
  | [] => Some []
  | s :: sets' =>
      match ws with
      | [] => None
      | w :: ws' =>
          match ppoll_pick_one s (snd w), ppoll_pick sets' ws' with
          | Some r, Some rs => Some (r :: rs)
          | _, _ => None
          end
      end
  end.

Definition check_ppoll (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match ppoll_plan i m ufds nfds tsp sig sigsetsize with
  | PpDecided None => CheckUnmodeled
  | PpDecided (Some (r, ws)) =>
      check_ppoll_eff (ppoll_reads i m ufds nfds tsp sig sigsetsize) r ws eff m
  | PpPoll tmo sets =>
      if negb (ppoll_all_answered i ufds nfds tsp tmo sets) then CheckUnmodeled
      else
        match ppoll_pick sets (eff_writes eff) with
        | None => CheckReject
        | Some rs =>
            match ppoll_finish i ufds nfds tsp tmo rs with
            | None => CheckReject
            | Some (r, ws) =>
                check_ppoll_eff (ppoll_reads i m ufds nfds tsp sig sigsetsize) r ws eff m
            end
        end
  end.

(** ** What the observed choice is *)

(** A picked choice is a choice. *)
Local Lemma ppoll_pick_choice : forall sets ws rs,
  ppoll_pick sets ws = Some rs -> ppoll_choice_in sets rs = true.
Proof.
  induction sets as [|s sets IH]; intros ws rs H.
  - cbn in H. injection H as <-. reflexivity.
  - destruct ws as [|w ws]; [discriminate H|].
    cbn [ppoll_pick] in H.
    destruct (ppoll_pick_one s (snd w)) as [r|] eqn:E1; cbv iota in H;
      [|discriminate H].
    destruct (ppoll_pick sets ws) as [rs'|] eqn:E2; cbv iota in H;
      [|discriminate H].
    injection H as <-. cbn [ppoll_choice_in].
    apply Bool.andb_true_iff. split; [|exact (IH _ _ E2)].
    unfold ppoll_pick_one in E1. apply find_some in E1 as [Hin _].
    apply existsb_exists. exists r. split; [exact Hin | apply Z.eqb_refl].
Qed.

(** No two admissible values of one entry store the same two bytes. *)
Definition ppoll_set_inj (s : list Z) : Prop :=
  forall r r', In r s -> In r' s ->
  listN_eqb (word_le2 (Z_to_bv 64 r')) (word_le2 (Z_to_bv 64 r)) = true -> r' = r.

Local Lemma ppoll_set_inj_single : forall v, ppoll_set_inj [v].
Proof.
  intros v. unfold ppoll_set_inj. intros r r' Hr Hr' _.
  destruct Hr as [<-|[]]; destruct Hr' as [<-|[]]; reflexivity.
Qed.

Local Lemma ppoll_set_inj_eventfd :
  ppoll_set_inj [0%Z; POLLIN; Z.lor POLLIN POLLERR].
Proof.
  unfold ppoll_set_inj. intros r r' Hr Hr' Hb. cbn [In] in Hr, Hr'.
  destruct Hr as [<-|[<-|[<-|[]]]]; destruct Hr' as [<-|[<-|[<-|[]]]];
    try reflexivity; vm_compute in Hb; discriminate Hb.
Qed.

Local Lemma ppoll_set_inj_signalfd : ppoll_set_inj [0%Z; POLLIN].
Proof.
  unfold ppoll_set_inj. intros r r' Hr Hr' Hb. cbn [In] in Hr, Hr'.
  destruct Hr as [<-|[<-|[]]]; destruct Hr' as [<-|[<-|[]]];
    try reflexivity; vm_compute in Hb; discriminate Hb.
Qed.

Local Lemma ppoll_revents_of_inj : forall m fd ev s,
  ppoll_revents_of m fd ev = Some s -> ppoll_set_inj s.
Proof.
  intros m fd ev s H. unfold ppoll_revents_of in H.
  destruct (fd <? 0)%Z; cbv iota in H.
  { injection H as <-. apply ppoll_set_inj_single. }
  destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [e|]; cbv iota in H.
  2:{ injection H as <-. apply ppoll_set_inj_single. }
  destruct e; cbv iota in H; try discriminate H;
    try (injection H as <-; apply ppoll_set_inj_single).
  (* the opaque kinds *)
  unfold ppoll_opaque_revents in H.
  destruct o; cbv iota in H; try discriminate H.
  - (* an eventfd *)
    destruct (Z.eqb ev POLLIN); cbv iota in H; [|discriminate H].
    injection H as <-. apply ppoll_set_inj_eventfd.
  - (* a signalfd *)
    destruct (negb (Z.eqb ev POLLIN)); cbv iota in H; [discriminate H|].
    destruct (signalfd_other_may_pend mask m); cbv iota in H; [discriminate H|].
    destruct (signalfd_sigchld_may_pend mask m); cbv iota in H; injection H as <-;
      [apply ppoll_set_inj_signalfd | apply ppoll_set_inj_single].
Qed.

Local Lemma ppoll_revents_inj : forall m es sets,
  ppoll_revents m es = Some sets -> Forall ppoll_set_inj sets.
Proof.
  intros m. induction es as [|[fd ev] es IH]; intros sets H.
  - cbn in H. injection H as <-. constructor.
  - cbn [ppoll_revents] in H.
    destruct (ppoll_revents_of m fd ev) as [s|] eqn:E1; cbv iota in H;
      [|discriminate H].
    destruct (ppoll_revents m es) as [ss|] eqn:E2; cbv iota in H;
      [|discriminate H].
    injection H as <-.
    constructor; [exact (ppoll_revents_of_inj _ _ _ _ E1) | exact (IH _ eq_refl)].
Qed.

Local Lemma ppoll_core_inj : forall i m ufds nfds sets,
  ppoll_core i m ufds nfds = PpCorePoll sets -> Forall ppoll_set_inj sets.
Proof.
  intros i m ufds nfds sets H. unfold ppoll_core in H. cbv zeta in H.
  do 3 (match type of H with
        | context [if ?b then _ else _] => destruct b; cbv iota in H; [discriminate H|]
        end).
  match type of H with
  | context [read_bytes_map ?a ?b ?c] => destruct (read_bytes_map a b c) as [bs|]
  end; cbv iota in H; [|discriminate H].
  match type of H with
  | context [ppoll_revents ?m0 ?es] => destruct (ppoll_revents m0 es) as [ss|] eqn:E
  end; cbv iota in H; [|discriminate H].
  injection H as <-. exact (ppoll_revents_inj _ _ _ E).
Qed.

(** What [Select.ppoll_finish] answers writes the choice's write-back
    first, or nothing at all where the range test refused. *)
Local Lemma ppoll_finish_writes : forall i ufds nfds tsp tmo rs r ws,
  ppoll_finish i ufds nfds tsp tmo rs = Some (r, ws) ->
  (exists x, ws = ppoll_writeback ufds rs ++ x)
  \/ (ws = [] /\ access_okb ufds (pollfd_bytes * bv_unsigned nfds) = false).
Proof.
  intros i ufds nfds tsp tmo rs r ws H.
  unfold ppoll_finish, ppoll_writeback_access in H.
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)) eqn:Ha.
  - left. unfold pselect_finish, pselect_writes in H.
    destruct tmo; cbv iota in H; try discriminate H.
    + destruct (Z.eqb (ppoll_count rs) 0); cbv iota in H; [discriminate H|].
      destruct (writes_all_writable i (ppoll_writeback ufds rs)); cbv iota in H;
        [|discriminate H].
      injection H as _ <-. exists []. rewrite app_nil_r. reflexivity.
    + destruct (writes_all_writable i (ppoll_writeback ufds rs)); cbv iota in H;
        [|discriminate H].
      injection H as _ <-. exists []. rewrite app_nil_r. reflexivity.
    + destruct (Z.eqb (ppoll_count rs) 0); cbv iota in H; [|discriminate H].
      destruct (writes_all_writable i
                  (ppoll_writeback ufds rs ++ [(tsp, pselect_timespec_zero)]));
        cbv iota in H; [|discriminate H].
      injection H as _ <-. eexists. reflexivity.
  - right. split; [|reflexivity].
    unfold pselect_finish, pselect_err in H.
    destruct tmo; cbv iota in H; try discriminate H;
      try (destruct (Z.eqb (ppoll_count rs) 0); cbv iota in H; try discriminate H);
      injection H as _ <-; reflexivity.
Qed.

(** The picked choice of an answered effect is the choice that made it. *)
Local Lemma ppoll_pick_writeback : forall sets rs p x,
  ppoll_choice_in sets rs = true -> Forall ppoll_set_inj sets ->
  ppoll_pick sets (ppoll_writeback p rs ++ x) = Some rs.
Proof.
  induction sets as [|s sets IH]; intros rs p x Hc Hinj.
  - destruct rs; [reflexivity | discriminate Hc].
  - destruct rs as [|r rs]; [discriminate Hc|].
    cbn [ppoll_choice_in] in Hc. apply Bool.andb_true_iff in Hc as [Hr Hc].
    inversion Hinj as [|s0 sets0 Hs Hinj']; subst.
    cbn [ppoll_writeback app ppoll_pick snd].
    rewrite (IH rs _ x Hc Hinj').
    assert (E : ppoll_pick_one s (word_le2 (Z_to_bv 64 r)) = Some r).
    { unfold ppoll_pick_one.
      apply existsb_exists in Hr as (r0 & Hin0 & Heq0).
      apply Z.eqb_eq in Heq0. subst r0.
      destruct (find (fun r' => listN_eqb (word_le2 (Z_to_bv 64 r'))
                                          (word_le2 (Z_to_bv 64 r))) s)
        as [r'|] eqn:Ef.
      - apply find_some in Ef as [Hin' Hb]. f_equal. exact (Hs r r' Hin0 Hin' Hb).
      - exfalso. eapply find_none in Ef; [|exact Hin0]. cbv beta in Ef.
        rewrite (proj2 (listN_eqb_eq _ _) eq_refl) in Ef. discriminate Ef. }
    rewrite E. reflexivity.
Qed.

Local Lemma ppoll_pick_finish :
  forall i m ufds nfds tsp sig sigsetsize tmo sets rs r ws,
  ppoll_plan i m ufds nfds tsp sig sigsetsize = PpPoll tmo sets ->
  ppoll_choice_in sets rs = true ->
  ppoll_finish i ufds nfds tsp tmo rs = Some (r, ws) ->
  ppoll_pick sets ws = Some rs.
Proof.
  intros i m ufds nfds tsp sig sigsetsize tmo sets rs r ws Hp Hc Hf.
  destruct (ppoll_plan_poll _ _ _ _ _ _ _ _ _ Hp) as [Hcore _].
  destruct (ppoll_finish_writes _ _ _ _ _ _ _ _ Hf) as [(x & ->) | (-> & Ha)].
  - exact (ppoll_pick_writeback _ _ _ _ Hc (ppoll_core_inj _ _ _ _ _ Hcore)).
  - pose proof (proj2 (ppoll_core_poll _ _ _ _ _ Hcore) Ha) as Hs. subst sets.
    destruct rs; [reflexivity | discriminate Hc].
Qed.

(** Every answer [check_ppoll] accepts leaves the model as it was and
    emits nothing. *)
Lemma check_ppoll_model : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  m' = m /\ evs = [].
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H.
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[[r ws]|]|tmo sets];
    cbv iota in H.
  - apply check_ppoll_eff_ok in H. destruct H as (_ & -> & ->). split; reflexivity.
  - discriminate H.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo sets)); cbv iota in H;
      [discriminate H|].
    destruct (ppoll_pick sets (eff_writes eff)) as [rs|]; cbv iota in H;
      [|discriminate H].
    destruct (ppoll_finish i ufds nfds tsp tmo rs) as [[r ws]|]; cbv iota in H;
      [|discriminate H].
    apply check_ppoll_eff_ok in H. destruct H as (_ & -> & ->). split; reflexivity.
Qed.

(** ** The four agreement lemmas *)

Lemma check_ppoll_sound_ok :
  forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs).
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H. unfold ppoll_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[[r ws]|]|tmo sets]
    eqn:Hp; cbv iota in H |- *.
  - apply check_ppoll_eff_ok in H. destruct H as (-> & -> & ->). apply pure_ok.
  - discriminate H.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo sets)) eqn:Ha;
      cbv beta iota in H |- *; [discriminate H|].
    destruct (ppoll_pick sets (eff_writes eff)) as [rs|] eqn:Hk; cbv iota in H;
      [|discriminate H].
    destruct (ppoll_finish i ufds nfds tsp tmo rs) as [[r ws]|] eqn:Hf;
      cbv iota in H; [|discriminate H].
    apply check_ppoll_eff_ok in H. destruct H as (-> & -> & ->).
    eapply bind_ok0.
    + apply (choose_ok _ (r, ws)). exists rs.
      split; [exact (ppoll_pick_choice _ _ _ Hk) | exact Hf].
    + cbv beta. cbn [fst snd]. apply pure_ok.
Qed.

Lemma check_ppoll_sound_unmodeled :
  forall i ufds nfds tsp sig sigsetsize eff m,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckUnmodeled ->
  ppoll_spec ufds nfds tsp sig sigsetsize i m Unmodeled.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m H.
  unfold check_ppoll in H. unfold ppoll_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[[r ws]|]|tmo sets]
    eqn:Hp; cbv iota in H |- *.
  - exfalso. exact (check_ppoll_eff_no_unmodeled _ _ _ _ _ H).
  - apply unmodeled_intro.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo sets)) eqn:Ha;
      cbv beta iota in H |- *; [apply unmodeled_intro|].
    exfalso.
    destruct (ppoll_pick sets (eff_writes eff)) as [rs|]; cbv iota in H;
      [|discriminate H].
    destruct (ppoll_finish i ufds nfds tsp tmo rs) as [[r ws]|]; cbv iota in H;
      [|discriminate H].
    exact (check_ppoll_eff_no_unmodeled _ _ _ _ _ H).
Qed.

Lemma check_ppoll_complete_ok :
  forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs) ->
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold ppoll_spec in H. apply bind_input_model_inv in H. cbv beta in H.
  unfold check_ppoll.
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[[r ws]|]|tmo sets]
    eqn:Hp; cbv iota in H |- *.
  - unfold pure in H. inversion H; clear H; subst. apply check_ppoll_eff_refl.
  - unfold unmodeled in H. discriminate H.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo sets)) eqn:Ha;
      cbv beta iota in H |- *; [unfold unmodeled in H; discriminate H|].
    unfold bind, choose, pure in H. cbv beta iota in H.
    destruct H as (rw & m1 & evs1 & evs2 & Hch & Hk & Hevs).
    destruct Hch as (rw' & (rs & Hc & Hf) & Hq).
    injection Hq as -> -> ->.
    cbv beta in Hk. injection Hk as -> -> ->.
    cbn [app] in Hevs. subst evs.
    destruct rw' as [r ws]. cbn [fst snd].
    change (eff_writes (with_copyins (ppoll_reads i m ufds nfds tsp sig sigsetsize)
                          (mkEffect r ws []))) with ws.
    rewrite (ppoll_pick_finish _ _ _ _ _ _ _ _ _ _ _ _ Hp Hc Hf). cbv iota.
    rewrite Hf. cbv iota. apply check_ppoll_eff_refl.
Qed.

Lemma check_ppoll_complete_unmodeled :
  forall i ufds nfds tsp sig sigsetsize m eff,
  ppoll_spec ufds nfds tsp sig sigsetsize i m Unmodeled ->
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckUnmodeled.
Proof.
  intros i ufds nfds tsp sig sigsetsize m eff H.
  unfold ppoll_spec in H. apply bind_input_model_inv in H. cbv beta in H.
  unfold check_ppoll.
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[[r ws]|]|tmo sets]
    eqn:Hp; cbv iota in H |- *.
  - unfold pure in H. discriminate H.
  - reflexivity.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo sets)) eqn:Ha;
      cbv beta iota in H |- *; [reflexivity|].
    exfalso. unfold bind, choose, pure in H. cbv beta iota in H.
    destruct H as [(rw & _ & Hq) | (rw & m1 & evs1 & _ & Hk)].
    + discriminate Hq.
    + discriminate Hk.
Qed.

(** ** The gate is exact

    [Select.ppoll_all_answered] tests two choices, the least and the most
    ready, where the spec's reading is about every choice.  These lemmas
    are what make the two the same: the gate admits only where EVERY
    choice is answered ([ppoll_all_answered_sound]), so no admissible
    choice is silently dropped, and where every choice of nonempty sets
    is answered the gate admits ([ppoll_all_answered_complete]). *)

Local Lemma ppoll_least_length : forall sets, length (ppoll_least sets) = length sets.
Proof. intros sets. unfold ppoll_least. apply length_map. Qed.

Local Lemma ppoll_most_length : forall sets, length (ppoll_most sets) = length sets.
Proof. intros sets. unfold ppoll_most. apply length_map. Qed.

Local Lemma ppoll_least_count : forall sets rs,
  ppoll_choice_in sets rs = true -> ppoll_count rs = 0%Z ->
  ppoll_count (ppoll_least sets) = 0%Z.
Proof.
  unfold ppoll_least.
  induction sets as [|s sets IH]; intros [|r rs] Hc H0; try discriminate Hc;
    [reflexivity|].
  cbn [ppoll_choice_in] in Hc. apply Bool.andb_true_iff in Hc as [Hr Hc].
  cbn [ppoll_count] in H0. pose proof (proj1 (ppoll_count_bounds rs)) as Hn.
  destruct (Z.eqb r 0) eqn:Er; cbv iota in H0; [|lia].
  apply Z.eqb_eq in Er. subst r.
  assert (E : ppoll_least_of s = 0%Z)
    by (unfold ppoll_least_of; rewrite Hr; reflexivity).
  cbn [map ppoll_count]. rewrite E.
  rewrite (IH rs Hc) by lia. reflexivity.
Qed.

Local Lemma ppoll_most_count : forall sets rs,
  ppoll_choice_in sets rs = true -> ppoll_count rs <> 0%Z ->
  ppoll_count (ppoll_most sets) <> 0%Z.
Proof.
  unfold ppoll_most.
  induction sets as [|s sets IH]; intros [|r rs] Hc H0; try discriminate Hc;
    [exact H0|].
  cbn [ppoll_choice_in] in Hc. apply Bool.andb_true_iff in Hc as [Hr Hc].
  cbn [map ppoll_count] in H0 |- *.
  pose proof (proj1 (ppoll_count_bounds rs)) as Hn.
  pose proof (proj1 (ppoll_count_bounds (map ppoll_most_of sets))) as Hm.
  destruct (Z.eqb r 0) eqn:Er; cbv iota in H0.
  - specialize (IH rs Hc ltac:(lia)).
    destruct (Z.eqb (ppoll_most_of s) 0); cbv iota; lia.
  - assert (Hs : Z.eqb (ppoll_most_of s) 0 = false).
    { unfold ppoll_most_of.
      apply existsb_exists in Hr as (r0 & Hin & Heq).
      apply Z.eqb_eq in Heq. subst r0.
      destruct (find (fun r1 => negb (Z.eqb r1 0)) s) as [r1|] eqn:Ef.
      - apply find_some in Ef as [_ Hb]. cbv beta in Hb.
        apply negb_true_iff in Hb. exact Hb.
      - eapply find_none in Ef; [|exact Hin]. cbv beta in Ef.
        rewrite Er in Ef. discriminate Ef. }
    rewrite Hs. cbv iota. lia.
Qed.

Local Lemma ppoll_least_choice : forall sets,
  Forall (fun s => s <> []) sets -> ppoll_choice_in sets (ppoll_least sets) = true.
Proof.
  unfold ppoll_least.
  induction sets as [|s sets IH]; intros Hne; [reflexivity|].
  inversion Hne as [|s0 sets0 Hs Hne']; subst.
  cbn [map ppoll_choice_in]. rewrite (IH Hne'), andb_true_r.
  unfold ppoll_least_of.
  destruct (existsb (Z.eqb 0) s) eqn:E; [exact E|].
  destruct s as [|v s']; [exfalso; apply Hs; reflexivity|].
  cbn [hd existsb]. rewrite Z.eqb_refl. reflexivity.
Qed.

Local Lemma ppoll_most_choice : forall sets,
  Forall (fun s => s <> []) sets -> ppoll_choice_in sets (ppoll_most sets) = true.
Proof.
  unfold ppoll_most.
  induction sets as [|s sets IH]; intros Hne; [reflexivity|].
  inversion Hne as [|s0 sets0 Hs Hne']; subst.
  cbn [map ppoll_choice_in]. rewrite (IH Hne'), andb_true_r.
  unfold ppoll_most_of.
  destruct (find (fun r => negb (Z.eqb r 0)) s) as [r|] eqn:E; cbv iota.
  - apply find_some in E as [Hin _]. apply existsb_exists.
    exists r. split; [exact Hin | apply Z.eqb_refl].
  - destruct s as [|v s']; [exfalso; apply Hs; reflexivity|].
    cbn [hd existsb]. rewrite Z.eqb_refl. reflexivity.
Qed.

(** [Select.ppoll_writeback]'s addresses and lengths do not depend on the
    values written, so neither does its writability. *)
Local Lemma ppoll_writeback_writable : forall i p rs rs' x,
  length rs = length rs' ->
  writes_all_writable i (ppoll_writeback p rs ++ x)
  = writes_all_writable i (ppoll_writeback p rs' ++ x).
Proof.
  intros i p rs. revert p.
  induction rs as [|r rs IH]; intros p [|r' rs'] x Hl; try discriminate Hl;
    [reflexivity|].
  cbn [ppoll_writeback app]. unfold writes_all_writable in *.
  cbn [forallb fst snd].
  rewrite (IH _ rs' x) by (cbn [length] in Hl; lia). reflexivity.
Qed.

(** [Select.ppoll_finish] answers or declines a choice by whether its
    count is 0 and by nothing else about it. *)
Local Lemma ppoll_finish_shape : forall i ufds nfds tsp tmo rs rs',
  length rs = length rs' ->
  Z.eqb (ppoll_count rs) 0 = Z.eqb (ppoll_count rs') 0 ->
  ppoll_answers (ppoll_finish i ufds nfds tsp tmo rs)
  = ppoll_answers (ppoll_finish i ufds nfds tsp tmo rs').
Proof.
  intros i ufds nfds tsp tmo rs rs' Hl Hc.
  pose proof (ppoll_writeback_writable i ufds rs rs' [] Hl) as Hw.
  rewrite !app_nil_r in Hw.
  pose proof (ppoll_writeback_writable i ufds rs rs'
                [(tsp, pselect_timespec_zero)] Hl) as Hd.
  unfold ppoll_finish, ppoll_writeback_access, pselect_finish, pselect_writes,
    pselect_err.
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)); destruct tmo;
    try reflexivity; rewrite ?Hc;
    repeat match goal with
           | |- context [if Z.eqb (ppoll_count rs') 0 then _ else _] =>
               destruct (Z.eqb (ppoll_count rs') 0)
           end;
    try reflexivity; rewrite ?Hw, ?Hd;
    repeat match goal with
           | |- context [if ?b then _ else _] => destruct b
           end;
    reflexivity.
Qed.

Lemma ppoll_all_answered_sound : forall i ufds nfds tsp tmo sets,
  ppoll_all_answered i ufds nfds tsp tmo sets = true ->
  forall rs, ppoll_choice_in sets rs = true ->
  ppoll_finish i ufds nfds tsp tmo rs <> None.
Proof.
  intros i ufds nfds tsp tmo sets Hg rs Hc.
  unfold ppoll_all_answered in Hg.
  apply Bool.andb_true_iff in Hg as [Hg Hhi].
  apply Bool.andb_true_iff in Hg as [Hg Hlo].
  pose proof (ppoll_choice_in_length _ _ Hc) as Hl.
  pose proof (ppoll_least_length sets) as Hllo.
  pose proof (ppoll_most_length sets) as Hlhi.
  assert (Ha : ppoll_answers (ppoll_finish i ufds nfds tsp tmo rs) = true).
  { destruct (Z.eqb (ppoll_count rs) 0) eqn:E.
    - apply Z.eqb_eq in E.
      rewrite (ppoll_finish_shape i ufds nfds tsp tmo rs (ppoll_least sets));
        [exact Hlo | lia |].
      rewrite (proj2 (Z.eqb_eq _ _) E),
        (proj2 (Z.eqb_eq _ _) (ppoll_least_count _ _ Hc E)).
      reflexivity.
    - apply Z.eqb_neq in E.
      rewrite (ppoll_finish_shape i ufds nfds tsp tmo rs (ppoll_most sets));
        [exact Hhi | lia |].
      rewrite (proj2 (Z.eqb_neq _ _) E),
        (proj2 (Z.eqb_neq _ _) (ppoll_most_count _ _ Hc E)).
      reflexivity. }
  unfold ppoll_answers in Ha.
  destruct (ppoll_finish i ufds nfds tsp tmo rs); [discriminate | discriminate Ha].
Qed.

Lemma ppoll_all_answered_complete : forall i ufds nfds tsp tmo sets,
  Forall (fun s => s <> []) sets ->
  (forall rs, ppoll_choice_in sets rs = true ->
     ppoll_finish i ufds nfds tsp tmo rs <> None) ->
  ppoll_all_answered i ufds nfds tsp tmo sets = true.
Proof.
  intros i ufds nfds tsp tmo sets Hne Hall.
  pose proof (ppoll_least_choice _ Hne) as Hlo.
  pose proof (ppoll_most_choice _ Hne) as Hhi.
  unfold ppoll_all_answered. rewrite Hlo, Hhi. cbn [andb].
  destruct (ppoll_finish i ufds nfds tsp tmo (ppoll_least sets)) eqn:E1;
    [|exfalso; exact (Hall _ Hlo E1)].
  destruct (ppoll_finish i ufds nfds tsp tmo (ppoll_most sets)) eqn:E2;
    [|exfalso; exact (Hall _ Hhi E2)].
  reflexivity.
Qed.
