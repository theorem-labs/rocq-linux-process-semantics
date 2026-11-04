(** * LinuxProcessSem.Checks.PpollAgree — the merged ppoll admits exactly what each of the two models it merges admits, wherever that model answers

    [Fs.Select.ppoll_spec] is one model built from two: the revision's,
    which answers on stream-pair ends and records the choice of
    EPOLLERR in [State.se_reset], and #78's (c1c-monitor-wait fc558cf),
    which answers on eventfd and signalfd entries, whose readiness the
    environment picks per entry.  This file keeps a verbatim copy of
    each, prefixed [rev_] and [p78_], and proves that wherever a copy
    does not decline, the merged spec admits exactly the outcomes the
    copy admits ([ppoll_spec_agrees_with_revision],
    [ppoll_spec_agrees_with_pr78]).  The copies use the merged file's
    shared parts unchanged: [pselect_timeout], [ppoll_sigmask],
    [ppoll_reads], [ppoll_count], [ppoll_writeback] and
    [writes_all_writable]; the revision's copy also [pselect_finish],
    [ppoll_writeback_access], [pselect_answer], [ppoll_record] and
    [ppoll_revents_of]; #78's also [ppoll_opaque_revents].

    The revision's proof follows one bijection.  Where the revision
    answers, no entry names an opaque descriptor, so each merged entry
    is the revision's pair of masks as alternatives ([pagree_alt]).  A
    choice of the revision is a set [sel] of undecided descriptors; the
    merged choice for it is the list of [revents] [rev_ppoll_pick]
    gives, and back, [ppoll_sel] of that list is [sel].

    #78's proof is the identity on choices.  Where #78 answers, no entry
    names a stream-pair end, so each merged entry is #78's list of
    [revents] tagged [PpOnly] or [PpEnv] ([p78_sets], [p78_free]), there
    is no stream-pair choice to record ([p78_und0]), and #78's answer for
    a choice is the merged one with no remaining time to choose
    ([p78_finish_some]): #78 answers a real deadline only where every
    choice counts 0, so the merged plan's decline of a real deadline with
    an eventfd or signalfd entry that can be ready never meets it
    ([p78_env_deadline]). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   The revision's ppoll, verbatim
   ========================================================================= *)

Fixpoint rev_ppoll_revents (fds : list (word * FdEntry)) (es : list (Z * Z))
    : option (list (Z * Z * Z)) :=
  match es with
  | [] => Some []
  | (fd, ev) :: rest =>
      match ppoll_revents_of fds fd ev with
      | None => None
      | Some (lo, hi) =>
          match rev_ppoll_revents fds rest with
          | None => None
          | Some cs => Some ((fd, lo, hi) :: cs)
          end
      end
  end.

Fixpoint rev_ppoll_undecided (cs : list (Z * Z * Z)) : Z :=
  match cs with
  | [] => 0%Z
  | (fd, lo, hi) :: rest =>
      Z.lor (if Z.eqb lo hi then 0%Z else Z.shiftl 1 fd) (rev_ppoll_undecided rest)
  end.

Fixpoint rev_ppoll_pick (cs : list (Z * Z * Z)) (sel : Z) : list Z :=
  match cs with
  | [] => []
  | (fd, lo, hi) :: rest =>
      (if Z.testbit sel fd then hi else lo) :: rev_ppoll_pick rest sel
  end.

Inductive RevPpollScan :=
  | RevScanGap
  | RevScanErr (e : Z)
  | RevScanDone (cs : list (Z * Z * Z)).

Definition rev_ppoll_scan (i : SyscallInput) (m : Model) (ufds nfds : word)
    : RevPpollScan :=
  let n := bv_unsigned nfds in
  if (bv_unsigned (m_nofile m) <? n)%Z then RevScanErr EINVAL
  else if (ppoll_nfds_max <? n)%Z then RevScanGap
  else if (negb (Z.eqb n 0) && negb (access_okb ufds (pollfd_bytes * n)%Z))%bool
  then RevScanErr EFAULT
  else
    match read_bytes_map (in_mem i) ufds (Z_to_bv 64 (pollfd_bytes * n)%Z) with
    | None => RevScanErr EFAULT
    | Some bs =>
        match rev_ppoll_revents (m_fds m) (decode_pollfds bs (Z.to_nat n)) with
        | None => RevScanGap
        | Some cs => RevScanDone cs
        end
    end.

Definition rev_ppoll_core (i : SyscallInput) (m : Model) (ufds nfds : word)
    : PselectCore :=
  match rev_ppoll_scan i m ufds nfds with
  | RevScanGap => PsCoreGap
  | RevScanErr e => PsCoreErr e
  | RevScanDone cs =>
      PsCoreDone (rev_ppoll_undecided cs)
        (fun sel => let rs := rev_ppoll_pick cs sel in
                    (ppoll_count rs, ppoll_writeback ufds rs))
  end.

Definition rev_ppoll_rec (pa : PselectAnswers) (sel : Z) (m : Model) : Model :=
  with_fds (ppoll_record (m_fds m) (pa_und pa) sel) m.

Definition rev_ppoll_outcome (i : SyscallInput) (m : Model)
    (ufds nfds tsp sig sigsetsize : word) : option PselectAnswers :=
  match pselect_timeout (in_mem i) tsp with
  | PsToFault => pselect_err EFAULT
  | PsToInval => pselect_err EINVAL
  | tmo =>
      match ppoll_sigmask (in_mem i) sig sigsetsize with
      | PpSigBadSize => pselect_err EINVAL
      | PpSigFault => pselect_err EFAULT
      | PpSigReal => None
      | PpSigNone =>
          pselect_finish i tsp tmo
            (ppoll_writeback_access ufds nfds tmo (rev_ppoll_core i m ufds nfds))
      end
  end.

Definition rev_ppoll_spec (ufds nfds tsp sig sigsetsize : word)
    : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match rev_ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | None => unmodeled
  | Some pa =>
      pselect_answer (ppoll_reads i m ufds nfds tsp sig sigsetsize) pa (rev_ppoll_rec pa)
  end.

(* =========================================================================
   The entries
   ========================================================================= *)

(** The revision's entry as the merged entry's alternatives. *)
Definition pagree_alt (c : Z * Z * Z) : Z * list (Z * PpollTag) :=
  let '(fd, lo, hi) := c in (fd, ppoll_pair_alts (lo, hi)).

(** What every entry the revision scans satisfies: where its two masks
    differ, its descriptor is not negative and its [hi] mask is not 0. *)
Definition pagree_ok (c : Z * Z * Z) : Prop :=
  let '(fd, lo, hi) := c in lo <> hi -> (0 <= fd)%Z /\ hi <> 0%Z.

Lemma pagree_entries : forall m es cs,
  rev_ppoll_revents (m_fds m) es = Some cs ->
  ppoll_entries m es = Some (map pagree_alt cs).
Proof.
  intros m. induction es as [|[fd ev] es IH]; intros cs H; cbn [rev_ppoll_revents] in H.
  - injection H as <-. reflexivity.
  - destruct (ppoll_revents_of (m_fds m) fd ev) as [[lo hi]|] eqn:Hr; [|discriminate H].
    destruct (rev_ppoll_revents (m_fds m) es) as [cs0|] eqn:Hes; [|discriminate H].
    injection H as <-.
    assert (Ha : ppoll_alts_of m fd ev = Some (ppoll_pair_alts (lo, hi))).
    { unfold ppoll_alts_of.
      destruct (fd <? 0)%Z eqn:Hneg.
      - rewrite Hr. reflexivity.
      - destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [e|] eqn:Hl.
        + destruct e; try (rewrite Hr; reflexivity).
          unfold ppoll_revents_of in Hr. rewrite Hneg, Hl in Hr. discriminate Hr.
        + rewrite Hr. reflexivity. }
    cbn [ppoll_entries map pagree_alt]. rewrite Ha, (IH cs0 eq_refl). reflexivity.
Qed.

Lemma pagree_revents_ok : forall fds es cs,
  rev_ppoll_revents fds es = Some cs -> Forall pagree_ok cs.
Proof.
  intros fds. induction es as [|[fd ev] es IH]; intros cs H; cbn [rev_ppoll_revents] in H.
  - injection H as <-. constructor.
  - destruct (ppoll_revents_of fds fd ev) as [[lo hi]|] eqn:Hr; [|discriminate H].
    destruct (rev_ppoll_revents fds es) as [cs0|] eqn:Hes; [|discriminate H].
    injection H as <-. constructor; [|exact (IH cs0 eq_refl)].
    unfold pagree_ok. intros Hne. split.
    + destruct (Z.ltb_spec fd 0) as [Hlt|Hge]; [|exact Hge].
      exfalso. apply Hne. unfold ppoll_revents_of in Hr.
      rewrite (proj2 (Z.ltb_lt fd 0) Hlt) in Hr. injection Hr as <- <-. reflexivity.
    + exact (ppoll_revents_of_mono _ _ _ _ _ Hr Hne).
Qed.

Lemma pagree_scan_err : forall i m ufds nfds e,
  rev_ppoll_scan i m ufds nfds = RevScanErr e -> ppoll_scan i m ufds nfds = PpScanErr e.
Proof.
  intros i m ufds nfds e H. unfold rev_ppoll_scan in H. unfold ppoll_scan.
  cbv zeta in H |- *.
  repeat (match type of H with
          | context [if ?b then _ else _] => destruct b eqn:?
          | context [match ?x with _ => _ end] => destruct x eqn:?
          end; cbv iota in H |- *; try discriminate H).
  all: injection H as <-; reflexivity.
Qed.

Lemma pagree_scan_done : forall i m ufds nfds cs,
  rev_ppoll_scan i m ufds nfds = RevScanDone cs ->
  ppoll_scan i m ufds nfds = PpScanDone (map pagree_alt cs) /\ Forall pagree_ok cs.
Proof.
  intros i m ufds nfds cs H. unfold rev_ppoll_scan in H. unfold ppoll_scan.
  cbv zeta in H |- *.
  repeat (match type of H with
          | context [if ?b then _ else _] => destruct b eqn:?
          | context [match ?x with _ => _ end] => destruct x eqn:?
          end; cbv iota in H |- *; try discriminate H).
  all: injection H as <-.
  all: match goal with
       | Hr : rev_ppoll_revents _ _ = Some _ |- _ =>
           split; [rewrite (pagree_entries _ _ _ Hr); reflexivity
                  | exact (pagree_revents_ok _ _ _ Hr)]
       end.
Qed.

Lemma pagree_und : forall cs, ppoll_und (map pagree_alt cs) = rev_ppoll_undecided cs.
Proof.
  induction cs as [|[[fd lo] hi] cs IH]; [reflexivity|].
  cbn [map pagree_alt ppoll_und rev_ppoll_undecided]. rewrite IH. f_equal.
  unfold ppoll_pair_alts. cbv beta iota zeta. destruct (Z.eqb lo hi); reflexivity.
Qed.

Lemma pagree_env_ready : forall cs, ppoll_env_ready (map pagree_alt cs) = false.
Proof.
  induction cs as [|[[fd lo] hi] cs IH]; [reflexivity|].
  unfold ppoll_env_ready in *. cbn [map existsb pagree_alt snd]. rewrite IH, orb_false_r.
  unfold ppoll_pair_alts. cbv beta iota zeta. destruct (Z.eqb lo hi); reflexivity.
Qed.

(* =========================================================================
   The choices
   ========================================================================= *)

Lemma pagree_bit_shiftl1 : forall fd n, (0 <= fd)%Z ->
  Z.testbit (Z.shiftl 1 fd) n = Z.eqb fd n.
Proof. intros fd n Hfd. rewrite Z.shiftl_1_l. apply Z.pow2_bits_eqb. exact Hfd. Qed.

Lemma pagree_tag_only : forall lo, ppoll_tag_of [(lo, PpOnly)] lo = Some PpOnly.
Proof. intros lo. unfold ppoll_tag_of. cbn [find fst]. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma pagree_tag_lo : forall lo hi, lo <> hi ->
  ppoll_tag_of [(lo, PpEnd false); (hi, PpEnd true)] lo = Some (PpEnd false).
Proof. intros lo hi _. unfold ppoll_tag_of. cbn [find fst]. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma pagree_tag_hi : forall lo hi, lo <> hi ->
  ppoll_tag_of [(lo, PpEnd false); (hi, PpEnd true)] hi = Some (PpEnd true).
Proof.
  intros lo hi Hne. unfold ppoll_tag_of. cbn [find fst].
  rewrite (proj2 (Z.eqb_neq lo hi) Hne), Z.eqb_refl. reflexivity.
Qed.

Lemma pagree_tag_of_in : forall s r t, ppoll_tag_of s r = Some t -> In (r, t) s.
Proof.
  intros s r t H. unfold ppoll_tag_of in H.
  destruct (find (fun a => Z.eqb (fst a) r) s) as [[r0 t0]|] eqn:Hf; [|discriminate H].
  cbn [option_map snd] in H. injection H as <-.
  apply find_some in Hf. destruct Hf as [Hin Heq]. cbn [fst] in Heq.
  apply Z.eqb_eq in Heq. subst r0. exact Hin.
Qed.

(** The revision's choice [sel], picked, is a merged choice. *)
Lemma pagree_choice_at_pick : forall sel cs,
  ppoll_choice_at sel (map pagree_alt cs) (rev_ppoll_pick cs sel) = true.
Proof.
  intros sel. induction cs as [|[[fd lo] hi] cs IH]; [reflexivity|].
  cbn [map pagree_alt rev_ppoll_pick ppoll_choice_at]. rewrite IH, andb_true_r.
  unfold ppoll_pair_alts. cbv beta iota zeta.
  destruct (Z.eqb_spec lo hi) as [<-|Hne]; cbv iota.
  - destruct (Z.testbit sel fd); cbv iota; rewrite pagree_tag_only; reflexivity.
  - destruct (Z.testbit sel fd) eqn:Hs; cbv iota.
    + rewrite (pagree_tag_hi lo hi Hne). try rewrite Hs. reflexivity.
    + rewrite (pagree_tag_lo lo hi Hne). try rewrite Hs. reflexivity.
Qed.

(** ...and every merged choice is one: the pick of the set it shows. *)
Lemma pagree_choice_pick : forall sel cs rs,
  ppoll_choice_at sel (map pagree_alt cs) rs = true -> rs = rev_ppoll_pick cs sel.
Proof.
  intros sel. induction cs as [|[[fd lo] hi] cs IH]; intros rs H; destruct rs as [|r rs];
    cbn [map pagree_alt ppoll_choice_at rev_ppoll_pick] in H |- *; try discriminate H;
    [reflexivity|].
  apply andb_true_iff in H as [Hr Hrs]. f_equal; [|exact (IH rs Hrs)].
  destruct (ppoll_tag_of (ppoll_pair_alts (lo, hi)) r) as [t|] eqn:Ht; [|discriminate Hr].
  apply pagree_tag_of_in in Ht.
  unfold ppoll_pair_alts in Ht. cbv beta iota zeta in Ht.
  destruct (Z.eqb_spec lo hi) as [<-|Hne]; cbv iota in Ht.
  - destruct Ht as [Ht|[]]. injection Ht as -> _.
    destruct (Z.testbit sel fd); reflexivity.
  - destruct Ht as [Ht|[Ht|[]]]; injection Ht as -> <-; cbv iota in Hr.
    + destruct (Z.testbit sel fd); [discriminate Hr|reflexivity].
    + destruct (Z.testbit sel fd); [reflexivity|discriminate Hr].
Qed.

(** The set a picked choice shows is the chosen part of the undecided
    set, bit by bit. *)
Lemma pagree_sel_pick : forall cs sel, Forall pagree_ok cs ->
  forall n, (0 <= n)%Z ->
  Z.testbit (ppoll_sel (map pagree_alt cs) (rev_ppoll_pick cs sel)) n
  = Z.testbit (Z.land (rev_ppoll_undecided cs) sel) n.
Proof.
  induction cs as [|[[fd lo] hi] cs IH]; intros sel Hok n Hn.
  - cbn [map rev_ppoll_pick ppoll_sel rev_ppoll_undecided].
    rewrite Z.land_0_l. reflexivity.
  - pose proof (Forall_inv Hok) as Hc. pose proof (Forall_inv_tail Hok) as Ht.
    unfold pagree_ok in Hc.
    cbn [map pagree_alt rev_ppoll_pick ppoll_sel rev_ppoll_undecided].
    rewrite Z.lor_spec, (IH sel Ht n Hn), !Z.land_spec, !Z.lor_spec.
    unfold ppoll_pair_alts. cbv beta iota zeta.
    destruct (Z.eqb_spec lo hi) as [<-|Hne]; cbv iota.
    + destruct (Z.testbit sel fd); cbv iota; rewrite pagree_tag_only; cbn [ppoll_is_hi];
        rewrite Z.testbit_0_l;
        destruct (Z.testbit (rev_ppoll_undecided cs) n), (Z.testbit sel n); reflexivity.
    + destruct (Hc Hne) as [Hfd _].
      destruct (Z.testbit sel fd) eqn:Hs; cbv iota.
      * rewrite (pagree_tag_hi lo hi Hne). cbn [ppoll_is_hi].
        rewrite (pagree_bit_shiftl1 fd n Hfd).
        destruct (Z.eqb_spec fd n) as [<-|Hfn].
        -- rewrite Hs. destruct (Z.testbit (rev_ppoll_undecided cs) fd); reflexivity.
        -- destruct (Z.testbit (rev_ppoll_undecided cs) n), (Z.testbit sel n); reflexivity.
      * rewrite (pagree_tag_lo lo hi Hne). cbn [ppoll_is_hi].
        rewrite Z.testbit_0_l, (pagree_bit_shiftl1 fd n Hfd).
        destruct (Z.eqb_spec fd n) as [<-|Hfn].
        -- rewrite Hs. destruct (Z.testbit (rev_ppoll_undecided cs) fd); reflexivity.
        -- destruct (Z.testbit (rev_ppoll_undecided cs) n), (Z.testbit sel n); reflexivity.
Qed.

(** A bit a merged choice shows is an undecided descriptor. *)
Lemma pagree_sel_sub : forall cs rs n, Forall pagree_ok cs -> (0 <= n)%Z ->
  Z.testbit (ppoll_sel (map pagree_alt cs) rs) n = true ->
  Z.testbit (rev_ppoll_undecided cs) n = true.
Proof.
  induction cs as [|[[fd lo] hi] cs IH]; intros rs n Hok Hn H; destruct rs as [|r rs];
    cbn [map pagree_alt ppoll_sel rev_ppoll_undecided] in H |- *;
    try (rewrite Z.testbit_0_l in H; discriminate H).
  pose proof (Forall_inv Hok) as Hc. unfold pagree_ok in Hc.
  rewrite Z.lor_spec in H |- *. apply orb_true_iff in H. destruct H as [H|H].
  - unfold ppoll_pair_alts in H. cbv beta iota zeta in H.
    destruct (Z.eqb_spec lo hi) as [<-|Hne]; cbv iota in H |- *.
    + exfalso. unfold ppoll_tag_of in H. cbn [find fst] in H.
      destruct (Z.eqb lo r); cbn [option_map snd ppoll_is_hi] in H;
        rewrite Z.testbit_0_l in H; discriminate H.
    + destruct (Hc Hne) as [Hfd _]. apply orb_true_iff. left.
      rewrite (pagree_bit_shiftl1 fd n Hfd).
      match type of H with
      | context [ppoll_tag_of ?s r] => destruct (ppoll_tag_of s r) as [t|]
      end; cbv iota in H; [|rewrite Z.testbit_0_l in H; discriminate H].
      destruct (ppoll_is_hi t); cbv iota in H; [|rewrite Z.testbit_0_l in H; discriminate H].
      rewrite (pagree_bit_shiftl1 fd n Hfd) in H. exact H.
  - apply orb_true_iff. right. exact (IH rs n (Forall_inv_tail Hok) Hn H).
Qed.

Lemma pagree_sel_land : forall cs rs, Forall pagree_ok cs ->
  Z.land (rev_ppoll_undecided cs) (ppoll_sel (map pagree_alt cs) rs)
  = ppoll_sel (map pagree_alt cs) rs.
Proof.
  intros cs rs Hok. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.testbit (ppoll_sel (map pagree_alt cs) rs) n) eqn:E.
  - rewrite (pagree_sel_sub cs rs n Hok Hn E). reflexivity.
  - apply andb_false_r.
Qed.

Lemma pagree_sel_of_pick : forall cs sel, Forall pagree_ok cs ->
  Z.land (rev_ppoll_undecided cs) sel = sel ->
  ppoll_sel (map pagree_alt cs) (rev_ppoll_pick cs sel) = sel.
Proof.
  intros cs sel Hok Hs. apply Z.bits_inj'. intros n Hn.
  rewrite (pagree_sel_pick cs sel Hok n Hn), Hs. reflexivity.
Qed.

(* =========================================================================
   The answers
   ========================================================================= *)

Lemma pagree_count_zero : forall rs, ppoll_count rs = 0%Z -> Forall (fun r => r = 0%Z) rs.
Proof.
  induction rs as [|r rs IH]; intros H; [constructor|].
  cbn [ppoll_count] in H. pose proof (ppoll_count_bounds rs) as Hb.
  destruct (Z.eqb_spec r 0) as [->|Hr]; cbv iota in H; [|lia].
  constructor; [reflexivity|]. apply IH. lia.
Qed.

Lemma pagree_zero_count : forall rs, Forall (fun r => r = 0%Z) rs -> ppoll_count rs = 0%Z.
Proof.
  induction rs as [|r rs IH]; intros H; [reflexivity|].
  pose proof (Forall_inv H) as Hr. cbv beta in Hr.
  cbn [ppoll_count]. rewrite Hr, (IH (Forall_inv_tail H)). reflexivity.
Qed.

Lemma pagree_pick_zero : forall cs sel, Forall pagree_ok cs ->
  Forall (fun r => r = 0%Z) (rev_ppoll_pick cs sel) ->
  Forall (fun r => r = 0%Z) (rev_ppoll_pick cs 0).
Proof.
  induction cs as [|[[fd lo] hi] cs IH]; intros sel Hok H;
    cbn [rev_ppoll_pick] in H |- *; [constructor|].
  pose proof (Forall_inv H) as Hr. pose proof (Forall_inv_tail H) as Hrs. cbv beta in Hr.
  constructor; [|exact (IH sel (Forall_inv_tail Hok) Hrs)].
  rewrite Z.testbit_0_l.
  pose proof (Forall_inv Hok) as Hc. unfold pagree_ok in Hc.
  destruct (Z.testbit sel fd); [|exact Hr].
  destruct (Z.eqb_spec lo hi) as [->|Hne]; [exact Hr|].
  exfalso. exact (proj2 (Hc Hne) Hr).
Qed.

(** Where the all-not-ready choice counts, every choice counts. *)
Lemma pagree_count_pick : forall cs sel, Forall pagree_ok cs ->
  (ppoll_count (rev_ppoll_pick cs 0) =? 0)%Z = false ->
  (ppoll_count (rev_ppoll_pick cs sel) =? 0)%Z = false.
Proof.
  intros cs sel Hok H. apply Z.eqb_neq. intros Hz. apply Z.eqb_neq in H. apply H.
  apply pagree_zero_count. exact (pagree_pick_zero cs sel Hok (pagree_count_zero _ Hz)).
Qed.

Lemma pagree_pick_length : forall cs sel, length (rev_ppoll_pick cs sel) = length cs.
Proof.
  induction cs as [|[[fd lo] hi] cs IH]; intros sel; [reflexivity|].
  cbn [rev_ppoll_pick length]. rewrite IH. reflexivity.
Qed.

(** Whether the write-back is writable depends on the number of entries
    only. *)
Lemma pagree_wb_len : forall i p rs rs' x, length rs = length rs' ->
  writes_all_writable i (ppoll_writeback p rs ++ x)
  = writes_all_writable i (ppoll_writeback p rs' ++ x).
Proof.
  intros i p rs. revert p. induction rs as [|r rs IH]; intros p rs' x H;
    destruct rs' as [|r' rs']; cbn [length] in H; try discriminate H; [reflexivity|].
  injection H as H. cbn [ppoll_writeback app]. unfold writes_all_writable in *.
  cbn [forallb fst snd]. rewrite (IH _ rs' x H). unfold word_le2. cbn [length].
  reflexivity.
Qed.

Lemma pagree_wb_pick : forall i p cs sel x,
  writes_all_writable i (ppoll_writeback p (rev_ppoll_pick cs sel) ++ x)
  = writes_all_writable i (ppoll_writeback p (rev_ppoll_pick cs 0) ++ x).
Proof.
  intros i p cs sel x. apply pagree_wb_len. rewrite !pagree_pick_length. reflexivity.
Qed.

Lemma pagree_wb_pick0 : forall i p cs sel,
  writes_all_writable i (ppoll_writeback p (rev_ppoll_pick cs sel))
  = writes_all_writable i (ppoll_writeback p (rev_ppoll_pick cs 0)).
Proof.
  intros i p cs sel.
  rewrite <- (app_nil_r (ppoll_writeback p (rev_ppoll_pick cs sel))),
    <- (app_nil_r (ppoll_writeback p (rev_ppoll_pick cs 0))).
  apply pagree_wb_pick.
Qed.

(** The revision's answers for a choice [sel] are the merged answers for
    the pick of [sel]. *)
Lemma pagree_finish : forall i ufds nfds tsp tmo cs pa,
  Forall pagree_ok cs ->
  (access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z = false -> cs = []) ->
  pselect_finish i tsp tmo
    (ppoll_writeback_access ufds nfds tmo
       (PsCoreDone (rev_ppoll_undecided cs)
          (fun sel => let rs := rev_ppoll_pick cs sel in
                      (ppoll_count rs, ppoll_writeback ufds rs))))
  = Some pa ->
  pa_und pa = rev_ppoll_undecided cs
  /\ forall sel, ppoll_finish i ufds nfds tsp tmo (rev_ppoll_pick cs sel)
                 = Some (ps_one (pa_ans pa sel)).
Proof.
  intros i ufds nfds tsp tmo cs pa Hok Hacc H.
  unfold pselect_finish, ppoll_writeback_access in H.
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z) eqn:Ha.
  2:{ specialize (Hacc eq_refl). subst cs.
      cbn [rev_ppoll_pick ppoll_count rev_ppoll_undecided fst] in H.
      destruct tmo as [| | | | sec nsec]; cbv beta iota zeta in H.
      all: unfold pselect_err, ps_fixed in H.
      all: try discriminate H.
      all: try (destruct (writes_all_writable i [(tsp, pselect_timespec_zero)]) eqn:Hw;
                [|discriminate H]).
      all: injection H as <-; split; [reflexivity|]; intros sel; cbn [rev_ppoll_pick];
        rewrite ppoll_finish_eq, Ha; try rewrite Hw; reflexivity. }
  cbv beta zeta iota in H.
  destruct tmo as [| | | | sec nsec]; cbv iota in H; try discriminate H.
  - destruct (Z.eqb (ppoll_count (rev_ppoll_pick cs 0)) 0) eqn:Hc0; [discriminate H|].
    destruct (writes_all_writable i (ppoll_writeback ufds (rev_ppoll_pick cs 0))) eqn:Hw0;
      [|discriminate H].
    injection H as <-. split; [reflexivity|]. intros sel.
    rewrite ppoll_finish_eq, Ha. cbv iota.
    rewrite (pagree_count_pick cs sel Hok Hc0), pagree_wb_pick0, Hw0. reflexivity.
  - destruct (writes_all_writable i (ppoll_writeback ufds (rev_ppoll_pick cs 0))) eqn:Hw0;
      [|discriminate H].
    injection H as <-. split; [reflexivity|]. intros sel.
    rewrite ppoll_finish_eq, Ha. cbv iota.
    rewrite pagree_wb_pick0, Hw0. reflexivity.
  - destruct (writes_all_writable i
                (ppoll_writeback ufds (rev_ppoll_pick cs 0) ++ [(tsp, pselect_timespec_zero)]))
      eqn:Hw0; [|discriminate H].
    injection H as <-. split; [reflexivity|]. intros sel.
    rewrite ppoll_finish_eq, Ha. cbv iota.
    rewrite pagree_wb_pick, Hw0. reflexivity.
Qed.

(* =========================================================================
   The outcomes
   ========================================================================= *)

Lemma pagree_answer_ext : forall reads pa rec1 rec2 i m o,
  (forall sel, Z.land (pa_und pa) sel = sel -> rec1 sel m = rec2 sel m) ->
  pselect_answer reads pa rec1 i m o <-> pselect_answer reads pa rec2 i m o.
Proof.
  intros reads pa rec1 rec2 i m o Hr. rewrite !pselect_answer_iff. split.
  - intros (sel & eff & Hs & He & ->). exists sel, eff.
    split; [exact Hs|]. split; [exact He|]. rewrite (Hr sel Hs). reflexivity.
  - intros (sel & eff & Hs & He & ->). exists sel, eff.
    split; [exact Hs|]. split; [exact He|]. rewrite (Hr sel Hs). reflexivity.
Qed.

Lemma pagree_rec_zero : forall pa sel m, pa_und pa = 0%Z ->
  Z.land (pa_und pa) sel = sel -> rev_ppoll_rec pa sel m = m.
Proof.
  intros pa sel m H0 Hs. rewrite H0, Z.land_0_l in Hs. subst sel.
  unfold rev_ppoll_rec. rewrite H0, ppoll_record_und0. apply with_fds_m_fds.
Qed.

(** An answer with no choice in it records nothing either way. *)
Lemma pagree_decided : forall reads pa i m o, pa_und pa = 0%Z ->
  pselect_answer reads pa (fun _ m0 => m0) i m o
  <-> pselect_answer reads pa (rev_ppoll_rec pa) i m o.
Proof.
  intros reads pa i m o H0. apply pagree_answer_ext. intros sel Hs. cbv beta.
  symmetry. exact (pagree_rec_zero pa sel m H0 Hs).
Qed.

Lemma pagree_err_und : forall e pa, pselect_err e = Some pa -> pa_und pa = 0%Z.
Proof. intros e pa H. unfold pselect_err, ps_fixed in H. injection H as <-. reflexivity. Qed.

Lemma pagree_wba_err : forall ufds nfds tmo e,
  ppoll_writeback_access ufds nfds tmo (PsCoreErr e) = PsCoreErr e.
Proof. reflexivity. Qed.

(** At [do_poll]: the merged choices are the revision's. *)
Lemma pagree_poll : forall i m ufds nfds tsp sig sigsetsize tmo cs pa o,
  rev_ppoll_scan i m ufds nfds = RevScanDone cs ->
  pselect_finish i tsp tmo
    (ppoll_writeback_access ufds nfds tmo
       (PsCoreDone (rev_ppoll_undecided cs)
          (fun sel => let rs := rev_ppoll_pick cs sel in
                      (ppoll_count rs, ppoll_writeback ufds rs))))
  = Some pa ->
  (if negb (ppoll_all_answered i ufds nfds tsp tmo (map pagree_alt cs)) then unmodeled
   else
     c <- choose (fun c : list Z * PselectAnswers =>
            ppoll_choice_in (map pagree_alt cs) (fst c) = true
            /\ ppoll_finish i ufds nfds tsp tmo (fst c) = Some (snd c)) ;;
     pselect_answer (ppoll_reads i m ufds nfds tsp sig sigsetsize) (snd c)
       (fun _ => ppoll_rec (map pagree_alt cs) (fst c))) i m o
  <-> pselect_answer (ppoll_reads i m ufds nfds tsp sig sigsetsize) pa (rev_ppoll_rec pa) i m o.
Proof.
  intros i m ufds nfds tsp sig sigsetsize tmo cs pa o Hsc Hpa.
  destruct (pagree_scan_done _ _ _ _ _ Hsc) as [Hscan Hok].
  assert (Hacc : access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z = false -> cs = []).
  { intros Ha. apply (map_eq_nil pagree_alt).
    exact (proj2 (ppoll_scan_done _ _ _ _ _ Hscan) Ha). }
  destruct (pagree_finish i ufds nfds tsp tmo cs pa Hok Hacc Hpa) as [Hund Hfin].
  assert (Hall : ppoll_all_answered i ufds nfds tsp tmo (map pagree_alt cs) = true).
  { apply ppoll_all_answered_complete; [exact (ppoll_scan_alts_ok _ _ _ _ _ Hscan)|].
    intros rs Hrs. unfold ppoll_choice_in in Hrs.
    rewrite (pagree_choice_pick _ _ _ Hrs), Hfin. intros E. discriminate E. }
  rewrite Hall. cbn [negb]. rewrite bind_choose_iff. split.
  - intros ([rs pa'] & (Hch & Hf) & Hans). cbn [fst snd] in Hch, Hf, Hans.
    apply pselect_answer_iff in Hans. destruct Hans as (sel0 & eff & _ & He & ->).
    assert (Hrs : rs = rev_ppoll_pick cs (ppoll_sel (map pagree_alt cs) rs))
      by (apply pagree_choice_pick; exact Hch).
    rewrite Hrs, Hfin in Hf. injection Hf as <-.
    apply pselect_answer_iff. exists (ppoll_sel (map pagree_alt cs) rs), eff.
    split; [rewrite Hund; apply pagree_sel_land; exact Hok|].
    split; [exact He|].
    cbv beta. f_equal. unfold ppoll_rec, rev_ppoll_rec. rewrite pagree_und, Hund.
    reflexivity.
  - intros Hans. apply pselect_answer_iff in Hans. destruct Hans as (sel & eff & Hs & He & ->).
    assert (Hsel : ppoll_sel (map pagree_alt cs) (rev_ppoll_pick cs sel) = sel)
      by (apply pagree_sel_of_pick; [exact Hok | rewrite <- Hund; exact Hs]).
    exists (rev_ppoll_pick cs sel, ps_one (pa_ans pa sel)). cbn [fst snd].
    split; [split|].
    + unfold ppoll_choice_in. rewrite Hsel. apply pagree_choice_at_pick.
    + apply Hfin.
    + apply pselect_answer_iff. exists 0%Z, eff.
      split; [reflexivity|]. split; [exact He|].
      cbv beta. f_equal. unfold ppoll_rec, rev_ppoll_rec. rewrite pagree_und, Hsel, Hund.
      reflexivity.
Qed.

(** THE REVISION: wherever the revision's ppoll answers, the merged
    ppoll admits exactly the outcomes it admits. *)
Theorem ppoll_spec_agrees_with_revision :
  forall ufds nfds tsp sig sigsetsize i m,
  ~ rev_ppoll_spec ufds nfds tsp sig sigsetsize i m Unmodeled ->
  forall o, ppoll_spec ufds nfds tsp sig sigsetsize i m o
            <-> rev_ppoll_spec ufds nfds tsp sig sigsetsize i m o.
Proof.
  intros ufds nfds tsp sig sigsetsize i m Hrev o.
  destruct (rev_ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [pa|] eqn:Hpa.
  2:{ exfalso. apply Hrev. unfold rev_ppoll_spec.
      apply bind_input_iff; cbv beta. apply bind_get_model; cbv beta.
      rewrite Hpa. reflexivity. }
  unfold ppoll_spec, rev_ppoll_spec.
  rewrite !bind_input_iff; cbv beta. rewrite !bind_get_model; cbv beta.
  rewrite Hpa. unfold rev_ppoll_outcome in Hpa. unfold ppoll_plan.
  destruct (pselect_timeout (in_mem i) tsp) as [| | | | sec nsec]; cbv iota in Hpa |- *.
  1-2: rewrite Hpa; cbv iota; apply pagree_decided; exact (pagree_err_und _ _ Hpa).
  all: destruct (ppoll_sigmask (in_mem i) sig sigsetsize); cbv iota in Hpa |- *;
    try discriminate Hpa;
    try (rewrite Hpa; cbv iota; apply pagree_decided; exact (pagree_err_und _ _ Hpa)).
  all: unfold rev_ppoll_core in Hpa.
  all: destruct (rev_ppoll_scan i m ufds nfds) as [|e|cs] eqn:Hsc; cbv iota in Hpa.
  all: try discriminate Hpa.
  all: try (rewrite (pagree_scan_err _ _ _ _ _ Hsc); cbv iota;
            rewrite pagree_wba_err in Hpa;
            rewrite Hpa; cbv iota; apply pagree_decided;
            exact (pselect_finish_err_und _ _ _ _ _ Hpa)).
  all: rewrite (proj1 (pagree_scan_done _ _ _ _ _ Hsc)); cbv iota.
  all: match goal with
       | |- context [ppoll_env_deadline ?t ?c] =>
           replace (ppoll_env_deadline t c) with false
             by (unfold ppoll_env_deadline; cbv iota;
                 first [reflexivity | apply pagree_env_ready
                       | symmetry; apply pagree_env_ready])
       end; cbv iota.
  all: exact (pagree_poll _ _ _ _ _ _ _ _ _ _ _ Hsc Hpa).
Qed.

(* =========================================================================
   #78's ppoll (c1c-monitor-wait fc558cf), verbatim
   ========================================================================= *)

(** fc558cf's definitions with a [p78_] prefix, from [Fs.Select] at
    that commit.  Two changes, both of form: fc558cf's [PsToDeadline]
    carried no arguments, so its arms here read [PsToDeadline _ _] (the
    merged [pselect_timeout] is fc558cf's with the deadline's two words
    added); and fc558cf's [FdEntry] had no [FdAnon], [FdStream],
    [FdEventfd] or [FdDgram], so [p78_revents_of] declines them.  The
    copy uses the merged file's [pselect_timeout], [ppoll_sigmask],
    [ppoll_reads], [ppoll_opaque_revents], [decode_pollfds],
    [ppoll_count], [ppoll_writeback] and [writes_all_writable], whose
    text is fc558cf's. *)

Inductive P78PselectCore :=
  | P78PsGap
  | P78PsErr (e : Z)
  | P78PsDone (ret : Z) (ws : list (word * list byte)).

Definition p78_pselect_err (e : Z) : option (word * list (word * list byte)) :=
  Some (errno_ret e, []).

Definition p78_pselect_writes (i : SyscallInput) (ret : Z)
    (ws : list (word * list byte)) : option (word * list (word * list byte)) :=
  if writes_all_writable i ws then Some (Z_to_bv 64 ret, ws) else None.

Definition p78_pselect_finish (i : SyscallInput) (tsp : word)
    (tmo : PselectTimeout) (c : P78PselectCore)
    : option (word * list (word * list byte)) :=
  match c with
  | P78PsGap => None
  | P78PsErr e =>
      match tmo with
      | PsToDeadline _ _ => None
      | _ => p78_pselect_err e
      end
  | P78PsDone ret ws =>
      match tmo with
      | PsToNone => if Z.eqb ret 0 then None else p78_pselect_writes i ret ws
      | PsToZero => p78_pselect_writes i ret ws
      | PsToDeadline _ _ =>
          if Z.eqb ret 0
          then p78_pselect_writes i 0 (ws ++ [(tsp, pselect_timespec_zero)])
          else None
      | _ => None
      end
  end.

Definition p78_revents_of (m : Model) (fd events : Z) : option (list Z) :=
  if (fd <? 0)%Z then Some [0%Z]
  else match fd_lookup (m_fds m) (Z_to_bv 64 fd) with
       | None => Some [POLLNVAL]
       | Some (FdFile _ _) | Some (FdFileW _ _) | Some FdDir =>
           Some [Z.land default_pollmask events]
       | Some (FdFileRW _ _) => Some [Z.land default_pollmask events]
       | Some (FdFileA _ _) => Some [Z.land default_pollmask events]
       | Some (FdChannel _) | Some (FdSocket _) | Some (FdPipe _ _) => None
       | Some (FdDevNull _ _) => None
       | Some FdUrandom => None
       | Some (FdOpaque o) => ppoll_opaque_revents m o events
       | Some (FdAnon _ _) | Some (FdStream _ _ _) | Some (FdEventfd _)
       | Some (FdDgram _) => None   (* kinds fc558cf did not have *)
       end.

Fixpoint p78_revents (m : Model) (es : list (Z * Z)) : option (list (list Z)) :=
  match es with
  | [] => Some []
  | (fd, ev) :: rest =>
      match p78_revents_of m fd ev with
      | None => None
      | Some s =>
          match p78_revents m rest with
          | None => None
          | Some ss => Some (s :: ss)
          end
      end
  end.

Fixpoint p78_choice_in (sets : list (list Z)) (rs : list Z) : bool :=
  match sets, rs with
  | [], [] => true
  | s :: sets', r :: rs' => existsb (Z.eqb r) s && p78_choice_in sets' rs'
  | _, _ => false
  end.

Inductive P78PpollCore :=
  | P78CoreGap
  | P78CoreErr (e : Z)
  | P78CorePoll (sets : list (list Z)).

Definition p78_core (i : SyscallInput) (m : Model) (ufds nfds : word)
    : P78PpollCore :=
  let n := bv_unsigned nfds in
  if (bv_unsigned (m_nofile m) <? n)%Z then P78CoreErr EINVAL
  else if (ppoll_nfds_max <? n)%Z then P78CoreGap
  else if (negb (Z.eqb n 0) && negb (access_okb ufds (pollfd_bytes * n)))%bool
  then P78CoreErr EFAULT
  else
    match read_bytes_map (in_mem i) ufds
            (Z_to_bv 64 (pollfd_bytes * n)) with
    | None => P78CoreErr EFAULT
    | Some bs =>
        match p78_revents m (decode_pollfds bs (Z.to_nat n)) with
        | None => P78CoreGap
        | Some sets => P78CorePoll sets
        end
    end.

Definition p78_writeback_access (ufds nfds : word) (tmo : PselectTimeout)
    (c : P78PselectCore) : P78PselectCore :=
  match c with
  | P78PsDone ret _ =>
      if access_okb ufds (pollfd_bytes * bv_unsigned nfds) then c
      else match tmo with
           | PsToNone => if Z.eqb ret 0 then P78PsGap else P78PsErr EFAULT
           | _ => P78PsErr EFAULT
           end
  | _ => c
  end.

Definition p78_finish (i : SyscallInput) (ufds nfds tsp : word)
    (tmo : PselectTimeout) (rs : list Z)
    : option (word * list (word * list byte)) :=
  p78_pselect_finish i tsp tmo
    (p78_writeback_access ufds nfds tmo
       (P78PsDone (ppoll_count rs) (ppoll_writeback ufds rs))).

Definition p78_least_of (s : list Z) : Z :=
  if existsb (Z.eqb 0) s then 0%Z else hd 0%Z s.

Definition p78_most_of (s : list Z) : Z :=
  match find (fun r => negb (Z.eqb r 0)) s with
  | Some r => r
  | None => hd 0%Z s
  end.

Definition p78_least (sets : list (list Z)) : list Z := map p78_least_of sets.

Definition p78_most (sets : list (list Z)) : list Z := map p78_most_of sets.

Definition p78_answers (o : option (word * list (word * list byte))) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Definition p78_all_answered (i : SyscallInput) (ufds nfds tsp : word)
    (tmo : PselectTimeout) (sets : list (list Z)) : bool :=
  p78_choice_in sets (p78_least sets)
  && p78_choice_in sets (p78_most sets)
  && p78_answers (p78_finish i ufds nfds tsp tmo (p78_least sets))
  && p78_answers (p78_finish i ufds nfds tsp tmo (p78_most sets)).

Inductive P78PpollPlan :=
  | P78Decided (o : option (word * list (word * list byte)))
  | P78Poll (tmo : PselectTimeout) (sets : list (list Z)).

Definition p78_plan (i : SyscallInput) (m : Model)
    (ufds nfds tsp sig sigsetsize : word) : P78PpollPlan :=
  match pselect_timeout (in_mem i) tsp with
  | PsToFault => P78Decided (p78_pselect_err EFAULT)
  | PsToInval => P78Decided (p78_pselect_err EINVAL)
  | tmo =>
      match ppoll_sigmask (in_mem i) sig sigsetsize with
      | PpSigBadSize => P78Decided (p78_pselect_err EINVAL)
      | PpSigFault => P78Decided (p78_pselect_err EFAULT)
      | PpSigReal => P78Decided None
      | PpSigNone =>
          match p78_core i m ufds nfds with
          | P78CoreGap => P78Decided None
          | P78CoreErr e => P78Decided (p78_pselect_finish i tsp tmo (P78PsErr e))
          | P78CorePoll sets => P78Poll tmo sets
          end
      end
  end.

Definition p78_spec (ufds nfds tsp sig sigsetsize : word)
    : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match p78_plan i m ufds nfds tsp sig sigsetsize with
  | P78Decided None => unmodeled
  | P78Decided (Some (r, ws)) =>
      pure (with_copyins (ppoll_reads i m ufds nfds tsp sig sigsetsize)
              (mkEffect r ws []))
  | P78Poll tmo sets =>
      if negb (p78_all_answered i ufds nfds tsp tmo sets) then unmodeled
      else
        rw <- choose (fun rw => exists rs,
                p78_choice_in sets rs = true
                /\ p78_finish i ufds nfds tsp tmo rs = Some rw) ;;
        pure (with_copyins (ppoll_reads i m ufds nfds tsp sig sigsetsize)
                (mkEffect (fst rw) (snd rw) []))
  end.

(* =========================================================================
   #78's entries in the merged form
   ========================================================================= *)

(** #78's admitted [revents] of each merged entry. *)
Fixpoint p78_sets (cs : list (Z * list (Z * PpollTag))) : list (list Z) :=
  match cs with
  | [] => []
  | (fd, s) :: rest => map fst s :: p78_sets rest
  end.

(** No alternative of the entry is a stream-pair end's: every entry #78
    answers has one answer ([PpOnly]) or the environment's ([PpEnv]). *)
Definition p78_free (c : Z * list (Z * PpollTag)) : Prop :=
  forall a, In a (snd c) -> forall b, snd a <> PpEnd b.

Lemma p78_pair_same : forall x, ppoll_pair_alts (x, x) = [(x, PpOnly)].
Proof. intros x. unfold ppoll_pair_alts. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma p78_map_fst : forall (t : PpollTag) (s : list Z), map fst (map (fun r => (r, t)) s) = s.
Proof.
  intros t s. induction s as [|r s IH]; [reflexivity|].
  cbn [map fst]. rewrite IH. reflexivity.
Qed.

Lemma p78_alts : forall m fd ev s, p78_revents_of m fd ev = Some s ->
  exists t, ppoll_alts_of m fd ev = Some (map (fun r => (r, t)) s)
            /\ (t = PpOnly \/ t = PpEnv).
Proof.
  intros m fd ev s H. unfold p78_revents_of in H. unfold ppoll_alts_of, ppoll_revents_of.
  destruct (fd <? 0)%Z; cbv iota in H |- *.
  - injection H as <-. exists PpOnly. split; [reflexivity | left; reflexivity].
  - destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [e|]; cbv iota in H |- *.
    + destruct e; cbv iota in H |- *; try discriminate H.
      all: try (injection H as <-; exists PpOnly;
                split; [cbn [option_map]; rewrite p78_pair_same; reflexivity
                       | left; reflexivity]).
      exists PpEnv. split; [rewrite H; reflexivity | right; reflexivity].
    + injection H as <-. exists PpOnly. split; [reflexivity | left; reflexivity].
Qed.

Lemma p78_entries : forall m es sets, p78_revents m es = Some sets ->
  exists cs, ppoll_entries m es = Some cs /\ p78_sets cs = sets /\ Forall p78_free cs.
Proof.
  intros m. induction es as [|[fd ev] es IH]; intros sets H; cbn [p78_revents] in H.
  - injection H as <-. exists []. split; [reflexivity|]. split; [reflexivity | constructor].
  - destruct (p78_revents_of m fd ev) as [s|] eqn:Hs; [|discriminate H].
    destruct (p78_revents m es) as [sets0|] eqn:Hes; [|discriminate H].
    injection H as <-.
    destruct (IH sets0 eq_refl) as (cs & Hcs & Hsets & Hfree).
    destruct (p78_alts _ _ _ _ Hs) as (t & Ha & Ht).
    exists ((fd, map (fun r => (r, t)) s) :: cs).
    cbn [ppoll_entries]. rewrite Ha, Hcs. split; [reflexivity|].
    split; [cbn [p78_sets]; rewrite p78_map_fst, Hsets; reflexivity|].
    constructor; [|exact Hfree].
    unfold p78_free. cbn [snd]. intros a Hin b Hb.
    apply in_map_iff in Hin. destruct Hin as (r & <- & _). cbn [snd] in Hb.
    destruct Ht as [Ht|Ht]; rewrite Ht in Hb; discriminate Hb.
Qed.

(** #78's core against the merged scan: the same errno, or the merged
    entries of #78's sets. *)
Lemma p78_scan_rel : forall i m ufds nfds,
  match p78_core i m ufds nfds with
  | P78CoreGap => True
  | P78CoreErr e => ppoll_scan i m ufds nfds = PpScanErr e
  | P78CorePoll sets => exists cs, ppoll_scan i m ufds nfds = PpScanDone cs
                                   /\ p78_sets cs = sets /\ Forall p78_free cs
  end.
Proof.
  intros i m ufds nfds. unfold p78_core, ppoll_scan. cbv zeta.
  repeat (match goal with
          | |- context [if ?b then _ else _] => destruct b
          end; cbv iota; try reflexivity; try exact I).
  match goal with
  | |- context [read_bytes_map ?mp ?p ?l] => destruct (read_bytes_map mp p l) as [bs|]
  end; cbv iota; [|reflexivity].
  match goal with
  | |- context [p78_revents ?m0 ?es] => destruct (p78_revents m0 es) as [sets|] eqn:Hr
  end; cbv iota; [|exact I].
  destruct (p78_entries _ _ _ Hr) as (cs & Hcs & Hsets & Hfree).
  rewrite Hcs. cbv iota. exists cs. split; [reflexivity|]. split; [exact Hsets | exact Hfree].
Qed.

Lemma p78_und0 : forall cs, Forall p78_free cs -> ppoll_und cs = 0%Z.
Proof.
  induction cs as [|[fd s] cs IH]; intros Hf; [reflexivity|].
  cbn [ppoll_und]. rewrite (IH (Forall_inv_tail Hf)).
  replace (existsb (fun a => ppoll_is_hi (snd a)) s) with false; [reflexivity|].
  symmetry. apply not_true_iff_false. intros Hex. apply existsb_exists in Hex.
  destruct Hex as ([r t] & Hin & Hhi). pose proof (Forall_inv Hf) as Hs.
  unfold p78_free in Hs. cbn [snd] in Hs, Hhi.
  destruct t as [| |b]; cbv [ppoll_is_hi] in Hhi; try discriminate Hhi.
  exact (Hs _ Hin b eq_refl).
Qed.

Lemma p78_choice_at : forall sel cs rs, Forall p78_free cs ->
  ppoll_choice_at sel cs rs = p78_choice_in (p78_sets cs) rs.
Proof.
  intros sel. induction cs as [|[fd s] cs IH]; intros rs Hf; destruct rs as [|r rs];
    try reflexivity.
  pose proof (Forall_inv Hf) as Hs. pose proof (Forall_inv_tail Hf) as Hcs.
  unfold p78_free in Hs. cbn [snd] in Hs.
  cbn [ppoll_choice_at p78_choice_in p78_sets]. rewrite (IH rs Hcs). f_equal.
  unfold ppoll_tag_of.
  destruct (find (fun a => Z.eqb (fst a) r) s) as [[r0 t]|] eqn:Hfd; cbn [option_map snd].
  - apply find_some in Hfd. destruct Hfd as [Hin Heq]. cbn [fst] in Heq.
    apply Z.eqb_eq in Heq. subst r0.
    transitivity true.
    + destruct t as [| |b]; cbv iota; try reflexivity. exfalso. exact (Hs _ Hin b eq_refl).
    + symmetry. apply existsb_exists. exists r.
      split; [exact (in_map fst _ _ Hin) | apply Z.eqb_refl].
  - symmetry. apply not_true_iff_false. intros Hex. apply existsb_exists in Hex.
    destruct Hex as (x & Hx & Hrx). apply in_map_iff in Hx.
    destruct Hx as ([x0 t] & Hx0 & Hin). cbn [fst] in Hx0. subst x0.
    pose proof (find_none _ _ Hfd _ Hin) as Hn. cbn [fst] in Hn.
    apply Z.eqb_eq in Hrx. subst x. rewrite Z.eqb_refl in Hn. discriminate Hn.
Qed.

Lemma p78_choice_in_eq : forall cs, Forall p78_free cs ->
  forall rs, ppoll_choice_in cs rs = p78_choice_in (p78_sets cs) rs.
Proof. intros cs Hf rs. unfold ppoll_choice_in. apply p78_choice_at. exact Hf. Qed.

Lemma p78_choice_in_length : forall sets rs,
  p78_choice_in sets rs = true -> length rs = length sets.
Proof.
  induction sets as [|s sets IH]; intros [|r rs] H; cbn [p78_choice_in] in H;
    try discriminate H.
  - reflexivity.
  - apply andb_true_iff in H as [_ H]. cbn [length]. f_equal. exact (IH rs H).
Qed.

Lemma p78_least_of_eq : forall s, ppoll_least_of s = p78_least_of (map fst s).
Proof.
  intros s. unfold ppoll_least_of, p78_least_of.
  replace (existsb (fun a => Z.eqb (fst a) 0) s) with (existsb (Z.eqb 0) (map fst s));
    [reflexivity|].
  induction s as [|[r t] s IH]; [reflexivity|].
  cbn [existsb map fst]. rewrite IH, (Z.eqb_sym r 0). reflexivity.
Qed.

Lemma p78_least_eq : forall cs, ppoll_least cs = p78_least (p78_sets cs).
Proof.
  unfold ppoll_least, p78_least.
  induction cs as [|[fd s] cs IH]; [reflexivity|].
  cbn [map p78_sets snd]. rewrite p78_least_of_eq, IH. reflexivity.
Qed.

Lemma p78_find_map : forall (s : list (Z * PpollTag)),
  find (fun r => negb (Z.eqb r 0)) (map fst s)
  = option_map fst (find (fun a => negb (Z.eqb (fst a) 0)) s).
Proof.
  induction s as [|[r t] s IH]; [reflexivity|].
  cbn [map find fst]. destruct (negb (Z.eqb r 0)); [reflexivity | exact IH].
Qed.

Lemma p78_most_of_eq : forall s, (forall a, In a s -> forall b, snd a <> PpEnd b) ->
  ppoll_most_of s = p78_most_of (map fst s).
Proof.
  intros s Hs. unfold ppoll_most_of, p78_most_of.
  replace (find (fun a => ppoll_is_hi (snd a)) s) with (@None (Z * PpollTag)).
  2:{ symmetry. destruct (find (fun a => ppoll_is_hi (snd a)) s) as [[r t]|] eqn:Hf;
        [|reflexivity].
      apply find_some in Hf. destruct Hf as [Hin Hhi]. cbn [snd] in Hhi.
      destruct t as [| |b]; cbv [ppoll_is_hi] in Hhi; try discriminate Hhi.
      exfalso. exact (Hs _ Hin b eq_refl). }
  rewrite p78_find_map.
  destruct (find (fun a => negb (Z.eqb (fst a) 0)) s); reflexivity.
Qed.

Lemma p78_most_eq : forall cs, Forall p78_free cs -> ppoll_most cs = p78_most (p78_sets cs).
Proof.
  unfold ppoll_most, p78_most.
  induction cs as [|[fd s] cs IH]; intros Hf; [reflexivity|].
  cbn [map p78_sets snd].
  rewrite (p78_most_of_eq s (Forall_inv Hf)), (IH (Forall_inv_tail Hf)). reflexivity.
Qed.

Lemma p78_sets_in : forall cs fd s, In (fd, s) cs -> In (map fst s) (p78_sets cs).
Proof.
  induction cs as [|[fd0 s0] cs IH]; intros fd s H; [destruct H|].
  cbn [p78_sets]. destruct H as [H|H].
  - injection H as -> ->. left. reflexivity.
  - right. exact (IH _ _ H).
Qed.

(* =========================================================================
   #78's answers
   ========================================================================= *)

Lemma p78_finish_eq : forall i ufds nfds tsp tmo rs,
  p78_finish i ufds nfds tsp tmo rs =
  if access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z then
    match tmo with
    | PsToNone =>
        if Z.eqb (ppoll_count rs) 0 then None
        else if writes_all_writable i (ppoll_writeback ufds rs)
        then Some (Z_to_bv 64 (ppoll_count rs), ppoll_writeback ufds rs)
        else None
    | PsToZero =>
        if writes_all_writable i (ppoll_writeback ufds rs)
        then Some (Z_to_bv 64 (ppoll_count rs), ppoll_writeback ufds rs)
        else None
    | PsToDeadline _ _ =>
        if Z.eqb (ppoll_count rs) 0
        then if writes_all_writable i (ppoll_writeback ufds rs ++ [(tsp, pselect_timespec_zero)])
             then Some (Z_to_bv 64 0, ppoll_writeback ufds rs ++ [(tsp, pselect_timespec_zero)])
             else None
        else None
    | _ => None
    end
  else
    match tmo with
    | PsToNone => if Z.eqb (ppoll_count rs) 0 then None else Some (errno_ret EFAULT, [])
    | PsToDeadline _ _ => None
    | _ => Some (errno_ret EFAULT, [])
    end.
Proof.
  intros i ufds nfds tsp tmo rs.
  unfold p78_finish, p78_writeback_access, p78_pselect_finish, p78_pselect_writes,
    p78_pselect_err.
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z); destruct tmo;
    try reflexivity; destruct (Z.eqb (ppoll_count rs) 0); reflexivity.
Qed.

(** Where #78 answers a choice, the merged ppoll answers it the same,
    with no remaining time to choose. *)
Lemma p78_finish_some : forall i ufds nfds tsp tmo rs rw,
  p78_finish i ufds nfds tsp tmo rs = Some rw ->
  ppoll_finish i ufds nfds tsp tmo rs = Some (ps_one (fst rw, snd rw, None)).
Proof.
  intros i ufds nfds tsp tmo rs rw H. rewrite p78_finish_eq in H. rewrite ppoll_finish_eq.
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z);
    destruct tmo as [| | | | sec nsec]; cbv iota in H |- *; try discriminate H.
  all: repeat (match type of H with
               | context [if ?b then _ else _] =>
                   destruct b; cbv iota in H |- *; try discriminate H
               end).
  all: injection H as <-; reflexivity.
Qed.

Lemma p78_wb_len0 : forall i p rs rs', length rs = length rs' ->
  writes_all_writable i (ppoll_writeback p rs)
  = writes_all_writable i (ppoll_writeback p rs').
Proof.
  intros i p rs rs' H.
  rewrite <- (app_nil_r (ppoll_writeback p rs)), <- (app_nil_r (ppoll_writeback p rs')).
  apply pagree_wb_len. exact H.
Qed.

Lemma p78_count_nz : forall rs r, In r rs -> r <> 0%Z -> ppoll_count rs <> 0%Z.
Proof.
  induction rs as [|r0 rs IH]; intros r Hin Hr; [destruct Hin|].
  cbn [ppoll_count]. pose proof (ppoll_count_bounds rs) as Hb.
  destruct Hin as [<-|Hin].
  - destruct (Z.eqb_spec r0 0) as [E|E]; cbv iota; [exfalso; exact (Hr E) | lia].
  - pose proof (IH r Hin Hr) as Hn. destruct (Z.eqb r0 0); cbv iota; lia.
Qed.

Lemma p78_most_of_nz : forall s r, In r s -> r <> 0%Z -> p78_most_of s <> 0%Z.
Proof.
  intros s r Hin Hr. unfold p78_most_of.
  destruct (find (fun r0 => negb (Z.eqb r0 0)) s) as [r0|] eqn:Hf.
  - apply find_some in Hf. destruct Hf as [_ Hf]. cbv beta in Hf.
    apply negb_true_iff, Z.eqb_neq in Hf. exact Hf.
  - pose proof (find_none _ _ Hf r Hin) as Hn. cbv beta in Hn.
    apply negb_false_iff, Z.eqb_eq in Hn. contradiction.
Qed.

(** Where every choice counts 0, LEAST does. *)
Lemma p78_least_zero : forall sets rs, p78_choice_in sets rs = true ->
  Forall (fun r => r = 0%Z) rs -> Forall (fun r => r = 0%Z) (p78_least sets).
Proof.
  unfold p78_least. induction sets as [|s sets IH]; intros rs Hc Hz; [constructor|].
  destruct rs as [|r rs]; cbn [p78_choice_in] in Hc; [discriminate Hc|].
  apply andb_true_iff in Hc as [Hr Hc].
  cbn [map]. constructor.
  - pose proof (Forall_inv Hz) as Hr0. cbv beta in Hr0 |- *. subst r.
    unfold p78_least_of. rewrite Hr. reflexivity.
  - exact (IH rs Hc (Forall_inv_tail Hz)).
Qed.

(** Where MOST counts 0, every choice does. *)
Lemma p78_most_zero : forall sets rs, p78_choice_in sets rs = true ->
  Forall (fun r => r = 0%Z) (p78_most sets) -> Forall (fun r => r = 0%Z) rs.
Proof.
  unfold p78_most. induction sets as [|s sets IH]; intros rs Hc Hz;
    destruct rs as [|r rs]; cbn [p78_choice_in] in Hc; try discriminate Hc; [constructor|].
  apply andb_true_iff in Hc as [Hr Hc]. cbn [map] in Hz.
  constructor.
  - cbv beta. destruct (Z.eq_dec r 0) as [E|E]; [exact E|exfalso].
    apply existsb_exists in Hr. destruct Hr as (x & Hx & Hrx).
    apply Z.eqb_eq in Hrx. subst x.
    exact (p78_most_of_nz s r Hx E (Forall_inv Hz)).
  - exact (IH rs Hc (Forall_inv_tail Hz)).
Qed.

(** #78's [p78_all_answered] answers every choice. *)
Lemma p78_all_answered_sound : forall i ufds nfds tsp tmo sets,
  (access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z = false -> sets = []) ->
  p78_all_answered i ufds nfds tsp tmo sets = true ->
  forall rs, p78_choice_in sets rs = true -> p78_finish i ufds nfds tsp tmo rs <> None.
Proof.
  intros i ufds nfds tsp tmo sets Hacc Hg rs Hc.
  unfold p78_all_answered in Hg.
  apply andb_true_iff in Hg as [Hg Ham]. apply andb_true_iff in Hg as [Hg Hal].
  apply andb_true_iff in Hg as [_ Hcm].
  pose proof (p78_choice_in_length _ _ Hc) as Hlen.
  assert (Hll : length rs = length (p78_least sets))
    by (unfold p78_least; rewrite length_map; exact Hlen).
  assert (Hlm : length rs = length (p78_most sets))
    by (unfold p78_most; rewrite length_map; exact Hlen).
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z) eqn:Ha.
  2:{ specialize (Hacc eq_refl). subst sets.
      destruct rs as [|r rs]; [|cbn [length] in Hlen; discriminate Hlen].
      unfold p78_least in Hal. cbn [map] in Hal. intros E. rewrite E in Hal.
      cbv [p78_answers] in Hal. discriminate Hal. }
  unfold p78_answers in Hal, Ham.
  rewrite p78_finish_eq in Hal. rewrite p78_finish_eq in Ham. rewrite p78_finish_eq.
  rewrite Ha in Hal, Ham |- *. cbv iota in Hal, Ham |- *.
  destruct tmo as [| | | | sec nsec]; cbv iota in Hal, Ham |- *;
    try discriminate Hal.
  - destruct (Z.eqb (ppoll_count (p78_least sets)) 0) eqn:Hl0; cbv iota in Hal;
      [discriminate Hal|].
    destruct (writes_all_writable i (ppoll_writeback ufds (p78_least sets))) eqn:Hw;
      cbv iota in Hal; [|discriminate Hal].
    destruct (Z.eqb (ppoll_count rs) 0) eqn:Hr0; cbv iota.
    + exfalso. apply Z.eqb_eq, pagree_count_zero in Hr0.
      rewrite (pagree_zero_count _ (p78_least_zero _ _ Hc Hr0)), Z.eqb_refl in Hl0.
      discriminate Hl0.
    + rewrite (p78_wb_len0 i ufds rs (p78_least sets) Hll), Hw. cbv iota.
      intros E. discriminate E.
  - destruct (writes_all_writable i (ppoll_writeback ufds (p78_least sets))) eqn:Hw;
      cbv iota in Hal; [|discriminate Hal].
    rewrite (p78_wb_len0 i ufds rs (p78_least sets) Hll), Hw. cbv iota.
    intros E. discriminate E.
  - destruct (Z.eqb (ppoll_count (p78_most sets)) 0) eqn:Hm0; cbv iota in Ham;
      [|discriminate Ham].
    destruct (writes_all_writable i
                (ppoll_writeback ufds (p78_most sets) ++ [(tsp, pselect_timespec_zero)]))
      eqn:Hw; cbv iota in Ham; [|discriminate Ham].
    apply Z.eqb_eq, pagree_count_zero in Hm0.
    assert (Hr0 : Z.eqb (ppoll_count rs) 0 = true)
      by (apply Z.eqb_eq, pagree_zero_count, (p78_most_zero _ _ Hc Hm0)).
    rewrite Hr0. cbv iota.
    rewrite (pagree_wb_len i ufds rs (p78_most sets) _ Hlm), Hw. cbv iota.
    intros E. discriminate E.
Qed.

(** An environment's entry that can be ready makes MOST count. *)
Lemma p78_env_count : forall cs, ppoll_env_ready cs = true ->
  ppoll_count (p78_most (p78_sets cs)) <> 0%Z.
Proof.
  intros cs H. unfold ppoll_env_ready in H. apply existsb_exists in H.
  destruct H as ([fd s] & Hin & Hs). cbn [snd] in Hs. apply existsb_exists in Hs.
  destruct Hs as ([r t] & Hr & Ht). cbn [fst snd] in Ht.
  destruct t; cbv iota in Ht; try discriminate Ht.
  apply negb_true_iff, Z.eqb_neq in Ht.
  apply (p78_count_nz _ (p78_most_of (map fst s))).
  - unfold p78_most. apply in_map. exact (p78_sets_in _ _ _ Hin).
  - apply (p78_most_of_nz _ r); [exact (in_map fst _ _ Hr) | exact Ht].
Qed.

(** So where #78 answers at [do_poll], the merged plan does not decline
    a real deadline. *)
Lemma p78_env_deadline : forall i ufds nfds tsp tmo cs,
  p78_all_answered i ufds nfds tsp tmo (p78_sets cs) = true ->
  ppoll_env_deadline tmo cs = false.
Proof.
  intros i ufds nfds tsp tmo cs Hall. unfold ppoll_env_deadline.
  destruct tmo as [| | | | sec nsec]; cbv iota; try reflexivity.
  apply not_true_iff_false. intros Henv.
  pose proof (p78_env_count cs Henv) as Hn.
  unfold p78_all_answered in Hall. apply andb_true_iff in Hall as [_ Ham].
  unfold p78_answers in Ham. rewrite p78_finish_eq in Ham.
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z); cbv iota in Ham;
    [|discriminate Ham].
  apply Z.eqb_neq in Hn. rewrite Hn in Ham. cbv iota in Ham. discriminate Ham.
Qed.

(** A decided answer with no choice in it is #78's one effect. *)
Lemma p78_fixed : forall reads r ws i m o,
  pselect_answer reads (ps_fixed r ws) (fun _ m0 => m0) i m o
  <-> pure (with_copyins reads (mkEffect r ws [])) i m o.
Proof.
  intros reads r ws i m o. rewrite pselect_answer_iff. unfold pure. split.
  - intros (sel & eff & _ & He & ->).
    unfold ps_fixed, pselect_effect in He. cbn [pa_ans] in He. subst eff. reflexivity.
  - intros ->. exists 0%Z, (with_copyins reads (mkEffect r ws [])).
    split; [reflexivity|]. split; [|reflexivity].
    unfold ps_fixed, pselect_effect. cbn [pa_ans]. reflexivity.
Qed.

(** At [do_poll]: the merged choices are #78's. *)
Lemma p78_poll : forall i m ufds nfds tsp sig sigsetsize tmo cs o,
  ppoll_scan i m ufds nfds = PpScanDone cs ->
  Forall p78_free cs ->
  p78_all_answered i ufds nfds tsp tmo (p78_sets cs) = true ->
  (if negb (ppoll_all_answered i ufds nfds tsp tmo cs) then unmodeled
   else
     c <- choose (fun c : list Z * PselectAnswers =>
            ppoll_choice_in cs (fst c) = true
            /\ ppoll_finish i ufds nfds tsp tmo (fst c) = Some (snd c)) ;;
     pselect_answer (ppoll_reads i m ufds nfds tsp sig sigsetsize) (snd c)
       (fun _ => ppoll_rec cs (fst c))) i m o
  <-> (rw <- choose (fun rw => exists rs,
                p78_choice_in (p78_sets cs) rs = true
                /\ p78_finish i ufds nfds tsp tmo rs = Some rw) ;;
       pure (with_copyins (ppoll_reads i m ufds nfds tsp sig sigsetsize)
               (mkEffect (fst rw) (snd rw) []))) i m o.
Proof.
  intros i m ufds nfds tsp sig sigsetsize tmo cs o Hscan Hfree Hall78.
  assert (Hacc : access_okb ufds (pollfd_bytes * bv_unsigned nfds)%Z = false ->
                 p78_sets cs = []).
  { intros Ha. rewrite (proj2 (ppoll_scan_done _ _ _ _ _ Hscan) Ha). reflexivity. }
  pose proof (p78_all_answered_sound _ _ _ _ _ _ Hacc Hall78) as Hsound.
  assert (Hall : ppoll_all_answered i ufds nfds tsp tmo cs = true).
  { pose proof Hall78 as Hg. unfold p78_all_answered in Hg. unfold ppoll_all_answered.
    rewrite (p78_least_eq cs), (p78_most_eq cs Hfree), !(p78_choice_in_eq cs Hfree).
    apply andb_true_iff in Hg as [Hg Ham]. apply andb_true_iff in Hg as [Hg Hal].
    apply andb_true_iff in Hg as [Hcl Hcm].
    rewrite Hcl, Hcm. cbn [andb].
    destruct (p78_finish i ufds nfds tsp tmo (p78_least (p78_sets cs))) as [rw|] eqn:El;
      [|cbv [p78_answers] in Hal; discriminate Hal].
    destruct (p78_finish i ufds nfds tsp tmo (p78_most (p78_sets cs))) as [rw'|] eqn:Em;
      [|cbv [p78_answers] in Ham; discriminate Ham].
    rewrite (p78_finish_some _ _ _ _ _ _ _ El), (p78_finish_some _ _ _ _ _ _ _ Em).
    reflexivity. }
  rewrite Hall. cbn [negb]. rewrite !bind_choose_iff. split.
  - intros ([rs pa] & (Hch & Hf) & Hans). cbn [fst snd] in Hch, Hf, Hans.
    rewrite (p78_choice_in_eq cs Hfree) in Hch.
    destruct (p78_finish i ufds nfds tsp tmo rs) as [rw|] eqn:E78;
      [|exfalso; exact (Hsound rs Hch E78)].
    rewrite (p78_finish_some _ _ _ _ _ _ _ E78) in Hf. injection Hf as <-.
    apply pselect_answer_iff in Hans. destruct Hans as (sel & eff & _ & He & ->).
    unfold ps_one, pselect_effect in He. cbn [pa_ans] in He. subst eff.
    exists rw. split; [exists rs; split; [exact Hch | exact E78]|].
    cbv beta delta [pure]. rewrite (ppoll_rec_und0 cs rs m (p78_und0 cs Hfree)).
    reflexivity.
  - intros (rw & (rs & Hch & Hf) & Hp). cbv beta delta [pure] in Hp. subst o.
    exists (rs, ps_one (fst rw, snd rw, None)). cbn [fst snd].
    split; [split|].
    + rewrite (p78_choice_in_eq cs Hfree). exact Hch.
    + exact (p78_finish_some _ _ _ _ _ _ _ Hf).
    + apply pselect_answer_iff.
      exists 0%Z, (with_copyins (ppoll_reads i m ufds nfds tsp sig sigsetsize)
                     (mkEffect (fst rw) (snd rw) [])).
      split; [reflexivity|]. split.
      * unfold ps_one, pselect_effect. cbn [pa_ans]. reflexivity.
      * cbv beta. rewrite (ppoll_rec_und0 cs rs m (p78_und0 cs Hfree)). reflexivity.
Qed.

(** #78: wherever #78's ppoll answers, the merged ppoll admits exactly
    the outcomes it admits. *)
Theorem ppoll_spec_agrees_with_pr78 :
  forall ufds nfds tsp sig sigsetsize i m,
  ~ p78_spec ufds nfds tsp sig sigsetsize i m Unmodeled ->
  forall o, ppoll_spec ufds nfds tsp sig sigsetsize i m o
            <-> p78_spec ufds nfds tsp sig sigsetsize i m o.
Proof.
  intros ufds nfds tsp sig sigsetsize i m H78 o.
  unfold ppoll_spec, p78_spec in *.
  rewrite bind_input_iff in H78; cbv beta in H78.
  rewrite bind_get_model in H78; cbv beta in H78.
  rewrite !bind_input_iff; cbv beta.
  rewrite !bind_get_model; cbv beta.
  unfold ppoll_plan, p78_plan in H78 |- *.
  destruct (pselect_timeout (in_mem i) tsp) as [| | | | sec nsec]; cbv iota in H78 |- *.
  1-2: unfold pselect_err, p78_pselect_err; cbv iota; apply p78_fixed.
  all: destruct (ppoll_sigmask (in_mem i) sig sigsetsize); cbv iota in H78 |- *;
    [ | unfold pselect_err, p78_pselect_err; cbv iota; apply p78_fixed
      | unfold pselect_err, p78_pselect_err; cbv iota; apply p78_fixed
      | reflexivity ].
  all: pose proof (p78_scan_rel i m ufds nfds) as Hrel.
  all: destruct (p78_core i m ufds nfds) as [|e|sets]; cbv iota in H78, Hrel |- *.
  all: try (exfalso; apply H78; exact eq_refl).
  all: try (rewrite Hrel; cbv iota;
            unfold pselect_finish, p78_pselect_finish in H78 |- *; cbv iota in H78 |- *;
            first [ exfalso; apply H78; exact eq_refl
                  | unfold pselect_err, p78_pselect_err; cbv iota; apply p78_fixed ]).
  all: destruct Hrel as (cs & Hscan & <- & Hfree).
  all: rewrite Hscan; cbv iota.
  all: match goal with
       | |- context [p78_all_answered ?a ?b ?c ?d ?t ?s] =>
           destruct (p78_all_answered a b c d t s) eqn:Hall78
       end; cbn [negb] in H78 |- *; [|exfalso; apply H78; exact eq_refl].
  all: rewrite (p78_env_deadline _ _ _ _ _ _ Hall78); cbv iota.
  all: exact (p78_poll _ _ _ _ _ _ _ _ _ _ Hscan Hfree Hall78).
Qed.
