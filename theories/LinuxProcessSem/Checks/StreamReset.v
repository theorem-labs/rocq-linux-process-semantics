(** * LinuxProcessSem.Checks.StreamReset — the survivor's reset state: it only moves forward, its first observation fixes it for both routes, it is reported at most once, and only the end's own calls write it

    [State.se_reset] records what a stream-pair end has shown of the
    error its peer's close may have left ([State.ResetState]; the design
    is dispatch://OSSV-287/artifact/d2-design-md).  Two routes show it,
    and both write it: the empty read ([Fs.ReadWrite.stream_read_reset],
    reached by [read_spec], [readv_spec] and [recvfrom_spec]) and a
    [ppoll] that names the end ([Fs.Select.ppoll_record], through
    [ppoll_spec]).  This file proves the four properties the design
    names, over THOSE spec arms on a survivor (read, readv, recvfrom,
    ppoll, and pselect6, which records nothing) and over the functions
    they call:

    1. ONLY FORWARD ([reads_on_forward], [ppoll_forward],
       [pselect6_keeps_the_model]): none of those arms moves [se_reset]
       back.  [RsNone] stays [RsNone] and [RsPending] becomes only
       [RsPending] or [RsNone].  The one-field updates below
       ([se_reset_of_set_rx] and the rest) keep the field, and
       [se_reset_of_fresh] says [State.stream_fresh], which [socketpair]
       uses for its two new ends, starts at [RsUnknown].
    2. THE FIRST OBSERVATION FIXES THE STATE FOR BOTH ROUTES
       ([decided_read_has_one_answer], [decided_ppoll_has_one_answer],
       and the three compositions after them): once [se_reset] is not
       [RsUnknown], the empty read and the ppoll each admit exactly one
       answer, a function of the state.
    3. AT MOST ONE RESET PER END ([reads_on_reset_leaves_none],
       [reads_on_after_none], [reads_on_at_most_one_reset],
       [ppoll_keeps_a_decided_end]): a read that answers -ECONNRESET
       leaves [RsNone], and with the peer gone, the queue empty and
       [RsNone] no read answers -ECONNRESET and no ppoll moves the end.
    4. A SINGLE REPORTER ([reads_on_single_reporter],
       [ppoll_single_reporter]): a read or a ppoll changes [se_reset]
       only on the end its descriptor holds, and only while that end's
       peer is gone.  The end that closed reports nothing: its entry is
       gone.

    NOT PROVED, each by name:
    - That no OTHER arm writes [se_reset], and so lemma 3 over a run
      with other calls between the two reads.  The read lemmas also
      assume the read's descriptor holds a stream end; a read on another
      kind is not one of them.
    - Lemma 2's compositions ([ppoll_clear_then_read_eof],
      [ppoll_set_then_read_reset]) are stated over the choice bit
      [ppoll_record] stores, for the call right after the ppoll, not over
      the [revents] in the ppoll's effect; the checker reads that bit
      back from [revents] ([Checks.Sys.Fs.Select.ppoll_rd]).
      [decided_ppoll_has_one_answer] is stated for one entry's masks
      ([Fs.Select.ppoll_revents_of]), not for the whole of [ppoll_spec].
    The first holds by reading the model: [State.se_set_reset] is the
    only function that changes the field, and it is called only by
    [Fs.ReadWrite.stream_read_reset] and [Fs.Select.ppoll_record]; every
    other arm that rewrites an end goes through the one-field updates
    above, which keep the field, and only [State.stream_fresh] builds an
    end at [RsUnknown].  This is the per-arm form that [Checks.AnonAgree]
    takes for its own replicated state, for the same reason.  The
    revision owner kept that scope for this state on 2026-11-02
    (dispatch://OSSV-287/artifact/d2-design-md).

    ONE HOLDER.  [se_reset] is kept in the descriptor entry, where Linux
    keeps [sk_err] on the socket that every descriptor of it shares.  The
    two agree because no arm makes a second descriptor of an end: [dup],
    [dup3], [fcntl] F_DUPFD, a [clone] whose table holds an end, a reopen
    through /proc/self/fd/N and [sendmsg] all decline
    ([Checks.Cases.Net.StreamReset.guard_no_second_descriptor_of_the_survivor]).
    Lemmas 3 and 4 depend on that.

    THE TRIGGER for proving it for every arm of the dispatch table (the
    whole-table form of [Checks.VmMapsDisjoint.checked_table_preserves_vm]):
    the FIRST arm found, in review or by a failing proof, that writes
    [se_reset] other than through [State.se_set_reset] in the two
    functions above, that builds a [StreamEnd] other than through
    [State.stream_fresh] and the one-field updates, or that makes a
    second descriptor of a stream-pair end.

    Nothing here is assumed: no axiom, no admitted step. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The order the state moves in
   ========================================================================= *)

(** [reset_forward r r']: [r'] is [r], or later than [r]. *)
Definition reset_forward (r r' : ResetState) : Prop :=
  match r with
  | RsUnknown => True
  | RsPending => r' = RsPending \/ r' = RsNone
  | RsNone => r' = RsNone
  end.

Lemma reset_forward_refl : forall r, reset_forward r r.
Proof. intros []; cbn; auto. Qed.

Lemma reset_forward_none : forall r, reset_forward r RsNone.
Proof. intros []; cbn; auto. Qed.

(** Only [RsUnknown] is before [RsUnknown]: no step writes it. *)
Lemma reset_forward_to_unknown : forall r, reset_forward r RsUnknown -> r = RsUnknown.
Proof. intros [] H; cbn in H; [reflexivity | destruct H; discriminate | discriminate]. Qed.

(** Every stream end of the table after a step was the same end at the
    same descriptor before it, with a state no later than its new one. *)
Definition resets_forward (fds fds' : list (word * FdEntry)) : Prop :=
  forall fd id s st',
    fd_lookup fds' fd = Some (FdStream id s st') ->
    exists st, fd_lookup fds fd = Some (FdStream id s st)
               /\ reset_forward (se_reset st) (se_reset st').

(** The one-field updates every other arm writes an end with carry
    [se_reset] across unchanged, and a new end starts at [RsUnknown]. *)
Lemma se_reset_of_set_rx : forall st q, se_reset (se_set_rx st q) = se_reset st.
Proof. reflexivity. Qed.
Lemma se_reset_of_set_nonblock : forall st b, se_reset (se_set_nonblock st b) = se_reset st.
Proof. reflexivity. Qed.
Lemma se_reset_of_set_sndbuf : forall st v, se_reset (se_set_sndbuf st v) = se_reset st.
Proof. reflexivity. Qed.
Lemma se_reset_of_set_rcvbuf : forall st v, se_reset (se_set_rcvbuf st v) = se_reset st.
Proof. reflexivity. Qed.
Lemma se_reset_of_add_shut : forall st rd wr, se_reset (se_add_shut st rd wr) = se_reset st.
Proof. reflexivity. Qed.
Lemma se_reset_of_fresh : forall nb s r, se_reset (stream_fresh nb s r) = RsUnknown.
Proof. reflexivity. Qed.

(* =========================================================================
   The fd table
   ========================================================================= *)

Lemma sr_bv_eqb_neq : forall a b : word, a <> b -> bv_eqb a b = false.
Proof.
  intros a b H. destruct (bv_eqb a b) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. contradiction.
Qed.

Lemma sr_lookup_filter_neq : forall fds fd fd', fd' <> fd ->
  fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) fd' = fd_lookup fds fd'.
Proof.
  induction fds as [|[k e] fds IH]; intros fd fd' Hne; [reflexivity|].
  cbn [List.filter fst].
  destruct (bv_eqb k fd) eqn:Hk.
  - apply bv_eqb_eq in Hk. subst k.
    cbn [negb]. rewrite IH by exact Hne. cbn [fd_lookup].
    rewrite (sr_bv_eqb_neq fd fd') by congruence. reflexivity.
  - cbn [negb fd_lookup]. destruct (bv_eqb k fd'); [reflexivity | apply IH; exact Hne].
Qed.

Lemma sr_lookup_insert_eq : forall fds fd e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros. unfold fd_insert. cbn [fd_lookup]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma sr_lookup_insert_neq : forall fds fd e fd', fd' <> fd ->
  fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd'.
Proof.
  intros fds fd e fd' Hne. unfold fd_insert. cbn [fd_lookup].
  rewrite (sr_bv_eqb_neq fd fd') by congruence. cbv beta iota.
  apply sr_lookup_filter_neq. exact Hne.
Qed.

Lemma sr_neq_of_eqb : forall a b : word, bv_eqb a b = false -> a <> b.
Proof. intros a b E ->. rewrite bv_eqb_refl in E. discriminate E. Qed.

(** A table with no end [(id, s)] keeps none when an entry is put in
    front of it that is not that end, or when entries are taken out. *)
Lemma sr_stream_end_cons_none : forall fds k e id s,
  stream_end ((k, e) :: fds) id s = None ->
  stream_end fds id s = None /\ forall l, stream_end ((k, e) :: l) id s = stream_end l id s.
Proof.
  intros fds k e id s H.
  destruct e; cbn [stream_end] in H |- *;
    try (split; [exact H | intros l; reflexivity]).
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Ec end;
    [discriminate H|].
  split; [exact H|]. intros l. cbn [stream_end]. try rewrite Ec. reflexivity.
Qed.

Lemma sr_stream_end_filter_none : forall f fds id s,
  stream_end fds id s = None -> stream_end (List.filter f fds) id s = None.
Proof.
  intros f fds id s. induction fds as [|[k e] fds IH]; intros H; [reflexivity|].
  destruct (sr_stream_end_cons_none _ _ _ _ _ H) as [Hr Hc].
  cbn [List.filter]. destruct (f (k, e)); cbv iota.
  - rewrite Hc. exact (IH Hr).
  - exact (IH Hr).
Qed.

(** Putting the end [(id, side)] at [fd] does not bring its peer back. *)
Lemma sr_peer_insert_none : forall fds fd id side st',
  stream_peer fds id side = None ->
  stream_peer (fd_insert fds fd (FdStream id side st')) id side = None.
Proof.
  intros fds fd id side st' H. unfold stream_peer in *. unfold fd_insert.
  cbn [stream_end]. rewrite bv_eqb_refl.
  destruct side; cbn [andb Bool.eqb negb];
    apply sr_stream_end_filter_none; exact H.
Qed.

(* =========================================================================
   What ppoll records
   ========================================================================= *)

Lemma sr_lookup_record : forall fds0 und sel fds k,
  fd_lookup (map (fun p => (fst p, ppoll_record_entry fds0 und sel (fst p) (snd p))) fds) k
  = option_map (ppoll_record_entry fds0 und sel k) (fd_lookup fds k).
Proof.
  intros fds0 und sel fds k. induction fds as [|[k0 e0] fds IH]; [reflexivity|].
  cbn [map fd_lookup fst snd].
  destruct (bv_eqb k0 k) eqn:E.
  - apply bv_eqb_eq in E. subst k0. reflexivity.
  - exact IH.
Qed.

Lemma lookup_ppoll_record : forall fds und sel k,
  fd_lookup (ppoll_record fds und sel) k
  = option_map (ppoll_record_entry fds und sel k) (fd_lookup fds k).
Proof. intros. unfold ppoll_record. apply sr_lookup_record. Qed.

(** The record rewrites a stream end into the same end, and changes its
    state only from [RsUnknown], only where the call's undecided set
    names the descriptor, and only while the peer is gone. *)
Lemma ppoll_record_entry_stream : forall fds und sel k e id s st',
  ppoll_record_entry fds und sel k e = FdStream id s st' ->
  exists st, e = FdStream id s st /\
    (st' = st
     \/ (Z.testbit und (bv_unsigned k) = true /\ stream_peer fds id s = None
         /\ se_reset st = RsUnknown
         /\ st' = se_set_reset st
                    (if Z.testbit sel (bv_unsigned k) then RsPending else RsNone))).
Proof.
  intros fds und sel k e id s st' H.
  destruct e; cbn [ppoll_record_entry] in H; try discriminate H.
  match goal with |- exists st0, FdStream ?a ?b ?c = _ /\ _ =>
    rename a into eid, b into eside, c into est end.
  destruct (Z.testbit und (bv_unsigned k)) eqn:Hu; cbv beta iota in H.
  2:{ injection H as <- <- <-. exists est. split; [reflexivity|left; reflexivity]. }
  destruct (stream_peer fds eid eside) as [pp|] eqn:Hp; cbv beta iota in H.
  { injection H as <- <- <-. exists est. split; [reflexivity|left; reflexivity]. }
  destruct (se_reset est) eqn:Hr; cbv beta iota in H;
    injection H as <- <- <-; exists est; (split; [reflexivity|]).
  - right. split; [reflexivity|split; [exact Hp|split; [exact Hr|reflexivity]]].
  - left; reflexivity.
  - left; reflexivity.
Qed.

Lemma sr_stream_end_record_none : forall fds0 und sel fds id s,
  stream_end fds id s = None ->
  stream_end (map (fun p => (fst p, ppoll_record_entry fds0 und sel (fst p) (snd p))) fds)
    id s = None.
Proof.
  intros fds0 und sel fds id s. induction fds as [|[k e] fds IH]; intros H; [reflexivity|].
  destruct (sr_stream_end_cons_none _ _ _ _ _ H) as [Hr _].
  cbn [map fst snd].
  destruct (ppoll_record_entry fds0 und sel k e) eqn:E; cbn [stream_end];
    try exact (IH Hr).
  apply ppoll_record_entry_stream in E. destruct E as (st0 & -> & _).
  match goal with |- (if ?c then _ else _) = _ => destruct c eqn:Ec end.
  - cbn [stream_end] in H. rewrite Ec in H. discriminate H.
  - exact (IH Hr).
Qed.

(** A ppoll does not bring a peer back. *)
Lemma peer_ppoll_record_none : forall fds und sel id side,
  stream_peer fds id side = None ->
  stream_peer (ppoll_record fds und sel) id side = None.
Proof.
  intros fds und sel id side H. unfold stream_peer, ppoll_record in *.
  apply sr_stream_end_record_none. exact H.
Qed.

(** A ppoll that recorded at [k] wrote what its [revents] showed. *)
Lemma ppoll_record_at : forall fds und sel k id side st,
  fd_lookup fds k = Some (FdStream id side st) ->
  stream_peer fds id side = None -> se_reset st = RsUnknown ->
  Z.testbit und (bv_unsigned k) = true ->
  fd_lookup (ppoll_record fds und sel) k
  = Some (FdStream id side
            (se_set_reset st (if Z.testbit sel (bv_unsigned k) then RsPending else RsNone))).
Proof.
  intros fds und sel k id side st Hk Hp Hr Hu.
  rewrite lookup_ppoll_record, Hk. cbn [option_map ppoll_record_entry].
  rewrite Hu, Hp, Hr. reflexivity.
Qed.

(** A ppoll leaves an end that has shown its error exactly as it was. *)
Lemma ppoll_record_keeps_decided : forall fds und sel k id side st,
  fd_lookup fds k = Some (FdStream id side st) -> se_reset st <> RsUnknown ->
  fd_lookup (ppoll_record fds und sel) k = Some (FdStream id side st).
Proof.
  intros fds und sel k id side st Hk Hr.
  rewrite lookup_ppoll_record, Hk. cbn [option_map ppoll_record_entry].
  destruct (Z.testbit und (bv_unsigned k)); [|reflexivity].
  destruct (stream_peer fds id side); [reflexivity|].
  destruct (se_reset st) eqn:Hr'; [exfalso; congruence|reflexivity|reflexivity].
Qed.

Lemma record_forward : forall fds und sel, resets_forward fds (ppoll_record fds und sel).
Proof.
  intros fds und sel. unfold resets_forward. intros fd id s st' H.
  rewrite lookup_ppoll_record in H.
  destruct (fd_lookup fds fd) as [e|] eqn:He; cbn [option_map] in H; [|discriminate H].
  injection H as H.
  apply ppoll_record_entry_stream in H.
  destruct H as (st & -> & [-> | (_ & _ & Hr & _)]).
  - exists st. split; [first [exact He | reflexivity] | apply reset_forward_refl].
  - exists st. split; [first [exact He | reflexivity]|]. rewrite Hr. exact I.
Qed.

(** What ppoll_spec does to the model: the record of one choice. *)
Lemma ppoll_spec_records : forall ufds nfds tsp sig sigsetsize i m eff m' evs,
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs) ->
  exists pa sel, ppoll_outcome i m ufds nfds tsp sig sigsetsize = Some pa
    /\ m' = with_fds (ppoll_record (m_fds m) (pa_und pa) sel) m.
Proof.
  intros ufds nfds tsp sig sigsetsize i m eff m' evs H.
  apply check_ppoll_complete_ok in H. unfold check_ppoll in H.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [pa|]; [|discriminate H].
  apply check_pselect_answer_model in H.
  exists pa, (Z.land (pa_und pa) (ppoll_rd i m ufds nfds (eff_writes eff))).
  split; [reflexivity|exact H].
Qed.

(** The call's undecided set is empty, or it is [ppoll_undecided] of the
    entries [do_poll] scanned. *)
Lemma pselect_finish_und : forall i tsp tmo c pa,
  pselect_finish i tsp tmo c = Some pa ->
  pa_und pa = 0%Z \/ exists und ans, c = PsCoreDone und ans /\ pa_und pa = und.
Proof.
  intros i tsp tmo c pa H.
  destruct c as [| e0 | und ans]; unfold pselect_finish in H.
  - discriminate H.
  - left. destruct tmo as [| | | | sec nsec]; cbv beta iota in H;
      try (unfold pselect_err, ps_fixed in H; injection H as <-; reflexivity).
    destruct (writes_all_writable i [(tsp, pselect_timespec_zero)]);
      cbv beta iota in H; [|discriminate H].
    injection H as <-. reflexivity.
  - right. exists und, ans. split; [reflexivity|].
    destruct (ans 0%Z) as [r0 ws0]. cbv beta iota in H.
    destruct tmo as [| | | | sec nsec]; cbv beta iota in H; try discriminate H.
    + destruct (r0 =? 0)%Z; cbv beta iota in H; [discriminate H|].
      destruct (writes_all_writable i ws0); cbv beta iota in H; [|discriminate H].
      injection H as <-. reflexivity.
    + destruct (writes_all_writable i ws0); cbv beta iota in H; [|discriminate H].
      injection H as <-. reflexivity.
    + destruct (writes_all_writable i (ws0 ++ [(tsp, pselect_timespec_zero)]));
        cbv beta iota in H; [|discriminate H].
      injection H as <-. reflexivity.
Qed.

Lemma writeback_access_done : forall ufds nfds tmo c und ans,
  ppoll_writeback_access ufds nfds tmo c = PsCoreDone und ans -> c = PsCoreDone und ans.
Proof.
  intros ufds nfds tmo c und ans H.
  destruct c as [| e0 | und0 ans0]; unfold ppoll_writeback_access in H;
    cbv beta iota in H; try exact H.
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)); [exact H|].
  destruct tmo; try discriminate H.
  destruct (fst (ans0 0%Z) =? 0)%Z; discriminate H.
Qed.

Lemma ppoll_outcome_und : forall i m ufds nfds tsp sig sigsetsize pa,
  ppoll_outcome i m ufds nfds tsp sig sigsetsize = Some pa ->
  pa_und pa = 0%Z
  \/ exists cs, ppoll_scan i m ufds nfds = PpScanDone cs /\ pa_und pa = ppoll_undecided cs.
Proof.
  intros i m ufds nfds tsp sig sigsetsize pa H.
  unfold ppoll_outcome in H.
  destruct (pselect_timeout (in_mem i) tsp) as [| | | | sec nsec]; cbv beta iota in H;
    try (unfold pselect_err, ps_fixed in H; injection H as <-; left; reflexivity).
  all: destruct (ppoll_sigmask (in_mem i) sig sigsetsize); cbv beta iota in H;
    try (unfold pselect_err, ps_fixed in H; injection H as <-; left; reflexivity);
    try discriminate H.
  all: apply pselect_finish_und in H;
    destruct H as [H|(und & ans & Hc & Hu)]; [left; exact H|right].
  all: apply writeback_access_done in Hc; unfold ppoll_core in Hc;
    destruct (ppoll_scan i m ufds nfds) as [| e0 | cs]; cbv beta iota in Hc;
    try discriminate Hc.
  all: injection Hc as Hund _; exists cs; split; [reflexivity|];
    rewrite Hu, Hund; reflexivity.
Qed.

(** A descriptor in the undecided set is one the call's entries name. *)
Lemma ppoll_undecided_named : forall cs b, (0 <= b)%Z ->
  Z.testbit (ppoll_undecided cs) b = true -> exists lo hi, In (b, lo, hi) cs.
Proof.
  induction cs as [|[[fd lo] hi] cs IH]; intros b Hb H.
  - cbn [ppoll_undecided] in H. rewrite Z.testbit_0_l in H. discriminate H.
  - cbn [ppoll_undecided] in H. rewrite Z.lor_spec in H.
    apply orb_true_iff in H. destruct H as [H|H].
    + destruct (Z.eqb lo hi); cbv iota in H;
        [rewrite Z.testbit_0_l in H; discriminate H|].
      rewrite Z.shiftl_1_l in H.
      destruct (Z.ltb_spec fd 0) as [Hneg|Hpos].
      * rewrite (Z.pow_neg_r 2 fd Hneg) in H. rewrite Z.testbit_0_l in H. discriminate H.
      * rewrite (Z.pow2_bits_eqb fd b Hpos) in H. apply Z.eqb_eq in H. subst b.
        exists lo, hi. left. reflexivity.
    + destruct (IH b Hb H) as (lo' & hi' & Hin). exists lo', hi'. right. exact Hin.
Qed.

(* =========================================================================
   What a read on an end does
   ========================================================================= *)

(** A read, by any of the three routes, on the descriptor [fd]. *)
Definition reads_on (fd : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : Prop :=
  (exists buf count, read_spec fd buf count i m o)
  \/ (exists iov iovcnt, readv_spec fd iov iovcnt i m o)
  \/ (exists buf size, recvfrom_spec fd buf size i m o).

(** The three things a read on the end [(id, side)] at [fd], whose state
    is [st], can do: nothing to the model, and no -ECONNRESET; take
    queued bytes, and no -ECONNRESET; or, on a survivor with an empty
    queue that has not shown its error to be gone, write [RsNone] into
    its own entry. *)
Definition read_moves (m m' : Model) (eff : SyscallEffect) (fd id : word)
    (side : bool) (st : StreamEnd) : Prop :=
  (m' = m /\ eff_ret eff <> errno_ret ECONNRESET)
  \/ (se_rx st <> [] /\
      (exists q, m' = with_fds (fd_insert (m_fds m) fd (FdStream id side (se_set_rx st q))) m)
      /\ eff_ret eff <> errno_ret ECONNRESET)
  \/ (stream_peer (m_fds m) id side = None /\ se_rx st = [] /\ se_reset st <> RsNone
      /\ m' = with_fds (stream_reset_seen fd id side st m) m).

Ltac sr_ne :=
  let H := fresh in
  intro H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.

Lemma sr_count_ne : forall n, (0 <= n <= MAX_RW_COUNT)%Z ->
  Z_to_bv 64 n <> errno_ret ECONNRESET.
Proof.
  intros n Hn H. apply (f_equal bv_unsigned) in H.
  rewrite stream_send_ret_unsigned in H by exact Hn.
  rewrite errno_ret_unsigned in H by (unfold ECONNRESET; lia).
  unfold two_pow_64, MAX_RW_COUNT, ECONNRESET in *. lia.
Qed.

Lemma sr_take_ne : forall q n, (n <= MAX_RW_COUNT)%Z ->
  len_word (pipe_take q n) <> errno_ret ECONNRESET.
Proof.
  intros q n Hn. unfold len_word. apply sr_count_ne.
  pose proof (pipe_take_length q n). unfold MAX_RW_COUNT in *. lia.
Qed.

Lemma read_empty_moves : forall fd id side st nb i m eff m' evs,
  se_rx st = [] ->
  stream_read_empty fd id side st nb m i m (Ok eff m' evs) ->
  read_moves m m' eff fd id side st.
Proof.
  intros fd id side st nb i m eff m' evs Hq H. unfold read_moves.
  unfold stream_read_empty in H.
  destruct (stream_peer (m_fds m) id side) as [p|] eqn:Hp; cbv beta iota in H.
  - left. destruct (se_shut_rd st); cbv beta iota in H.
    + apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
      split; [reflexivity|]. cbn [eff_ret]. sr_ne.
    + destruct nb; cbv beta iota in H.
      * unfold err_ret in H. apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
        split; [reflexivity|]. cbn [eff_ret]. sr_ne.
      * exfalso. exact (unmodeled_no_ok _ _ _ _ _ H).
  - unfold stream_read_reset, err_ret in H.
    destruct (se_reset st) eqn:Hr; cbv beta iota in H.
    + right; right. unfold alt in H.
      destruct H as [H|H]; apply stream_reset_ret_ok_inv in H; destruct H as (_ & -> & _);
        (split; [first [exact Hp | reflexivity]|split; [first [exact Hq | reflexivity]|split; [congruence|reflexivity]]]).
    + right; right. apply stream_reset_ret_ok_inv in H. destruct H as (_ & -> & _).
      split; [first [exact Hp | reflexivity]|split; [first [exact Hq | reflexivity]|split; [congruence|reflexivity]]].
    + left. apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
      split; [reflexivity|]. cbn [eff_ret]. sr_ne.
Qed.

Lemma read_stream_moves : forall fd id side st nb buf count i m eff m' evs,
  stream_read fd id side st nb buf count i m i m (Ok eff m' evs) ->
  read_moves m m' eff fd id side st.
Proof.
  intros fd id side st nb buf count i m eff m' evs H.
  unfold stream_read in H.
  destruct (se_rx st) as [|b q0] eqn:Hq; cbv beta iota zeta in H.
  { exact (read_empty_moves _ _ _ _ _ _ _ _ _ _ Hq H). }
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (pipe_take (b :: q0) (rw_count_clamp count)))) as [w|];
    cbv beta iota in H.
  - unfold read_moves. right; left. split; [rewrite Hq; discriminate|].
    destruct H as (u & m1 & evs1 & evs2 & Hset & Hret & ->).
    unfold set_fds, modify in Hset. inversion Hset; subst; clear Hset.
    cbv beta in Hret. unfold pure in Hret. inversion Hret; subst; clear Hret.
    split; [eexists; reflexivity|]. cbn [eff_ret].
    apply sr_take_ne. exact (proj2 (rw_count_clamp_range count)).
  - unfold read_moves. left.
    destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)); cbv beta iota in H.
    + exfalso. exact (unmodeled_no_ok _ _ _ _ _ H).
    + unfold err_ret in H. apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
      split; [reflexivity|]. cbn [eff_ret]. sr_ne.
Qed.

Lemma readv_stream_moves : forall fd id side st iovs0 i m eff m' evs,
  readv_imported fd (RdStream id side st) iovs0 i m i m (Ok eff m' evs) ->
  read_moves m m' eff fd id side st.
Proof.
  intros fd id side st iovs0 i m eff m' evs H.
  unfold readv_imported in H. cbv zeta in H.
  destruct (Z.eqb (iovs_total (cap_iovecs iovs0)) 0); cbv beta iota in H.
  { unfold read_moves. left. apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
    split; [reflexivity|]. cbn [eff_ret]. sr_ne. }
  destruct (se_rx st) as [|b q0] eqn:Hq; cbv beta iota zeta in H.
  { exact (read_empty_moves _ _ _ _ _ _ _ _ _ _ Hq H). }
  destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0) [Z_to_bv 8 0]);
    cbv beta iota in H.
  2:{ unfold read_moves. left. unfold err_ret in H. apply ret_only_ok_inv in H.
      destruct H as (-> & -> & _).
      split; [reflexivity|]. cbn [eff_ret]. sr_ne. }
  destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0)
              (pipe_take (b :: q0) (iovs_total (cap_iovecs iovs0)))) as [writes|];
    cbv beta iota in H.
  2:{ exfalso. unfold readv_buf_gap in H. exact (unmodeled_no_ok _ _ _ _ _ H). }
  unfold read_moves. right; left. split; [rewrite Hq; discriminate|].
  destruct H as (u & m1 & evs1 & evs2 & Hset & Hret & ->).
  unfold set_fds, modify in Hset. inversion Hset; subst; clear Hset.
  cbv beta in Hret. unfold pure in Hret. inversion Hret; subst; clear Hret.
  split; [eexists; reflexivity|]. cbn [eff_ret].
  apply sr_take_ne. rewrite iovs_total_cap. lia.
Qed.

(** THE THREE ROUTES ON A SURVIVOR'S DESCRIPTOR, read off the spec
    arms. *)
Lemma reads_on_moves : forall fd id side st i m eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdStream id side st) ->
  reads_on fd i m (Ok eff m' evs) ->
  read_moves m m' eff fd id side st.
Proof.
  intros fd id side st i m eff m' evs Hfd Hr. unfold reads_on in Hr. unfold read_moves.
  destruct Hr as [(buf & count & H) | [(iov & iovcnt & H) | (buf & size & H)]].
  - unfold read_spec in H. apply input_bind_ok_inv in H. cbv beta in H.
    apply get_model_bind_ok_inv in H. cbv beta in H.
    rewrite Hfd in H. cbv beta iota in H.
    destruct (negb (access_okb buf (bv_unsigned count))); cbv beta iota in H.
    { left. unfold err_ret in H. apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
      split; [reflexivity|]. cbn [eff_ret]. sr_ne. }
    destruct (w_is0 count); cbv beta iota in H.
    { left. apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
      split; [reflexivity|]. cbn [eff_ret]. sr_ne. }
    exact (read_stream_moves _ _ _ _ _ _ _ _ _ _ _ _ H).
  - unfold readv_spec in H. apply input_bind_ok_inv in H. cbv beta in H.
    apply get_model_bind_ok_inv in H. cbv beta in H.
    rewrite Hfd in H. cbv beta iota in H. unfold readable_fd in H. cbv beta iota in H.
    destruct (readv_heap_iovecb iovcnt); cbv beta iota in H.
    { exfalso. unfold readv_heap_gap, readv_buf_gap in H.
      exact (unmodeled_no_ok _ _ _ _ _ H). }
    apply record_copyins_ok_inv in H. destruct H as (core & H & ->).
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs0| |];
      cbv beta iota in H.
    + exact (readv_stream_moves _ _ _ _ _ _ _ _ _ _ H).
    + left. unfold err_ret in H. apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
      split; [reflexivity|]. cbn [eff_ret with_copyins]. sr_ne.
    + left. unfold err_ret in H. apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
      split; [reflexivity|]. cbn [eff_ret with_copyins]. sr_ne.
  - unfold recvfrom_spec in H.
    destruct (negb (modeled_rw_count size)); cbv beta iota in H.
    { exfalso. exact (unmodeled_no_ok _ _ _ _ _ H). }
    apply input_bind_ok_inv in H. cbv beta in H.
    apply get_model_bind_ok_inv in H. cbv beta in H.
    unfold access_ok_zero in H.
    destruct (access_okb buf (bv_unsigned size)); cbv beta iota in H.
    2:{ left. unfold err_ret in H. apply ret_only_ok_inv in H. destruct H as (-> & -> & _).
        split; [reflexivity|]. cbn [eff_ret]. sr_ne. }
    rewrite Hfd in H. cbv beta iota in H.
    destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 (in_arg i 3))) MSG_DONTWAIT) 0));
      cbv beta iota in H.
    { exfalso. exact (unmodeled_no_ok _ _ _ _ _ H). }
    destruct (negb (w_is0 (in_arg i 4))); cbv beta iota in H.
    { exfalso. exact (unmodeled_no_ok _ _ _ _ _ H). }
    exact (read_stream_moves _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

(* =========================================================================
   LEMMA 1 — only forward
   ========================================================================= *)

Lemma read_moves_forward : forall m m' eff fd id side st,
  fd_lookup (m_fds m) fd = Some (FdStream id side st) ->
  read_moves m m' eff fd id side st ->
  resets_forward (m_fds m) (m_fds m').
Proof.
  intros m m' eff fd id side st Hfd Hmv. unfold resets_forward. intros fd' id' s' st' H.
  unfold read_moves in Hmv.
  destruct Hmv as [[-> _] | [(_ & (q & ->) & _) | (_ & _ & _ & ->)]].
  - exists st'. split; [exact H | apply reset_forward_refl].
  - rewrite m_fds_with_fds in H.
    destruct (bv_eqb fd' fd) eqn:E.
    + apply bv_eqb_eq in E. subst fd'. rewrite sr_lookup_insert_eq in H.
      injection H as <- <- <-. exists st. split; [exact Hfd|].
      exact (reset_forward_refl (se_reset st)).
    + rewrite (sr_lookup_insert_neq _ _ _ _ (sr_neq_of_eqb _ _ E)) in H.
      exists st'. split; [exact H | apply reset_forward_refl].
  - unfold stream_reset_seen in H. rewrite m_fds_with_fds in H.
    destruct (bv_eqb fd' fd) eqn:E.
    + apply bv_eqb_eq in E. subst fd'. rewrite sr_lookup_insert_eq in H.
      injection H as <- <- <-. exists st. split; [exact Hfd|].
      exact (reset_forward_none (se_reset st)).
    + rewrite (sr_lookup_insert_neq _ _ _ _ (sr_neq_of_eqb _ _ E)) in H.
      exists st'. split; [exact H | apply reset_forward_refl].
Qed.

(** LEMMA 1, THE READ: no read on a stream end, by read, readv or
    recvfrom, moves any end's [se_reset] back. *)
Theorem reads_on_forward : forall fd id side st i m eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdStream id side st) ->
  reads_on fd i m (Ok eff m' evs) ->
  resets_forward (m_fds m) (m_fds m').
Proof.
  intros fd id side st i m eff m' evs Hfd H.
  exact (read_moves_forward _ _ _ _ _ _ _ Hfd (reads_on_moves _ _ _ _ _ _ _ _ _ Hfd H)).
Qed.

(** LEMMA 1, THE PPOLL: no ppoll moves any end's [se_reset] back. *)
Theorem ppoll_forward : forall ufds nfds tsp sig sigsetsize i m eff m' evs,
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs) ->
  resets_forward (m_fds m) (m_fds m').
Proof.
  intros ufds nfds tsp sig sigsetsize i m eff m' evs H.
  destruct (ppoll_spec_records _ _ _ _ _ _ _ _ _ _ H) as (pa & sel & _ & ->).
  rewrite m_fds_with_fds. apply record_forward.
Qed.

(** ...and pselect6 moves nothing at all: one answer, no record. *)
Theorem pselect6_keeps_the_model : forall n32 inp outp exp tsp sig i m eff m' evs,
  pselect6_spec n32 inp outp exp tsp sig i m (Ok eff m' evs) -> m' = m.
Proof.
  intros n32 inp outp exp tsp sig i m eff m' evs H.
  apply check_pselect6_complete_ok in H. unfold check_pselect6 in H.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [pa|]; [|discriminate H].
  apply check_pselect_answer_model in H. exact H.
Qed.

(* =========================================================================
   LEMMA 2 — the first observation fixes the state for both routes
   ========================================================================= *)

(** The answer of the empty read from a decided state, and the model
    after it. *)
Definition reset_ret (r : ResetState) : word :=
  match r with RsPending => errno_ret ECONNRESET | _ => Z_to_bv 64 0 end.

Definition reset_after (fd id : word) (side : bool) (st : StreamEnd) (m : Model) : Model :=
  match se_reset st with
  | RsPending => with_fds (stream_reset_seen fd id side st m) m
  | _ => m
  end.

(** LEMMA 2, THE READ: once the state is decided, the survivor's empty
    read has exactly one outcome, a function of the state: -ECONNRESET
    and [RsNone] after [RsPending], end of file and nothing moved after
    [RsNone]. *)
Theorem decided_read_has_one_answer : forall fd id side st nb i m o,
  stream_peer (m_fds m) id side = None -> se_reset st <> RsUnknown ->
  stream_read_empty fd id side st nb m i m o
  <-> o = Ok (mkEffect (reset_ret (se_reset st)) [] []) (reset_after fd id side st m) [].
Proof.
  intros fd id side st nb i m o Hp Hu.
  unfold stream_read_empty, reset_after. rewrite Hp. cbv beta iota.
  unfold stream_read_reset, err_ret.
  destruct (se_reset st) eqn:Hr; [exfalso; congruence|..]; cbv beta iota; split.
  - destruct o as [eff m' evs|]; intro H.
    + apply stream_reset_ret_ok_inv in H. destruct H as (-> & -> & ->). reflexivity.
    + exfalso. exact (stream_reset_ret_no_unmodeled _ _ _ _ H).
  - intros ->. apply stream_reset_ret_ok.
  - destruct o as [eff m' evs|]; intro H.
    + apply ret_only_ok_inv in H. destruct H as (-> & -> & ->). reflexivity.
    + exfalso. exact (ret_only_no_unmodeled _ _ _ H).
  - intros ->. apply pure_ok.
Qed.

(** LEMMA 2, THE PPOLL: once the state is decided, the survivor's entry
    in a ppoll has one answer -- its two masks are equal, so it is in no
    choice and nothing is recorded -- with POLLERR (bit 3) set exactly
    after [RsPending]. *)
Theorem decided_ppoll_has_one_answer : forall fds fd ev id side st,
  (0 <= fd)%Z ->
  fd_lookup fds (Z_to_bv 64 fd) = Some (FdStream id side st) ->
  stream_peer fds id side = None -> se_reset st <> RsUnknown ->
  exists r, ppoll_revents_of fds fd ev = Some (r, r)
            /\ Z.testbit r 3 = match se_reset st with RsPending => true | _ => false end.
Proof.
  intros fds fd ev id side st Hfd0 Hfd Hp Hu.
  unfold ppoll_revents_of.
  replace (fd <? 0)%Z with false
    by (rewrite (proj2 (Z.ltb_ge fd 0) Hfd0); reflexivity).
  rewrite Hfd. cbv beta iota zeta.
  unfold stream_poll_mask. rewrite Hp. cbv beta iota zeta.
  assert (Hf : Z.testbit (Z.lor ev (Z.lor EPOLLERR EPOLLHUP)) 3 = true).
  { rewrite Z.lor_spec. apply orb_true_iff. right. reflexivity. }
  destruct (se_reset st) eqn:Hr; [exfalso; congruence|..]; cbv beta iota;
    (eexists; split; [reflexivity|]);
    rewrite Z.land_spec, Hf, andb_true_r;
    destruct (se_rx st); destruct (4 <=? se_sndbuf st)%Z; reflexivity.
Qed.

(** In particular, a ppoll that chose "clear" for a survivor that had
    shown nothing is followed by reads that answer end of file and move
    nothing. *)
Theorem ppoll_clear_then_read_eof : forall m und sel k id side st nb i o,
  fd_lookup (m_fds m) k = Some (FdStream id side st) ->
  stream_peer (m_fds m) id side = None -> se_reset st = RsUnknown ->
  Z.testbit und (bv_unsigned k) = true -> Z.testbit sel (bv_unsigned k) = false ->
  let m1 := with_fds (ppoll_record (m_fds m) und sel) m in
  fd_lookup (m_fds m1) k = Some (FdStream id side (se_set_reset st RsNone))
  /\ (stream_read_empty k id side (se_set_reset st RsNone) nb m1 i m1 o
      <-> o = Ok (mkEffect (Z_to_bv 64 0) [] []) m1 []).
Proof.
  intros m und sel k id side st nb i o Hk Hp Hr Hu Hs m1.
  assert (Hk1 : fd_lookup (m_fds m1) k = Some (FdStream id side (se_set_reset st RsNone))).
  { unfold m1. rewrite m_fds_with_fds, (ppoll_record_at _ _ _ _ _ _ _ Hk Hp Hr Hu), Hs.
    reflexivity. }
  split; [exact Hk1|].
  assert (Hp1 : stream_peer (m_fds m1) id side = None).
  { unfold m1. rewrite m_fds_with_fds. apply peer_ppoll_record_none. exact Hp. }
  assert (Hd : se_reset (se_set_reset st RsNone) <> RsUnknown) by (cbn; discriminate).
  exact (decided_read_has_one_answer k id side (se_set_reset st RsNone) nb i m1 o Hp1 Hd).
Qed.

(** ...and one that chose "set" is followed by one -ECONNRESET, which
    leaves [RsNone]. *)
Theorem ppoll_set_then_read_reset : forall m und sel k id side st nb i o,
  fd_lookup (m_fds m) k = Some (FdStream id side st) ->
  stream_peer (m_fds m) id side = None -> se_reset st = RsUnknown ->
  Z.testbit und (bv_unsigned k) = true -> Z.testbit sel (bv_unsigned k) = true ->
  let m1 := with_fds (ppoll_record (m_fds m) und sel) m in
  fd_lookup (m_fds m1) k = Some (FdStream id side (se_set_reset st RsPending))
  /\ (stream_read_empty k id side (se_set_reset st RsPending) nb m1 i m1 o
      <-> o = Ok (mkEffect (errno_ret ECONNRESET) [] [])
                 (with_fds (stream_reset_seen k id side (se_set_reset st RsPending) m1) m1) []).
Proof.
  intros m und sel k id side st nb i o Hk Hp Hr Hu Hs m1.
  assert (Hk1 : fd_lookup (m_fds m1) k = Some (FdStream id side (se_set_reset st RsPending))).
  { unfold m1. rewrite m_fds_with_fds, (ppoll_record_at _ _ _ _ _ _ _ Hk Hp Hr Hu), Hs.
    reflexivity. }
  split; [exact Hk1|].
  assert (Hp1 : stream_peer (m_fds m1) id side = None).
  { unfold m1. rewrite m_fds_with_fds. apply peer_ppoll_record_none. exact Hp. }
  assert (Hd : se_reset (se_set_reset st RsPending) <> RsUnknown) by (cbn; discriminate).
  exact (decided_read_has_one_answer k id side (se_set_reset st RsPending) nb i m1 o Hp1 Hd).
Qed.

(** ...and a read's -ECONNRESET, by either route of choice, leaves the
    end at [RsNone], where the read answers end of file and the ppoll
    entry shows POLLERR clear. *)
Theorem after_reset_both_routes_clear : forall fd id side st nb i m eff m' evs ev,
  se_rx st = [] ->
  stream_read_empty fd id side st nb m i m (Ok eff m' evs) ->
  eff_ret eff = errno_ret ECONNRESET ->
  fd_lookup (m_fds m') fd = Some (FdStream id side (se_set_reset st RsNone))
  /\ (forall nb2 i2 o, stream_read_empty fd id side (se_set_reset st RsNone) nb2 m' i2 m' o
                       <-> o = Ok (mkEffect (Z_to_bv 64 0) [] []) m' [])
  /\ exists r, ppoll_revents_of (m_fds m') (bv_unsigned fd) ev = Some (r, r)
               /\ Z.testbit r 3 = false.
Proof.
  intros fd id side st nb i m eff m' evs ev Hq H Hret.
  pose proof (read_empty_moves _ _ _ _ _ _ _ _ _ _ Hq H) as Hmv.
  unfold read_moves in Hmv.
  destruct Hmv as [[_ Hne] | [(Hne & _) | (Hp & _ & _ & ->)]];
    [contradiction | contradiction |].
  set (m1 := with_fds (stream_reset_seen fd id side st m) m).
  assert (Hk1 : fd_lookup (m_fds m1) fd = Some (FdStream id side (se_set_reset st RsNone))).
  { unfold m1, stream_reset_seen. rewrite m_fds_with_fds. apply sr_lookup_insert_eq. }
  assert (Hp1 : stream_peer (m_fds m1) id side = None).
  { unfold m1, stream_reset_seen. rewrite m_fds_with_fds. apply sr_peer_insert_none.
    exact Hp. }
  assert (Hd : se_reset (se_set_reset st RsNone) <> RsUnknown) by (cbn; discriminate).
  split; [exact Hk1|]. split.
  - intros nb2 i2 o.
    exact (decided_read_has_one_answer fd id side (se_set_reset st RsNone) nb2 i2 m1 o Hp1 Hd).
  - assert (Hfd' : fd_lookup (m_fds m1) (Z_to_bv 64 (bv_unsigned fd))
                   = Some (FdStream id side (se_set_reset st RsNone))).
    { rewrite Z_to_bv_bv_unsigned. exact Hk1. }
    destruct (decided_ppoll_has_one_answer (m_fds m1) (bv_unsigned fd) ev id side
                (se_set_reset st RsNone) (proj1 (bv_unsigned_in_range _ fd)) Hfd' Hp1 Hd)
      as (r & Hr & Hb).
    exists r. split; [exact Hr | exact Hb].
Qed.

(* =========================================================================
   LEMMA 3 — at most one reset per end
   ========================================================================= *)

(** A read that answers -ECONNRESET, by any route, was the survivor's
    empty read, and it left [RsNone] in the end's own entry. *)
Theorem reads_on_reset_leaves_none : forall fd id side st i m eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdStream id side st) ->
  reads_on fd i m (Ok eff m' evs) ->
  eff_ret eff = errno_ret ECONNRESET ->
  stream_peer (m_fds m) id side = None /\ se_rx st = []
  /\ m' = with_fds (fd_insert (m_fds m) fd (FdStream id side (se_set_reset st RsNone))) m.
Proof.
  intros fd id side st i m eff m' evs Hfd H Hret.
  pose proof (reads_on_moves _ _ _ _ _ _ _ _ _ Hfd H) as Hmv. unfold read_moves in Hmv.
  destruct Hmv as [[_ Hne] | [(_ & _ & Hne) | (Hp & Hq & _ & ->)]];
    [contradiction | contradiction |].
  split; [exact Hp|split; [exact Hq|reflexivity]].
Qed.

(** With the peer gone, the queue empty and [RsNone], no read answers
    -ECONNRESET, and none moves the model. *)
Theorem reads_on_after_none : forall fd id side st i m eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdStream id side st) ->
  stream_peer (m_fds m) id side = None -> se_rx st = [] -> se_reset st = RsNone ->
  reads_on fd i m (Ok eff m' evs) ->
  eff_ret eff <> errno_ret ECONNRESET /\ m' = m.
Proof.
  intros fd id side st i m eff m' evs Hfd Hp Hq Hr H.
  pose proof (reads_on_moves _ _ _ _ _ _ _ _ _ Hfd H) as Hmv. unfold read_moves in Hmv.
  destruct Hmv as [[-> Hne] | [(Hne & _ & _) | (_ & _ & Hn & _)]].
  - split; [exact Hne | reflexivity].
  - contradiction.
  - contradiction.
Qed.

(** So no two reads on one end both answer -ECONNRESET: after the first,
    every read answers something else and moves nothing. *)
Theorem reads_on_at_most_one_reset : forall fd id side st i m eff m1 evs i2 eff2 m2 evs2,
  fd_lookup (m_fds m) fd = Some (FdStream id side st) ->
  reads_on fd i m (Ok eff m1 evs) ->
  eff_ret eff = errno_ret ECONNRESET ->
  reads_on fd i2 m1 (Ok eff2 m2 evs2) ->
  eff_ret eff2 <> errno_ret ECONNRESET /\ m2 = m1.
Proof.
  intros fd id side st i m eff m1 evs i2 eff2 m2 evs2 Hfd H Hret H2.
  destruct (reads_on_reset_leaves_none _ _ _ _ _ _ _ _ _ Hfd H Hret) as (Hp & Hq & ->).
  eapply (reads_on_after_none fd id side (se_set_reset st RsNone) i2);
    [| | exact Hq | reflexivity | exact H2].
  - rewrite m_fds_with_fds. apply sr_lookup_insert_eq.
  - rewrite m_fds_with_fds. apply sr_peer_insert_none. exact Hp.
Qed.

(** ...and no ppoll between them changes that: a ppoll leaves an end that
    has shown its error exactly as it was, and its peer gone. *)
Theorem ppoll_keeps_a_decided_end : forall ufds nfds tsp sig sigsetsize i m eff m' evs
    fd id side st,
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs) ->
  fd_lookup (m_fds m) fd = Some (FdStream id side st) -> se_reset st <> RsUnknown ->
  fd_lookup (m_fds m') fd = Some (FdStream id side st)
  /\ (stream_peer (m_fds m) id side = None -> stream_peer (m_fds m') id side = None).
Proof.
  intros ufds nfds tsp sig sigsetsize i m eff m' evs fd id side st H Hfd Hr.
  destruct (ppoll_spec_records _ _ _ _ _ _ _ _ _ _ H) as (pa & sel & _ & ->).
  rewrite m_fds_with_fds. split.
  - apply ppoll_record_keeps_decided; assumption.
  - apply peer_ppoll_record_none.
Qed.

(* =========================================================================
   LEMMA 4 — a single reporter
   ========================================================================= *)

(** A read changes the [se_reset] of no end but the one its descriptor
    holds, and that one only while its peer is gone. *)
Theorem reads_on_single_reporter : forall fd id side st i m eff m' evs fd' id' s' st0 st1,
  fd_lookup (m_fds m) fd = Some (FdStream id side st) ->
  reads_on fd i m (Ok eff m' evs) ->
  fd_lookup (m_fds m) fd' = Some (FdStream id' s' st0) ->
  fd_lookup (m_fds m') fd' = Some (FdStream id' s' st1) ->
  se_reset st1 <> se_reset st0 ->
  fd' = fd /\ stream_peer (m_fds m) id' s' = None.
Proof.
  intros fd id side st i m eff m' evs fd' id' s' st0 st1 Hfd H H0 H1 Hne.
  pose proof (reads_on_moves _ _ _ _ _ _ _ _ _ Hfd H) as Hmv. unfold read_moves in Hmv.
  destruct Hmv as [[-> _] | [(_ & (q & ->) & _) | (Hp & _ & _ & ->)]].
  - rewrite H0 in H1. injection H1 as E. subst st1. exfalso. apply Hne. reflexivity.
  - rewrite m_fds_with_fds in H1.
    destruct (bv_eqb fd' fd) eqn:E.
    + apply bv_eqb_eq in E. subst fd'.
      rewrite sr_lookup_insert_eq in H1. rewrite Hfd in H0.
      injection H0 as E1 E2 E3. injection H1 as E4 E5 E6. subst.
      exfalso. apply Hne. reflexivity.
    + rewrite (sr_lookup_insert_neq _ _ _ _ (sr_neq_of_eqb _ _ E)) in H1.
      rewrite H0 in H1. injection H1 as E'. subst st1. exfalso. apply Hne. reflexivity.
  - unfold stream_reset_seen in H1. rewrite m_fds_with_fds in H1.
    destruct (bv_eqb fd' fd) eqn:E.
    + apply bv_eqb_eq in E. subst fd'. split; [reflexivity|].
      rewrite Hfd in H0. injection H0 as E1 E2 E3. subst. exact Hp.
    + rewrite (sr_lookup_insert_neq _ _ _ _ (sr_neq_of_eqb _ _ E)) in H1.
      rewrite H0 in H1. injection H1 as E'. subst st1. exfalso. apply Hne. reflexivity.
Qed.

(** A ppoll changes the [se_reset] of an end only at a descriptor one of
    its entries names, and only while that end's peer is gone. *)
Theorem ppoll_single_reporter : forall ufds nfds tsp sig sigsetsize i m eff m' evs
    fd id s st0 st1,
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs) ->
  fd_lookup (m_fds m) fd = Some (FdStream id s st0) ->
  fd_lookup (m_fds m') fd = Some (FdStream id s st1) ->
  se_reset st1 <> se_reset st0 ->
  stream_peer (m_fds m) id s = None
  /\ exists cs lo hi, ppoll_scan i m ufds nfds = PpScanDone cs /\ In (bv_unsigned fd, lo, hi) cs.
Proof.
  intros ufds nfds tsp sig sigsetsize i m eff m' evs fd id s st0 st1 H H0 H1 Hne.
  destruct (ppoll_spec_records _ _ _ _ _ _ _ _ _ _ H) as (pa & sel & Ho & ->).
  rewrite m_fds_with_fds, lookup_ppoll_record, H0 in H1. cbn [option_map] in H1.
  assert (H1' : ppoll_record_entry (m_fds m) (pa_und pa) sel fd (FdStream id s st0)
                = FdStream id s st1) by (injection H1 as H1; exact H1).
  clear H1. apply ppoll_record_entry_stream in H1'.
  destruct H1' as (st & E & [-> | (Hu & Hp & _ & _)]).
  - injection E as E. subst st. exfalso. apply Hne. reflexivity.
  - split; [exact Hp|].
    destruct (ppoll_outcome_und _ _ _ _ _ _ _ _ Ho) as [H0u | (cs & Hs & Hcs)].
    + rewrite H0u, Z.testbit_0_l in Hu. discriminate Hu.
    + rewrite Hcs in Hu.
      destruct (ppoll_undecided_named cs (bv_unsigned fd)
                  (proj1 (bv_unsigned_in_range _ fd)) Hu) as (lo & hi & Hin).
      exists cs, lo, hi. split; [exact Hs | exact Hin].
Qed.
