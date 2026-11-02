(** * LinuxProcessSem.Checks.Sys.Fs.ReadWrite — the read (63), write (64), pread64 (67), pwrite64 (68), writev (66), readv (65), lseek (62) checkers, and their proofs

    Mirrors [Sys/Fs/ReadWrite.v], which answers to Linux
    [fs/read_write.c]: this file holds the checkers for the syscalls
    defined there, and no others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad RiscvSemantics Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Uaccess.

(** [ReadWrite.socket_pending_error] as an acceptor: the read that
    reports the peer's RST or timeout also consumes it, so the accepted
    model is the one whose connection has moved to [SkReset].  No byte
    moves, so the range verdict is all that is left in front of it. *)

Definition check_socket_pending_error (e : Z) (fd : word) (peer : PeerAddr)
    (ch : word) (buf count : word) (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_access_ok_zero buf count eff m
    (check_ret_only eff (errno_ret e)
       (with_fds (fd_insert (m_fds m) fd (FdSocket (SkReset peer ch))) m) []).

(** [ReadWrite.read_urandom] as an acceptor, branch for branch: the
    zero count, the first-byte verdict, the stream's length test, the
    whole-delivery verdict, and then ONE delivery — exactly the clamped
    count off the front of [m_urandom] at [buf], the stream advanced
    past them, no event.  Nothing is chosen, so the accepted effect is
    computed rather than matched against a predicate. *)
Definition check_read_urandom (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if w_is0 count then check_ret_only eff (Z_to_bv 64 0) m []
  else
  match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
  | None => check_ret_only eff (errno_ret EFAULT) m []
  | Some _ =>
      let r := stream_take_z (m_urandom m) (rw_count_clamp count) in
      if negb (Z.eqb (Z.of_nat (length (fst r))) (rw_count_clamp count))
      then CheckUnmodeled
      else
      match read_bytes_map (in_wmem i) buf (len_word (fst r)) with
      | None => CheckUnmodeled
      | Some _ =>
          match eff with
          | mkEffectU ret [(a, bs)] [] [] [] [] =>
              if bv_eqb a buf && bv_eqb ret (len_word (fst r)) && listN_eqb bs (fst r)
              then CheckOk (with_urandom (snd r) m) []
              else CheckReject
          | _ => CheckReject
          end
      end
  end.

Lemma check_read_urandom_sound_ok : forall i buf count eff m m' evs,
  check_read_urandom i buf count eff m = CheckOk m' evs ->
  read_urandom buf count i m i m (Ok eff m' evs).
Proof.
  intros i buf count eff m m' evs H.
  unfold check_read_urandom in H. unfold read_urandom. cbv zeta in *.
  destruct (w_is0 count).
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|].
  2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (negb (Z.eqb (Z.of_nat (length (fst (stream_take_z (m_urandom m)
                                                  (rw_count_clamp count)))))
                        (rw_count_clamp count))); [discriminate|].
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (stream_take_z (m_urandom m) (rw_count_clamp count)))))
    as [wn|]; [|discriminate].
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs] [|]];
    destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
  destruct (bv_eqb a buf
            && bv_eqb ret (len_word (fst (stream_take_z (m_urandom m) (rw_count_clamp count))))
            && listN_eqb bs (fst (stream_take_z (m_urandom m) (rw_count_clamp count))))
    eqn:Hb; [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in Hb as [Hb HC].
  apply andb_true_iff in Hb as [HA HB].
  apply bv_eqb_eq in HA; subst a. apply bv_eqb_eq in HB; subst ret.
  apply listN_eqb_eq in HC; subst bs.
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_read_urandom_sound_unmodeled : forall i buf count eff m,
  check_read_urandom i buf count eff m = CheckUnmodeled ->
  read_urandom buf count i m i m Unmodeled.
Proof.
  intros i buf count eff m H.
  unfold check_read_urandom in H. unfold read_urandom. cbv zeta in *.
  destruct (w_is0 count); [now apply check_ret_only_no_unmodeled in H|].
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|];
    [|now apply check_ret_only_no_unmodeled in H].
  destruct (negb (Z.eqb (Z.of_nat (length (fst (stream_take_z (m_urandom m)
                                                  (rw_count_clamp count)))))
                        (rw_count_clamp count))); [apply unmodeled_intro|].
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (stream_take_z (m_urandom m) (rw_count_clamp count)))))
    as [wn|]; [|apply unmodeled_intro].
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs] [|]];
    destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
  destruct (bv_eqb a buf
            && bv_eqb ret (len_word (fst (stream_take_z (m_urandom m) (rw_count_clamp count))))
            && listN_eqb bs (fst (stream_take_z (m_urandom m) (rw_count_clamp count))));
    discriminate.
Qed.

Lemma check_read_urandom_complete_ok : forall i buf count eff m m' evs,
  read_urandom buf count i m i m (Ok eff m' evs) ->
  check_read_urandom i buf count eff m = CheckOk m' evs.
Proof.
  intros i buf count eff m m' evs H.
  unfold read_urandom in H. unfold check_read_urandom. sys_unfold. cbv zeta in *.
  destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok.
  { cbn; rewrite bv_eqb_refl; reflexivity. }
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
    hall Hw1; inv_ok.
  2:{ cbn; rewrite bv_eqb_refl; reflexivity. }
  destruct (negb (Z.eqb (Z.of_nat (length (fst (stream_take_z (m_urandom m)
                                                  (rw_count_clamp count)))))
                        (rw_count_clamp count))) eqn:Hlen; hall Hlen; inv_ok.
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (stream_take_z (m_urandom m) (rw_count_clamp count)))))
    as [wn|] eqn:Hwn; hall Hwn; inv_ok.
  cbn. rewrite !bv_eqb_refl. rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
  reflexivity.
Qed.

Lemma check_read_urandom_complete_unmodeled : forall i buf count m eff,
  read_urandom buf count i m i m Unmodeled ->
  check_read_urandom i buf count eff m = CheckUnmodeled.
Proof.
  intros i buf count m eff H.
  unfold read_urandom in H. unfold check_read_urandom. sys_unfold. cbv zeta in *.
  destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok.
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
    hall Hw1; inv_ok.
  destruct (negb (Z.eqb (Z.of_nat (length (fst (stream_take_z (m_urandom m)
                                                  (rw_count_clamp count)))))
                        (rw_count_clamp count))) eqn:Hlen; hall Hlen; inv_ok;
    [reflexivity|].
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (stream_take_z (m_urandom m) (rw_count_clamp count)))))
    as [wn|] eqn:Hwn; hall Hwn; inv_ok.
  reflexivity.
Qed.

(** What a delivery through the device measures: exactly the clamped
    count, which is under the clamp by construction.
    [Checks.Cases.Fs.ReadWrite.read_delivery_clamped] reads it. *)
Lemma check_read_urandom_delivery_clamped : forall i buf count eff m m' evs a bs,
  check_read_urandom i buf count eff m = CheckOk m' evs ->
  eff_writes eff = [(a, bs)] ->
  (Z.of_nat (length bs) <= MAX_RW_COUNT)%Z.
Proof.
  intros i buf count eff m m' evs a bs H Hws.
  unfold check_read_urandom in H. cbv zeta in H.
  destruct (w_is0 count); cbv iota in H.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & _ & _). discriminate Hws. }
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)); cbv iota in H.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & _ & _). discriminate Hws. }
  destruct (Z.eqb (Z.of_nat (length (fst (stream_take_z (m_urandom m)
                                            (rw_count_clamp count)))))
                  (rw_count_clamp count)) eqn:Hlen; cbn [negb] in H; cbv iota in H;
    [|discriminate].
  apply Z.eqb_eq in Hlen.
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (stream_take_z (m_urandom m) (rw_count_clamp count)))));
    cbv iota in H; [|discriminate].
  destruct eff as [ret ws zs us cs copyins]. cbn in Hws. subst ws.
  destruct zs; destruct us; destruct cs; destruct copyins;
    cbv iota in H; try discriminate H.
  destruct (bv_eqb a buf
            && bv_eqb ret (len_word (fst (stream_take_z (m_urandom m) (rw_count_clamp count))))
            && listN_eqb bs (fst (stream_take_z (m_urandom m) (rw_count_clamp count))))
    eqn:Hb; [|discriminate].
  apply andb_true_iff in Hb as [_ HC]. apply listN_eqb_eq in HC. subst bs.
  rewrite Hlen. pose proof (rw_count_clamp_range count). lia.
Qed.

(** THE SAME STREAM READS THE SAME BYTES: two models that agree on
    [m_urandom] — the source and
    the target of an equivalence pair, seeded from one [in_urandom] —
    hand the same bytes to the same request and leave the same
    remainder, whatever else they differ in.  Nothing is chosen on the
    way, so this is by computation rather than by a relation between
    choices.  [Checks.Cases.Fs.Open] instantiates it on a concrete
    pair. *)
Lemma check_read_urandom_same_stream :
  forall i buf count eff1 eff2 m1 m2 m1' m2' evs1 evs2,
  m_urandom m1 = m_urandom m2 ->
  check_read_urandom i buf count eff1 m1 = CheckOk m1' evs1 ->
  check_read_urandom i buf count eff2 m2 = CheckOk m2' evs2 ->
  eff_writes eff1 = eff_writes eff2
  /\ eff_ret eff1 = eff_ret eff2
  /\ m_urandom m1' = m_urandom m2'.
Proof.
  intros i buf count eff1 eff2 m1 m2 m1' m2' evs1 evs2 Hu H1 H2.
  unfold check_read_urandom in H1, H2. cbv zeta in H1, H2. rewrite Hu in H1.
  destruct (w_is0 count).
  { apply check_ret_only_ok_iff in H1. destruct H1 as (-> & -> & ->).
    apply check_ret_only_ok_iff in H2. destruct H2 as (-> & -> & ->).
    now repeat split. }
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|].
  2:{ apply check_ret_only_ok_iff in H1. destruct H1 as (-> & -> & ->).
      apply check_ret_only_ok_iff in H2. destruct H2 as (-> & -> & ->).
      now repeat split. }
  destruct (negb (Z.eqb (Z.of_nat (length (fst (stream_take_z (m_urandom m2)
                                                  (rw_count_clamp count)))))
                        (rw_count_clamp count))); [discriminate|].
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (stream_take_z (m_urandom m2) (rw_count_clamp count)))))
    as [wn|]; [|discriminate].
  destruct eff1 as [ret1 ws1 zs1 us1 cs1 ci1]; destruct ws1 as [|[a1 bs1] [|]];
    destruct zs1 as [|? ?]; destruct us1 as [|? ?];
    destruct cs1 as [|? ?]; destruct ci1 as [|? ?]; try discriminate.
  destruct eff2 as [ret2 ws2 zs2 us2 cs2 ci2]; destruct ws2 as [|[a2 bs2] [|]];
    destruct zs2 as [|? ?]; destruct us2 as [|? ?];
    destruct cs2 as [|? ?]; destruct ci2 as [|? ?]; try discriminate.
  destruct (bv_eqb a1 buf
            && bv_eqb ret1 (len_word (fst (stream_take_z (m_urandom m2) (rw_count_clamp count))))
            && listN_eqb bs1 (fst (stream_take_z (m_urandom m2) (rw_count_clamp count))))
    eqn:Hb1; [|discriminate].
  destruct (bv_eqb a2 buf
            && bv_eqb ret2 (len_word (fst (stream_take_z (m_urandom m2) (rw_count_clamp count))))
            && listN_eqb bs2 (fst (stream_take_z (m_urandom m2) (rw_count_clamp count))))
    eqn:Hb2; [|discriminate].
  inversion H1; clear H1; subst. inversion H2; clear H2; subst.
  apply andb_true_iff in Hb1 as [Hb1 HC1]. apply andb_true_iff in Hb1 as [HA1 HB1].
  apply andb_true_iff in Hb2 as [Hb2 HC2]. apply andb_true_iff in Hb2 as [HA2 HB2].
  apply bv_eqb_eq in HA1, HB1, HA2, HB2. apply listN_eqb_eq in HC1, HC2. subst.
  cbn. autorewrite with model. now repeat split.
Qed.

(** [ReadWrite.read_proc_spec] as an acceptor, branch for branch: the
    [access_ok] -EFAULT, the count gate, then the destination.  Over a
    wholly writable range an effect is accepted when it is an
    error-encoded return with nothing written (the spec's
    [Syscall.errno_any]), a 0 with nothing written (the empty delivery),
    or a return of [len bs] with the ONE write [(buf, bs)] of a nonempty
    [bs] no longer than [count] (the spec's [Uaccess.delivered_writes]).
    Over a range not one byte of which is writable only the first two
    are, and a partly writable range is declined. *)
Definition check_read_proc_bare (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_any_b ret || bv_eqb ret (Z_to_bv 64 0) then CheckOk m []
      else CheckReject
  | _ => CheckReject
  end.

Definition check_read_proc (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb buf (bv_unsigned count))
  then check_ret_only eff (errno_ret EFAULT) m []
  else if negb (modeled_rw_count count) then CheckUnmodeled
  else
  match read_bytes_map (in_wmem i) buf count with
  | Some _ =>
      match eff with
      | mkEffectU ret [(a, bs)] [] [] [] [] =>
          if bv_eqb a buf && bv_eqb ret (len_word bs)
             && negb (Nat.eqb (length bs) 0)
             && (Z.of_nat (length bs) <=? bv_unsigned count)%Z
          then CheckOk m [] else CheckReject
      | _ => check_read_proc_bare eff m
      end
  | None =>
      match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
      | None => check_read_proc_bare eff m
      | Some _ => CheckUnmodeled
      end
  end.

Local Lemma check_read_proc_bare_sound_ok : forall i (buf count : word) eff m m' evs,
  (0 <= bv_unsigned count)%Z ->
  check_read_proc_bare eff m = CheckOk m' evs ->
  alt (bind errno_any (fun e => err_ret e))
      (bind (choose (fun bs : list byte =>
                       (Z.of_nat (length bs) <= bv_unsigned count)%Z))
            (fun bs => pure (mkEffect (len_word bs) (delivered_writes buf bs) [])))
    i m (Ok eff m' evs).
Proof.
  intros i buf count eff m m' evs Hc H.
  unfold check_read_proc_bare in H.
  destruct eff as [ret ws zs us cs ci].
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct ci as [|? ?]; try discriminate.
  destruct (errno_any_b ret) eqn:He; cbn [orb] in H.
  - inversion H; clear H; subst.
    apply errno_any_b_errno in He. destruct He as (e & He & ->).
    apply alt_l. eapply bind_ok0.
    { unfold errno_any. apply (choose_ok _ e). exact He. }
    apply pure_ok.
  - destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:H0; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in H0. subst ret.
    apply alt_r. eapply bind_ok0.
    { apply (choose_ok _ []). cbn. lia. }
    apply pure_ok.
Qed.

Lemma check_read_proc_sound_ok : forall i buf count eff m m' evs,
  check_read_proc i buf count eff m = CheckOk m' evs ->
  read_proc_spec buf count i m (Ok eff m' evs).
Proof.
  intros i buf count eff m m' evs H.
  pose proof (bv_unsigned_in_range 64 count) as Hrange.
  unfold check_read_proc in H. unfold read_proc_spec.
  destruct (negb (access_okb buf (bv_unsigned count))).
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (negb (modeled_rw_count count)); [discriminate|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) buf count) as [w|].
  - destruct eff as [ret ws zs us cs ci].
    destruct ws as [|[a bs] [|]]; destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct ci as [|? ?];
      try (eapply check_read_proc_bare_sound_ok; [lia|exact H]).
    destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
              && negb (Nat.eqb (length bs) 0)
              && (Z.of_nat (length bs) <=? bv_unsigned count)%Z) eqn:Hb;
      [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hb as [Hb Hle]. apply andb_true_iff in Hb as [Hb Hne].
    apply andb_true_iff in Hb as [Ha Hr].
    apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. subst a ret.
    apply Z.leb_le in Hle.
    apply alt_r. eapply bind_ok0; [apply (choose_ok _ bs); exact Hle|].
    destruct bs as [|b bs']; [discriminate|]. apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|];
      [discriminate|].
    unfold check_read_proc_bare in H.
    destruct eff as [ret ws zs us cs ci].
    destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct ci as [|? ?]; try discriminate.
    destruct (errno_any_b ret) eqn:He; cbn [orb] in H.
    + inversion H; clear H; subst.
      apply errno_any_b_errno in He. destruct He as (e & He & ->).
      apply alt_l. eapply bind_ok0.
      { unfold errno_any. apply (choose_ok _ e). exact He. }
      apply pure_ok.
    + destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:H0; [|discriminate].
      inversion H; clear H; subst. apply bv_eqb_eq in H0. subst ret.
      apply alt_r. apply pure_ok.
Qed.

Local Lemma check_read_proc_bare_no_unmodeled : forall eff m,
  check_read_proc_bare eff m <> CheckUnmodeled.
Proof.
  intros [ret ws zs us cs ci] m. unfold check_read_proc_bare.
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct ci as [|? ?]; try discriminate.
  destruct (errno_any_b ret || bv_eqb ret (Z_to_bv 64 0)); discriminate.
Qed.

Lemma check_read_proc_sound_unmodeled : forall i buf count eff m,
  check_read_proc i buf count eff m = CheckUnmodeled ->
  read_proc_spec buf count i m Unmodeled.
Proof.
  intros i buf count eff m H.
  unfold check_read_proc in H. unfold read_proc_spec.
  destruct (negb (access_okb buf (bv_unsigned count)));
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (negb (modeled_rw_count count)); [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) buf count) as [w|].
  - exfalso.
    destruct eff as [ret ws zs us cs ci].
    destruct ws as [|[a bs] [|]]; destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct ci as [|? ?];
      try exact (check_read_proc_bare_no_unmodeled _ _ H).
    destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
              && negb (Nat.eqb (length bs) 0)
              && (Z.of_nat (length bs) <=? bv_unsigned count)%Z); discriminate.
  - destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|];
      [apply unmodeled_intro|].
    exfalso. exact (check_read_proc_bare_no_unmodeled _ _ H).
Qed.

Lemma check_read_proc_complete_ok : forall i buf count eff m m' evs,
  read_proc_spec buf count i m (Ok eff m' evs) ->
  check_read_proc i buf count eff m = CheckOk m' evs.
Proof.
  intros i buf count eff m m' evs H.
  unfold read_proc_spec, errno_any in H. unfold check_read_proc.
  sys_unfold.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha; hall Ha; inv_ok.
  { cbn; rewrite bv_eqb_refl; reflexivity. }
  destruct (negb (modeled_rw_count count)) eqn:Hc; hall Hc; inv_ok.
  destruct (read_bytes_map (in_wmem i) buf count) as [w|] eqn:Hw; hall Hw; inv_ok.
  - (* the errno *)
    unfold check_read_proc_bare. rewrite errno_any_b_ret by (intuition lia). reflexivity.
  - (* a delivery of [x] bytes *)
    match goal with
    | Hx : (Z.of_nat (length ?x) <= bv_unsigned count)%Z |- _ =>
        destruct x as [|b bs]; cbn [delivered_writes]; cbv beta iota
    end.
    + unfold check_read_proc_bare. cbv beta iota.
      first [ reflexivity
            | rewrite Bool.orb_true_r; reflexivity
            | rewrite bv_eqb_refl, Bool.orb_true_r; reflexivity ].
    + match goal with
      | Hx : (Z.of_nat (length (_ :: _)) <= _)%Z |- _ =>
          apply Z.leb_le in Hx; rewrite !bv_eqb_refl, Hx; reflexivity
      end.
  - destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
      hall Hw1; inv_ok;
      unfold check_read_proc_bare; cbv beta iota.
    + rewrite errno_any_b_ret by (intuition lia). reflexivity.
    + first [ reflexivity
            | rewrite Bool.orb_true_r; reflexivity
            | rewrite bv_eqb_refl, Bool.orb_true_r; reflexivity ].
Qed.

Lemma check_read_proc_complete_unmodeled : forall i buf count m eff,
  read_proc_spec buf count i m Unmodeled ->
  check_read_proc i buf count eff m = CheckUnmodeled.
Proof.
  intros i buf count m eff H.
  unfold read_proc_spec, errno_any in H. unfold check_read_proc.
  sys_unfold.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha; hall Ha; inv_ok.
  destruct (negb (modeled_rw_count count)) eqn:Hc; hall Hc; inv_ok;
    [reflexivity|].
  destruct (read_bytes_map (in_wmem i) buf count) as [w|] eqn:Hw; hall Hw; inv_ok.
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
    hall Hw1; inv_ok.
  reflexivity.
Qed.

(** What a sysctl read delivers is under the clamp: the count gate keeps
    [count] at or below [Uaccess.rw_bytes_max], and the delivery at or
    below [count].  [Checks.Cases.Fs.ReadWrite.read_delivery_clamped]
    reads it, beside [check_read_urandom_delivery_clamped]. *)
Lemma check_read_proc_delivery_clamped : forall i buf count eff m m' evs a bs,
  check_read_proc i buf count eff m = CheckOk m' evs ->
  eff_writes eff = [(a, bs)] ->
  (Z.of_nat (length bs) <= MAX_RW_COUNT)%Z.
Proof.
  intros i buf count eff m m' evs a bs H Hws.
  unfold check_read_proc in H.
  destruct (negb (access_okb buf (bv_unsigned count))).
  { apply check_ret_only_ok_iff in H. destruct H as (-> & _ & _). discriminate Hws. }
  destruct (negb (modeled_rw_count count)) eqn:Hc; [discriminate|].
  unfold modeled_rw_count in Hc. apply negb_false_iff, Z.leb_le in Hc.
  destruct eff as [ret ws zs us cs ci]. cbn in Hws. subst ws.
  destruct (read_bytes_map (in_wmem i) buf count).
  2:{ destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)); [discriminate|].
      unfold check_read_proc_bare in H. discriminate. }
  destruct zs as [|? ?]; destruct us as [|? ?]; destruct cs as [|? ?];
    destruct ci as [|? ?]; cbv beta iota in H;
    try (unfold check_read_proc_bare in H; discriminate).
  destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
            && negb (Nat.eqb (length bs) 0)
            && (Z.of_nat (length bs) <=? bv_unsigned count)%Z) eqn:Hb;
    [|discriminate].
  apply andb_true_iff in Hb as [_ Hle]. apply Z.leb_le in Hle.
  unfold rw_bytes_max, MAX_RW_COUNT in *. lia.
Qed.

(* -------------------------------------------------------------------------
   read (63) and write (64) on an eventfd ([ReadWrite.read_eventfd_spec],
   [ReadWrite.write_eventfd_spec])
   ------------------------------------------------------------------------- *)

(** Two closed facts about [eff_is_errno] that the proofs below rewrite
    with rather than recompute. *)
Local Lemma eff_is_errno_mkEffect : forall c r,
  eff_is_errno c (mkEffect r [] []) = bv_eqb r (errno_ret c).
Proof. reflexivity. Qed.

Local Lemma eff_is_errno_with_copyins : forall c reads r,
  eff_is_errno c (clear_copyins (with_copyins reads (mkEffect r [] [])))
  = bv_eqb r (errno_ret c).
Proof. reflexivity. Qed.

Local Lemma efault_not_eagain : bv_eqb (errno_ret EFAULT) (errno_ret EAGAIN) = false.
Proof. vm_compute. reflexivity. Qed.

Local Lemma eight_not_eagain : bv_eqb (Z_to_bv 64 8) (errno_ret EAGAIN) = false.
Proof. vm_compute. reflexivity. Qed.

(** [ReadWrite.eventfd_deliver] as an acceptor: 8 returned, ONE 8-byte
    write at [buf] that [eventfd_value_ok] admits, nothing else. *)
Definition check_eventfd_deliver (flags buf : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match eff with
  | mkEffectU r [(a, bs)] [] [] [] [] =>
      if bv_eqb r (Z_to_bv 64 8) && bv_eqb a buf && eventfd_value_ok flags bs
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

Local Lemma check_eventfd_deliver_ok : forall flags buf i eff m m' evs,
  check_eventfd_deliver flags buf eff m = CheckOk m' evs ->
  eventfd_deliver flags buf i m (Ok eff m' evs).
Proof.
  intros flags buf i eff m m' evs H.
  unfold check_eventfd_deliver in H. unfold eventfd_deliver.
  destruct eff as [r ws zs us cs ci].
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct ci as [|? ?]; try discriminate.
  cbv beta iota in H.
  destruct (bv_eqb r (Z_to_bv 64 8) && bv_eqb a buf && eventfd_value_ok flags bs)
    eqn:Hb; [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in Hb as [Hb Hv]. apply andb_true_iff in Hb as [Hr Ha].
  apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst r a.
  eapply bind_ok0; [apply (choose_ok _ bs); exact Hv|]. apply pure_ok.
Qed.

Local Lemma check_eventfd_deliver_no_unmodeled : forall flags buf eff m,
  check_eventfd_deliver flags buf eff m <> CheckUnmodeled.
Proof.
  intros flags buf [r ws zs us cs ci] m. unfold check_eventfd_deliver.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct ci as [|? ?]; try discriminate.
  cbv beta iota.
  destruct (bv_eqb r (Z_to_bv 64 8) && bv_eqb a buf && eventfd_value_ok flags bs);
    discriminate.
Qed.

Local Lemma check_eventfd_deliver_refl : forall flags buf bs m,
  eventfd_value_ok flags bs = true ->
  check_eventfd_deliver flags buf (mkEffect (Z_to_bv 64 8) [(buf, bs)] []) m
  = CheckOk m [].
Proof.
  intros flags buf bs m Hv. unfold check_eventfd_deliver. cbv beta iota.
  rewrite !bv_eqb_refl, Hv. reflexivity.
Qed.

Local Lemma check_eventfd_deliver_len : forall flags buf eff m m' evs a bs,
  check_eventfd_deliver flags buf eff m = CheckOk m' evs ->
  eff_writes eff = [(a, bs)] -> length bs = 8%nat.
Proof.
  intros flags buf [r ws zs us cs ci] m m' evs a bs H Hws.
  cbn in Hws. subst ws. unfold check_eventfd_deliver in H.
  destruct zs as [|? ?]; destruct us as [|? ?]; destruct cs as [|? ?];
    destruct ci as [|? ?]; try discriminate.
  cbv beta iota in H.
  destruct (bv_eqb r (Z_to_bv 64 8) && bv_eqb a buf && eventfd_value_ok flags bs)
    eqn:Hb; [|discriminate].
  apply andb_true_iff in Hb as [_ Hv]. unfold eventfd_value_ok in Hv.
  apply andb_true_iff in Hv as [Hv _]. apply andb_true_iff in Hv as [Hv _].
  now apply Nat.eqb_eq in Hv.
Qed.

Local Lemma eventfd_deliver_inv : forall flags buf i m eff m' evs,
  eventfd_deliver flags buf i m (Ok eff m' evs) ->
  exists bs, eff = mkEffect (Z_to_bv 64 8) [(buf, bs)] []
             /\ m' = m /\ evs = [] /\ eventfd_value_ok flags bs = true.
Proof.
  intros flags buf i m eff m' evs H.
  unfold eventfd_deliver in H. sys_unfold. inv_ok.
  eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. eassumption.
Qed.

Local Lemma eventfd_deliver_no_unmodeled : forall flags buf i m,
  ~ eventfd_deliver flags buf i m Unmodeled.
Proof.
  intros flags buf i m H. unfold eventfd_deliver in H. sys_unfold. inv_ok.
Qed.

(** [ReadWrite.read_eventfd_spec] as an acceptor, branch for branch:
    [access_ok]'s -EFAULT, the short-count -EINVAL, the decline of a
    blocking eventfd, then the destination: an -EAGAIN with nothing
    written beside the delivery, or beside the -EFAULT of a destination
    with no writable byte. *)
Definition check_read_eventfd (i : SyscallInput) (flags buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb buf (bv_unsigned count))
  then check_ret_only eff (errno_ret EFAULT) m []
  else if (bv_unsigned count <? 8)%Z
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (efd_nonblock_b flags) then CheckUnmodeled
  else
  match read_bytes_map (in_wmem i) buf (Z_to_bv 64 8) with
  | Some _ =>
      if eff_is_errno EAGAIN eff then CheckOk m []
      else check_eventfd_deliver flags buf eff m
  | None =>
      match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
      | None =>
          if eff_is_errno EAGAIN eff then CheckOk m []
          else check_ret_only eff (errno_ret EFAULT) m []
      | Some _ => CheckUnmodeled
      end
  end.

Lemma check_read_eventfd_sound_ok : forall i flags buf count eff m m' evs,
  check_read_eventfd i flags buf count eff m = CheckOk m' evs ->
  read_eventfd_spec flags buf count i m (Ok eff m' evs).
Proof.
  intros i flags buf count eff m m' evs H.
  unfold check_read_eventfd in H. unfold read_eventfd_spec.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (bv_unsigned count <? 8)%Z eqn:Hc; cbv beta iota in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (negb (efd_nonblock_b flags)) eqn:Hn; cbv beta iota in H |- *;
    [discriminate H|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 8)) as [w|] eqn:Hw;
    cbv beta iota in H |- *.
  - destruct (eff_is_errno EAGAIN eff) eqn:He; cbv beta iota in H.
    + apply eff_is_errno_true in He. subst eff. inversion H; clear H; subst.
      apply alt_l. apply pure_ok.
    + apply alt_r. now apply check_eventfd_deliver_ok.
  - destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
      cbv beta iota in H |- *; [discriminate H|].
    destruct (eff_is_errno EAGAIN eff) eqn:He; cbv beta iota in H.
    + apply eff_is_errno_true in He. subst eff. inversion H; clear H; subst.
      apply alt_l. apply pure_ok.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      apply alt_r. apply pure_ok.
Qed.

Lemma check_read_eventfd_sound_unmodeled : forall i flags buf count eff m,
  check_read_eventfd i flags buf count eff m = CheckUnmodeled ->
  read_eventfd_spec flags buf count i m Unmodeled.
Proof.
  intros i flags buf count eff m H.
  unfold check_read_eventfd in H. unfold read_eventfd_spec.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (bv_unsigned count <? 8)%Z eqn:Hc; cbv beta iota in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (efd_nonblock_b flags)) eqn:Hn; cbv beta iota in H |- *;
    [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 8)) as [w|] eqn:Hw;
    cbv beta iota in H |- *.
  - exfalso.
    destruct (eff_is_errno EAGAIN eff) eqn:He; cbv beta iota in H;
      [discriminate H|].
    exact (check_eventfd_deliver_no_unmodeled _ _ _ _ H).
  - destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
      cbv beta iota in H |- *; [apply unmodeled_intro|].
    exfalso.
    destruct (eff_is_errno EAGAIN eff) eqn:He; cbv beta iota in H;
      [discriminate H|].
    now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_read_eventfd_complete_ok : forall i flags buf count eff m m' evs,
  read_eventfd_spec flags buf count i m (Ok eff m' evs) ->
  check_read_eventfd i flags buf count eff m = CheckOk m' evs.
Proof.
  intros i flags buf count eff m m' evs H.
  unfold read_eventfd_spec in H. unfold check_read_eventfd.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    apply check_ret_only_ok_iff. now repeat split. }
  destruct (bv_unsigned count <? 8)%Z eqn:Hc; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    apply check_ret_only_ok_iff. now repeat split. }
  destruct (negb (efd_nonblock_b flags)) eqn:Hn; cbv beta iota in H |- *;
    [unfold unmodeled in H; discriminate H|].
  apply input_bind_ok_inv in H. cbv beta in H.
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 8)) as [w|] eqn:Hw;
    cbv beta iota in H |- *.
  - unfold alt in H. destruct H as [H|H].
    + unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
      rewrite eff_is_errno_mkEffect, bv_eqb_refl. reflexivity.
    + apply eventfd_deliver_inv in H. destruct H as (bs & -> & -> & -> & Hv).
      replace (eff_is_errno EAGAIN (mkEffect (Z_to_bv 64 8) [(buf, bs)] []))
        with false by reflexivity.
      cbv beta iota. now apply check_eventfd_deliver_refl.
  - destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
      cbv beta iota in H |- *; [unfold unmodeled in H; discriminate H|].
    unfold alt in H. destruct H as [H|H];
      unfold err_ret, ret_only, pure in H; inversion H; clear H; subst.
    + rewrite eff_is_errno_mkEffect, bv_eqb_refl. reflexivity.
    + rewrite eff_is_errno_mkEffect, efault_not_eagain. cbv beta iota.
      apply check_ret_only_ok_iff. now repeat split.
Qed.

Lemma check_read_eventfd_complete_unmodeled : forall i flags buf count m eff,
  read_eventfd_spec flags buf count i m Unmodeled ->
  check_read_eventfd i flags buf count eff m = CheckUnmodeled.
Proof.
  intros i flags buf count m eff H.
  unfold read_eventfd_spec in H. unfold check_read_eventfd.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (bv_unsigned count <? 8)%Z eqn:Hc; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (negb (efd_nonblock_b flags)) eqn:Hn; cbv beta iota in H |- *;
    [reflexivity|].
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 8)) as [w|] eqn:Hw;
    cbv beta iota in H |- *.
  - exfalso. unfold alt in H. destruct H as [H|H].
    + unfold err_ret, ret_only, pure in H. discriminate H.
    + exact (eventfd_deliver_no_unmodeled _ _ _ _ H).
  - destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
      cbv beta iota in H |- *; [reflexivity|].
    exfalso. unfold alt in H. destruct H as [H|H];
      unfold err_ret, ret_only, pure in H; discriminate H.
Qed.

(** What an eventfd read delivers is 8 bytes, under the clamp. *)
Lemma check_read_eventfd_delivery_clamped : forall i flags buf count eff m m' evs a bs,
  check_read_eventfd i flags buf count eff m = CheckOk m' evs ->
  eff_writes eff = [(a, bs)] ->
  (Z.of_nat (length bs) <= MAX_RW_COUNT)%Z.
Proof.
  intros i flags buf count eff m m' evs a bs H Hws.
  assert (Hro : forall v mk evs', check_ret_only eff v mk evs' = CheckOk m' evs -> False).
  { intros v mk evs' Hc. apply check_ret_only_ok_iff in Hc.
    destruct Hc as (-> & _ & _). discriminate Hws. }
  unfold check_read_eventfd in H.
  destruct (negb (access_okb buf (bv_unsigned count))); cbv beta iota in H;
    [destruct (Hro _ _ _ H)|].
  destruct (bv_unsigned count <? 8)%Z; cbv beta iota in H; [destruct (Hro _ _ _ H)|].
  destruct (negb (efd_nonblock_b flags)); cbv beta iota in H; [discriminate H|].
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 8)); cbv beta iota in H.
  - destruct (eff_is_errno EAGAIN eff) eqn:He; cbv beta iota in H.
    + apply eff_is_errno_true in He. subst eff. discriminate Hws.
    + rewrite (check_eventfd_deliver_len _ _ _ _ _ _ _ _ H Hws).
      unfold MAX_RW_COUNT. lia.
  - destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)); cbv beta iota in H;
      [discriminate H|].
    destruct (eff_is_errno EAGAIN eff) eqn:He; cbv beta iota in H;
      [|destruct (Hro _ _ _ H)].
    apply eff_is_errno_true in He. subst eff. discriminate Hws.
Qed.

(** [ReadWrite.write_eventfd_spec] as an acceptor, branch for branch:
    [access_ok]'s -EFAULT, the count -EINVAL, the failed copy's -EFAULT
    with an empty ledger, and past the copy, under its 8-byte ledger,
    the [ULLONG_MAX] -EINVAL, an -EAGAIN on a non-blocking eventfd, and
    the 8. *)
Definition check_write_eventfd (i : SyscallInput) (flags buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb buf (bv_unsigned count))
  then check_ret_only eff (errno_ret EFAULT) m []
  else if negb (Z.eqb (bv_unsigned count) 8)
  then check_ret_only eff (errno_ret EINVAL) m []
  else
  match read_bytes_map (in_mem i) buf (Z_to_bv 64 8) with
  | None => check_ret_only eff (errno_ret EFAULT) m []
  | Some bs =>
      if Z.eqb (bytes_le_to_Z bs) (2 ^ 64 - 1)%Z
      then check_ret_only_copyins [(buf, 8%nat)] eff (errno_ret EINVAL) m []
      else if efd_nonblock_b flags
      then (if eff_is_errno EAGAIN (clear_copyins eff)
            then check_ret_only_copyins [(buf, 8%nat)] eff (errno_ret EAGAIN) m []
            else check_ret_only_copyins [(buf, 8%nat)] eff (Z_to_bv 64 8) m [])
      else check_ret_only_copyins [(buf, 8%nat)] eff (Z_to_bv 64 8) m []
  end.

Lemma check_write_eventfd_sound_ok : forall i flags buf count eff m m' evs,
  check_write_eventfd i flags buf count eff m = CheckOk m' evs ->
  write_eventfd_spec flags buf count i m (Ok eff m' evs).
Proof.
  intros i flags buf count eff m m' evs H.
  unfold check_write_eventfd in H. unfold write_eventfd_spec.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (negb (Z.eqb (bv_unsigned count) 8)) eqn:Hc; cbv beta iota in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_mem i) buf (Z_to_bv 64 8)) as [bs|] eqn:Hr;
    cbv beta iota in H |- *.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (Z.eqb (bytes_le_to_Z bs) (2 ^ 64 - 1)%Z) eqn:Hmax; cbv beta iota in H |- *.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
  destruct (efd_nonblock_b flags) eqn:Hn; cbv beta iota in H |- *.
  - destruct (eff_is_errno EAGAIN (clear_copyins eff)) eqn:He; cbv beta iota in H.
    + apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      apply record_copyins_ok_empty; [reflexivity|]. apply alt_l. apply pure_ok.
    + apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      apply record_copyins_ok_empty; [reflexivity|]. apply alt_r. apply pure_ok.
  - apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
Qed.

Local Lemma check_write_eventfd_no_unmodeled : forall i flags buf count eff m,
  check_write_eventfd i flags buf count eff m <> CheckUnmodeled.
Proof.
  intros i flags buf count eff m H.
  unfold check_write_eventfd in H.
  destruct (negb (access_okb buf (bv_unsigned count))); cbv beta iota in H;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (negb (Z.eqb (bv_unsigned count) 8)); cbv beta iota in H;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (read_bytes_map (in_mem i) buf (Z_to_bv 64 8)) as [bs|]; cbv beta iota in H;
    [|now apply check_ret_only_no_unmodeled in H].
  destruct (Z.eqb (bytes_le_to_Z bs) (2 ^ 64 - 1)%Z); cbv beta iota in H;
    [now apply check_ret_only_copyins_no_unmodeled in H|].
  destruct (efd_nonblock_b flags); cbv beta iota in H;
    [|now apply check_ret_only_copyins_no_unmodeled in H].
  destruct (eff_is_errno EAGAIN (clear_copyins eff)); cbv beta iota in H;
    now apply check_ret_only_copyins_no_unmodeled in H.
Qed.

Lemma check_write_eventfd_sound_unmodeled : forall i flags buf count eff m,
  check_write_eventfd i flags buf count eff m = CheckUnmodeled ->
  write_eventfd_spec flags buf count i m Unmodeled.
Proof.
  intros i flags buf count eff m H. exfalso.
  exact (check_write_eventfd_no_unmodeled _ _ _ _ _ _ H).
Qed.

Lemma check_write_eventfd_complete_ok : forall i flags buf count eff m m' evs,
  write_eventfd_spec flags buf count i m (Ok eff m' evs) ->
  check_write_eventfd i flags buf count eff m = CheckOk m' evs.
Proof.
  intros i flags buf count eff m m' evs H.
  unfold write_eventfd_spec in H. unfold check_write_eventfd.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    apply check_ret_only_ok_iff. now repeat split. }
  destruct (negb (Z.eqb (bv_unsigned count) 8)) eqn:Hc; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    apply check_ret_only_ok_iff. now repeat split. }
  apply input_bind_ok_inv in H. cbv beta in H.
  destruct (read_bytes_map (in_mem i) buf (Z_to_bv 64 8)) as [bs|] eqn:Hr;
    cbv beta iota in H |- *.
  2:{ unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
      apply check_ret_only_ok_iff. now repeat split. }
  apply record_copyins_ok_inv in H. destruct H as (core & H & ->).
  destruct (Z.eqb (bytes_le_to_Z bs) (2 ^ 64 - 1)%Z) eqn:Hmax; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (efd_nonblock_b flags) eqn:Hn; cbv beta iota in H |- *.
  - unfold alt in H. destruct H as [H|H];
      unfold err_ret, ret_only, pure in H; inversion H; clear H; subst.
    + rewrite eff_is_errno_with_copyins, bv_eqb_refl. cbv beta iota.
      apply check_ret_only_copyins_ok_iff. now repeat split.
    + rewrite eff_is_errno_with_copyins, eight_not_eagain. cbv beta iota.
      apply check_ret_only_copyins_ok_iff. now repeat split.
  - unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    apply check_ret_only_copyins_ok_iff. now repeat split.
Qed.

Lemma check_write_eventfd_complete_unmodeled : forall i flags buf count m eff,
  write_eventfd_spec flags buf count i m Unmodeled ->
  check_write_eventfd i flags buf count eff m = CheckUnmodeled.
Proof.
  intros i flags buf count m eff H. exfalso.
  unfold write_eventfd_spec in H.
  destruct (negb (access_okb buf (bv_unsigned count))); cbv beta iota in H;
    [unfold err_ret, ret_only, pure in H; discriminate H|].
  destruct (negb (Z.eqb (bv_unsigned count) 8)); cbv beta iota in H;
    [unfold err_ret, ret_only, pure in H; discriminate H|].
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  destruct (read_bytes_map (in_mem i) buf (Z_to_bv 64 8)) as [bs|]; cbv beta iota in H;
    [|unfold err_ret, ret_only, pure in H; discriminate H].
  apply record_copyins_unmodeled_inv in H.
  destruct (Z.eqb (bytes_le_to_Z bs) (2 ^ 64 - 1)%Z); cbv beta iota in H;
    [unfold err_ret, ret_only, pure in H; discriminate H|].
  destruct (efd_nonblock_b flags); cbv beta iota in H.
  - unfold alt in H. destruct H as [H|H];
      unfold err_ret, ret_only, pure in H; discriminate H.
  - unfold ret_only, pure in H. discriminate H.
Qed.

(* -------------------------------------------------------------------------
   read (63) on a signalfd ([ReadWrite.read_signalfd_spec])
   ------------------------------------------------------------------------- *)

(** What [Signalfd.signalfd_records_b] admits is at most [n] whole
    records. *)
Local Lemma signalfd_records_b_length : forall n bs,
  signalfd_records_b n bs = true -> (length bs <= 128 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs H; [discriminate H|].
  cbn [signalfd_records_b] in H.
  change (Z.to_nat SIGNALFD_SIGINFO_BYTES) with 128%nat in H.
  apply andb_true_iff in H as [Hr Hk].
  unfold signalfd_record_ok in Hr.
  change (Z.to_nat SIGNALFD_SIGINFO_BYTES) with 128%nat in Hr.
  apply andb_true_iff in Hr as [Hl _].
  apply Nat.eqb_eq in Hl. rewrite length_firstn in Hl.
  revert Hk.
  destruct (skipn 128 bs) as [|b rest] eqn:E; intros Hk.
  - pose proof (f_equal (@length _) E) as HE.
    rewrite length_skipn in HE. cbn [length] in HE. lia.
  - pose proof (f_equal (@length _) E) as HE.
    rewrite length_skipn in HE.
    specialize (IH _ Hk). lia.
Qed.

(** [ReadWrite.signalfd_deliver] as an acceptor: the length returned,
    ONE write at [buf] that [Signalfd.signalfd_records_b] admits, nothing
    else. *)
Definition check_signalfd_deliver (buf : word) (kmax : Z) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match eff with
  | mkEffectU r [(a, bs)] [] [] [] [] =>
      if bv_eqb r (len_word bs) && bv_eqb a buf
         && signalfd_records_b (Z.to_nat kmax) bs
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

Local Lemma check_signalfd_deliver_ok : forall buf kmax i eff m m' evs,
  check_signalfd_deliver buf kmax eff m = CheckOk m' evs ->
  signalfd_deliver buf kmax i m (Ok eff m' evs).
Proof.
  intros buf kmax i eff m m' evs H.
  unfold check_signalfd_deliver in H. unfold signalfd_deliver.
  destruct eff as [r ws zs us cs ci].
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct ci as [|? ?]; try discriminate.
  cbv beta iota in H.
  destruct (bv_eqb r (len_word bs) && bv_eqb a buf
            && signalfd_records_b (Z.to_nat kmax) bs) eqn:Hb; [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in Hb as [Hb Hv]. apply andb_true_iff in Hb as [Hr Ha].
  apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst r a.
  eapply bind_ok0; [apply (choose_ok _ bs); exact Hv|]. apply pure_ok.
Qed.

Local Lemma check_signalfd_deliver_no_unmodeled : forall buf kmax eff m,
  check_signalfd_deliver buf kmax eff m <> CheckUnmodeled.
Proof.
  intros buf kmax [r ws zs us cs ci] m. unfold check_signalfd_deliver.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct ci as [|? ?]; try discriminate.
  cbv beta iota.
  destruct (bv_eqb r (len_word bs) && bv_eqb a buf
            && signalfd_records_b (Z.to_nat kmax) bs); discriminate.
Qed.

Local Lemma check_signalfd_deliver_refl : forall buf kmax bs m,
  signalfd_records_b (Z.to_nat kmax) bs = true ->
  check_signalfd_deliver buf kmax (mkEffect (len_word bs) [(buf, bs)] []) m
  = CheckOk m [].
Proof.
  intros buf kmax bs m Hv. unfold check_signalfd_deliver. cbv beta iota.
  rewrite !bv_eqb_refl, Hv. reflexivity.
Qed.

Local Lemma check_signalfd_deliver_len : forall buf kmax eff m m' evs a bs,
  check_signalfd_deliver buf kmax eff m = CheckOk m' evs ->
  eff_writes eff = [(a, bs)] -> (length bs <= 128 * Z.to_nat kmax)%nat.
Proof.
  intros buf kmax [r ws zs us cs ci] m m' evs a bs H Hws.
  cbn in Hws. subst ws. unfold check_signalfd_deliver in H.
  destruct zs as [|? ?]; destruct us as [|? ?]; destruct cs as [|? ?];
    destruct ci as [|? ?]; try discriminate.
  cbv beta iota in H.
  destruct (bv_eqb r (len_word bs) && bv_eqb a buf
            && signalfd_records_b (Z.to_nat kmax) bs) eqn:Hb; [|discriminate].
  apply andb_true_iff in Hb as [_ Hv].
  exact (signalfd_records_b_length _ _ Hv).
Qed.

Local Lemma signalfd_deliver_inv : forall buf kmax i m eff m' evs,
  signalfd_deliver buf kmax i m (Ok eff m' evs) ->
  exists bs, eff = mkEffect (len_word bs) [(buf, bs)] []
             /\ m' = m /\ evs = [] /\ signalfd_records_b (Z.to_nat kmax) bs = true.
Proof.
  intros buf kmax i m eff m' evs H.
  unfold signalfd_deliver in H. sys_unfold. inv_ok.
  eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. eassumption.
Qed.

Local Lemma signalfd_deliver_no_unmodeled : forall buf kmax i m,
  ~ signalfd_deliver buf kmax i m Unmodeled.
Proof.
  intros buf kmax i m H. unfold signalfd_deliver in H. sys_unfold. inv_ok.
Qed.

(** [ReadWrite.read_signalfd_spec] as an acceptor, branch for branch:
    [access_ok]'s -EFAULT, the no-record -EINVAL, the decline of a
    blocking signalfd and of a mask selecting a signal the process may
    hold pending, the -EAGAIN alone where no SIGCHLD can be pending, the
    count gate, then the destination: an -EAGAIN beside the records, or
    the decline of a destination not wholly writable. *)
Definition check_read_signalfd (i : SyscallInput) (mask flags buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb buf (bv_unsigned count))
  then check_ret_only eff (errno_ret EFAULT) m []
  else if Z.eqb (signalfd_read_max count) 0
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (sfd_nonblock_b flags) then CheckUnmodeled
  else if signalfd_other_may_pend mask m then CheckUnmodeled
  else if negb (signalfd_sigchld_may_pend mask m)
  then check_ret_only eff (errno_ret EAGAIN) m []
  else if negb (modeled_rw_count count) then CheckUnmodeled
  else
  match read_bytes_map (in_wmem i) buf
          (Z_to_bv 64 (SIGNALFD_SIGINFO_BYTES * signalfd_read_max count)) with
  | Some _ =>
      if eff_is_errno EAGAIN eff then CheckOk m []
      else check_signalfd_deliver buf (signalfd_read_max count) eff m
  | None => CheckUnmodeled
  end.

Lemma check_read_signalfd_sound_ok : forall i mask flags buf count eff m m' evs,
  check_read_signalfd i mask flags buf count eff m = CheckOk m' evs ->
  read_signalfd_spec mask flags buf count i m (Ok eff m' evs).
Proof.
  intros i mask flags buf count eff m m' evs H.
  unfold check_read_signalfd in H. unfold read_signalfd_spec.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (Z.eqb (signalfd_read_max count) 0) eqn:Hc; cbv beta iota in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (negb (sfd_nonblock_b flags)) eqn:Hn; cbv beta iota in H |- *;
    [discriminate H|].
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (signalfd_other_may_pend mask m) eqn:Hp; cbv beta iota in H |- *;
    [discriminate H|].
  destruct (negb (signalfd_sigchld_may_pend mask m)) eqn:Hq; cbv beta iota in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (negb (modeled_rw_count count)) eqn:Hg; cbv beta iota in H |- *;
    [discriminate H|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (SIGNALFD_SIGINFO_BYTES * signalfd_read_max count)))
    as [w|] eqn:Hw; cbv beta iota in H |- *; [|discriminate H].
  destruct (eff_is_errno EAGAIN eff) eqn:He; cbv beta iota in H.
  - apply eff_is_errno_true in He. subst eff. inversion H; clear H; subst.
    apply alt_l. apply pure_ok.
  - apply alt_r. now apply check_signalfd_deliver_ok.
Qed.

Lemma check_read_signalfd_sound_unmodeled : forall i mask flags buf count eff m,
  check_read_signalfd i mask flags buf count eff m = CheckUnmodeled ->
  read_signalfd_spec mask flags buf count i m Unmodeled.
Proof.
  intros i mask flags buf count eff m H.
  unfold check_read_signalfd in H. unfold read_signalfd_spec.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (Z.eqb (signalfd_read_max count) 0) eqn:Hc; cbv beta iota in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (sfd_nonblock_b flags)) eqn:Hn; cbv beta iota in H |- *;
    [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (signalfd_other_may_pend mask m) eqn:Hp; cbv beta iota in H |- *;
    [apply unmodeled_intro|].
  destruct (negb (signalfd_sigchld_may_pend mask m)) eqn:Hq; cbv beta iota in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (modeled_rw_count count)) eqn:Hg; cbv beta iota in H |- *;
    [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (SIGNALFD_SIGINFO_BYTES * signalfd_read_max count)))
    as [w|] eqn:Hw; cbv beta iota in H |- *; [|apply unmodeled_intro].
  exfalso.
  destruct (eff_is_errno EAGAIN eff) eqn:He; cbv beta iota in H; [discriminate H|].
  exact (check_signalfd_deliver_no_unmodeled _ _ _ _ H).
Qed.

Lemma check_read_signalfd_complete_ok : forall i mask flags buf count eff m m' evs,
  read_signalfd_spec mask flags buf count i m (Ok eff m' evs) ->
  check_read_signalfd i mask flags buf count eff m = CheckOk m' evs.
Proof.
  intros i mask flags buf count eff m m' evs H.
  unfold read_signalfd_spec in H. unfold check_read_signalfd.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    apply check_ret_only_ok_iff. now repeat split. }
  destruct (Z.eqb (signalfd_read_max count) 0) eqn:Hc; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    apply check_ret_only_ok_iff. now repeat split. }
  destruct (negb (sfd_nonblock_b flags)) eqn:Hn; cbv beta iota in H |- *;
    [unfold unmodeled in H; discriminate H|].
  apply get_model_bind_ok_inv in H. cbv beta in H.
  destruct (signalfd_other_may_pend mask m) eqn:Hp; cbv beta iota in H |- *;
    [unfold unmodeled in H; discriminate H|].
  destruct (negb (signalfd_sigchld_may_pend mask m)) eqn:Hq; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    apply check_ret_only_ok_iff. now repeat split. }
  destruct (negb (modeled_rw_count count)) eqn:Hg; cbv beta iota in H |- *;
    [unfold unmodeled in H; discriminate H|].
  apply input_bind_ok_inv in H. cbv beta in H.
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (SIGNALFD_SIGINFO_BYTES * signalfd_read_max count)))
    as [w|] eqn:Hw; cbv beta iota in H |- *;
    [|unfold unmodeled in H; discriminate H].
  unfold alt in H. destruct H as [H|H].
  - unfold err_ret, ret_only, pure in H. inversion H; clear H; subst.
    rewrite eff_is_errno_mkEffect, bv_eqb_refl. reflexivity.
  - apply signalfd_deliver_inv in H. destruct H as (bs & -> & -> & -> & Hv).
    replace (eff_is_errno EAGAIN (mkEffect (len_word bs) [(buf, bs)] []))
      with false by reflexivity.
    cbv beta iota. now apply check_signalfd_deliver_refl.
Qed.

Lemma check_read_signalfd_complete_unmodeled : forall i mask flags buf count m eff,
  read_signalfd_spec mask flags buf count i m Unmodeled ->
  check_read_signalfd i mask flags buf count eff m = CheckUnmodeled.
Proof.
  intros i mask flags buf count m eff H.
  unfold read_signalfd_spec in H. unfold check_read_signalfd.
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Ha;
    cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (Z.eqb (signalfd_read_max count) 0) eqn:Hc; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (negb (sfd_nonblock_b flags)) eqn:Hn; cbv beta iota in H |- *;
    [reflexivity|].
  apply get_model_bind_unmodeled_inv in H. cbv beta in H.
  destruct (signalfd_other_may_pend mask m) eqn:Hp; cbv beta iota in H |- *;
    [reflexivity|].
  destruct (negb (signalfd_sigchld_may_pend mask m)) eqn:Hq; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (negb (modeled_rw_count count)) eqn:Hg; cbv beta iota in H |- *;
    [reflexivity|].
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (SIGNALFD_SIGINFO_BYTES * signalfd_read_max count)))
    as [w|] eqn:Hw; cbv beta iota in H |- *; [|reflexivity].
  exfalso. unfold alt in H. destruct H as [H|H].
  - unfold err_ret, ret_only, pure in H. discriminate H.
  - exact (signalfd_deliver_no_unmodeled _ _ _ _ H).
Qed.

(** What a signalfd read delivers is whole records under the count
    gate, so under the clamp. *)
Lemma check_read_signalfd_delivery_clamped :
  forall i mask flags buf count eff m m' evs a bs,
  check_read_signalfd i mask flags buf count eff m = CheckOk m' evs ->
  eff_writes eff = [(a, bs)] ->
  (Z.of_nat (length bs) <= MAX_RW_COUNT)%Z.
Proof.
  intros i mask flags buf count eff m m' evs a bs H Hws.
  assert (Hro : forall v mk evs', check_ret_only eff v mk evs' = CheckOk m' evs -> False).
  { intros v mk evs' Hc. apply check_ret_only_ok_iff in Hc.
    destruct Hc as (-> & _ & _). discriminate Hws. }
  unfold check_read_signalfd in H.
  destruct (negb (access_okb buf (bv_unsigned count))); cbv beta iota in H;
    [destruct (Hro _ _ _ H)|].
  destruct (Z.eqb (signalfd_read_max count) 0); cbv beta iota in H;
    [destruct (Hro _ _ _ H)|].
  destruct (negb (sfd_nonblock_b flags)); cbv beta iota in H; [discriminate H|].
  destruct (signalfd_other_may_pend mask m); cbv beta iota in H; [discriminate H|].
  destruct (negb (signalfd_sigchld_may_pend mask m)); cbv beta iota in H;
    [destruct (Hro _ _ _ H)|].
  destruct (negb (modeled_rw_count count)) eqn:Hg; cbv beta iota in H;
    [discriminate H|].
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (SIGNALFD_SIGINFO_BYTES * signalfd_read_max count)));
    cbv beta iota in H; [|discriminate H].
  destruct (eff_is_errno EAGAIN eff) eqn:He; cbv beta iota in H.
  - apply eff_is_errno_true in He. subst eff. discriminate Hws.
  - pose proof (check_signalfd_deliver_len _ _ _ _ _ _ _ _ H Hws) as Hl.
    apply negb_false_iff in Hg. unfold modeled_rw_count, rw_bytes_max in Hg.
    apply Z.leb_le in Hg.
    assert (Hk : (0 <= signalfd_read_max count <= 1024)%Z).
    { pose proof (word_unsigned_range count) as Hc.
      unfold signalfd_read_max, rw_count_clamp, SIGNALFD_SIGINFO_BYTES, MAX_RW_COUNT.
      split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
    unfold MAX_RW_COUNT. lia.
Qed.

(** [ReadWrite.read_opaque_spec] as an acceptor, one arm per object. *)
Definition check_read_opaque (i : SyscallInput) (o : OpaqueFd) (buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match o with
  | OProcFile _ => check_read_proc i buf count eff m
  | OEventFd fl => check_read_eventfd i fl buf count eff m
  | OSignalFd mk fl => check_read_signalfd i mk fl buf count eff m
  | OProcPath _ | ONsFile _ | OProcFdDir _ _ => CheckUnmodeled
  end.

Lemma check_read_opaque_sound_ok : forall i o buf count eff m m' evs,
  check_read_opaque i o buf count eff m = CheckOk m' evs ->
  read_opaque_spec o buf count i m (Ok eff m' evs).
Proof.
  intros i o buf count eff m m' evs H.
  unfold check_read_opaque in H. unfold read_opaque_spec.
  destruct o; cbv beta iota in H |- *; try discriminate H.
  - now apply check_read_proc_sound_ok.
  - now apply check_read_eventfd_sound_ok.
  - now apply check_read_signalfd_sound_ok.
Qed.

Lemma check_read_opaque_sound_unmodeled : forall i o buf count eff m,
  check_read_opaque i o buf count eff m = CheckUnmodeled ->
  read_opaque_spec o buf count i m Unmodeled.
Proof.
  intros i o buf count eff m H.
  unfold check_read_opaque in H. unfold read_opaque_spec.
  destruct o; cbv beta iota in H |- *;
    [ apply unmodeled_intro
    | eapply check_read_proc_sound_unmodeled; exact H
    | eapply check_read_eventfd_sound_unmodeled; exact H
    | apply unmodeled_intro | apply unmodeled_intro
    | eapply check_read_signalfd_sound_unmodeled; exact H ].
Qed.

Lemma check_read_opaque_complete_ok : forall i o buf count eff m m' evs,
  read_opaque_spec o buf count i m (Ok eff m' evs) ->
  check_read_opaque i o buf count eff m = CheckOk m' evs.
Proof.
  intros i o buf count eff m m' evs H.
  unfold read_opaque_spec in H. unfold check_read_opaque.
  destruct o; cbv beta iota in H |- *;
    [ unfold unmodeled in H; discriminate H
    | now apply check_read_proc_complete_ok
    | now apply check_read_eventfd_complete_ok
    | unfold unmodeled in H; discriminate H
    | unfold unmodeled in H; discriminate H
    | now apply check_read_signalfd_complete_ok ].
Qed.

Lemma check_read_opaque_complete_unmodeled : forall i o buf count m eff,
  read_opaque_spec o buf count i m Unmodeled ->
  check_read_opaque i o buf count eff m = CheckUnmodeled.
Proof.
  intros i o buf count m eff H.
  unfold read_opaque_spec in H. unfold check_read_opaque.
  destruct o; cbv beta iota in H |- *;
    [ reflexivity
    | now apply check_read_proc_complete_unmodeled
    | now apply check_read_eventfd_complete_unmodeled
    | reflexivity | reflexivity
    | now apply check_read_signalfd_complete_unmodeled ].
Qed.

(** What an opaque descriptor's read delivers is under the clamp: a
    /proc/sys file's at most [count], an eventfd's 8 bytes, a signalfd's
    whole records under the count gate. *)
Lemma check_read_opaque_delivery_clamped : forall i o buf count eff m m' evs a bs,
  check_read_opaque i o buf count eff m = CheckOk m' evs ->
  eff_writes eff = [(a, bs)] ->
  (Z.of_nat (length bs) <= MAX_RW_COUNT)%Z.
Proof.
  intros i o buf count eff m m' evs a bs H Hws.
  unfold check_read_opaque in H.
  destruct o; cbv beta iota in H; try discriminate H.
  - exact (check_read_proc_delivery_clamped _ _ _ _ _ _ _ _ _ H Hws).
  - exact (check_read_eventfd_delivery_clamped _ _ _ _ _ _ _ _ _ _ H Hws).
  - exact (check_read_signalfd_delivery_clamped _ _ _ _ _ _ _ _ _ _ _ H Hws).
Qed.

(** [ReadWrite.write_opaque_spec] as an acceptor: the eventfd's arm, and
    the decline on the other five objects. *)
Definition check_write_opaque (i : SyscallInput) (o : OpaqueFd) (buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match o with
  | OEventFd fl => check_write_eventfd i fl buf count eff m
  | OProcPath _ | OProcFile _ | ONsFile _ | OProcFdDir _ _ | OSignalFd _ _ => CheckUnmodeled
  end.

Lemma check_write_opaque_sound_ok : forall i o buf count eff m m' evs,
  check_write_opaque i o buf count eff m = CheckOk m' evs ->
  write_opaque_spec o buf count i m (Ok eff m' evs).
Proof.
  intros i o buf count eff m m' evs H.
  unfold check_write_opaque in H. unfold write_opaque_spec.
  destruct o; cbv beta iota in H |- *; try discriminate H.
  now apply check_write_eventfd_sound_ok.
Qed.

Lemma check_write_opaque_sound_unmodeled : forall i o buf count eff m,
  check_write_opaque i o buf count eff m = CheckUnmodeled ->
  write_opaque_spec o buf count i m Unmodeled.
Proof.
  intros i o buf count eff m H.
  unfold check_write_opaque in H. unfold write_opaque_spec.
  destruct o; cbv beta iota in H |- *;
    [ apply unmodeled_intro | apply unmodeled_intro
    | eapply check_write_eventfd_sound_unmodeled; exact H
    | apply unmodeled_intro | apply unmodeled_intro | apply unmodeled_intro ].
Qed.

Lemma check_write_opaque_complete_ok : forall i o buf count eff m m' evs,
  write_opaque_spec o buf count i m (Ok eff m' evs) ->
  check_write_opaque i o buf count eff m = CheckOk m' evs.
Proof.
  intros i o buf count eff m m' evs H.
  unfold write_opaque_spec in H. unfold check_write_opaque.
  destruct o; cbv beta iota in H |- *;
    [ unfold unmodeled in H; discriminate H
    | unfold unmodeled in H; discriminate H
    | now apply check_write_eventfd_complete_ok
    | unfold unmodeled in H; discriminate H
    | unfold unmodeled in H; discriminate H
    | unfold unmodeled in H; discriminate H ].
Qed.

Lemma check_write_opaque_complete_unmodeled : forall i o buf count m eff,
  write_opaque_spec o buf count i m Unmodeled ->
  check_write_opaque i o buf count eff m = CheckUnmodeled.
Proof.
  intros i o buf count m eff H.
  unfold write_opaque_spec in H. unfold check_write_opaque.
  destruct o; cbv beta iota in H |- *;
    [ reflexivity | reflexivity
    | now apply check_write_eventfd_complete_unmodeled
    | reflexivity | reflexivity | reflexivity ].
Qed.

Definition check_read (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdFileW _ _) => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdFileA _ _) => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel ch) =>
      if negb (w_is0 ch) then check_ret_only eff (errno_ret EBADF) m []
      else
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []   (* vfs_read's access_ok, fs/read_write.c at v6.18.46 *)
      else
      if w_is0 count then check_ret_only eff (Z_to_bv 64 0) m []
      else
        match m_stdin m with
        | IEof => check_ret_only eff (Z_to_bv 64 0) m []   (* end of input (sticky) *)
        | ICons _ _ =>
            match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
            | None => check_ret_only eff (errno_ret EFAULT) m []  (* no byte can land: -EFAULT *)
            | Some _ =>
            match read_bytes_map (in_wmem i) buf
                    (len_word (fst (stream_take_z (m_stdin m) (rw_count_clamp count)))) with
            | None => CheckUnmodeled     (* partially writable destination: fail closed *)
            | Some _ =>
                match eff with
                | mkEffectU ret [(a, bs)] [] [] [] [] =>
                    if bv_eqb a buf
                       && bv_eqb ret (len_word bs)
                       && (1 <=? Z.of_nat (length bs))%Z
                       && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
                       && listN_eqb (fst (stream_take (m_stdin m) (length bs))) bs
                       && wmem_ok i buf (len_word bs)  (* delivered prefix writable *)
                    then CheckOk
                           (with_stdin (snd (stream_take (m_stdin m) (length bs))) m)
                           (map (ReadEv ch) bs)
                    else CheckReject
                | _ => CheckReject
                end
            end
            end
        end
  | Some FdDir =>
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else check_ret_only eff (errno_ret EISDIR) m []
  | Some (FdSocket sk) =>
      if negb (modeled_rw_range buf count) then CheckUnmodeled
      else
      if w_is0 count then
        check_access_ok_zero buf count eff m
          (check_ret_only eff (Z_to_bv 64 0) m [])
          (* [read(fd, buf, 0)] short-circuits before the protocol on ANY
             socket, so this precedes the state dispatch below *)
      else
      match sk with
      | SkConnected peer ch rx =>
          match rx with
          | NFin =>
              check_access_ok_zero buf count eff m
                (check_ret_only eff (Z_to_bv 64 0) m [])
          | NRst =>
              check_socket_pending_error ECONNRESET fd peer ch buf count i eff m
          | NTimedOut =>
              check_socket_pending_error ETIMEDOUT fd peer ch buf count i eff m
          | NCons _ _ =>
              if negb (access_okb buf (bv_unsigned count))
              then check_ret_only eff (errno_ret EFAULT) m []
                (* [vfs_read]'s [access_ok] on the named count, the guard on
                   both walks below; see [ReadWrite.read_spec]'s [NCons] *)
              else
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => check_ret_only eff (errno_ret EFAULT) m []
              | Some _ =>
              match read_bytes_map (in_wmem i) buf
                      (len_word (fst (net_take_z rx (rw_count_clamp count)))) with
              | None => CheckUnmodeled     (* partially writable destination: fail closed *)
              | Some _ =>
                  (* the delivered bytes are a nonempty prefix of what the
                     peer has left to say, and the script advances past
                     exactly them -- the channel rule, on [net_take] *)
                  match eff with
                  | mkEffectU ret [(a, bs)] [] [] [] [] =>
                      if bv_eqb a buf
                         && bv_eqb ret (len_word bs)
                         && (1 <=? Z.of_nat (length bs))%Z
                         && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
                         && listN_eqb (fst (net_take rx (length bs))) bs
                         && wmem_ok i buf (len_word bs)
                      then CheckOk
                             (with_fds
                                (fd_insert (m_fds m) fd
                                   (FdSocket
                                      (SkConnected peer ch
                                         (snd (net_take rx (length bs)))))) m)
                             (map (ReadEv ch) bs)
                      else CheckReject
                  | _ => CheckReject
                  end
              end
              end
          end
      | SkReset _ _ =>
          check_access_ok_zero buf count eff m
            (check_ret_only eff (Z_to_bv 64 0) m [])
          (* the peer's error was reported once and RCV_SHUTDOWN is set:
             0, NOT the -ENOTCONN the socket's TCP_CLOSE state suggests *)
      | _ =>
          check_access_ok_zero buf count eff m
            (check_ret_only eff (errno_ret ENOTCONN) m [])
          (* fresh, bound or listening: never TCP_ESTABLISHED *)
      end
  | Some (FdFile p off) =>
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else
      match fs_lookup (m_fs m) p with
      | None => CheckUnmodeled
      | Some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count)) in
          match read_bytes_map (in_wmem i) buf (len_word bs) with
          | None =>                  (* the DELIVERED prefix is not fully writable *)
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => check_ret_only eff (errno_ret EFAULT) m []
                                     (* not even the first delivered byte: -EFAULT *)
              | Some _ => CheckUnmodeled   (* partially writable: fail closed *)
              end
          | Some _ =>
              let m' := with_fds
                          (fd_insert (m_fds m) fd
                             (FdFile p (off + len_word bs))) m in
              match bs, eff with
              (* zero-byte read (EOF / count = 0): canonical empty-writes
                 shape, same as a zero-byte channel read *)
              | [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
              | _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
                  if bv_eqb a buf && listN_eqb bs' bs
                     && bv_eqb ret (len_word bs)
                  then CheckOk m' []
                  else CheckReject
              | _, _ => CheckReject
              end
          end
      end
  | Some (FdFileRW p off) =>   (* the [FdFile] arm above, on the O_RDWR kind *)
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else
      match fs_lookup (m_fs m) p with
      | None => CheckUnmodeled
      | Some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count)) in
          match read_bytes_map (in_wmem i) buf (len_word bs) with
          | None =>                  (* the DELIVERED prefix is not fully writable *)
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => check_ret_only eff (errno_ret EFAULT) m []
                                     (* not even the first delivered byte: -EFAULT *)
              | Some _ => CheckUnmodeled   (* partially writable: fail closed *)
              end
          | Some _ =>
              let m' := with_fds
                          (fd_insert (m_fds m) fd
                             (FdFileRW p (off + len_word bs))) m in
              match bs, eff with
              (* zero-byte read (EOF / count = 0): canonical empty-writes
                 shape, same as a zero-byte channel read *)
              | [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
              | _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
                  if bv_eqb a buf && listN_eqb bs' bs
                     && bv_eqb ret (len_word bs)
                  then CheckOk m' []
                  else CheckReject
              | _, _ => CheckReject
              end
          end
      end
  | Some (FdDevNull rd _) =>
      if negb rd then check_ret_only eff (errno_ret EBADF) m []
      else check_access_ok_zero buf count eff m
             (check_ret_only eff (Z_to_bv 64 0) m [])   (* [read_null]: 0 *)
  | Some FdUrandom =>
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else check_read_urandom i buf count eff m   (* the declared stream *)
  | Some (FdOpaque o) => check_read_opaque i o buf count eff m
  | Some (FdPipe id w) =>
      if w then check_ret_only eff (errno_ret EBADF) m []   (* write end: -EBADF *)
      else
      if negb (modeled_rw_range buf count) then CheckUnmodeled
      else
      if w_is0 count then
        check_access_ok_zero buf count eff m
          (check_ret_only eff (Z_to_bv 64 0) m [])   (* "Null read succeeds" *)
      else
      match pipe_lookup (m_pipes m) id with
      | None => CheckUnmodeled
      | Some ([], _) =>
          if pipe_end_live (m_fds m) id true then CheckUnmodeled  (* would block *)
          else check_access_ok_zero buf count eff m
                 (check_ret_only eff (Z_to_bv 64 0) m [])         (* end of file *)
      | Some ((b :: bs0) as q, used) =>
          if negb (access_okb buf (bv_unsigned count))
          then check_ret_only eff (errno_ret EFAULT) m []
            (* [vfs_read]'s [access_ok] on the named count, the guard on
               both walks below; see [ReadWrite.read_spec]'s pipe arm *)
          else
          let del := pipe_take q (rw_count_clamp count) in
          match read_bytes_map (in_wmem i) buf (len_word del) with
          | None =>
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => check_ret_only eff (errno_ret EFAULT) m []
              | Some _ => CheckUnmodeled   (* partially writable: fail closed *)
              end
          | Some _ =>
              let m' := with_pipes
                          (pipe_insert (m_pipes m) id
                             (pipe_consume (q, used) (length del))) m in
              match eff with
              | mkEffectU ret ws [] [] [] [] =>
                  if writes_eqb ws (delivered_writes buf del)
                     && bv_eqb ret (len_word del)
                  then CheckOk m' []
                  else CheckReject
              | _ => CheckReject
              end
          end
      end
  end.

(** The executable form of [ReadWrite.sigpipe_write], shared by the
    three arms that can raise signal 13.  The answer is -EPIPE with an
    EMPTY ledger -- no byte of the source is read on this path, on
    Linux or here -- over the model [ReadWrite.raise_sigpipe] produced,
    which either records the halt (signal 13 unblocked: the process
    dies, [Run.sstep_killed] fires and discards this effect) or records
    the signal as pending (signal 13 blocked: the -EPIPE is what the
    program reads). *)
Definition check_sigpipe_write (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_ret_only eff (errno_ret EPIPE) (raise_sigpipe m) [].
(** [ReadWrite.write_fault_extend] as an acceptor: the -EFAULT a
    positional file write answers when no source byte is readable, over
    the model that write still LEAVES BEHIND -- the file extended to
    [off], the descriptor untouched.  [write], [writev] and [pwrite64]
    all accept through this, so the three cannot drift from the spec
    helper or from each other.

    [reads] is the ledger the arm has already recorded when it gets
    here: empty for [write] and [pwrite64], which read nothing before
    the source, and the iovec import's ranges for [writev], which has
    read the descriptor array. *)
Definition check_write_fault_extend (reads : list (word * nat))
    (m : Model) (p : path) (off : word) (eff : SyscallEffect)
    : check_result :=
  match fs_lookup (m_fs m) p with
  | None => CheckUnmodeled
  | Some data =>
      if negb (modeled_zero_fill (bv_unsigned off) data) then CheckUnmodeled
      else check_ret_only_copyins reads eff (errno_ret EFAULT)
             (with_fs (fs_set (m_fs m) p (file_extend data off)) m) []
  end.
Definition check_write (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel ch) =>
      if w_is0 ch then check_ret_only eff (errno_ret EBADF) m []
      else
      if negb (modeled_rw_range buf count) then CheckUnmodeled
      else
      if w_is0 count
      then check_access_ok_zero buf count eff m
             (check_ret_only eff (Z_to_bv 64 0) m [])
             (* [count = 0] moves no byte, so only the range verdict is
                left — see [Uaccess.access_ok_zero] *)
      else
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
        (* [vfs_write]'s [access_ok] on the named count, the guard on the
           [write_source] walk below and the test the no-reader branch
           needs; see [ReadWrite.write_spec] *)
      else
      if negb (m_channel_reader m)
      then check_sigpipe_write eff m
        (* the far end has no reader: signal 13, behind [access_ok] as
           [vfs_write] runs it before [f_op->write_iter] *)
      else
      let bs := write_source (in_mem i) buf count in
      if Nat.eqb (length bs) 0
      then check_ret_only eff (errno_ret EFAULT) m []
      else
        (* the claimed return determines the delivered prefix: any
           nonempty prefix of the readable prefix is admissible.

           The ledger test is a nested [if] under the range test, not a
           third [&&]: [andb] is an ordinary application and [vm_compute]
           is call by value, so every operand is evaluated, and this one
           converts [ret] to a unary [nat] -- about 2^64 constructors for
           an errno-encoded return, which does not terminate (36 GB
           resident and climbing, measured).  Under the range test the
           conversion is bounded by [length bs].  Extraction is not
           affected: ExtrOcamlBasic inlines [andb] as OCaml's lazy [(&&)].
           [check_writev]'s channel arm and
           [Net.Socket.check_send_on_socket] have the same shape for the
           same reason; [check_read] never puts [ret] inside a [Z.to_nat],
           since every length it tests comes from the delivered bytes.
           Checks/Cases/Fs/ReadWrite.v's [write_channel_eintr_rejected]
           and [write_channel_epipe_rejected] close by [check_eq], which
           pins that this path evaluates. *)
        match eff with
        | mkEffectU ret [] [] [] [] copyins =>
            if (1 <=? bv_unsigned ret)%Z
               && (bv_unsigned ret <=? Z.of_nat (length bs))%Z
            then
              if access_ranges_eqb copyins [(buf, Z.to_nat (bv_unsigned ret))]
              then CheckOk m (map (WriteEv ch)
                                (firstn (Z.to_nat (bv_unsigned ret)) bs))
              else CheckReject
            else CheckReject
        | _ => CheckReject
        end
  | Some FdDir => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdSocket sk) =>
      if negb (sock_send_dead sk) then CheckUnmodeled
        (* a DELIVERING socket write is still unmodeled; see
           [ReadWrite.write_spec]'s socket arm *)
      else
      if negb (modeled_rw_range buf count) then CheckUnmodeled
      else
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else check_sigpipe_write eff m
        (* no connection to send on: -EPIPE and SIGPIPE, with no
           zero-count short-circuit -- see [ReadWrite.write_spec] *)
  | Some (FdFileW p off) =>
      if negb (modeled_rw_range buf count) then CheckUnmodeled
      else
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []   (* [vfs_write]'s [access_ok] *)
      else
      let bs := write_source (in_mem i) buf count in
      if negb (w_is0 count) && Nat.eqb (length bs) 0
      then check_write_fault_extend [] m p off eff
      else
        let k :=
          match fs_lookup (m_fs m) p with
          | None => CheckUnmodeled
          | Some data =>
              if negb (modeled_file_gap data off bs) then CheckUnmodeled
              else
              let m' :=
                with_fds (fd_insert (m_fds m) fd
                            (FdFileW p (off + len_word bs)))
                  (with_fs (fs_set (m_fs m) p (file_write data off bs)) m) in
              if w_is0 count
              then check_ret_only eff (len_word bs) m' []
              else check_ret_only_copyins [(buf, length bs)] eff (len_word bs) m' []
          end in
        if w_is0 count then check_access_ok_zero buf count eff m k else k
  | Some (FdFileRW p off) =>   (* the [FdFileW] arm above, on the O_RDWR kind *)
      if negb (modeled_rw_range buf count) then CheckUnmodeled
      else
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []   (* [vfs_write]'s [access_ok] *)
      else
      let bs := write_source (in_mem i) buf count in
      if negb (w_is0 count) && Nat.eqb (length bs) 0
      then check_write_fault_extend [] m p off eff
      else
        let k :=
          match fs_lookup (m_fs m) p with
          | None => CheckUnmodeled
          | Some data =>
              if negb (modeled_file_gap data off bs) then CheckUnmodeled
              else
              let m' :=
                with_fds (fd_insert (m_fds m) fd
                            (FdFileRW p (off + len_word bs)))
                  (with_fs (fs_set (m_fs m) p (file_write data off bs)) m) in
              if w_is0 count
              then check_ret_only eff (len_word bs) m' []
              else check_ret_only_copyins [(buf, length bs)] eff (len_word bs) m' []
          end in
        if w_is0 count then check_access_ok_zero buf count eff m k else k
  | Some (FdFileA p off) =>
      (* the arm above with the destination moved to end-of-file, the
         [modeled_file_gap] guard dropped, and [rw_verify_area]'s test
         kept on the fd's real position; see [ReadWrite.write_spec].  The
         count gate is the arm above's, [modeled_rw_range], and it does
         not subsume the [access_ok] below it -- that argument is in
         [ReadWrite.write_spec]'s [FdFileA] arm *)
      if negb (modeled_rw_range buf count) then CheckUnmodeled
      else if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb off (bv_unsigned count)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      let bs := write_source (in_mem i) buf count in
      if negb (w_is0 count) && Nat.eqb (length bs) 0
      then check_ret_only eff (errno_ret EFAULT) m []
      else
        let k :=
          match fs_lookup (m_fs m) p with
          | None => CheckUnmodeled
          | Some data =>
              let m' :=
                with_fds (fd_insert (m_fds m) fd
                            (FdFileA p (append_new_pos data bs off)))
                  (with_fs (fs_set (m_fs m) p
                              (file_write data (len_word data) bs)) m) in
              if w_is0 count
              then check_ret_only eff (len_word bs) m' []
              else check_ret_only_copyins [(buf, length bs)] eff (len_word bs) m' []
          end in
        if w_is0 count then check_access_ok_zero buf count eff m k else k
  | Some FdUrandom => check_ret_only eff (errno_ret EBADF) m []   (* read-only *)
  | Some (FdOpaque o) => check_write_opaque i o buf count eff m
  | Some (FdDevNull _ wr) =>
      if negb wr then check_ret_only eff (errno_ret EBADF) m []
      else
      if negb (modeled_rw_range buf count) then CheckUnmodeled
      else check_access_ok_zero buf count eff m
             (check_ret_only eff (Z_to_bv 64 (rw_count_clamp count)) m [])
             (* [write_null]: the clamped count, no copy-in *)
  | Some (FdPipe id w) =>
      if negb w then check_ret_only eff (errno_ret EBADF) m []   (* read end: -EBADF *)
      else
      if negb (modeled_rw_range buf count) then CheckUnmodeled
      else
      if w_is0 count
      then check_access_ok_zero buf count eff m
             (check_ret_only eff (Z_to_bv 64 0) m [])   (* "Null write succeeds" *)
      else
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
        (* [vfs_write]'s [access_ok], ahead of [anon_pipe_write]'s readers
           test; see [ReadWrite.write_spec]'s pipe arm *)
      else
      if negb (pipe_end_live (m_fds m) id false)
      then check_sigpipe_write eff m   (* no reader: -EPIPE and SIGPIPE *)
      else
      match pipe_lookup (m_pipes m) id with
      | None => CheckUnmodeled
      | Some st =>
          if negb (pipe_write_room st (bv_unsigned count)) then CheckUnmodeled
          else
          let bs := write_source (in_mem i) buf count in
          if negb (Nat.eqb (length bs) (word_to_nat count)) then CheckUnmodeled
          else
          let deliver :=
            check_ret_only_copyins [(buf, length bs)] eff count
              (with_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) m) [] in
          if pipe_needs_page st
          then
            (* [anon_pipe_get_page] may come back NULL before a byte is
               copied: [ReadWrite.write_errnos] beside the delivery *)
            match eff with
            | mkEffectU ret [] [] [] [] [] =>
                if errno_ret_in write_errnos ret then CheckOk m [] else deliver
            | _ => deliver
            end
          else deliver
      end
  end.

Lemma check_read_sound_ok : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs ->
  read_spec fd buf count i m (Ok eff m' evs).
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_read in H. unfold read_spec.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque ?o) |- _ =>
                cbv beta iota in H;
                eapply bind_ok0; [apply input_ok|]; cbv beta;
                eapply bind_ok0; [apply get_model_ok|]; cbv beta iota;
                srw Hfd; apply check_read_opaque_sound_ok; exact H
            end).
  9:{ (* /dev/null: -EBADF without FMODE_READ, else the range verdict and 0 *)
      destruct rd; cbn [negb] in H; cbv beta iota in H;
        [ unfold check_access_ok_zero in H;
          destruct (access_okb buf (bv_unsigned count)) eqn:Hok | ];
        apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
        (eapply bind_ok0; [apply input_ok|]); cbv beta;
        (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
        srw Hfd; cbn [negb]; cbv beta iota; try rewrite Hok; cbn [negb];
        cbv beta iota; apply pure_ok. }
  9:{ (* /dev/urandom: the range verdict, then [read_urandom] *)
      destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hok.
      { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. apply pure_ok. }
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply check_read_urandom_sound_ok. exact H. }
  - (* channel *)
    destruct (negb (w_is0 ch)) eqn:Hm.
    { (* write-only channel: -EBADF *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hm.
      apply pure_ok. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { (* the range is refused: -EFAULT is the only Ok this branch admits *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hm.
      apply pure_ok. }
    destruct (w_is0 count) eqn:Hc.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hm.
      apply pure_ok.
    + destruct (m_stdin m) as [|b0 s0] eqn:He.
      * apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hm.
        srw He. apply pure_ok.
      * destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
        2: { (* not one byte of the destination can be written: -EFAULT *)
          apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
          eapply bind_ok0; [apply input_ok|]. cbv beta.
          eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
          srw Hfd. srw Hm. srw He. srw Hw1. apply pure_ok. }
        destruct (read_bytes_map (in_wmem i) buf
                    (len_word (fst (stream_take_z (ICons b0 s0) (rw_count_clamp count)))))
          as [wn|] eqn:Hwn; [|discriminate].
        destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs] [|]];
          destruct zs as [|? ?]; destruct us as [|? ?];
          destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
        (* bytes delivered into a writable prefix *)
        destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
                  && (1 <=? Z.of_nat (length bs))%Z
                  && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
                  && listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
                  && wmem_ok i buf (len_word bs)) eqn:Hb;
          [|discriminate].
        inversion H; clear H; subst.
        apply andb_true_iff in Hb as [Hb HW].
        apply andb_true_iff in Hb as [Hb HE].
        apply andb_true_iff in Hb as [Hb HD].
        apply andb_true_iff in Hb as [Hb HC].
        apply andb_true_iff in Hb as [HA HB].
        apply bv_eqb_eq in HA; subst a. apply bv_eqb_eq in HB; subst ret.
        apply Z.leb_le in HC. apply Z.leb_le in HD.
        apply listN_eqb_eq in HE. apply wmem_ok_true in HW.
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hm. srw He. srw Hw1. srw Hwn.
        eapply bind_ok0.
        { apply (choose_ok _ bs). cbv beta. repeat split; assumption. }
        cbv beta.
        eapply bind_ok0; [apply modify_ok|].
        eapply bind_ok_eq; [apply emit_ok|apply pure_ok|].
        now rewrite app_nil_r.
  - (* file *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { (* the range is refused: -EFAULT *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    cbv zeta in H.
    destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs.
    + (* zero-byte read: canonical empty-writes shape *)
      destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H;
        [|rewrite read_bytes_map_nil in Hw; discriminate].
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbs. srw Hw.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H.
      2: { (* the delivered prefix is not fully writable *)
        destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
          [discriminate|].
        (* not even its first byte can land: -EFAULT *)
        apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hfs. srw Hbs. srw Hw. srw Hw1. apply pure_ok. }
      destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs'] [|]];
        destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
      destruct (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                && bv_eqb ret (len_word (b :: bsr))) eqn:Hb; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in Hb as [Hb HC].
      apply andb_true_iff in Hb as [HA HB].
      apply bv_eqb_eq in HA; subst a. apply listN_eqb_eq in HB; subst bs'.
      apply bv_eqb_eq in HC; subst ret.
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbs. srw Hw.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - (* write-only file fd: -EBADF *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
    apply pure_ok.
  - (* append fd: -EBADF for the same reason *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
    apply pure_ok.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { (* the range is refused: -EFAULT *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    cbv zeta in H.
    destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs.
    + (* zero-byte read: canonical empty-writes shape *)
      destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H;
        [|rewrite read_bytes_map_nil in Hw; discriminate].
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbs. srw Hw.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H.
      2: { (* the delivered prefix is not fully writable *)
        destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
          [discriminate|].
        (* not even its first byte can land: -EFAULT *)
        apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hfs. srw Hbs. srw Hw. srw Hw1. apply pure_ok. }
      destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs'] [|]];
        destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
      destruct (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                && bv_eqb ret (len_word (b :: bsr))) eqn:Hb; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in Hb as [Hb HC].
      apply andb_true_iff in Hb as [HA HB].
      apply bv_eqb_eq in HA; subst a. apply listN_eqb_eq in HB; subst bs'.
      apply bv_eqb_eq in HC; subst ret.
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbs. srw Hw.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - (* directory fd: -EFAULT past TASK_SIZE, -EISDIR under it *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn;
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      (eapply bind_ok0; [apply input_ok|]); cbv beta;
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
      apply pure_ok.
  - (* socket *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; [discriminate|].
    destruct (w_is0 count) eqn:Hc.
    { (* [read(fd, buf, 0)] answers 0 on any socket, before the protocol *)
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ]. }
    destruct sk as [| | |peer ch rx|peer ch].
    + (* fresh: never reached TCP_ESTABLISHED, so -ENOTCONN, and nothing
         but the range verdict stands in front of it *)
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ].
    + (* bound: likewise *)
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ].
    + (* listening: likewise *)
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ].
    + (* connected: the answer is the head of what the peer has left *)
      destruct rx as [| | |b0 rx0].
      * (* the peer's FIN, already consumed in sequence: 0, and sticky *)
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ].
      * (* the peer's RST: reported once, and the report consumes it *)
        unfold check_socket_pending_error in H. unfold socket_pending_error.
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
        ok_zero_cases H buf count;
          [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
            eapply bind_ok0; [apply modify_ok|]; apply pure_ok
          | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
            apply pure_ok ].
      * (* the retransmit timer gave up: the same shape, -ETIMEDOUT *)
        unfold check_socket_pending_error in H. unfold socket_pending_error.
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
        ok_zero_cases H buf count;
          [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
            eapply bind_ok0; [apply modify_ok|]; apply pure_ok
          | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
            apply pure_ok ].
      * (* queued bytes: a nonempty prefix lands in a writable prefix *)
        destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
        { (* [vfs_read]'s [access_ok] refuses the named range: -EFAULT *)
          apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
          eapply bind_ok0; [apply input_ok|]. cbv beta.
          eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
          srw Hfd. apply pure_ok. }
        destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
        2: { (* not one byte of the destination can be written: -EFAULT *)
          apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
          eapply bind_ok0; [apply input_ok|]. cbv beta.
          eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
          srw Hfd. srw Hw1. apply pure_ok. }
        destruct (read_bytes_map (in_wmem i) buf
                    (len_word (fst (net_take_z (NCons b0 rx0) (rw_count_clamp count)))))
          as [wn|] eqn:Hwn; [|discriminate].
        destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs] [|]];
          destruct zs as [|? ?]; destruct us as [|? ?];
          destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
        destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
                  && (1 <=? Z.of_nat (length bs))%Z
                  && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
                  && listN_eqb (fst (net_take (NCons b0 rx0) (length bs))) bs
                  && wmem_ok i buf (len_word bs)) eqn:Hb;
          [|discriminate].
        inversion H; clear H; subst.
        apply andb_true_iff in Hb as [Hb HW].
        apply andb_true_iff in Hb as [Hb HE].
        apply andb_true_iff in Hb as [Hb HD].
        apply andb_true_iff in Hb as [Hb HC].
        apply andb_true_iff in Hb as [HA HB].
        apply bv_eqb_eq in HA; subst a. apply bv_eqb_eq in HB; subst ret.
        apply Z.leb_le in HC. apply Z.leb_le in HD.
        apply listN_eqb_eq in HE. apply wmem_ok_true in HW.
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hw1. srw Hwn.
        eapply bind_ok0.
        { apply (choose_ok _ bs). cbv beta. repeat split; assumption. }
        cbv beta.
        eapply bind_ok0; [apply modify_ok|].
        eapply bind_ok_eq; [apply emit_ok|apply pure_ok|].
        now rewrite app_nil_r.
    + (* reset: the error was reported already, so RCV_SHUTDOWN gives 0 *)
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ].
  - (* pipe: -EBADF on the write end, else the queue's head, its
       end-of-file zero, or a destination fault *)
    destruct w.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; [discriminate|].
    destruct (w_is0 count) eqn:Hc.
    { eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ]. }
    destruct (pipe_lookup (m_pipes m) id) as [[q used]|] eqn:Hp; [|discriminate].
    destruct q as [|b bs0].
    { destruct (pipe_end_live (m_fds m) id true) eqn:Hlv; [discriminate|].
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. srw Hp. srw Hlv.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ]. }
    cbv zeta in H.
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_read]'s [access_ok] refuses the named range: -EFAULT *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. srw Hp. apply pure_ok. }
    destruct (read_bytes_map (in_wmem i) buf
                (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))) as [okw|]
      eqn:Hw.
    2:{ destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        [discriminate|].
        apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd. srw Hp. srw Hw. srw Hw1. apply pure_ok. }
    destruct eff as [ret ws zs us cs copyins]; destruct zs as [|? ?];
      destruct us as [|? ?]; destruct cs as [|? ?]; destruct copyins as [|? ?];
      try discriminate.
    destruct (writes_eqb ws
                (delivered_writes buf (pipe_take (b :: bs0) (rw_count_clamp count)))
              && bv_eqb ret
                   (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))) eqn:Hb;
      [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hb as [HA HB].
    apply writes_eqb_eq in HA; subst ws. apply bv_eqb_eq in HB; subst ret.
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota zeta.
    srw Hfd. srw Hp. srw Hw.
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
    apply pure_ok.
Qed.

Lemma check_read_sound_unmodeled : forall i fd buf count eff m,
  check_read i fd buf count eff m = CheckUnmodeled ->
  read_spec fd buf count i m Unmodeled.
Proof.
  intros i fd buf count eff m H.
  unfold check_read in H. unfold read_spec.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque ?o) |- _ =>
                eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
                eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
                srw Hfd; cbv beta iota in H;
                eapply check_read_opaque_sound_unmodeled; exact H
            end).
  9:{ destruct rd; cbn [negb] in H; cbv beta iota in H;
        [ unfold check_access_ok_zero in H;
          destruct (access_okb buf (bv_unsigned count)) | ];
        now apply check_ret_only_no_unmodeled in H. }
  9:{ (* /dev/urandom *)
      destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hok;
        [now apply check_ret_only_no_unmodeled in H|].
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd.
      apply check_read_urandom_sound_unmodeled with (eff := eff). exact H. }
  - (* channel: no fail-closed error remains *)
    destruct (negb (w_is0 ch)) eqn:Hm.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (w_is0 count) eqn:Hc.
    + now apply check_ret_only_no_unmodeled in H.
    + destruct (m_stdin m) as [|b0 s0] eqn:He.
      * now apply check_ret_only_no_unmodeled in H.
      * destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
        -- destruct (read_bytes_map (in_wmem i) buf
                       (len_word (fst (stream_take_z (ICons b0 s0) (rw_count_clamp count)))))
             as [wn|] eqn:Hwn.
           ++ destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs] [|]];
                destruct zs as [|? ?]; destruct us as [|? ?];
                destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
              destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
                        && (1 <=? Z.of_nat (length bs))%Z
                        && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
                        && listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
                        && wmem_ok i buf (len_word bs)); discriminate.
           ++ (* partially writable destination: fail closed *)
              eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
              eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
              srw Hfd. srw Hm. srw He. srw Hw1. srw Hwn. apply unmodeled_intro.
        -- (* not one byte of the destination is writable: -EFAULT, never
              [CheckUnmodeled] *)
           now apply check_ret_only_no_unmodeled in H.
  - destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + cbv zeta in H.
      destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
        as [|b bsr] eqn:Hbs.
      * destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
          as [bs0|] eqn:Hw; cbv beta iota zeta in H.
        -- now apply check_ret_only_no_unmodeled in H.
        -- rewrite read_bytes_map_nil in Hw; discriminate.
      * destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
          as [bs0|] eqn:Hw; cbv beta iota zeta in H.
        -- destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs'] [|]];
             destruct zs as [|? ?]; destruct us as [|? ?];
          destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
           destruct (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                     && bv_eqb ret (len_word (b :: bsr))); discriminate.
        -- destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
           ++ (* partially writable destination: fail closed *)
              eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
              eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
              srw Hfd. srw Hfs. srw Hbs. srw Hw. srw Hw1. apply unmodeled_intro.
           ++ (* nothing writable at all: -EFAULT, never [CheckUnmodeled] *)
              now apply check_ret_only_no_unmodeled in H.
    + eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hfs.
      apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
  - (* append fd: -EBADF, never [CheckUnmodeled] *)
    now apply check_ret_only_no_unmodeled in H.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + cbv zeta in H.
      destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
        as [|b bsr] eqn:Hbs.
      * destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
          as [bs0|] eqn:Hw; cbv beta iota zeta in H.
        -- now apply check_ret_only_no_unmodeled in H.
        -- rewrite read_bytes_map_nil in Hw; discriminate.
      * destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
          as [bs0|] eqn:Hw; cbv beta iota zeta in H.
        -- destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs'] [|]];
             destruct zs as [|? ?]; destruct us as [|? ?];
          destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
           destruct (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                     && bv_eqb ret (len_word (b :: bsr))); discriminate.
        -- destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
           ++ (* partially writable destination: fail closed *)
              eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
              eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
              srw Hfd. srw Hfs. srw Hbs. srw Hw. srw Hw1. apply unmodeled_intro.
           ++ (* nothing writable at all: -EFAULT, never [CheckUnmodeled] *)
              now apply check_ret_only_no_unmodeled in H.
    + eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hfs.
      apply unmodeled_intro.
  - (* directory fd: both arms answer *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn;
      now apply check_ret_only_no_unmodeled in H.
  - (* socket: fail closed only on a count past [rw_bytes_max] and on the
       access_ok gap; every state answers otherwise *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply unmodeled_intro. }
    destruct (w_is0 count) eqn:Hc.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ]. }
    destruct sk as [| | |peer ch rx|peer ch].
    + (* fresh *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ].
    + (* bound *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ].
    + (* listening *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ].
    + (* connected *)
      destruct rx as [| | |b0 rx0].
      * (* FIN *)
        eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ].
      * (* RST *)
        unfold check_socket_pending_error in H. unfold socket_pending_error.
        eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ].
      * (* timed out *)
        unfold check_socket_pending_error in H. unfold socket_pending_error.
        eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ].
      * (* queued bytes: -EFAULT, a delivery, or the partial decline *)
        destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
        { now apply check_ret_only_no_unmodeled in H. }
        destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
        -- destruct (read_bytes_map (in_wmem i) buf
                       (len_word (fst (net_take_z (NCons b0 rx0) (rw_count_clamp count)))))
             as [wn|] eqn:Hwn.
           ++ destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs] [|]];
                destruct zs as [|? ?]; destruct us as [|? ?];
                destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
              destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
                        && (1 <=? Z.of_nat (length bs))%Z
                        && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
                        && listN_eqb (fst (net_take (NCons b0 rx0) (length bs))) bs
                        && wmem_ok i buf (len_word bs)); discriminate.
           ++ eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
              eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
              srw Hfd. srw Hw1. srw Hwn. apply unmodeled_intro.
        -- now apply check_ret_only_no_unmodeled in H.
    + (* reset *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ].
  - (* pipe *)
    destruct w.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply unmodeled_intro. }
    destruct (w_is0 count) eqn:Hc.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ]. }
    destruct (pipe_lookup (m_pipes m) id) as [[q used]|] eqn:Hp.
    2:{ eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd. srw Hp. apply unmodeled_intro. }
    destruct q as [|b bs0].
    { destruct (pipe_end_live (m_fds m) id true) eqn:Hlv.
      { (* empty queue with a live writer: would block, fail closed *)
        eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd. srw Hp. srw Hlv. apply unmodeled_intro. }
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. srw Hp. srw Hlv.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ]. }
    cbv zeta in H.
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (read_bytes_map (in_wmem i) buf
                (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))) as [okw|]
      eqn:Hw.
    + destruct eff as [ret ws zs us cs copyins]; destruct zs as [|? ?];
        destruct us as [|? ?]; destruct cs as [|? ?];
        destruct copyins as [|? ?]; try discriminate.
      destruct (writes_eqb ws
                  (delivered_writes buf (pipe_take (b :: bs0) (rw_count_clamp count)))
                && bv_eqb ret
                     (len_word (pipe_take (b :: bs0) (rw_count_clamp count))));
        discriminate.
    + destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
      * (* partially writable destination: fail closed *)
        eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd. srw Hp. srw Hw. srw Hw1. apply unmodeled_intro.
      * now apply check_ret_only_no_unmodeled in H.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_read_complete_ok : forall i fd buf count eff m m' evs,
  read_spec fd buf count i m (Ok eff m' evs) ->
  check_read i fd buf count eff m = CheckOk m' evs.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold read_spec in H. unfold check_read. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd; hall Hfd; inv_ok.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque ?o) |- _ =>
                cbv beta iota in *;
                apply check_read_opaque_complete_ok; assumption
            end).
  - destruct (negb (w_is0 ch)) eqn:Hm; hall Hm; inv_ok; [reflexivity|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
    { (* the range is refused: -EFAULT *)
      cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok;
      [ cbn; rewrite bv_eqb_refl; reflexivity |].
    destruct (m_stdin m) as [|b0 s0] eqn:He; hall He; inv_ok.
    + (* end of input *) cbn; rewrite bv_eqb_refl; reflexivity.
    + (* bytes branch *)
      destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        hall Hw1; inv_ok.
      2: (* nothing writable: -EFAULT *) reflexivity.
      destruct (read_bytes_map (in_wmem i) buf
                  (len_word (fst (stream_take_z (ICons b0 s0) (rw_count_clamp count)))))
        as [wn|] eqn:Hwn; hall Hwn; inv_ok.
      match goal with
      | Hne : read_bytes_map (in_wmem i) buf (len_word _) <> None |- _ =>
          rewrite (proj2 (wmem_ok_true _ _ _) Hne)
      end.
      match goal with
      | Hst : fst (stream_take _ _) = ?bs |- _ =>
          rewrite (proj2 (listN_eqb_eq _ _) Hst)
      end.
      bool_true. cbn. now rewrite app_nil_r.
  - destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
    { (* the range is refused: -EFAULT *)
      cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    cbv zeta. unfold delivered_writes in *.
    destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; hall Hbs; inv_ok.
    + (* zero-byte read *)
      destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok;
        [ cbn; rewrite bv_eqb_refl; reflexivity
        | rewrite read_bytes_map_nil in Hw; discriminate ].
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok.
      2: { (* the delivered prefix is not fully writable *)
        destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
          hall Hw1; inv_ok.
        (* nothing writable: -EFAULT *) reflexivity. }
      bool_true. rewrite (proj2 (listN_eqb_eq _ _) eq_refl). cbn. reflexivity.
  - inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
  - (* append fd: -EBADF, as for the write-only fd above *)
    inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
    { (* the range is refused: -EFAULT *)
      cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    cbv zeta. unfold delivered_writes in *.
    destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; hall Hbs; inv_ok.
    + (* zero-byte read *)
      destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok;
        [ cbn; rewrite bv_eqb_refl; reflexivity
        | rewrite read_bytes_map_nil in Hw; discriminate ].
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok.
      2: { (* the delivered prefix is not fully writable *)
        destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
          hall Hw1; inv_ok.
        (* nothing writable: -EFAULT *) reflexivity. }
      bool_true. rewrite (proj2 (listN_eqb_eq _ _) eq_refl). cbn. reflexivity.
  - (* directory fd *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      cbn; rewrite bv_eqb_refl; reflexivity.
  - (* socket *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok.
    destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok;
      [ ok_zero_complete buf count |].
    destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *.
    + (* fresh: -ENOTCONN *) ok_zero_complete buf count.
    + (* bound *) ok_zero_complete buf count.
    + (* listening *) ok_zero_complete buf count.
    + (* connected *)
      destruct rx as [| | |b0 rx0]; cbv beta iota zeta in *.
      * (* FIN *) ok_zero_complete buf count.
      * (* RST, consumed by the read that reports it *)
        unfold check_socket_pending_error. unfold socket_pending_error in *.
        ok_zero_complete buf count.
      * (* timed out *)
        unfold check_socket_pending_error. unfold socket_pending_error in *.
        ok_zero_complete buf count.
      * (* queued bytes *)
        inv_ok.
        destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
          inv_ok.
        { (* the named range is refused: -EFAULT *)
          cbn; rewrite bv_eqb_refl; reflexivity. }
        destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
          hall Hw1; inv_ok.
        2: (* nothing writable: -EFAULT *) reflexivity.
        destruct (read_bytes_map (in_wmem i) buf
                    (len_word (fst (net_take_z (NCons b0 rx0) (rw_count_clamp count)))))
          as [wn|] eqn:Hwn; hall Hwn; inv_ok.
        match goal with
        | Hne : read_bytes_map (in_wmem i) buf (len_word _) <> None |- _ =>
            rewrite (proj2 (wmem_ok_true _ _ _) Hne)
        end.
        match goal with
        | Hst : fst (net_take _ _) = ?bs |- _ =>
            rewrite (proj2 (listN_eqb_eq _ _) Hst)
        end.
        bool_true. cbn. now rewrite app_nil_r.
    + (* reset: reads as end-of-stream *)
      ok_zero_complete buf count.
  - (* pipe *)
    destruct w; inv_ok.
    { (* write end: -EBADF *) cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok.
    destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok;
      [ ok_zero_complete buf count |].
    destruct (pipe_lookup (m_pipes m) id) as [[q used]|] eqn:Hp; hall Hp; inv_ok.
    destruct q as [|b bs0]; inv_ok.
    + (* empty queue: end of file, or the would-block decline *)
      destruct (pipe_end_live (m_fds m) id true) eqn:Hlv; hall Hlv; inv_ok.
      ok_zero_complete buf count.
    + cbv zeta.
      destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
        inv_ok.
      { (* the named range is refused: -EFAULT *)
        cbn; rewrite bv_eqb_refl; reflexivity. }
      destruct (read_bytes_map (in_wmem i) buf
                  (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))) as [okw|]
        eqn:Hw; hall Hw; inv_ok.
      2: { destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|]
             eqn:Hw1; hall Hw1; inv_ok. reflexivity. }
      rewrite (proj2 (writes_eqb_eq _ _) eq_refl). cbn.
      rewrite bv_eqb_refl. reflexivity.
  - (* /dev/null *)
    destruct rd; cbn [negb] in *; cbv beta iota in *;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hn; hall Hn;
        cbn [negb] in *; cbv beta iota in * | ];
      inv_ok; unfold check_access_ok_zero; try rewrite Hn;
      cbn; try rewrite bv_eqb_refl; reflexivity.
  - (* /dev/urandom *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
    { cbn; rewrite bv_eqb_refl; reflexivity. }
    cbn [app]. apply check_read_urandom_complete_ok. eassumption.
  - reflexivity.
Qed.

Lemma check_read_complete_unmodeled : forall i fd buf count m eff,
  read_spec fd buf count i m Unmodeled ->
  check_read i fd buf count eff m = CheckUnmodeled.
Proof.
  intros i fd buf count m eff H.
  unfold read_spec in H. unfold check_read. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd; hall Hfd; inv_ok;
    try discriminate.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque ?o) |- _ =>
                cbv beta iota in *;
                apply check_read_opaque_complete_unmodeled; assumption
            end).
  - destruct (negb (w_is0 ch)) eqn:Hm; hall Hm; inv_ok; try discriminate.
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      try discriminate.
    destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok; try discriminate.
    destruct (m_stdin m) as [|b0 s0] eqn:He; hall He; inv_ok; try discriminate.
    destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
      hall Hw1; inv_ok; try discriminate.
    destruct (read_bytes_map (in_wmem i) buf
                (len_word (fst (stream_take_z (ICons b0 s0) (rw_count_clamp count)))))
      as [wn|] eqn:Hwn; hall Hwn; inv_ok; try discriminate; reflexivity.
  - destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      try discriminate.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      try discriminate; [|reflexivity].
    cbv zeta.
    destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; hall Hbs; inv_ok.
    + (* a zero-byte read answers on both sides; only the impossible
         [None] on an empty range is left, and [Hw] refutes it *)
      destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok.
      rewrite read_bytes_map_nil in Hw; discriminate.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok; try discriminate.
      destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        hall Hw1; inv_ok; try discriminate; reflexivity.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      try discriminate.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      try discriminate; [|reflexivity].
    cbv zeta.
    destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; hall Hbs; inv_ok.
    + (* a zero-byte read answers on both sides; only the impossible
         [None] on an empty range is left, and [Hw] refutes it *)
      destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok.
      rewrite read_bytes_map_nil in Hw; discriminate.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok; try discriminate.
      destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        hall Hw1; inv_ok; try discriminate; reflexivity.
  - (* directory fd: both arms answer *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      discriminate.
  - (* socket *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok;
      [reflexivity|].
    destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok;
      [ ok_zero_complete buf count |].
    destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *.
    + ok_zero_complete buf count.
    + ok_zero_complete buf count.
    + ok_zero_complete buf count.
    + destruct rx as [| | |b0 rx0]; cbv beta iota zeta in *.
      * ok_zero_complete buf count.
      * unfold check_socket_pending_error. unfold socket_pending_error in *.
        ok_zero_complete buf count.
      * unfold check_socket_pending_error. unfold socket_pending_error in *.
        ok_zero_complete buf count.
      * (* queued bytes: -EFAULT, a delivery, or the partial decline *)
        inv_ok.
        destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
          inv_ok; try discriminate.
        destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
          hall Hw1; inv_ok; try discriminate.
        destruct (read_bytes_map (in_wmem i) buf
                    (len_word (fst (net_take_z (NCons b0 rx0) (rw_count_clamp count)))))
          as [wn|] eqn:Hwn; hall Hwn; inv_ok; try discriminate; reflexivity.
    + ok_zero_complete buf count.
  - (* pipe *)
    destruct w; inv_ok; try discriminate.
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok;
      [reflexivity|].
    destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok;
      [ ok_zero_complete buf count |].
    destruct (pipe_lookup (m_pipes m) id) as [[q used]|] eqn:Hp; hall Hp; inv_ok;
      try discriminate; [|reflexivity].
    destruct q as [|b bs0]; inv_ok.
    + destruct (pipe_end_live (m_fds m) id true) eqn:Hlv; hall Hlv; inv_ok;
        [reflexivity|].
      ok_zero_complete buf count.
    + cbv zeta.
      destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
        inv_ok; try discriminate.
      destruct (read_bytes_map (in_wmem i) buf
                  (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))) as [okw|]
        eqn:Hw; hall Hw; inv_ok; try discriminate.
      destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        hall Hw1; inv_ok; try discriminate; reflexivity.
  - (* /dev/null *)
    destruct rd; cbn [negb] in *; cbv beta iota in *;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hn; hall Hn;
        cbn [negb] in *; cbv beta iota in * | ];
      inv_ok.
  - (* /dev/urandom *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      try discriminate.
    apply check_read_urandom_complete_unmodeled. eassumption.
Qed.

(* ----------------------------------------------------------------- write *)

Lemma check_write_sound_ok : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs ->
  write_spec fd buf count i m (Ok eff m' evs).
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_write in H.
  unfold write_spec, write_range_gate, write_file_tail, write_fault_keep,
    write_ledger.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque ?o) |- _ =>
                cbv beta iota in H;
                eapply bind_ok0; [apply input_ok|]; cbv beta;
                eapply bind_ok0; [apply get_model_ok|]; cbv beta iota;
                srw Hfd; apply check_write_opaque_sound_ok; exact H
            end).
  9:{ (* /dev/null: -EBADF without FMODE_WRITE, the range gate, the range
         verdict, then the clamped count *)
      destruct wr; cbn [negb] in H; cbv beta iota in H;
        [ destruct (modeled_rw_range buf count) eqn:Hg; cbn [negb] in H;
          cbv beta iota in H;
          [ unfold check_access_ok_zero in H;
            destruct (access_okb buf (bv_unsigned count)) eqn:Hok
          | discriminate ] | ];
        apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
        (eapply bind_ok0; [apply input_ok|]); cbv beta;
        (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
        srw Hfd; cbn [negb]; cbv beta iota; try rewrite Hg; cbn [negb];
        cbv beta iota; unfold access_ok_zero; try rewrite Hok;
        cbv beta iota; apply pure_ok. }
  9:{ (* /dev/urandom: read-only by construction, -EBADF *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply pure_ok. }
  - (* channel *)
    destruct (w_is0 ch) eqn:Hm.
    { (* stdin is read-only: -EBADF *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hm.
      apply pure_ok. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; [discriminate|].
    destruct (w_is0 count) eqn:Hc.
    { (* count = 0: return 0 where the range verdict allows it, -EFAULT
         where it does not *)
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hm.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ]. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_write]'s [access_ok] refuses the named range: -EFAULT *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hm.
      apply pure_ok. }
    destruct (negb (m_channel_reader m)) eqn:Hcr; cbv beta iota in H.
    { (* the far end has no reader, past [access_ok]: -EPIPE and signal 13 *)
      unfold check_sigpipe_write in H.
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hm. srw Hcr.
      unfold sigpipe_write. eapply bind_ok0; [apply modify_ok|].
      apply pure_ok. }
    cbv zeta in H.
    destruct (Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + (* EFAULT *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hm.
      srw Hcr. srw Hg.
      apply pure_ok.
    + (* short or full delivery, picked by the claimed return *)
      destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
        destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; try discriminate.
      destruct ((1 <=? bv_unsigned ret)%Z
                && (bv_unsigned ret
                    <=? Z.of_nat (length (write_source (in_mem i) buf count)))%Z)
        eqn:Hb; [|discriminate].
      destruct (access_ranges_eqb copyins [(buf, Z.to_nat (bv_unsigned ret))])
        eqn:Hreads; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in Hb as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2.
      apply access_ranges_eqb_eq in Hreads. subst copyins.
      pose proof (write_source_length_le (in_mem i) buf count) as Hcnt.
      pose proof (word_unsigned_range ret) as Hr.
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hm.
      srw Hcr.
      set (bs := write_source (in_mem i) buf count) in *.
      srw Hg.
      set (ds := firstn (Z.to_nat (bv_unsigned ret)) bs) in *.
      assert (Hlen : Z.of_nat (length ds) = bv_unsigned ret)
        by (apply firstn_length_le_Z; lia).
      assert (Hlw : len_word ds = ret).
      { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
      eapply bind_ok0.
      { apply (choose_ok _ ds). cbv beta. repeat split; [lia|lia|].
        assert (Hlnat : length ds = Z.to_nat (bv_unsigned ret)) by lia.
        rewrite Hlnat. reflexivity. }
      cbv beta. rewrite <- Hlw.
      eapply bind_ok_eq; [apply emit_ok| |].
      { replace (Z.to_nat (bv_unsigned (len_word ds))) with (length ds)
          by (rewrite Hlw, <- Hlen; lia).
        eapply (record_copyins_ok [(buf, length ds)]
          (ret_only (len_word ds)) i m'
          (mkEffect (len_word ds) [] []) m' []).
        apply pure_ok. }
      now rewrite app_nil_r.
  - (* read-only file fd: -EBADF *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
    apply pure_ok.
  - (* write-only file *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; [discriminate|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_write]'s [access_ok] refuses the named range: -EFAULT *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    cbv zeta in H.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + (* the faulting source: -EFAULT over the file it still extends *)
      unfold check_write_fault_extend in H.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        [discriminate|].
      apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hg.
      unfold write_fault_extend. srw Hfs. srw Hz.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hg.
      destruct (w_is0 count).
      2: { destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
           destruct (negb (modeled_file_gap data off
                             (write_source (in_mem i) buf count))) eqn:Hk;
             [discriminate|].
           apply check_ret_only_copyins_ok_iff in H.
           destruct H as (-> & -> & ->).
           cbv beta iota zeta.
           eapply bind_ok0; [apply modify_ok|].
           eapply bind_ok0; [apply modify_ok|].
           apply record_copyins_ok. apply pure_ok. }
      ok_zero_cases H buf count;
        [ destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate];
          destruct (negb (modeled_file_gap data off
                            (write_source (in_mem i) buf count))) eqn:Hk;
            [discriminate|];
          apply check_ret_only_ok_iff in H;
          destruct H as (-> & -> & ->);
          cbv beta iota zeta;
          eapply bind_ok0; [apply modify_ok|];
          eapply bind_ok0; [apply modify_ok|];
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ].
  - (* append fd: the same, minus the zero-fill guard and plus
       [rw_verify_area]'s -EINVAL *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; [discriminate|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (rw_pos_einvalb off (bv_unsigned count)) eqn:Hpos.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hpos. apply pure_ok. }
    cbv zeta in H.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hpos. srw Hg. apply pure_ok.
    + eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hpos. srw Hg.
      destruct (w_is0 count).
      2: { destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
           apply check_ret_only_copyins_ok_iff in H.
           destruct H as (-> & -> & ->).
           cbv beta iota zeta.
           eapply bind_ok0; [apply modify_ok|].
           eapply bind_ok0; [apply modify_ok|].
           apply record_copyins_ok. apply pure_ok. }
      ok_zero_cases H buf count;
        [ destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate];
          apply check_ret_only_ok_iff in H;
          destruct H as (-> & -> & ->);
          cbv beta iota zeta;
          eapply bind_ok0; [apply modify_ok|];
          eapply bind_ok0; [apply modify_ok|];
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ].
  - (* the same file opened O_RDWR: the write-only bullet above *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; [discriminate|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_write]'s [access_ok] refuses the named range: -EFAULT *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    cbv zeta in H.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + (* the faulting source: the [FdFileW] branch above *)
      unfold check_write_fault_extend in H.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        [discriminate|].
      apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hg.
      unfold write_fault_extend. srw Hfs. srw Hz.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hg.
      destruct (w_is0 count).
      2: { destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
           destruct (negb (modeled_file_gap data off
                             (write_source (in_mem i) buf count))) eqn:Hk;
             [discriminate|].
           apply check_ret_only_copyins_ok_iff in H.
           destruct H as (-> & -> & ->).
           cbv beta iota zeta.
           eapply bind_ok0; [apply modify_ok|].
           eapply bind_ok0; [apply modify_ok|].
           apply record_copyins_ok. apply pure_ok. }
      ok_zero_cases H buf count;
        [ destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate];
          destruct (negb (modeled_file_gap data off
                            (write_source (in_mem i) buf count))) eqn:Hk;
            [discriminate|];
          apply check_ret_only_ok_iff in H;
          destruct H as (-> & -> & ->);
          cbv beta iota zeta;
          eapply bind_ok0; [apply modify_ok|];
          eapply bind_ok0; [apply modify_ok|];
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ].
  - (* directory fd: -EBADF *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok.
  - (* socket: a delivering write and a count the model does not judge are
       [CheckUnmodeled]; a socket with no connection answers -EFAULT past
       [access_ok], else -EPIPE and signal 13 *)
    destruct (negb (sock_send_dead sk)) eqn:Hsd; [discriminate|].
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; [discriminate|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hok;
      cbv beta iota in H; [|unfold check_sigpipe_write in H];
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      (eapply bind_ok0; [apply input_ok|]); cbv beta;
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; srw Hsd.
    + apply pure_ok.
    + unfold sigpipe_write. eapply bind_ok0; [apply modify_ok|].
      apply pure_ok.
  - (* pipe: the read end's -EBADF, and the write end's answers *)
    destruct w.
    2:{ (* read end is O_RDONLY: -EBADF, before the source buffer *)
        apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
        apply pure_ok. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; [discriminate|].
    destruct (w_is0 count) eqn:Hc.
    { (* "Null write succeeds": 0 where the range verdict allows it *)
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      ok_zero_cases H buf count;
        [ apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok
        | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
          apply pure_ok ]. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_write]'s [access_ok] refuses the named range: -EFAULT, ahead
         of the readers test *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (negb (pipe_end_live (m_fds m) id false)) eqn:Hl.
    { (* no reader left, past [access_ok]: -EPIPE and signal 13 *)
      cbv beta iota in H. unfold check_sigpipe_write in H.
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      srw Hl. unfold sigpipe_write.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok. }
    (* the three declines below are [CheckUnmodeled], so none of them
       reaches a [CheckOk] and each closes by discrimination *)
    destruct (pipe_lookup (m_pipes m) id) as [st|] eqn:Hp; [|discriminate].
    destruct (negb (pipe_write_room st (bv_unsigned count))) eqn:Hroom;
      [discriminate|].
    cbv zeta in H.
    destruct (negb (Nat.eqb (length (write_source (in_mem i) buf count))
                      (word_to_nat count))) eqn:Hfull; [discriminate|].
    (* the page the empty pipe's write must allocate: the injected
       -ENOMEM stands beside the delivery, so the acceptor takes
       either *)
    destruct (pipe_needs_page st) eqn:Hpg.
    { destruct eff as [ret ws zs us cs copyins].
      destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; destruct copyins as [|? ?];
        try (apply check_ret_only_copyins_ok_iff in H;
             destruct H as (-> & -> & ->);
             eapply bind_ok0; [apply input_ok|]; cbv beta;
             eapply bind_ok0; [apply get_model_ok|]; cbv beta iota; srw Hfd;
             srw Hl; srw Hp; srw Hroom; srw Hfull; srw Hpg;
             apply alt_r;
             eapply bind_ok0; [apply modify_ok|];
             apply record_copyins_ok; apply pure_ok).
      destruct (errno_ret_in write_errnos ret) eqn:He.
      - inversion H; clear H; subst.
        apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
        srw Hl. srw Hp. srw Hroom. srw Hfull. srw Hpg.
        apply alt_l. eapply bind_ok0; [apply (choose_ok _ e), HIn|].
        cbv beta. apply pure_ok.
      - apply check_ret_only_copyins_ok_iff in H.
        destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
        srw Hl. srw Hp. srw Hroom. srw Hfull. srw Hpg.
        apply alt_r.
        eapply bind_ok0; [apply modify_ok|].
        apply record_copyins_ok. apply pure_ok. }
    apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
    srw Hl. srw Hp. srw Hroom. srw Hfull. srw Hpg.
    eapply bind_ok0; [apply modify_ok|].
    apply record_copyins_ok. apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok.
Qed.

Lemma check_write_sound_unmodeled : forall i fd buf count eff m,
  check_write i fd buf count eff m = CheckUnmodeled ->
  write_spec fd buf count i m Unmodeled.
Proof.
  intros i fd buf count eff m H.
  unfold check_write in H. unfold write_spec, write_range_gate,
    write_file_tail, write_fault_keep, write_ledger.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque ?o) |- _ =>
                eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
                eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
                srw Hfd; cbv beta iota in H;
                eapply check_write_opaque_sound_unmodeled; exact H
            end).
  9:{ destruct wr; cbn [negb] in H; cbv beta iota in H;
        [ destruct (modeled_rw_range buf count) eqn:Hg; cbn [negb] in H;
          cbv beta iota in H;
          [ unfold check_access_ok_zero in H;
            destruct (access_okb buf (bv_unsigned count));
            now apply check_ret_only_no_unmodeled in H | ]
        | now apply check_ret_only_no_unmodeled in H ].
      (eapply bind_unmodeled2; [apply input_ok|]); cbv beta.
      (eapply bind_unmodeled2; [apply get_model_ok|]); cbv beta iota.
      srw Hfd. cbn [negb]. cbv beta iota. try rewrite Hg. cbn [negb]. cbv beta iota.
      apply unmodeled_intro. }
  9:{ now apply check_ret_only_no_unmodeled in H. }
  - destruct (w_is0 ch) eqn:Hm.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { (* count past [rw_bytes_max]: fail closed *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hm. apply unmodeled_intro. }
    destruct (w_is0 count).
    { (* count = 0: the range verdict answers either way, so no
         [Unmodeled] is left on this branch *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hm.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ]. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (negb (m_channel_reader m)); cbv beta iota in H.
    { (* the far end has no reader: -EPIPE, never a decline *)
      unfold check_sigpipe_write in H.
      now apply check_ret_only_no_unmodeled in H. }
    cbv zeta in H.
    destruct (Nat.eqb (length (write_source (in_mem i) buf count)) 0).
    { now apply check_ret_only_no_unmodeled in H. }
    destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
      destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
    destruct ((1 <=? bv_unsigned ret)%Z
              && (bv_unsigned ret
                  <=? Z.of_nat (length (write_source (in_mem i) buf count)))%Z);
      [destruct (access_ranges_eqb _ _)|]; discriminate.
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { (* count past [rw_bytes_max]: fail closed *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply unmodeled_intro. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { now apply check_ret_only_no_unmodeled in H. }
    cbv zeta in H.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + (* the faulting source: an answer unless the hole is too large *)
      unfold check_write_fault_extend in H.
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hg. unfold write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
        [ destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
          [ apply unmodeled_intro
          | now apply check_ret_only_copyins_no_unmodeled in H ]
        | apply unmodeled_intro ].
    + eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hg.
      destruct (w_is0 count);
        [ ok_zero_cases H buf count;
          [ | now apply check_ret_only_no_unmodeled in H ]
        | ].
      (* both branches end in the same file analysis: the hole past
         end-of-file is the only fail-closed answer left *)
      all: (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
            [ destruct (negb (modeled_file_gap data off
                                (write_source (in_mem i) buf count))) eqn:Hk;
              [ apply unmodeled_intro
              | first
                  [ now apply check_ret_only_no_unmodeled in H
                  | now apply check_ret_only_copyins_no_unmodeled in H ] ]
            | apply unmodeled_intro ]).
  - (* append fd: the same, with only the missing-key decline left *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply unmodeled_intro. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (rw_pos_einvalb off (bv_unsigned count)) eqn:Hpos.
    { now apply check_ret_only_no_unmodeled in H. }
    cbv zeta in H.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + now apply check_ret_only_no_unmodeled in H.
    + eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hpos. srw Hg.
      destruct (w_is0 count);
        [ ok_zero_cases H buf count;
          [ | now apply check_ret_only_no_unmodeled in H ]
        | ].
      all: (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
            [ first
                [ now apply check_ret_only_no_unmodeled in H
                | now apply check_ret_only_copyins_no_unmodeled in H ]
            | apply unmodeled_intro ]).
  - (* the same file opened O_RDWR: the write-only bullet above *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { (* count past [rw_bytes_max]: fail closed *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply unmodeled_intro. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { now apply check_ret_only_no_unmodeled in H. }
    cbv zeta in H.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + (* the faulting source: the [FdFileW] branch above *)
      unfold check_write_fault_extend in H.
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hg. unfold write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
        [ destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
          [ apply unmodeled_intro
          | now apply check_ret_only_copyins_no_unmodeled in H ]
        | apply unmodeled_intro ].
    + eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hg.
      destruct (w_is0 count);
        [ ok_zero_cases H buf count;
          [ | now apply check_ret_only_no_unmodeled in H ]
        | ].
      (* both branches end in the same file analysis: the hole past
         end-of-file is the only fail-closed answer left *)
      all: (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
            [ destruct (negb (modeled_file_gap data off
                                (write_source (in_mem i) buf count))) eqn:Hk;
              [ apply unmodeled_intro
              | first
                  [ now apply check_ret_only_no_unmodeled in H
                  | now apply check_ret_only_copyins_no_unmodeled in H ] ]
            | apply unmodeled_intro ]).
  - now apply check_ret_only_no_unmodeled in H.
  - (* socket: a delivering write, and a count the model does not judge;
       a socket with no connection is answered, never declined *)
    destruct (negb (sock_send_dead sk)) eqn:Hsd; cbv beta iota in H.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      srw Hsd. apply unmodeled_intro. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; cbv beta iota in H.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      srw Hsd. apply unmodeled_intro. }
    destruct (negb (access_okb buf (bv_unsigned count)));
      cbv beta iota in H; [|unfold check_sigpipe_write in H];
      now apply check_ret_only_no_unmodeled in H.
  - (* pipe: the write end's four fail-closed verdicts -- an unevaluable
       count, a missing table entry, a write needing a second ring slot,
       and a source not wholly readable -- and no other decline; the read
       end's -EBADF is not one, and neither is the no-reader -EPIPE *)
    destruct w.
    2:{ now apply check_ret_only_no_unmodeled in H. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply unmodeled_intro. }
    destruct (w_is0 count) eqn:Hc.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd.
      ok_zero_cases H buf count;
        [ now apply check_ret_only_no_unmodeled in H
        | now apply check_ret_only_no_unmodeled in H ]. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (negb (pipe_end_live (m_fds m) id false)) eqn:Hrd.
    { (* no reader left: -EPIPE and signal 13, never a decline *)
      cbv beta iota in H. unfold check_sigpipe_write in H.
      now apply check_ret_only_no_unmodeled in H. }
    destruct (pipe_lookup (m_pipes m) id) as [st|] eqn:Hp.
    2:{ eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd. srw Hrd. srw Hp. apply unmodeled_intro. }
    destruct (negb (pipe_write_room st (bv_unsigned count))) eqn:Hroom.
    { (* the write needs a second ring slot: fail closed *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. srw Hrd. srw Hp. srw Hroom. apply unmodeled_intro. }
    cbv zeta in H.
    destruct (negb (Nat.eqb (length (write_source (in_mem i) buf count))
                      (word_to_nat count))) eqn:Hsrc.
    { (* the source is not wholly readable: fail closed *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. srw Hrd. srw Hp. srw Hroom. srw Hsrc. apply unmodeled_intro. }
    destruct (pipe_needs_page st) eqn:Hpg;
      [ destruct eff as [ret ws zs us cs copyins];
        destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; destruct copyins as [|? ?];
        try (now apply check_ret_only_copyins_no_unmodeled in H);
        destruct (errno_ret_in write_errnos ret);
        [ discriminate | now apply check_ret_only_copyins_no_unmodeled in H ]
      | now apply check_ret_only_copyins_no_unmodeled in H ].
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_write_complete_ok : forall i fd buf count eff m m' evs,
  write_spec fd buf count i m (Ok eff m' evs) ->
  check_write i fd buf count eff m = CheckOk m' evs.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold write_spec, write_range_gate, write_file_tail, write_fault_keep,
    write_ledger, sigpipe_write in H.
  unfold check_write. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd; hall Hfd; inv_ok.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque ?o) |- _ =>
                cbv beta iota in *;
                apply check_write_opaque_complete_ok; assumption
            end).
  - destruct (w_is0 ch) eqn:Hm; hall Hm; inv_ok;
      [cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity|].
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok.
    destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok;
      [ok_zero_complete buf count|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak; inv_ok.
    { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
    destruct (negb (m_channel_reader m)) eqn:Hrdr; hall Hrdr; inv_ok.
    { (* the far end has no reader, past [access_ok]: -EPIPE and signal 13 *)
      try unfold check_sigpipe_write;
        cbn; try rewrite bv_eqb_refl; reflexivity. }
    cbv zeta.
    destruct (Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg; hall Hg; inv_ok.
    + (* -EFAULT *)
      cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
    + (* the environment's delivered prefix, replayed through the guard *)
      cbn.
      pose proof (word_unsigned_range count) as Hcr.
      unfold rw_count_clamp in *.
      pose proof (f_equal (@length _) H5) as Hfl.
      rewrite length_firstn in Hfl.
      assert (Hsm : (Z.of_nat (length x3) < two_pow_64)%Z) by lia.
      rewrite (len_word_unsigned x3 Hsm).
      assert (Hnat : Z.to_nat (Z.of_nat (length x3)) = length x3) by lia.
      rewrite Hnat, <- H5.
      bool_true.
      cbn. rewrite Nat.eqb_refl. cbn. now rewrite app_nil_r.
  - cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
  - destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok.
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak; inv_ok.
    { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
    cbv zeta.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg; hall Hg; inv_ok.
    + (* the faulting source, over the file it still extends *)
      unfold write_fault_extend in *; cbv beta iota zeta in *.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        hall Hz; inv_ok.
      sys_unfold; inv_ok.
      unfold check_write_fault_extend. rewrite Hfs, Hz.
      unfold check_ret_only_copyins, check_ret_only, clear_copyins; cbn;
        rewrite ?bv_eqb_refl, ?Nat.eqb_refl; reflexivity.
    + destruct (w_is0 count); [ok_zero_split buf count|].
      (* [count = 0] past [TASK_SIZE]: -EFAULT, with no file to look at *)
      2: { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
      all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
      all: destruct (negb (modeled_file_gap data off
                             (write_source (in_mem i) buf count))) eqn:Hk;
           hall Hk; inv_ok.
      all: unfold check_ret_only_copyins, check_ret_only, clear_copyins; cbn;
        rewrite ?bv_eqb_refl, ?Nat.eqb_refl; reflexivity.
  - (* append fd: the arm above with no zero-fill guard to replay *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok.
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak; inv_ok.
    { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
    destruct (rw_pos_einvalb off (bv_unsigned count)) eqn:Hpos; hall Hpos; inv_ok.
    { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
    cbv zeta.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg; hall Hg; inv_ok.
    + cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
    + destruct (w_is0 count); [ok_zero_split buf count|].
      2: { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
      all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
      all: unfold check_ret_only_copyins, check_ret_only, clear_copyins; cbn;
        rewrite ?bv_eqb_refl, ?Nat.eqb_refl; reflexivity.
  - (* the same file opened O_RDWR: the write-only bullet above *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok.
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak; inv_ok.
    { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
    cbv zeta.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg; hall Hg; inv_ok.
    + (* the faulting source: the [FdFileW] branch above *)
      unfold write_fault_extend in *; cbv beta iota zeta in *.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        hall Hz; inv_ok.
      sys_unfold; inv_ok.
      unfold check_write_fault_extend. rewrite Hfs, Hz.
      unfold check_ret_only_copyins, check_ret_only, clear_copyins; cbn;
        rewrite ?bv_eqb_refl, ?Nat.eqb_refl; reflexivity.
    + destruct (w_is0 count); [ok_zero_split buf count|].
      (* [count = 0] past [TASK_SIZE]: -EFAULT, with no file to look at *)
      2: { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
      all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
      all: destruct (negb (modeled_file_gap data off
                             (write_source (in_mem i) buf count))) eqn:Hk;
           hall Hk; inv_ok.
      all: unfold check_ret_only_copyins, check_ret_only, clear_copyins; cbn;
        rewrite ?bv_eqb_refl, ?Nat.eqb_refl; reflexivity.
  - cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
  - (* socket with no connection: -EFAULT past [access_ok], else -EPIPE
       and signal 13; every other socket write declines, so [inv_ok]
       closes it against an [Ok] hypothesis *)
    destruct (negb (sock_send_dead sk)) eqn:Hsd; hall Hsd; inv_ok.
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok.
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hok;
      hall Hok; inv_ok; try unfold check_sigpipe_write;
      cbn; try rewrite bv_eqb_refl; reflexivity.
  - (* pipe: the write end's 0 at a zero count, its -EPIPE with signal 13
       when no reader is left, and its deterministic full write; the read
       end's -EBADF.  Every other arm is a decline, so [inv_ok] closes it
       against an [Ok] hypothesis *)
    destruct w; cbn [negb] in *; cbv beta iota zeta in *; inv_ok.
    { destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok.
      destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok;
        [ok_zero_complete buf count|].
      destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
        inv_ok.
      { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
      destruct (negb (pipe_end_live (m_fds m) id false)) eqn:Hrd;
        hall Hrd; inv_ok;
        [unfold check_sigpipe_write; cbn; try rewrite bv_eqb_refl;
         reflexivity|].
      destruct (pipe_lookup (m_pipes m) id) as [st|] eqn:Hp; hall Hp; inv_ok.
      destruct (negb (pipe_write_room st (bv_unsigned count))) eqn:Hroom;
        hall Hroom; inv_ok.
      cbv zeta.
      destruct (negb (Nat.eqb (length (write_source (in_mem i) buf count))
                        (word_to_nat count))) eqn:Hsrc; hall Hsrc; inv_ok.
      (* [write_errnos] IS UNFOLDED BEFORE [inv_ok] runs, for the reason
         [check_getdents64_complete_ok] gives: [errno_from]'s [choose]
         leaves [In e write_errnos] with [e] still a variable, and
         [inv_ok] matches [_ \/ _] syntactically *)
      destruct (pipe_needs_page st) eqn:Hpg; hall Hpg;
        unfold write_errnos in *; cbn [In] in *; inv_ok;
        try contradiction;
        unfold check_ret_only_copyins, check_ret_only, clear_copyins; cbn;
        rewrite ?bv_eqb_refl, ?Nat.eqb_refl; reflexivity. }
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
  - (* /dev/null *)
    destruct wr; cbn [negb] in *; cbv beta iota in *;
      [ destruct (modeled_rw_range buf count) eqn:Hg; hall Hg;
        cbn [negb] in *; cbv beta iota in *;
        [ unfold access_ok_zero in *; sys_unfold;
          destruct (access_okb buf (bv_unsigned count)) eqn:Hn; hall Hn;
          cbn [negb] in *; cbv beta iota in * | ] | ];
      inv_ok; unfold check_access_ok_zero; try rewrite Hn;
      cbn; try rewrite bv_eqb_refl; reflexivity.
  - (* /dev/urandom: -EBADF *)
    inv_ok; cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
  - cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_write_complete_unmodeled : forall i fd buf count m eff,
  write_spec fd buf count i m Unmodeled ->
  check_write i fd buf count eff m = CheckUnmodeled.
Proof.
  intros i fd buf count m eff H.
  unfold write_spec, write_range_gate, write_file_tail, write_fault_keep,
    write_ledger, sigpipe_write in H.
  unfold check_write. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd; hall Hfd; inv_ok;
    try discriminate.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque ?o) |- _ =>
                cbv beta iota in *;
                apply check_write_opaque_complete_unmodeled; assumption
            end).
  - destruct (w_is0 ch) eqn:Hm; hall Hm; inv_ok; try discriminate.
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok;
      [reflexivity|].
    destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok;
      [ok_zero_complete buf count|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
      inv_ok; try discriminate.
    (* the far end has no reader, past [access_ok]: -EPIPE with signal 13,
       an [Ok] the [Unmodeled] hypothesis refutes *)
    destruct (negb (m_channel_reader m)) eqn:Hcr; hall Hcr; inv_ok.
    cbv zeta.
    destruct (Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg; hall Hg; inv_ok; discriminate.
  - destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok;
      [reflexivity|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
      inv_ok; try discriminate.
    cbv zeta.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg; hall Hg; inv_ok.
    { (* the faulting source declines only on the hole it will not build *)
      unfold write_fault_extend in *; cbv beta iota zeta in *.
      unfold check_write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
        try discriminate; [|reflexivity].
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        hall Hz; inv_ok; try discriminate; [reflexivity|];
        sys_unfold; inv_ok. }
    destruct (w_is0 count); [ok_zero_split buf count|].
    all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
         try discriminate; try reflexivity.
    all: destruct (negb (modeled_file_gap data off
                           (write_source (in_mem i) buf count))) eqn:Hk;
         hall Hk; inv_ok; try discriminate.
    all: reflexivity.
  - (* append fd: the only decline left is the missing key *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok;
      [reflexivity|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
      inv_ok; try discriminate.
    destruct (rw_pos_einvalb off (bv_unsigned count)) eqn:Hpos; hall Hpos;
      inv_ok; try discriminate.
    cbv zeta.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg; hall Hg; inv_ok; try discriminate.
    destruct (w_is0 count); [ok_zero_split buf count|].
    all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
         try discriminate; try reflexivity.
  - (* the same file opened O_RDWR: the write-only bullet above *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok;
      [reflexivity|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
      inv_ok; try discriminate.
    cbv zeta.
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg; hall Hg; inv_ok.
    { (* the faulting source: the [FdFileW] branch above *)
      unfold write_fault_extend in *; cbv beta iota zeta in *.
      unfold check_write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
        try discriminate; [|reflexivity].
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        hall Hz; inv_ok; try discriminate; [reflexivity|];
        sys_unfold; inv_ok. }
    destruct (w_is0 count); [ok_zero_split buf count|].
    all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
         try discriminate; try reflexivity.
    all: destruct (negb (modeled_file_gap data off
                           (write_source (in_mem i) buf count))) eqn:Hk;
         hall Hk; inv_ok; try discriminate.
    all: reflexivity.
  - (* socket: a delivering write, or a count the model does not judge;
       a socket with no connection is answered on both sides *)
    destruct (negb (sock_send_dead sk)) eqn:Hsd; hall Hsd; inv_ok;
      [reflexivity|].
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok;
      [reflexivity|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hok;
      hall Hok; inv_ok.
  - (* pipe *)
    destruct w; cbn [negb] in *; cbv beta iota zeta in *; inv_ok;
      try discriminate.
    destruct (negb (modeled_rw_range buf count)) eqn:Hn; hall Hn; inv_ok;
      [reflexivity|].
    destruct (w_is0 count) eqn:Hc; hall Hc; inv_ok;
      [ok_zero_complete buf count|].
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak; hall Hak;
      inv_ok; try discriminate.
    (* no reader left is -EPIPE with signal 13, an [Ok] the [Unmodeled]
       hypothesis refutes *)
    destruct (negb (pipe_end_live (m_fds m) id false)) eqn:Hrd; hall Hrd; inv_ok.
    destruct (pipe_lookup (m_pipes m) id) as [st|] eqn:Hp; hall Hp; inv_ok;
      [|reflexivity].
    destruct (negb (pipe_write_room st (bv_unsigned count))) eqn:Hroom;
      hall Hroom; inv_ok; [reflexivity|].
    cbv zeta.
    destruct (negb (Nat.eqb (length (write_source (in_mem i) buf count))
                      (word_to_nat count))) eqn:Hsrc; hall Hsrc; inv_ok;
      [reflexivity|].
    destruct (pipe_needs_page st) eqn:Hpg; hall Hpg;
      unfold write_errnos in *; cbn [In] in *; inv_ok; try discriminate;
      try contradiction.
  - (* /dev/null *)
    destruct wr; cbn [negb] in *; cbv beta iota in *;
      [ destruct (modeled_rw_range buf count) eqn:Hg; hall Hg;
        cbn [negb] in *; cbv beta iota in *;
        [ unfold access_ok_zero in *; sys_unfold;
          destruct (access_okb buf (bv_unsigned count)) eqn:Hn; hall Hn;
          cbn [negb] in *; cbv beta iota in * | ] | ];
      inv_ok; reflexivity.
Qed.

(* ---------------------------------------------------------------- writev *)

(** The pread64 (67) and pwrite64 (68) acceptors.  Each mirrors its spec
    arm for arm, including the two tests [ksys_pread64] and
    [ksys_pwrite64] make ahead of [vfs_read] / [vfs_write] — the negative
    position and the [FMODE_PREAD] / [FMODE_PWRITE] gate — so the ORDER
    the spec's header argues for is the order this decides in too. *)

Definition check_pread64 (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if ppos_einvalb pos then check_ret_only eff (errno_ret EINVAL) m []
  else
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) => check_ret_only eff (errno_ret ESPIPE) m []
  | Some (FdPipe _ _) => check_ret_only eff (errno_ret ESPIPE) m []
  | Some (FdSocket _) => check_ret_only eff (errno_ret ESPIPE) m []
  | Some (FdFileW _ _) => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdFileA _ _) => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdDevNull rd _) =>
      if negb rd then check_ret_only eff (errno_ret EBADF) m []
      else if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count)
      then check_ret_only eff (errno_ret EINVAL) m []
      else check_ret_only eff (Z_to_bv 64 0) m []
  | Some (FdOpaque _) => CheckUnmodeled
  | Some FdUrandom =>
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count)
      then check_ret_only eff (errno_ret EINVAL) m []
      else check_read_urandom i buf count eff m
  | Some FdDir =>
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count)
      then check_ret_only eff (errno_ret EINVAL) m []
      else check_ret_only eff (errno_ret EISDIR) m []
  | Some (FdFile p _) | Some (FdFileRW p _) =>
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      match fs_lookup (m_fs m) p with
      | None => CheckUnmodeled
      | Some data =>
          let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count)) in
          match read_bytes_map (in_wmem i) buf (len_word bs) with
          | None =>
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => check_ret_only eff (errno_ret EFAULT) m []
              | Some _ => CheckUnmodeled   (* partially writable: fail closed *)
              end
          | Some _ =>
              (* the model does not move: a pread advances no offset *)
              match bs, eff with
              | [], _ => check_ret_only eff (Z_to_bv 64 0) m []
              | _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
                  if bv_eqb a buf && listN_eqb bs' bs
                     && bv_eqb ret (len_word bs)
                  then CheckOk m []
                  else CheckReject
              | _, _ => CheckReject
              end
          end
      end
  end.

Definition check_pwrite64 (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if ppos_einvalb pos then check_ret_only eff (errno_ret EINVAL) m []
  else
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) => check_ret_only eff (errno_ret ESPIPE) m []
  | Some (FdPipe _ _) => check_ret_only eff (errno_ret ESPIPE) m []
  | Some (FdSocket _) => check_ret_only eff (errno_ret ESPIPE) m []
  | Some (FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | Some FdDir => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdFileA _ _) => CheckUnmodeled   (* see [ReadWrite.pwrite64_spec] *)
  | Some FdUrandom => check_ret_only eff (errno_ret EBADF) m []   (* read-only *)
  | Some (FdOpaque _) => CheckUnmodeled
  | Some (FdDevNull _ wr) =>
      if negb wr then check_ret_only eff (errno_ret EBADF) m []
      else if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count)
      then check_ret_only eff (errno_ret EINVAL) m []
      else check_ret_only eff (Z_to_bv 64 (rw_count_clamp count)) m []
  | Some (FdFileW p _) | Some (FdFileRW p _) =>
      if negb (access_okb buf (bv_unsigned count))
      then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      let bs := write_source (in_mem i) buf count in
        (* no count gate: see [ReadWrite.pwrite64_spec] *)
      if negb (w_is0 count) && Nat.eqb (length bs) 0
      then check_write_fault_extend [] m p pos eff
      else
      match fs_lookup (m_fs m) p with
      | None => CheckUnmodeled
      | Some data =>
          if negb (modeled_file_gap data pos bs) then CheckUnmodeled
          else
          let m' := with_fs (fs_set (m_fs m) p (file_write data pos bs)) m in
          if w_is0 count
          then check_ret_only eff (len_word bs) m' []
          else check_ret_only_copyins [(buf, length bs)] eff (len_word bs) m' []
      end
  end.

Lemma check_pread64_sound_ok : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs ->
  pread64_spec fd buf count pos i m (Ok eff m' evs).
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pread64 in H. unfold pread64_spec.
  destruct (ppos_einvalb pos) eqn:Hpos.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ => discriminate
            end).
  - (* channel: no FMODE_PREAD *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok.
  - (* readable file *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    cbv zeta in H.
    destruct (file_read data pos (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H;
        [|rewrite read_bytes_map_nil in Hw; discriminate].
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbs. srw Hw. apply pure_ok.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H.
      2: { destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
             [discriminate|].
           apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
           eapply bind_ok0; [apply input_ok|]. cbv beta.
           eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
           srw Hfd. srw Hfs. srw Hbs. srw Hw. srw Hw1. apply pure_ok. }
      destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs'] [|]];
        destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
      destruct (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                && bv_eqb ret (len_word (b :: bsr))) eqn:Hb; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in Hb as [Hb HC].
      apply andb_true_iff in Hb as [HA HB].
      apply bv_eqb_eq in HA; subst a. apply listN_eqb_eq in HB; subst bs'.
      apply bv_eqb_eq in HC; subst ret.
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbs. srw Hw. apply pure_ok.
  - (* write-only file fd: [vfs_read]'s -EBADF *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok.
  - (* append fd: the same -EBADF, from the same FMODE_READ test *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok.
  - (* the same file opened O_RDWR: the readable-file bullet above *)
    (* readable file *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    cbv zeta in H.
    destruct (file_read data pos (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H;
        [|rewrite read_bytes_map_nil in Hw; discriminate].
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbs. srw Hw. apply pure_ok.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H.
      2: { destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
             [discriminate|].
           apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
           eapply bind_ok0; [apply input_ok|]. cbv beta.
           eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
           srw Hfd. srw Hfs. srw Hbs. srw Hw. srw Hw1. apply pure_ok. }
      destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs'] [|]];
        destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
      destruct (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                && bv_eqb ret (len_word (b :: bsr))) eqn:Hb; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in Hb as [Hb HC].
      apply andb_true_iff in Hb as [HA HB].
      apply bv_eqb_eq in HA; subst a. apply listN_eqb_eq in HB; subst bs'.
      apply bv_eqb_eq in HC; subst ret.
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbs. srw Hw. apply pure_ok.
  - (* directory: -EFAULT, -EINVAL and -EISDIR, in that order *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn;
      [ | destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv ];
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      (eapply bind_ok0; [apply input_ok|]); cbv beta;
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
      apply pure_ok.
  - (* socket *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok.
  - (* either pipe end *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok.
  - (* /dev/null *)
    destruct rd; cbn [negb] in H; cbv beta iota in H;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hok; cbn [negb] in H;
        cbv beta iota in H;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv | ] | ];
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      (eapply bind_ok0; [apply input_ok|]); cbv beta;
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; cbn [negb]; cbv beta iota; try rewrite Hok; cbn [negb];
      cbv beta iota; try rewrite Hrv; cbv beta iota; apply pure_ok.
  - (* /dev/urandom *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hok.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply pure_ok. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply pure_ok. }
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply check_read_urandom_sound_ok. exact H.
  - (* no such descriptor *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok.
Qed.

Lemma check_pread64_sound_unmodeled : forall i fd buf count pos eff m,
  check_pread64 i fd buf count pos eff m = CheckUnmodeled ->
  pread64_spec fd buf count pos i m Unmodeled.
Proof.
  intros i fd buf count pos eff m H.
  unfold check_pread64 in H. unfold pread64_spec.
  destruct (ppos_einvalb pos) eqn:Hpos.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd;
    try (now apply check_ret_only_no_unmodeled in H).
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ =>
                eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
                eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
                srw Hfd; apply unmodeled_intro
            end).
  - (* readable file: the two declines *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    2: { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
         eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
         srw Hfd. srw Hfs. apply unmodeled_intro. }
    cbv zeta in H.
    destruct (file_read data pos (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H;
        [now apply check_ret_only_no_unmodeled in H|].
      rewrite read_bytes_map_nil in Hw; discriminate.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H.
      * destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs'] [|]];
          destruct zs as [|? ?]; destruct us as [|? ?];
          destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
        destruct (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                  && bv_eqb ret (len_word (b :: bsr))); discriminate.
      * destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
          [|now apply check_ret_only_no_unmodeled in H].
        eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hfs. srw Hbs. srw Hw. srw Hw1.
        apply unmodeled_intro.
  - (* the same file opened O_RDWR: the readable-file bullet above *)
    (* readable file: the two declines *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    2: { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
         eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
         srw Hfd. srw Hfs. apply unmodeled_intro. }
    cbv zeta in H.
    destruct (file_read data pos (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H;
        [now apply check_ret_only_no_unmodeled in H|].
      rewrite read_bytes_map_nil in Hw; discriminate.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; cbv beta iota zeta in H.
      * destruct eff as [ret ws zs us cs copyins]; destruct ws as [|[a bs'] [|]];
          destruct zs as [|? ?]; destruct us as [|? ?];
          destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
        destruct (bv_eqb a buf && listN_eqb bs' (b :: bsr)
                  && bv_eqb ret (len_word (b :: bsr))); discriminate.
      * destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
          [|now apply check_ret_only_no_unmodeled in H].
        eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hfs. srw Hbs. srw Hw. srw Hw1.
        apply unmodeled_intro.
  - (* directory: three errno answers, no decline *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv;
      now apply check_ret_only_no_unmodeled in H.
  - (* /dev/null *)
    destruct rd; cbn [negb] in H; cbv beta iota in H;
      [ destruct (access_okb buf (bv_unsigned count)); cbn [negb] in H;
        cbv beta iota in H;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) | ] | ];
      now apply check_ret_only_no_unmodeled in H.
  - (* /dev/urandom *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hok;
      [now apply check_ret_only_no_unmodeled in H|].
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv;
      [now apply check_ret_only_no_unmodeled in H|].
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd.
    apply check_read_urandom_sound_unmodeled with (eff := eff). exact H.
Qed.

Lemma check_pread64_complete_ok : forall i fd buf count pos eff m m' evs,
  pread64_spec fd buf count pos i m (Ok eff m' evs) ->
  check_pread64 i fd buf count pos eff m = CheckOk m' evs.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold pread64_spec in H. unfold check_pread64. sys_unfold.
  destruct (ppos_einvalb pos) eqn:Hpos.
  { cbv iota in H. inv_ok. cbn; rewrite bv_eqb_refl; reflexivity. }
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd;
    hall Hfd; inv_ok;
    try (cbn; rewrite bv_eqb_refl; reflexivity).
  - (* readable file *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
    { cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok.
    { cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    cbv zeta. unfold delivered_writes in *.
    destruct (file_read data pos (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; hall Hbs; inv_ok.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok;
        [ cbn; rewrite bv_eqb_refl; reflexivity
        | rewrite read_bytes_map_nil in Hw; discriminate ].
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok.
      2: { destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
             hall Hw1; inv_ok. reflexivity. }
      bool_true. rewrite (proj2 (listN_eqb_eq _ _) eq_refl). cbn. reflexivity.
  - (* the same file opened O_RDWR: the readable-file bullet above *)
    (* readable file *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
    { cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok.
    { cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    cbv zeta. unfold delivered_writes in *.
    destruct (file_read data pos (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; hall Hbs; inv_ok.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok;
        [ cbn; rewrite bv_eqb_refl; reflexivity
        | rewrite read_bytes_map_nil in Hw; discriminate ].
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok.
      2: { destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
             hall Hw1; inv_ok. reflexivity. }
      bool_true. rewrite (proj2 (listN_eqb_eq _ _) eq_refl). cbn. reflexivity.
  - (* directory *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
    { cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok;
      cbn; rewrite bv_eqb_refl; reflexivity.
  - (* /dev/null *)
    destruct rd; cbn [negb] in *; cbv beta iota in *;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hn; hall Hn;
        cbn [negb] in *; cbv beta iota in *;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv | ] | ];
      inv_ok; cbn; try rewrite bv_eqb_refl; reflexivity.
  - (* /dev/urandom *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
    { cbn; rewrite bv_eqb_refl; reflexivity. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok.
    { cbn; rewrite bv_eqb_refl; reflexivity. }
    cbn [app]. apply check_read_urandom_complete_ok. eassumption.
Qed.

Lemma check_pread64_complete_unmodeled : forall i fd buf count pos m eff,
  pread64_spec fd buf count pos i m Unmodeled ->
  check_pread64 i fd buf count pos eff m = CheckUnmodeled.
Proof.
  intros i fd buf count pos m eff H.
  unfold pread64_spec in H. unfold check_pread64. sys_unfold.
  destruct (ppos_einvalb pos) eqn:Hpos; [cbv iota in H; inv_ok|].
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd;
    hall Hfd; inv_ok; try discriminate.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ => reflexivity
            end).
  - destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      try discriminate.
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok;
      try discriminate.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      [|reflexivity].
    cbv zeta in *.
    destruct (file_read data pos (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; hall Hbs; inv_ok.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok; discriminate.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok; try discriminate.
      destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        hall Hw1; inv_ok; try discriminate; reflexivity.
  - (* the same file opened O_RDWR: the readable-file bullet above *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      try discriminate.
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok;
      try discriminate.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      [|reflexivity].
    cbv zeta in *.
    destruct (file_read data pos (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; hall Hbs; inv_ok.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok; discriminate.
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)))
        as [bs0|] eqn:Hw; hall Hw; inv_ok; try discriminate.
      destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        hall Hw1; inv_ok; try discriminate; reflexivity.
  - destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      try discriminate.
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok;
      discriminate.
  - (* /dev/null *)
    destruct rd; cbn [negb] in *; cbv beta iota in *;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hn; hall Hn;
        cbn [negb] in *; cbv beta iota in *;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv | ] | ];
      inv_ok.
  - (* /dev/urandom *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
      try discriminate.
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok;
      try discriminate.
    apply check_read_urandom_complete_unmodeled. eassumption.
Qed.

Lemma check_pwrite64_sound_ok : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs ->
  pwrite64_spec fd buf count pos i m (Ok eff m' evs).
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pwrite64 in H. unfold pwrite64_spec.
  destruct (ppos_einvalb pos) eqn:Hpos.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd;
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         eapply bind_ok0; [apply input_ok|]; cbv beta;
         (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
         apply pure_ok).
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ => discriminate
            end).
  (* Three goals survive that: the write-only file arm and the O_RDWR
     one, which both transfer, and the APPEND arm, whose checker is
     [CheckUnmodeled] and so never equals a [CheckOk] -- see
     [ReadWrite.pwrite64_spec].  The first two are ONE SCRIPT run twice:
     a positional write reads no [f_pos], so nothing on this path tells
     the two kinds apart. *)
  2: discriminate.
  1: {
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok. }
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok. }
  cbv zeta in H.
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg.
  { (* the faulting source: -EFAULT over the file it still extends *)
    unfold check_write_fault_extend in H.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
      [discriminate|].
    apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hg. unfold write_fault_extend. srw Hfs. srw Hz.
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk;
    [discriminate|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
  srw Hfd. srw Hg. srw Hfs. srw Hk.
  destruct (w_is0 count).
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    cbv beta iota zeta.
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    cbv beta iota zeta.
    eapply bind_ok0; [apply modify_ok|].
    apply record_copyins_ok. apply pure_ok.
  }
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok. }
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. apply pure_ok. }
  cbv zeta in H.
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg.
  { (* the faulting source: the branch above, on the O_RDWR kind *)
    unfold check_write_fault_extend in H.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
      [discriminate|].
    apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hg. unfold write_fault_extend. srw Hfs. srw Hz.
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk;
    [discriminate|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
  srw Hfd. srw Hg. srw Hfs. srw Hk.
  destruct (w_is0 count).
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    cbv beta iota zeta.
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    cbv beta iota zeta.
    eapply bind_ok0; [apply modify_ok|].
    apply record_copyins_ok. apply pure_ok.
  - (* /dev/null *)
    destruct wr; cbn [negb] in H; cbv beta iota in H;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hok; cbn [negb] in H;
        cbv beta iota in H;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv | ] | ];
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      (eapply bind_ok0; [apply input_ok|]); cbv beta;
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; cbn [negb]; cbv beta iota; try rewrite Hok; cbn [negb];
      cbv beta iota; try rewrite Hrv; cbv beta iota; apply pure_ok.
Qed.

Lemma check_pwrite64_sound_unmodeled : forall i fd buf count pos eff m,
  check_pwrite64 i fd buf count pos eff m = CheckUnmodeled ->
  pwrite64_spec fd buf count pos i m Unmodeled.
Proof.
  intros i fd buf count pos eff m H.
  unfold check_pwrite64 in H. unfold pwrite64_spec.
  destruct (ppos_einvalb pos) eqn:Hpos.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd;
    try (now apply check_ret_only_no_unmodeled in H).
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ =>
                eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
                eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
                srw Hfd; apply unmodeled_intro
            end).
  (* the APPEND arm declines on both sides, for the reason
     [ReadWrite.pwrite64_spec] gives: the position pwrite64 named is
     discarded and the bytes land at end of file *)
  2: { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
       eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
       srw Hfd. apply unmodeled_intro. }
  (* the write-only arm and the O_RDWR one are one script, run twice *)
  1: {
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
  { now apply check_ret_only_no_unmodeled in H. }
  cbv zeta in H.
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg.
  { (* the faulting source answers unless the hole is too large *)
    unfold check_write_fault_extend in H.
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hg. unfold write_fault_extend.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
      [ destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
        [ apply unmodeled_intro
        | now apply check_ret_only_copyins_no_unmodeled in H ]
      | apply unmodeled_intro ]. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
  2: { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
       eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
       srw Hfd. srw Hg. srw Hfs. apply unmodeled_intro. }
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hg. srw Hfs. srw Hk.
    apply unmodeled_intro. }
  destruct (w_is0 count).
  - now apply check_ret_only_no_unmodeled in H.
  - now apply check_ret_only_copyins_no_unmodeled in H.
  }
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
  { now apply check_ret_only_no_unmodeled in H. }
  cbv zeta in H.
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg.
  { (* the faulting source: the branch above, on the O_RDWR kind *)
    unfold check_write_fault_extend in H.
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hg. unfold write_fault_extend.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
      [ destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
        [ apply unmodeled_intro
        | now apply check_ret_only_copyins_no_unmodeled in H ]
      | apply unmodeled_intro ]. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
  2: { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
       eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
       srw Hfd. srw Hg. srw Hfs. apply unmodeled_intro. }
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hg. srw Hfs. srw Hk.
    apply unmodeled_intro. }
  destruct (w_is0 count).
  - now apply check_ret_only_no_unmodeled in H.
  - now apply check_ret_only_copyins_no_unmodeled in H.
  - (* /dev/null *)
    destruct wr; cbn [negb] in H; cbv beta iota in H;
      [ destruct (access_okb buf (bv_unsigned count)); cbn [negb] in H;
        cbv beta iota in H;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) | ] | ];
      now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_pwrite64_complete_ok : forall i fd buf count pos eff m m' evs,
  pwrite64_spec fd buf count pos i m (Ok eff m' evs) ->
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold pwrite64_spec in H. unfold check_pwrite64. sys_unfold.
  destruct (ppos_einvalb pos) eqn:Hpos.
  { cbv iota in H. inv_ok. cbn; rewrite bv_eqb_refl; reflexivity. }
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd;
    hall Hfd; inv_ok;
    try (cbn; rewrite bv_eqb_refl; reflexivity).
  (* Two goals survive: the write-only file arm and the O_RDWR one.
     They are one script run twice -- a positional write reads no
     [f_pos], so the two kinds are indistinguishable here. *)
  1: {
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
  { cbn; rewrite bv_eqb_refl; reflexivity. }
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok.
  { cbn; rewrite bv_eqb_refl; reflexivity. }
  cbv zeta in *.
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg;
    hall Hg; inv_ok.
  { (* the faulting source, over the file it still extends *)
    unfold write_fault_extend in *; cbv beta iota zeta in *.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
      hall Hz; inv_ok.
    sys_unfold; inv_ok.
    unfold check_write_fault_extend. rewrite Hfs, Hz.
    apply check_ret_only_copyins_ok_iff. repeat split; reflexivity. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk;
    hall Hk; inv_ok.
  destruct (w_is0 count); inv_ok.
  - cbn; rewrite bv_eqb_refl; reflexivity.
  - apply check_ret_only_copyins_ok_iff. repeat split; reflexivity.
  }
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok.
  { cbn; rewrite bv_eqb_refl; reflexivity. }
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok.
  { cbn; rewrite bv_eqb_refl; reflexivity. }
  cbv zeta in *.
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg;
    hall Hg; inv_ok.
  { (* the faulting source: the branch above, on the O_RDWR kind *)
    unfold write_fault_extend in *; cbv beta iota zeta in *.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
      hall Hz; inv_ok.
    sys_unfold; inv_ok.
    unfold check_write_fault_extend. rewrite Hfs, Hz.
    apply check_ret_only_copyins_ok_iff. repeat split; reflexivity. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk;
    hall Hk; inv_ok.
  destruct (w_is0 count); inv_ok.
  - cbn; rewrite bv_eqb_refl; reflexivity.
  - apply check_ret_only_copyins_ok_iff. repeat split; reflexivity.
  - (* /dev/null *)
    destruct wr; cbn [negb] in *; cbv beta iota in *;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hn; hall Hn;
        cbn [negb] in *; cbv beta iota in *;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv | ] | ];
      inv_ok; cbn; try rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_pwrite64_complete_unmodeled : forall i fd buf count pos m eff,
  pwrite64_spec fd buf count pos i m Unmodeled ->
  check_pwrite64 i fd buf count pos eff m = CheckUnmodeled.
Proof.
  intros i fd buf count pos m eff H.
  unfold pwrite64_spec in H. unfold check_pwrite64. sys_unfold.
  destruct (ppos_einvalb pos) eqn:Hpos; [cbv iota in H; inv_ok|].
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd;
    hall Hfd; inv_ok; try discriminate.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ => reflexivity
            end).
  (* three goals survive: the write-only file arm, the APPEND arm where
     both sides decline outright, and the O_RDWR arm, which is the
     write-only script run again *)
  2: reflexivity.
  1: {
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
    try discriminate.
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok;
    try discriminate.
  cbv zeta in *.
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg;
    hall Hg; inv_ok.
  { (* the faulting source declines only on the hole it will not build *)
    unfold write_fault_extend in *; cbv beta iota zeta in *.
    unfold check_write_fault_extend.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      try discriminate; [|reflexivity].
    destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
      hall Hz; inv_ok; try discriminate; [reflexivity|];
      sys_unfold; inv_ok. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
    [|reflexivity].
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk;
    hall Hk; inv_ok; [reflexivity|].
  destruct (w_is0 count); inv_ok; discriminate.
  }
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn; hall Hn; inv_ok;
    try discriminate.
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv; inv_ok;
    try discriminate.
  cbv zeta in *.
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg;
    hall Hg; inv_ok.
  { (* the faulting source: the branch above, on the O_RDWR kind *)
    unfold write_fault_extend in *; cbv beta iota zeta in *.
    unfold check_write_fault_extend.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      try discriminate; [|reflexivity].
    destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
      hall Hz; inv_ok; try discriminate; [reflexivity|];
      sys_unfold; inv_ok. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
    [|reflexivity].
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk;
    hall Hk; inv_ok; [reflexivity|].
  destruct (w_is0 count); inv_ok; discriminate.
  - (* /dev/null *)
    destruct wr; cbn [negb] in *; cbv beta iota in *;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hn; hall Hn;
        cbn [negb] in *; cbv beta iota in *;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv; hall Hrv | ] | ];
      inv_ok.
Qed.

(** The vectored form of [check_sigpipe_write]: the same -EPIPE over the
    same [ReadWrite.raise_sigpipe] model, with the iovec array's import
    in the ledger, because [do_writev] imports the array before
    [vfs_writev] reaches the far end -- see [ReadWrite.writev_spec]'s
    channel arm. *)
Definition check_sigpipe_writev (reads : list (word * nat))
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_ret_only_copyins reads eff (errno_ret EPIPE) (raise_sigpipe m) [].

Definition check_writev (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | Some FdDir => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdSocket _) => CheckUnmodeled
  | Some (FdChannel ch) =>
      if w_is0 ch then check_ret_only eff (errno_ret EBADF) m []
      else
        match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
        | ImpFault => check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
        | ImpInval => check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
        | ImpOk iovs0 =>
            let total := iovs_total (cap_iovecs iovs0) in
            let bs := writev_gathered (in_mem i) iovs0 in
            if Z.eqb total 0
            then check_ret_only_copyins
              (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
              eff (Z_to_bv 64 0) m []
            else if negb (m_channel_reader m)
            then check_sigpipe_writev
              (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)) eff m
              (* the far end has no reader: -EPIPE and signal 13, after
                 the zero-aggregate answer as on [check_write] *)
            else if Nat.eqb (length bs) 0
            then check_ret_only_copyins
              (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
              eff (errno_ret EFAULT) m []
            else if addr_is_error_b (len_word bs) then CheckUnmodeled
            else
              (* as for [check_write]: the claimed return picks the
                 delivered (possibly short) prefix; an error-encoded
                 return is never a delivered length *)
              match eff with
              | mkEffectU ret [] [] [] [] copyins =>
                  if (1 <=? bv_unsigned ret)%Z
                     && (bv_unsigned ret <=? Z.of_nat (length bs))%Z
                     && negb (addr_is_error_b ret)
                  then
                    (* a nested [if] rather than a fourth [&&]: [vm_compute]
                       evaluates every operand of [andb], and this operand
                       converts [ret] to a unary numeral -- bounded by
                       [length bs] once the range test has passed, and by
                       nothing for an errno-encoded return *)
                    if access_ranges_eqb copyins
                         (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) ++
                          iov_prefix_accesses (cap_iovecs iovs0)
                            (Z.to_nat (bv_unsigned ret)))
                    then CheckOk m (map (WriteEv ch)
                                      (firstn (Z.to_nat (bv_unsigned ret)) bs))
                    else CheckReject
                  else CheckReject
              | _ => CheckReject
              end
        end
  | Some (FdFileW p off) =>
      match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
      | ImpFault => check_ret_only_copyins
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
          eff (errno_ret EFAULT) m []
      | ImpInval => check_ret_only_copyins
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
          eff (errno_ret EINVAL) m []
      | ImpOk iovs0 =>
          let total := iovs_total (cap_iovecs iovs0) in
          let bs := writev_gathered (in_mem i) iovs0 in
          if Z.eqb total 0
          then check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (Z_to_bv 64 0) m []
          else if rw_pos_einvalb off total
          then check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
          else if Nat.eqb (length bs) 0
          then check_write_fault_extend
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            m p off eff
          else
            match fs_lookup (m_fs m) p with
            | None => CheckUnmodeled
            | Some data =>
                if negb (modeled_file_gap data off bs) then CheckUnmodeled
                else if addr_is_error_b (len_word bs) then CheckUnmodeled
                else check_ret_only_copyins
                  (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) ++
                   iov_prefix_accesses (cap_iovecs iovs0) (length bs))
                  eff (len_word bs)
                  (with_fds (fd_insert (m_fds m) fd
                               (FdFileW p (off + len_word bs)))
                     (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                  []
            end
      end
  | Some (FdFileRW p off) =>   (* the [FdFileW] arm above, on the O_RDWR kind *)
      match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
      | ImpFault => check_ret_only_copyins
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
          eff (errno_ret EFAULT) m []
      | ImpInval => check_ret_only_copyins
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
          eff (errno_ret EINVAL) m []
      | ImpOk iovs0 =>
          let total := iovs_total (cap_iovecs iovs0) in
          let bs := writev_gathered (in_mem i) iovs0 in
          if Z.eqb total 0
          then check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (Z_to_bv 64 0) m []
          else if rw_pos_einvalb off total
          then check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
          else if Nat.eqb (length bs) 0
          then check_write_fault_extend
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            m p off eff
          else
            match fs_lookup (m_fs m) p with
            | None => CheckUnmodeled
            | Some data =>
                if negb (modeled_file_gap data off bs) then CheckUnmodeled
                else if addr_is_error_b (len_word bs) then CheckUnmodeled
                else check_ret_only_copyins
                  (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) ++
                   iov_prefix_accesses (cap_iovecs iovs0) (length bs))
                  eff (len_word bs)
                  (with_fds (fd_insert (m_fds m) fd
                               (FdFileRW p (off + len_word bs)))
                     (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                  []
            end
      end
  | Some (FdFileA p off) =>
      (* [rw_pos_einvalb] still reads [off], the fd's real position; only
         the destination moves.  See [ReadWrite.writev_spec]'s
         [FdFileA] arm *)
      match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
      | ImpFault => check_ret_only_copyins
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
          eff (errno_ret EFAULT) m []
      | ImpInval => check_ret_only_copyins
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
          eff (errno_ret EINVAL) m []
      | ImpOk iovs0 =>
          let total := iovs_total (cap_iovecs iovs0) in
          let bs := writev_gathered (in_mem i) iovs0 in
          if Z.eqb total 0
          then check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (Z_to_bv 64 0) m []
          else if rw_pos_einvalb off total
          then check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
          else if Nat.eqb (length bs) 0
          then check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
          else
            match fs_lookup (m_fs m) p with
            | None => CheckUnmodeled
            | Some data =>
                if addr_is_error_b (len_word bs) then CheckUnmodeled
                else check_ret_only_copyins
                  (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) ++
                   iov_prefix_accesses (cap_iovecs iovs0) (length bs))
                  eff (len_word bs)
                  (with_fds (fd_insert (m_fds m) fd
                               (FdFileA p (append_new_pos data bs off)))
                     (with_fs (fs_set (m_fs m) p
                                 (file_write data (len_word data) bs)) m))
                  []
            end
      end
  | Some (FdPipe _ w) =>
      if negb w then check_ret_only eff (errno_ret EBADF) m []   (* read end: -EBADF *)
      else
        match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
        | ImpFault => check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
        | ImpInval => check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
        | ImpOk iovs0 =>
            if Z.eqb (iovs_total (cap_iovecs iovs0)) 0
            then check_ret_only_copyins
              (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
              eff (Z_to_bv 64 0) m []
            else CheckUnmodeled   (* vectored pipe writes are unmodeled *)
        end
  | Some FdUrandom => check_ret_only eff (errno_ret EBADF) m []   (* read-only *)
  | Some (FdOpaque _) => CheckUnmodeled
  | Some (FdDevNull _ wr) =>
      if negb wr then check_ret_only eff (errno_ret EBADF) m []
      else
        match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
        | ImpFault => check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EFAULT) m []
        | ImpInval => check_ret_only_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            eff (errno_ret EINVAL) m []
        | ImpOk iovs0 =>
            check_ret_only_copyins
              (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
              eff (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) m []
              (* [write_iter_null]: the capped aggregate, the iovec array
                 the only copy-in *)
        end
  end.

(* The proofs below open every spec bind with the same two steps and
   close every errno arm with [check_ret_only_copyins_ok_iff]; the
   [Ltac] pair keeps that from being repeated arm by arm. *)
Local Ltac wv_open Hfd :=
  eapply bind_ok0; [apply input_ok|]; cbv beta;
  eapply bind_ok0; [apply get_model_ok|]; cbv beta iota; srw Hfd.

Local Ltac wv_errno H :=
  apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->).

Lemma check_writev_sound_ok : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs ->
  writev_spec fd iov iovcnt i m (Ok eff m' evs).
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_writev in H. unfold writev_spec, writev_file_arm,
    write_fault_keep, writev_ledger.
  unfold writev_gathered in H |- *.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ => discriminate
            end).
  9:{ (* /dev/null: -EBADF without FMODE_WRITE, else the import's answer *)
      destruct wr.
      2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
          wv_open Hfd. apply pure_ok. }
      cbn [negb] in H |- *. cbv iota in H |- *.
      destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
        (wv_errno H; wv_open Hfd; srw Hiv; cbn [with_copyins];
         apply record_copyins_ok_empty; [reflexivity|apply pure_ok]). }
  9:{ (* /dev/urandom: -EBADF *)
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      wv_open Hfd. apply pure_ok. }
  - (* channel *)
    destruct (w_is0 ch) eqn:Hm.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      wv_open Hfd. srw Hm. apply pure_ok. }
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wv_errno H. wv_open Hfd. srw Hm. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    2:{ wv_errno H. wv_open Hfd. srw Hm. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    cbv zeta in H.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { wv_errno H. wv_open Hfd. srw Hm. srw Hiv. srw Htot.
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (negb (m_channel_reader m)) eqn:Hrdr; cbv beta iota in H.
    { (* no reader on the far end: -EPIPE and signal 13, the import in
         the ledger *)
      unfold check_sigpipe_writev in H.
      wv_errno H. wv_open Hfd. srw Hm. srw Hiv. srw Htot. srw Hrdr.
      apply record_copyins_ok_empty; [reflexivity|].
      unfold sigpipe_write. eapply bind_ok0; [apply modify_ok|]. apply pure_ok. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { wv_errno H. wv_open Hfd. srw Hm. srw Hiv. srw Htot. srw Hrdr. srw Ht.
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))))
      eqn:Hae; [discriminate|].
    destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
      destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
    destruct ((1 <=? bv_unsigned ret)%Z
              && (bv_unsigned ret
                  <=? Z.of_nat (length (gather_prefix (in_mem i) (cap_iovecs iovs))))%Z
              && negb (addr_is_error_b ret)) eqn:Hb; [|discriminate].
    destruct (access_ranges_eqb copyins
                (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) ++
                 iov_prefix_accesses (cap_iovecs iovs)
                   (Z.to_nat (bv_unsigned ret)))) eqn:Hreads; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hb as [Hb Hne].
    apply andb_true_iff in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    apply negb_true_iff in Hne.
    apply access_ranges_eqb_eq in Hreads. subst copyins.
    pose proof (word_unsigned_range ret) as Hr.
    wv_open Hfd. srw Hm. srw Hiv.
    set (bs := gather_prefix (in_mem i) (cap_iovecs iovs)) in *.
    srw Htot. srw Hrdr. srw Ht. srw Hae.
    set (ds := firstn (Z.to_nat (bv_unsigned ret)) bs) in *.
    assert (Hlen : Z.of_nat (length ds) = bv_unsigned ret)
      by (apply firstn_length_le_Z; lia).
    assert (Hlw : len_word ds = ret).
    { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
    replace (Z.to_nat (bv_unsigned ret)) with (length ds) by lia.
    rewrite <- Hlw.
    eapply record_copyins_ok with
      (eff := with_copyins
        (iov_prefix_accesses (cap_iovecs iovs) (length ds))
        (mkEffect (len_word ds) [] [])).
    eapply bind_ok0.
    { apply (choose_ok _ ds). cbv beta.
      repeat split; [lia|lia|rewrite Hlw; exact Hne|].
      assert (Hlnat : length ds = Z.to_nat (bv_unsigned ret)) by lia.
      rewrite Hlnat. reflexivity. }
    cbv beta.
    eapply bind_ok_eq; [apply emit_ok| |].
    { replace (Z.to_nat (bv_unsigned (len_word ds))) with (length ds)
        by (rewrite Hlw, <- Hlen; lia).
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    now rewrite app_nil_r.
  - (* read-only file fd: -EBADF *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    wv_open Hfd. apply pure_ok.
  - (* write-only file *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wv_errno H. wv_open Hfd. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    2:{ wv_errno H. wv_open Hfd. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    cbv zeta in H.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { wv_errno H. wv_open Hfd. srw Hiv. srw Htot.
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
    { wv_errno H. wv_open Hfd. srw Hiv. srw Htot. srw Hpos.
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { (* the faulting source: -EFAULT over the file it still extends *)
      unfold check_write_fault_extend in H.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        [discriminate|].
      wv_errno H. wv_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
      unfold write_fault_extend. srw Hfs. srw Hz.
      apply record_copyins_ok_empty; [reflexivity|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    destruct (negb (modeled_file_gap data off
                      (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk;
      [discriminate|].
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))))
      eqn:Hae; [discriminate|].
    wv_errno H. wv_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
    srw Hfs. srw Hk. srw Hae.
    eapply record_copyins_ok with
      (eff := with_copyins
        (iov_prefix_accesses (cap_iovecs iovs)
           (length (gather_prefix (in_mem i) (cap_iovecs iovs))))
        (mkEffect
          (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))) [] [])).
    eapply bind_ok0; [apply modify_ok|].
    eapply bind_ok0; [apply modify_ok|].
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
  - (* append fd: the arm above, minus the zero-fill guard *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wv_errno H. wv_open Hfd. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    2:{ wv_errno H. wv_open Hfd. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    cbv zeta in H.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { wv_errno H. wv_open Hfd. srw Hiv. srw Htot.
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
    { wv_errno H. wv_open Hfd. srw Hiv. srw Htot. srw Hpos.
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { wv_errno H. wv_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))))
      eqn:Hae; [discriminate|].
    wv_errno H. wv_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
    srw Hfs. srw Hae.
    eapply record_copyins_ok with
      (eff := with_copyins
        (iov_prefix_accesses (cap_iovecs iovs)
           (length (gather_prefix (in_mem i) (cap_iovecs iovs))))
        (mkEffect
          (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))) [] [])).
    eapply bind_ok0; [apply modify_ok|].
    eapply bind_ok0; [apply modify_ok|].
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
  - (* the same file opened O_RDWR: the write-only bullet above *)
    (* write-only file *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wv_errno H. wv_open Hfd. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    2:{ wv_errno H. wv_open Hfd. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    cbv zeta in H.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { wv_errno H. wv_open Hfd. srw Hiv. srw Htot.
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
    { wv_errno H. wv_open Hfd. srw Hiv. srw Htot. srw Hpos.
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { (* the faulting source: the [FdFileW] branch above *)
      unfold check_write_fault_extend in H.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        [discriminate|].
      wv_errno H. wv_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
      unfold write_fault_extend. srw Hfs. srw Hz.
      apply record_copyins_ok_empty; [reflexivity|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    destruct (negb (modeled_file_gap data off
                      (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk;
      [discriminate|].
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))))
      eqn:Hae; [discriminate|].
    wv_errno H. wv_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
    srw Hfs. srw Hk. srw Hae.
    eapply record_copyins_ok with
      (eff := with_copyins
        (iov_prefix_accesses (cap_iovecs iovs)
           (length (gather_prefix (in_mem i) (cap_iovecs iovs))))
        (mkEffect
          (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))) [] [])).
    eapply bind_ok0; [apply modify_ok|].
    eapply bind_ok0; [apply modify_ok|].
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
  - (* directory fd: -EBADF *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    wv_open Hfd. apply pure_ok.
  - (* socket: the gap declines, so the checker never says [CheckOk] *)
    discriminate.
  - (* pipe *)
    destruct w.
    2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        wv_open Hfd. apply pure_ok. }
    cbn [negb] in H |- *. cbv iota in H |- *.
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wv_errno H. wv_open Hfd. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    2:{ wv_errno H. wv_open Hfd. srw Hiv. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; [|discriminate].
    wv_errno H. wv_open Hfd. srw Hiv. srw Htot.
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    wv_open Hfd. apply pure_ok.
Qed.

Local Ltac wv_open_unmodeled Hfd :=
  eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
  eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota; srw Hfd.

Lemma check_writev_sound_unmodeled : forall i fd iov iovcnt eff m,
  check_writev i fd iov iovcnt eff m = CheckUnmodeled ->
  writev_spec fd iov iovcnt i m Unmodeled.
Proof.
  intros i fd iov iovcnt eff m H.
  unfold check_writev in H. unfold writev_spec, writev_file_arm,
    write_fault_keep, writev_ledger.
  unfold writev_gathered in H |- *.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ =>
                eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
                eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
                srw Hfd; apply unmodeled_intro
            end).
  9:{ destruct wr.
      2:{ now apply check_ret_only_no_unmodeled in H. }
      cbn [negb] in H. cbv iota in H.
      destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |];
        now apply check_ret_only_copyins_no_unmodeled in H. }
  9:{ now apply check_ret_only_no_unmodeled in H. }
  - destruct (w_is0 ch) eqn:Hm.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      [| now apply check_ret_only_copyins_no_unmodeled in H
       | now apply check_ret_only_copyins_no_unmodeled in H ].
    cbv zeta in H.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (negb (m_channel_reader m)) eqn:Hrdr; cbv beta iota in H.
    { (* no reader on the far end: -EPIPE, never a decline *)
      unfold check_sigpipe_writev in H.
      now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae.
    2:{ destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
        destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; try discriminate.
        destruct ((1 <=? bv_unsigned ret)%Z
                  && (bv_unsigned ret
                      <=? Z.of_nat (length (gather_prefix (in_mem i) (cap_iovecs iovs))))%Z
                  && negb (addr_is_error_b ret));
          [destruct (access_ranges_eqb _ _)|]; discriminate. }
    wv_open_unmodeled Hfd. srw Hm. srw Hiv. srw Htot. srw Hrdr. srw Ht. srw Hae.
    apply record_copyins_unmodeled.
    unfold writev_buf_gap. apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      [| now apply check_ret_only_copyins_no_unmodeled in H
       | now apply check_ret_only_copyins_no_unmodeled in H ].
    cbv zeta in H.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { (* the faulting source answers unless the hole is too large *)
      unfold check_write_fault_extend in H.
      wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
      apply record_copyins_unmodeled. unfold write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
        [ destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
          [ apply unmodeled_intro
          | now apply check_ret_only_copyins_no_unmodeled in H ]
        | apply unmodeled_intro ]. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (negb (modeled_file_gap data off
                        (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk.
      { wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk.
        apply record_copyins_unmodeled.
        unfold writev_buf_gap. apply unmodeled_intro. }
      destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae.
      2:{ now apply check_ret_only_copyins_no_unmodeled in H. }
      wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk. srw Hae.
      apply record_copyins_unmodeled.
      unfold writev_buf_gap. apply unmodeled_intro.
    + wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs.
      apply record_copyins_unmodeled.
      unfold writev_buf_gap. apply unmodeled_intro.
  - (* append fd: the same declines, minus the zero-fill one *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      [| now apply check_ret_only_copyins_no_unmodeled in H
       | now apply check_ret_only_copyins_no_unmodeled in H ].
    cbv zeta in H.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae.
      2:{ now apply check_ret_only_copyins_no_unmodeled in H. }
      wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hae.
      apply record_copyins_unmodeled.
      unfold writev_buf_gap. apply unmodeled_intro.
    + wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs.
      apply record_copyins_unmodeled.
      unfold writev_buf_gap. apply unmodeled_intro.
  - (* the same file opened O_RDWR: the write-only bullet above *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      [| now apply check_ret_only_copyins_no_unmodeled in H
       | now apply check_ret_only_copyins_no_unmodeled in H ].
    cbv zeta in H.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { (* the faulting source: the [FdFileW] bullet above *)
      unfold check_write_fault_extend in H.
      wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
      apply record_copyins_unmodeled. unfold write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
        [ destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
          [ apply unmodeled_intro
          | now apply check_ret_only_copyins_no_unmodeled in H ]
        | apply unmodeled_intro ]. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (negb (modeled_file_gap data off
                        (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk.
      { wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk.
        apply record_copyins_unmodeled.
        unfold writev_buf_gap. apply unmodeled_intro. }
      destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae.
      2:{ now apply check_ret_only_copyins_no_unmodeled in H. }
      wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk. srw Hae.
      apply record_copyins_unmodeled.
      unfold writev_buf_gap. apply unmodeled_intro.
    + wv_open_unmodeled Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs.
      apply record_copyins_unmodeled.
      unfold writev_buf_gap. apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
  - (* socket: writing one is unmodeled at every count *)
    wv_open_unmodeled Hfd.
    unfold writev_buf_gap. apply unmodeled_intro.
  - (* pipe: the write end's vectored gap, below the zero-aggregate answer *)
    destruct w.
    2:{ now apply check_ret_only_no_unmodeled in H. }
    cbn [negb] in H |- *. cbv iota in H |- *.
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      [| now apply check_ret_only_copyins_no_unmodeled in H
       | now apply check_ret_only_copyins_no_unmodeled in H ].
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { now apply check_ret_only_copyins_no_unmodeled in H. }
    wv_open_unmodeled Hfd. srw Hiv. srw Htot.
    apply record_copyins_unmodeled.
    unfold writev_buf_gap. apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

(* Closing an errno arm in the completeness direction: the copy-in ledger
   the spec recorded is exactly the one the checker compares against. *)
Local Ltac wv_errno_complete :=
  unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins];
  rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl);
  cbn; rewrite ?bv_eqb_refl; reflexivity.

Lemma check_writev_complete_ok : forall i fd iov iovcnt eff m m' evs,
  writev_spec fd iov iovcnt i m (Ok eff m' evs) ->
  check_writev i fd iov iovcnt eff m = CheckOk m' evs.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold writev_spec, writev_file_arm, write_fault_keep, writev_ledger,
    sigpipe_write in H.
  unfold check_writev.
  unfold writev_gathered in H |- *.
  unfold writev_buf_gap in H. sys_unfold. cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd; hall Hfd; inv_ok.
  - destruct (w_is0 ch) eqn:Hm; hall Hm; inv_ok.
    { cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok.
    2:{ wv_errno_complete. }
    2:{ wv_errno_complete. }
    cbv zeta in *.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok.
    { wv_errno_complete. }
    destruct (negb (m_channel_reader m)) eqn:Hrdr; hall Hrdr; inv_ok.
    { (* no reader on the far end: -EPIPE and signal 13 *)
      unfold check_sigpipe_writev. wv_errno_complete. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0)
      eqn:Ht; hall Ht; inv_ok.
    { wv_errno_complete. }
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae;
      hall Hae; inv_ok.
    pose proof (f_equal (@length _) H6) as Hfl.
    rewrite length_firstn in Hfl.
    cbn.
    rewrite (len_word_unsigned x6 H4), H5.
    assert (Hnat : Z.to_nat (Z.of_nat (length x6)) = length x6) by lia.
    rewrite Hnat, <- H6.
    bool_true.
    rewrite !app_nil_r.
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl).
    cbn. now rewrite ?app_nil_r.
  - cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
  - destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok.
    2:{ wv_errno_complete. }
    2:{ wv_errno_complete. }
    cbv zeta in *.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok.
    { wv_errno_complete. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos; hall Hpos; inv_ok.
    { wv_errno_complete. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0)
      eqn:Ht; hall Ht; inv_ok.
    { (* the faulting source, over the file it still extends *)
      unfold write_fault_extend in *; cbv beta iota zeta in *.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        hall Hz; inv_ok.
      sys_unfold; inv_ok.
      unfold check_write_fault_extend. rewrite Hfs, Hz.
      wv_errno_complete. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    destruct (negb (modeled_file_gap data off
                      (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk; hall Hk; inv_ok.
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae;
      hall Hae; inv_ok.
    unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins].
    rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl).
    cbn. now rewrite ?bv_eqb_refl.
  - (* append fd: the arm above with no zero-fill guard to replay *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok.
    2:{ wv_errno_complete. }
    2:{ wv_errno_complete. }
    cbv zeta in *.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok.
    { wv_errno_complete. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos; hall Hpos; inv_ok.
    { wv_errno_complete. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0)
      eqn:Ht; hall Ht; inv_ok.
    { wv_errno_complete. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae;
      hall Hae; inv_ok.
    unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins].
    rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl).
    cbn. now rewrite ?bv_eqb_refl.
  - (* the same file opened O_RDWR: the write-only bullet above *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok.
    2:{ wv_errno_complete. }
    2:{ wv_errno_complete. }
    cbv zeta in *.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok.
    { wv_errno_complete. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos; hall Hpos; inv_ok.
    { wv_errno_complete. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0)
      eqn:Ht; hall Ht; inv_ok.
    { (* the faulting source: the [FdFileW] bullet above *)
      unfold write_fault_extend in *; cbv beta iota zeta in *.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        hall Hz; inv_ok.
      sys_unfold; inv_ok.
      unfold check_write_fault_extend. rewrite Hfs, Hz.
      wv_errno_complete. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    destruct (negb (modeled_file_gap data off
                      (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk; hall Hk; inv_ok.
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae;
      hall Hae; inv_ok.
    unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins].
    rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl).
    cbn. now rewrite ?bv_eqb_refl.
  - cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
  - (* pipe: the read end's -EBADF, the write end's 0 at a zero aggregate;
       every other vectored write is a decline, which [inv_ok] closes
       against an [Ok] hypothesis *)
    destruct w; cbn [negb] in *; cbv beta iota zeta in *; inv_ok.
    { destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
        hall Hiv; inv_ok.
      2:{ wv_errno_complete. }
      2:{ wv_errno_complete. }
      destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok.
      wv_errno_complete. }
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
  - (* /dev/null *)
    destruct wr; cbn [negb] in *; cbv beta iota in *.
    2:{ inv_ok; cbn; try rewrite bv_eqb_refl; reflexivity. }
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok; wv_errno_complete.
  - (* /dev/urandom: -EBADF *)
    inv_ok; cbn; try rewrite bv_eqb_refl; reflexivity.
  - cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_writev_complete_unmodeled : forall i fd iov iovcnt m eff,
  writev_spec fd iov iovcnt i m Unmodeled ->
  check_writev i fd iov iovcnt eff m = CheckUnmodeled.
Proof.
  intros i fd iov iovcnt m eff H.
  unfold writev_spec, writev_file_arm, write_fault_keep, writev_ledger,
    sigpipe_write in H.
  unfold check_writev.
  unfold writev_gathered in H |- *.
  unfold writev_buf_gap in H. sys_unfold. cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd; hall Hfd; inv_ok;
    try discriminate.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ => reflexivity
            end).
  - destruct (w_is0 ch) eqn:Hm; hall Hm; inv_ok; try discriminate.
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok; try discriminate.
    cbv zeta in *.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok;
      try discriminate.
    destruct (negb (m_channel_reader m)) eqn:Hrdr; hall Hrdr; inv_ok;
      try discriminate.
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht;
      hall Ht; inv_ok; try discriminate.
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae;
      hall Hae; inv_ok; try discriminate.
    reflexivity.
  - destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok; try discriminate.
    cbv zeta in *.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok;
      try discriminate.
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos; hall Hpos; inv_ok;
      try discriminate.
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht;
      hall Ht; inv_ok.
    { (* the faulting source declines only on the hole it will not build *)
      unfold write_fault_extend in *; cbv beta iota zeta in *.
      unfold check_write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
        try discriminate; [|reflexivity].
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        hall Hz; inv_ok; try discriminate; [reflexivity|];
        sys_unfold; inv_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      try discriminate.
    + destruct (negb (modeled_file_gap data off
                        (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk; hall Hk; inv_ok;
        try discriminate.
      { reflexivity. }
      destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae;
        hall Hae; inv_ok; try discriminate.
      reflexivity.
    + reflexivity.
  - (* append fd: only the missing key declines *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok; try discriminate.
    cbv zeta in *.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok;
      try discriminate.
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos; hall Hpos; inv_ok;
      try discriminate.
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht;
      hall Ht; inv_ok; try discriminate.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      try discriminate.
    + destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae;
        hall Hae; inv_ok; try discriminate.
      reflexivity.
    + reflexivity.
  - (* the same file opened O_RDWR: the write-only bullet above *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok; try discriminate.
    cbv zeta in *.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok;
      try discriminate.
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos; hall Hpos; inv_ok;
      try discriminate.
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht;
      hall Ht; inv_ok.
    { (* the faulting source: the [FdFileW] bullet above *)
      unfold write_fault_extend in *; cbv beta iota zeta in *.
      unfold check_write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
        try discriminate; [|reflexivity].
      destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
        hall Hz; inv_ok; try discriminate; [reflexivity|];
        sys_unfold; inv_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      try discriminate.
    + destruct (negb (modeled_file_gap data off
                        (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk; hall Hk; inv_ok;
        try discriminate.
      { reflexivity. }
      destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hae;
        hall Hae; inv_ok; try discriminate.
      reflexivity.
    + reflexivity.
  - (* socket: writing one is unmodeled at every count *)
    reflexivity.
  - (* pipe: a zero aggregate is an [Ok], so only the gap below it declines *)
    destruct w; cbn [negb] in *; cbv beta iota zeta in *; inv_ok;
      try discriminate.
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok; try discriminate.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot; hall Htot; inv_ok;
      try discriminate; reflexivity.
  - (* /dev/null *)
    destruct wr; cbn [negb] in *; cbv beta iota in *; [|inv_ok].
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
      hall Hiv; inv_ok.
Qed.

(* ----------------------------------------------------------------- readv *)

(** The checker-side spelling of a readv fail-closed gap: a plain
    decline.  See [ReadWrite.readv_buf_gap]. *)

Definition check_readv_gap : check_result := CheckUnmodeled.

Lemma readv_heap_gap_no_ok : forall i m eff m' evs,
  readv_heap_gap i m (Ok eff m' evs) -> False.
Proof.
  intros i m eff m' evs H.
  unfold readv_heap_gap, readv_buf_gap, unmodeled in H. discriminate.
Qed.

Definition check_readv_imported (i : SyscallInput) (fd : word)
    (r : ReadableFd) (iovs0 : list (word * word))
    (eff : SyscallEffect) (m : Model) : check_result :=
  let iovs := cap_iovecs iovs0 in
  let total := iovs_total iovs in
  if Z.eqb total 0 then check_ret_only eff (Z_to_bv 64 0) m []
  else
  match r with
  | RdChannel ch =>
      match m_stdin m with
      | IEof => check_ret_only eff (Z_to_bv 64 0) m []
      | ICons _ _ =>
          match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
          | None => check_ret_only eff (errno_ret EFAULT) m []
          | Some _ =>
              match scatter_iovecs (in_wmem i) iovs
                      (fst (stream_take_z (m_stdin m) total)) with
              | None => check_readv_gap   (* partially writable destination *)
              | Some _ =>
                  match eff with
                  | mkEffectU ret writes [] [] [] [] =>
                      let bs := concat (map snd writes) in
                      match scatter_iovecs (in_wmem i) iovs bs with
                      | None => CheckReject
                      | Some expected =>
                          if bv_eqb ret (len_word bs)
                             && writes_eqb writes expected
                             && (1 <=? Z.of_nat (length bs))%Z
                             && (Z.of_nat (length bs) <=? total)%Z
                             && listN_eqb
                                  (fst (stream_take (m_stdin m) (length bs))) bs
                          then CheckOk
                                 (with_stdin
                                    (snd (stream_take (m_stdin m) (length bs))) m)
                                 (map (ReadEv ch) bs)
                          else CheckReject
                      end
                  | _ => CheckReject
                  end
              end
          end
      end
  | RdSocket sk =>
      match sk with
      | SkConnected peer ch rx =>
          match rx with
          | NFin => check_ret_only eff (Z_to_bv 64 0) m []
          | NRst =>
              check_ret_only eff (errno_ret ECONNRESET)
                (with_fds (fd_insert (m_fds m) fd
                             (FdSocket (SkReset peer ch))) m) []
          | NTimedOut =>
              check_ret_only eff (errno_ret ETIMEDOUT)
                (with_fds (fd_insert (m_fds m) fd
                             (FdSocket (SkReset peer ch))) m) []
          | NCons _ _ =>
              match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
              | None => check_ret_only eff (errno_ret EFAULT) m []
              | Some _ =>
                  match scatter_iovecs (in_wmem i) iovs
                          (fst (net_take_z rx total)) with
                  | None => check_readv_gap   (* partially writable destination *)
                  | Some _ =>
                      (* exactly the channel shape, on the connection's
                         script: the ledger is the canonical scatter of the
                         delivered bytes, so the writes determine them *)
                      match eff with
                      | mkEffectU ret writes [] [] [] [] =>
                          let bs := concat (map snd writes) in
                          match scatter_iovecs (in_wmem i) iovs bs with
                          | None => CheckReject
                          | Some expected =>
                              if bv_eqb ret (len_word bs)
                                 && writes_eqb writes expected
                                 && (1 <=? Z.of_nat (length bs))%Z
                                 && (Z.of_nat (length bs) <=? total)%Z
                                 && listN_eqb (fst (net_take rx (length bs))) bs
                              then CheckOk
                                     (with_fds
                                        (fd_insert (m_fds m) fd
                                           (FdSocket
                                              (SkConnected peer ch
                                                 (snd (net_take rx (length bs)))))) m)
                                     (map (ReadEv ch) bs)
                              else CheckReject
                          end
                      | _ => CheckReject
                      end
                  end
              end
          end
      | SkReset _ _ => check_ret_only eff (Z_to_bv 64 0) m []
      | _ => check_ret_only eff (errno_ret ENOTCONN) m []
      end
  | RdPipe _ => check_readv_gap   (* vectored pipe reads are unmodeled *)
  | RdDevNull => check_ret_only eff (Z_to_bv 64 0) m []   (* [read_iter_null]: 0 *)
  | RdUrandom => check_readv_gap   (* vectored device reads decline: [ReadWrite.readv_imported] *)
  | RdDir => check_ret_only eff (errno_ret EISDIR) m []
  | RdFile p off =>
      match fs_lookup (m_fs m) p with
      | None => check_readv_gap
      | Some data =>
          if rw_pos_einvalb off total then check_ret_only eff (errno_ret EINVAL) m []
          else
          let bs := file_read data off (Z_to_bv 64 total) in
          match scatter_iovecs (in_wmem i) iovs bs with
          | Some writes =>
              if addr_is_error_b (len_word bs) then check_readv_gap
              else
              match eff with
              | mkEffectU ret writes' [] [] [] [] =>
                  if bv_eqb ret (len_word bs) && writes_eqb writes' writes
                  then CheckOk
                         (with_fds (fd_insert (m_fds m) fd
                                      (FdFile p (off + len_word bs))) m) []
                  else CheckReject
              | _ => CheckReject
              end
          | None =>
              match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
              | None => check_ret_only eff (errno_ret EFAULT) m []
              | Some _ => check_readv_gap
              end
          end
      end
  | RdFileRW p off =>   (* the [RdFile] arm above, on the O_RDWR kind *)
      match fs_lookup (m_fs m) p with
      | None => check_readv_gap
      | Some data =>
          if rw_pos_einvalb off total then check_ret_only eff (errno_ret EINVAL) m []
          else
          let bs := file_read data off (Z_to_bv 64 total) in
          match scatter_iovecs (in_wmem i) iovs bs with
          | Some writes =>
              if addr_is_error_b (len_word bs) then check_readv_gap
              else
              match eff with
              | mkEffectU ret writes' [] [] [] [] =>
                  if bv_eqb ret (len_word bs) && writes_eqb writes' writes
                  then CheckOk
                         (with_fds (fd_insert (m_fds m) fd
                                      (FdFileRW p (off + len_word bs))) m) []
                  else CheckReject
              | _ => CheckReject
              end
          | None =>
              match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
              | None => check_ret_only eff (errno_ret EFAULT) m []
              | Some _ => check_readv_gap
              end
          end
      end
  end.

Definition check_readv (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some e =>
      match readable_fd e with
      | None =>
          if fd_is_opaque e then CheckUnmodeled
          else check_ret_only eff (errno_ret EBADF) m []
          (* the read end has a [RdPipe]; only the O_WRONLY write end
             reaches this arm, where -EBADF is the kernel's own answer *)
      | Some r =>
          if readv_heap_iovecb iovcnt then check_readv_gap
          else
            match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
            | ImpFault => check_ret_only_copyins
                (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
                eff (errno_ret EFAULT) m []
            | ImpInval => check_ret_only_copyins
                (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
                eff (errno_ret EINVAL) m []
            | ImpOk iovs0 =>
                check_copyin_prefix
                  (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)) eff
                  (check_readv_imported i fd r iovs0
                     (strip_copyin_prefix
                        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
                        eff) m)
            end
      end
  end.

Example readv_copyin_reports_the_iovec_table :
  List.map (fun p => (bv_unsigned (fst p), snd p))
    (import_iovecs_accesses (fun _ => Some 0) 0x2000 2) =
    [(0x2000%Z, 16%nat); (0x2010%Z, 16%nat)].
Proof. vm_compute. reflexivity. Qed.

Definition one_iovec_mem : word -> option byte :=
  write_to_mem (fun _ => Some 0) 0x2000
    (Z_to_le_bytes 8 0x3000 ++ Z_to_le_bytes 8 2).

Example writev_copyin_reports_table_and_delivered_data :
  List.map (fun p => (bv_unsigned (fst p), snd p))
    (copy_iovecs_accesses one_iovec_mem 0x2000 1 ++
     iov_prefix_accesses [(0x3000, 2)] 2) =
    [(0x2000%Z, 16%nat); (0x3000%Z, 2%nat)].
Proof. vm_compute. reflexivity. Qed.

Definition invalid_first_iovec_mem : word -> option byte :=
  write_to_mem (fun _ => Some 0) 0x2000
    (Z_to_le_bytes 8 0x3000 ++ Z_to_le_bytes 8 (2 ^ 63)).

Example invalid_iovec_charges_only_the_attempted_descriptor :
  copy_iovecs_accesses invalid_first_iovec_mem 0x2000 2 =
    [(0x2000, 16%nat)].
Proof. vm_compute. reflexivity. Qed.

Lemma check_readv_imported_sound_ok : forall i fd e iovs eff m m' evs,
  check_readv_imported i fd e iovs eff m = CheckOk m' evs ->
  readv_imported fd e iovs i m i m (Ok eff m' evs).
Proof.
  intros i fd e iovs eff m m' evs H.
  unfold check_readv_imported in H. unfold readv_imported. cbv zeta in *.
  destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Hz.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct e as [ch|p off|p off| |sk|pid| | ].
  7:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  7:{ unfold check_readv_gap in H. discriminate. }
  - destruct (m_stdin m) as [|b s] eqn:Hs.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
      as [one|] eqn:Hone.
    2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                (fst (stream_take_z (ICons b s) (iovs_total (cap_iovecs iovs)))))
      as [need|] eqn:Hneed.
    2:{ unfold check_readv_gap in H. discriminate. }
    destruct eff as [ret writes zs us cs copyins].
    destruct zs as [|z zs]; [|discriminate].
    destruct us as [|u us]; [|discriminate].
    destruct cs as [|c cs]; [|discriminate].
    destruct copyins as [|ci copyins]; [|discriminate].
    set (bs := concat (map snd writes)) in *.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) bs)
      as [expected|] eqn:Hscatter; [|discriminate].
    destruct (bv_eqb ret (len_word bs) && writes_eqb writes expected
              && (1 <=? Z.of_nat (length bs))%Z
              && (Z.of_nat (length bs) <=? iovs_total (cap_iovecs iovs))%Z
              && listN_eqb (fst (stream_take (ICons b s) (length bs))) bs)
      eqn:Hgood; [|discriminate].
    inversion H; clear H; subst m' evs.
    apply andb_true_iff in Hgood as [Hgood Hstream].
    apply andb_true_iff in Hgood as [Hgood Hhi].
    apply andb_true_iff in Hgood as [Hgood Hlo].
    apply andb_true_iff in Hgood as [Hret Hwrites].
    apply bv_eqb_eq in Hret; subst ret.
    apply writes_eqb_eq in Hwrites; subst expected.
    apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    apply listN_eqb_eq in Hstream.
    eapply bind_ok0.
    { apply (choose_ok _ bs). repeat split; try assumption.
      rewrite Hscatter. discriminate. }
    cbv beta. rewrite Hscatter.
    eapply bind_ok0; [apply modify_ok|].
    eapply bind_ok_eq; [apply emit_ok|apply pure_ok|]. now rewrite app_nil_r.
  - destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
      { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
      cbv zeta in *.
      destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                  (file_read data off
                     (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
        as [writes|] eqn:Hscatter.
      * destruct (addr_is_error_b
                    (len_word (file_read data off
                       (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))) eqn:Hae.
        { unfold check_readv_gap in H. discriminate. }
        destruct eff as [ret writes' zs us cs copyins].
        destruct zs as [|z zs]; [|discriminate].
        destruct us as [|u us]; [|discriminate].
        destruct cs as [|c cs]; [|discriminate].
        destruct copyins as [|ci copyins]; [|discriminate].
        destruct (bv_eqb ret
                    (len_word (file_read data off
                       (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
                  && writes_eqb writes' writes) eqn:Hgood; [|discriminate].
        inversion H; clear H; subst m' evs.
        apply andb_true_iff in Hgood as [Hret Hwrites].
        apply bv_eqb_eq in Hret; subst ret.
        apply writes_eqb_eq in Hwrites; subst writes'.
        eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
      * destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
          as [one|] eqn:Hone.
        -- unfold check_readv_gap in H. discriminate.
        -- apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
           apply pure_ok.
    + unfold check_readv_gap in H. discriminate.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
      { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
      cbv zeta in *.
      destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                  (file_read data off
                     (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
        as [writes|] eqn:Hscatter.
      * destruct (addr_is_error_b
                    (len_word (file_read data off
                       (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))) eqn:Hae.
        { unfold check_readv_gap in H. discriminate. }
        destruct eff as [ret writes' zs us cs copyins].
        destruct zs as [|z zs]; [|discriminate].
        destruct us as [|u us]; [|discriminate].
        destruct cs as [|c cs]; [|discriminate].
        destruct copyins as [|ci copyins]; [|discriminate].
        destruct (bv_eqb ret
                    (len_word (file_read data off
                       (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
                  && writes_eqb writes' writes) eqn:Hgood; [|discriminate].
        inversion H; clear H; subst m' evs.
        apply andb_true_iff in Hgood as [Hret Hwrites].
        apply bv_eqb_eq in Hret; subst ret.
        apply writes_eqb_eq in Hwrites; subst writes'.
        eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
      * destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
          as [one|] eqn:Hone.
        -- unfold check_readv_gap in H. discriminate.
        -- apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
           apply pure_ok.
    + unfold check_readv_gap in H. discriminate.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
  - (* socket *)
    destruct sk as [| | |peer ch rx|peer ch].
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
    + destruct rx as [| | |b0 rx0].
      * apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
      * apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
      * apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
      * destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
          as [one|] eqn:Hone.
        2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                    (fst (net_take_z (NCons b0 rx0) (iovs_total (cap_iovecs iovs)))))
          as [need|] eqn:Hneed.
        2:{ unfold check_readv_gap in H. discriminate. }
        destruct eff as [ret writes zs us cs copyins].
        destruct zs as [|z zs]; [|discriminate].
        destruct us as [|u us]; [|discriminate].
        destruct cs as [|c cs]; [|discriminate].
        destruct copyins as [|k ks]; [|discriminate].
        set (bs := concat (map snd writes)) in *.
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) bs)
          as [expected|] eqn:Hscatter; [|discriminate].
        destruct (bv_eqb ret (len_word bs) && writes_eqb writes expected
                  && (1 <=? Z.of_nat (length bs))%Z
                  && (Z.of_nat (length bs) <=? iovs_total (cap_iovecs iovs))%Z
                  && listN_eqb (fst (net_take (NCons b0 rx0) (length bs))) bs)
          eqn:Hgood; [|discriminate].
        inversion H; clear H; subst m' evs.
        apply andb_true_iff in Hgood as [Hgood Hstream].
        apply andb_true_iff in Hgood as [Hgood Hhi].
        apply andb_true_iff in Hgood as [Hgood Hlo].
        apply andb_true_iff in Hgood as [Hret Hwrites].
        apply bv_eqb_eq in Hret; subst ret.
        apply writes_eqb_eq in Hwrites; subst expected.
        apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
        apply listN_eqb_eq in Hstream.
        eapply bind_ok0.
        { apply (choose_ok _ bs). repeat split; try assumption.
          rewrite Hscatter. discriminate. }
        cbv beta. rewrite Hscatter.
        eapply bind_ok0; [apply modify_ok|].
        eapply bind_ok_eq; [apply emit_ok|apply pure_ok|]. now rewrite app_nil_r.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
  - unfold check_readv_gap in H. discriminate.
Qed.

Lemma check_readv_imported_sound_unmodeled : forall i fd e iovs eff m,
  check_readv_imported i fd e iovs eff m = CheckUnmodeled ->
  readv_imported fd e iovs i m i m Unmodeled.
Proof.
  intros i fd e iovs eff m H.
  unfold check_readv_imported in H. unfold readv_imported. cbv zeta in *.
  destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Hz.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct e as [ch|p off|p off| |sk|pid| | ].
  7:{ now apply check_ret_only_no_unmodeled in H. }
  7:{ unfold readv_buf_gap. apply unmodeled_intro. }
  - destruct (m_stdin m) as [|b s] eqn:Hs.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
      as [one|] eqn:Hone.
    2:{ now apply check_ret_only_no_unmodeled in H. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                (fst (stream_take_z (ICons b s) (iovs_total (cap_iovecs iovs)))))
      as [need|] eqn:Hneed.
    2:{ unfold readv_buf_gap. apply unmodeled_intro. }
    destruct eff as [ret writes zs us cs copyins]. destruct zs; [|discriminate].
    destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct copyins; [|discriminate].
    set (bs := concat (map snd writes)) in *.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) bs).
    + destruct (bv_eqb ret (len_word bs) && writes_eqb writes l
               && (1 <=? Z.of_nat (length bs))%Z
               && (Z.of_nat (length bs) <=? iovs_total (cap_iovecs iovs))%Z
               && listN_eqb (fst (stream_take (ICons b s) (length bs))) bs);
        discriminate.
    + discriminate.
  - destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
      { now apply check_ret_only_no_unmodeled in H. }
      cbv zeta in *.
      destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                  (file_read data off
                     (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
        as [writes|] eqn:Hscatter.
      * destruct (addr_is_error_b
                    (len_word (file_read data off
                       (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))) eqn:Hae.
        -- unfold readv_buf_gap. apply unmodeled_intro.
        -- destruct eff as [ret writes' zs us cs copyins]. destruct zs; [|discriminate].
           destruct us; [|discriminate]. destruct cs; [|discriminate].
           destruct copyins; [|discriminate].
           destruct (bv_eqb ret
                       (len_word (file_read data off
                          (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
                     && writes_eqb writes' writes); discriminate.
      * destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
          as [one|] eqn:Hone.
        -- unfold readv_buf_gap. apply unmodeled_intro.
        -- now apply check_ret_only_no_unmodeled in H.
    + unfold readv_buf_gap. apply unmodeled_intro.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
      { now apply check_ret_only_no_unmodeled in H. }
      cbv zeta in *.
      destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                  (file_read data off
                     (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
        as [writes|] eqn:Hscatter.
      * destruct (addr_is_error_b
                    (len_word (file_read data off
                       (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))) eqn:Hae.
        -- unfold readv_buf_gap. apply unmodeled_intro.
        -- destruct eff as [ret writes' zs us cs copyins]. destruct zs; [|discriminate].
           destruct us; [|discriminate]. destruct cs; [|discriminate].
           destruct copyins; [|discriminate].
           destruct (bv_eqb ret
                       (len_word (file_read data off
                          (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
                     && writes_eqb writes' writes); discriminate.
      * destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
          as [one|] eqn:Hone.
        -- unfold readv_buf_gap. apply unmodeled_intro.
        -- now apply check_ret_only_no_unmodeled in H.
    + unfold readv_buf_gap. apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
  - (* socket *)
    destruct sk as [| | |peer ch rx|peer ch].
    + now apply check_ret_only_no_unmodeled in H.
    + now apply check_ret_only_no_unmodeled in H.
    + now apply check_ret_only_no_unmodeled in H.
    + destruct rx as [| | |b0 rx0].
      * now apply check_ret_only_no_unmodeled in H.
      * now apply check_ret_only_no_unmodeled in H.
      * now apply check_ret_only_no_unmodeled in H.
      * destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
          as [one|] eqn:Hone.
        2:{ now apply check_ret_only_no_unmodeled in H. }
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                    (fst (net_take_z (NCons b0 rx0) (iovs_total (cap_iovecs iovs)))))
          as [need|] eqn:Hneed.
        2:{ unfold readv_buf_gap. apply unmodeled_intro. }
        destruct eff as [ret writes zs us cs copyins].
        destruct zs; [|discriminate]. destruct us; [|discriminate].
        destruct cs; [|discriminate]. destruct copyins; [|discriminate].
        set (bs := concat (map snd writes)) in *.
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) bs).
        -- destruct (bv_eqb ret (len_word bs) && writes_eqb writes l
                     && (1 <=? Z.of_nat (length bs))%Z
                     && (Z.of_nat (length bs) <=? iovs_total (cap_iovecs iovs))%Z
                     && listN_eqb (fst (net_take (NCons b0 rx0) (length bs))) bs);
             discriminate.
        -- discriminate.
    + now apply check_ret_only_no_unmodeled in H.
  - (* pipe read end: both sides decline *)
    unfold readv_buf_gap. apply unmodeled_intro.
Qed.

Lemma check_readv_imported_complete_ok : forall i fd e iovs eff m m' evs,
  readv_imported fd e iovs i m i m (Ok eff m' evs) ->
  check_readv_imported i fd e iovs eff m = CheckOk m' evs.
Proof.
  intros i fd e iovs eff m m' evs H.
  unfold readv_imported in H. unfold check_readv_imported. cbv zeta in *.
  unfold readv_buf_gap, err_ret, ret_only, set_stdin, set_fds, modify, bind,
    pure, choose, emit, unmodeled in H.
  destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Hz; hall Hz; inv_ok.
  { inv_ok. cbn; rewrite bv_eqb_refl. reflexivity. }
  destruct e as [ch|p off|p off| |sk|pid| | ].
  7:{ inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  7:{ discriminate. }
  - destruct (m_stdin m) as [|b s] eqn:Hs; hall Hs; inv_ok.
    { inv_ok. cbn; rewrite bv_eqb_refl. reflexivity. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
      as [one|] eqn:Hone; hall Hone; inv_ok.
    2:{ cbn; rewrite bv_eqb_refl. reflexivity. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                (fst (stream_take_z (ICons b s) (iovs_total (cap_iovecs iovs)))))
      as [need|] eqn:Hneed; hall Hneed; inv_ok.
    match goal with
    | Hlo : (1 <= Z.of_nat (length ?bs))%Z |- _ =>
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) bs)
          as [writes|] eqn:Hsc
    end.
    2:{ hall Hsc; inv_ok; contradiction. }
    hall Hsc; inv_ok.
    match goal with
    | Hlo : (1 <= Z.of_nat (length ?bs))%Z |- _ =>
        pose proof (scatter_iovecs_concat _ _ _ _ Hsc) as Hcat;
        rewrite Hcat; rewrite Hsc
    end.
    bool_true.
    match goal with Hpre : fst (stream_take _ _) = _ |- _ =>
      rewrite (proj2 (listN_eqb_eq _ _) Hpre) end.
    rewrite (proj2 (writes_eqb_eq _ _) eq_refl).
    now rewrite app_nil_r.
  - destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos;
      hall Hpos; inv_ok.
    { cbn; rewrite bv_eqb_refl. reflexivity. }
    cbv zeta.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                (file_read data off
                   (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
      as [writes|] eqn:Hscatter; hall Hscatter; inv_ok.
    + destruct (addr_is_error_b
                  (len_word (file_read data off
                     (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))) eqn:Hae;
        hall Hae; inv_ok.
      rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl).
      reflexivity.
    + destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
        as [one|] eqn:Hone; hall Hone; inv_ok.
      cbn; rewrite bv_eqb_refl. reflexivity.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos;
      hall Hpos; inv_ok.
    { cbn; rewrite bv_eqb_refl. reflexivity. }
    cbv zeta.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                (file_read data off
                   (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
      as [writes|] eqn:Hscatter; hall Hscatter; inv_ok.
    + destruct (addr_is_error_b
                  (len_word (file_read data off
                     (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))) eqn:Hae;
        hall Hae; inv_ok.
      rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl).
      reflexivity.
    + destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
        as [one|] eqn:Hone; hall Hone; inv_ok.
      cbn; rewrite bv_eqb_refl. reflexivity.
  - inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
  - (* socket *)
    destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *.
    + inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
    + inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
    + inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
    + destruct rx as [| | |b0 rx0]; cbv beta iota zeta in *.
      * inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
      * inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
      * inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
      * inv_ok.
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
          as [one|] eqn:Hone; hall Hone; inv_ok.
        2:{ cbn; rewrite bv_eqb_refl. reflexivity. }
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                    (fst (net_take_z (NCons b0 rx0) (iovs_total (cap_iovecs iovs)))))
          as [need|] eqn:Hneed; hall Hneed; inv_ok.
        match goal with
        | Hlo : (1 <= Z.of_nat (length ?bs))%Z |- _ =>
            destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) bs)
              as [writes|] eqn:Hsc
        end.
        2:{ hall Hsc; inv_ok; contradiction. }
        hall Hsc; inv_ok.
        match goal with
        | Hlo : (1 <= Z.of_nat (length ?bs))%Z |- _ =>
            pose proof (scatter_iovecs_concat _ _ _ _ Hsc) as Hcat;
            rewrite Hcat; rewrite Hsc
        end.
        bool_true.
        match goal with Hpre : fst (net_take _ _) = _ |- _ =>
          rewrite (proj2 (listN_eqb_eq _ _) Hpre) end.
        rewrite (proj2 (writes_eqb_eq _ _) eq_refl).
        now rewrite app_nil_r.
    + inv_ok. cbn; rewrite bv_eqb_refl. reflexivity.
  - (* pipe read end: the gap declines, so it admits no [Ok] *)
    discriminate.
Qed.

Lemma check_readv_imported_complete_unmodeled : forall i fd e iovs m eff,
  readv_imported fd e iovs i m i m Unmodeled ->
  check_readv_imported i fd e iovs eff m = CheckUnmodeled.
Proof.
  intros i fd e iovs m eff H.
  unfold readv_imported in H. unfold check_readv_imported. cbv zeta in *.
  unfold readv_buf_gap, err_ret, ret_only, set_stdin, set_fds, modify, bind,
    pure, choose, emit, unmodeled in H.
  destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Hz; hall Hz; inv_ok;
    try discriminate.
  destruct e as [ch|p off|p off| |sk|pid| | ].
  7:{ inv_ok. }
  7:{ reflexivity. }
  - destruct (m_stdin m) as [|b s] eqn:Hs; hall Hs; inv_ok; try discriminate.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
      as [one|] eqn:Hone; hall Hone; inv_ok; try discriminate.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                (fst (stream_take_z (ICons b s) (iovs_total (cap_iovecs iovs)))))
      as [need|] eqn:Hneed; hall Hneed; inv_ok; [|reflexivity].
    match goal with
    | Hlo : (1 <= Z.of_nat (length ?bs))%Z |- _ =>
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) bs)
          eqn:Hsc
    end.
    + hall Hsc; inv_ok; discriminate.
    + hall Hsc; inv_ok; discriminate.
  - destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      [|reflexivity].
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos;
      hall Hpos; inv_ok; try discriminate.
    cbv zeta.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                (file_read data off
                   (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
      as [writes|] eqn:Hscatter; hall Hscatter; inv_ok; try discriminate.
    { destruct (addr_is_error_b
                  (len_word (file_read data off
                     (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))) eqn:Hae;
        hall Hae; inv_ok; try discriminate.
      reflexivity. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
      as [one|] eqn:Hone; hall Hone; inv_ok; try discriminate.
    reflexivity.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
      [|reflexivity].
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos;
      hall Hpos; inv_ok; try discriminate.
    cbv zeta.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                (file_read data off
                   (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))
      as [writes|] eqn:Hscatter; hall Hscatter; inv_ok; try discriminate.
    { destruct (addr_is_error_b
                  (len_word (file_read data off
                     (Z_to_bv 64 (iovs_total (cap_iovecs iovs)))))) eqn:Hae;
        hall Hae; inv_ok; try discriminate.
      reflexivity. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
      as [one|] eqn:Hone; hall Hone; inv_ok; try discriminate.
    reflexivity.
  - discriminate.
  - (* socket *)
    destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *; inv_ok;
      try discriminate.
    destruct rx as [| | |b0 rx0]; cbv beta iota zeta in *; inv_ok;
      try discriminate.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) [Z_to_bv 8 0])
      as [one|] eqn:Hone; hall Hone; inv_ok; try discriminate.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs)
                (fst (net_take_z (NCons b0 rx0) (iovs_total (cap_iovecs iovs)))))
      as [need|] eqn:Hneed; hall Hneed; inv_ok; [|reflexivity].
    match goal with
    | Hlo : (1 <= Z.of_nat (length ?bs))%Z |- _ =>
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs) bs) eqn:Hsc
    end; hall Hsc; inv_ok; discriminate.
  - (* pipe read end: both sides decline *)
    reflexivity.
Qed.

Lemma check_readv_sound_ok : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs ->
  readv_spec fd iov iovcnt i m (Ok eff m' evs).
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_readv in H. unfold readv_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - destruct (readable_fd e) as [r|] eqn:Hr.
    + destruct (readv_heap_iovecb iovcnt) eqn:Hheap.
      { unfold check_readv_gap in H.
        discriminate. }
      destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt))
        as [iovs0| |] eqn:Himp.
      * unfold check_copyin_prefix in H.
        remember (check_readv_imported i fd r iovs0
          (strip_copyin_prefix
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)) eff) m)
          as checked eqn:Hchecked.
        destruct checked as [checked_m checked_evs| |].
        2:{ destruct (access_ranges_eqb
              (firstn
                (length (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)))
                (eff_copyins eff))
              (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)));
            discriminate. }
        2:{ discriminate. }
        destruct (access_ranges_eqb
          (firstn
            (length (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)))
            (eff_copyins eff))
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)))
          eqn:Hreads; [|discriminate].
        inversion H; clear H; subst checked_m checked_evs.
        apply access_ranges_eqb_eq in Hreads.
        destruct eff as [ret writes zeros unmaps copies copyins]. cbn in Hreads.
        unfold strip_copyin_prefix, with_copyins in Hchecked. cbn in Hchecked.
        symmetry in Hchecked.
        apply check_readv_imported_sound_ok in Hchecked.
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
        srw Hfd; srw Hr; srw Himp.
        assert (Hcopyins :
          import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) ++
          skipn
            (length (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)))
            copyins = copyins).
        { transitivity
            (firstn
               (length (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)))
               copyins ++
             skipn
               (length (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)))
               copyins).
          - now rewrite Hreads.
          - apply firstn_skipn. }
        rewrite <- Hcopyins.
        pose proof (record_copyins_ok
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
          (readv_imported fd r iovs0 i m)
          i m
          (mkEffectU ret writes zeros unmaps copies
            (skipn
              (length (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)))
              copyins))
          m' evs Hchecked) as Hrecord.
        exact Hrecord.
      * apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
        srw Hfd; srw Hr; srw Himp. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
      * apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
        eapply bind_ok0; [apply input_ok|]. cbv beta.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
        srw Hfd; srw Hr; srw Himp. cbn [with_copyins].
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
    + (* the gate said no: -EBADF on every kind *)
      destruct e; cbv beta iota in H |- *; try discriminate;
        (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         eapply bind_ok0; [apply input_ok|]; cbv beta;
         eapply bind_ok0; [apply get_model_ok|]; cbv beta iota;
         srw Hfd; srw Hr; apply pure_ok).
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply pure_ok.
Qed.

Lemma check_readv_sound_unmodeled : forall i fd iov iovcnt eff m,
  check_readv i fd iov iovcnt eff m = CheckUnmodeled ->
  readv_spec fd iov iovcnt i m Unmodeled.
Proof.
  intros i fd iov iovcnt eff m H.
  unfold check_readv in H. unfold readv_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  2:{ now apply check_ret_only_no_unmodeled in H. }
  destruct (readable_fd e) as [r|] eqn:Hr.
  2:{ destruct e; cbv beta iota in H |- *;
        try (now apply check_ret_only_no_unmodeled in H).
      (* the opaque kinds: the gate's [None] declines on both sides *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
      srw Hfd; srw Hr. apply unmodeled_intro. }
  destruct (readv_heap_iovecb iovcnt) eqn:Hheap.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd; srw Hr. unfold readv_heap_gap, readv_buf_gap.
    apply unmodeled_intro. }
  destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt))
    as [iovs0| |] eqn:Himp;
    try (now apply check_ret_only_copyins_no_unmodeled in H).
  unfold check_copyin_prefix in H.
  remember (check_readv_imported i fd r iovs0
    (strip_copyin_prefix
      (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)) eff) m)
    as checked eqn:Hchecked.
  destruct checked as [checked_m checked_evs| |].
  - destruct (access_ranges_eqb
      (firstn
        (length (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)))
        (eff_copyins eff))
      (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)));
      discriminate.
  - destruct (access_ranges_eqb
      (firstn
        (length (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)))
        (eff_copyins eff))
      (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)));
      discriminate.
  - clear H.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
  srw Hfd; srw Hr; srw Himp.
  apply record_copyins_unmodeled.
  symmetry in Hchecked.
  eapply check_readv_imported_sound_unmodeled; exact Hchecked.
Qed.

Lemma check_readv_complete_ok : forall i fd iov iovcnt eff m m' evs,
  readv_spec fd iov iovcnt i m (Ok eff m' evs) ->
  check_readv i fd iov iovcnt eff m = CheckOk m' evs.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold readv_spec in H. unfold check_readv.
  sys_unfold. cbv iota zeta in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok.
  - destruct (readable_fd e) as [r|] eqn:Hr; hall Hr; inv_ok.
    + destruct (readv_heap_iovecb iovcnt) eqn:Hheap.
      { hall Hheap.
        match goal with
        | Hgap : readv_heap_gap _ _ (Ok _ _ _) |- _ =>
            exfalso; exact (readv_heap_gap_no_ok _ _ _ _ _ Hgap)
        end. }
      hall Hheap. inv_ok.
      destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt))
        as [iovs0| |] eqn:Himp; hall Himp; inv_ok.
      * destruct x as [ret writes zeros unmaps copies copyins].
        pose proof (check_readv_imported_complete_ok _ _ _ _ _ _ _ _ H) as Hb.
        unfold check_copyin_prefix, strip_copyin_prefix, with_copyins.
        cbn [eff_copyins].
        rewrite firstn_app, firstn_all, Nat.sub_diag. cbn.
        rewrite app_nil_r,
          (proj2 (access_ranges_eqb_eq _ _) eq_refl).
        rewrite skipn_app, skipn_all, Nat.sub_diag. cbn.
        rewrite skipn_O, app_nil_r.
        rewrite Hb. reflexivity.
      * unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins];
          rewrite app_nil_r,
            (proj2 (access_ranges_eqb_eq _ _) eq_refl); reflexivity.
      * unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins];
          rewrite app_nil_r,
            (proj2 (access_ranges_eqb_eq _ _) eq_refl); reflexivity.
    + (* the gate said no: -EBADF *)
      destruct e; cbv beta iota in *; try discriminate; inv_ok;
        cbn; try rewrite bv_eqb_refl; reflexivity.
  - cbn; try rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_readv_complete_unmodeled : forall i fd iov iovcnt m eff,
  readv_spec fd iov iovcnt i m Unmodeled ->
  check_readv i fd iov iovcnt eff m = CheckUnmodeled.
Proof.
  intros i fd iov iovcnt m eff H.
  unfold readv_spec in H. unfold check_readv.
  sys_unfold. cbv iota zeta in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd;
    hall Hfd; inv_ok; try discriminate.
  (* the gate's [None] is a real -EBADF for every kind, so the spec
     cannot decline there and that goal closes by [discriminate] *)
  destruct (readable_fd e) as [r|] eqn:Hr; hall Hr; inv_ok; try discriminate.
  2:{ (* the gate's [None]: the opaque kinds decline on both sides, every
         other kind is a real -EBADF the spec cannot decline *)
      destruct e; cbv beta iota in *; inv_ok; first [reflexivity | discriminate]. }
  destruct (readv_heap_iovecb iovcnt) eqn:Hheap.
  { (* the heap-backed band declines whatever the raw count is *)
    hall Hheap. reflexivity. }
  hall Hheap. inv_ok.
  destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt))
    as [iovs0| |] eqn:Himp; hall Himp; inv_ok; try discriminate.
  pose proof (check_readv_imported_complete_unmodeled
    i fd r iovs0 m
    (strip_copyin_prefix
      (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)) eff) H) as Hb.
  unfold check_copyin_prefix. rewrite Hb. reflexivity.
Qed.

(* ----------------------------------------------------------------- lseek *)

Definition check_lseek (fd off whence : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some e =>
      if (SEEK_MAX <? bv_unsigned whence)%Z
      then (if fd_is_opaque e then CheckUnmodeled
            else check_ret_only eff (errno_ret EINVAL) m [])  (* before the fd's kind: see [ReadWrite.lseek_spec] *)
      else
      match e with
      | FdChannel _ => check_ret_only eff (errno_ret ESPIPE) m []
      | FdSocket _ => check_ret_only eff (errno_ret ESPIPE) m []
          (* a socket file has no [.llseek] and never gets FMODE_LSEEK, so
             [vfs_llseek] is -ESPIPE -- after the -EINVAL above, which
             [ksys_lseek] decides first *)
      | FdPipe _ _ => check_ret_only eff (errno_ret ESPIPE) m []
      | FdDevNull _ _ => check_ret_only eff (Z_to_bv 64 0) m []   (* [null_lseek]: 0 *)
      | FdUrandom => check_ret_only eff (Z_to_bv 64 0) m []   (* [noop_llseek]: the pinned 0 *)
      | FdOpaque _ => CheckUnmodeled   (* declined: see [ReadWrite.lseek_spec] *)
      | FdDir => CheckUnmodeled   (* unmodeled: see [ReadWrite.lseek_spec] *)
      | FdFile p cur =>
          match fs_lookup (m_fs m) p with
          | None => CheckUnmodeled
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => CheckUnmodeled   (* SEEK_DATA/SEEK_HOLE: unmodeled *)
              | Some base =>
                  match lseek_dest base off with
                  | None => check_ret_only eff (errno_ret EINVAL) m []
                  | Some r =>
                      check_ret_only eff r
                        (with_fds (fd_insert (m_fds m) fd (FdFile p r)) m) []
                  end
              end
          end
      | FdFileW p cur =>
          match fs_lookup (m_fs m) p with
          | None => CheckUnmodeled
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => CheckUnmodeled   (* SEEK_DATA/SEEK_HOLE: unmodeled *)
              | Some base =>
                  match lseek_dest base off with
                  | None => check_ret_only eff (errno_ret EINVAL) m []
                  | Some r =>
                      check_ret_only eff r
                        (with_fds (fd_insert (m_fds m) fd (FdFileW p r)) m) []
                  end
              end
          end
      | FdFileRW p cur =>   (* the [FdFileW] arm above, on the O_RDWR kind *)
          match fs_lookup (m_fs m) p with
          | None => CheckUnmodeled
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => CheckUnmodeled   (* SEEK_DATA/SEEK_HOLE: unmodeled *)
              | Some base =>
                  match lseek_dest base off with
                  | None => check_ret_only eff (errno_ret EINVAL) m []
                  | Some r =>
                      check_ret_only eff r
                        (with_fds (fd_insert (m_fds m) fd (FdFileRW p r)) m) []
                  end
              end
          end
      | FdFileA p cur =>
          match fs_lookup (m_fs m) p with
          | None => CheckUnmodeled
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => CheckUnmodeled   (* SEEK_DATA/SEEK_HOLE: unmodeled *)
              | Some base =>
                  match lseek_dest base off with
                  | None => check_ret_only eff (errno_ret EINVAL) m []
                  | Some r =>
                      check_ret_only eff r
                        (with_fds (fd_insert (m_fds m) fd (FdFileA p r)) m) []
                  end
              end
          end
      end
  end.

(** [fsync]/[fdatasync]: total over [FdEntry], so there is no
    [CheckUnmodeled] arm.  Kernel citations live on [Sync.fsync_spec]. *)

Lemma check_lseek_sound_ok : forall fd off whence eff m m' evs i,
  check_lseek fd off whence eff m = CheckOk m' evs ->
  lseek_spec fd off whence i m (Ok eff m' evs).
Proof.
  intros fd off whence eff m m' evs i H.
  unfold check_lseek in H. unfold lseek_spec.
  (* the whence gate precedes the fd's KIND on both sides, but follows
     the fd lookup: [ksys_lseek]'s order *)
  destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|id w|rd wr| |o]|] eqn:Hfd.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ =>
                destruct ((SEEK_MAX <? bv_unsigned whence)%Z); cbv beta iota in H;
                discriminate
            end).
  9:{ (* /dev/null: -EINVAL past SEEK_MAX, else [null_lseek]'s 0 *)
      destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw;
        apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
        (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
        srw Hfd; try rewrite Hw; cbv beta iota; apply pure_ok. }
  9:{ (* /dev/urandom: -EINVAL past SEEK_MAX, else [noop_llseek]'s 0 *)
      destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw;
        apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
        (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
        srw Hfd; try rewrite Hw; cbv beta iota; apply pure_ok. }
  - (* channel: -EINVAL past SEEK_MAX, -ESPIPE otherwise *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw;
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
      apply pure_ok.
  - destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    destruct (lseek_base whence cur (len_word data)) as [base|]
      eqn:Hbase; [|discriminate].
    destruct (lseek_dest base off) as [r|] eqn:Hdst.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbase. srw Hdst.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbase. srw Hdst. apply pure_ok.
  - (* write-only file fd: same repositioning *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    destruct (lseek_base whence cur (len_word data)) as [base|]
      eqn:Hbase; [|discriminate].
    destruct (lseek_dest base off) as [r|] eqn:Hdst.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbase. srw Hdst.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbase. srw Hdst. apply pure_ok.
  - (* append fd: same repositioning again *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    destruct (lseek_base whence cur (len_word data)) as [base|]
      eqn:Hbase; [|discriminate].
    destruct (lseek_dest base off) as [r|] eqn:Hdst.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbase. srw Hdst.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbase. srw Hdst. apply pure_ok.
  - (* the same file opened O_RDWR: same repositioning, on the offset both directions share *)
    (* write-only file fd: same repositioning *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw.
    { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
      apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
    destruct (lseek_base whence cur (len_word data)) as [base|]
      eqn:Hbase; [|discriminate].
    destruct (lseek_dest base off) as [r|] eqn:Hdst.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbase. srw Hdst.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. srw Hfs. srw Hbase. srw Hdst. apply pure_ok.
  - (* directory fd: -EINVAL past SEEK_MAX, unmodeled otherwise *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw; [|discriminate].
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
    apply pure_ok.
  - (* socket: -EINVAL past SEEK_MAX, -ESPIPE otherwise -- the channel
       shape *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw;
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
      apply pure_ok.
  - (* either pipe end: -ESPIPE, as for a channel *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw;
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
      apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
    apply pure_ok.
Qed.

Lemma check_lseek_sound_unmodeled : forall fd off whence eff m i,
  check_lseek fd off whence eff m = CheckUnmodeled ->
  lseek_spec fd off whence i m Unmodeled.
Proof.
  intros fd off whence eff m i H.
  unfold check_lseek in H. unfold lseek_spec.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|id w|rd wr| |o]|] eqn:Hfd.
  all: try (match goal with
            | Hfd : fd_lookup _ _ = Some (FdOpaque _) |- _ =>
                eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
                srw Hfd; destruct ((SEEK_MAX <? bv_unsigned whence)%Z);
                cbv beta iota; apply unmodeled_intro
            end).
  9:{ destruct ((SEEK_MAX <? bv_unsigned whence)%Z);
        now apply check_ret_only_no_unmodeled in H. }
  9:{ destruct ((SEEK_MAX <? bv_unsigned whence)%Z);
        now apply check_ret_only_no_unmodeled in H. }
  - destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw;
      now apply check_ret_only_no_unmodeled in H.
  - destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (lseek_base whence cur (len_word data)) as [base|]
        eqn:Hbase.
      * destruct (lseek_dest base off) as [r|] eqn:Hdst;
          now apply check_ret_only_no_unmodeled in H.
      * (* SEEK_DATA/SEEK_HOLE: both sides fail closed *)
        eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hfs. srw Hbase. apply unmodeled_intro.
    + eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hfs.
      apply unmodeled_intro.
  - (* write-only file fd *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (lseek_base whence cur (len_word data)) as [base|]
        eqn:Hbase.
      * destruct (lseek_dest base off) as [r|] eqn:Hdst;
          now apply check_ret_only_no_unmodeled in H.
      * eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hfs. srw Hbase. apply unmodeled_intro.
    + eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hfs.
      apply unmodeled_intro.
  - (* append fd *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (lseek_base whence cur (len_word data)) as [base|]
        eqn:Hbase.
      * destruct (lseek_dest base off) as [r|] eqn:Hdst;
          now apply check_ret_only_no_unmodeled in H.
      * eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hfs. srw Hbase. apply unmodeled_intro.
    + eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hfs.
      apply unmodeled_intro.
  - (* the same file opened O_RDWR *)
    (* write-only file fd *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw.
    { now apply check_ret_only_no_unmodeled in H. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (lseek_base whence cur (len_word data)) as [base|]
        eqn:Hbase.
      * destruct (lseek_dest base off) as [r|] eqn:Hdst;
          now apply check_ret_only_no_unmodeled in H.
      * eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
        srw Hfd. srw Hfs. srw Hbase. apply unmodeled_intro.
    + eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hfs.
      apply unmodeled_intro.
  - (* directory fd: unmodeled, both sides fail closed *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw.
    { now apply check_ret_only_no_unmodeled in H. }
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hfd.
    apply unmodeled_intro.
  - (* socket: both whence bands answer, so there is nothing to decline *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw;
      now apply check_ret_only_no_unmodeled in H.
  - (* either pipe end: -ESPIPE, never a decline *)
    destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw;
      now apply check_ret_only_no_unmodeled in H.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_lseek_complete_ok : forall fd off whence eff m m' evs i,
  lseek_spec fd off whence i m (Ok eff m' evs) ->
  check_lseek fd off whence eff m = CheckOk m' evs.
Proof.
  intros fd off whence eff m m' evs i H.
  unfold lseek_spec in H. unfold check_lseek. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|id w|rd wr| |o]|] eqn:Hfd; hall Hfd; inv_ok;
    try (destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw; hall Hw; inv_ok);
    try (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok);
    try (destruct (lseek_base whence cur (len_word data)) as [base|]
           eqn:Hbase; hall Hbase; inv_ok);
    try (destruct (lseek_dest base off) as [r|] eqn:Hdst; hall Hdst; inv_ok);
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_lseek_complete_unmodeled : forall fd off whence m i eff,
  lseek_spec fd off whence i m Unmodeled ->
  check_lseek fd off whence eff m = CheckUnmodeled.
Proof.
  intros fd off whence m i eff H.
  unfold lseek_spec in H. unfold check_lseek. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|id w|rd wr| |o]|] eqn:Hfd; hall Hfd; inv_ok;
    try (destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw; hall Hw; inv_ok);
    try (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok);
    try (destruct (lseek_base whence cur (len_word data)) as [base|]
           eqn:Hbase; hall Hbase; inv_ok);
    try (destruct (lseek_dest base off) as [r|] eqn:Hdst; hall Hdst; inv_ok);
    first [reflexivity | discriminate].
Qed.

(* ----------------------------------------------------------------- fsync *)

(* ------------------------------------------------------------------- brk *)
