(** * LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers — the clock_gettime (113) and clock_getres (114) checkers

    Mirrors [Sys/Kernel/Time/PosixTimers.v], which answers to Linux
    [kernel/time/posix-timers.c]: this file holds the checkers for the
    syscalls defined there, and no others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Uaccess.

(** clock_gettime: CLOCK_MONOTONIC, CLOCK_PROCESS_CPUTIME_ID or one of
    the per-call ids ([Kernel.Time.PosixTimers.clockid_percall_b] —
    CLOCK_REALTIME and the raw, coarse and boottime ids), only a fully
    writable 16-byte destination, and only a reading
    [Kernel.Time.PosixTimers.timespec_ok_b] (respectively
    [Kernel.Time.PosixTimers.realtime_ok_b],
    [Kernel.Time.PosixTimers.cputime_ok_b]) admits — the same booleans
    the spec chooses against, so acceptor and spec cannot drift apart.
    The effect must be exactly one write of those bytes at [tp] and
    nothing else: no zeros, no unmaps, no copies, no copy-ins.

    The three arms differ in three places, and each is the point.  Only
    the monotonic arm tests an envelope on [m_clock], because it is the
    only one that reads it, and only it answers
    [CheckOk (with_clock ...) ...] rather than [CheckOk m] — an
    accepted per-call or [CLOCK_PROCESS_CPUTIME_ID] call leaves
    the model where it was.  Those two are then separated by the
    predicate alone. *)
Definition check_clock_gettime (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if clockid_percall_b clkid then
    match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
    | None => CheckUnmodeled
    | Some _ =>
        match eff with
        | mkEffectU r [(a, bs)] [] [] [] [] =>
            if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp && realtime_ok_b bs
            then CheckOk m []
            else CheckReject
        | _ => CheckReject
        end
    end
  else if Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID then
    match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
    | None => CheckUnmodeled
    | Some _ =>
        match eff with
        | mkEffectU r [(a, bs)] [] [] [] [] =>
            if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp && cputime_ok_b bs
            then CheckOk m []
            else CheckReject
        | _ => CheckReject
        end
    end
  else if negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC) then CheckUnmodeled
  else if negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)
  then CheckUnmodeled
  else
  match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
  | None => CheckUnmodeled
  | Some _ =>
      match eff with
      | mkEffectU r [(a, bs)] [] [] [] [] =>
          if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp
             && timespec_ok_b bs (m_clock m)
          then CheckOk (with_clock (Z_to_bv 64 (timespec_ns bs)) m) []
          else CheckReject
      | _ => CheckReject
      end
  end.

Lemma check_clock_gettime_sound_ok : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs ->
  clock_gettime_spec clkid tp i m (Ok eff m' evs).
Proof.
  intros i clkid tp [ret ws zs us cs copyins] m m' evs H.
  unfold check_clock_gettime in H. unfold clock_gettime_spec.
  destruct (clockid_percall_b clkid) eqn:Hrt; cbv iota.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst0;
      [|discriminate]. cbv iota in H.
    destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
              && realtime_ok_b bs) eqn:Hok; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hok as [Hok1 Hts].
    apply andb_true_iff in Hok1 as [Hr Ha].
    apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst.
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    rewrite Hdst0. cbv iota.
    eapply bind_ok0; [apply (choose_ok _ bs); exact Hts|].
    apply pure_ok. }
  destruct (Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID) eqn:Hcp;
    cbv iota.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst1;
      [|discriminate]. cbv iota in H.
    destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
              && cputime_ok_b bs) eqn:Hok; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hok as [Hok1 Hts].
    apply andb_true_iff in Hok1 as [Hr Ha].
    apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst.
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    rewrite Hdst1. cbv iota.
    eapply bind_ok0; [apply (choose_ok _ bs); exact Hts|].
    apply pure_ok. }
  destruct (negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)) eqn:Hid;
    [discriminate|]. cbv iota.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)) eqn:Henv;
    [discriminate|]. cbv iota.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst;
    [|discriminate]. cbv iota.
  destruct ws as [|[a bs] ws']; [discriminate|].
  destruct ws' as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
            && timespec_ok_b bs (m_clock m)) eqn:Hok; [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in Hok as [Hok1 Hts].
  apply andb_true_iff in Hok1 as [Hr Ha].
  apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst.
  eapply bind_ok0; [apply (choose_ok _ bs); exact Hts|].
  eapply bind_ok0; [apply modify_ok|].
  apply pure_ok.
Qed.

Lemma check_clock_gettime_sound_unmodeled : forall i clkid tp eff m,
  check_clock_gettime i clkid tp eff m = CheckUnmodeled ->
  clock_gettime_spec clkid tp i m Unmodeled.
Proof.
  intros i clkid tp [ret ws zs us cs copyins] m H.
  unfold check_clock_gettime in H. unfold clock_gettime_spec.
  destruct (clockid_percall_b clkid) eqn:Hrt; cbv iota.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst0;
      cbv iota; [|apply unmodeled_intro].
    exfalso. cbv iota in H.
    destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
              && realtime_ok_b bs); discriminate. }
  destruct (Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID) eqn:Hcp;
    cbv iota.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst1;
      cbv iota; [|apply unmodeled_intro].
    exfalso. cbv iota in H.
    destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
              && cputime_ok_b bs); discriminate. }
  destruct (negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)) eqn:Hid;
    cbv iota; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)) eqn:Henv;
    cbv iota; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst;
    cbv iota; [|apply unmodeled_intro].
  exfalso. cbv iota in H.
  destruct ws as [|[a bs] ws']; [discriminate|].
  destruct ws' as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
            && timespec_ok_b bs (m_clock m)); discriminate.
Qed.

Lemma check_clock_gettime_complete_ok : forall i clkid tp eff m m' evs,
  clock_gettime_spec clkid tp i m (Ok eff m' evs) ->
  check_clock_gettime i clkid tp eff m = CheckOk m' evs.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold clock_gettime_spec in H. unfold check_clock_gettime.
  destruct (clockid_percall_b clkid) eqn:Hrt;
    cbv iota in *; sys_unfold; inv_ok.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst0;
      cbv iota in *; inv_ok.
    cbv iota. bool_true. reflexivity. }
  destruct (Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID) eqn:Hcp;
    cbv iota in *; sys_unfold; inv_ok.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst1;
      cbv iota in *; inv_ok.
    cbv iota. bool_true. reflexivity. }
  destruct (negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)) eqn:Hid;
    cbv iota in *; inv_ok.
  destruct (negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)) eqn:Henv;
    cbv iota in *; inv_ok.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst;
    cbv iota in *; inv_ok.
  cbv iota. bool_true. reflexivity.
Qed.

Lemma check_clock_gettime_complete_unmodeled : forall i clkid tp m eff,
  clock_gettime_spec clkid tp i m Unmodeled ->
  check_clock_gettime i clkid tp eff m = CheckUnmodeled.
Proof.
  intros i clkid tp m eff H.
  unfold clock_gettime_spec in H. unfold check_clock_gettime.
  destruct (clockid_percall_b clkid) eqn:Hrt;
    cbv iota in *; sys_unfold; inv_ok.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst0;
      cbv iota in *; [|reflexivity]. inv_ok. }
  destruct (Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID) eqn:Hcp;
    cbv iota in *; sys_unfold; inv_ok.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst1;
      cbv iota in *; [|reflexivity]. inv_ok. }
  destruct (negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)) eqn:Hid;
    cbv iota in *; [reflexivity|]. inv_ok.
  destruct (negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)) eqn:Henv;
    cbv iota in *; [reflexivity|]. inv_ok.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst;
    cbv iota in *; [|reflexivity]. inv_ok.
Qed.

(** The successful result, after the destination gate has passed. *)
Definition check_clock_getres_result (clkid tp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if w_is0 tp then check_ret_only eff (Z_to_bv 64 0) m []
  else match eff with
       | mkEffectU r [(a, bs)] [] [] [] [] =>
           if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp
              && clock_getres_resolution_b clkid bs
           then CheckOk m [] else CheckReject
       | _ => CheckReject
       end.

Lemma check_clock_getres_result_sound_ok : forall clkid tp eff m m' evs i,
  check_clock_getres_result clkid tp eff m = CheckOk m' evs ->
  clock_getres_result_spec clkid tp i m (Ok eff m' evs).
Proof.
  intros clkid tp [r ws zs us cs copyins] m m' evs i H.
  unfold check_clock_getres_result in H.
  unfold clock_getres_result_spec.
  destruct (w_is0 tp) eqn:Hnull.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->).
    unfold ret_only. apply pure_ok.
  - destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp
              && clock_getres_resolution_b clkid bs) eqn:Hok;
      [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hok as [Hok1 Hres].
    apply andb_true_iff in Hok1 as [Hr Ha].
    apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst.
    eapply bind_ok0; [apply (choose_ok _ bs); exact Hres|].
    apply pure_ok.
Qed.

Lemma check_clock_getres_result_no_unmodeled : forall clkid tp eff m,
  check_clock_getres_result clkid tp eff m <> CheckUnmodeled.
Proof.
  intros clkid tp eff m H.
  unfold check_clock_getres_result in H.
  destruct (w_is0 tp).
  - now apply check_ret_only_no_unmodeled in H.
  - destruct eff as [r ws zs us cs copyins].
    destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp
              && clock_getres_resolution_b clkid bs); discriminate.
Qed.

Lemma check_clock_getres_result_complete_ok : forall clkid tp eff m m' evs i,
  clock_getres_result_spec clkid tp i m (Ok eff m' evs) ->
  check_clock_getres_result clkid tp eff m = CheckOk m' evs.
Proof.
  intros clkid tp eff m m' evs i H.
  unfold clock_getres_result_spec in H.
  unfold check_clock_getres_result.
  destruct (w_is0 tp) eqn:Hnull.
  - unfold ret_only, pure in H. inversion H; subst.
    now apply check_ret_only_ok_iff.
  - sys_unfold; inv_ok. cbv iota. bool_true. reflexivity.
Qed.

Lemma clock_getres_result_no_unmodeled : forall clkid tp i m,
  ~ clock_getres_result_spec clkid tp i m Unmodeled.
Proof.
  intros clkid tp i m H.
  unfold clock_getres_result_spec in H.
  destruct (w_is0 tp).
  - unfold ret_only, pure in H. discriminate.
  - sys_unfold; inv_ok.
Qed.

Definition check_clock_getres (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if clock_getres_supported_b clkid then
    if clock_getres_dst_ok_b i tp then
      if clock_getres_alarm_b clkid
         && bv_eqb (eff_ret eff) (errno_ret EINVAL)
      then check_ret_only eff (errno_ret EINVAL) m []
      else check_clock_getres_result clkid tp eff m
    else CheckUnmodeled
  else if Z.eqb (bv_unsigned clkid) CLOCK_SGI_CYCLE
  then check_ret_only eff (errno_ret EINVAL) m []
  else CheckUnmodeled.

Lemma check_clock_getres_sound_ok : forall i clkid tp eff m m' evs,
  check_clock_getres i clkid tp eff m = CheckOk m' evs ->
  clock_getres_spec clkid tp i m (Ok eff m' evs).
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_getres in H.
  unfold clock_getres_spec.
  destruct (clock_getres_supported_b clkid) eqn:Hs.
  - eapply bind_ok0; [apply input_ok|]. cbv beta.
    destruct (clock_getres_dst_ok_b i tp) eqn:Hd; [|discriminate].
    destruct (clock_getres_alarm_b clkid) eqn:Ha.
    + cbn [andb] in H.
      destruct (bv_eqb (eff_ret eff) (errno_ret EINVAL)) eqn:Hr.
      * apply check_ret_only_ok_iff in H as (-> & -> & ->).
        apply alt_l. unfold err_ret, ret_only. apply pure_ok.
      * apply alt_r. now eapply check_clock_getres_result_sound_ok.
    + now eapply check_clock_getres_result_sound_ok.
  - destruct (Z.eqb (bv_unsigned clkid) CLOCK_SGI_CYCLE); [|discriminate].
    apply check_ret_only_ok_iff in H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok.
Qed.

Lemma check_clock_getres_sound_unmodeled : forall i clkid tp eff m,
  check_clock_getres i clkid tp eff m = CheckUnmodeled ->
  clock_getres_spec clkid tp i m Unmodeled.
Proof.
  intros i clkid tp eff m H.
  unfold check_clock_getres in H.
  unfold clock_getres_spec.
  destruct (clock_getres_supported_b clkid) eqn:Hs.
  - eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    destruct (clock_getres_dst_ok_b i tp) eqn:Hd;
      [|apply unmodeled_intro].
    destruct (clock_getres_alarm_b clkid) eqn:Ha.
    + cbn [andb] in H.
      destruct (bv_eqb (eff_ret eff) (errno_ret EINVAL)).
      * now apply check_ret_only_no_unmodeled in H.
      * now apply check_clock_getres_result_no_unmodeled in H.
    + now apply check_clock_getres_result_no_unmodeled in H.
  - destruct (Z.eqb (bv_unsigned clkid) CLOCK_SGI_CYCLE).
    + now apply check_ret_only_no_unmodeled in H.
    + apply unmodeled_intro.
Qed.

Lemma check_clock_getres_complete_ok : forall i clkid tp eff m m' evs,
  clock_getres_spec clkid tp i m (Ok eff m' evs) ->
  check_clock_getres i clkid tp eff m = CheckOk m' evs.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold clock_getres_spec in H.
  unfold check_clock_getres.
  destruct (clock_getres_supported_b clkid) eqn:Hs.
  - apply input_bind_ok_inv in H. cbv beta in H.
    destruct (clock_getres_dst_ok_b i tp) eqn:Hd; [|discriminate].
    destruct (clock_getres_alarm_b clkid) eqn:Ha.
    + unfold alt in H. destruct H as [H|H].
      * unfold err_ret, ret_only, pure in H. inversion H; subst.
        cbn [eff_ret]. rewrite bv_eqb_refl.
        now apply check_ret_only_ok_iff.
      * pose proof (check_clock_getres_result_complete_ok _ _ _ _ _ _ _ H)
          as Hcheck.
        destruct (bv_eqb (eff_ret eff) (errno_ret EINVAL)) eqn:Hr.
        -- apply bv_eqb_eq in Hr.
           unfold clock_getres_result_spec in H.
           destruct (w_is0 tp); sys_unfold; inv_ok;
             subst; change (bv_eqb (Z_to_bv 64 0) (errno_ret EINVAL))
               with false in Hr; discriminate.
        -- exact Hcheck.
    + exact (check_clock_getres_result_complete_ok clkid tp eff m m' evs i H).
  - destruct (Z.eqb (bv_unsigned clkid) CLOCK_SGI_CYCLE) eqn:H10; [|discriminate].
    unfold err_ret, ret_only, pure in H. inversion H; subst.
    now apply check_ret_only_ok_iff.
Qed.

Lemma check_clock_getres_complete_unmodeled : forall i clkid tp m eff,
  clock_getres_spec clkid tp i m Unmodeled ->
  check_clock_getres i clkid tp eff m = CheckUnmodeled.
Proof.
  intros i clkid tp m eff H.
  unfold clock_getres_spec in H.
  unfold check_clock_getres.
  destruct (clock_getres_supported_b clkid) eqn:Hs.
  - apply input_bind_unmodeled_inv in H. cbv beta in H.
    destruct (clock_getres_dst_ok_b i tp) eqn:Hd; [|reflexivity].
    destruct (clock_getres_alarm_b clkid) eqn:Ha.
    + unfold alt in H. destruct H as [H|H].
      * unfold err_ret, ret_only, pure in H. discriminate.
      * exfalso. exact (clock_getres_result_no_unmodeled clkid tp i m H).
    + exfalso. exact (clock_getres_result_no_unmodeled clkid tp i m H).
  - destruct (Z.eqb (bv_unsigned clkid) CLOCK_SGI_CYCLE); [|reflexivity].
    unfold err_ret, ret_only, pure in H. discriminate.
Qed.
