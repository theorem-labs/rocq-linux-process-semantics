(** * LinuxProcessSem.Checks.Sys.Kernel.Time.Hrtimer — the nanosleep (101) checker, and its proofs

    Mirrors [Sys/Kernel/Time/Hrtimer.v], which answers to Linux
    [kernel/time/hrtimer.c]: this file holds the checkers for the
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

(** nanosleep: an unreadable request, or one read from the vDSO pair,
    declines; an invalid one is -EINVAL; and otherwise BOTH outcomes are
    admissible, so the acceptor decides which arm it is being shown from
    the return value.

    THE REQUEST'S SECONDS FIELD GATES NOTHING.  A [tv_sec] at or
    above [Uapi.KTIME_SEC_MAX] does not decline here, and
    [Kernel.Time.Hrtimer.nanosleep_spec] says why it must not: the
    remainder the same spec may write reaches that band, and the
    standard retry loop feeds the remainder back as the next request.
    The conversion [ktime_set] performs lives in
    [Uapi.timespec_ktime] and is read by [nanosleep_clock], not by a
    guard.

    - 0 with no writes is the completed sleep, and carries the whole
      request into [m_clock], saturated at [Uapi.KTIME_MAX].
    - -EINTR is the interruption.  With a NULL [rmtp] it carries no
      write and moves nothing, the slept duration being unknowable;
      with a non-NULL one it MUST carry exactly one write at [rmtp]
      that [Kernel.Time.Hrtimer.nanosleep_rem_ok_b] admits, and carries
      the part of the request that provably elapsed into [m_clock].

    That last "must" is the sharp claim: with a remainder destination,
    an -EINTR and no write is REJECTED, because [do_nanosleep] reports
    success rather than an interruption when it has no positive
    remainder to write.

    AND EVERY ACCEPTED OUTCOME MUST CARRY THE COPY-IN.  The request
    reaches the kernel through [get_timespec64], so an effect that
    claims one of these outcomes without the 16-byte read at [rqtp] in
    its ledger describes a kernel that decided the call without looking
    at the request, and is rejected.  The requirement sits on the
    accepting arms only: every [CheckUnmodeled] verdict is
    reached before any effect is inspected and must stay reachable
    whatever ledger that effect carries, or
    [check_nanosleep_complete_unmodeled] would be false.

    THERE IS NO GATE ON THE MODEL'S CLOCK EITHER.  A sleep whose
    deadline would leave [ktime_t] is one Linux serves at a saturated
    deadline rather than refusing, so
    [Kernel.Time.Hrtimer.nanosleep_clock] clamps and this acceptor
    reads [m] only to compute the new clock and to find the vDSO pair.
    That is why the declines that remain — a request that is unreadable
    or read from the vDSO pair, and an unwritable [rmtp] — are the only
    ones. *)
Definition check_nanosleep (i : SyscallInput) (rqtp rmtp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match user_read i m rqtp (Z_to_bv 64 16) with
  | UFault => CheckUnmodeled
  | USpecial => CheckUnmodeled
  | UOk req =>
      if negb (timespec_valid_b req)
      then check_ret_only_copyins [(rqtp, 16%nat)] eff (errno_ret EINVAL) m []
      else if w_is0 rmtp
      then
        check_copyins [(rqtp, 16%nat)] eff
        (match eff with
         | mkEffectU r [] [] [] [] _ =>
             if bv_eqb r (Z_to_bv 64 0)
             then CheckOk (with_clock (nanosleep_clock (m_clock m) req []) m) []
             else if bv_eqb r (errno_ret EINTR) then CheckOk m []
             else CheckReject
         | _ => CheckReject
         end)
      else
        match read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16) with
        | None => CheckUnmodeled
        | Some _ =>
            check_copyins [(rqtp, 16%nat)] eff
            (match eff with
             | mkEffectU r [] [] [] [] _ =>
                 if bv_eqb r (Z_to_bv 64 0)
                 then CheckOk (with_clock (nanosleep_clock (m_clock m) req []) m) []
                 else CheckReject
             | mkEffectU r [(a, rem)] [] [] [] _ =>
                 if bv_eqb r (errno_ret EINTR) && bv_eqb a rmtp
                    && nanosleep_rem_ok_b rem
                 then CheckOk
                        (with_clock (nanosleep_clock (m_clock m) req rem) m) []
                 else CheckReject
             | _ => CheckReject
             end)
        end
  end.

(** Peeling [record_copyins] off the spec on the accepting side.  The
    acceptor has already forced the effect's ledger to be exactly the
    request's copy-in, so what is left to prove is the arm's body
    against the same effect with an empty ledger.  All four proofs
    below reach this step. *)
Local Lemma nanosleep_ledger_ok :
  forall rqtp spec i m ret ws zs us cs m' evs,
  spec i m (Ok (mkEffectU ret ws zs us cs []) m' evs) ->
  record_copyins [(rqtp, 16%nat)] spec i m
    (Ok (mkEffectU ret ws zs us cs [(rqtp, 16%nat)]) m' evs).
Proof.
  intros rqtp spec i m ret ws zs us cs m' evs H.
  exact (record_copyins_ok_empty [(rqtp, 16%nat)] spec i m
           (mkEffectU ret ws zs us cs []) m' evs eq_refl H).
Qed.

(** What the acceptor demands of the ledger, read back out of an
    acceptance.  Soundness needs it before it can peel
    [record_copyins], because the ledger has to be known before the
    effect can be split into the part the body produces and the part
    the wrapper prepends. *)
Local Lemma check_nanosleep_ok_copyins : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs ->
  eff_copyins eff = [(rqtp, 16%nat)].
Proof.
  intros i rqtp rmtp eff m m' evs H. unfold check_nanosleep in H.
  destruct (user_read i m rqtp (Z_to_bv 64 16)) as [req| |] eqn:Hrq;
    [|discriminate|discriminate].
  destruct (negb (timespec_valid_b req)) eqn:Hv.
  { unfold check_ret_only_copyins in H.
    destruct (check_ret_only (clear_copyins eff) (errno_ret EINVAL) m []);
      try discriminate.
    destruct (access_ranges_eqb (eff_copyins eff) [(rqtp, 16%nat)]) eqn:Hc;
      [|discriminate].
    now apply access_ranges_eqb_eq in Hc. }
  unfold check_copyins in H.
  destruct (w_is0 rmtp) eqn:Hrm.
  - destruct (access_ranges_eqb (eff_copyins eff) [(rqtp, 16%nat)]) eqn:Hc;
      [|discriminate].
    now apply access_ranges_eqb_eq in Hc.
  - destruct (read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16)) eqn:Hrm2;
      [|discriminate].
    destruct (access_ranges_eqb (eff_copyins eff) [(rqtp, 16%nat)]) eqn:Hc;
      [|discriminate].
    now apply access_ranges_eqb_eq in Hc.
Qed.

Lemma check_nanosleep_sound_ok : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs ->
  nanosleep_spec rqtp rmtp i m (Ok eff m' evs).
Proof.
  intros i rqtp rmtp eff m m' evs H.
  pose proof (check_nanosleep_ok_copyins _ _ _ _ _ _ _ H) as Hled.
  unfold check_nanosleep in H. unfold nanosleep_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (user_read i m rqtp (Z_to_bv 64 16)) as [req| |] eqn:Hrq;
    [|discriminate|discriminate]. cbv iota.
  destruct eff as [ret ws zs us cs copyins]. cbn in Hled. subst copyins.
  apply nanosleep_ledger_ok.
  destruct (negb (timespec_valid_b req)) eqn:Hv; cbv iota.
  { apply check_ret_only_copyins_ok_iff in H as (Heq & -> & ->).
    cbn in Heq. inversion Heq; subst. apply pure_ok. }
  cbv zeta.
  unfold check_copyins in H. cbn [eff_copyins] in H.
  rewrite access_ranges_eqb_refl in H. cbv iota in H.
  destruct (w_is0 rmtp) eqn:Hrm; cbv iota.
  - destruct ws as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:H0.
    + apply bv_eqb_eq in H0; subst ret. inversion H; clear H; subst.
      apply alt_l. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + destruct (bv_eqb ret (errno_ret EINTR)) eqn:HE; [|discriminate].
      apply bv_eqb_eq in HE; subst ret. inversion H; clear H; subst.
      apply alt_r. apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16)) eqn:Hrm2;
      [|discriminate]. cbv iota.
    destruct ws as [|[a rem] ws'].
    + destruct zs as [|? ?]; [|discriminate].
      destruct us as [|? ?]; [|discriminate].
      destruct cs as [|? ?]; [|discriminate].
      destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:H0; [|discriminate].
      apply bv_eqb_eq in H0; subst ret. inversion H; clear H; subst.
      apply alt_l. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + destruct ws' as [|? ?]; [|discriminate].
      destruct zs as [|? ?]; [|discriminate].
      destruct us as [|? ?]; [|discriminate].
      destruct cs as [|? ?]; [|discriminate].
      destruct (bv_eqb ret (errno_ret EINTR) && bv_eqb a rmtp
                && nanosleep_rem_ok_b rem) eqn:Hok; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in Hok as [Hok1 Hrem].
      apply andb_true_iff in Hok1 as [Hr Ha].
      apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst.
      apply alt_r.
      eapply bind_ok0; [apply (choose_ok _ rem); exact Hrem|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_nanosleep_sound_unmodeled : forall i rqtp rmtp eff m,
  check_nanosleep i rqtp rmtp eff m = CheckUnmodeled ->
  nanosleep_spec rqtp rmtp i m Unmodeled.
Proof.
  intros i rqtp rmtp eff m H.
  unfold check_nanosleep in H. unfold nanosleep_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (user_read i m rqtp (Z_to_bv 64 16)) as [req| |] eqn:Hrq;
    cbv iota; [|apply unmodeled_intro|apply unmodeled_intro]. cbv iota in H.
  apply record_copyins_unmodeled.
  destruct (negb (timespec_valid_b req)) eqn:Hv; cbv iota; cbv iota in H.
  { exfalso. now apply check_ret_only_copyins_no_unmodeled in H. }
  cbv zeta.
  unfold check_copyins in H.
  destruct (w_is0 rmtp) eqn:Hrm; cbv iota; cbv iota in H.
  - exfalso.
    destruct (access_ranges_eqb (eff_copyins eff) [(rqtp, 16%nat)]);
      [|discriminate].
    destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0)); [discriminate|].
    destruct (bv_eqb ret (errno_ret EINTR)); discriminate.
  - destruct (read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16)) eqn:Hrm2;
      cbv iota; [|apply unmodeled_intro].
    exfalso. cbv iota in H.
    destruct (access_ranges_eqb (eff_copyins eff) [(rqtp, 16%nat)]);
      [|discriminate].
    destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|[a rem] ws'].
    + destruct zs as [|? ?]; [|discriminate].
      destruct us as [|? ?]; [|discriminate].
      destruct cs as [|? ?]; [|discriminate].
      destruct (bv_eqb ret (Z_to_bv 64 0)); discriminate.
    + destruct ws' as [|? ?]; [|discriminate].
      destruct zs as [|? ?]; [|discriminate].
      destruct us as [|? ?]; [|discriminate].
      destruct cs as [|? ?]; [|discriminate].
      destruct (bv_eqb ret (errno_ret EINTR) && bv_eqb a rmtp
                && nanosleep_rem_ok_b rem); discriminate.
Qed.

Lemma check_nanosleep_complete_ok : forall i rqtp rmtp eff m m' evs,
  nanosleep_spec rqtp rmtp i m (Ok eff m' evs) ->
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs.
Proof.
  intros i rqtp rmtp eff m m' evs H.
  unfold nanosleep_spec in H. unfold check_nanosleep. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (user_read i m rqtp (Z_to_bv 64 16)) as [req| |] eqn:Hrq;
    hall Hrq; inv_ok.
  destruct (negb (timespec_valid_b req)) eqn:Hv; hall Hv; inv_ok.
  { unfold check_ret_only_copyins, clear_copyins, with_copyins, check_ret_only.
    cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
    rewrite bv_eqb_refl, access_ranges_eqb_refl. reflexivity. }
  destruct (w_is0 rmtp) eqn:Hrm; hall Hrm; inv_ok.
  all: try (destruct (read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16)) eqn:Hrm2;
            hall Hrm2; inv_ok).
  all: unfold check_copyins;
       cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins];
       rewrite access_ranges_eqb_refl; cbv iota.
  all: cbn [check_ret_only]; try rewrite bv_eqb_refl.
  all: try solve [ bool_true; reflexivity ].
  all: reflexivity.
Qed.

Lemma check_nanosleep_complete_unmodeled : forall i rqtp rmtp m eff,
  nanosleep_spec rqtp rmtp i m Unmodeled ->
  check_nanosleep i rqtp rmtp eff m = CheckUnmodeled.
Proof.
  intros i rqtp rmtp m eff H.
  unfold nanosleep_spec in H. unfold check_nanosleep. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (user_read i m rqtp (Z_to_bv 64 16)) as [req| |] eqn:Hrq;
    hall Hrq; inv_ok; [|reflexivity|reflexivity].
  destruct (negb (timespec_valid_b req)) eqn:Hv; hall Hv; inv_ok.
  destruct (w_is0 rmtp) eqn:Hrm; hall Hrm; inv_ok.
  destruct (read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16)) eqn:Hrm2;
    hall Hrm2; inv_ok; reflexivity.
Qed.
