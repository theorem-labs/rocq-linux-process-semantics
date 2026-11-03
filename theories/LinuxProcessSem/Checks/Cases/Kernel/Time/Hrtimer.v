(** * LinuxProcessSem.Checks.Cases.Kernel.Time.Hrtimer — worked examples over nanosleep (101)

    Mirrors [Sys/Kernel/Time/Hrtimer.v], which answers to Linux
    [kernel/time/hrtimer.c]: this file holds the worked examples for the
    syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    What is here is the whole of
    [m_clock] — how far a sleep carries the clock is model-internal
    state that reaches no trace at all — plus the request CEILING and
    the SATURATING deadline, both of which need a request or a clock 292
    years along and so are unreachable from either side, and the
    remainder shapes no truthful kernel writes. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.
(* [wmem_ts], [clock_model] and [ts_1s] are this subsystem's shared
   fixtures: sixteen writable bytes at 4096, a model whose clock reads a
   given nanosecond count, and one second as the kernel would write it.
   They are defined beside [clock_gettime]'s cases rather than
   duplicated here. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time
  Require Import PosixTimers.

(** Sixteen bytes of [bs] READABLE at [base], and nothing else — the
    [in_mem] counterpart of [wmem_ts].  [nanosleep] reads its request
    through [in_mem], where [clock_gettime] and [gettimeofday] read no
    input memory at all and can hand the checker an empty view. *)
Definition mem_at (base : Z) (bs : list byte) : word -> option byte :=
  fun a => if (base <=? bv_unsigned a)%Z
           then nth_error bs (Z.to_nat (bv_unsigned a - base))
           else None.

(** [nanosleep(8192, rmtp)] with [req] readable at 8192.  A non-NULL
    [rmtp] is passed as 4096, which [wmem_ts] makes wholly writable. *)
Definition nanosleep_input (rmtp : word) (req : list byte) : SyscallInput :=
  mkInput 101 [8192; rmtp; 0; 0; 0; 0] (mem_at 8192 req) wmem_ts.

(** Requests and remainders, each 16 bytes of [struct timespec]. *)
(** tv_sec = 0, tv_nsec = 0 — no time at all. *)
Definition ts_zero : list byte :=
  [0; 0; 0; 0; 0; 0; 0; 0] ++ [0; 0; 0; 0; 0; 0; 0; 0].
(** tv_sec = 0, tv_nsec = 250000000 — a quarter second. *)
Definition ts_250ms : list byte :=
  [0; 0; 0; 0; 0; 0; 0; 0] ++ [128; 178; 230; 14; 0; 0; 0; 0].
(** tv_sec = 0, tv_nsec = 1000 — one microsecond. *)
Definition ts_1us : list byte :=
  [0; 0; 0; 0; 0; 0; 0; 0] ++ [232; 3; 0; 0; 0; 0; 0; 0].
(** tv_sec = 0, tv_nsec = 51000 — 51 microseconds, which is one
    microsecond plus the default 50us of timer slack. *)
Definition ts_51us : list byte :=
  [0; 0; 0; 0; 0; 0; 0; 0] ++ [56; 199; 0; 0; 0; 0; 0; 0].

(** MODEL-INTERNAL STATE.  A completed sleep carries [m_clock] forward
    by the WHOLE request: the hrtimer's soft expiry is exactly now plus
    the request and a timer never fires early, so returning 0 means at
    least that much elapsed on the very clock [m_clock] tracks.
    Nothing about [m_clock] reaches a trace, so no run sees the
    advance directly; a run feels it only indirectly, through a
    later [clock_gettime] being judged against a clock a second further
    on.  [rmtp] is NULL here, the shape a program that does not care
    what was left passes. *)
Example nanosleep_completed_sleep_advances_the_clock :
  check_syscall (nanosleep_input 0 ts_1s)
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [] []))
    (clock_model 0)
  = CheckOk (clock_model 1000000000) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE.  With a NULL [rmtp] the interrupted arm has
    nowhere to report the remainder, so how much of the sleep elapsed is
    unknowable and the clock stays where it was.  This is the only
    accepted [nanosleep] outcome that does not move [m_clock], and the
    pair with the case above is what makes the distinction non-vacuous. *)
Example nanosleep_null_remainder_interruption_holds_the_clock :
  check_syscall (nanosleep_input 0 ts_1s)
    (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret EINTR) [] []))
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE.  The interrupted arm carries [m_clock] forward
    by the request LESS the reported remainder — a second requested with
    a quarter second left is three quarters of a second elapsed.  What
    the model records is the one-sided fact the kernel actually
    establishes, and it is invisible from outside for the same reason
    the case above is. *)
Example nanosleep_interruption_advances_by_the_difference :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
    (clock_model 0)
  = CheckOk (clock_model 750000000) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE, and the sharp one.  A remainder LARGER than
    the request is admissible, because [do_nanosleep] measures what is
    left against the HARD expiry and [hrtimer_nanosleep] sets that
    [current->timer_slack_ns] past the soft one — 50 microseconds by
    default.  So a one-microsecond sleep can report 51 microseconds
    remaining, and [nanosleep_rem_ok_b] deliberately does not bound the
    remainder by the request.  The advance is then floored at the
    clock's previous value rather than going negative: without the
    [Z.max (bv_unsigned prev)] in [nanosleep_clock] the difference would
    be -50000 and the clock would wrap to within 50 microseconds of
    2^64, turning a one-microsecond sleep into 584 years of recorded
    time.  This is the case that makes that [Z.max] non-vacuous, and no
    run can see it — the reported remainder is observable, the clock
    it moves is not. *)
Example nanosleep_remainder_past_the_request_floors_at_zero :
  check_syscall (nanosleep_input 4096 ts_1us)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_51us)] []))
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

(** The request at the ceiling, and the remainder that reaches it.
    [tv_sec = KTIME_SEC_MAX] is where [ktime_set] stops converting; one
    second below it is the control that shows it still does. *)
(** tv_sec = 9223372036 = [KTIME_SEC_MAX], tv_nsec = 0. *)
Definition ts_ceiling : list byte :=
  [4; 125; 193; 37; 2; 0; 0; 0] ++ [0; 0; 0; 0; 0; 0; 0; 0].
(** tv_sec = 9223372035, tv_nsec = 0 — one second below the ceiling. *)
Definition ts_below_ceiling : list byte :=
  [3; 125; 193; 37; 2; 0; 0; 0] ++ [0; 0; 0; 0; 0; 0; 0; 0].
(** tv_sec = 2^63, tv_nsec = 0 — the first second [timespec64_valid]
    refuses, reading the field as the [s64] it is. *)
Definition ts_neg_sec : list byte :=
  [0; 0; 0; 0; 0; 0; 0; 128] ++ [0; 0; 0; 0; 0; 0; 0; 0].

(** MODEL-INTERNAL STATE.
    A request AT [KTIME_SEC_MAX] is ANSWERED, and a completed sleep
    carries [m_clock] to [Uapi.KTIME_MAX].  That is what Linux serves:
    [timespec64_to_ktime] is [ktime_set] (include/linux/ktime.h at
    v6.18.46), whose [if (unlikely(secs >= KTIME_SEC_MAX)) return
    KTIME_MAX;] hands [hrtimer_nanosleep] the end of [ktime_t] rather
    than a product, and the sleep that follows is an ordinary
    interruptible one toward that deadline.

    A real run cannot reach this from either side — issuing the call
    really would park the process for 292 years —
    so the whole of the arm is here.

    A decline here would not be conservative.  [nanosleep_rem_ok_b]
    admits a remainder with
    [tv_sec = KTIME_SEC_MAX] (the case below exhibits one), and the
    standard retry loop
    [while (nanosleep(&ts, &ts) == -1 && errno == EINTR);] — dropbear's
    auth delay — hands the remainder back as the next request.  So one
    admissible environment choice would make the NEXT call unmodeled, and
    [Equivalence.modeled] being the negation of an existential over
    resolutions, that one resolution would cost the whole program its
    [modeled] status on every input on which it slept. *)
Example nanosleep_request_at_the_ceiling_sleeps_to_ktime_max :
  check_syscall (nanosleep_input 0 ts_ceiling)
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [] []))
    (clock_model 0)
  = CheckOk (clock_model (2 ^ 63 - 1)) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE — the control, and the reason the case above is
    not vacuous.  One second BELOW the ceiling [ktime_set] converts
    rather than saturating, so the recorded clock is the plain product
    9223372035 * 10^9 and not [KTIME_MAX].  The two requests are one
    second apart and the clocks they record are 1854775807 ns apart:
    that gap is exactly [ktime_set]'s early return firing, and a
    [timespec_ktime] that always converted, or always saturated, would
    fail one of the pair. *)
Example nanosleep_request_below_the_ceiling_converts :
  check_syscall (nanosleep_input 0 ts_below_ceiling)
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [] []))
    (clock_model 0)
  = CheckOk (clock_model 9223372035000000000) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE — the band's TOP, and the case that stops the
    two above from being read as a claim about one value.  The band
    [ktime_set] saturates over is [[KTIME_SEC_MAX, 2^63)] of whole
    seconds, and every other case here sits at its BOTTOM: a spec that
    judged [tv_sec = KTIME_SEC_MAX] and went on declining everything
    above it would satisfy all of them, and would still cost the retry
    loop nothing, since [nanosleep_rem_ok_b] cannot spell a remainder
    past the bottom.  The largest [tv_sec] [timespec64_valid] accepts is
    2^63 - 1, one below the word that reads as negative, and it sleeps
    to [KTIME_MAX] exactly as the bottom of the band does — [ktime_set]
    tests [secs >= KTIME_SEC_MAX] and returns the same constant across
    the whole band. *)
(** tv_sec = 2^63 - 1, tv_nsec = 999999999 — the largest request
    [timespec64_valid] accepts, and the top of the saturating band. *)
Definition ts_top_of_band : list byte :=
  [255; 255; 255; 255; 255; 255; 255; 127]
  ++ [255; 201; 154; 59; 0; 0; 0; 0].

Example nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max :
  check_syscall (nanosleep_input 0 ts_top_of_band)
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [] []))
    (clock_model 0)
  = CheckOk (clock_model (2 ^ 63 - 1)) [].
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the same rejection at
    the top of the band as at its bottom.  An -EINTR reporting a
    remainder of exactly zero is refused wherever the request sits, and
    with this pair the whole band is judged in both directions rather
    than merely answered in one. *)
Example nanosleep_at_the_top_of_the_band_zero_remainder_rejected :
  check_syscall (nanosleep_input 4096 ts_top_of_band)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE.  The ceiling request INTERRUPTED: the clock
    moves to the deadline the kernel armed — [KTIME_MAX] — less the
    reported remainder, exactly as at any smaller request.  A quarter
    second left leaves [KTIME_MAX - 250000000]. *)
Example nanosleep_request_at_the_ceiling_interrupted :
  check_syscall (nanosleep_input 4096 ts_ceiling)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
    (clock_model 0)
  = CheckOk (clock_model 9223372036604775807) [].
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and this is the
    REJECTION a decline at the ceiling would cost: a spec that answered
    [CheckUnmodeled] there for EVERY effect would refuse nothing.  The
    -EINTR reporting a remainder of exactly zero is REFUSED, as it is at
    every other request. *)
Example nanosleep_at_the_ceiling_zero_remainder_rejected :
  check_syscall (nanosleep_input 4096 ts_ceiling)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the other half of the
    band, and the boundary the ceiling arm must NOT move.  One
    second past the ceiling is still inside [timespec64_valid]; 2^63
    seconds is not, because [tv_sec] is signed and that word reads as
    negative.  So the answer there is -EINVAL and not a sleep, and
    judging the ceiling does not widen the band that answers.  Without
    this case a [timespec_valid_b] weakened alongside the gate would go
    unnoticed. *)
Example nanosleep_request_at_two_to_the_63_is_einval :
  check_syscall (nanosleep_input 4096 ts_neg_sec)
    (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret EINVAL) [] []))
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder AT the
    ceiling, which is the value that would poison the next call if a
    request at the ceiling declined.
    [nanosleep_rem_ok_b] admits it: 9223372036 * 10^9 is 854775808 ns
    below [CLOCK_NS_ENVELOPE], so the envelope conjunct passes, and the
    other three do too.  The clock does not move — the request was a
    second and the remainder is 292 years, so the difference is negative
    and [Z.max prev] holds it — which is the [nanosleep_clock] floor
    doing its job at the top of the range rather than the bottom.

    Read this case together with the request cases above: THIS is the
    remainder, THAT is what the next call does with it. *)
Example nanosleep_remainder_at_the_ceiling_admitted :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_ceiling)] []))
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

(** UNIVERSALLY QUANTIFIED, and the pinning test for the retry loop.
    EVERY remainder this spec may write is a request the same spec
    JUDGES: given the destination the loop reuses, no [rem] that
    [nanosleep_rem_ok_b] admits can make the next call decline.  The
    two hypotheses are the loop's own, not extra assumptions —
    [while (nanosleep(&ts, &ts) == -1 && errno == EINTR);] passes the
    remainder back as the request, and it passes the same pointer as
    both, so the destination it hands the second call is one the first
    call already found writable.  The disjunction covers the other
    spelling, where [rmtp] is NULL and no remainder is reported at all.
    Both hypotheses are on the bare walk and not on
    [State.copy_bytes_map], and the statement keeps that strength: a
    range [access_ok] refuses is answered with -EFAULT at either
    pointer, never declined, so the range test cannot reopen the hole.

    THE STATEMENT IS A NON-DECLINE, not an acceptance, on purpose: it
    must hold for EVERY effect, and most effects at a given input are
    rejected.  What it rules out is the third verdict — the one that
    escapes through [Equivalence]'s unmodeled arm and takes the whole
    program's [modeled] status with it.

    Nothing else in the tree states this.  The concrete cases above pin
    one remainder value and one request value; this pins that no value
    in between them, or beyond, reopens the hole. *)
(** [bytes_le_to_Z] never decodes to a negative number, which is what
    turns [nanosleep_rem_ok_b]'s bound on the TOTAL into a bound on
    [tv_sec] alone.  [Common.PropExec] proves the same fact, and is not
    in this file's import closure. *)
Local Lemma bytes_le_to_Z_nonneg' : forall bs, (0 <= bytes_le_to_Z bs)%Z.
Proof.
  induction bs as [|b bs IH]; cbn; [lia|].
  apply Z.lor_nonneg. split.
  - pose proof (bv_unsigned_in_range _ b). lia.
  - apply Z.shiftl_nonneg. exact IH.
Qed.

Local Lemma timespec_ns_nonneg : forall bs, (0 <= timespec_ns bs)%Z.
Proof.
  intro bs. unfold timespec_ns, tv_sec_of, tv_frac_of.
  pose proof (bytes_le_to_Z_nonneg' (firstn 8 bs)).
  pose proof (bytes_le_to_Z_nonneg' (skipn 8 bs)). lia.
Qed.

Local Lemma timespec_ktime_nonneg : forall bs, (0 <= timespec_ktime bs)%Z.
Proof.
  intro bs. unfold timespec_ktime.
  destruct (tv_sec_of bs <? KTIME_SEC_MAX)%Z; [apply timespec_ns_nonneg|].
  unfold KTIME_MAX. change (2 ^ 63)%Z with 9223372036854775808%Z. lia.
Qed.

(** UNIVERSALLY QUANTIFIED, and the machine-checkable proxy for the one
    thing [nanosleep_clock]'s prose claims: that what it records is a
    LOWER bound on the real [CLOCK_MONOTONIC].  The full statement is
    not expressible here — the real clock is not a term in this
    development, and the argument that a timer never fires before its
    soft expiry is kernel prose, not Rocq.  What IS expressible is the
    model-side half of it, and this is that half: the recorded clock
    never runs past the deadline the kernel armed, which
    [nanosleep_clock] computes as [Z.min (prev + timespec_ktime req)
    KTIME_MAX].

    Both saturating arms land on that bound, from a clock the
    model may have anywhere below the envelope, so it is worth having
    checked rather than argued.  It is also the step the spec's
    "the FIRST saturation is not load-bearing" paragraph rests on:
    NOTHING of the shape [Z.min _ KTIME_MAX] exceeds [KTIME_MAX], which
    is the armed deadline throughout the saturating band, so reading the
    request as a plain product would still be sound — it would just be
    less exact.

    The remaining gap, and it is a real one: this is a fact about one
    call, not an invariant of the model.  Nothing in the tree says
    every arm preserves [m_clock < CLOCK_NS_ENVELOPE]; the two arms
    that move the clock at all are this one and
    [Kernel.Time.PosixTimers.clock_gettime_spec], and each argues its
    own bound in prose.  No model invariant states it. *)
Lemma nanosleep_clock_at_most_the_armed_deadline : forall prev req rem,
  (bv_unsigned prev <= KTIME_MAX)%Z ->
  (bv_unsigned (nanosleep_clock prev req rem)
     <= Z.min (bv_unsigned prev + timespec_ktime req) KTIME_MAX)%Z.
Proof.
  intros prev req rem Hprev.
  pose proof (bv_unsigned_in_range 64 prev) as Hrange.
  pose proof (timespec_ktime_nonneg req) as Hk.
  pose proof (timespec_ns_nonneg rem) as Hr.
  unfold nanosleep_clock. unfold KTIME_MAX in *.
  change (2 ^ 63)%Z with 9223372036854775808%Z in *.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  lia.
Qed.

(** UNIVERSALLY QUANTIFIED — the corollary [nanosleep_spec] needs to
    carry no envelope gate of its own.  A clock inside the band
    [Kernel.Time.PosixTimers.clock_gettime_spec] ANSWERS in is still
    inside it after any sleep, whatever the request and whatever the
    remainder, because the deadline is clamped at [KTIME_MAX] and that
    is [CLOCK_NS_ENVELOPE - 1].  Without this a sleep could park
    [m_clock] where the very next monotonic read declines; the
    saturating deadline avoids that trap by one nanosecond. *)
Lemma nanosleep_clock_under_the_envelope : forall prev req rem,
  (bv_unsigned prev < CLOCK_NS_ENVELOPE)%Z ->
  (bv_unsigned (nanosleep_clock prev req rem) < CLOCK_NS_ENVELOPE)%Z.
Proof.
  intros prev req rem Hprev.
  pose proof (nanosleep_clock_at_most_the_armed_deadline prev req rem) as H.
  unfold CLOCK_NS_ENVELOPE, KTIME_MAX in *.
  change (2 ^ 63)%Z with 9223372036854775808%Z in *.
  assert (Hle : (bv_unsigned prev <= 9223372036854775807)%Z) by lia.
  specialize (H Hle). lia.
Qed.

Lemma nanosleep_admissible_remainder_is_a_judged_request :
  forall i rqtp rmtp eff m rem,
    read_bytes_map (in_mem i) rqtp (Z_to_bv 64 16) = Some rem ->
    nanosleep_rem_ok_b rem = true ->
    (w_is0 rmtp = true
     \/ read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16) <> None) ->
    check_nanosleep i rqtp rmtp eff m <> CheckUnmodeled.
Proof.
  intros i rqtp rmtp eff m rem Hread Hrem Hdest.
  assert (Hvalid : timespec_valid_b rem = true).
  { unfold nanosleep_rem_ok_b in Hrem.
    apply andb_true_iff in Hrem as [Hrem Henv].
    apply andb_true_iff in Hrem as [Hrem _].
    apply andb_true_iff in Hrem as [_ Hfrac].
    apply Z.ltb_lt in Henv.
    pose proof (bytes_le_to_Z_nonneg' (skipn 8 rem)) as Hnn.
    unfold timespec_valid_b. rewrite Hfrac, andb_true_r.
    apply Z.ltb_lt.
    unfold timespec_ns, CLOCK_NS_ENVELOPE, tv_sec_of, tv_frac_of in *.
    change (2 ^ 63)%Z with 9223372036854775808%Z in *. lia. }
  intro Hc. unfold check_nanosleep in Hc.
  destruct (access_okb rqtp 16) eqn:Hok.
  2:{ rewrite (copy_bytes_map_refused (in_mem i) rqtp 16 Hok) in Hc.
      cbv iota in Hc. try rewrite Hok in Hc. cbn [negb] in Hc. cbv iota in Hc.
      now apply check_ret_only_no_unmodeled in Hc. }
  rewrite (copy_bytes_map_accepted (in_mem i) rqtp 16 Hok) in Hc.
  rewrite Hread, Hvalid in Hc. cbn [negb] in Hc. cbv iota in Hc.
  destruct eff as [ret ws zs us cs cp].
  destruct (w_is0 rmtp) eqn:Hw; cbv iota in Hc.
  - unfold check_copyins in Hc.
    destruct (access_ranges_eqb (eff_copyins _) [(rqtp, 16%nat)]);
      [|discriminate].
    destruct ws as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0)); [discriminate|].
    destruct (bv_eqb ret (errno_ret EINTR)); discriminate.
  - destruct Hdest as [Hz|Hd]; [rewrite Hz in Hw; discriminate|].
    destruct (access_okb rmtp 16) eqn:Hok2.
    2:{ rewrite (copy_bytes_map_refused (in_wmem i) rmtp 16 Hok2) in Hc.
        cbv iota in Hc. try rewrite Hok2 in Hc. cbn [negb] in Hc. cbv iota in Hc.
        unfold check_copyins in Hc.
        destruct (access_ranges_eqb (eff_copyins _) [(rqtp, 16%nat)]);
          [|discriminate].
        destruct ws as [|? ?]; [|discriminate].
        destruct zs as [|? ?]; [|discriminate].
        destruct us as [|? ?]; [|discriminate].
        destruct cs as [|? ?]; [|discriminate].
        destruct (bv_eqb ret (Z_to_bv 64 0)); [discriminate|].
        destruct (bv_eqb ret (errno_ret EFAULT)); discriminate. }
    rewrite (copy_bytes_map_accepted (in_wmem i) rmtp 16 Hok2) in Hc.
    destruct (read_bytes_map (in_wmem i) rmtp (Z_to_bv 64 16)) eqn:Hr2;
      [|now apply Hd]. cbv iota in Hc.
    unfold check_copyins in Hc.
    destruct (access_ranges_eqb (eff_copyins _) [(rqtp, 16%nat)]);
      [|discriminate].
    destruct ws as [|[a r'] ws'].
    + destruct zs as [|? ?]; [|discriminate].
      destruct us as [|? ?]; [|discriminate].
      destruct cs as [|? ?]; [|discriminate].
      destruct (bv_eqb ret (Z_to_bv 64 0)); discriminate.
    + destruct ws' as [|? ?]; [|discriminate].
      destruct zs as [|? ?]; [|discriminate].
      destruct us as [|? ?]; [|discriminate].
      destruct cs as [|? ?]; [|discriminate].
      destruct (bv_eqb ret (errno_ret EINTR) && bv_eqb a rmtp
                && nanosleep_rem_ok_b r'); discriminate.
Qed.

(** MODEL-INTERNAL STATE.  A
    clock already within a second of the top of [ktime_t]'s range
    ANSWERS a one-second sleep, recording the saturated deadline
    [Uapi.KTIME_MAX] rather than a sum the type cannot hold.  That is
    what Linux does: [__hrtimer_start_range_ns] converts the relative
    request with [ktime_add_safe], which replaces an overflowing sum
    with [ktime_set(KTIME_SEC_MAX, 0)] — [KTIME_MAX] — and sleeps to
    THAT deadline rather than reporting an error.

    A decline here would not be
    merely conservative: [PosixTimers.clock_gettime_spec] records
    whatever monotonic reading the ENVIRONMENT chooses, bounded only by
    [timespec_ok_b]'s [< 2^63], so a single [clock_gettime] from
    [init_model] could put [m_clock] here and the next sleep of one
    nanosecond would decline.  [Equivalence.modeled] is the negation of an
    existential over resolutions, so that one resolution would cost the
    whole program its [modeled] status — for ANY program that reads the
    monotonic clock and then sleeps, which is dropbear's shape.

    Note the recorded value is [2^63 - 1] and not [2^63]: the
    saturation constant is [KTIME_MAX], because [ktime_set]'s early
    return tests [secs >= KTIME_SEC_MAX] and so fires on the very value
    [ktime_add_safe] passes it.  One nanosecond, and it is the
    nanosecond that keeps [m_clock] inside the band
    [clock_gettime_spec] answers in. *)
Example nanosleep_clock_near_envelope_clamps :
  check_syscall (nanosleep_input 0 ts_1s)
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [] []))
    (clock_model (2 ^ 63 - 1000000000))
  = CheckOk (clock_model (2 ^ 63 - 1)) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE — the control for the case above, and the
    reason it is not vacuous.  The same one-second sleep against a
    clock two seconds below the ceiling does NOT clamp: the sum fits,
    so the recorded value is the plain [prev + request].  Without this
    pair a [nanosleep_clock] that clamped everything to [KTIME_MAX]
    would satisfy the case above. *)
Example nanosleep_clock_below_the_ceiling_does_not_clamp :
  check_syscall (nanosleep_input 0 ts_1s)
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [] []))
    (clock_model (2 ^ 63 - 2000000000))
  = CheckOk (clock_model (2 ^ 63 - 1000000000)) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE, and the case that pins WHERE the remainder is
    subtracted.  A saturating one-second sleep interrupted with one
    microsecond left records [KTIME_MAX - 1000], not [prev + request -
    remainder].  The order matters because the two disagree by more
    than the whole envelope here.  A [nanosleep_clock] that subtracted
    BEFORE clamping would compute [Z.min (prev + 10^9 - 1000)
    KTIME_MAX], which is [KTIME_MAX] outright, losing the microsecond.
    One that did not clamp at all would record
    [prev + 10^9 - 1000 = 2^63 + 999997000] — no wrap, since that is
    well under 2^64, but ABOVE [CLOCK_NS_ENVELOPE], which is the band
    [PosixTimers.clock_gettime_spec] declines in.  So the unclamped
    spelling would put the clock somewhere the very next monotonic read
    is [unmodeled], reintroducing one call later exactly the existential
    decline the clamp exists to prevent.  Keeping [m_clock]
    inside [clock_gettime]'s answering band is the clamp's job as much
    as faithfulness is.

    The soundness argument is [nanosleep_spec]'s: the kernel armed
    [node.expires] at the saturated deadline, [hrtimer_expires_remaining]
    measures the remainder against THAT, so the wake time is the
    saturated deadline less the remainder — never [prev + request] less
    it, because the sleep the kernel ran was shorter than the one asked
    for. *)
Example nanosleep_saturated_deadline_less_the_remainder :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_1us)] []))
    (clock_model (2 ^ 63 - 2000))
  = CheckOk (clock_model (2 ^ 63 - 1001)) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE — the [Z.max prev] floor, in its SECOND form.
    The floor already had a case above, where a remainder exceeding the
    request drove the difference negative.  This is the other way it
    can fire, and it needs the clamp to exist at all: a saturating
    sleep interrupted with a quarter second left leaves
    [KTIME_MAX - 250000000], which is BELOW a clock sitting 1000 ns
    from the ceiling.  The clock holds where it was rather than
    stepping back a quarter second.

    Nothing else in the tree separates [Z.max prev] from [Z.max 0]
    applied to the subtraction: with the clock at 0 the two agree, and
    only a clock near the ceiling makes [KTIME_MAX - rem] fall below
    [prev]. *)
Example nanosleep_saturated_deadline_never_steps_the_clock_back :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
    (clock_model (2 ^ 63 - 1000))
  = CheckOk (clock_model (2 ^ 63 - 1000)) [].
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and this is the
    REJECTION a decline near the ceiling would cost.  A spec that
    answered [CheckUnmodeled] there for EVERY effect would refuse
    nothing: a lying kernel's impossible answers would be declined
    rather than rejected, and a decline is not a rejection — it admits
    the step under [Equivalence]'s unmodeled escape instead of ruling it
    out.  With the clamp in place the same [-EINTR] reporting a
    remainder of exactly zero is REFUSED at a clock near the ceiling,
    exactly as it is at a clock of 0.

    So the clamp gives the model reach in BOTH directions: it models a
    trace Linux really produces, and it rejects impossible traces in
    this band. *)
Example nanosleep_near_the_ceiling_zero_remainder_rejected :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
    (clock_model (2 ^ 63 - 1000000000)) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the mirror of the
    case above, at the ceiling.  A completed sleep that also writes a
    remainder is refused near the envelope too.  Together the two pin
    that the band near the ceiling is fully judged rather
    than waved through. *)
Example nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [(4096, ts_250ms)] []))
    (clock_model (2 ^ 63 - 1000000000)) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  An -EINTR reporting
    a remainder of exactly zero is REFUSED.  [do_nanosleep] computes
    what is left and, when that is at or below zero, returns 0 having
    written nothing — the deadline has passed, so the call is a
    completed sleep and is reported as one.  A remainder of [{0, 0}] is
    therefore a shape no kernel produces, and [nanosleep_rem_ok_b]'s
    strict positivity is what refuses it. *)
Example nanosleep_zero_remainder_rejected :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's
    ENVELOPE conjunct, which nothing else reaches.  A remainder of
    9223372037 seconds is normalized ([tv_nsec = 0]), sixteen bytes
    long and strictly positive, so it fails [nanosleep_rem_ok_b]'s
    fourth conjunct ALONE and the rejection attributes to it. *)
Definition ts_over_envelope : list byte :=   (* 9223372037 s: past 2^63 ns *)
  [5; 125; 193; 37; 2; 0; 0; 0] ++ [0; 0; 0; 0; 0; 0; 0; 0].

Example nanosleep_remainder_past_the_envelope_rejected :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_over_envelope)] []))
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVELOPE CONJUNCT'S BOUNDARY, one nanosecond either side.
    [ts_over_envelope] above sits a whole second past the boundary and
    so does not locate it; the pair below does.

    [KTIME_MAX] nanoseconds — 9223372036 s and 854775807 ns — is the
    LARGEST remainder [nanosleep_rem_ok_b] admits, and the request here
    is a microsecond, so the difference is 292 years negative and
    [Z.max prev] holds the clock at 0. *)
Definition ts_ktime_max : list byte :=      (* 9223372036 s, 854775807 ns *)
  [4; 125; 193; 37; 2; 0; 0; 0] ++ [255; 215; 242; 50; 0; 0; 0; 0].

Example nanosleep_remainder_of_exactly_ktime_max_admitted :
  check_syscall (nanosleep_input 4096 ts_1us)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_ktime_max)] []))
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — ONE NANOSECOND
    further.  9223372036 s and 854775808 ns is 2^63 exactly, which is
    [CLOCK_NS_ENVELOPE] and not below it, so the fourth conjunct's
    strict [<] refuses it and the other three still pass.  Without this
    twin the case above would be satisfied by a bound of [<=] as
    happily as by [<]. *)
Definition ts_at_envelope : list byte :=    (* 9223372036 s, 854775808 ns *)
  [4; 125; 193; 37; 2; 0; 0; 0] ++ [0; 216; 242; 50; 0; 0; 0; 0].

Example nanosleep_remainder_of_exactly_the_envelope_rejected :
  check_syscall (nanosleep_input 4096 ts_1us)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_at_envelope)] []))
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's
    LENGTH conjunct, on its own.  Eight bytes decoding to
    [tv_sec = 1]: [tv_frac_of] of the empty tail is 0, so the reading
    is normalized, and [timespec_ns] is 10^9, positive and far under
    the envelope.  Only the length is wrong.

    This is the shape a truncating kernel would produce. *)
Definition ts_half : list byte :=            (* 8 bytes: tv_sec = 1 *)
  [1; 0; 0; 0; 0; 0; 0; 0].

Example nanosleep_half_a_remainder_rejected :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(4096, ts_half)] []))
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the mirror.  A
    completed sleep that ALSO writes a remainder is refused.  The kernel
    reaches [nanosleep_copyout] only on the interrupted path, so a
    return of 0 and a write at [rmtp] cannot both happen; admitting the
    pair would let a lying kernel move [m_clock] by the whole request
    while claiming a remainder against it.  The remainder written here
    is a PERFECTLY VALID one, which is what makes the case attribute:
    the only thing wrong with this effect is that a completed sleep
    carries it. *)
Example nanosleep_completed_sleep_with_a_remainder_rejected :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [(4096, ts_250ms)] []))
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the LEDGER, which
    every case above carries and none of them pins.  The kernel reads
    the request with [get_timespec64] before it decides anything, so
    every outcome [nanosleep] can reach has already consumed those
    sixteen bytes at [rqtp].  An effect that is otherwise the accepted
    completed sleep, but claims to have decided without reading the
    request, describes a kernel that cannot exist, and is refused.

    Without this case the [record_copyins] in [nanosleep_spec] would be
    unfalsifiable from the example side: every other case here would
    still pass with the ledger dropped from both the spec and the
    acceptor. *)
Example nanosleep_missing_copyin_rejected :
  check_syscall (nanosleep_input 0 ts_1s) (mkEffect 0 [] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** And the ledger has to name the REQUEST.  Sixteen bytes recorded at
    [rmtp] — the remainder destination, which [nanosleep] writes and
    never reads — is the right width at the wrong address, and is
    refused for that alone.  This is what separates an acceptor that
    compares the whole range from one that only counts bytes. *)
Example nanosleep_copyin_at_the_wrong_pointer_rejected :
  check_syscall (nanosleep_input 4096 ts_1s)
    (with_copyins [(4096, 16%nat)] (mkEffect 0 [] []))
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(* =========================================================================
   THE TWO TIME POINTERS THAT WALKED OFF THE TOP OF THE ADDRESS SPACE

   [nanosleep_spec] read [rqtp] and tested [rmtp] with
   [State.read_bytes_map] bare, and that walk WRAPS at 2^64
   ([State.copy_bytes_map]'s note).  A pointer in the last sixteen bytes
   of the address space read the bytes below the wrap and then the bytes
   from 0, said [Some], and the arm ANSWERED: a request there was slept
   on, and an interruption wrote its remainder there.  Both now go
   through [State.copy_bytes_map], and [Checks.Cases.Net.Socket]'s wrap
   groups are the shape these take.

   EACH GROUP IS THREE EXAMPLES.  The wrapping call is judged by the
   range test; a NEIGHBOURING ordinary call at the top of what
   [State.access_okb] accepts is still answered, so the guard is not a
   blanket refusal of high addresses; and the bare walk is shown reading
   the wrapped range back, so the refusal cannot be passing because the
   memory stopped short.  Every memory maps EXACTLY its own sixteen
   bytes and nothing else.
   ========================================================================= *)

(* ---- the request, [rqtp] ------------------------------------------------ *)

(** Eight bytes below the top and eight from 0, all zero: the request
    decodes as [{0, 0}], which [timespec_valid_b] accepts, so before the
    guard this call slept and returned 0. *)
Definition nanosleep_wrap_rqtp : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition nanosleep_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 8)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Definition nanosleep_wrap_rqtp_input : SyscallInput :=
  mkInput 101 [nanosleep_wrap_rqtp; 0; 0; 0; 0; 0]
    nanosleep_wrap_mem (fun _ => None).

Example nanosleep_wrap_rqtp_would_pass_the_bare_walk :
  read_bytes_map nanosleep_wrap_mem nanosleep_wrap_rqtp (Z_to_bv 64 16) <> None.
Proof. vm_compute. discriminate. Qed.

(** -EFAULT with an EMPTY ledger is the answer: [get_timespec64]'s
    [copy_from_user] (kernel/time/time.c) refuses the range before a
    byte moves, and [SYSCALL_DEFINE2(nanosleep)] (kernel/time/hrtimer.c)
    returns that before it validates or sleeps.  Refused: the completed
    sleep the bare walk admitted, and the -EFAULT claiming the request
    was read. *)
Example nanosleep_wrapping_rqtp_is_efault :
  check_syscall nanosleep_wrap_rqtp_input
    (mkEffect (errno_ret EFAULT) [] []) (clock_model 0)
  = CheckOk (clock_model 0) []
  /\ check_syscall nanosleep_wrap_rqtp_input
       (with_copyins [(nanosleep_wrap_rqtp, 16%nat)] (mkEffect 0 [] []))
       (clock_model 0)
     = CheckReject
  /\ check_syscall nanosleep_wrap_rqtp_input
       (with_copyins [(nanosleep_wrap_rqtp, 16%nat)]
          (mkEffect (errno_ret EFAULT) [] []))
       (clock_model 0)
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** THE NEIGHBOUR: the last sixteen bytes [State.access_okb] accepts,
    holding one second.  The sleep is answered with the copy-in ledger
    and carries the clock a second on, and -EFAULT is refused there. *)
Definition nanosleep_top_rqtp : word := Z_to_bv 64 (TASK_SIZE - 16).

Definition nanosleep_top_rqtp_input : SyscallInput :=
  mkInput 101 [nanosleep_top_rqtp; 0; 0; 0; 0; 0]
    (mem_at (TASK_SIZE - 16) ts_1s) (fun _ => None).

Example nanosleep_rqtp_at_the_top_still_sleeps :
  check_syscall nanosleep_top_rqtp_input
    (with_copyins [(nanosleep_top_rqtp, 16%nat)] (mkEffect 0 [] []))
    (clock_model 0)
  = CheckOk (clock_model 1000000000) []
  /\ check_syscall nanosleep_top_rqtp_input
       (mkEffect (errno_ret EFAULT) [] []) (clock_model 0)
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- the remainder destination, [rmtp] ---------------------------------- *)

(** The request is the ordinary one at 8192; [rmtp] is eight bytes below
    the top and its sixteen bytes wrap onto the eight from 0. *)
Definition nanosleep_wrap_rmtp : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition nanosleep_wrap_wmem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 8)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Definition nanosleep_wrap_rmtp_input : SyscallInput :=
  mkInput 101 [8192; nanosleep_wrap_rmtp; 0; 0; 0; 0]
    (mem_at 8192 ts_1s) nanosleep_wrap_wmem.

Example nanosleep_wrap_rmtp_would_pass_the_bare_walk :
  read_bytes_map nanosleep_wrap_wmem nanosleep_wrap_rmtp (Z_to_bv 64 16)
    <> None.
Proof. vm_compute. discriminate. Qed.

(** [put_timespec64]'s [copy_to_user] (kernel/time/time.c) refuses the
    range, so an interruption is [nanosleep_copyout]'s -EFAULT with
    nothing written and the clock held (kernel/time/hrtimer.c), and a
    completed sleep, which never reaches the copy, is still 0.  Both are
    accepted, each with the request's ledger, since the request WAS
    read.  Refused: the -EINTR with a remainder written at the wrapping
    [rmtp], which the bare walk admitted, and the -EFAULT without the
    request's ledger. *)
Example nanosleep_wrapping_rmtp_is_efault_or_completed :
  check_syscall nanosleep_wrap_rmtp_input
    (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret EFAULT) [] []))
    (clock_model 0)
  = CheckOk (clock_model 0) []
  /\ check_syscall nanosleep_wrap_rmtp_input
       (with_copyins [(8192, 16%nat)] (mkEffect 0 [] []))
       (clock_model 0)
     = CheckOk (clock_model 1000000000) []
  /\ check_syscall nanosleep_wrap_rmtp_input
       (with_copyins [(8192, 16%nat)]
          (mkEffect (errno_ret EINTR) [(nanosleep_wrap_rmtp, ts_250ms)] []))
       (clock_model 0)
     = CheckReject
  /\ check_syscall nanosleep_wrap_rmtp_input
       (mkEffect (errno_ret EFAULT) [] []) (clock_model 0)
     = CheckReject.
Proof. split; [|split; [|split]]; check_eq. Qed.

(** THE NEIGHBOUR: an [rmtp] at the last sixteen bytes
    [State.access_okb] accepts, mapped end to end.  The interruption
    writes its remainder there and is accepted, and -EFAULT is
    refused. *)
Definition nanosleep_top_rmtp : word := Z_to_bv 64 (TASK_SIZE - 16).

Definition nanosleep_top_wmem : word -> option byte :=
  fun a => if ((TASK_SIZE - 16 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Definition nanosleep_top_rmtp_input : SyscallInput :=
  mkInput 101 [8192; nanosleep_top_rmtp; 0; 0; 0; 0]
    (mem_at 8192 ts_1s) nanosleep_top_wmem.

Example nanosleep_rmtp_at_the_top_still_gets_the_remainder :
  check_syscall nanosleep_top_rmtp_input
    (with_copyins [(8192, 16%nat)]
       (mkEffect (errno_ret EINTR) [(nanosleep_top_rmtp, ts_250ms)] []))
    (clock_model 0)
  = CheckOk (clock_model 750000000) []
  /\ check_syscall nanosleep_top_rmtp_input
       (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret EFAULT) [] []))
       (clock_model 0)
     = CheckReject.
Proof. split; check_eq. Qed.
