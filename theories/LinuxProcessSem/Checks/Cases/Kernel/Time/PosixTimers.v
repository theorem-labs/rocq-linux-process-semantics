(** * LinuxProcessSem.Checks.Cases.Kernel.Time.PosixTimers — worked examples over clock_gettime (113) and clock_getres (114)

    Mirrors [Sys/Kernel/Time/PosixTimers.v], which answers to Linux
    [kernel/time/posix-timers.c]: this file holds the worked examples
    for the syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    What is here is the model's own notion of
    a clock: [m_clock] is internal state no observation reveals, and no
    kernel can be asked to run CLOCK_MONOTONIC backwards or to stand still
    on demand.  For CLOCK_REALTIME what is here is the mirror image — the
    ABSENCE of a cross-call constraint, which shows up as the cases the
    monotonic arm rejects and this one admits. *)

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

(** Sixteen writable bytes at 4096, and nothing else. *)
Definition wmem_ts : word -> option byte :=
  fun a => if ((4096 <=? bv_unsigned a)%Z && (bv_unsigned a <? 4112)%Z)%bool
           then Some 0 else None.

Definition clock_input (clkid : word) : SyscallInput :=
  mkInput 113 [clkid; 4096; 0; 0; 0; 0] (fun _ => None) wmem_ts.

(** A model whose monotonic clock reads [t] nanoseconds.  [mkModel]
    starts the clock at its origin, so the reading is set on top of one. *)
Definition clock_model (t : Z) : Model :=
  with_clock (Z_to_bv 64 t)
    (mkModel [] (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None).

(** One second, as the kernel would write it: tv_sec = 1, tv_nsec = 0. *)
Definition ts_1s : list byte :=
  [1; 0; 0; 0; 0; 0; 0; 0] ++ [0; 0; 0; 0; 0; 0; 0; 0].
(** Two seconds. *)
Definition ts_2s : list byte :=
  [2; 0; 0; 0; 0; 0; 0; 0] ++ [0; 0; 0; 0; 0; 0; 0; 0].
(** One nanosecond BEFORE one second: tv_sec = 0, tv_nsec = 999999999. *)
Definition ts_1s_minus : list byte :=
  [0; 0; 0; 0; 0; 0; 0; 0] ++ [255; 201; 154; 59; 0; 0; 0; 0].
(** tv_sec = 1 with an UNNORMALIZED tv_nsec of exactly 10^9. *)
Definition ts_denorm : list byte :=
  [1; 0; 0; 0; 0; 0; 0; 0] ++ [0; 202; 154; 59; 0; 0; 0; 0].

(** UNIVERSALLY QUANTIFIED.  Every clock id but the SEVEN modeled ones
    declines, whatever the destination, the effect or the model — so no
    future arm can quietly start answering for CLOCK_THREAD_CPUTIME_ID,
    CLOCK_TAI or the alarm variants without this failing.  The id is
    tested before anything else, which is why no hypothesis about [tp]
    or [eff] is needed. *)
Lemma clock_gettime_only_the_modeled_clocks :
  forall i clkid tp eff m,
    (bv_unsigned clkid =? CLOCK_REALTIME)%Z = false ->
    (bv_unsigned clkid =? CLOCK_MONOTONIC_RAW)%Z = false ->
    (bv_unsigned clkid =? CLOCK_REALTIME_COARSE)%Z = false ->
    (bv_unsigned clkid =? CLOCK_MONOTONIC_COARSE)%Z = false ->
    (bv_unsigned clkid =? CLOCK_BOOTTIME)%Z = false ->
    (bv_unsigned clkid =? CLOCK_PROCESS_CPUTIME_ID)%Z = false ->
    (bv_unsigned clkid =? CLOCK_MONOTONIC)%Z = false ->
    check_clock_gettime i clkid tp eff m = CheckUnmodeled.
Proof.
  intros i clkid tp eff m Hrt Hraw Hrtc Hmc Hbt Hcp Hmono.
  unfold check_clock_gettime, clockid_percall_b.
  rewrite Hrt, Hraw, Hrtc, Hmc, Hbt, Hcp, Hmono. reflexivity.
Qed.

(** MODEL-INTERNAL STATE.  A clock already at the top of [ktime_t]'s
    range declines rather than inventing a reading.  Unreachable from
    [init_model] — the origin is 0 and every arm stays under the
    envelope — but [Progress.receptive] quantifies over arbitrary model
    states, so the arm has to be there and has to be right. *)
Example clock_at_envelope_declines :
  check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_1s)] [])
    (clock_model (2 ^ 63)) = CheckUnmodeled.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  Two readings that
    return the SAME nanosecond are admissible: CLOCK_MONOTONIC never runs
    backwards, but it is not required to advance, and a coarse
    clocksource really does answer two quick calls alike.  No program can
    force that coincidence, so it is pinned here.  The accepted step
    leaves [m_clock] where it was. *)
Example clock_equal_reading_is_admissible :
  check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_1s)] [])
    (clock_model 1000000000)
  = CheckOk (clock_model 1000000000) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE.  An advancing reading is admissible too, and
    the point of the case is the SECOND half: the accepted step carries
    the new time into [m_clock].  That the clock is updated at all is
    invisible from outside — nothing about [m_clock] reaches a trace —
    so no run can check it directly; a run sees it
    only indirectly, through a later call being judged against it. *)
Example clock_advancing_reading_records_it :
  check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_2s)] [])
    (clock_model 1000000000)
  = CheckOk (clock_model 2000000000) [].
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the [CheckReject]
    half.  A reading one nanosecond EARLIER than the last is refused.
    This is the monotonicity guarantee itself, and no real kernel can be
    asked to violate it. *)
Example clock_backwards_reading_rejected :
  check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_1s_minus)] [])
    (clock_model 1000000000) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the exact boundary.
    The boundary itself, tv_nsec = 10^9 exactly, is refused
    even though the total it encodes moves forward: the kernel's
    normalization carries whole seconds out of the nanosecond field, so
    a full second never appears there, and admitting it would make two
    different byte strings mean the same instant. *)
Example clock_denormalized_nsec_rejected :
  check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_denorm)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.


(** The reading's own ENVELOPE, which no real run can reach.

    [timespec_ok_b]'s fourth conjunct bounds the READING, where
    [clock_at_envelope_declines] above bounds the previously RECORDED
    clock; nothing else in the tree separates the two. *)
Definition ts_max : list byte :=          (* 2^63 - 1 ns exactly *)
  [4; 125; 193; 37; 2; 0; 0; 0] ++ [255; 215; 242; 50; 0; 0; 0; 0].
Definition ts_over : list byte :=         (* 2^63 ns: one too many *)
  [4; 125; 193; 37; 2; 0; 0; 0] ++ [0; 216; 242; 50; 0; 0; 0; 0].
(** tv_sec = 18446744073, tv_nsec = 709552616 — a reading of 2^64 + 1000
    nanoseconds, whose LOW 64 BITS are 1000. *)
Definition ts_wrap : list byte :=
  [9; 250; 130; 75; 4; 0; 0; 0] ++ [232; 233; 74; 42; 0; 0; 0; 0].

(** The largest reading [ktime_t] can hold is admissible, and recorded. *)
Example clock_reading_at_envelope_minus_one_admissible :
  check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_max)] [])
    (clock_model 0)
  = CheckOk (clock_model (2 ^ 63 - 1)) [].
Proof. check_eq. Qed.

(** One nanosecond further is refused: [ktime_t] is signed 64-bit, so
    2^63 ns is not a time a kernel can report. *)
Example clock_reading_at_envelope_rejected :
  check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_over)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ONE CASE THAT PINS THE [Z] ARITHMETIC.  [timespec_ns] sums
    [tv_sec * 10^9 + tv_nsec] in [Z] on purpose.  Summed in [word] this
    reading is 1000 ns — larger than the recorded 0 and far under the
    envelope — so a wrapping spelling answers [CheckOk] and lets an
    absurd [tv_sec] present itself as a small, admissible time.  Every
    other case in this file passes under both spellings; this is the
    only one that separates them. *)
Example clock_reading_wrapping_sum_rejected :
  check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_wrap)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** ---------------------------------------------------------------------
    CLOCK_REALTIME, whose whole content is what it does NOT promise.

    What no real run can reach is the ABSENCE of the
    cross-call constraint: a kernel will not run its wall clock
    backwards between two calls on request, and [m_clock] not moving is
    invisible from outside.  Each case below is therefore paired with
    the CLOCK_MONOTONIC case directly above that it contradicts.
    ------------------------------------------------------------------ *)

(** UNIVERSALLY QUANTIFIED, and the load-bearing one: an accepted
    per-call — CLOCK_REALTIME, raw, coarse or boottime — call leaves
    the model EXACTLY as it found it, for
    every input, destination, effect and starting model.  This is what
    stops a future change quietly giving any of those ids an [m_clock]-
    style field — a field written by the spec and read by nothing would
    look like a guarantee the kernel does not give.  For the wall clock
    [Kernel.Time.PosixTimers.realtime_ok_b] says why there is none to
    record: [do_settimeofday64] refuses nothing that sets the clock
    EARLIER, and [adjtimex]'s ADJ_SETOFFSET steps it by a signed value
    straight from userspace.  Neither needs the modeled process to do
    anything.  For the other four ids
    [Kernel.Time.PosixTimers.clockid_percall_b] says why the guarantees
    they DO carry are deliberately not stated. *)
Lemma clock_gettime_percall_leaves_the_model_alone :
  forall i clkid tp eff m m' evs,
    clockid_percall_b clkid = true ->
    check_clock_gettime i clkid tp eff m = CheckOk m' evs ->
    m' = m /\ evs = [].
Proof.
  intros i clkid tp [ret ws zs us cs copyins] m m' evs Hid H.
  unfold check_clock_gettime in H. rewrite Hid in H. cbv iota in H.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16));
    [|discriminate]. cbv iota in H.
  destruct ws as [|[a bs] ws']; [discriminate|].
  destruct ws' as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
            && realtime_ok_b bs); [|discriminate].
  inversion H; auto.
Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the exact
    counterpart of [clock_backwards_reading_rejected] above: the SAME
    bytes, the SAME recorded clock, the other id.  A wall-clock reading
    one nanosecond EARLIER than the last monotonic one is admissible,
    because CLOCK_REALTIME carries no monotonicity at all — and the
    accepted step leaves the recorded clock where it was rather than
    dragging it backwards. *)
Example realtime_backwards_reading_is_admissible :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_1s_minus)] [])
    (clock_model 1000000000)
  = CheckOk (clock_model 1000000000) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE, and the counterpart of
    [clock_at_envelope_declines].  A recorded clock past what [ktime_t]
    holds declines a MONOTONIC read, because the choice that read makes
    is relative to it and would be empty.  It does not decline a
    WALL-CLOCK read: that arm never consults [m_clock], so there is
    nothing for the envelope to be empty against. *)
Example realtime_ignores_the_recorded_clock :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_1s)] [])
    (clock_model (2 ^ 63))
  = CheckOk (clock_model (2 ^ 63)) [].
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  What the wall clock
    DOES have to satisfy, it satisfies on the same terms as the
    monotonic one.  A tv_nsec of exactly 10^9 is refused:
    [ktime_get_real_ts64] sets the field to 0 and normalizes with
    [timespec64_add_ns], so a full second never appears there. *)
Example realtime_denormalized_nsec_rejected :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_denorm)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  A reading of 2^63 ns
    is refused for the wall clock too.  The bound is
    [timespec64_valid_settod], which every writer of the wall clock
    passes and which stops thirty years SHORT of [KTIME_SEC_MAX]
    precisely so uptime cannot carry the clock out of [ktime_t]. *)
Example realtime_reading_at_envelope_rejected :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_over)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** The largest wall-clock reading [ktime_t] can hold is admissible, and
    is NOT recorded — the pair with the case above makes the boundary
    non-vacuous, and the pair with
    [clock_reading_at_envelope_minus_one_admissible], which records the
    same bytes, makes the difference between the arms non-vacuous. *)
Example realtime_reading_at_envelope_minus_one_admissible :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_max)] [])
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

(** ---------------------------------------------------------------------
    CLOCK_PROCESS_CPUTIME_ID, which is not a clock.

    It reports the thread group's [sum_exec_runtime] — a [u64] count of
    nanoseconds of CPU consumed — so
    [Kernel.Time.PosixTimers.cputime_ok_b] keeps the wall clock's
    per-reading conditions and moves the 2^63 ns envelope onto the
    SIGNED reading, two-sided.  That is the whole difference between
    the arms, and it is the half no real run can reach: no kernel can be
    asked for a reading near either end of an [s64], and [m_clock] not
    moving is invisible from outside.  Where a case below decides a
    boundary or contradicts a sibling arm it is paired — with the
    reading one nanosecond away, or with the case on the arm that
    answers the other way for the same bytes.
    ------------------------------------------------------------------ *)

(** Readings at the two ends of the [s64] [ns_to_timespec64] is handed.

    [ts_cpu_min] is what the kernel writes for a sample of exactly
    2^63: [ns_to_timespec64]'s [nsec < 0] branch gives
    [tv_sec = -div_u64_rem(-nsec - 1, 10^9, &rem) - 1 = -9223372037] and
    [tv_nsec = 10^9 - rem - 1 = 145224192].  ([-nsec] is the one place
    that expression can overflow, and this is the input where it does:
    at [INT64_MIN] the negation wraps to itself, and the [- 1] and the
    [u64] parameter of [div_u64_rem] are what make the result come out
    right anyway — 2^63 - 1 is the value divided.)  [ts_cpu_below] is that
    reading one nanosecond lower, which is not in the branch's image.
    [ts_cpu_neg1] is the largest sample a [u64] holds, 2^64 - 1, which
    the same branch spells as [tv_sec = -1] with a full [tv_nsec]. *)
Definition ts_cpu_min : list byte :=      (* signed total -2^63 exactly *)
  [251; 130; 62; 218; 253; 255; 255; 255] ++ [0; 242; 167; 8; 0; 0; 0; 0].
Definition ts_cpu_below : list byte :=    (* -2^63 - 1: one too few *)
  [251; 130; 62; 218; 253; 255; 255; 255] ++ [255; 241; 167; 8; 0; 0; 0; 0].
Definition ts_cpu_neg1 : list byte :=     (* tv_sec = -1, tv_nsec = 10^9 - 1 *)
  [255; 255; 255; 255; 255; 255; 255; 255] ++ [255; 201; 154; 59; 0; 0; 0; 0].

(** UNIVERSALLY QUANTIFIED, and the load-bearing one, for the reason
    [clock_gettime_percall_leaves_the_model_alone] gives and one more
    of its own: an accepted CLOCK_PROCESS_CPUTIME_ID call leaves the
    model EXACTLY as it found it, for every input, destination, effect
    and starting model.  This is what stops a future change relating
    CPU consumed to [m_clock].  The two are different quantities and no
    kernel-enforced inequality connects them — a thread group on
    several CPUs burns CPU faster than any clock advances, and one that
    is not scheduled burns none — so a field here could only be written
    and never read. *)
Lemma clock_gettime_cputime_leaves_the_model_alone :
  forall i clkid tp eff m m' evs,
    (bv_unsigned clkid =? CLOCK_PROCESS_CPUTIME_ID)%Z = true ->
    check_clock_gettime i clkid tp eff m = CheckOk m' evs ->
    m' = m /\ evs = [].
Proof.
  intros i clkid tp [ret ws zs us cs copyins] m m' evs Hid H.
  assert (Hpc : clockid_percall_b clkid = false).
  { unfold clockid_percall_b.
    rewrite (proj1 (Z.eqb_eq _ _) Hid). reflexivity. }
  unfold check_clock_gettime in H. rewrite Hpc, Hid in H. cbv iota in H.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16));
    [|discriminate]. cbv iota in H.
  destruct ws as [|[a bs] ws']; [discriminate|].
  destruct ws' as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
            && cputime_ok_b bs); [|discriminate].
  inversion H; auto.
Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the counterpart
    of [realtime_backwards_reading_is_admissible] and
    [clock_backwards_reading_rejected]: the SAME bytes, the SAME
    recorded clock, a third id.  A CPU-time reading is related to no
    earlier reading and to no clock, so it is admissible below the
    recorded one, and the accepted step leaves that clock alone. *)
Example cputime_backwards_reading_is_admissible :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_1s_minus)] [])
    (clock_model 1000000000)
  = CheckOk (clock_model 1000000000) [].
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE, the counterpart of
    [clock_at_envelope_declines] and [realtime_ignores_the_recorded_clock].
    A recorded clock past what [ktime_t] holds declines a MONOTONIC
    read and not this one: this arm never consults [m_clock] either. *)
Example cputime_ignores_the_recorded_clock :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_1s)] [])
    (clock_model (2 ^ 63))
  = CheckOk (clock_model (2 ^ 63)) [].
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  The conjunct that
    survives on this arm still bites: a tv_nsec of exactly 10^9 is
    refused, because all three branches of [ns_to_timespec64] leave
    that field below 10^9 — the [nsec < 0] one by computing
    [NSEC_PER_SEC - rem - 1]. *)
Example cputime_denormalized_nsec_rejected :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_denorm)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and THE PAIR THAT IS
    THE WHOLE DIFFERENCE BETWEEN THIS ARM AND THE WALL CLOCK'S.  A
    reading with a NEGATIVE tv_sec is what [ns_to_timespec64] writes
    once the [u64] sample passes 2^63, so this arm must admit it; the
    wall clock has no such shape, [realtime_ok_b] reads tv_sec
    unsigned, and the case below rejects the identical bytes. *)
Example cputime_negative_tv_sec_admissible :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_cpu_neg1)] [])
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

Example realtime_negative_tv_sec_rejected :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_cpu_neg1)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the bottom of the
    envelope, which exists only on this arm.  A SAMPLE of exactly 2^63
    is admissible: it is the smallest [u64] the [nsec < 0] branch sees,
    and so the one whose READING is the most negative of any this id
    can report.  (Larger samples read HIGHER, not lower, back up
    towards -1 — [ts_cpu_neg1] above is the largest sample of all.) *)
Example cputime_at_signed_envelope_admissible :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_cpu_min)] [])
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

(** One nanosecond lower is refused, which is what makes the bound
    above non-vacuous: the argument to [ns_to_timespec64] is an [s64],
    so nothing below -2^63 is in its image. *)
Example cputime_below_signed_envelope_rejected :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_cpu_below)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — and the top of the
    envelope, where this arm agrees with the other two rather than
    differing from them.  Putting the bound on the signed reading does
    not delete it: 2^63 - 1 ns is the largest positive sample, and
    2^63 is refused here exactly as it is for the wall clock. *)
Example cputime_reading_at_envelope_minus_one_admissible :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_max)] [])
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

Example cputime_reading_at_envelope_rejected :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_over)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** ---------------------------------------------------------------------
    The raw, coarse and boottime ids, which share the wall-clock arm.

    [Kernel.Time.PosixTimers.clockid_percall_b] carries the argument;
    what the cases below pin is that the sharing is REAL — each id is
    judged exactly as CLOCK_REALTIME is, per call, against
    [realtime_ok_b] alone, and the model is left exactly as found.
    One case per id, each deciding the conjunct or the absence a real
    run cannot reach for that id.
    ------------------------------------------------------------------ *)

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the counterpart of
    [clock_backwards_reading_rejected] on an id that IS monotone in the
    kernel: a BOOTTIME reading below the recorded monotonic clock is
    admissible, because a per-call id is deliberately related to
    nothing — each call is independently arbitrary — and the accepted
    step leaves the recorded clock alone. *)
Example boottime_backwards_reading_is_admissible :
  check_syscall (clock_input 7) (mkEffect 0 [(4096, ts_1s_minus)] [])
    (clock_model 1000000000)
  = CheckOk (clock_model 1000000000) [].
Proof. check_eq. Qed.

(** What a per-call id DOES have to satisfy, it satisfies on the wall
    clock's terms.  A tv_nsec of exactly 10^9 is refused for
    CLOCK_MONOTONIC_RAW: [ktime_get_raw_ts64] normalizes with
    [timespec64_add_ns] like every fine-grained path here. *)
Example monotonic_raw_denormalized_nsec_rejected :
  check_syscall (clock_input 4) (mkEffect 0 [(4096, ts_denorm)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** The envelope survives the sharing: a CLOCK_REALTIME_COARSE reading
    of 2^63 ns is refused — a tick snapshot of the wall clock is still
    a time [ktime_t] must be able to hold. *)
Example realtime_coarse_reading_at_envelope_rejected :
  check_syscall (clock_input 5) (mkEffect 0 [(4096, ts_over)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** MODEL-INTERNAL STATE, the counterpart of
    [realtime_ignores_the_recorded_clock] for the id nearest the one
    that owns the field: a recorded clock past what [ktime_t] holds
    declines a MONOTONIC read and not a MONOTONIC_COARSE one — a
    per-call arm never consults [m_clock], even for an id that reads
    the same underlying clock at tick granularity. *)
Example monotonic_coarse_ignores_the_recorded_clock :
  check_syscall (clock_input 6) (mkEffect 0 [(4096, ts_1s)] [])
    (clock_model (2 ^ 63))
  = CheckOk (clock_model (2 ^ 63)) [].
Proof. check_eq. Qed.

Definition getres_input (clkid tp : word) (wmem : word -> option byte)
    : SyscallInput :=
  mkInput 114 [clkid; tp; 0; 0; 0; 0] (fun _ => None) wmem.

Definition res_1ns : list byte :=
  Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 1.
Definition res_4ms : list byte :=
  Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 4000000.

Example clock_getres_null_and_invalid_clock :
  check_syscall (getres_input 1 0 (fun _ => None))
    (mkEffect 0 [] []) (clock_model 0) = CheckOk (clock_model 0) []
  /\ check_syscall (getres_input 10 0 (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (clock_model 0)
       = CheckOk (clock_model 0) []
  /\ check_syscall (getres_input 1 0 (fun _ => Some (Z_to_bv 8 0)))
       (mkEffect 0 [] []) (clock_model 0) = CheckUnmodeled
  /\ check_syscall (getres_input 10 0 (fun _ => None))
       (mkEffect 0 [] []) (clock_model 0) = CheckReject.
Proof. repeat split; check_eq. Qed.

Example clock_getres_cpu_and_general_resolutions :
  check_syscall (getres_input 2 4096 wmem_ts)
    (mkEffect 0 [(4096, res_1ns)] []) (clock_model 0)
    = CheckOk (clock_model 0) []
  /\ check_syscall (getres_input 3 4096 wmem_ts)
       (mkEffect 0 [(4096, res_1ns)] []) (clock_model 0)
       = CheckOk (clock_model 0) []
  /\ check_syscall (getres_input 4294967298 4096 wmem_ts)
       (mkEffect 0 [(4096, res_1ns)] []) (clock_model 0)
       = CheckOk (clock_model 0) []
  /\ check_syscall (getres_input 1 4096 wmem_ts)
       (mkEffect 0 [(4096, res_4ms)] []) (clock_model 0)
       = CheckOk (clock_model 0) []
  /\ check_syscall (getres_input 2 4096 wmem_ts)
       (mkEffect 0 [(4096, res_4ms)] []) (clock_model 0)
       = CheckReject.
Proof. repeat split; check_eq. Qed.

Example clock_getres_alarm_and_memory_edges :
  check_syscall (getres_input 8 4096 wmem_ts)
    (mkEffect (errno_ret EINVAL) [] []) (clock_model 0)
    = CheckOk (clock_model 0) []
  /\ check_syscall (getres_input 8 4096 wmem_ts)
       (mkEffect 0 [(4096, res_1ns)] []) (clock_model 0)
       = CheckOk (clock_model 0) []
  /\ check_syscall (getres_input 8 4096 (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (clock_model 0)
       = CheckUnmodeled
  /\ check_syscall (getres_input 1 4096 (fun _ => None))
       (mkEffect 0 [(4096, res_1ns)] []) (clock_model 0)
       = CheckUnmodeled
  /\ check_syscall (getres_input 1 4096 wmem_ts)
       (mkEffect 0 [(4096, Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0)] [])
       (clock_model 0) = CheckReject
  /\ check_syscall (getres_input 1 4096 wmem_ts)
       (mkEffect 0 [(4096, Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 1000000000)] [])
       (clock_model 0) = CheckReject
  /\ check_syscall (getres_input 1 4096 wmem_ts)
       (mkEffect 0 [(4096, Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 0)] [])
       (clock_model 0) = CheckReject
  /\ check_syscall (getres_input 1 0 (fun _ => None))
       (mkEffect 0 [(0, res_1ns)] []) (clock_model 0) = CheckReject.
Proof. repeat split; check_eq. Qed.
