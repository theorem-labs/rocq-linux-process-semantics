(** * LinuxProcessSem.Checks.Cases.Fs.PollChoice — worked examples for the two answers of ppoll (73) and pselect6 (72) that are choices shown in the effect

    Mirrors the choice arms of [Sys/Fs/Select.v], which answers to Linux
    fs/select.c ([poll_select_finish], [do_select], [do_pollfd]) and
    net/unix/af_unix.c ([unix_poll], [unix_writable]), v6.18.46 (commit
    1f99e9ab748f).  The cases replay the census shapes of the design
    dispatch://OSSV-287/artifact/d1d3-design-md:

    - D1 (PART 1): a return under a real timeout that did not run out.
      [poll_select_finish] writes the remaining time to [*tsp]; the model
      chooses it from [0, timeout] and the checker reads it back from the
      write.
    - D3 (PART 2): POLLOUT in the band where [unix_writable] turns on skb
      truesize, and EPOLLERR on a survivor whose peer closed.  The model
      chooses, for each such pair end, which of its two masks Linux
      reports; the checker reads the choice back from [revents] or from
      the result word.

    Every Example is stated through [check_syscall] and
    [syscall_spec_witness] alone, so the same text compiles against the
    model before this change (#57's head, 9c7928a).  There each one is
    FALSE except the controls of PART 3, because the model declined every
    one of these calls.  That is the fail-before half. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export Prelude.

(* =========================================================================
   Fixtures
   ========================================================================= *)

(** The start: [init_model]'s three channels, so the pair takes 3 and 4. *)
Definition pc_m0 : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

Fixpoint region_byte (rs : list (Z * list byte)) (a : Z) : option byte :=
  match rs with
  | [] => None
  | (b, bs) :: r =>
      if ((b <=? a) && (a <? b + Z.of_nat (length bs)))%Z
      then nth_error bs (Z.to_nat (a - b)%Z)
      else region_byte r a
  end.
Definition region_mem (rs : list (Z * list byte)) : word -> option byte :=
  fun a => region_byte rs (bv_unsigned a).

Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.
Definition w (z : Z) : word := Z_to_bv 64 z.

(** Addresses: the [int sv[2]] of socketpair, a write source, the
    [struct pollfd] array (room for two entries), a [struct
    __kernel_timespec], and one [fd_set] word. *)
Definition sv_a : Z := 0x1000.
Definition src_a : Z := 0x2000.
Definition pfd_a : Z := 0x3000.
Definition ts_a : Z := 0x3100.
Definition set_a : Z := 0x3200.

(** Everything a call below writes is writable. *)
Definition pc_wmem : word -> option byte :=
  region_mem [(sv_a, zeros 8); (pfd_a, zeros 16); (ts_a, zeros 16); (set_a, zeros 8)].

Definition mk (sysno : Z) (args : list Z) (rs : list (Z * list byte)) : SyscallInput :=
  mkInput (w sysno) (map w args) (region_mem rs) pc_wmem.

(** socketpair(AF_UNIX, SOCK_STREAM, 0, sv) = 0, storing 3 and 4. *)
Definition pair_step : SyscallInput * SyscallEffect :=
  (mk 199 [1; 1; 0; sv_a]%Z [],
   mkEffect 0 [(w sv_a, Z_to_le_bytes 4 3); (w (sv_a + 4), Z_to_le_bytes 4 4)] []).

(** write(3, "h", 1) = 1: the byte lands in 4's queue. *)
Definition write_step : SyscallInput * SyscallEffect :=
  (mk 64 [3; src_a; 1]%Z [(src_a, [Z_to_bv 8 104])],
   with_copyins [(w src_a, 1%nat)] (mkEffect (w 1) [] [])).

(** close(3) = 0. *)
Definition close_step : SyscallInput * SyscallEffect :=
  (mk 57 [3]%Z [], mkEffect 0 [] []).

(** The fresh pair; the pair after 3 wrote one byte to 4; the pair
    after 3 closed. *)
Definition fresh : list (SyscallInput * SyscallEffect) := [pair_step].
Definition written : list (SyscallInput * SyscallEffect) := [pair_step; write_step].
Definition closed : list (SyscallInput * SyscallEffect) := [pair_step; close_step].

(** Run the steps through the checker, each one required to be accepted;
    the model after the last, or [None] at the first step not accepted. *)
Fixpoint run_accepted (m : Model) (steps : list (SyscallInput * SyscallEffect))
    : option Model :=
  match steps with
  | [] => Some m
  | (i, e) :: rest =>
      match check_syscall i e m with
      | CheckOk m' _ => run_accepted m' rest
      | _ => None
      end
  end.

(** The verdict of one more call after an accepted run. *)
Definition after (steps : list (SyscallInput * SyscallEffect))
    (i : SyscallInput) (e : SyscallEffect) : option check_result :=
  match run_accepted pc_m0 steps with
  | Some m => Some (check_syscall i e m)
  | None => None
  end.

Definition is_ok (r : option check_result) : bool :=
  match r with Some (CheckOk _ _) => true | _ => false end.

(** The witness's outcome after a run is accepted by the checker. *)
Definition witness_accepted (steps : list (SyscallInput * SyscallEffect))
    (i : SyscallInput) : Prop :=
  match run_accepted pc_m0 steps with
  | Some m =>
      match syscall_spec_witness i m with
      | Ok eff m' evs => check_syscall i eff m = CheckOk m' evs
      | Unmodeled => False
      end
  | None => False
  end.

(** A [struct __kernel_timespec], and one [struct pollfd] with [revents]
    0. *)
Definition ts (sec nsec : Z) : list byte := Z_to_le_bytes 8 sec ++ Z_to_le_bytes 8 nsec.
Definition pollfd (fd events : Z) : list byte :=
  Z_to_le_bytes 4 fd ++ Z_to_le_bytes 2 events ++ Z_to_le_bytes 2 0.

(** ppoll(pfd, 1, tsp, NULL, 8) on one entry {[fd], [events]}: [tsp] is
    [ts_a] holding the timeout [to], or NULL for [None]. *)
Definition ppoll_in (fd events : Z) (to : option (Z * Z)) : SyscallInput :=
  match to with
  | Some (s, ns) => mk 73 [pfd_a; 1; ts_a; 0; 8]%Z [(pfd_a, pollfd fd events); (ts_a, ts s ns)]
  | None => mk 73 [pfd_a; 1; 0; 0; 8]%Z [(pfd_a, pollfd fd events)]
  end.

(** The same on two entries that name one descriptor. *)
Definition ppoll2_in (fd events : Z) (to : Z * Z) : SyscallInput :=
  mk 73 [pfd_a; 2; ts_a; 0; 8]%Z
     [(pfd_a, pollfd fd events ++ pollfd fd events); (ts_a, ts (fst to) (snd to))].

(** ppoll's effect: return [r], the [revents] of each entry, and the
    remaining time [rem] when one is written.  The ledger is the timespec
    (when [tsp] is not NULL) and the array, in the kernel's order. *)
Definition ppoll_eff (to : bool) (r : Z) (revs : list Z) (rem : option (list byte))
    : SyscallEffect :=
  with_copyins ((if to then [(w ts_a, 16%nat)] else [])
                ++ [(w pfd_a, (8 * length revs)%nat)])
    (mkEffect (w r)
       (map (fun '(k, rv) => (w (pfd_a + 8 * Z.of_nat k + 6), Z_to_le_bytes 2 rv))
            (combine (seq 0 (length revs)) revs)
        ++ match rem with Some b => [(w ts_a, b)] | None => [] end) []).

(** pselect6(n, inp, outp, NULL, tsp, NULL) with the one [fd_set] word
    [v] at [set_a] passed as [readfds] ([rd] true) or as [writefds]. *)
Definition pselect_in (n : Z) (rd : bool) (v : Z) (to : option (Z * Z)) : SyscallInput :=
  let inp := if rd then set_a else 0%Z in
  let outp := if rd then 0%Z else set_a in
  match to with
  | Some (s, ns) => mk 72 [n; inp; outp; 0; ts_a; 0]%Z [(set_a, Z_to_le_bytes 8 v); (ts_a, ts s ns)]
  | None => mk 72 [n; inp; outp; 0; 0; 0]%Z [(set_a, Z_to_le_bytes 8 v)]
  end.

(** pselect6's effect: return [r], the result word [v] written back over
    the set, then the remaining time [rem] when one is written. *)
Definition pselect_eff (to : bool) (r v : Z) (rem : option (list byte)) : SyscallEffect :=
  with_copyins ((if to then [(w ts_a, 16%nat)] else []) ++ [(w set_a, 8%nat)])
    (mkEffect (w r)
       ((w set_a, Z_to_le_bytes 8 v)
        :: match rem with Some b => [(w ts_a, b)] | None => [] end) []).

(* =========================================================================
   PART 1 — D1: the remaining time under a real timeout
   ========================================================================= *)

(** D1, THE CENSUS CASE.  3 has written one byte to 4, so 4 is readable;
    ppoll asks POLLIN on it with a timeout of {0, 100000000} and returns
    1 with [revents] POLLIN.  [poll_select_finish] (fs/select.c) then
    writes [end_time - ktime_get_ts64()] to [*tsp], clamped at 0: a
    normalized timespec in [0, timeout].  40 ms is one such value. *)
Example d1_ppoll_remaining_time_in_range_is_accepted :
  is_ok (after written (ppoll_in 4 1 (Some (0, 100000000)%Z))
               (ppoll_eff true 1 [1]%Z (Some (ts 0 40000000)))) = true.
Proof. check_eq. Qed.

(** ...and so are the two ends of the range: the whole timeout (no time
    passed) and zero (the clamp). *)
Example d1_ppoll_remaining_time_range_ends_are_accepted :
  is_ok (after written (ppoll_in 4 1 (Some (0, 100000000)%Z))
               (ppoll_eff true 1 [1]%Z (Some (ts 0 100000000)))) = true
  /\ is_ok (after written (ppoll_in 4 1 (Some (0, 100000000)%Z))
                  (ppoll_eff true 1 [1]%Z (Some (ts 0 0)))) = true.
Proof. split; check_eq. Qed.

(** One nanosecond more than the timeout is refused: the monotonic clock
    does not go back between the entry and [poll_select_finish]. *)
Example d1_ppoll_remaining_time_above_the_timeout_is_refused :
  after written (ppoll_in 4 1 (Some (0, 100000000)%Z))
        (ppoll_eff true 1 [1]%Z (Some (ts 0 100000001))) = Some CheckReject.
Proof. check_eq. Qed.

(** {0, 1000000000} is refused: [timespec64_sub] normalizes, so a written
    [tv_nsec] is below [NSEC_PER_SEC]. *)
Example d1_ppoll_non_normalized_remaining_time_is_refused :
  after written (ppoll_in 4 1 (Some (0, 100000000)%Z))
        (ppoll_eff true 1 [1]%Z (Some (ts 0 1000000000))) = Some CheckReject.
Proof. check_eq. Qed.

(** NORMALIZATION REFUSES ON ITS OWN.  Under a timeout of 2 s,
    {0, 1500000000} is 1.5 s, inside the range, and is still refused,
    while the same 1.5 s written as {1, 500000000} is accepted. *)
Example d1_ppoll_normalization_alone_refuses :
  after written (ppoll_in 4 1 (Some (2, 0)%Z))
        (ppoll_eff true 1 [1]%Z (Some (ts 0 1500000000))) = Some CheckReject
  /\ is_ok (after written (ppoll_in 4 1 (Some (2, 0)%Z))
                  (ppoll_eff true 1 [1]%Z (Some (ts 1 500000000)))) = true.
Proof. split; check_eq. Qed.

(** The write-back is not optional: the same return with no remaining
    time written is refused. *)
Example d1_ppoll_without_the_write_back_is_refused :
  after written (ppoll_in 4 1 (Some (0, 100000000)%Z))
        (ppoll_eff true 1 [1]%Z None) = Some CheckReject.
Proof. check_eq. Qed.

(** D1 AGAIN, THROUGH pselect6: [readfds] = {4}, the same timeout, return
    1 with the word 16 written back, then the remaining time. *)
Example d1_pselect6_remaining_time :
  is_ok (after written (pselect_in 5 true 16 (Some (0, 100000000)%Z))
               (pselect_eff true 1 16 (Some (ts 0 40000000)))) = true
  /\ after written (pselect_in 5 true 16 (Some (0, 100000000)%Z))
           (pselect_eff true 1 16 (Some (ts 0 100000001))) = Some CheckReject
  /\ after written (pselect_in 5 true 16 (Some (0, 100000000)%Z))
           (pselect_eff true 1 16 (Some (ts 0 1000000000))) = Some CheckReject
  /\ after written (pselect_in 5 true 16 (Some (0, 100000000)%Z))
           (pselect_eff true 1 16 None) = Some CheckReject.
Proof. split; [|split; [|split]]; check_eq. Qed.

(** AN ERRNO FROM THE CORE TAKES THE SAME WRITE-BACK.  [readfds] names the
    closed descriptor 9, so [max_select_fd] answers -EBADF, and that
    return passes through [poll_select_finish] like a count does. *)
Example d1_pselect6_errno_under_a_deadline_writes_a_remaining_time :
  is_ok (after written (pselect_in 10 true 512 (Some (0, 100000000)%Z))
               (with_copyins [(w ts_a, 16%nat); (w set_a, 8%nat)]
                  (mkEffect (errno_ret EBADF) [(w ts_a, ts 0 40000000)] []))) = true
  /\ after written (pselect_in 10 true 512 (Some (0, 100000000)%Z))
           (with_copyins [(w ts_a, 16%nat); (w set_a, 8%nat)]
              (mkEffect (errno_ret EBADF) [] [])) = Some CheckReject.
Proof. split; check_eq. Qed.

(** The witness of the census call is an answer the checker accepts. *)
Example d1_witness_is_accepted :
  witness_accepted written (ppoll_in 4 1 (Some (0, 100000000)%Z)).
Proof. check_eq. Qed.

(* =========================================================================
   PART 2 — D3: POLLOUT in the truesize band, and EPOLLERR after a close
   ========================================================================= *)

(** D3, THE CENSUS CASE.  After 3 wrote one byte, 3's [sk_wmem_alloc] is
    1 plus the truesize of that skb, and [unix_writable] asks whether four
    times it is at most [sk_sndbuf].  The model does not carry truesize,
    so on 3 (the writer's end) POLLOUT is a choice: return 0 with
    [revents] 0, or return 1 with [revents] POLLOUT (4).  Both are
    accepted. *)
Example d3_ppoll_pollout_in_the_band_has_two_answers :
  is_ok (after written (ppoll_in 3 4 (Some (0, 0)%Z)) (ppoll_eff true 0 [0]%Z None)) = true
  /\ is_ok (after written (ppoll_in 3 4 (Some (0, 0)%Z)) (ppoll_eff true 1 [4]%Z None)) = true.
Proof. split; check_eq. Qed.

(** ...and nothing else: a third mask, and either mask with the other's
    count, are refused. *)
Example d3_ppoll_a_third_answer_is_refused :
  after written (ppoll_in 3 4 (Some (0, 0)%Z)) (ppoll_eff true 1 [5]%Z None) = Some CheckReject
  /\ after written (ppoll_in 3 4 (Some (0, 0)%Z)) (ppoll_eff true 0 [4]%Z None) = Some CheckReject
  /\ after written (ppoll_in 3 4 (Some (0, 0)%Z)) (ppoll_eff true 1 [0]%Z None) = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** ONE END, ONE ANSWER.  Two entries naming 3 read the same
    [sk_wmem_alloc] in the same pass of [do_poll], so they report the same
    mask: both 0 or both POLLOUT, never one of each. *)
Example d3_ppoll_one_end_named_twice_answers_once :
  is_ok (after written (ppoll2_in 3 4 (0, 0)%Z) (ppoll_eff true 0 [0; 0]%Z None)) = true
  /\ is_ok (after written (ppoll2_in 3 4 (0, 0)%Z) (ppoll_eff true 2 [4; 4]%Z None)) = true
  /\ after written (ppoll2_in 3 4 (0, 0)%Z) (ppoll_eff true 1 [4; 0]%Z None) = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** D3 THROUGH pselect6: [writefds] = {3}.  The result word is 0 with
    return 0, or 8 with return 1; return 1 with the word 0 is refused. *)
Example d3_pselect6_writefds_in_the_band :
  is_ok (after written (pselect_in 4 false 8 (Some (0, 0)%Z)) (pselect_eff true 0 0 None)) = true
  /\ is_ok (after written (pselect_in 4 false 8 (Some (0, 0)%Z)) (pselect_eff true 1 8 None)) = true
  /\ after written (pselect_in 4 false 8 (Some (0, 0)%Z)) (pselect_eff true 1 0 None)
     = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** D3 UNDER A DEADLINE, which is where the two halves meet.  The smaller
    answer counts 0, so its deadline ran out and the remaining time is 16
    zero bytes; the larger counts 1 and chooses a remaining time.  A zero
    count with time left is refused. *)
Example d3_ppoll_band_under_a_deadline :
  is_ok (after written (ppoll_in 3 4 (Some (0, 100000000)%Z))
               (ppoll_eff true 0 [0]%Z (Some (zeros 16)))) = true
  /\ is_ok (after written (ppoll_in 3 4 (Some (0, 100000000)%Z))
                  (ppoll_eff true 1 [4]%Z (Some (ts 0 40000000)))) = true
  /\ after written (ppoll_in 3 4 (Some (0, 100000000)%Z))
           (ppoll_eff true 0 [0]%Z (Some (ts 0 40000000))) = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** THE FALLOUT THE DESIGN NAMES.  After 3 closes, 4's peer left
    SHUTDOWN_MASK (HUP, RDHUP, IN).  The close does not record whether it
    also left [sk_err]; the first ppoll that shows it records what it
    showed ([Fs.Select.ppoll_record]).  EPOLLERR is in every filter.  So
    this first ppoll on 4 asking POLLIN answers 1 with [revents]
    POLLIN|POLLHUP (17), or with POLLERR too (25); POLLHUP alone is
    refused. *)
Example d3_ppoll_peer_closed_answers_with_epollerr_set_or_clear :
  is_ok (after closed (ppoll_in 4 1 None) (ppoll_eff false 1 [17]%Z None)) = true
  /\ is_ok (after closed (ppoll_in 4 1 None) (ppoll_eff false 1 [25]%Z None)) = true
  /\ after closed (ppoll_in 4 1 None) (ppoll_eff false 1 [16]%Z None) = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** The witness of the census call is an answer the checker accepts. *)
Example d3_witness_is_accepted :
  witness_accepted written (ppoll_in 3 4 (Some (0, 0)%Z)).
Proof. check_eq. Qed.

(* =========================================================================
   PART 3 — controls, true before this change and after it
   ========================================================================= *)

(** CONTROL: with 4's queue empty, 3's [sk_wmem_alloc] is 1 and POLLOUT
    is decided, so there is one answer. *)
Example control_decided_pollout_has_one_answer :
  is_ok (after fresh (ppoll_in 3 4 (Some (0, 0)%Z)) (ppoll_eff true 1 [4]%Z None)) = true
  /\ after fresh (ppoll_in 3 4 (Some (0, 0)%Z)) (ppoll_eff true 0 [0]%Z None) = Some CheckReject.
Proof. split; check_eq. Qed.

(** CONTROL: a deadline that runs out with nothing ready writes 16 zero
    bytes, and only those. *)
Example control_expired_deadline_writes_zeros :
  is_ok (after fresh (ppoll_in 4 1 (Some (0, 100000000)%Z))
               (ppoll_eff true 0 [0]%Z (Some (zeros 16)))) = true
  /\ after fresh (ppoll_in 4 1 (Some (0, 100000000)%Z))
           (ppoll_eff true 0 [0]%Z (Some (ts 0 40000000))) = Some CheckReject.
Proof. split; check_eq. Qed.

(** CONTROL: the band under a NULL timeout still declines.  The smaller
    answer counts 0, and with no timeout [do_poll] then sleeps forever,
    so one of Linux's two behaviors is a call that never returns. *)
Example control_band_under_a_null_timeout_declines :
  after written (ppoll_in 3 4 None) (ppoll_eff false 1 [4]%Z None) = Some CheckUnmodeled
  /\ match run_accepted pc_m0 written with
     | Some m => syscall_spec_witness (ppoll_in 3 4 None) m = Unmodeled
     | None => False
     end.
Proof. split; check_eq. Qed.

(** CONTROL: pselect6 with no timeout on a readable end answers as
    before. *)
Example control_pselect6_readable_without_a_timeout :
  is_ok (after written (pselect_in 5 true 16 None) (pselect_eff false 1 16 None)) = true.
Proof. check_eq. Qed.
