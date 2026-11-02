(** * LinuxProcessSem.Checks.Cases.Net.StreamReset — worked examples of the survivor's reset state: read (63), recvfrom (207), ppoll (73) and pselect6 (72) on a stream-pair end whose peer closed

    Mirrors the survivor arms of [Sys/Fs/ReadWrite.v]
    ([stream_read_reset]) and [Sys/Fs/Select.v] ([stream_poll_mask],
    [ppoll_record]), which answer to Linux net/unix/af_unix.c
    ([unix_release_sock], [unix_stream_read_generic], [unix_poll]),
    net/socket.c ([sock_read_iter]) and include/net/sock.h
    ([sock_error], [sock_rcvlowat]), v6.18.46 (commit 1f99e9ab748f).  The
    design is dispatch://OSSV-287/artifact/d2-design-md.

    ONE FIXTURE: socketpair makes 3 and 4, 3 writes "h", and 4 closes
    without reading it.  On Linux that close leaves [sk_err =
    ECONNRESET] on 3, the survivor, because 4's own queue still held the
    byte; the model's close is kind-blind, so the survivor's error is
    open until a call shows it ([State.ResetState]).  Every call below
    is on 3.  In PART 3, the delivery control and [r7] add one write
    from 4 before the close ([survivor_with_byte]), so that 3 has a byte
    queued; the -EPIPE control uses the fixture as it is.

    Every Example is stated through [check_syscall] and
    [syscall_spec_witness] alone, so the same text compiles against the
    model before this change (f7da1a0, ossv287/poll-choices).  There
    each one is FALSE except the controls of PART 3 and the guard and
    control of PART 4, because the model declined the survivor's empty
    read.  That is the fail-before half; this file is the pass-after
    half. *)

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
Definition sr_m0 : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** Addresses.  [sv_addr]: the 8-byte [int sv[2]].  [src_addr]: a source
    buffer whose first two bytes are "hi".  [dst_addr]: a 64-byte
    destination.  [pfd_addr]: two [struct pollfd]s, both {fd 3, POLLIN}.
    [ts_addr]: a zero [struct timespec].  [set_addr]: one [fd_set] word
    holding bit 3. *)
Definition sv_addr : word := Z_to_bv 64 4096.
Definition src_addr : word := Z_to_bv 64 8192.
Definition dst_addr : word := Z_to_bv 64 24576.
Definition pfd_addr : word := Z_to_bv 64 32768.
Definition ts_addr : word := Z_to_bv 64 32800.
Definition set_addr : word := Z_to_bv 64 32832.

Definition in_range (a : word) (lo n : Z) : bool :=
  ((lo <=? bv_unsigned a) && (bv_unsigned a <? lo + n))%Z.

Definition pollfd_bytes3 : list byte :=
  Z_to_le_bytes 4 3 ++ Z_to_le_bytes 2 1 ++ Z_to_le_bytes 2 0.

(** What the process may READ. *)
Definition sr_rmem : word -> option byte :=
  fun a =>
    if in_range a 8192 8192 then
      Some (if Z.eqb (bv_unsigned a) 8192 then Z_to_bv 8 104          (* 'h' *)
            else if Z.eqb (bv_unsigned a) 8193 then Z_to_bv 8 105     (* 'i' *)
            else Z_to_bv 8 0)
    else if in_range a 32768 16 then
      Some (nth (Z.to_nat (bv_unsigned a - 32768)%Z)
              (pollfd_bytes3 ++ pollfd_bytes3) (Z_to_bv 8 0))
    else if in_range a 32800 16 then Some (Z_to_bv 8 0)
    else if in_range a 32832 8 then
      Some (nth (Z.to_nat (bv_unsigned a - 32832)%Z) (Z_to_le_bytes 8 8) (Z_to_bv 8 0))
    else None.

(** What the process may WRITE: [sv], the destination, the pollfds and
    the [fd_set] word. *)
Definition sr_wmem : word -> option byte :=
  fun a =>
    if (in_range a 4096 8 || in_range a 24576 64 || in_range a 32768 16
        || in_range a 32832 8)%bool
    then Some (Z_to_bv 8 0) else None.

Definition mk (sysno : Z) (args : list word) : SyscallInput :=
  mkInput (Z_to_bv 64 sysno) args sr_rmem sr_wmem.

(** socketpair(AF_UNIX, SOCK_STREAM, 0, sv) = 0, storing 3 and 4. *)
Definition pair_step : SyscallInput * SyscallEffect :=
  (mk 199 [Z_to_bv 64 1; Z_to_bv 64 1; 0; sv_addr; 0; 0],
   mkEffect 0 [(sv_addr, [3; 0; 0; 0]); (sv_addr + Z_to_bv 64 4, [4; 0; 0; 0])] []).

(** write(fd, src, 1) = 1: "h" lands in the other end's queue. *)
Definition write_step (fd : Z) : SyscallInput * SyscallEffect :=
  (mk 64 [Z_to_bv 64 fd; src_addr; Z_to_bv 64 1; 0; 0; 0],
   with_copyins [(src_addr, 1%nat)] (mkEffect (Z_to_bv 64 1) [] [])).

(** close(fd) = 0. *)
Definition close_step (fd : Z) : SyscallInput * SyscallEffect :=
  (mk 57 [Z_to_bv 64 fd; 0; 0; 0; 0; 0], mkEffect 0 [] []).

(** THE FIXTURE: 3 writes "h" to 4, and 4 closes without reading it. *)
Definition survivor : list (SyscallInput * SyscallEffect) :=
  [pair_step; write_step 3; close_step 4].

(** read(3, dst, n), and recvfrom(3, dst, n, 0, NULL, NULL). *)
Definition read_in (n : Z) : SyscallInput :=
  mk 63 [Z_to_bv 64 3; dst_addr; Z_to_bv 64 n; 0; 0; 0].
Definition recvfrom_in (n : Z) : SyscallInput :=
  mk 207 [Z_to_bv 64 3; dst_addr; Z_to_bv 64 n; 0; 0; 0].

(** The two answers of the survivor's empty read: -ECONNRESET, and end
    of file. *)
Definition reset : SyscallEffect := mkEffect (errno_ret ECONNRESET) [] [].
Definition eof : SyscallEffect := mkEffect 0 [] [].

(** ppoll(pfd, n, &{0,0}, NULL, 8) over the first [n] entries, every one
    {3, POLLIN}. *)
Definition ppoll_in (n : Z) : SyscallInput :=
  mk 73 [pfd_addr; Z_to_bv 64 n; ts_addr; 0; Z_to_bv 64 8; 0].

(** Its effect: every entry's [revents] is [rv], and the return counts
    them.  On 3, POLLIN | POLLHUP (17) is EPOLLERR clear, and 25 adds
    POLLERR (8): EPOLLERR set. *)
Definition ppoll_eff (rvs : list Z) : SyscallEffect :=
  with_copyins [(ts_addr, 16%nat); (pfd_addr, (8 * length rvs)%nat)]
    (mkEffect (Z_to_bv 64 (Z.of_nat (length rvs)))
       (map (fun '(k, rv) => (pfd_addr + Z_to_bv 64 (8 * Z.of_nat k + 6), Z_to_le_bytes 2 rv))
            (combine (seq 0 (length rvs)) rvs)) []).

Definition clear_step : SyscallInput * SyscallEffect := (ppoll_in 1, ppoll_eff [17%Z]).
Definition set_step : SyscallInput * SyscallEffect := (ppoll_in 1, ppoll_eff [25%Z]).

(** pselect6(4, {3}, NULL, NULL, NULL, NULL): readable, so 1 with the
    word written back. *)
Definition pselect_step : SyscallInput * SyscallEffect :=
  (mk 72 [Z_to_bv 64 4; set_addr; 0; 0; 0; 0],
   with_copyins [(set_addr, 8%nat)] (mkEffect 1 [(set_addr, Z_to_le_bytes 8 8)] [])).

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
  match run_accepted sr_m0 steps with
  | Some m => Some (check_syscall i e m)
  | None => None
  end.

Definition is_ok (r : option check_result) : bool :=
  match r with Some (CheckOk _ _) => true | _ => false end.

(** The witness's outcome after a run is accepted by the checker. *)
Definition witness_accepted (steps : list (SyscallInput * SyscallEffect))
    (i : SyscallInput) : Prop :=
  match run_accepted sr_m0 steps with
  | Some m =>
      match syscall_spec_witness i m with
      | Ok eff m' evs => check_syscall i eff m = CheckOk m' evs
      | Unmodeled => False
      end
  | None => False
  end.

(* =========================================================================
   PART 1 — the read: one -ECONNRESET at most, then end of file
   ========================================================================= *)

(** NOTHING SHOWN YET.  The survivor's empty read answers -ECONNRESET or
    end of file: Linux gives the first here, and would give the second
    had 4's queue been empty, and the kind-blind close does not record
    which.  Both are accepted. *)
Example r1_unknown_read_answers_reset_or_eof :
  is_ok (after survivor (read_in 64) reset) = true
  /\ is_ok (after survivor (read_in 64) eof) = true.
Proof. split; check_eq. Qed.

(** ...and nothing else: -EAGAIN, which a live peer's empty queue gives
    a non-blocking reader, is refused. *)
Example r1_unknown_read_has_no_third_answer :
  after survivor (read_in 64) (mkEffect (errno_ret EAGAIN) [] []) = Some CheckReject.
Proof. check_eq. Qed.

(** AFTER -ECONNRESET: [sock_error] cleared the error, so a second
    -ECONNRESET is refused and end of file is accepted. *)
Example r2_after_reset_a_second_reset_is_refused :
  after (survivor ++ [(read_in 64, reset)]) (read_in 64) reset = Some CheckReject
  /\ is_ok (after (survivor ++ [(read_in 64, reset)]) (read_in 64) eof) = true.
Proof. split; check_eq. Qed.

(** AFTER END OF FILE the error is known to be gone: -ECONNRESET is
    refused, end of file is accepted again. *)
Example r2_after_eof_reset_is_refused :
  after (survivor ++ [(read_in 64, eof)]) (read_in 64) reset = Some CheckReject
  /\ is_ok (after (survivor ++ [(read_in 64, eof)]) (read_in 64) eof) = true.
Proof. split; check_eq. Qed.

(** The witness of the survivor's read is an answer the checker
    accepts. *)
Example r2_survivor_read_witness_is_accepted :
  witness_accepted survivor (read_in 64).
Proof. check_eq. Qed.

(* =========================================================================
   PART 2 — the other route: ppoll records what it showed
   ========================================================================= *)

(** A PPOLL THAT CHOSE "CLEAR" (17, no POLLERR) fixed the error as gone:
    a later -ECONNRESET is refused, end of file is accepted, and a later
    ppoll that shows POLLERR (25) is refused. *)
Example r3_ppoll_clear_then_reset_is_refused :
  after (survivor ++ [clear_step]) (read_in 64) reset = Some CheckReject
  /\ is_ok (after (survivor ++ [clear_step]) (read_in 64) eof) = true
  /\ after (survivor ++ [clear_step]) (ppoll_in 1) (ppoll_eff [25%Z]) = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** A PPOLL THAT CHOSE "SET" (25, POLLERR) fixed the error as pending:
    a read of end of file is refused and -ECONNRESET is accepted; a
    later ppoll shows POLLERR again and not 17. *)
Example r4_ppoll_set_then_eof_is_refused :
  after (survivor ++ [set_step]) (read_in 64) eof = Some CheckReject
  /\ is_ok (after (survivor ++ [set_step]) (read_in 64) reset) = true
  /\ is_ok (after (survivor ++ [set_step]) (ppoll_in 1) (ppoll_eff [25%Z])) = true
  /\ after (survivor ++ [set_step]) (ppoll_in 1) (ppoll_eff [17%Z]) = Some CheckReject.
Proof. split; [|split; [|split]]; check_eq. Qed.

(** ...and the read that answered that -ECONNRESET consumed it: end of
    file next, a second -ECONNRESET refused, and ppoll back to 17. *)
Example r4_ppoll_set_then_reset_then_eof :
  is_ok (after (survivor ++ [set_step; (read_in 64, reset)]) (read_in 64) eof) = true
  /\ after (survivor ++ [set_step; (read_in 64, reset)]) (read_in 64) reset
     = Some CheckReject
  /\ is_ok (after (survivor ++ [set_step; (read_in 64, reset)])
                  (ppoll_in 1) (ppoll_eff [17%Z])) = true
  /\ after (survivor ++ [set_step; (read_in 64, reset)]) (ppoll_in 1) (ppoll_eff [25%Z])
     = Some CheckReject.
Proof. split; [|split; [|split]]; check_eq. Qed.

(** ONE STATE PER END, NOT PER ENTRY.  Two entries naming 3 read and
    record one state: both 25 is accepted, 17 beside 25 is refused, and
    after both-25 the read's end of file is refused. *)
Example r4_two_entries_record_one_state :
  is_ok (after survivor (ppoll_in 2) (ppoll_eff [25%Z; 25%Z])) = true
  /\ after survivor (ppoll_in 2) (ppoll_eff [17%Z; 25%Z]) = Some CheckReject
  /\ after (survivor ++ [(ppoll_in 2, ppoll_eff [25%Z; 25%Z])]) (read_in 64) eof
     = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** PSELECT6 HAS ONE ANSWER AND RECORDS NOTHING: EPOLLERR only reaches
    [POLLIN_SET] and [POLLOUT_SET], which the survivor already meets, so
    readfds {3} gives 1 either way, and the read after it may still
    answer either. *)
Example r4_pselect6_leaves_the_state_open :
  is_ok (after survivor (fst pselect_step) (snd pselect_step)) = true
  /\ is_ok (after (survivor ++ [pselect_step]) (read_in 64) reset) = true
  /\ is_ok (after (survivor ++ [pselect_step]) (read_in 64) eof) = true.
Proof. split; [|split]; check_eq. Qed.

(* =========================================================================
   PART 3 — which reads reach [sock_error], and the controls
   ========================================================================= *)

(** A ZERO-LENGTH read(2) is 0 in [sock_read_iter], before the protocol,
    so it shows nothing: -ECONNRESET is refused for it, and the read
    after it can still answer -ECONNRESET. *)
Example r5_zero_length_read_keeps_the_state :
  is_ok (after survivor (read_in 0) eof) = true
  /\ after survivor (read_in 0) reset = Some CheckReject
  /\ is_ok (after (survivor ++ [(read_in 0, eof)]) (read_in 64) reset) = true.
Proof. split; [|split]; check_eq. Qed.

(** A ZERO-LENGTH recvfrom has no such test ([sock_rcvlowat] makes the
    target 1), so it reaches [sock_error] and consumes the state: either
    answer is accepted, and after either a later -ECONNRESET is
    refused. *)
Example r6_zero_length_recvfrom_consumes_the_state :
  is_ok (after survivor (recvfrom_in 0) reset) = true
  /\ is_ok (after survivor (recvfrom_in 0) eof) = true
  /\ after (survivor ++ [(recvfrom_in 0, reset)]) (read_in 64) reset = Some CheckReject
  /\ after (survivor ++ [(recvfrom_in 0, eof)]) (read_in 64) reset = Some CheckReject.
Proof. split; [|split; [|split]]; check_eq. Qed.

(** The fixture with a byte queued on the survivor: 4 also writes "h" to
    3 before it closes. *)
Definition survivor_with_byte : list (SyscallInput * SyscallEffect) :=
  [pair_step; write_step 3; write_step 4; close_step 4].

(** CONTROL: a read with bytes queued delivers them, whatever the error
    state ([unix_stream_read_generic] looks at [sk_err] only when the
    queue is empty); end of file is refused. *)
Example control_bytes_queued_are_delivered :
  is_ok (after survivor_with_byte (read_in 64)
               (mkEffect 1 [(dst_addr, [Z_to_bv 8 104])] [])) = true
  /\ after survivor_with_byte (read_in 64) eof = Some CheckReject.
Proof. split; check_eq. Qed.

(** ...and that delivery leaves the state open: the next, empty read may
    still answer either. *)
Example r7_delivery_keeps_the_state :
  is_ok (after (survivor_with_byte ++ [(read_in 64, mkEffect 1 [(dst_addr, [Z_to_bv 8 104])] [])])
               (read_in 64) reset) = true
  /\ is_ok (after (survivor_with_byte ++ [(read_in 64, mkEffect 1 [(dst_addr, [Z_to_bv 8 104])] [])])
                  (read_in 64) eof) = true.
Proof. split; check_eq. Qed.

(** CONTROL: a send on the survivor is -EPIPE: SEND_SHUTDOWN comes first
    in [unix_stream_sendmsg], so the send does not consume the error.
    sendto(3, src, 1, MSG_NOSIGNAL, NULL, 0). *)
Example control_send_on_the_survivor_is_epipe :
  is_ok (after survivor
               (mk 206 [Z_to_bv 64 3; src_addr; Z_to_bv 64 1; Z_to_bv 64 16384; 0; 0])
               (mkEffect (errno_ret EPIPE) [] [])) = true.
Proof. check_eq. Qed.

(* =========================================================================
   PART 4 — no second descriptor reaches the survivor's state
   ========================================================================= *)

(** [se_reset] is kept in the end's descriptor entry.  In Linux the
    pending error is socket state ([sk_err]), shared by every descriptor
    of the socket, so it is reported once in total.  The model keeps that
    because every call that would make a second descriptor of an end
    declines: [dup] and [dup3] ([Fs.File.dup_modeled_entry]), [fcntl]
    F_DUPFD (answered on no kind), a [clone] whose table holds an end
    ([Kernel.Fork.clone_no_shared_file_b]), a reopen through
    /proc/self/fd/N ([Fs.Open.openat_procfd_spec]) and [sendmsg] (no
    SCM_RIGHTS).  So the state has one holder, and the one -ECONNRESET of
    [r2] is the only one.  GUARD: dup(3), dup3(3, 7, 0) and
    fcntl(3, F_DUPFD, 0) on the survivor decline, whatever answer is
    claimed.  It holds before this change too; it fails the day an arm
    makes a second descriptor of an end without sharing its state. *)
Example guard_no_second_descriptor_of_the_survivor :
  after survivor (mk 23 [Z_to_bv 64 3; 0; 0; 0; 0; 0]) (mkEffect 4 [] []) = Some CheckUnmodeled
  /\ after survivor (mk 24 [Z_to_bv 64 3; Z_to_bv 64 7; 0; 0; 0; 0]) (mkEffect 7 [] [])
     = Some CheckUnmodeled
  /\ after survivor (mk 25 [Z_to_bv 64 3; 0; 0; 0; 0; 0]) (mkEffect 4 [] []) = Some CheckUnmodeled.
Proof. split; [|split]; check_eq. Qed.

(** CONTROL: dup of a channel is answered, so the decline above comes
    from the pair end: dup(0) = 4, the lowest free descriptor once 4 has
    closed. *)
Example control_dup_of_a_channel_is_answered :
  is_ok (after survivor (mk 23 [0; 0; 0; 0; 0; 0]) (mkEffect 4 [] [])) = true.
Proof. check_eq. Qed.
