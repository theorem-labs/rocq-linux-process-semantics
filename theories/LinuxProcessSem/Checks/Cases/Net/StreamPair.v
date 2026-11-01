(** * LinuxProcessSem.Checks.Cases.Net.StreamPair — worked examples over socketpair(AF_UNIX, SOCK_STREAM) (199) and a stream-pair end

    Mirrors the stream-pair arms of [Sys/Net/Socket.v], [Sys/Fs/ReadWrite.v]
    and [Sys/Fs/Select.v], which answer to Linux net/unix/af_unix.c,
    net/socket.c, net/core/sock.c and fs/select.c (v6.18.46, commit
    1f99e9ab748f).  The examples are the acceptance cases A1 to A3 of
    dispatch://OSSV-287.

    PART 1 (A1 to A3) and PART 3 (A5's pair calls, A6's bind) name no
    constructor this change adds: every Example there is stated through
    [check_syscall] and [syscall_spec_witness] alone, so the same text
    also compiles against the model before this change, where each of
    them is FALSE — socketpair(AF_UNIX) declined there, so every run below
    stops at its first call, and bind on a pair end declined.  That is the
    fail-before half of each pair; this file is the pass-after half.

    PART 2 pins the exact model states the calls produce, so a change to
    what an end carries is caught here and not only in a run.

    Both directions are pinned, as in [Checks.Cases.Fs.Pipe]: an answer
    beside the answer the model refuses, and a decline beside the same call
    answered on a neighbouring state. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
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
Definition sp_m0 : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** Addresses.  [sv_addr]: the 8-byte [int sv[2]].  [src_addr]: a source
    buffer whose first two bytes are "hi" and whose next 8190 are zero.
    [dst_addr]: a 64-byte destination.  [opt_addr]/[len_addr]: a socket
    option and its length.  [pfd_addr]/[ts_addr]: one [struct pollfd] and a
    zero [struct timespec] for ppoll. *)
Definition sv_addr : word := Z_to_bv 64 4096.
Definition src_addr : word := Z_to_bv 64 8192.
Definition dst_addr : word := Z_to_bv 64 24576.
Definition opt_addr : word := Z_to_bv 64 28672.
Definition len_addr : word := Z_to_bv 64 28680.
Definition pfd_addr : word := Z_to_bv 64 32768.
Definition ts_addr : word := Z_to_bv 64 32784.

Definition in_range (a : word) (lo n : Z) : bool :=
  ((lo <=? bv_unsigned a) && (bv_unsigned a <? lo + n))%Z.

(** What the process may READ.  [opt] is the 4-byte option value at
    [opt_addr], [len] the 4-byte length at [len_addr], [pfd_fd] and
    [pfd_ev] the [fd] and [events] of the pollfd. *)
Definition sp_rmem (opt len pfd_fd pfd_ev : Z) : word -> option byte :=
  fun a =>
    if in_range a 8192 8192 then
      Some (if Z.eqb (bv_unsigned a) 8192 then Z_to_bv 8 104          (* 'h' *)
            else if Z.eqb (bv_unsigned a) 8193 then Z_to_bv 8 105     (* 'i' *)
            else Z_to_bv 8 0)
    else if in_range a 28672 4 then
      Some (nth (Z.to_nat (bv_unsigned a - 28672)%Z) (Z_to_le_bytes 4 opt) (Z_to_bv 8 0))
    else if in_range a 28680 4 then
      Some (nth (Z.to_nat (bv_unsigned a - 28680)%Z) (Z_to_le_bytes 4 len) (Z_to_bv 8 0))
    else if in_range a 32768 8 then
      Some (nth (Z.to_nat (bv_unsigned a - 32768)%Z)
              (Z_to_le_bytes 4 pfd_fd ++ Z_to_le_bytes 2 pfd_ev ++ Z_to_le_bytes 2 0)
              (Z_to_bv 8 0))
    else if in_range a 32784 16 then Some (Z_to_bv 8 0)
    else None.

(** What the process may WRITE: [sv], the destination, the option and its
    length, and the pollfd. *)
Definition sp_wmem : word -> option byte :=
  fun a =>
    if (in_range a 4096 8 || in_range a 24576 64 || in_range a 28672 12
        || in_range a 32768 8)%bool
    then Some (Z_to_bv 8 0) else None.

Definition mk (sysno : Z) (args : list word) : SyscallInput :=
  mkInput (Z_to_bv 64 sysno) args (sp_rmem 0 4 4 1) sp_wmem.

Definition mk_opt (sysno : Z) (args : list word) (opt len : Z) : SyscallInput :=
  mkInput (Z_to_bv 64 sysno) args (sp_rmem opt len 4 1) sp_wmem.

Definition mk_poll (args : list word) (fd ev : Z) : SyscallInput :=
  mkInput (Z_to_bv 64 73) args (sp_rmem 0 4 fd ev) sp_wmem.

(** socketpair(AF_UNIX = 1, [ty], 0, sv): SOCK_STREAM is 1, SOCK_NONBLOCK
    is 2048. *)
Definition socketpair_in (ty : Z) : SyscallInput :=
  mk 199 [Z_to_bv 64 1; Z_to_bv 64 ty; 0; sv_addr; 0; 0].

(** Its success: return 0 and the two [put_user] stores of 3 and 4. *)
Definition socketpair_ok : SyscallEffect :=
  mkEffect 0 [(sv_addr, [3; 0; 0; 0]); (sv_addr + Z_to_bv 64 4, [4; 0; 0; 0])] [].

(** write(fd, src, n) returning [k], having read the first [k] bytes. *)
Definition write_in (fd n : Z) : SyscallInput :=
  mk 64 [Z_to_bv 64 fd; src_addr; Z_to_bv 64 n; 0; 0; 0].
Definition write_ok (k : Z) : SyscallEffect :=
  with_copyins [(src_addr, Z.to_nat k)] (mkEffect (Z_to_bv 64 k) [] []).

(** read(fd, dst, n) returning the bytes [bs]. *)
Definition read_in (fd n : Z) : SyscallInput :=
  mk 63 [Z_to_bv 64 fd; dst_addr; Z_to_bv 64 n; 0; 0; 0].
Definition read_ok (bs : list byte) : SyscallEffect :=
  mkEffect (Z_to_bv 64 (Z.of_nat (length bs)))
           (match bs with [] => [] | _ => [(dst_addr, bs)] end) [].

Definition errno_eff (e : Z) : SyscallEffect := mkEffect (errno_ret e) [] [].

(** close(fd) = 0. *)
Definition close_ok (fd : Z) : SyscallInput * SyscallEffect :=
  (mk 57 [Z_to_bv 64 fd; 0; 0; 0; 0; 0], mkEffect 0 [] []).

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
  match run_accepted sp_m0 steps with
  | Some m => Some (check_syscall i e m)
  | None => None
  end.

(** The verdict is [CheckOk] with some model. *)
Definition is_ok (r : option check_result) : bool :=
  match r with Some (CheckOk _ _) => true | _ => false end.

Definition pair : list (SyscallInput * SyscallEffect) := [(socketpair_in 1, socketpair_ok)].
Definition pair_nb : list (SyscallInput * SyscallEffect) := [(socketpair_in 2049, socketpair_ok)].

(* =========================================================================
   PART 1 — A1: the pair carries a byte, and the blocking read declines
   ========================================================================= *)

(** A1, the pass half: socketpair(AF_UNIX, SOCK_STREAM, 0) returns 0 with 3
    and 4 stored, a byte written to 3 is read from 4, and the read takes
    exactly what was written ("h", one byte of a 64-byte read: the queue
    runs out, [unix_stream_read_generic]'s do-while). *)
Example a1_pair_carries_a_byte :
  is_ok (after (pair ++ [(write_in 3 1, write_ok 1)])
               (read_in 4 64) (read_ok [Z_to_bv 8 104])) = true.
Proof. check_eq. Qed.

(** ...and the other direction, 4 to 3: the pair is symmetric. *)
Example a1_pair_carries_a_byte_back :
  is_ok (after (pair ++ [(write_in 4 2, write_ok 2)])
               (read_in 3 64) (read_ok [Z_to_bv 8 104; Z_to_bv 8 105])) = true.
Proof. check_eq. Qed.

(** The negative half: a read claiming bytes that were never written is
    refused, and so is a read claiming the written byte on the WRITER's
    own end, whose queue is empty (a non-blocking pair, so that end answers
    -EAGAIN rather than declining). *)
Example a1_pair_refuses_invented_bytes :
  after (pair ++ [(write_in 3 1, write_ok 1)])
        (read_in 4 64) (read_ok [Z_to_bv 8 104; Z_to_bv 8 105]) = Some CheckReject
  /\ after (pair_nb ++ [(write_in 3 1, write_ok 1)])
           (read_in 3 64) (read_ok [Z_to_bv 8 104]) = Some CheckReject.
Proof. split; check_eq. Qed.

(** A1, the declining case — the acceptance pair of spec v3: the two runs
    differ only in whether the peer wrote first.  With no write, the
    blocking read of the empty queue, whose peer is open, DECLINES: Linux
    would sleep in [unix_stream_data_wait] forever, and the model declines
    rather than represent a run that cannot progress
    ([Fs.ReadWrite.stream_read]).  Offered end of file, it still declines:
    the decline is not a refusal of one answer. *)
Example a1_blocking_read_of_empty_queue_declines :
  after pair (read_in 4 64) (read_ok []) = Some CheckUnmodeled
  /\ after pair (read_in 4 64) (errno_eff EAGAIN) = Some CheckUnmodeled.
Proof. split; check_eq. Qed.

(** The same read on a NON-BLOCKING pair (SOCK_NONBLOCK) is answered:
    -EAGAIN, and end of file is refused.  So the decline above is about
    blocking, not about the descriptor. *)
Example a1_nonblocking_read_of_empty_queue_is_eagain :
  is_ok (after pair_nb (read_in 4 64) (errno_eff EAGAIN)) = true
  /\ after pair_nb (read_in 4 64) (read_ok []) = Some CheckReject.
Proof. split; check_eq. Qed.

(** After the peer's shutdown(SHUT_WR), the empty queue is end of file,
    blocking or not: RCV_SHUTDOWN on this end, mirrored by
    [unix_shutdown].  Bytes the peer sent before it are still read first. *)
Example a1_read_after_peer_shutdown_is_eof :
  is_ok (after (pair ++ [(mk 210 [Z_to_bv 64 3; Z_to_bv 64 1; 0; 0; 0; 0], mkEffect 0 [] [])])
               (read_in 4 64) (read_ok [])) = true
  /\ is_ok (after (pair ++ [(write_in 3 1, write_ok 1);
                           (mk 210 [Z_to_bv 64 3; Z_to_bv 64 1; 0; 0; 0; 0], mkEffect 0 [] [])])
                  (read_in 4 64) (read_ok [Z_to_bv 8 104])) = true.
Proof. split; check_eq. Qed.

(** After the peer CLOSES, the empty read declines: Linux answers end of
    file, or first one -ECONNRESET when the closing end left bytes
    unread, and the kind-blind close does not record which
    ([State.StreamEnd]).  The survivor's send is answered: -EPIPE. *)
Example a1_after_peer_close :
  after (pair ++ [close_ok 3]) (read_in 4 64) (read_ok []) = Some CheckUnmodeled
  /\ is_ok (after (pair ++ [close_ok 3])
                  (mk 206 [Z_to_bv 64 4; src_addr; Z_to_bv 64 1; Z_to_bv 64 16384; 0; 0])
                  (errno_eff EPIPE)) = true.
Proof. split; check_eq. Qed.

(** A1's witness: [syscall_spec_witness] gives an outcome for the
    socketpair call, and the checker accepts that outcome. *)
Example a1_socketpair_witness_is_accepted :
  match syscall_spec_witness (socketpair_in 1) sp_m0 with
  | Ok eff m' evs => check_syscall (socketpair_in 1) eff sp_m0 = CheckOk m' evs
  | Unmodeled => False
  end.
Proof. check_eq. Qed.

(** The witness of the declined read is [Unmodeled]. *)
Example a1_declined_read_witness_is_unmodeled :
  match run_accepted sp_m0 pair with
  | Some m => syscall_spec_witness (read_in 4 64) m = Unmodeled
  | None => False
  end.
Proof. check_eq. Qed.

(* =========================================================================
   PART 1 — A2: ppoll on a pair end
   ========================================================================= *)

(** ppoll(pfd, 1, &{0,0}, NULL, 8) on fd [fd] asking [ev]. *)
Definition ppoll_in (fd ev : Z) : SyscallInput :=
  mk_poll [pfd_addr; Z_to_bv 64 1; ts_addr; 0; Z_to_bv 64 8; 0] fd ev.

(** The outcome the model gives for a ppoll after [steps]: its return and
    its writes, read off the witness, with the checker accepting it. *)
Definition ppoll_answer (steps : list (SyscallInput * SyscallEffect)) (fd ev : Z)
    : option (word * list (word * list byte)) :=
  match run_accepted sp_m0 steps with
  | Some m =>
      match syscall_spec_witness (ppoll_in fd ev) m with
      | Ok eff m' evs =>
          match check_syscall (ppoll_in fd ev) eff m with
          | CheckOk m'' _ => Some (eff_ret eff, eff_writes eff)
          | _ => None
          end
      | Unmodeled => None
      end
  | None => None
  end.

(** A2: a pair end with a non-empty inbound queue polls READABLE — return
    1, [revents = POLLIN] — and one with an empty queue polls NOT READY,
    return 0 and [revents = 0], under a zero timeout.  POLLIN is 1. *)
Example a2_ppoll_readable_with_bytes_queued :
  ppoll_answer (pair ++ [(write_in 3 1, write_ok 1)]) 4 1
  = Some (Z_to_bv 64 1, [(pfd_addr + Z_to_bv 64 6, [1; 0])]).
Proof. check_eq. Qed.

Example a2_ppoll_not_ready_when_empty :
  ppoll_answer pair 4 1 = Some (Z_to_bv 64 0, [(pfd_addr + Z_to_bv 64 6, [0; 0])]).
Proof. check_eq. Qed.

(** Writable is answered too where it is decided: the peer's queue is
    empty, so [unix_writable] holds — POLLOUT (4) is reported. *)
Example a2_ppoll_writable_with_empty_peer_queue :
  ppoll_answer pair 3 4 = Some (Z_to_bv 64 1, [(pfd_addr + Z_to_bv 64 6, [4; 0])]).
Proof. check_eq. Qed.

(** ...and the peer's shutdown(SHUT_WR) is reported: POLLIN and, asked
    for, POLLRDHUP (0x2000), with the queue empty. *)
Example a2_ppoll_rdhup_after_peer_shutdown :
  ppoll_answer (pair ++ [(mk 210 [Z_to_bv 64 3; Z_to_bv 64 1; 0; 0; 0; 0], mkEffect 0 [] [])])
               4 (1 + 8192)
  = Some (Z_to_bv 64 1, [(pfd_addr + Z_to_bv 64 6, [1; 32])]).
Proof. check_eq. Qed.

(** After the peer CLOSES, ppoll on the survivor answers with EPOLLERR
    set or clear: EPOLLERR is in every filter, and whether the close left
    [sk_err] is not recorded, so the model admits both.  POLLIN (1) and
    POLLHUP (16) are set either way.  The witness gives the answer
    without EPOLLERR (17), the one with it (25) is accepted too, and
    POLLHUP alone is refused. *)
Example a2_ppoll_after_peer_close_answers_with_epollerr_set_or_clear :
  ppoll_answer (pair ++ [close_ok 3]) 4 1
  = Some (Z_to_bv 64 1, [(pfd_addr + Z_to_bv 64 6, [17; 0])])
  /\ is_ok (after (pair ++ [close_ok 3]) (ppoll_in 4 1)
              (with_copyins [(ts_addr, 16%nat); (pfd_addr, 8%nat)]
                 (mkEffect 1 [(pfd_addr + Z_to_bv 64 6, [25; 0])] []))) = true
  /\ after (pair ++ [close_ok 3]) (ppoll_in 4 1)
       (with_copyins [(ts_addr, 16%nat); (pfd_addr, 8%nat)]
          (mkEffect 1 [(pfd_addr + Z_to_bv 64 6, [16; 0])] [])) = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** A pipe end still declines ppoll, beside a pair end that answers, in
    the same model: pipe2 makes 3 and 4, socketpair makes 5 and 6. *)
Definition pipe_fildes : word := Z_to_bv 64 4096.
Example a2_pipe_end_still_declines :
  match run_accepted sp_m0
          [(mk 59 [pipe_fildes; 0; 0; 0; 0; 0],
            mkEffect 0 [(pipe_fildes, [3; 0; 0; 0; 4; 0; 0; 0])] []);
           (socketpair_in 1,
            mkEffect 0 [(sv_addr, [5; 0; 0; 0]); (sv_addr + Z_to_bv 64 4, [6; 0; 0; 0])] [])] with
  | Some m =>
      syscall_spec_witness (ppoll_in 3 1) m = Unmodeled
      /\ (match syscall_spec_witness (ppoll_in 6 1) m with
          | Ok _ _ _ => True | Unmodeled => False end)
  | None => False
  end.
Proof. vm_compute. split; [reflexivity|exact I]. Qed.

(* =========================================================================
   PART 1 — A3: SO_SNDBUF, SO_RCVBUF and the other levels
   ========================================================================= *)

(** setsockopt(fd, level, name, opt, 4) with the option value [v]. *)
Definition setsockopt_in (fd level name v : Z) : SyscallInput :=
  mk_opt 208 [Z_to_bv 64 fd; Z_to_bv 64 level; Z_to_bv 64 name; opt_addr; Z_to_bv 64 4; 0] v 4.
Definition setsockopt_ok : SyscallEffect :=
  with_copyins [(opt_addr, 4%nat)] (mkEffect 0 [] []).

(** getsockopt(fd, level, name, opt, &len) with [*len = 4]: the value the
    model reports, read off the witness, with the checker accepting it. *)
Definition getsockopt_in (fd level name : Z) : SyscallInput :=
  mk_opt 209 [Z_to_bv 64 fd; Z_to_bv 64 level; Z_to_bv 64 name; opt_addr; len_addr; 0] 0 4.
Definition getsockopt_answer (steps : list (SyscallInput * SyscallEffect)) (fd level name : Z)
    : option (word * list (word * list byte)) :=
  match run_accepted sp_m0 steps with
  | Some m =>
      match syscall_spec_witness (getsockopt_in fd level name) m with
      | Ok eff _ _ =>
          match check_syscall (getsockopt_in fd level name) eff m with
          | CheckOk _ _ => Some (eff_ret eff, eff_writes eff)
          | _ => None
          end
      | Unmodeled => None
      end
  | None => None
  end.

(** SOL_SOCKET = 1, SO_SNDBUF = 7, SO_RCVBUF = 8, IPPROTO_TCP = 6,
    TCP_NODELAY = 1. *)

(** A3: SO_SNDBUF stores the DOUBLED value — 10000 asked, 20000 reported —
    and the default before any set is [net.core.wmem_default] = 212992. *)
Example a3_sndbuf_default_is_wmem_default :
  getsockopt_answer pair 3 1 7
  = Some (Z_to_bv 64 0, [(opt_addr, Z_to_le_bytes 4 212992); (len_addr, [4; 0; 0; 0])]).
Proof. check_eq. Qed.

Example a3_sndbuf_set_is_doubled :
  getsockopt_answer (pair ++ [(setsockopt_in 3 1 7 10000, setsockopt_ok)]) 3 1 7
  = Some (Z_to_bv 64 0, [(opt_addr, Z_to_le_bytes 4 20000); (len_addr, [4; 0; 0; 0])]).
Proof. check_eq. Qed.

(** ...CLAMPED below at SOCK_MIN_SNDBUF = 2 * (2048 + 256) = 4608 ... *)
Example a3_sndbuf_set_is_raised_to_the_floor :
  getsockopt_answer (pair ++ [(setsockopt_in 3 1 7 100, setsockopt_ok)]) 3 1 7
  = Some (Z_to_bv 64 0, [(opt_addr, Z_to_le_bytes 4 4608); (len_addr, [4; 0; 0; 0])]).
Proof. check_eq. Qed.

(** ...and above at 2 * [net.core.wmem_max] = 2 * 4194304. *)
Example a3_sndbuf_set_is_clamped_to_wmem_max :
  getsockopt_answer (pair ++ [(setsockopt_in 3 1 7 (2 ^ 31), setsockopt_ok)]) 3 1 7
  = Some (Z_to_bv 64 0, [(opt_addr, Z_to_le_bytes 4 8388608); (len_addr, [4; 0; 0; 0])]).
Proof. check_eq. Qed.

(** The negative half of the set: a setsockopt claiming an errno is
    refused. *)
Example a3_sndbuf_set_refuses_an_errno :
  after pair (setsockopt_in 3 1 7 10000) (with_copyins [(opt_addr, 4%nat)] (errno_eff EINVAL))
  = Some CheckReject.
Proof. check_eq. Qed.

(** A3: a write is REFUSED once the peer's queue reaches the writer's send
    buffer.  With SO_SNDBUF set to the floor (4608), a non-blocking write of
    4608 bytes onto an empty queue is admitted; the next write finds 4608
    queued, [sock_alloc_send_pskb] admits nothing, and only -EAGAIN is
    accepted. *)
Definition small_buf : list (SyscallInput * SyscallEffect) :=
  pair_nb ++ [(setsockopt_in 3 1 7 100, setsockopt_ok); (write_in 3 4608, write_ok 4608)].

Example a3_write_refused_when_peer_queue_is_full :
  is_ok (after small_buf (write_in 3 1) (errno_eff EAGAIN)) = true
  /\ after small_buf (write_in 3 1) (write_ok 1) = Some CheckReject.
Proof. split; check_eq. Qed.

(** The control: before the queue fills, the same one-byte write is
    admitted — so the refusal above is the queue's, not the descriptor's. *)
Example a3_write_admitted_before_the_queue_fills :
  is_ok (after (pair_nb ++ [(setsockopt_in 3 1 7 100, setsockopt_ok)])
               (write_in 3 1) (write_ok 1)) = true.
Proof. check_eq. Qed.

(** A3: SO_RCVBUF has NO EFFECT on writes.  The reader's SO_RCVBUF at its
    floor (2304) leaves the writer's 212992-byte budget in force: an
    8192-byte write onto the empty queue moves all of it, which the floor
    alone would forbid if [sk_rcvbuf] bounded the queue. *)
Example a3_rcvbuf_does_not_bound_writes :
  is_ok (after (pair_nb ++ [(setsockopt_in 4 1 8 100, setsockopt_ok)])
               (write_in 3 8192) (write_ok 8192)) = true.
Proof. check_eq. Qed.

(** ...while SO_RCVBUF is stored and reported: max(2 * 100, 2304) = 2304. *)
Example a3_rcvbuf_is_reported :
  getsockopt_answer (pair ++ [(setsockopt_in 4 1 8 100, setsockopt_ok)]) 4 1 8
  = Some (Z_to_bv 64 0, [(opt_addr, Z_to_le_bytes 4 2304); (len_addr, [4; 0; 0; 0])]).
Proof. check_eq. Qed.

(** A3: every level other than SOL_SOCKET.  setsockopt at IPPROTO_TCP —
    curl's TCP_NODELAY — is -EOPNOTSUPP ([unix_setsockopt]'s first test),
    and NOT the -ENOPROTOOPT an AF_INET socket gives for an unknown level. *)
Example a3_setsockopt_tcp_level_is_eopnotsupp :
  is_ok (after pair (setsockopt_in 3 6 1 1) (errno_eff EOPNOTSUPP)) = true
  /\ after pair (setsockopt_in 3 6 1 1) (errno_eff ENOPROTOOPT) = Some CheckReject
  /\ after pair (setsockopt_in 3 6 1 1) setsockopt_ok = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** getsockopt at IPPROTO_TCP is -EOPNOTSUPP too: [unix_stream_ops] has no
    [.getsockopt]. *)
Example a3_getsockopt_tcp_level_is_eopnotsupp :
  match getsockopt_answer pair 3 6 1 with
  | Some (r, ws) => r = errno_ret EOPNOTSUPP /\ ws = []
  | None => False
  end.
Proof. vm_compute. split; [apply bv_eq; reflexivity|reflexivity]. Qed.

(* =========================================================================
   PART 2 — the exact states an end carries
   ========================================================================= *)

(** A fresh end of the default build: empty queue, blocking, both buffers
    at [net.core.wmem_default] = [rmem_default] = 212992, no shutdown bit,
    no error. *)
Definition st0 : StreamEnd := stream_fresh false 212992 212992.

(** socketpair installs (0, false) at 3 and (0, true) at 4, both fresh;
    nothing else in the model moves. *)
Example socketpair_installs_two_fresh_ends :
  check_syscall (socketpair_in 1) socketpair_ok sp_m0
  = CheckOk (with_fds (fd_insert (fd_insert (m_fds sp_m0) 3 (FdStream 0 false st0))
                                 4 (FdStream 0 true st0)) sp_m0) [].
Proof. check_eq. Qed.

(** A write through 3 lands in 4's queue — the receiving end's — and 3 is
    unchanged. *)
Example write_appends_to_the_peer_queue :
  match run_accepted sp_m0 (pair ++ [(write_in 3 1, write_ok 1)]) with
  | Some m =>
      fd_lookup (m_fds m) 4 = Some (FdStream 0 true (se_set_rx st0 [Z_to_bv 8 104]))
      /\ fd_lookup (m_fds m) 3 = Some (FdStream 0 false st0)
  | None => False
  end.
Proof. vm_compute. split; repeat first [reflexivity | (apply bv_eq; reflexivity) | progress f_equal]. Qed.

(** Closing 3 removes 3 and leaves 4's entry exactly as it was: the close
    is kind-blind ([Fs.Open.close_spec]), and 4 reads the close off the
    table. *)
Example close_moves_nothing_but_the_entry :
  match run_accepted sp_m0 (pair ++ [close_ok 3]) with
  | Some m => fd_lookup (m_fds m) 3 = None
              /\ fd_lookup (m_fds m) 4 = Some (FdStream 0 true st0)
  | None => False
  end.
Proof. vm_compute. split; repeat first [reflexivity | (apply bv_eq; reflexivity) | progress f_equal]. Qed.

(* =========================================================================
   PART 3 — A5: the calls curl_fuzzer_proto_http makes on its pair
   ========================================================================= *)

(** The sequences below are the two that the census of
    curl_fuzzer_proto_http (curl-fuzzer de8de30, release recipe
    v2026.10.0-src, plain build sha256 42869c82...) found on its pair, as
    calls with their arguments and results.  The census:
    /home/sami/work/workers/curl-lps-pair/a5/SUMMARY.md, section 4, on
    ossv-agent-open5; the sequences are rows 1 and 3 of its
    [pairs/pairs.sequences.tsv].  Descriptor numbers differ (the model
    gives 3 and 4, the traced process 5 and 6) and the byte counts are
    shortened; every call, flag word and result kind is the traced one.
    sv[0] = 3 is the mock server's end, sv[1] = 4 curl's.

    So these replay the pair half of A5 through the checker.  They say
    nothing about the calls that are not on the pair (eventfd2, the IPv6
    probe socket, rt_sigaction), which the census also found. *)

(** fcntl(fd, F_GETFL) = [r]; fcntl(fd, F_SETFL, O_RDWR | O_NONBLOCK) = 0
    (0x802, the word the traced kernel saw). *)
Definition getfl (fd r : Z) : SyscallInput * SyscallEffect :=
  (mk 25 [Z_to_bv 64 fd; Z_to_bv 64 3; 0; 0; 0; 0], mkEffect (Z_to_bv 64 r) [] []).
Definition setfl_nonblock (fd : Z) : SyscallInput * SyscallEffect :=
  (mk 25 [Z_to_bv 64 fd; Z_to_bv 64 4; Z_to_bv 64 2050; 0; 0; 0], mkEffect 0 [] []).

(** sendto(fd, src, n, MSG_NOSIGNAL, NULL, 0) = n. *)
Definition sendto_all (fd n : Z) : SyscallInput * SyscallEffect :=
  (mk 206 [Z_to_bv 64 fd; src_addr; Z_to_bv 64 n; Z_to_bv 64 16384; 0; 0],
   with_copyins [(src_addr, Z.to_nat n)] (mkEffect (Z_to_bv 64 n) [] [])).

(** The first [n] bytes of the source buffer: "hi" and zeros. *)
Definition src_bytes (n : nat) : list byte :=
  firstn n ([Z_to_bv 8 104; Z_to_bv 8 105] ++ repeat (Z_to_bv 8 0) n).

(** recvfrom(fd, dst, len, 0, NULL, NULL) returning [bs]. *)
Definition recvfrom_got (fd len : Z) (bs : list byte) : SyscallInput * SyscallEffect :=
  (mk 207 [Z_to_bv 64 fd; dst_addr; Z_to_bv 64 len; 0; 0; 0], read_ok bs).
Definition recvfrom_err (fd len e : Z) : SyscallInput * SyscallEffect :=
  (mk 207 [Z_to_bv 64 fd; dst_addr; Z_to_bv 64 len; 0; 0; 0], errno_eff e).

(** read(fd, dst, 4096) returning [bs], or an errno. *)
Definition read_got (fd : Z) (bs : list byte) : SyscallInput * SyscallEffect :=
  (read_in fd 4096, read_ok bs).
Definition read_err (fd e : Z) : SyscallInput * SyscallEffect :=
  (read_in fd 4096, errno_eff e).

(** shutdown(fd, SHUT_WR) = 0. *)
Definition shut_wr (fd : Z) : SyscallInput * SyscallEffect :=
  (mk 210 [Z_to_bv 64 fd; Z_to_bv 64 1; 0; 0; 0; 0], mkEffect 0 [] []).

(** setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &1, 4) = -EOPNOTSUPP. *)
Definition tcp_nodelay (fd : Z) : SyscallInput * SyscallEffect :=
  (setsockopt_in fd 6 1 1, errno_eff EOPNOTSUPP).

(** getsockname(fd, dst, &len) with [len = 128] in: 0, [len = 2] out and the
    unnamed AF_UNIX address [sun_family = 1] at [dst]. *)
Definition getsockname_unnamed (fd : Z) : SyscallInput * SyscallEffect :=
  (mk_opt 204 [Z_to_bv 64 fd; dst_addr; len_addr; 0; 0; 0] 0 128,
   with_copyins [(len_addr, 4%nat)]
     (mkEffect 0 [(len_addr, [2; 0; 0; 0]); (dst_addr, [1; 0])] [])).

(** Sequence 1, 80 of the 140 traced pairs: the response preloaded, the
    request sent, the response read, end of file, both ends closed. *)
Definition a5_sequence_1 : list (SyscallInput * SyscallEffect) :=
  [ (socketpair_in 1, socketpair_ok);
    getfl 3 2; setfl_nonblock 3;
    sendto_all 3 10;
    shut_wr 3;
    tcp_nodelay 4;
    getfl 4 2; setfl_nonblock 4;
    getsockname_unnamed 4; getsockname_unnamed 4;
    sendto_all 4 7;
    recvfrom_got 4 16384 (src_bytes 10);
    getfl 4 2050;
    recvfrom_got 4 16384 [];
    close_ok 4; close_ok 3 ].

Example a5_sequence_1_is_accepted :
  match run_accepted sp_m0 a5_sequence_1 with
  | Some m => fd_lookup (m_fds m) 3 = None /\ fd_lookup (m_fds m) 4 = None
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** Sequence 3, the chunked responses: a part sent, read, then -EAGAIN on
    curl's end; the mock server reads the request, then -EAGAIN on its own;
    the next part; and only then SHUT_WR and end of file. *)
Definition a5_sequence_3 : list (SyscallInput * SyscallEffect) :=
  [ (socketpair_in 1, socketpair_ok);
    getfl 3 2; setfl_nonblock 3;
    sendto_all 3 6;
    tcp_nodelay 4;
    getfl 4 2; setfl_nonblock 4;
    getsockname_unnamed 4; getsockname_unnamed 4;
    sendto_all 4 7;
    recvfrom_got 4 1024 (src_bytes 6);
    recvfrom_err 4 1024 EAGAIN;
    read_got 3 (src_bytes 7);
    read_err 3 EAGAIN;
    sendto_all 3 2;
    shut_wr 3;
    recvfrom_got 4 1024 (src_bytes 2);
    recvfrom_got 4 1024 [];
    close_ok 4; close_ok 3 ].

Example a5_sequence_3_is_accepted :
  match run_accepted sp_m0 a5_sequence_3 with
  | Some m => fd_lookup (m_fds m) 3 = None /\ fd_lookup (m_fds m) 4 = None
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** The control that keeps the two above from being vacuous: the same
    sequence with curl's FIRST recvfrom claiming end of file — before the
    mock server's SHUT_WR, with bytes queued — is refused at that step. *)
Example a5_sequence_with_a_false_eof_is_refused :
  run_accepted sp_m0
    (firstn 10 a5_sequence_3 ++ [recvfrom_got 4 1024 []]) = None.
Proof. check_eq. Qed.

(** bind(fd, sa_addr, len) where [sa_addr] holds the [struct sockaddr_in]
    curl binds, {AF_INET, port 12345, 0.0.0.0}: [sin_family] 2
    little-endian, [sin_port] 12345 = 0x3039 big-endian, [sin_addr] and
    [sin_zero] zero.  The rest of memory is [sp_rmem]'s. *)
Definition sa_addr : word := Z_to_bv 64 36864.
Definition sin_any_12345 : list byte :=
  [Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 48; Z_to_bv 8 57] ++ repeat (Z_to_bv 8 0) 12.
Definition bind_in (fd len : Z) : SyscallInput :=
  mkInput (Z_to_bv 64 200) [Z_to_bv 64 fd; sa_addr; Z_to_bv 64 len; 0; 0; 0]
    (fun a => if in_range a 36864 16
              then Some (nth (Z.to_nat (bv_unsigned a - 36864)%Z) sin_any_12345 (Z_to_bv 8 0))
              else sp_rmem 0 4 4 1 a)
    sp_wmem.

(** A6, the census's kind D6 (dispatch://OSSV-286/artifact/census-wave3-md):
    curl binds that 16-byte AF_INET address on its end, sv[1] = 4.  Linux
    copies the 16 bytes in ([move_addr_to_kernel]) and [unix_bind] answers
    -EINVAL, because [unix_validate_addr] finds a family other than
    AF_UNIX; nothing moves.  The success curl asks for is refused, and so
    is the -EINVAL without the copy-in. *)
Example a6_bind_af_inet_on_a_pair_end_is_einval :
  match run_accepted sp_m0 pair with
  | Some m =>
      check_syscall (bind_in 4 16) (with_copyins [(sa_addr, 16%nat)] (errno_eff EINVAL)) m
        = CheckOk m []
      /\ check_syscall (bind_in 4 16) (with_copyins [(sa_addr, 16%nat)] (mkEffect 0 [] [])) m
           = CheckReject
      /\ check_syscall (bind_in 4 16) (errno_eff EINVAL) m = CheckReject
  | None => False
  end.
Proof. vm_compute. split; [|split]; reflexivity. Qed.
