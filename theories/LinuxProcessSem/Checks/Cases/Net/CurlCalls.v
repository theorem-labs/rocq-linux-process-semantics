(** * LinuxProcessSem.Checks.Cases.Net.CurlCalls — worked examples over the calls beside the pair that curl_fuzzer_proto_http makes: eventfd2 (19), socket (198) for a datagram socket, ioctl (29) SIOCGIFINDEX, and rt_sigaction (134) for SIGPIPE

    The acceptance cases A5 (the four call groups beside the pair) and A6
    of dispatch://OSSV-287, spec version 5.  Linux v6.18.46 (commit
    1f99e9ab748f) throughout: fs/eventfd.c, net/socket.c,
    net/core/dev_ioctl.c, kernel/signal.c.

    PART 1 names no constructor that this change adds: every Example is
    stated through [check_syscall] and [syscall_spec_witness] alone, so
    the same text compiles against the model before this change.  There
    every one of them is FALSE, because each run below starts with a call
    that the model declined: eventfd2 past its flag gate, socket for a
    datagram socket, and any SIGPIPE install.  That is the fail-before
    half of each pair.  The controls say so where they are. *)

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

(** The start: [init_model]'s three channels, the default launch (SIGPIPE
    at SIG_DFL), so the next descriptor is 3. *)
Definition cc_m0 : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** A memory view from a list of regions, each a base address and its
    bytes. *)
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

(** Addresses: [buf] an 8-byte transfer buffer, [act] and [oact] two
    [struct sigaction]s (24 bytes each on riscv64: handler, flags, mask),
    [ifr] a 40-byte [struct ifreq], [pfd] one pollfd and [ts] a zero
    timespec, [set] an 8-byte signal set, [fildes] an [int[2]]. *)
Definition buf_a : Z := 0x9000.
Definition act_a : Z := 0x9100.
Definition oact_a : Z := 0x9200.
Definition ifr_a : Z := 0x9300.
Definition pfd_a : Z := 0x9400.
Definition ts_a : Z := 0x9410.
Definition set_a : Z := 0x9500.
Definition fildes_a : Z := 0x9600.

(** Everything the examples write is writable: 64 bytes at each address. *)
Definition cc_wmem : word -> option byte :=
  region_mem (map (fun a => (a, zeros 64)) [buf_a; act_a; oact_a; ifr_a; pfd_a; set_a; fildes_a]).

Definition w (z : Z) : word := Z_to_bv 64 z.

Definition mk (sysno : Z) (args : list Z) (rs : list (Z * list byte)) : SyscallInput :=
  mkInput (w sysno) (map w args) (region_mem rs) cc_wmem.

Definition le (n : nat) (z : Z) : list byte := Z_to_le_bytes n z.

(** A [struct sigaction] for [act]. *)
Definition sigact (handler flags mask : Z) : list byte := le 8 handler ++ le 8 flags ++ le 8 mask.

Definition SA_RESTART_flag : Z := 0x10000000.

(** Run the steps through the checker; a step with [None] takes the
    effect from [syscall_spec_witness] (only used for calls whose spec has
    one outcome); every step must be accepted.  The model after the last,
    or [None] at the first step not accepted. *)
Fixpoint run_steps (m : Model) (steps : list (SyscallInput * option SyscallEffect))
    : option Model :=
  match steps with
  | [] => Some m
  | (i, oe) :: rest =>
      let e := match oe with
               | Some e => Some e
               | None => match syscall_spec_witness i m with
                         | Ok e _ _ => Some e
                         | Unmodeled => None
                         end
               end in
      match e with
      | None => None
      | Some e =>
          match check_syscall i e m with
          | CheckOk m' _ => run_steps m' rest
          | _ => None
          end
      end
  end.

(** The verdict of one more call after an accepted run. *)
Definition after (steps : list (SyscallInput * option SyscallEffect))
    (i : SyscallInput) (e : SyscallEffect) : option check_result :=
  match run_steps cc_m0 steps with
  | Some m => Some (check_syscall i e m)
  | None => None
  end.
Definition is_ok (r : option check_result) : bool :=
  match r with Some (CheckOk _ _) => true | _ => false end.

(** The effect the model's witness gives after a run, with the checker
    accepting it: its return and its writes. *)
Definition answer (steps : list (SyscallInput * option SyscallEffect)) (i : SyscallInput)
    : option (word * list (word * list byte)) :=
  match run_steps cc_m0 steps with
  | Some m =>
      match syscall_spec_witness i m with
      | Ok e _ _ => match check_syscall i e m with
                    | CheckOk _ _ => Some (eff_ret e, eff_writes e)
                    | _ => None
                    end
      | Unmodeled => None
      end
  | None => None
  end.

Definition errno_eff (e : Z) : SyscallEffect := mkEffect (errno_ret e) [] [].

(* =========================================================================
   PART 1 — the eventfd (R10)
   ========================================================================= *)

(** eventfd2(0, EFD_CLOEXEC | EFD_NONBLOCK), curl's multi wakeup: fd 3. *)
Definition efd_create : SyscallInput * option SyscallEffect :=
  (mk 19 [0; 0x80000 + 0x800]%Z [], Some (mkEffect (w 3) [] [])).

(** read(3, buf, 8). *)
Definition efd_read_in : SyscallInput := mk 63 [3; buf_a; 8]%Z [].

(** write(3, buf, 8) of the counter value [v]. *)
Definition efd_write (v : Z) : SyscallInput * option SyscallEffect :=
  (mk 64 [3; buf_a; 8]%Z [(buf_a, le 8 v)],
   Some (with_copyins [(w buf_a, 8%nat)] (mkEffect (w 8) [] []))).

(** A zero counter on a non-blocking eventfd: -EAGAIN, as the census
    shows; a read claiming 8 bytes is refused. *)
Example efd_zero_counter_read_is_eagain :
  is_ok (after [efd_create] efd_read_in (errno_eff EAGAIN)) = true
  /\ after [efd_create] efd_read_in (mkEffect (w 8) [(w buf_a, le 8 0)] []) = Some CheckReject.
Proof. split; check_eq. Qed.

(** A write adds to the counter, and a read returns it and resets it:
    5 is read back, then the next read is -EAGAIN again. *)
Example efd_write_then_read :
  is_ok (after [efd_create; efd_write 5] efd_read_in
               (mkEffect (w 8) [(w buf_a, le 8 5)] [])) = true
  /\ is_ok (after [efd_create; efd_write 5; (efd_read_in, Some (mkEffect (w 8) [(w buf_a, le 8 5)] []))]
                  efd_read_in (errno_eff EAGAIN)) = true
  /\ after [efd_create; efd_write 5] efd_read_in
           (mkEffect (w 8) [(w buf_a, le 8 4)] []) = Some CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** A read of fewer than 8 bytes is -EINVAL ([eventfd_read]'s first test). *)
Example efd_short_read_is_einval :
  is_ok (after [efd_create] (mk 63 [3; buf_a; 4]%Z []) (errno_eff EINVAL)) = true.
Proof. check_eq. Qed.

(** F_GETFL is O_RDWR | O_NONBLOCK; ppoll asking POLLIN | POLLOUT on a zero
    counter answers POLLOUT (4) alone ([eventfd_poll]). *)
Example efd_getfl_and_ppoll :
  answer [efd_create] (mk 25 [3; 3]%Z []) = Some (w 2050, [])
  /\ answer [efd_create] (mk 73 [pfd_a; 1; ts_a; 0; 8]%Z
                              [(pfd_a, le 4 3 ++ le 2 5 ++ le 2 0); (ts_a, zeros 16)])
     = Some (w 1, [(w pfd_a + w 6, [4; 0])]).
Proof. split; check_eq. Qed.

(* =========================================================================
   PART 1 — the datagram socket and SIOCGIFINDEX (R11)
   ========================================================================= *)

(** socket(AF_INET6, SOCK_DGRAM, 0) — curl's IPv6 probe — then close. *)
Example dgram_probe_socket_then_close :
  is_ok (after [(mk 198 [10; 2; 0]%Z [], Some (mkEffect (w 3) [] []))]
               (mk 57 [3]%Z []) (mkEffect 0 [] [])) = true.
Proof. check_eq. Qed.

(** socket(AF_UNIX, SOCK_DGRAM | SOCK_CLOEXEC, 0), then
    ioctl(3, SIOCGIFINDEX, &ifr) with the name "lo": 0, and the 40 bytes
    written back with ifr_ifindex = 1 at offset 16. *)
Definition ifr_lo : list byte := [Z_to_bv 8 108; Z_to_bv 8 111] ++ zeros 38.
Definition ifr_lo_out : list byte := [Z_to_bv 8 108; Z_to_bv 8 111] ++ zeros 14 ++ le 4 1 ++ zeros 20.
Definition unix_dgram : SyscallInput * option SyscallEffect :=
  (mk 198 [1; 2 + 0x80000; 0]%Z [], Some (mkEffect (w 3) [] [])).

Example siocgifindex_lo_is_one :
  answer [unix_dgram] (mk 29 [3; 0x8933; ifr_a]%Z [(ifr_a, ifr_lo)])
  = Some (w 0, [(w ifr_a, ifr_lo_out)]).
Proof. check_eq. Qed.

(** Another name declines: the interface table is the environment's. *)
Example siocgifindex_other_name_declines :
  after [unix_dgram] (mk 29 [3; 0x8933; ifr_a]%Z
                        [(ifr_a, [Z_to_bv 8 101; Z_to_bv 8 116; Z_to_bv 8 104; Z_to_bv 8 48] ++ zeros 36)])
        (mkEffect 0 [] []) = Some CheckUnmodeled.
Proof. check_eq. Qed.

(* =========================================================================
   PART 1 — rt_sigaction(SIGPIPE) (R12)
   ========================================================================= *)

(** rt_sigaction(SIGPIPE, act, oact, 8) with [act] = {SIG_IGN, SA_RESTART,
    0}, as musl's signal(SIGPIPE, SIG_IGN) passes it: 0, and the PREVIOUS
    action {SIG_DFL, 0, 0} in [oact].  The three shapes follow: old action
    only reads back what the install stored, flags included; action only
    restores SIG_DFL. *)
Definition sig_both : SyscallInput :=
  mk 134 [13; act_a; oact_a; 8]%Z [(act_a, sigact 1 SA_RESTART_flag 0)].
Definition sig_oact_only : SyscallInput := mk 134 [13; 0; oact_a; 8]%Z [].
Definition sig_act_only (h : Z) : SyscallInput :=
  mk 134 [13; act_a; 0; 8]%Z [(act_a, sigact h SA_RESTART_flag 0)].

Example sigpipe_install_reports_the_previous_action :
  answer [] sig_both = Some (w 0, [(w oact_a, sigact 0 0 0)]).
Proof. check_eq. Qed.

Example sigpipe_old_action_reads_back_the_stored_flags :
  answer [(sig_both, None)] sig_oact_only = Some (w 0, [(w oact_a, sigact 1 SA_RESTART_flag 0)]).
Proof. check_eq. Qed.

Example sigpipe_action_only_restores_the_default :
  answer [(sig_both, None)] (sig_act_only 0) = Some (w 0, [])
  /\ answer [(sig_both, None); (sig_act_only 0, None)] sig_oact_only
     = Some (w 0, [(w oact_a, sigact 0 SA_RESTART_flag 0)]).
Proof. split; check_eq. Qed.

(** A real handler declines: the chosen boundary. *)
Example sigpipe_real_handler_declines :
  syscall_spec_witness (mk 134 [13; act_a; 0; 8]%Z [(act_a, sigact 0x10000 0 0)]) cc_m0 = Unmodeled.
Proof. check_eq. Qed.

(** A pending SIGPIPE is discarded by an install of SIG_IGN, so the
    process lives.  pipe2 makes 3 and 4; the read end 3 is closed;
    SIGPIPE is blocked; write(4) is -EPIPE and leaves SIGPIPE pending;
    then SIG_IGN is installed and SIGPIPE unblocked.  The control: the
    same run without the install ends by signal 13 at the unblock. *)
Definition block_pipe (how : Z) : SyscallInput * option SyscallEffect :=
  (mk 135 [how; set_a; 0; 8]%Z [(set_a, le 8 0x1000)], None).
Definition broken_pipe_write : list (SyscallInput * option SyscallEffect) :=
  [ (mk 59 [fildes_a; 0]%Z [], Some (mkEffect 0 [(w fildes_a, [3; 0; 0; 0; 4; 0; 0; 0])] []));
    (mk 57 [3]%Z [], Some (mkEffect 0 [] []));
    block_pipe 0;
    (mk 64 [4; buf_a; 1]%Z [(buf_a, [Z_to_bv 8 120])], None) ].

Example sigpipe_ign_install_discards_the_pending_signal :
  match run_steps cc_m0 (broken_pipe_write ++ [(sig_act_only 1, None); block_pipe 1]) with
  | Some m => m_halted m = None
  | None => False
  end
  /\ match run_steps cc_m0 (broken_pipe_write ++ [block_pipe 1]) with
     | Some m => m_halted m <> None
     | None => False
     end.
Proof. vm_compute. split; [reflexivity|discriminate]. Qed.
