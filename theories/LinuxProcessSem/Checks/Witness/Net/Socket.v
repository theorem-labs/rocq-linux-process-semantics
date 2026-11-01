(** * LinuxProcessSem.Checks.Witness.Net.Socket — the socket (198), bind (200),
      listen (201), accept (202), getsockname (204), getpeername (205),
      sendto (206), setsockopt (208), getsockopt (209), shutdown (210),
      sendmsg (211), accept4 (242) witnesses, and their proofs

    Mirrors [Sys/Net/Socket.v], which answers to Linux [net/socket.c]:
    this file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude Uaccess Fs.ReadWrite.

(* =========================================================================
   socket (198) — witness: the concrete argument errno where the spec has
   one, the environment-failure branch (errno 12) where it succeeds, or
   the fail-closed [Unmodeled]
   ========================================================================= *)

(** As [openat_witness] does, this takes the ERRNO side of the [alt] on
    every arm that can succeed: [socket_errnos] is headed by ENOMEM, and
    so is [socket_dgram_errnos] for either family, so
    [errno_head_witness] supplies the outcome and the success branch's
    [lowest_fd] never has to be shown inhabited. *)
Definition socket_witness (domain type protocol : word) (m : Model)
    : outcome SyscallEffect :=
  let tu := bv_unsigned (abi_low32 type) in
  let flagbits := Z.ldiff tu SOCK_TYPE_MASK in
  if negb (Z.eqb (Z.ldiff flagbits (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)
  then ret_outcome (errno_ret EINVAL) m          (* unknown flag bit *)
  else if negb (Z.eqb (Z.land flagbits SOCK_NONBLOCK) 0)
  then Unmodeled                                 (* SOCK_NONBLOCK: no O_NONBLOCK notion *)
  else
    let ty  := Z.land tu SOCK_TYPE_MASK in
    let fam := sint32 domain in
    let pro := sint32 protocol in
    if orb (Z.ltb fam 0) (Z.leb NPROTO fam)
    then ret_outcome (errno_ret EAFNOSUPPORT) m
    else if Z.leb SOCK_MAX ty then ret_outcome (errno_ret EINVAL) m
    else if socket_dgram_b fam ty pro
    then ret_outcome (errno_ret witness_errno) m   (* env-failure branch *)
    else if negb (Z.eqb fam AF_INET) then Unmodeled  (* registration the model cannot know *)
    else if Z.eqb ty SOCK_PACKET then Unmodeled      (* rewritten to PF_PACKET above the
                                                        protocol range — see [socket_spec] *)
    else if orb (Z.ltb pro 0) (Z.leb IPPROTO_MAX pro)
    then ret_outcome (errno_ret EINVAL) m
    else if Z.eqb ty SOCK_STREAM then
      if orb (Z.eqb pro IPPROTO_SCTP) (Z.eqb pro IPPROTO_MPTCP) then Unmodeled
      else if negb (orb (Z.eqb pro IPPROTO_IP) (Z.eqb pro IPPROTO_TCP))
      then ret_outcome (errno_ret EPROTONOSUPPORT) m
      else ret_outcome (errno_ret witness_errno) m   (* env-failure branch *)
    else if orb (Z.eqb ty SOCK_DGRAM) (Z.eqb ty SOCK_RAW)
    then Unmodeled                                   (* SOCK_DGRAM / SOCK_RAW; SOCK_PACKET is above *)
    else if orb (Z.eqb ty SOCK_SEQPACKET) (Z.eqb ty SOCK_DCCP)
    then Unmodeled                                   (* sctp and dccp register these *)
    else ret_outcome (errno_ret ESOCKTNOSUPPORT) m.

Lemma socket_witness_ok : forall domain type protocol i m,
  socket_spec domain type protocol i m (socket_witness domain type protocol m).
Proof.
  intros. unfold socket_spec, socket_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
  destruct (negb (Z.eqb (Z.ldiff (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
                           (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)).
  { apply pure_ok. }
  destruct (negb (Z.eqb (Z.land (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
                           SOCK_NONBLOCK) 0)).
  { apply unmodeled_intro. }
  cbv beta zeta.
  destruct (orb (Z.ltb (sint32 domain) 0) (Z.leb NPROTO (sint32 domain))).
  { apply pure_ok. }
  destruct (Z.leb SOCK_MAX (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)).
  { apply pure_ok. }
  destruct (socket_dgram_b (sint32 domain)
              (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
              (sint32 protocol)).
  { apply alt_l. eapply bind_step; [|apply pure_ok].
    unfold socket_dgram_errnos, socket_errnos.
    destruct (Z.eqb (sint32 domain) AF_INET6); apply errno_head_witness. }
  destruct (negb (Z.eqb (sint32 domain) AF_INET)). { apply unmodeled_intro. }
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_PACKET).
  { apply unmodeled_intro. }
  destruct (orb (Z.ltb (sint32 protocol) 0) (Z.leb IPPROTO_MAX (sint32 protocol))).
  { apply alt_l. apply pure_ok. }
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_STREAM).
  - destruct (orb (Z.eqb (sint32 protocol) IPPROTO_SCTP)
                  (Z.eqb (sint32 protocol) IPPROTO_MPTCP)).
    { apply unmodeled_intro. }
    destruct (negb (orb (Z.eqb (sint32 protocol) IPPROTO_IP)
                        (Z.eqb (sint32 protocol) IPPROTO_TCP))).
    { apply alt_l. apply pure_ok. }
    apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
  - destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DGRAM)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_RAW)).
    { apply unmodeled_intro. }
    destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_SEQPACKET)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DCCP)).
    { apply unmodeled_intro. }
    apply alt_l. apply pure_ok.
Qed.

(* =========================================================================
   bind (200) — witness: the concrete argument errno, the -EADDRINUSE
   failure branch where the spec succeeds, or the fail-closed [Unmodeled]
   ========================================================================= *)

Definition bind_witness (fd addrp addrlen : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdSocket sk) =>
      let al := sint32 addrlen in
      if orb (Z.ltb al 0) (Z.ltb SOCKADDR_STORAGE_SIZE al)
      then ret_outcome (errno_ret EINVAL) m
      else if Z.eqb al 0 then ret_outcome (errno_ret EINVAL) m
      else
      match copy_bytes_map (in_mem i) addrp al with
      | None => ret_outcome (errno_ret EFAULT) m
      | Some bs =>
          (* PAST THE COPY: [move_addr_to_kernel] has moved [al] bytes, so
             every outcome exhibited below has to carry the ledger
             [bind_spec] records there.  [outcome_copyins] attaches it and
             leaves an [Unmodeled] alone, which is what [record_copyins]
             does on the spec side. *)
          outcome_copyins [(addrp, Z.to_nat al)]
          (
          if Z.ltb al SOCKADDR_IN_SIZE then ret_outcome (errno_ret EINVAL) m
          else
            if negb (orb (Z.eqb (sa_family_of bs) AF_INET)
                         (andb (Z.eqb (sa_family_of bs) AF_UNSPEC)
                               (Z.eqb (sin_addr_of bs) INADDR_ANY)))
            then ret_outcome (errno_ret EAFNOSUPPORT) m
            else if negb (Z.eqb (sin_addr_of bs) INADDR_ANY) then Unmodeled
            else if negb (Z.eqb (sin_port_of bs) 0) then Unmodeled
            else
              match sk with
              | SkFresh => ret_outcome (errno_ret EADDRINUSE) m  (* [get_port] can fail *)
              | SkBound | SkListening
              | SkConnected _ _ (NCons _ _) | SkConnected _ _ NFin =>
                  ret_outcome (errno_ret EINVAL) m
              | SkConnected _ _ NRst | SkConnected _ _ NTimedOut
              | SkReset _ _ => Unmodeled
              end)
      end
  | Some (FdStream _ _ _) => Unmodeled          (* [unix_bind]: a name the model lacks *)
  | Some (FdDgram _) => Unmodeled               (* a socket: an address it lacks *)
  | Some _ => ret_outcome (errno_ret ENOTSOCK) m
  end.

Lemma bind_witness_ok : forall fd addrp addrlen i m,
  bind_spec fd addrp addrlen i m (bind_witness fd addrp addrlen i m).
Proof.
  intros. unfold bind_spec, bind_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|];
    cbv beta iota zeta; try apply pure_ok; try apply unmodeled_intro.
  (* socket *)
  destruct (orb (Z.ltb (sint32 addrlen) 0)
                (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))); [apply pure_ok|].
  destruct (Z.eqb (sint32 addrlen) 0); [apply pure_ok|].
  destruct (copy_bytes_map (in_mem i) addrp (sint32 addrlen)) as [bs|];
    [|apply pure_ok].
  apply record_copyins_outcome.
  destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE); [apply pure_ok|].
  destruct (negb (orb (Z.eqb (sa_family_of bs) AF_INET)
                      (andb (Z.eqb (sa_family_of bs) AF_UNSPEC)
                            (Z.eqb (sin_addr_of bs) INADDR_ANY)))); [apply pure_ok|].
  destruct (negb (Z.eqb (sin_addr_of bs) INADDR_ANY)); [apply unmodeled_intro|].
  destruct (negb (Z.eqb (sin_port_of bs) 0)); [apply unmodeled_intro|].
  destruct sk as [| | |peer ch rx|peer ch].
  - (* fresh: the one arm that can bind, taken on its -EADDRINUSE branch *)
    apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
  - apply pure_ok.                                   (* bound: -EINVAL *)
  - apply pure_ok.                                   (* listening: -EINVAL *)
  - (* connected: -EINVAL while the connection is live or half-closed,
       and fail-closed once the peer's error is pending — a reset
       connection is unbound again and Linux autobinds it *)
    destruct rx; [apply pure_ok|apply unmodeled_intro|apply unmodeled_intro|apply pure_ok].
  - apply unmodeled_intro.                           (* reset: see [bind_spec] *)
Qed.

(* =========================================================================
   listen (201) — deterministic except on a fresh socket, where the
   autobind's -EADDRINUSE is the witness
   ========================================================================= *)

Definition listen_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdSocket sk) =>
      match sk with
      | SkConnected _ _ _ => ret_outcome (errno_ret EINVAL) m
      | SkReset _ _ => ret_outcome (errno_ret EINVAL) m
      | SkListening => ret_outcome (Z_to_bv 64 0) m       (* re-listen *)
      | SkBound =>
          ret_outcome (Z_to_bv 64 0)
            (with_fds (fd_insert (m_fds m) fd (FdSocket SkListening)) m)
      | SkFresh => ret_outcome (errno_ret EADDRINUSE) m   (* the autobind's failure *)
      end
  | Some (FdStream _ _ _) => ret_outcome (errno_ret EINVAL) m   (* unbound pair end *)
  | Some (FdDgram _) => Unmodeled                              (* a socket: declined *)
  | Some _ => ret_outcome (errno_ret ENOTSOCK) m
  end.

Lemma listen_witness_ok : forall fd backlog i m,
  listen_spec fd backlog i m (listen_witness fd m).
Proof.
  intros. unfold listen_spec, listen_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|];
    cbv beta iota zeta; try apply pure_ok; try apply unmodeled_intro.
  destruct sk as [| | |peer ch rx|peer ch]; try apply pure_ok.
  - (* fresh: the autobind's -EADDRINUSE *)
    apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
  - (* bound: it already has a port, so [get_port] cannot fail *)
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

(* =========================================================================
   accept4 (242), which accept (202) reaches with flags = 0 — witness:
   the concrete fd/flag errno, the environment-failure branch (errno 12)
   where a connection would be handed over, or the fail-closed [Unmodeled]
   ========================================================================= *)

(** Taking the errno side of the [alt] is what keeps this cheap: the
    success branch would have to exhibit a free fd AND the accepted
    socket's state, and [accept_errnos] is headed by ENOMEM. *)
Definition accept4_witness (fd addrp flags : word) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some e =>
      let fl := bv_unsigned (abi_low32 flags) in
      if negb (Z.eqb (Z.ldiff fl (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)
      then ret_outcome (errno_ret EINVAL) m
      else if negb (Z.eqb (Z.land fl SOCK_NONBLOCK) 0) then Unmodeled
      else
      match e with
      | FdSocket sk =>
          if negb (w_is0 addrp) then Unmodeled   (* the peer address is not reported *)
          else
          match sk with
          | SkListening => ret_outcome (errno_ret witness_errno) m
          | _ => ret_outcome (errno_ret EINVAL) m
          end
      | FdStream _ _ _ => Unmodeled              (* a socket: see [accept4_spec] *)
      | FdDgram _ => Unmodeled                   (* a socket: see [accept4_spec] *)
      | _ => if negb (Z.ltb (bv_unsigned (alloc_fd (m_fds m))) NR_OPEN_DEFAULT)
             then Unmodeled
             else ret_outcome (errno_ret ENOTSOCK) m
      end
  end.

Lemma accept4_witness_ok : forall fd addrp addrlenp flags i m,
  accept4_spec fd addrp addrlenp flags i m (accept4_witness fd addrp flags m).
Proof.
  intros. unfold accept4_spec, accept4_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (fd_lookup (m_fds m) fd) as [e|]; [|apply pure_ok].
  cbv beta iota zeta.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 flags))
                           (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)); [apply pure_ok|].
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags)) SOCK_NONBLOCK) 0));
    [apply unmodeled_intro|].
  destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af];
    try apply unmodeled_intro;
    try (destruct (negb (Z.ltb (bv_unsigned (alloc_fd (m_fds m))) NR_OPEN_DEFAULT));
         [apply unmodeled_intro | apply alt_l; apply pure_ok]).
  destruct (negb (w_is0 addrp)); [apply unmodeled_intro|].
  destruct sk as [| | |peer ch rx|peer ch];
    try (apply alt_l; apply pure_ok).
  (* listening: the one arm that can hand a connection over, taken on its
     environment-failure branch *)
  apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
Qed.

(* =========================================================================
   connect (203) — wholly deterministic: every answered arm is a fixed
   errno or 0, and the attempt itself is declined, so the witness is a
   mirror of the spec rather than a choice among its alternatives
   ========================================================================= *)

Definition connect_witness (fd addrp addrlen : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some e =>
      let al := sint32 addrlen in
      if orb (Z.ltb al 0) (Z.ltb SOCKADDR_STORAGE_SIZE al)
      then ret_outcome (errno_ret EINVAL) m
      else
      match move_addr_bytes (in_mem i) addrp al with
      | None => ret_outcome (errno_ret EFAULT) m
      | Some bs =>
          outcome_copyins (if Z.eqb al 0 then [] else [(addrp, length bs)])
          (match e with
           | FdSocket sk =>
               if Z.ltb al SA_FAMILY_SIZE then ret_outcome (errno_ret EINVAL) m
               else if Z.eqb (sa_family_of bs) AF_UNSPEC then
                 match sk with
                 | SkFresh => ret_outcome (Z_to_bv 64 0) m
                 | SkBound | SkListening
                 | SkConnected _ _ _ | SkReset _ _ => Unmodeled
                 end
               else
                 match sk with
                 | SkListening | SkConnected _ _ _ | SkReset _ _ =>
                     ret_outcome (errno_ret EISCONN) m
                 | SkFresh | SkBound =>
                     if Z.ltb al SOCKADDR_IN_SIZE
                     then ret_outcome (errno_ret EINVAL) m
                     else if negb (Z.eqb (sa_family_of bs) AF_INET)
                     then ret_outcome (errno_ret EAFNOSUPPORT) m
                     else Unmodeled
                 end
           | FdStream _ _ _ => Unmodeled        (* [unix_stream_connect]: a name lookup *)
           | FdDgram _ => Unmodeled             (* a peer [State.FdDgram] lacks *)
           | _ => ret_outcome (errno_ret ENOTSOCK) m
           end)
      end
  end.

Lemma connect_witness_ok : forall fd addrp addrlen i m,
  connect_spec fd addrp addrlen i m (connect_witness fd addrp addrlen i m).
Proof.
  intros. unfold connect_spec, connect_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|];
    cbv beta iota zeta; [ | | | | | | | | | | | | | | apply pure_ok ].
  all: destruct (orb (Z.ltb (sint32 addrlen) 0)
                     (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen)));
       cbv beta iota zeta; [ apply pure_ok | ].
  all: destruct (move_addr_bytes (in_mem i) addrp (sint32 addrlen))
         as [bs|]; cbv beta iota zeta; [ | apply pure_ok ].
  all: apply record_copyins_outcome; cbv beta iota zeta.
  (* every non-socket entry answers -ENOTSOCK below the copy, and the
     stream-pair end and the datagram socket decline there *)
  all: try apply pure_ok.
  all: try apply unmodeled_intro.
  (* the socket arm *)
  destruct (Z.ltb (sint32 addrlen) SA_FAMILY_SIZE); [apply pure_ok|].
  destruct (Z.eqb (sa_family_of bs) AF_UNSPEC).
  - destruct sk as [| | |peer ch rx|peer ch];
      solve [ apply pure_ok | apply unmodeled_intro ].
  - destruct sk as [| | |peer ch rx|peer ch];
      try solve [ apply pure_ok | apply unmodeled_intro ].
    all: destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE); [apply pure_ok|].
    all: destruct (negb (Z.eqb (sa_family_of bs) AF_INET));
         [apply pure_ok|apply unmodeled_intro].
Qed.

(* =========================================================================
   getsockname (204), getpeername (205), setsockopt (208), getsockopt (209),
   shutdown (210) — witness: the spec read straight off
   ========================================================================= *)

(** A stream-pair witness walks its spec test for test: split the
    witness's next test and the spec's is decided with it; each leaf is
    an [Ok] the spec returns, a decline, a recorded ledger, or a
    descriptor-table update. *)
Local Ltac wsplit :=
  match goal with
  | |- _ _ _ (if ?b then _ else _) => destruct b
  | |- _ _ _ (match ?x with _ => _ end) => destruct x
  end; cbv beta iota.

Local Ltac wsolve :=
  repeat (first [ wsplit | apply record_copyins_outcome ]);
  first [ apply pure_ok
        | apply unmodeled_intro
        | (eapply bind_step; [apply modify_ok|]; apply pure_ok) ].

(** [Net.Socket.stream_getname] read straight off: every arm is fixed by
    the input, so the witness IS the spec's one outcome. *)
Definition stream_getname_witness (uaddr ulen : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (access_okb ulen 4) then ret_outcome (errno_ret EFAULT) m
  else
  match read_bytes_map (in_mem i) ulen (Z_to_bv 64 4) with
  | None =>
      match read_bytes_map (in_mem i) ulen (Z_to_bv 64 1) with
      | None => ret_outcome (errno_ret EFAULT) m
      | Some _ => Unmodeled
      end
  | Some lbs =>
      outcome_copyins [(ulen, 4%nat)]
        (let len := Z.min (sint32 (le_bytes_to_word lbs)) 2 in
         if (len <? 0)%Z then ret_outcome (errno_ret EINVAL) m
         else if negb (user_range_writable i ulen 4) then Unmodeled
         else if Z.eqb len 0
         then Ok (mkEffect (Z_to_bv 64 0) [(ulen, word_le4 (Z_to_bv 64 2))] []) m []
         else if user_range_writable i uaddr len
         then Ok (mkEffect (Z_to_bv 64 0)
                    [(ulen, word_le4 (Z_to_bv 64 2));
                     (uaddr, firstn (Z.to_nat len) unix_unnamed_addr)] []) m []
         else match read_bytes_map (in_wmem i) uaddr (Z_to_bv 64 1) with
              | None =>
                  Ok (mkEffect (errno_ret EFAULT) [(ulen, word_le4 (Z_to_bv 64 2))] [])
                     m []
              | Some _ => Unmodeled
              end)
  end.

Lemma stream_getname_witness_ok : forall uaddr ulen i m,
  stream_getname uaddr ulen i i m (stream_getname_witness uaddr ulen i m).
Proof.
  intros. unfold stream_getname, stream_getname_witness. cbv beta zeta.
  wsolve.
Qed.

(** [Net.Socket.stream_setsockopt] read straight off: its one model
    update is the [with_fds] the spec's [set_fds] performs. *)
Definition stream_setsockopt_witness (fd id : word) (side : bool) (st : StreamEnd)
    (optname optval optlen : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  let on := bv_unsigned optname in
  if negb ((on =? SO_SNDBUF) || (on =? SO_RCVBUF))%Z then Unmodeled
  else if (bv_unsigned optlen <? 4)%Z then ret_outcome (errno_ret EINVAL) m
  else
  match copy_bytes_map (in_mem i) optval 4 with
  | None => ret_outcome (errno_ret EFAULT) m
  | Some vbs =>
      let v := bv_unsigned (le_bytes_to_word vbs) in
      outcome_copyins [(optval, 4%nat)]
        (ret_outcome (Z_to_bv 64 0)
           (with_fds (fd_insert (m_fds m) fd
                        (FdStream id side
                           (if (on =? SO_SNDBUF)%Z
                            then se_set_sndbuf st (sndbuf_after_set (m_kernel m) v)
                            else se_set_rcvbuf st (rcvbuf_after_set (m_kernel m) v)))) m))
  end.

Lemma stream_setsockopt_witness_ok : forall fd id side st optname optval optlen i m,
  stream_setsockopt fd id side st optname optval optlen i m i m
    (stream_setsockopt_witness fd id side st optname optval optlen i m).
Proof.
  intros. unfold stream_setsockopt, stream_setsockopt_witness. cbv beta zeta.
  wsolve.
Qed.

(** [Net.Socket.stream_getsockopt] read straight off. *)
Definition stream_getsockopt_witness (st : StreamEnd) (optname optval optlenp : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  let on := bv_unsigned optname in
  if negb ((on =? SO_SNDBUF) || (on =? SO_RCVBUF))%Z then Unmodeled
  else
  match copy_bytes_map (in_mem i) optlenp 4 with
  | None => ret_outcome (errno_ret EFAULT) m
  | Some lbs =>
      outcome_copyins [(optlenp, 4%nat)]
        (let len := sint32 (le_bytes_to_word lbs) in
         if (len <? 0)%Z then ret_outcome (errno_ret EINVAL) m
         else
         let len' := Z.min len 4 in
         let v := if (on =? SO_SNDBUF)%Z then se_sndbuf st else se_rcvbuf st in
         let vw := if Z.eqb len' 0 then []
                   else [(optval, firstn (Z.to_nat len') (word_le4 (Z_to_bv 64 v)))] in
         if negb (Z.eqb len' 0 || user_range_writable i optval len')%bool then
           match read_bytes_map (in_wmem i) optval (Z_to_bv 64 1) with
           | None => ret_outcome (errno_ret EFAULT) m
           | Some _ => Unmodeled
           end
         else if user_range_writable i optlenp 4
         then Ok (mkEffect (Z_to_bv 64 0)
                    (vw ++ [(optlenp, word_le4 (Z_to_bv 64 len'))]) []) m []
         else match read_bytes_map (in_wmem i) optlenp (Z_to_bv 64 1) with
              | None => Ok (mkEffect (errno_ret EFAULT) vw []) m []
              | Some _ => Unmodeled
              end)
  end.

Lemma stream_getsockopt_witness_ok : forall st optname optval optlenp i m,
  stream_getsockopt st optname optval optlenp i i m
    (stream_getsockopt_witness st optname optval optlenp i m).
Proof.
  intros. unfold stream_getsockopt, stream_getsockopt_witness. cbv beta zeta.
  wsolve.
Qed.

(** [Net.Socket.stream_shutdown] read straight off: 0, over the table
    the spec builds. *)
Definition stream_shutdown_witness (fd id : word) (side : bool) (st : StreamEnd)
    (how : word) (m : Model) : outcome SyscallEffect :=
  let rd := negb (Z.eqb (bv_unsigned how) SHUT_WR) in
  let wr := negb (Z.eqb (bv_unsigned how) SHUT_RD) in
  let fds1 := fd_insert (m_fds m) fd (FdStream id side (se_add_shut st rd wr)) in
  ret_outcome (Z_to_bv 64 0)
    (with_fds (match stream_peer fds1 id side with
               | None => fds1
               | Some (pfd, pst) =>
                   fd_insert fds1 pfd (FdStream id (negb side) (se_add_shut pst wr rd))
               end) m).

Lemma stream_shutdown_witness_ok : forall fd id side st how i m,
  stream_shutdown fd id side st how m i m (stream_shutdown_witness fd id side st how m).
Proof.
  intros. unfold stream_shutdown, stream_shutdown_witness. cbv beta zeta.
  eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

(** Every AF_INET arm of the five is an errno, a fixed 0, or [Unmodeled]
    — none draws from an [errno_from] set and none is an [alt] — and so
    is every stream-pair arm, whose answers are fixed by the input and
    the end; so each witness is its spec read straight off, and none of
    them can get stuck.  The descriptor half is [Net.Socket.sock_fd] in
    all five; what differs is the socket arm, which is the whole point of
    there being five.  See [Net.Socket.getsockname_spec] and its four
    neighbours. *)
Definition getsockname_witness (fd : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match sock_fd m fd with
  | SoErr e => ret_outcome (errno_ret e) m
  | SoInet _ => Unmodeled
  | SoPair _ _ _ => stream_getname_witness (in_arg i 1) (in_arg i 2) i m
  | SoInert _ => Unmodeled                 (* [State.FdDgram]: declined *)
  end.

Lemma getsockname_witness_ok : forall fd i m,
  getsockname_spec fd i m (getsockname_witness fd i m).
Proof.
  intros. unfold getsockname_spec, getsockname_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e]; cbv beta iota zeta.
  - apply unmodeled_intro.
  - eapply bind_step; [apply input_ok|]. cbv beta.
    apply stream_getname_witness_ok.
  - apply unmodeled_intro.
  - apply pure_ok.
Qed.

Definition getpeername_witness (fd : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match sock_fd m fd with
  | SoErr e => ret_outcome (errno_ret e) m
  | SoInet sk =>
      match sk with
      | SkFresh           => ret_outcome (errno_ret ENOTCONN) m
      | SkBound           => ret_outcome (errno_ret ENOTCONN) m
      | SkListening       => ret_outcome (errno_ret ENOTCONN) m
      | SkReset _ _       => ret_outcome (errno_ret ENOTCONN) m
      | SkConnected _ _ _ => Unmodeled
      end
  | SoPair _ _ _ => stream_getname_witness (in_arg i 1) (in_arg i 2) i m
  | SoInert _ => Unmodeled
  end.

Lemma getpeername_witness_ok : forall fd i m,
  getpeername_spec fd i m (getpeername_witness fd i m).
Proof.
  intros. unfold getpeername_spec, getpeername_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e]; cbv beta iota zeta.
  - destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta;
      solve [apply pure_ok | apply unmodeled_intro].
  - eapply bind_step; [apply input_ok|]. cbv beta.
    apply stream_getname_witness_ok.
  - apply unmodeled_intro.
  - apply pure_ok.
Qed.

Definition setsockopt_witness (fd level optlen : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  match sock_fd m fd with
  | SoErr e => ret_outcome (errno_ret e) m
  | SoInet _ =>
      if int32_neg optlen then ret_outcome (errno_ret EINVAL) m
      else if negb (sock_level_known level) then ret_outcome (errno_ret ENOPROTOOPT) m
      else Unmodeled
  | SoPair id side st =>
      if int32_neg optlen then ret_outcome (errno_ret EINVAL) m
      else if negb (Z.eqb (bv_unsigned level) SOL_SOCKET)
      then ret_outcome (errno_ret EOPNOTSUPP) m
      else stream_setsockopt_witness fd id side st (in_arg i 2) (in_arg i 3) optlen i m
  | SoInert _ => Unmodeled
  end.

Lemma setsockopt_witness_ok : forall fd level optlen i m,
  setsockopt_spec fd level optlen i m (setsockopt_witness fd level optlen i m).
Proof.
  intros. unfold setsockopt_spec, setsockopt_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e]; cbv beta iota zeta.
  - destruct (int32_neg optlen); cbv beta iota zeta; [apply pure_ok|].
    destruct (negb (sock_level_known level)); cbv beta iota zeta;
      [apply pure_ok | apply unmodeled_intro].
  - destruct (int32_neg optlen); cbv beta iota zeta; [apply pure_ok|].
    destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)); cbv beta iota zeta;
      [apply pure_ok|].
    eapply bind_step; [apply input_ok|]. cbv beta.
    apply stream_setsockopt_witness_ok.
  - apply unmodeled_intro.
  - apply pure_ok.
Qed.

(** [outcome_copyins] attaches the [optlen] ledger and leaves an
    [Unmodeled] alone, which is what [record_copyins] does on the spec
    side.  It sits OUTSIDE the level test for the same reason it does
    there: the read precedes the dispatch. *)
Definition getsockopt_witness (fd level optlenp : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  match sock_fd m fd with
  | SoErr e => ret_outcome (errno_ret e) m
  | SoInet _ =>
      outcome_copyins (getsockopt_optlen_read i optlenp)
        (if negb (sock_level_known level)
         then ret_outcome (errno_ret EOPNOTSUPP) m
         else Unmodeled)
  | SoPair _ _ st =>
      outcome_copyins (getsockopt_optlen_read i optlenp)
        (if negb (Z.eqb (bv_unsigned level) SOL_SOCKET)
         then ret_outcome (errno_ret EOPNOTSUPP) m
         else stream_getsockopt_witness st (in_arg i 2) (in_arg i 3) optlenp i m)
  | SoInert _ => Unmodeled
  end.

Lemma getsockopt_witness_ok : forall fd level optlenp i m,
  getsockopt_spec fd level optlenp i m (getsockopt_witness fd level optlenp i m).
Proof.
  intros. unfold getsockopt_spec, getsockopt_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e]; cbv beta iota zeta.
  - apply record_copyins_outcome.
    destruct (negb (sock_level_known level)); cbv beta iota zeta;
      [apply pure_ok | apply unmodeled_intro].
  - apply record_copyins_outcome.
    destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)); cbv beta iota zeta;
      [apply pure_ok|].
    apply stream_getsockopt_witness_ok.
  - apply unmodeled_intro.
  - apply pure_ok.
Qed.

Definition shutdown_witness (fd how : word) (m : Model)
    : outcome SyscallEffect :=
  match sock_fd m fd with
  | SoErr e => ret_outcome (errno_ret e) m
  | SoInet sk =>
      if negb (shut_how_ok how) then ret_outcome (errno_ret EINVAL) m
      else
        match sk with
        | SkListening =>
            if (bv_unsigned how =? SHUT_WR)%Z
            then ret_outcome (Z_to_bv 64 0) m
            else Unmodeled
        | _ => Unmodeled
        end
  | SoPair id side st =>
      if negb (shut_how_ok how) then ret_outcome (errno_ret EINVAL) m
      else stream_shutdown_witness fd id side st how m
  | SoInert _ => Unmodeled
  end.

Lemma shutdown_witness_ok : forall fd how i m,
  shutdown_spec fd how i m (shutdown_witness fd how m).
Proof.
  intros. unfold shutdown_spec, shutdown_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e]; cbv beta iota zeta.
  - destruct (negb (shut_how_ok how)); cbv beta iota zeta; [apply pure_ok|].
    destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta;
      try apply unmodeled_intro.
    destruct (bv_unsigned how =? SHUT_WR)%Z; cbv beta iota zeta;
      [apply pure_ok | apply unmodeled_intro].
  - destruct (negb (shut_how_ok how)); cbv beta iota zeta; [apply pure_ok|].
    apply stream_shutdown_witness_ok.
  - apply unmodeled_intro.
  - apply pure_ok.
Qed.

(* =========================================================================
   sendto (206) and sendmsg (211) — witness: the deterministic errno, or
   the ONE-BYTE delivery on a live connection
   ========================================================================= *)

(** The socket half both calls share, so the send's one [choose] is
    discharged once rather than twice.

    [Net.Socket.SendGoes] is the only arm carrying nondeterminism, and
    the witness takes the SHORTEST admissible send rather than the
    longest: exactly one byte, which is [Fs.ReadWrite.writev_witness]'s
    choice on a channel and for the same reason.  A one-byte prefix needs
    only [count <> 0] to satisfy [Net.Socket.send_bytes]'s
    [1 <= length ds <= total], where the full prefix would additionally
    need the gathered length bounded by the requested total — true, but a
    lemma [Net.Socket.send_bytes] does not carry and receptivity does not
    need.

    The ledger travels with the outcome: [pre] on every arm, and the
    one delivered byte's ranges on the arm that delivers.

    [Net.Socket.SendErr] consumes the pending error, so its witness
    carries the UPDATED model: the same [fd_insert] the spec performs,
    which is why the arm is a [modify] step and not a [pure] one. *)
Definition send_on_socket_witness (pre : list (word * nat))
    (acc : nat -> list (word * nat)) (fd : word) (sk : SockState)
    (total : word) (bs : list byte) (m : Model) : outcome SyscallEffect :=
  match send_state sk with
  | SendGoes ch =>
      if w_is0 total
      then outcome_copyins pre (ret_outcome (Z_to_bv 64 0) m)   (* zero-length request *)
      else if Nat.eqb (length bs) 0
      then outcome_copyins pre (ret_outcome (errno_ret EFAULT) m)  (* nothing readable *)
      else outcome_copyins (pre ++ acc (length (firstn 1 bs)))
             (Ok (mkEffect (len_word (firstn 1 bs)) [] []) m
                 (map (WriteEv ch) (firstn 1 bs)))            (* the one-byte send *)
  | SendErr e peer ch =>
      outcome_copyins pre
        (ret_outcome (errno_ret e)
           (with_fds (fd_insert (m_fds m) fd (FdSocket (SkReset peer ch))) m))
  | SendDead => outcome_copyins pre (ret_outcome (errno_ret EPIPE) m)
  end.

Lemma send_on_socket_witness_ok : forall pre acc fd sk total bs i m,
  send_on_socket pre acc fd sk total bs m i m
    (send_on_socket_witness pre acc fd sk total bs m).
Proof.
  intros. unfold send_on_socket, send_on_socket_witness.
  destruct (send_state sk) as [ch|e peer ch|]; cbv beta iota zeta.
  - (* SendGoes: the connection takes bytes *)
    unfold send_bytes.
    destruct (w_is0 total) eqn:Ht;
      [apply record_copyins_outcome; apply pure_ok|].
    destruct (Nat.eqb (length bs) 0) eqn:Hb;
      [apply record_copyins_outcome; apply pure_ok|].
    assert (Hpos : (1 <= bv_unsigned total)%Z).
    { unfold w_is0, bv_eqb in Ht. apply Z.eqb_neq in Ht.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Ht.
      pose proof (bv_unsigned_in_range 64 total). lia. }
    assert (Hl1 : length (firstn 1 bs) = 1%nat).
    { rewrite length_firstn. apply Nat.eqb_neq in Hb. lia. }
    eapply bind_step.
    { apply (choose_ok _ (firstn 1 bs)).
      repeat split.
      - rewrite Hl1. lia.
      - rewrite Hl1. exact Hpos.
      - rewrite Hl1. reflexivity. }
    cbv beta. unfold outcome_copyins.
    eapply witness_bind_ok_eq with
      (evs1 := map (WriteEv ch) (firstn 1 bs)) (evs2 := []);
      [apply emit_ok| |now rewrite app_nil_r].
    eapply record_copyins_ok. apply pure_ok.
  - (* SendErr: the pending error is consumed, and the fd is rewritten *)
    apply record_copyins_outcome.
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - (* SendDead: -EPIPE *)
    apply record_copyins_outcome. apply pure_ok.
Qed.

(** [sendto]'s three gates, then [import_ubuf]'s range verdict, then the
    fd — the nesting the spec insists on, mirrored here so that a
    reordering on either side stops matching.  A stream-pair end's send
    is [Fs.ReadWrite.witness_stream_write]'s. *)
Definition sendto_witness (fd buf count flags addrp : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (send_flags_modeled flags || stream_send_flags_ok flags)%bool then Unmodeled
  else if negb (w_is0 addrp) then Unmodeled
  else if negb (modeled_rw_count count) then Unmodeled
  else
    access_ok_zero_witness buf count m
      (match fd_lookup (m_fds m) fd with
       | None => ret_outcome (errno_ret EBADF) m
       | Some (FdSocket sk) =>
           if negb (send_flags_modeled flags) then Unmodeled
           else
           send_on_socket_witness [] (fun n => [(buf, n)]) fd sk count
             (readable_bytes (in_mem i) buf count) m
       | Some (FdStream id side st) =>
           if negb (stream_send_flags_ok flags) then Unmodeled
           else witness_stream_write id side st
                  (se_nonblock st || send_flag flags MSG_DONTWAIT)%bool
                  (send_flag flags MSG_NOSIGNAL) buf count i m
       | Some (FdDgram _) => Unmodeled        (* a socket with no peer: declined *)
       | Some _ => ret_outcome (errno_ret ENOTSOCK) m
       end).

Lemma sendto_witness_ok : forall fd buf count flags addrp addrlen i m,
  sendto_spec fd buf count flags addrp addrlen i m
    (sendto_witness fd buf count flags addrp i m).
Proof.
  intros. unfold sendto_spec, sendto_witness. cbv zeta.
  destruct (negb (send_flags_modeled flags || stream_send_flags_ok flags)%bool);
    [apply unmodeled_intro|].
  destruct (negb (w_is0 addrp)); [apply unmodeled_intro|].
  destruct (negb (modeled_rw_count count)); [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  unfold access_ok_zero, access_ok_zero_witness.
  destruct (access_okb buf (bv_unsigned count)); [|apply pure_ok].
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|];
    cbv beta iota zeta; try apply pure_ok.
  - destruct (negb (send_flags_modeled flags)); [apply unmodeled_intro|].
    apply send_on_socket_witness_ok.
  - destruct (negb (stream_send_flags_ok flags)); [apply unmodeled_intro|].
    apply witness_stream_write_ok.
  - apply unmodeled_intro.                   (* the datagram socket *)
Qed.

(** [sendmsg]'s fd comes FIRST and the header second — the opposite
    nesting to [sendto_witness] above, and deliberately not shared with
    it. *)
Definition sendmsg_witness (fd msgp flags : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (send_flags_modeled flags) then Unmodeled
  else
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) | Some (FdFile _ _)
  | Some (FdFileW _ _) | Some FdDir
  | Some (FdFileA _ _) | Some (FdFileRW _ _)
  | Some (FdPipe _ _) | Some (FdDevNull _ _) | Some FdUrandom
  | Some (FdEventfd _) | Some (FdAnon _ _) =>
      ret_outcome (errno_ret ENOTSOCK) m
  | Some (FdStream _ _ _) => Unmodeled          (* SCM_RIGHTS: see [sendmsg_spec] *)
  | Some (FdDgram _) => Unmodeled               (* see [sendmsg_spec] *)
  | Some (FdSocket sk) =>
      match copy_bytes_map (in_mem i) msgp MSGHDR_SIZE with
      | None => ret_outcome (errno_ret EFAULT) m
      | Some _ =>
          match read_u64 (in_mem i) msgp,
                read_u64 (in_mem i) (msgp + Z_to_bv 64 8),
                read_u64 (in_mem i) (msgp + Z_to_bv 64 16),
                read_u64 (in_mem i) (msgp + Z_to_bv 64 24),
                read_u64 (in_mem i) (msgp + Z_to_bv 64 32),
                read_u64 (in_mem i) (msgp + Z_to_bv 64 40) with
          | Some name, Some _, Some iov, Some iovlen, Some _, Some ctllen =>
              if negb (w_is0 name) then Unmodeled          (* a destination address *)
              else if (IOV_MAX <? bv_unsigned iovlen)%Z
              then outcome_copyins [(msgp, Z.to_nat MSGHDR_SIZE)]
                     (ret_outcome (errno_ret EMSGSIZE) m)  (* __copy_msghdr's own errno *)
              else if (UIO_FASTIOV <? bv_unsigned iovlen)%Z then Unmodeled
              else
              match import_iovecs (in_mem i) iov iovlen with
              | ImpFault =>
                  outcome_copyins
                    ([(msgp, Z.to_nat MSGHDR_SIZE)]
                     ++ import_iovecs_accesses (in_mem i) iov iovlen)
                    (ret_outcome (errno_ret EFAULT) m)
              | ImpInval =>
                  outcome_copyins
                    ([(msgp, Z.to_nat MSGHDR_SIZE)]
                     ++ import_iovecs_accesses (in_mem i) iov iovlen)
                    (ret_outcome (errno_ret EINVAL) m)
              | ImpOk iovs0 =>
                  if negb (w_is0 ctllen) then Unmodeled   (* ancillary data, after
                                                             the import: see the spec *)
                  else if negb (iovs_total (cap_iovecs iovs0) <=? rw_bytes_max)%Z
                  then Unmodeled
                  else
                  send_on_socket_witness
                    ([(msgp, Z.to_nat MSGHDR_SIZE)]
                     ++ import_iovecs_accesses (in_mem i) iov iovlen)
                    (fun n => iov_prefix_accesses (cap_iovecs iovs0) n)
                    fd sk
                    (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))
                    (writev_gathered (in_mem i) iovs0) m
              end
          | _, _, _, _, _, _ =>
              outcome_copyins [(msgp, Z.to_nat MSGHDR_SIZE)]
                (ret_outcome (errno_ret EFAULT) m)
          end
      end
  end.

Lemma sendmsg_witness_ok : forall fd msgp flags i m,
  sendmsg_spec fd msgp flags i m (sendmsg_witness fd msgp flags i m).
Proof.
  intros. unfold sendmsg_spec, sendmsg_witness.
  destruct (negb (send_flags_modeled flags)); [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|];
    cbv beta iota zeta; try apply pure_ok; try apply unmodeled_intro.
  destruct (copy_bytes_map (in_mem i) msgp MSGHDR_SIZE);
    cbv beta iota zeta; [|apply pure_ok].
  (* Six independent reads, so 64 shapes; 63 of them are the total-match
     -EFAULT arm the spec calls unreachable, and only the all-[Some] one
     continues.  The goal selector is what keeps this cheap -- do not
     replace it with a uniform [cbn], which would delta-reduce the
     iovec fuel below. *)
  destruct (read_u64 (in_mem i) msgp) as [name|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 8)) as [namelen|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 16)) as [iov|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 24)) as [iovlen|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 32)) as [ctl|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 40)) as [ctllen|];
    cbv beta iota zeta;
    try (apply record_copyins_outcome; apply pure_ok).
  destruct (negb (w_is0 name)); [apply unmodeled_intro|].
  destruct ((IOV_MAX <? bv_unsigned iovlen)%Z);
    [apply record_copyins_outcome; apply pure_ok|].
  destruct ((UIO_FASTIOV <? bv_unsigned iovlen)%Z); [apply unmodeled_intro|].
  destruct (import_iovecs (in_mem i) iov iovlen) as [iovs0| |];
    cbv beta iota zeta;
    [ | apply record_copyins_outcome; apply pure_ok
      | apply record_copyins_outcome; apply pure_ok ].
  destruct (negb (w_is0 ctllen)); [apply unmodeled_intro|].
  destruct (negb (iovs_total (cap_iovecs iovs0) <=? rw_bytes_max)%Z);
    [apply unmodeled_intro|].
  apply send_on_socket_witness_ok.
Qed.

(* ---------------- socketpair (199), recvfrom (207), recvmsg (212) ------

   Each witness takes the arm its spec decides first, and on socketpair
   the [alt]s LEFT branch — the reservation errno — so it never has to
   build the two descriptor writes, for the AF_UNIX triple as for the
   AF_INET ones. *)


Definition socketpair_witness (family type protocol sv : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (socketpair_flags_ok type) then ret_outcome (errno_ret EINVAL) m
  else if negb (socketpair_modeled_b family type protocol
                || socketpair_unix_b family type protocol)%bool then Unmodeled
  else
  match socketpair_fds (m_fds m) with
  | None => Unmodeled
  | Some _ =>
      if socketpair_dest_writable (in_wmem i) sv
      then (if socketpair_unix_b family type protocol
            then (if stream_id_live (m_fds m) (stream_new_id (m_fds m))
                  then Unmodeled   (* the pair id would alias a live one *)
                  else ret_outcome (errno_ret EMFILE) m)
            else ret_outcome (errno_ret EMFILE) m)
      else if negb (access_okb sv 4)
      then ret_outcome (errno_ret EMFILE) m
      else Unmodeled
  end.


Lemma socketpair_witness_ok : forall family type protocol sv i m,
  socketpair_spec family type protocol sv i m
    (socketpair_witness family type protocol sv i m).
Proof.
  intros. unfold socketpair_spec, socketpair_witness.
  destruct (negb (socketpair_flags_ok type)) eqn:Hfl; cbv beta iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (negb (socketpair_modeled_b family type protocol
                  || socketpair_unix_b family type protocol)%bool) eqn:Hmo;
    cbv beta iota; [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (socketpair_fds (m_fds m)) as [[fd1 fd2]|] eqn:Hfds; cbv beta iota;
    [|apply unmodeled_intro].
  destruct (socketpair_dest_writable (in_wmem i) sv) eqn:Hmem;
    cbv beta iota.
  - destruct (socketpair_unix_b family type protocol) eqn:Hu; cbv beta iota.
    + unfold socketpair_unix_written. cbv zeta.
      destruct (stream_id_live (m_fds m) (stream_new_id (m_fds m))) eqn:Hl;
        cbv beta iota; [apply unmodeled_intro|].
      apply alt_l.
      eapply bind_step; [apply choose_ok; left; reflexivity|].
      cbv beta. unfold err_ret, ret_only, ret_outcome. apply pure_ok.
    + unfold socketpair_written. apply alt_l.
      eapply bind_step; [apply choose_ok; left; reflexivity|].
      cbv beta. unfold err_ret, ret_only, ret_outcome. apply pure_ok.
  - destruct (negb (access_okb sv 4)) eqn:Ho; cbv beta iota;
      [|apply unmodeled_intro].
    unfold socketpair_faulted. apply alt_l.
    eapply bind_step; [apply choose_ok; left; reflexivity|].
    cbv beta. unfold err_ret, ret_only, ret_outcome. apply pure_ok.
Qed.


(** A stream-pair end reads through [Fs.ReadWrite.witness_stream_read]
    under the spec's two declines; every other descriptor answers its
    errno or, a socket, declines. *)
Definition recvfrom_witness (fd buf size : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if negb (modeled_rw_count size) then Unmodeled
  else if access_okb buf (bv_unsigned size)
  then (match fd_lookup (m_fds m) fd with
        | Some (FdStream id side st) =>
            if negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 (in_arg i 3)))
                                    MSG_DONTWAIT) 0)
            then Unmodeled
            else if negb (w_is0 (in_arg i 4)) then Unmodeled
            else witness_stream_read fd id side st
                   (se_nonblock st
                    || negb (Z.eqb (Z.land (bv_unsigned (abi_low32 (in_arg i 3)))
                                           MSG_DONTWAIT) 0))%bool
                   buf size i m
        | _ =>
            match sockfd_lookup_errno (m_fds m) fd with
            | Some e => ret_outcome (errno_ret e) m
            | None => Unmodeled
            end
        end)
  else ret_outcome (errno_ret EFAULT) m.


Lemma recvfrom_witness_ok : forall fd buf size i m,
  recvfrom_spec fd buf size i m (recvfrom_witness fd buf size i m).
Proof.
  intros. unfold recvfrom_spec, recvfrom_witness.
  destruct (negb (modeled_rw_count size)) eqn:Hc; cbv beta iota;
    [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  unfold access_ok_zero.
  destruct (access_okb buf (bv_unsigned size)) eqn:Hok; cbv beta iota.
  { destruct (fd_lookup (m_fds m) fd)
      as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
      cbv beta iota zeta;
      (* every kind but the stream-pair end: its errno, or a socket's
         decline *)
      try (unfold recv_fd_answer;
           destruct (sockfd_lookup_errno (m_fds m) fd) as [e|]; cbv beta iota;
           [unfold err_ret, ret_only, ret_outcome; apply pure_ok
           |apply unmodeled_intro]).
    destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 (in_arg i 3)))
                                   MSG_DONTWAIT) 0)); cbv beta iota;
      [apply unmodeled_intro|].
    destruct (negb (w_is0 (in_arg i 4))); cbv beta iota; [apply unmodeled_intro|].
    apply witness_stream_read_ok. }
  unfold err_ret, ret_only, ret_outcome. apply pure_ok.
Qed.


Definition recvmsg_witness (fd flags : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags)) MSG_CMSG_COMPAT) 0)
  then Unmodeled
  else match sockfd_lookup_errno (m_fds m) fd with
       | Some e => ret_outcome (errno_ret e) m
       | None => Unmodeled
       end.


Lemma recvmsg_witness_ok : forall fd flags i m,
  recvmsg_spec fd flags i m (recvmsg_witness fd flags m).
Proof.
  intros. unfold recvmsg_spec, recvmsg_witness.
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags))
                                MSG_CMSG_COMPAT) 0)) eqn:Hf; cbv beta iota;
    [apply unmodeled_intro|].
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  unfold recv_fd_answer.
  destruct (sockfd_lookup_errno (m_fds m) fd) as [e|]; cbv beta iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok
    |apply unmodeled_intro].
Qed.
