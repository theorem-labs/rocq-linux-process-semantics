(** * LinuxProcessSem.Sys.Net.Socket — socket (198), bind (200), listen (201),
      accept (202), connect (203), getsockname (204), getpeername (205),
      sendto (206), setsockopt (208), getsockopt (209), shutdown (210),
      sendmsg (211), accept4 (242)

    This file answers to Linux [net/socket.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess Fs.File Fs.ReadWrite Fs.Fcntl.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** The errnos [socket] and [accept4] can fail with for reasons the model
    does not decide — the descriptor table filling up ([alloc_fd] over
    the soft RLIMIT_NOFILE, or [expand_files] over sysctl_nr_open), the
    system file table filling up ([alloc_file_pseudo]), and the
    allocations behind both.  The soft limit itself IS carried
    ([State.m_nofile]), and this spec does not consult it: that
    is a known gap, not something
    this list decides.  Drawn from with [errno_from] under an
    [alt], exactly as [openat_errnos] is: the failure has to stay LIVE,
    or a target could delete the source's error handling and remain
    equivalent. *)
Definition socket_errnos : list Z := [ENOMEM; EMFILE; ENFILE].
Definition accept_errnos : list Z := [ENOMEM; EMFILE; ENFILE].

(** [bind] and [listen] both reach [inet_csk_get_port], whose every
    failure — an exhausted net.ipv4.ip_local_port_range, or a bind-bucket
    allocation failure — is reported as -EADDRINUSE: the function
    initialises [ret = -EADDRINUSE] and never overwrites it.  The model
    has no port table, so which of the two happens is not something it
    can decide; the branch is kept live so it can happen. *)
Definition bind_errnos   : list Z := [EADDRINUSE].
Definition listen_errnos : list Z := [EADDRINUSE].

(** THE TRACE CHANNEL OF THE [n]-TH CONNECTION HANDED OVER, which is
    [3 + n]: past stdin, stdout and stderr, and never colliding with
    them or with another connection.

    NOT THE FD.  [lowest_fd] reissues a closed descriptor, so after
    [close(1)] the next [accept] would return fd 1 and a socket read
    would be reported on stdout's channel.

    NOT A COUNTER IN THE MODEL EITHER, in the sense that matters: it
    counts CONNECTIONS TAKEN FROM THE INPUT, not allocations, so it is a
    function of the environment and of how many connections the program
    has accepted — the same for two binaries that accept the same
    connections in the same order, and different the moment they do not.
    An allocation-derived id would pin the observable to the order the
    program happened to allocate in. *)
Definition conn_channel (ix : word) : word := ix + Z_to_bv 64 3.

(** THE COUNTER IS EXHAUSTED once three values remain, because
    [conn_channel] adds three and a [word] wraps.  Hand a connection over
    at [ix] and it is reported on channel [ix + 3]; the last index that
    does not wrap is [2^64 - 4], reported on [2^64 - 1].  At [2^64 - 3]
    the next channel would be 0 — STDIN's — and a target could read that
    connection where the source read standard input and produce the same
    trace.  [accept] refuses to hand one over from here on, which is what
    keeps the issued channels inside [[3, 2^64 - 1]]: injective, and
    disjoint from the three standard streams.

    NOTHING REACHES THIS IN A RUN ANYONE WILL EXECUTE — it takes 2^64
    successful accepts.  It is not here to be reached.  It is here
    because [Run.star] admits chains of any finite length and
    [State.with_accepted] increments unconditionally, so without it the
    separation [Checks.Cases.Net.Socket.conn_channel_not_std] states is
    not merely unreached but FALSE at a reachable configuration — which
    is an unsoundness in [Equivalence.strong_universal_T] and not a
    caveat on a helper lemma. *)
Definition conn_ix_exhausted (ix : word) : bool :=
  (two_pow_64 - 3 <=? bv_unsigned ix)%Z.

(* -------------------------------------------------------------------------
   struct sockaddr_in, decoded from the bytes the guest supplied
   ------------------------------------------------------------------------- *)

(** [sin_family]: a [sa_family_t], i.e. an [unsigned short] in HOST byte
    order, at offset 0.  riscv64 is little-endian. *)
Definition sa_family_of (bs : list byte) : Z :=
  match bs with
  | b0 :: b1 :: _ => (bv_unsigned b0 + 256 * bv_unsigned b1)%Z
  | _ => (-1)%Z          (* fewer than two bytes: no family to read *)
  end.

(** [sin_port]: a [__be16] at offset 2 — NETWORK byte order, so the
    high-order byte comes first. *)
Definition sin_port_of (bs : list byte) : Z :=
  match bs with
  | _ :: _ :: b2 :: b3 :: _ => (256 * bv_unsigned b2 + bv_unsigned b3)%Z
  | _ => (-1)%Z
  end.

(** [sin_addr.s_addr]: a [__be32] at offset 4 — network byte order. *)
Definition sin_addr_of (bs : list byte) : Z :=
  match bs with
  | _ :: _ :: _ :: _ :: b4 :: b5 :: b6 :: b7 :: _ =>
      (16777216 * bv_unsigned b4 + 65536 * bv_unsigned b5
       + 256 * bv_unsigned b6 + bv_unsigned b7)%Z
  | _ => (-1)%Z
  end.

(** INADDR_ANY, the only bind address the model accepts. *)
Definition INADDR_ANY : Z := 0%Z.

(** [socket domain type protocol].

    net/socket.c [__sys_socket] -> __sys_socket_create -> sock_create ->
    __sock_create -> net/ipv4/af_inet.c [inet_create], v6.12.  THE ORDER
    IS LOAD-BEARING and is what this spec follows:

    1. [__sys_socket_create] rejects an unknown flag bit —
       [if ((type & ~SOCK_TYPE_MASK) & ~(SOCK_CLOEXEC | SOCK_NONBLOCK))
        return -EINVAL;] — BEFORE anything else, so a bad flag beats a
       bad family AND a bad protocol.  It then does
       [type &= SOCK_TYPE_MASK], which is why the type reaching
       [__sock_create] is always in [0, 15] and that function's
       [type < 0] arm is dead on this path.
    2. [__sock_create] rejects [family < 0 || family >= NPROTO] (46)
       with -EAFNOSUPPORT, and only then [type >= SOCK_MAX] (11) with
       -EINVAL.
    3. An in-range but unregistered family is -EAFNOSUPPORT.
    4. [inet_create] rejects [protocol < 0 || protocol >= IPPROTO_MAX]
       with -EINVAL.  IPPROTO_MAX IS 263, not 256 — see the constant.
    5. The [inetsw[type]] walk: an empty list leaves -ESOCKTNOSUPPORT,
       a non-empty list with no match gives -EPROTONOSUPPORT.

    Fd allocation comes LAST, unlike openat's: [__sys_socket] finishes
    with [sock_map_fd], which is where [get_unused_fd_flags] runs.  So
    every validation errno above preempts -EMFILE, and the injected
    failure set attaches to the SUCCESS path alone.

    THE NARROWING, the same one [openat_spec] carries: [sock_alloc] can
    fail with -ENFILE after the family and type checks but before
    [inet_create], so Linux can answer -ENFILE where this spec insists
    on -EINVAL/-EPROTONOSUPPORT/-ESOCKTNOSUPPORT.  That admits fewer
    behaviors than Linux, never more.

    WHAT IS DECLINED, and why:
    - [SOCK_NONBLOCK] in the flags sets O_NONBLOCK on the new file, and
      the model has no notion of a non-blocking fd.  ([SOCK_CLOEXEC] is
      accepted and ignored, as [openat_spec] does for O_CLOEXEC: it
      touches only the descriptor's close-on-exec bit, and there is no
      execve here.)
    - Every family but AF_INET.  Whether an in-range family is
      registered is a property of the kernel build, so neither success
      nor -EAFNOSUPPORT can be asserted.
    - SOCK_DGRAM, SOCK_RAW and SOCK_PACKET under AF_INET.  The first two
      would SUCCEED and hand back a socket whose protocol this model
      does not have; the third is silently rewritten to PF_PACKET by
      [__sock_create] before [inet_create] ever runs.  THAT REWRITE MOVES
      SOCK_PACKET's DECLINE ABOVE STEP 4: the protocol range is
      [inet_create]'s, and a rewritten call never reaches it, so judging
      SOCK_PACKET by [IPPROTO_MAX] would answer -EINVAL where Linux
      answers -EPERM or succeeds.  SOCK_DGRAM and SOCK_RAW are not
      rewritten and so stay below it. *)
Definition socket_spec (domain type protocol : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let tu := bv_unsigned (abi_low32 type) in
  let flagbits := Z.ldiff tu SOCK_TYPE_MASK in
  if negb (Z.eqb (Z.ldiff flagbits (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)
  then err_ret EINVAL                    (* unknown flag bit: real -EINVAL, before everything *)
  else if negb (Z.eqb (Z.land flagbits SOCK_NONBLOCK) 0)
  then unmodeled                         (* SOCK_NONBLOCK: no O_NONBLOCK notion — fail closed *)
  else
    let ty  := Z.land tu SOCK_TYPE_MASK in
    let fam := sint32 domain in
    let pro := sint32 protocol in
    if orb (Z.ltb fam 0) (Z.leb NPROTO fam) then err_ret EAFNOSUPPORT
    else if Z.leb SOCK_MAX ty then err_ret EINVAL
    else if negb (Z.eqb fam AF_INET) then unmodeled
      (* an in-range family whose registration the model cannot know *)
    else if Z.eqb ty SOCK_PACKET then unmodeled
      (* SOCK_PACKET UNDER AF_INET NEVER REACHES [inet_create], so the
         protocol range BELOW must not judge it, and this arm has to sit
         above that range rather than with the other declined types.
         net/socket.c [__sock_create] (v6.12) rewrites
         [family = PF_PACKET] for [family == PF_INET && type ==
         SOCK_PACKET] — after the family and type range checks, before
         [pf->create] — so the call is built by
         net/packet/af_packet.c [packet_create], which answers -EPERM
         without CAP_NET_RAW and otherwise succeeds, and which casts
         [protocol] straight to a [__be16] ethertype
         ([__be16 proto = (__force __be16)protocol]) without any range
         check at all.  Judged by [IPPROTO_MAX] instead, [socket(AF_INET,
         SOCK_PACKET, -1)] would answer a confidently wrong -EINVAL for a
         protocol Linux never rejects.  The rewrite is conditional on the
         family, which is why this sits below the AF_INET test: under any
         other in-range family SOCK_PACKET is declined by that test. *)
    else if orb (Z.ltb pro 0) (Z.leb IPPROTO_MAX pro) then err_ret EINVAL
    else if Z.eqb ty SOCK_STREAM then
      (* The BUILT-IN [inetsw_array] holds exactly
         {SOCK_STREAM, IPPROTO_TCP} for this type.  Protocol 0 takes the
         wildcard arm, which REWRITES the protocol to IPPROTO_TCP and
         breaks; protocol 6 matches directly.
         Two other protocols can join that list at runtime, and neither
         answer is the model's to give: net/sctp/protocol.c registers
         {SOCK_STREAM, IPPROTO_SCTP} and net/mptcp/protocol.c registers
         {SOCK_STREAM, IPPROTO_MPTCP} through [inet_register_protosw].
         Whether either is present is a property of the KERNEL BUILD --
         CONFIG_MPTCP is on by default on the distributions this runs
         under, and [inet_create] even [request_module]s for an absent
         one and retries the walk -- exactly the reason an in-range
         FAMILY is declined above.  So they are declined too, rather
         than answered -EPROTONOSUPPORT.
         The ordering is safe: [inetsw_array]'s TCP entry carries
         INET_PROTOSW_PERMANENT and [inet_register_protosw] inserts
         non-permanent entries AFTER the last permanent one, so
         protocol 0 still wildcards to TCP however many modules load. *)
      if orb (Z.eqb pro IPPROTO_SCTP) (Z.eqb pro IPPROTO_MPTCP) then unmodeled
      else if negb (orb (Z.eqb pro IPPROTO_IP) (Z.eqb pro IPPROTO_TCP))
      then err_ret EPROTONOSUPPORT
      else
        alt (e <- errno_from socket_errnos ;; err_ret e)  (* no free fd, or an untracked failure *)
            (fd <- lowest_fd (m_fds m) ;;                 (* success: the lowest free fd, as Linux *)
             set_fds (fd_insert (m_fds m) fd (FdSocket SkFresh)) ;;
             ret_only fd)
    else if orb (Z.eqb ty SOCK_DGRAM) (Z.eqb ty SOCK_RAW)
    then unmodeled                       (* SOCK_DGRAM / SOCK_RAW — see above.  Both keep
                                            family AF_INET all the way to [inet_create], so
                                            the protocol range above judges them and really
                                            does answer -EINVAL; only SOCK_PACKET escapes it,
                                            and it is decided earlier *)
    else if orb (Z.eqb ty SOCK_SEQPACKET) (Z.eqb ty SOCK_DCCP)
    then unmodeled
      (* Same kernel-build argument one level up: net/sctp/protocol.c
         registers a SOCK_SEQPACKET entry and net/dccp registers a
         SOCK_DCCP one, so [inetsw[ty]] is empty for these two only on a
         kernel that builds neither. *)
    else err_ret ESOCKTNOSUPPORT.        (* [inetsw[ty]] is empty for every remaining type
                                            (0, 4, 7, 8 and 9): no in-tree AF_INET protocol
                                            registers one, so the walk never runs and the
                                            pre-loop -ESOCKTNOSUPPORT stands *)

(** [bind fd addr addrlen].

    net/socket.c [__sys_bind] -> move_addr_to_kernel -> __sys_bind_socket
    -> net/ipv4/af_inet.c [inet_bind_sk] -> __inet_bind, v6.12.  Order:

    1. THE FD IS RESOLVED FIRST: -EBADF for a closed fd, then
       -ENOTSOCK for an open one that is not a socket.  The test is
       [sock_from_file] (net/socket.c), which is the single comparison
       [file->f_op == &socket_file_ops] and is byte-identical across
       v6.10-v6.15 but for a [likely()] hint added at v6.13.  HOW EACH
       RELEASE REACHES IT differs and nothing here depends on which:
       through [sockfd_lookup_light] at v6.10-v6.12, inlined at the call
       site from v6.13 — the same fd-class conversion ([CLASS(fd, f)] /
       [fd_empty]) that [Fs.Ioctl]'s header records for [fdget].
    2. [move_addr_to_kernel]: [addrlen < 0 || > sizeof(struct
       sockaddr_storage)] (128) is -EINVAL; [addrlen == 0] copies
       NOTHING and returns 0, leaving the kernel's buffer untouched;
       otherwise a failed [copy_from_user] is -EFAULT.  So -EFAULT
       PRECEDES the 16-byte minimum: a 4-byte unreadable address is
       -EFAULT, not -EINVAL.
    3. [inet_bind_sk]: [addr_len < sizeof(struct sockaddr_in)] (16) is
       -EINVAL.
    4. [__inet_bind]: a [sin_family] other than AF_INET is
       -EAFNOSUPPORT — NOT -EINVAL — except that AF_UNSPEC with
       INADDR_ANY is deliberately accepted as AF_INET ("Compatibility
       games").  Then -EADDRNOTAVAIL, then -EACCES for a privileged
       port, then -EINVAL for a double bind, then -EADDRINUSE from
       [inet_csk_get_port].

    WHAT IS DECLINED.  Only INADDR_ANY on port 0 is accepted.  A
    specific address needs the local address table that decides
    -EADDRNOTAVAIL; a specific port needs the port table that decides
    -EADDRINUSE and the per-netns sysctl
    net.ipv4.ip_unprivileged_port_start that decides -EACCES (a TUNABLE,
    not a hardcoded 1024: [inet_port_requires_bind_service],
    include/net/ip.h, reads that sysctl under CONFIG_SYSCTL and falls
    back to the [PROT_SOCK] MACRO — 1024, include/net/sock.h — only
    without it.  1024 is still the DEFAULT either way, because
    net/ipv4/af_inet.c [inet_init_net] seeds the sysctl from that same
    [PROT_SOCK]; what no model can know is its CURRENT value).  A
    one-process model has none of that, so it declines rather than
    inventing an answer.

    EVEN PORT 0 CAN FAIL, which is why the errno branch is live: with
    [snum == 0] and IP_BIND_ADDRESS_NO_PORT unset, [__inet_bind] still
    calls [get_port], and every failure inside [inet_csk_get_port] —
    an exhausted net.ipv4.ip_local_port_range, or a bind-bucket
    allocation failure — is reported as -EADDRINUSE, because that
    function initialises [ret = -EADDRINUSE] and never overwrites it.

    A NARROWING, and it reaches ONE of the two length checks above and
    not both.  [__sys_bind] runs [move_addr_to_kernel] and only then
    [__sys_bind_socket], whose first statement is [security_socket_bind]
    and whose second is [ops->bind] — so step 2's [0, 128] range test
    PRECEDES the LSM while step 3's 16-byte minimum FOLLOWS it.  An LSM
    can therefore answer -EACCES where this spec answers step 3's
    -EINVAL, and cannot where it answers step 2's.  Fewer behaviors,
    never more. *)
Definition bind_spec (fd addrp addrlen : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* fd not open: real -EBADF *)
  | Some (FdSocket sk) =>
      let al := sint32 addrlen in
      if orb (Z.ltb al 0) (Z.ltb SOCKADDR_STORAGE_SIZE al) then err_ret EINVAL
      else if Z.eqb al 0 then err_ret EINVAL
        (* nothing is copied and nothing faults; [inet_bind_sk] then
           rejects the zero length *)
      else
      match read_bytes_map (in_mem i) addrp (Z_to_bv 64 al) with
      | None => err_ret EFAULT                   (* copy_from_user failed: real -EFAULT *)
      | Some bs =>
          (* PAST THE COPY.  [move_addr_to_kernel] (net/socket.c) is
             [if (ulen == 0) return 0; if (copy_from_user(kaddr, uaddr, ulen)) return -EFAULT;],
             so every [addrlen > 0] that does not fault really has copied
             [addrlen] bytes out of user memory before anything looks at
             the family.  The ledger records it from here down and NOT
             above: the two [addrlen]-range arms return before the copy
             is attempted, and the -EFAULT arm is the copy FAILING, which
             transfers nothing.  That boundary is [Kernel.Sys.prlimit64_spec]'s,
             and it is what makes the ledger discriminate rather than
             decorate — the -EINVAL below is reached only AFTER a read,
             so it carries the ledger while the -EINVAL above does not. *)
          record_copyins [(addrp, Z.to_nat al)]
          (
          if Z.ltb al SOCKADDR_IN_SIZE then err_ret EINVAL
          else
            let fam  := sa_family_of bs in
            let port := sin_port_of bs in
            let a    := sin_addr_of bs in
            if negb (orb (Z.eqb fam AF_INET)
                         (andb (Z.eqb fam AF_UNSPEC) (Z.eqb a INADDR_ANY)))
            then err_ret EAFNOSUPPORT            (* NOT -EINVAL; see above *)
            else if negb (Z.eqb a INADDR_ANY) then unmodeled
            else if negb (Z.eqb port 0) then unmodeled
            else
              match sk with
              | SkFresh =>
                  alt (e <- errno_from bind_errnos ;; err_ret e)
                      (set_fds (fd_insert (m_fds m) fd (FdSocket SkBound)) ;;
                       ret_only (Z_to_bv 64 0))
              | SkBound | SkListening
              | SkConnected _ _ (NCons _ _) | SkConnected _ _ NFin =>
                  err_ret EINVAL
                  (* [__inet_bind]'s
                     [sk->sk_state != TCP_CLOSE || inet->inet_num].  For
                     each of these one conjunct or the other holds: a
                     bound socket has a port, a listening one is
                     TCP_LISTEN, and a live or half-closed connection is
                     TCP_ESTABLISHED or TCP_CLOSE_WAIT with a port. *)
              | SkConnected _ _ NRst | SkConnected _ _ NTimedOut
              | SkReset _ _ => unmodeled
                  (* A CONNECTION THE PEER HAS RESET IS UNBOUND AGAIN,
                     and -EINVAL here would be a confidently wrong
                     answer.  net/ipv4/tcp.c [tcp_done] runs
                     [tcp_set_state(sk, TCP_CLOSE)], whose TCP_CLOSE arm
                     calls [inet_put_port] whenever
                     [icsk_bind_hash && !(sk_userlocks & SOCK_BINDPORT_LOCK)];
                     net/core/sock.c [sk_clone_lock] clears that bit on
                     EVERY accepted child
                     ([newsk->sk_userlocks = sk->sk_userlocks & ~SOCK_BINDPORT_LOCK]),
                     so the guard never saves it; and
                     net/ipv4/inet_hashtables.c [__inet_put_port] sets
                     [inet_sk(sk)->inet_num = 0].  Both conjuncts are
                     then false and Linux AUTOBINDS and returns 0.
                     (Contrast [listen_spec]'s [SkReset] arm, which is
                     -EINVAL for a reason that does survive: [inet_listen]
                     tests [sock->state], which [tcp_done] does not
                     touch.)
                     The model still declines rather than returning 0,
                     for a second reason of its own: the reset runs
                     [tcp_done] when the SEGMENT ARRIVES, not when the
                     program reads it, so for [NRst]/[NTimedOut] the
                     model does not even know the socket is already
                     unbound.  And a successful bind here would leave a
                     socket that is bound AND still reads as
                     end-of-stream, which [SockState] cannot express. *)
              end)
      end
  | Some _ => err_ret ENOTSOCK
      (* AN OPEN FD THAT IS NOT A SOCKET, whatever kind it is.  This arm
         is a wildcard on purpose and stays correct as [FdEntry] grows:
         [sock_from_file] is one comparison against [socket_file_ops]
         (step 1 above), so -ENOTSOCK is a property of the kernel's
         DISPATCH rather than of any enumeration of file kinds.  It is
         therefore the right answer for every non-socket kind this
         model has — [FdChannel], [FdFile], [FdFileW], [FdFileA],
         [FdFileRW], [FdDir], [FdPipe], [FdDevNull] and [FdUrandom] — and
         for any kind a later change adds,
         without this arm being touched.  [FdPipe] and [FdFileA] are the
         two kinds to have arrived since this claim was written, and
         both arrived without the arm needing an edit, which is the
         argument working rather than an exception to it: a pipe end's
         [f_op] is [pipeanon_fops] (fs/pipe.c [create_pipe_files],
         v6.18.46) and an append fd's is its filesystem's, so
         [sock_from_file] returns NULL for each exactly as for the
         other four.
         [listen_spec] and [accept4_spec] answer the same way for the
         same reason. *)
  end.

(** [listen fd backlog].

    net/socket.c [__sys_listen] -> __sys_listen_socket ->
    net/ipv4/af_inet.c [inet_listen] -> __inet_listen_sk, v6.12.

    THE BACKLOG IS NEVER REJECTED, only clamped:
    [if ((unsigned int)backlog > somaxconn) backlog = somaxconn;].  The
    cast is what makes a NEGATIVE backlog wrap to a huge unsigned and
    get clamped to SOMAXCONN (4096) rather than refused.  Nothing in
    this model observes the backlog — no call reports it — so the
    clamped value is not recorded and the argument is unused here.

    THE FD IS RESOLVED FIRST (-EBADF, then -ENOTSOCK), before the
    clamp: the clamp reads [sock_net(sock->sk)] and so structurally
    cannot precede the lookup.  The -ENOTSOCK test is [sock_from_file];
    [bind_spec]'s step 1 gives its shape and how each release reaches
    it.

    LISTEN WITHOUT BIND SUCCEEDS.  [inet_csk_listen_start] calls
    [get_port(sk, inet->inet_num)] with [inet_num == 0] for an unbound
    socket, and [inet_csk_find_open_port] picks an ephemeral port out of
    net.ipv4.ip_local_port_range.  That autobind is also the only thing
    that can fail here ONCE THE MODELED SURFACE IS TAKEN INTO ACCOUNT,
    with -EADDRINUSE, so the errno branch is live on exactly the arm
    that autobinds and NOT on the others: a socket that is already bound
    has a port, and [get_port] cannot fail for it.  The qualifier is
    needed because [inet_csk_listen_start] has two OTHER error exits,
    and both are unreachable here rather than absent: it opens with
    [inet_ulp_can_listen], which is -EINVAL only for a socket carrying a
    ULP whose ops have no [clone], and it checks [sk_prot->hash], whose
    sole failing path is [inet_reuseport_add_sock] under the
    [if (sk->sk_reuseport)] guard of [inet_hash]
    (net/ipv4/inet_hashtables.c:796-797, Linux v6.18.46; formerly
    [__inet_hash]).  A ULP is set by setsockopt(TCP_ULP) and SO_REUSEPORT by
    setsockopt(SO_REUSEPORT).  [setsockopt] (208) IS in [modeled_sysnos],
    but both of those are option-table calls at a KNOWN
    level, and [setsockopt_spec] answers every one of them [unmodeled] —
    a run that issues either leaves the modeled surface AT THAT CALL and
    never reaches this [listen].  Neither of that spec's two real arms
    can set a bit: a negative [optlen] is -EINVAL out of
    [do_sock_setsockopt] before any option is looked at, and an unknown
    level is -ENOPROTOOPT out of [ip_setsockopt].  So neither bit is
    ever set on a modeled run.

    RE-LISTENING IS LEGAL: TCPF_LISTEN is in [__inet_listen_sk]'s
    accepted mask, so a second listen writes the new backlog, skips
    [inet_csk_listen_start] entirely, and returns 0.

    A connected socket is -EINVAL.  Two different predicates produce it
    — [inet_listen] tests [sock->state != SS_UNCONNECTED || sock->type
    != SOCK_STREAM], and [__inet_listen_sk] tests
    [(1 << old_state) & (TCPF_CLOSE | TCPF_LISTEN)] — and this spec
    cannot tell them apart, because both give -EINVAL and the model has
    only one connected state.  ([sock_no_listen]'s -EOPNOTSUPP for a
    datagram socket is unreachable: [socket_spec] creates no such
    socket.) *)
Definition listen_spec (fd backlog : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let _ := backlog in                            (* clamped, and nothing observes it *)
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF
  | Some (FdSocket sk) =>
      match sk with
      | SkConnected _ _ _ => err_ret EINVAL      (* not SS_UNCONNECTED: real -EINVAL *)
      | SkReset _ _ => err_ret EINVAL
          (* ALSO -EINVAL, but NOT for the reason the arm above gives, and the
             difference is worth stating.  [__inet_listen_sk]'s state test is
             [(1 << old_state) & (TCPF_CLOSE | TCPF_LISTEN)], which ACCEPTS
             TCP_CLOSE — and TCP_CLOSE is exactly the state
             net/ipv4/tcp.c [tcp_done] left this socket in when the peer's error
             was delivered.  That test alone would let the listen SUCCEED.
             What refuses it is [inet_listen]'s EARLIER check,
             [sock->state != SS_UNCONNECTED]: only [inet_release] and
             [tcp_disconnect] move [sock->state] back, and neither ran here —
             this socket was never closed or disconnected, a read merely
             consumed its pending error — so [sock->state] is still
             SS_CONNECTED. *)
      | SkListening => ret_only (Z_to_bv 64 0)   (* re-listen: backlog only *)
      | SkBound =>
          set_fds (fd_insert (m_fds m) fd (FdSocket SkListening)) ;;
          ret_only (Z_to_bv 64 0)                (* already has a port: [get_port] cannot fail *)
      | SkFresh =>
          alt (e <- errno_from listen_errnos ;; err_ret e)   (* the autobind's -EADDRINUSE *)
              (set_fds (fd_insert (m_fds m) fd (FdSocket SkListening)) ;;
               ret_only (Z_to_bv 64 0))
      end
  | Some _ => err_ret ENOTSOCK
  end.

(** [accept4 fd addr addrlen flags], which [accept] reaches with
    [flags = 0] — net/socket.c's [SYSCALL_DEFINE3(accept)] is literally
    [return __sys_accept4(fd, upeer_sockaddr, upeer_addrlen, 0);], so
    there is one spec and not two.

    ORDER, from __sys_accept4 -> __sys_accept4_file -> do_accept, v6.12:

    0. [fdget] in [__sys_accept4] — **-EBADF COMES FIRST**, before the
       flags are even looked at.
    1. [flags & ~(SOCK_CLOEXEC | SOCK_NONBLOCK)] -> -EINVAL.
    2. [get_unused_fd_flags] -> -EMFILE (or -ENOMEM); NOT -ENFILE, which
       comes later.
    3. [sock_from_file] -> -ENOTSOCK.
    4-6. [sock_alloc] / [sock_alloc_file] / LSM -> -ENFILE, -ENOMEM,
       -EPERM.
    7. [inet_csk_accept] -> -EINVAL when the socket is not TCP_LISTEN.
    8-9. [inet_getname] and [move_addr_to_user], which run only when the
       address argument is non-NULL.

    STEPS 1 THROUGH 7 LEAVE THE QUEUE UNTOUCHED.  [inet_csk_accept]
    reaches [reqsk_queue_remove] only after every error exit has been
    passed, so a failing accept never loses a connection; steps 8 and 9
    do, via [out_fd: fput(newfile)], which is one reason a non-NULL
    address argument is not modeled here.

    THE ERRNO BRANCH IS LIVE, and that is not decoration.  Without it a
    source that handles an accept failure and a target with that
    handling deleted would have identical trace sets, while differing on
    real Linux.  It is also what makes [accept] RECEPTIVE at fd
    exhaustion: [alloc_fd]'s scan is bounded at 4096 candidates, and
    when it runs out [lowest_fd]'s freeness conjunct empties the success
    branch, leaving this one.  An errno is an ordinary [Ok], so an
    errno-versus-success [alt] is not the shape that a [choose] between
    [Ok] and [Unmodeled] would be.

    WHAT IS DECLINED:
    - [SOCK_NONBLOCK] in the flags — it marks the NEW file O_NONBLOCK,
      and the model has no such notion.  (Note it does not affect
      whether this call blocks: [do_accept] takes that from the
      LISTENING socket's own [f_flags], not from the argument.)
      [SOCK_CLOEXEC] is accepted and ignored.
    - A non-NULL address argument.  [getsockname] and [getpeername] ARE
      modeled, and all three declines wait on the same missing
      export: [SyscallEffect] cannot express the [move_addr_to_user]
      write.  WHAT THE EXPORT ALONE BUYS IS NOT THE SAME IN ALL THREE.
      For this arm, and for [getpeername_spec]'s [SkConnected] arm, the
      value is already there and honest — [State.nq_peer] takes the peer
      from the quantified [ProcInput] — so the export closes both, and
      neither before then.  [getsockname_spec] declines on EVERY socket
      state, and the export would leave it declining on all but
      [SkFresh]: a fresh socket really is 0.0.0.0:0, but past it the
      local port is an EPHEMERAL one the kernel drew with
      [get_random_u32_below] (and a socket handed over by [accept]
      inherits the listener's), so it is not a function of the
      process's own state at all.  That call needs a VALUE the model
      does not carry, not just a way to write one; see
      [getsockname_spec]'s own comment.  With a NULL address,
      [do_accept] never touches [addrlen] either — not read, not
      written, not validated — so that argument is genuinely unused
      here.
    - -ECONNABORTED, which is unreachable for AF_INET/TCP: it comes only
      from [inet_getname] failing on [inet_dport == 0], and [do_accept]
      passes [peer = 2] specifically so the TCPF_CLOSE test is skipped.
      A peer that resets between the handshake and the accept does NOT
      abort the connection — the child stays queued and is handed over,
      and the reset surfaces as -ECONNRESET on the first read.  That is
      exactly a connection whose script begins with [NRst].

    A NARROWING, openat's again: for a non-socket fd, and for a socket
    that is not listening, this spec insists on -ENOTSOCK / -EINVAL
    where Linux could answer -EMFILE first. *)
Definition accept4_spec (fd addrp addrlenp flags : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let _ := addrlenp in                           (* untouched while [addrp] is NULL *)
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* [fdget], before the flags check *)
  | Some e =>
      let fl := bv_unsigned (abi_low32 flags) in
      if negb (Z.eqb (Z.ldiff fl (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)
      then err_ret EINVAL
      else if negb (Z.eqb (Z.land fl SOCK_NONBLOCK) 0) then unmodeled
      else
      match e with
      | FdSocket sk =>
          if negb (w_is0 addrp) then unmodeled   (* the peer address: see above *)
          else
          match sk with
          | SkListening =>
              alt (er <- errno_from accept_errnos ;; err_ret er)
                  (if conn_ix_exhausted (m_conn_ix m)
                   then choose (fun _ => False)
                     (* The channel space is used up; see
                        [conn_ix_exhausted].  Spelled as a [choose] with
                        no witness rather than [unmodeled] because the
                        SIBLING of this [alt] answers a concrete errno at
                        the very same (input, model), and
                        [check_syscall_err_iff] holds against a TOTAL
                        checker: an arm that both answers and declines
                        there is not statable.  This is the idiom
                        [Fs.ReadWrite.readv_heap_gap] already uses.  The
                        errno branch stays live, so [accept] still has an
                        answer here and [Checks.Progress.receptive] is
                        untouched. *)
                   else
                   nfd <- lowest_fd (m_fds m) ;;
                   modify (with_accepted
                             (fd_insert (m_fds m) nfd
                                (FdSocket
                                   (SkConnected (nq_peer (m_net m))
                                                (conn_channel (m_conn_ix m))
                                                (nq_script (m_net m)))))) ;;
                   ret_only nfd)
          | _ => err_ret EINVAL                  (* [inet_csk_accept]: not TCP_LISTEN *)
          end
      | _ => err_ret ENOTSOCK
      end
  end.

(** [connect fd addr addrlen].

    net/socket.c [__sys_connect] -> [move_addr_to_kernel] ->
    [__sys_connect_file] -> net/ipv4/af_inet.c [inet_stream_connect] ->
    [__inet_stream_connect] -> net/ipv4/tcp_ipv4.c [tcp_v4_connect].

    THE VERSION WINDOW, stated per function because one of them does not
    have a clean one.  [move_addr_to_kernel], [__sys_connect_file],
    [__inet_stream_connect] and [tcp_v4_connect] are unchanged in
    behaviour across v6.1, v6.6, v6.12 and mainline, stable branches
    included and not mainline alone, ON THE ARMS THIS SPEC ANSWERS.
    Two diffs exist and neither reaches them: [READ_ONCE(sock->ops)]
    from v6.6 and mainline's [sockaddr_unsized] parameter type are not
    observable at all, and v6.6 added [sk_disconnects] bookkeeping to
    [__inet_stream_connect] with a new -EPIPE return, which lies inside
    the declined region (it needs a connect that already reached
    SYN_SENT).  v6.12 and mainline are otherwise byte-identical here;
    the whole delta is v6.1 -> v6.6.  [__sys_connect] is the exception:
    its BEHAVIOUR is v5.5 onward — up to v5.4 it opened with
    [sockfd_lookup_light] and had bind's order — but its body has since
    been respelled twice without changing anything, and the newest
    spelling was BACKPORTED, so "v6.12" alone does not identify one.
    The body quoted below is the [CLASS(fd, f)] one: mainline v6.13
    onward, and 6.12.y from v6.12.91, NOT the v6.12 release.

    THE ORDER IS NOT BIND'S, and the difference is observable.
    [__sys_bind] resolves the descriptor FIRST ([sock_from_file], so
    -EBADF then -ENOTSOCK) and copies the address second.
    [__sys_connect] resolves only far enough for -EBADF, then copies,
    and reaches -ENOTSOCK only inside [__sys_connect_file]:

      if (fd_empty(f)) return -EBADF;
      ret = move_addr_to_kernel(uservaddr, addrlen, &address);
      if (ret) return ret;
      return __sys_connect_file(fd_file(f), &address, addrlen, 0);

    So [connect(non_socket_fd, NULL, 4)] is -EFAULT while
    [bind(non_socket_fd, NULL, 4)] is -ENOTSOCK.  [record_copyins] below
    sits at exactly that seam, which is what it is for: the copy is
    attached BEFORE the -ENOTSOCK arm, so the two paths that both answer
    past the copy are distinguishable from the one that does not reach
    it.

    1. [move_addr_to_kernel]: [ulen < 0 || ulen > sizeof(struct
       sockaddr_storage)] (128) is -EINVAL; [ulen == 0] copies NOTHING
       and returns 0; otherwise a failed [copy_from_user] is -EFAULT.
       A zero length needs no special case for the READ — [read_bytes_map]
       at length 0 is [Some []] whatever the pointer, which is exactly
       "copies nothing, cannot fault" — and the empty address then fails
       step 3's 2-byte minimum.  It does need one for the LEDGER: a
       zero-length address reads no user byte, so it records an empty
       ledger rather than a singleton zero-length range, as
       [ReadWrite.write_spec] does for a zero-length write.
    2. [__sys_connect_file]: [sock_from_file] is -ENOTSOCK.
    3. [__inet_stream_connect]: [addr_len < sizeof(uaddr->sa_family)]
       (2) is -EINVAL.
    4. [__inet_stream_connect]: an AF_UNSPEC family is a DISCONNECT, not
       a connect, and is handled BEFORE its switch on [sock->state].
    5. [tcp_v4_connect]: [addr_len < sizeof(struct sockaddr_in)] (16) is
       -EINVAL, then a [sin_family] other than AF_INET is -EAFNOSUPPORT.

    -EISCONN FOR A LISTENING SOCKET, WHICH IS THE ANSWER MOST WORTH
    GETTING RIGHT.  -EINVAL is the plausible guess and it is wrong.
    [listen] leaves [sock->state] at SS_UNCONNECTED — [inet_listen]
    REFUSES anything else — and moves only [sk->sk_state], to
    TCP_LISTEN.  The switch's SS_UNCONNECTED arm opens

      case SS_UNCONNECTED:
              err = -EISCONN;
              if (sk->sk_state != TCP_CLOSE)
                      goto out;

    so a listening socket takes the -EISCONN it pre-loaded.  An ACCEPTED
    socket answers -EISCONN too, from the arm above it: [__inet_accept]
    ends with [newsock->state = SS_CONNECTED].

    A RESET CONNECTION IS ALSO -EISCONN, by the argument [listen_spec]
    already makes: net/ipv4/tcp.c [tcp_done] moves [sk->sk_state] and
    not [sock->state], and only [inet_release] and [tcp_disconnect] move
    that back.  So [SkConnected] and [SkReset] both still read
    SS_CONNECTED whatever the peer has left to say, which is why this
    spec does not split on [rx] as [bind_spec] does.

    THE CONNECTION ATTEMPT ITSELF IS DECLINED, and that is the whole
    modeling decision.  Once the address has passed steps 1-5 on a fresh
    or bound socket, [sk->sk_prot->connect] runs and the outcome is the
    ENVIRONMENT's: success; -ECONNREFUSED/-ETIMEDOUT/-ECONNABORTED from
    [__inet_stream_connect]'s [sock_error] exit; -ENETUNREACH with no
    route and for a multicast or broadcast one (NOT -EACCES, which comes
    only from a [prohibit] route, net/ipv4/fib_semantics.c [fib_props]);
    -EHOSTUNREACH from an [unreachable] route; -EADDRNOTAVAIL and
    -EADDRINUSE from [inet_hash_connect]; -EINTR from a signal.  Nothing
    in a one-process model decides among them.

    Not a [choose] over that list, because the list has to include
    SUCCESS, and a successful connect hands back a PEER ADDRESS and a
    BYTE STREAM whose only source here is [m_net] — the queue [accept]
    draws from.  Taking an outbound connection out of it is a wrong
    answer, not a narrowing.  What the decline costs: no modeled
    execution can produce a connected socket by connecting, which is what
    keeps -EINPROGRESS, -EALREADY and the SS_DISCONNECTING -EINVAL arm
    unreachable rather than merely unmodeled.

    AF_UNSPEC IS ANSWERED ONLY ON A FRESH SOCKET.  It takes

      if (uaddr->sa_family == AF_UNSPEC) {
              sk->sk_disconnects++;
              err = sk->sk_prot->disconnect(sk, flags);
              sock->state = err ? SS_DISCONNECTING : SS_UNCONNECTED;
              goto out;
      }

    and for TCP [disconnect] is net/ipv4/tcp.c [tcp_disconnect], which
    has ONE return statement and it is [return 0].  On a fresh socket
    every branch inside it is dead — [old_state] is TCP_CLOSE, so no
    [inet_csk_listen_stop], no [tcp_need_reset] (mask
    ESTABLISHED/CLOSE_WAIT/FIN_WAIT1/FIN_WAIT2/SYN_RECV), no
    TCP_SYN_SENT arm, and [tp->repair] needs setsockopt(TCP_REPAIR),
    syscall 208 — and there is no port to release.  It is not quite a
    no-op inside the kernel: it advances [tp->write_seq] from 0 to 2,
    which [tcp_v4_connect] would later reuse in place of a secure ISN
    ([if (!tp->write_seq) WRITE_ONCE(tp->write_seq, st.seq)]).  Nothing
    modeled reads it, and the connect that would is declined — so the
    call returns 0 and changes nothing THIS MODEL can see.  That is an
    absence argument, and it is the one that rots first if the attempt
    is ever modeled.

    The other four states are DECLINED rather than answered 0, each for
    a state change [SockState] cannot express:
    - [SkBound]: whether the port survives turns on
      [inet_bhash2_reset_saddr] and the SOCK_BINDADDR_LOCK bit
      [__inet_bind] sets, and whether the socket is still bound
      afterwards is exactly what decides whether a later [listen]
      autobinds.  That bookkeeping is not carried here.
    - [SkListening]: [tcp_disconnect] runs [inet_csk_listen_stop], which
      destroys the accept queue.  The queue this model has is the
      ENVIRONMENT's [m_net], not the socket's, and there is no way to
      say that a socket has dropped it.
    - [SkConnected _ _ (NCons _ _)] and [SkConnected _ _ NFin]: a live or
      half-closed connection is TCP_ESTABLISHED or TCP_CLOSE_WAIT, both
      inside [tcp_need_reset]'s mask, so [tcp_disconnect] really does
      send an RST — and leaves a socket that is neither connected nor
      fresh in this model's vocabulary.
    - [SkConnected _ _ NRst], [SkConnected _ _ NTimedOut] and [SkReset]:
      NO RST IS SENT, and saying otherwise would contradict this file
      two paragraphs up.  [tcp_done] has already run for [SkReset]
      ([State.v] says so: that is what the constructor MEANS) and may
      already have run for the other two, since the reset arrives when
      the SEGMENT does and not when the program reads it.  Either way
      the socket is TCP_CLOSE, which [tcp_need_reset]'s mask
      ({ESTABLISHED, CLOSE_WAIT, FIN_WAIT1, FIN_WAIT2, SYN_RECV})
      EXCLUDES, so [tcp_disconnect] only clears queues and timers and
      returns 0.  The decline stands anyway, on [SkBound]'s reason
      rather than on an RST: the port and queue bookkeeping it changes
      is not something [SockState] carries.

    WHAT IS UNREACHABLE RATHER THAN DECLINED, with what would falsify
    each claim, because an absence argument rots as the modeled surface
    grows:
    - -EINPROGRESS.  ASSIGNED only after [sk->sk_prot->connect] has
      returned >= 0, strictly inside the declined region, so no arm that
      answers here can be preempted by it.  The argument is positional
      and not "only on a non-blocking socket", which is false:
      [inet_wait_for_connect] returns 0 when a set SO_SNDTIMEO expires,
      so a BLOCKING socket returns -EINPROGRESS too.
    - -EALREADY, and -EISCONN from the [DEFER_CONNECT] arm.  Both need
      [sock->state] to be SS_CONNECTING, which only a connect that
      already returned can produce — and every connect that gets that
      far is [unmodeled] here, so no modeled execution has such a
      socket.  Admitting a connect result is what would make them real.
    - Every errno of net/unix/af_unix.c [unix_stream_connect] and
      [unix_dgram_connect] — including -EINVAL, not -EISCONN, for a
      listening socket, the one place the two families disagree on an
      answer this spec gives.  [socket_spec] admits only AF_INET
      SOCK_STREAM into the fd table, so [ops->connect] is always
      [inet_stream_connect] and neither function is ever entered.  An
      AF_UNIX ADDRESS on an AF_INET socket is a different thing and IS
      answered: -EAFNOSUPPORT, after the 16-byte -EINVAL.  Modeling
      AF_UNIX sockets is what would make the unix path reachable.
    - [__inet_stream_connect]'s [default:] -EINVAL arm, for
      SS_DISCONNECTING.  TWO things write that state and both are shut:
      a failed disconnect, and [tcp_disconnect] cannot fail; and
      [inet_shutdown], which needs SS_CONNECTING.  [shutdown] (210) IS
      dispatched here, so the argument rests on the connect
      half alone.  SS_CONNECTING is written only by a connect that
      already returned, and every such connect is [unmodeled] above, so
      no modeled execution reaches a [shutdown] on one.  Nor could that
      spec write the state if it did: [shutdown_spec]'s one answering
      arm is [SkListening] under SHUT_WR, and every other socket state
      is [unmodeled].
    - [tcp_v4_connect]'s second -EINVAL, [if (!daddr) return -EINVAL]
      under [inet_opt->opt.srr]: [inet_opt] is set by
      setsockopt(IP_OPTIONS).  [setsockopt] (208) IS in [modeled_sysnos],
      but IP_OPTIONS is an
      option-table call at a KNOWN level (SOL_IP), and [setsockopt_spec]
      answers every one of those [unmodeled] — a run that issues it
      leaves the modeled surface AT THAT CALL and never reaches this
      [connect].

    NARROWINGS, all of them "fewer behaviors, never more", and each
    stated by which arms it can and cannot preempt:
    - [security_socket_connect] runs in [__sys_connect_file], between
      [sock_from_file] and [ops->connect] — so BEFORE everything
      [__inet_stream_connect] does.  An LSM can therefore answer
      -EACCES/-EPERM where this spec answers step 3's -EINVAL, step 5's
      -EINVAL/-EAFNOSUPPORT, -EISCONN, AND the AF_UNSPEC 0, which is the
      only arm here that answers a success.  It cannot where this spec
      answers -EBADF, -ENOTSOCK, or [move_addr_to_kernel]'s
      -EINVAL/-EFAULT, all of which precede it.  (The default hook
      returns 0, include/linux/lsm_hook_defs.h.)
    - A cgroup BPF program at CGROUP_INET4_CONNECT
      ([BPF_CGROUP_PRE_CONNECT_ENABLED]) can return an arbitrary error,
      and it is NOT confined to the declined region: [pre_connect] runs
      inside the SS_UNCONNECTED arm, after the [sk_state != TCP_CLOSE]
      bail but BEFORE [tcp_v4_connect].  So it can preempt step 5's
      -EAFNOSUPPORT.  It cannot preempt -EISCONN, which is above it, nor
      step 5's 16-byte -EINVAL, which [tcp_v4_pre_connect] REPLICATES
      above it for exactly this reason.
    - [move_addr_to_kernel] ends with [audit_sockaddr], whose
      [__audit_sockaddr] kmallocs and can answer -ENOMEM when auditing
      is on.  It sits after the copy and after the [ulen == 0] early
      return, so Linux can answer -ENOMEM wherever this spec answers
      anything past step 1 AT A NONZERO LENGTH — not on the -EINVAL a
      zero-length address gets. *)
Definition connect_spec (fd addrp addrlen : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* [fd_empty], before the address is touched *)
  | Some e =>
      let al := sint32 addrlen in
      if orb (Z.ltb al 0) (Z.ltb SOCKADDR_STORAGE_SIZE al) then err_ret EINVAL
      else
      match read_bytes_map (in_mem i) addrp (Z_to_bv 64 al) with
      | None => err_ret EFAULT                   (* copy_from_user failed, BEFORE -ENOTSOCK *)
      | Some bs =>
          record_copyins (if Z.eqb al 0 then [] else [(addrp, length bs)])
          (* the copy is attached HERE, above the -ENOTSOCK arm, because
             that is where [move_addr_to_kernel] performed it; a
             zero-length address reads no user byte and so records
             nothing *)
          (match e with
           | FdSocket sk =>
               if Z.ltb al SA_FAMILY_SIZE then err_ret EINVAL
                 (* [__inet_stream_connect]'s first test; also where a
                    zero-length address lands *)
               else if Z.eqb (sa_family_of bs) AF_UNSPEC then
                 match sk with
                 | SkFresh => ret_only (Z_to_bv 64 0)
                     (* [tcp_disconnect] on a socket with nothing to
                        disconnect: returns 0, changes nothing modeled *)
                 | SkBound | SkListening
                 | SkConnected _ _ _ | SkReset _ _ => unmodeled
                     (* a real disconnect: port release, accept-queue
                        teardown, or an RST — see above *)
                 end
               else
                 match sk with
                 | SkListening | SkConnected _ _ _ | SkReset _ _ =>
                     err_ret EISCONN
                     (* NOT -EINVAL.  Listening is SS_UNCONNECTED with
                        [sk_state] TCP_LISTEN, which the SS_UNCONNECTED
                        arm's pre-loaded -EISCONN catches; accepted and
                        reset sockets are SS_CONNECTED. *)
                 | SkFresh | SkBound =>
                     if Z.ltb al SOCKADDR_IN_SIZE then err_ret EINVAL
                     else if negb (Z.eqb (sa_family_of bs) AF_INET)
                     then err_ret EAFNOSUPPORT   (* [tcp_v4_connect], NOT -EINVAL *)
                     else unmodeled              (* the attempt itself: the environment's *)
                 end
           | _ => err_ret ENOTSOCK               (* [sock_from_file], AFTER the copy *)
           end)
      end
  end.

(* =========================================================================
   Socket options and addresses: getsockname (204), getpeername (205),
   setsockopt (208), getsockopt (209), shutdown (210)
   ========================================================================= *)

(** WHAT THE FIVE SHARE IS THE DESCRIPTOR — AND NOTHING ELSE.

    [__sys_getsockname], [__sys_getpeername], [__sys_setsockopt],
    [__sys_getsockopt] and [__sys_shutdown] (net/socket.c) each open with
    the descriptor lookup ([sockfd_lookup_light] to v6.12, inlined from
    v6.13), which presets -EBADF, calls [fdget], and
    answers -ENOTSOCK once [fdget] has produced a file whose [f_op] is
    not [socket_file_ops] ([sock_from_file], same file).  NOTHING else
    about the call is examined before that verdict, so on a descriptor
    that is NOT a socket the answer still does not depend on the level,
    the optname, the option buffer, the address buffer, or [how].  That
    much is [sock_fd], and it is the whole of these five calls on a
    channel, a file or a directory fd.

    ON A SOCKET THEY SHARE NOTHING, which is why there are five
    definitions below and not one.  The [FdEntry] arms are spelled out
    rather than matched with a wildcard SO THAT a new [FdEntry]
    constructor breaks the definition and forces
    an answer, rather than silently inheriting -ENOTSOCK for a descriptor
    that IS a socket.

    -ENOTSOCK IS NOT A TOTAL ANSWER.  [socket_spec] (198) and
    [accept4_spec] (202/242) hand out socket fds, so only the [sock_fd]
    half holds for every descriptor.  The exactness claim is confined
    below to the arms that earn it, each with the version window it was
    checked over.

    ONE ROUTE PAST [sock_fd]'s DICHOTOMY EXISTS ON LINUX, and the model
    is closed to it for a separate reason.  An O_PATH descriptor carries
    [FMODE_PATH], which [fdget]'s mask rejects, so all five answer -EBADF
    on it — even on [open("/proc/self/fd/N", O_PATH)] where N really is a
    socket, an OPEN descriptor that is nonetheless -EBADF rather than
    -ENOTSOCK.  No modeled program can hold one: [modeled_open_flags]
    declines O_PATH before an fd is allocated.

    A NOTE ON THE LSM, once, for all five.  Each call runs a
    [security_socket_*] hook past the lookup, and every hook here can
    deny.  This model, like every other spec in this file, describes a
    kernel whose active LSMs do not deny (the default capability LSM's
    socket hooks all return 0); an enforcing SELinux or AppArmor policy
    is outside the modeled environment, not a case answered wrongly. *)
Definition sock_fd (m : Model) (fd : word) : SockState + Z :=
  match fd_lookup (m_fds m) fd with
  | None                => inr EBADF   (* fd not open: real -EBADF, before any argument is examined *)
  | Some (FdChannel _)  => inr ENOTSOCK    (* an external channel is not a socket *)
  | Some (FdFile _ _)   => inr ENOTSOCK
  | Some (FdFileW _ _)  => inr ENOTSOCK
  | Some (FdFileA _ _)  => inr ENOTSOCK
  | Some (FdFileRW _ _) => inr ENOTSOCK
  | Some FdDir          => inr ENOTSOCK
  | Some (FdPipe _ _)   => inr ENOTSOCK  (* a pipe end is not a socket either: [pipeanon_fops]
                                            is not [socket_file_ops], so [sock_from_file]
                                            returns NULL (net/socket.c, v6.18.46) *)
  | Some (FdDevNull _ _) => inr ENOTSOCK (* nor is /dev/null: its [f_op] is [null_fops]
                                            (drivers/char/mem.c), and the same comparison
                                            fails *)
  | Some FdUrandom => inr ENOTSOCK       (* nor /dev/urandom: [urandom_fops]
                                            (drivers/char/random.c) *)
  | Some (FdSocket sk)  => inl sk
  end.

(** A level with a handler on an AF_INET/SOCK_STREAM socket.  Anything
    else is refused BY THE LEVEL, and the two option calls refuse it with
    DIFFERENT ERRNOS — see [setsockopt_spec] and [getsockopt_spec]. *)
Definition sock_level_known (level : word) : bool :=
  let l := bv_unsigned level in
  ((l =? SOL_SOCKET) || (l =? IPPROTO_IP) || (l =? IPPROTO_TCP))%Z%bool.

(** [how] is one of the three [enum sock_shutdown_cmd] members. *)
Definition shut_how_ok (how : word) : bool :=
  let h := bv_unsigned how in
  ((h =? SHUT_RD) || (h =? SHUT_WR) || (h =? SHUT_RDWR))%Z%bool.

(** Negative when its LOW 32 BITS are read as the [int] the argument is.
    [sint32] does that truncation itself, so this is total on a [word]:
    the model's tests on these arguments are the kernel's own, and the
    kernel's are on the truncated [int]. *)
Definition int32_neg (w : word) : bool := (sint32 w <? 0)%Z.

(** [getsockname fd addr addrlen] (204) — DECLINED ON A SOCKET, and the
    reason is worth stating because it is not "hard".

    [inet_getname] (net/ipv4/af_inet.c) with [peer = 0] HAS NO ERROR
    RETURN AT ALL: it fills a [sockaddr_in] from [inet_sport] and
    [inet_rcv_saddr] (falling back to [inet_saddr]) and returns a length.
    So on a socket the only answer this call has is a SUCCESS THAT WRITES
    AN ADDRESS THROUGH [move_addr_to_user], and that write is what the
    model cannot do: [SyscallEffect] has no [sockaddr_in] export, and
    [move_addr_to_user] (net/socket.c, byte-identical v6.1-v6.17) is a
    three-step in/out protocol — [get_user(len, ulen)]; clamp
    [len] down to [klen]; -EINVAL if the user's [len] was negative (the
    clamp runs FIRST, so a negative length survives it); copy [len]
    bytes; then write back the UNTRUNCATED [klen].  This is the same
    write [accept4_spec] declines its non-NULL address argument over, and
    declining it in one place and inventing it in another would be
    incoherent.

    AND THE VALUE IS NOT THE MODEL'S TO KNOW past [SkFresh].  A fresh
    socket really is 0.0.0.0:0 — [inet_create] allocates through
    [sk_alloc] with [__GFP_ZERO], so [inet_sport], [inet_rcv_saddr] and
    [inet_saddr] are all 0 — but [bind] and [listen] autobind an
    EPHEMERAL PORT, and net/ipv4/inet_connection_sock.c
    [inet_csk_find_open_port] draws it with [get_random_u32_below] (that
    spelling from v6.2; v6.1 called the same primitive
    [prandom_u32_max]) over the per-netns [ip_local_port_range] sysctl,
    scanning a machine-global bind hash.  A [SkConnected] socket handed
    over by [accept] inherits the listener's port, so it is not a
    function of the process's own state either.  Answering here would
    mean answering from a [choose], and a [choose] over a value a program
    can PRINT is a trace this model would have to admit and Linux would
    not produce.

    (One more reason not to hard-code 16 as the length: from v6.7
    [inet_getname] returns a local [sin_addr_len] that a
    CGROUP_INET4_GETSOCKNAME BPF program may rewrite, where up to v6.6 it
    was a literal [return sizeof] of the [sockaddr_in].) *)
Definition getsockname_spec (fd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match sock_fd m fd with
  | inr e => err_ret e
  | inl _ => unmodeled                 (* an address write, and a port the model cannot know *)
  end.

(** [getpeername fd addr addrlen] (205) — THE ONE CALL OF THE FIVE THAT
    SEPARATES THE SOCKET STATES, and the arm this model most wanted.

    [inet_getname] with [peer = 1] (net/ipv4/af_inet.c) refuses first:

      if (!inet->inet_dport ||
          (((1 << sk->sk_state) & (TCPF_CLOSE | TCPF_SYN_SENT)) &&
           peer == 1))
              return -ENOTCONN;

    and only past that copies the address out.  THE WINDOW BELONGS TO
    THE TEST, NOT TO THE FUNCTION: the statement above is byte-identical
    v6.1-v6.19, while [inet_getname] around it changed twice in that
    span — v6.7 gave it the [sin_addr_len] out-parameter
    [getsockname_spec] records above, and v6.19 dropped its
    [struct sockaddr] casts.  (The kernel writes the refusal with
    braces and a [release_sock(sk)] ahead of the return; the CONDITION
    is quoted exactly.)  Two disjunct, and each catches a different set
    of this model's states:

    - [inet_dport == 0] on every socket that was never connected —
      [SkFresh], [SkBound], [SkListening].  Nothing about the address
      buffer is consulted, so this is a plain errno with no memory
      effect, and it is EXACT.
    - [sk_state] in [TCPF_CLOSE] on [SkReset].  This is the whole reason
      [State.SockState] carries [SkReset] as a constructor of its own,
      and this arm is where it pays: a peer RST ran net/ipv4/tcp.c
      [tcp_done] (reached from tcp_input.c [tcp_reset] directly up to
      v6.10, through [tcp_done_with_error] from v6.11), which does
      [tcp_set_state(sk, TCP_CLOSE)] and does NOT clear [inet_dport].
      The dport survives; the STATE test fires.  A consumed FIN, by
      contrast, leaves TCP_CLOSE_WAIT, which is in NEITHER disjunct — so
      [SkConnected peer ch NFin] SUCCEEDS and returns the peer, while
      [SkReset peer ch] is -ENOTCONN.  Collapsing the two states would
      have made this call answer confidently and wrongly on one of them.

    [SkConnected] is declined, and only for [getsockname_spec]'s reason:
    the answer is a success that writes an address.  The address itself
    is available and honest — [nq_peer] took it from the quantified
    [ProcInput], never from a [choose] — so this decline is a missing
    export, not a missing value.  (The decline also absorbs a timing the
    model does not track: a script whose head is [NRst] has, on a real
    kernel, ALREADY run [tcp_done] by the time the program asks, so that
    socket may be -ENOTCONN before any read consumes the reset.  Failing
    closed there is right; answering would have been a guess about when
    the segment arrived.) *)
Definition getpeername_spec (fd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match sock_fd m fd with
  | inr e => err_ret e
  | inl sk =>
      match sk with
      | SkFresh            => err_ret ENOTCONN   (* inet_dport == 0 *)
      | SkBound            => err_ret ENOTCONN
      | SkListening        => err_ret ENOTCONN
      | SkReset _ _        => err_ret ENOTCONN   (* tcp_done left TCP_CLOSE; dport still set *)
      | SkConnected _ _ _  => unmodeled          (* succeeds, writing the peer: no address export *)
      end
  end.

(** [setsockopt fd level optname optval optlen] (208).  Two arms are
    real, and the level arm is NOT the same errno [getsockopt] gives.

    -EINVAL FOR A NEGATIVE [optlen], FIRST.  [do_sock_setsockopt]
    (net/socket.c) opens with [if (optlen < 0) return -EINVAL;] — ahead
    of [security_socket_setsockopt], ahead of
    [BPF_CGROUP_RUN_PROG_SETSOCKOPT], ahead of every level dispatch — so
    it is the answer on any socket whatever the level, the optname or the
    buffer.  VERSION-DEPENDENT, and the window matters: identical v6.7
    through v6.19, but up to v6.6 the check sat in [__sys_setsockopt]
    AHEAD OF [sockfd_lookup_light], where the same call on a CLOSED fd
    was -EINVAL and not -EBADF.  This model states the v6.7-and-later
    order, which is why the check is inside the socket arm here rather
    than beside [sock_fd].

    -ENOPROTOOPT FOR AN UNKNOWN LEVEL, SECOND, and NOT -EOPNOTSUPP.
    Past the length, [do_sock_setsockopt] sends everything that is not
    SOL_SOCKET to [inet_stream_ops.setsockopt] = [sock_common_setsockopt]
    -> [tcp_setsockopt], which forwards any level but SOL_TCP to
    [ipv4_specific.setsockopt] = [ip_setsockopt] (net/ipv4/ip_sockglue.c),
    whose FIRST statement is [if (level != SOL_IP) return -ENOPROTOOPT;].
    Unchanged v6.1 through v6.19.  The check is in [ip_setsockopt] and
    not in [do_ip_setsockopt], which has no level test at all — and
    [getsockopt]'s mirror image of this path answers -EOPNOTSUPP instead
    (see [getsockopt_spec]).  THE ASYMMETRY IS REAL and is exactly the
    shape a model invents symmetry over.
    No user memory is read on the way: [optval] is untouched and [optlen]
    is by value.

    EVERYTHING PAST THE LEVEL IS DECLINED — the option table itself.
    Three shapes it would have to get right, none of them guessable:
    an unknown optname is -ENOPROTOOPT at every layer and not -EINVAL
    (net/core/sock.c [sk_setsockopt]'s [default:]); two options ACCEPT
    AND DISCARD, validating their argument, storing nothing and returning
    0 — SO_BSDCOMPAT (a bare [break] in [sk_setsockopt]) and
    TCP_THIN_DUPACK (net/ipv4/tcp.c [do_tcp_setsockopt] validates
    [val] in {0,1} and stores it nowhere); and several options really do
    change later behaviour, so accepting them silently is not free. *)
Definition setsockopt_spec (fd level optlen : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match sock_fd m fd with
  | inr e => err_ret e
  | inl _ =>
      if int32_neg optlen then err_ret EINVAL       (* do_sock_setsockopt's first statement (v6.7+) *)
      else if negb (sock_level_known level) then err_ret ENOPROTOOPT   (* ip_setsockopt *)
      else unmodeled                                (* the option table *)
  end.

(** [getsockopt fd level optname optval optlen] (209) — the same walk,
    the OTHER errno.

    [do_sock_getsockopt] (net/socket.c) handles SOL_SOCKET itself
    ([sk_getsockopt]) and sends every other level to
    [inet_stream_ops.getsockopt] = [sock_common_getsockopt] ->
    [tcp_getsockopt], which forwards any level but SOL_TCP to
    [ipv4_specific.getsockopt] = [ip_getsockopt] -> [do_ip_getsockopt],
    whose FIRST statement is [if (level != SOL_IP) return -EOPNOTSUPP;].
    Unchanged v6.1 through v6.19.  So an unknown level is -EOPNOTSUPP
    here and -ENOPROTOOPT on the set side, out of two different functions
    in the same file.

    IT ALSO BEATS A BAD [optlen] POINTER, which is the ordering a reader
    expects backwards.  The length that DECIDES anything is read inside
    [do_ip_getsockopt] ([copy_from_sockptr] -> -EFAULT) and inside
    [sk_getsockopt], both DOWNSTREAM of the level test, so
    [getsockopt(sockfd, 12345, ..., NULL)] is -EOPNOTSUPP and not -EFAULT.

    FOUR BYTES AT [optlen] ARE READ ANYWAY, BEFORE THE DISPATCH, and this
    spec RECORDS them.  [do_sock_getsockopt] (net/socket.c) runs
    [security_socket_getsockopt] and returns on its error, and then —
    before it has looked at [level] at all —

      if (!compat)
              copy_from_sockptr(&max_optlen, optlen, sizeof(int));

    [__sys_getsockopt] passes [in_compat_syscall()] for [compat], false
    for a native riscv64 task, so on this port the read is
    UNCONDITIONAL: every -EOPNOTSUPP this spec gives has already moved
    four bytes out of user memory.  The RESULT is discarded — no
    assignment, no test, and [max_optlen] simply keeps its [= 0]
    initialiser when the copy faults — so it changes no errno.  What it
    changes is [eff_copyins], which is neither a write nor a return
    value; the bytes really left user memory, so the ledger names them.
    ([Checks.Sys.Net.Socket.check_getsockopt] compares that ledger.)

    THE VERSION WINDOW IS NOT A RANGE, because the change was BACKPORTED
    and two stable branches carry it below the mainline tag.  The read
    has always sat in this POSITION, between the LSM hook and the level
    dispatch — v5.15, v6.1, v6.4, v6.6, v6.10 and v6.18 all agree.  What
    changed is whether it FIRES.  Before the fix it was
    [BPF_CGROUP_GETSOCKOPT_MAX_OPTLEN] (include/linux/bpf-cgroup.h),
    whose body is [if (cgroup_bpf_enabled(CGROUP_GETSOCKOPT))
    get_user(__ret, optlen);], so a kernel with no cgroup BPF getsockopt
    program attached read NOTHING.  Commit 33f339a1ba54 ("bpf, net: Fix a
    potential race in do_sock_getsockopt()") deleted the macro and left
    the bare [copy_from_sockptr].  Where it is:

      - mainline: v6.11-rc7 and later, so every v6.11 release and
        everything after it.  NOT rc1 — the commit's committer date is
        2024-09-03, after v6.11-rc6 was tagged;
      - linux-6.6.y: v6.6.51 and later (backport f8d6acb19f4a).  NOT
        v6.6.50;
      - linux-6.10.y: v6.10.10 and later (backport e454476c4452).  NOT
        v6.10.9;
      - linux-6.1.y, linux-5.15.y, linux-5.10.y: NEVER — read at the
        6.1.185, 5.15.218 and 5.10.267 tips, all three still carry the
        guarded macro.

    v6.6.51 is therefore the OLDEST release carrying it, and "v6.11+" is
    the wrong window in both directions.  The modeled tree — stable
    v6.18.46, 1f99e9ab748f — is inside it, so this ledger is exact
    there.  Run against an older kernel, or any 6.1/5.15/5.10 point
    release, it names a read that happens only with a cgroup BPF program
    attached: a range too MANY.  [State.syscall_effect_accesses] charges
    what the ledger names, so a range too many can only reject, never
    accept — the safe direction for a spec that targets v6.18.

    WHETHER TO RECORD AN UNREADABLE [optlen] IS A DECISION, not a
    default, because the errno does not settle it: a faulting
    [copy_from_sockptr] is discarded exactly like a successful one, so
    -EOPNOTSUPP stands either way and both ledgers were available.  It is
    recorded only when the whole four-byte range is MAPPED.  An
    unconditional ledger would claim four bytes left user memory on a
    call where [copy_from_user] took its fixup path and moved none, and
    [eff_copyins] feeds [State.materialize_model_accesses], which charges
    a first touch against the backing limit — so it would charge a page
    the kernel never faulted in and could refuse a run Linux allows.
    That is [bind_spec]'s boundary above ([move_addr_to_kernel]'s failed
    copy transfers nothing) and [Kernel.Time.Hrtimer.nanosleep_spec]'s.

    ONE RESIDUE, NAMED RATHER THAN LEFT SILENT.  [copy_from_user] copies
    PARTIALLY: a four-byte [optlen] straddling a page boundary whose
    first page is mapped really does touch that first page before
    faulting, while [read_bytes_map] fails on the whole range and this
    spec then records nothing.  That under-records by at most one page,
    in the accept-more direction, and it is the
    identical bound [bind_spec] and [nanosleep_spec] carry.
    The [struct iovec] copy-in ledger (readv/writev/sendmsg/import)
    carries it too: on riscv64 with HAVE_EFFICIENT_UNALIGNED_ACCESS off,
    [__get_user_nocheck] copies a misaligned [iov_len] one byte at a
    time (arch/riscv/include/asm/uaccess.h:188-194, arch/riscv/lib/
    uaccess.S), so a field crossing from a lazily-backed page into an
    unmapped one touches the first page, while the ledger records
    nothing for a faulting field and charges no page.
    Closing it needs a longest-readable-prefix range
    and would have to move all four at once.

    A KNOWN LEVEL IS DECLINED, for [setsockopt_spec]'s reasons plus one
    of its own: on the get side an over-long [*optlen] is silently
    TRUNCATED rather than refused, and [*optlen] is rewritten to the
    bytes actually copied — a memory write, and the export the model
    does not have.  The ledger is recorded on that arm too, and simply
    never compared: an [Unmodeled] carries no effect for a ledger to be
    right or wrong about. *)

(** The four bytes [do_sock_getsockopt] reads at [optlen] before it
    dispatches on the level, or NOTHING when that range is not wholly
    readable and [copy_from_user] therefore moved none of it.  One
    definition for the spec, the checker and the witness so the three
    cannot drift apart. *)
Definition getsockopt_optlen_read (i : SyscallInput) (optlenp : word)
    : list (word * nat) :=
  match read_bytes_map (in_mem i) optlenp (Z_to_bv 64 4) with
  | Some _ => [(optlenp, 4%nat)]
  | None => []
  end.

Definition getsockopt_spec (fd level optlenp : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match sock_fd m fd with
  | inr e => err_ret e
      (* [__sys_getsockopt] resolves the fd before it calls
         [do_sock_getsockopt], so neither -EBADF nor -ENOTSOCK reaches
         the read and neither carries a ledger *)
  | inl _ =>
      record_copyins (getsockopt_optlen_read i optlenp)
        (if negb (sock_level_known level) then err_ret EOPNOTSUPP  (* do_ip_getsockopt *)
         else unmodeled)                                           (* the option table *)
  end.

(** [shutdown fd how] (210).  Two real answers and a decline, and the
    DECLINE is the most carefully argued arm in this file.

    -EINVAL FOR A [how] OUTSIDE {0,1,2}, ON EVERY SOCKET STATE.  Nothing
    in net/socket.c tests [how] — neither [__sys_shutdown] nor
    [__sys_shutdown_sock] contains a single test on it — which is why a
    NON-socket fd is -ENOTSOCK and not -EINVAL however wild the argument.
    The rejection is [inet_shutdown]'s (net/ipv4/af_inet.c), and it is
    the first thing that function does:

      how++;                              // 0->1, 1->2, 2->3
      if ((how & ~SHUTDOWN_MASK) || !how) // MAXINT->0
              return -EINVAL;
      lock_sock(sk);

    It returns BEFORE [lock_sock] and before any write to [sk_shutdown],
    so this -EINVAL leaves the socket bit-for-bit unchanged — which is
    what lets the model answer it without tracking anything.  Unchanged
    v6.1 through v6.19.  (Note the [how++]: userspace's 0/1/2 become the
    [RCV_SHUTDOWN]/[SEND_SHUTDOWN] bits 1/2/3 of include/net/sock.h.
    [how = -1] passes [~SHUTDOWN_MASK] and is caught by [!how]; that is
    what the [MAXINT->0] comment means.)

    0 FOR SHUT_WR ON A LISTENING SOCKET, WITH NO STATE CHANGE.  The
    switch on [sk_state] has a [case TCP_LISTEN:] whose whole body is
    [if (!(how & RCV_SHUTDOWN)) break;].  For SHUT_WR the incremented
    [how] is 2, [2 & RCV_SHUTDOWN] is 0, and the [break] leaves [err] at
    0 WITHOUT falling into the [default:] arm — so [sk_shutdown] is not
    ORed, [sk_prot->shutdown] is not called, and [disconnect] is not
    called.  A listener's [sock->state] is SS_UNCONNECTED, so the
    SS_CONNECTING fixup above the switch is a no-op too.  All that
    remains is [sk->sk_state_change(sk)], which wakes pollers, and this
    model has no poll.  Exact, and a genuine success rather than an
    errno.

    EVERYTHING ELSE IS DECLINED, AND HERE IS THE TRAP THAT FORCES IT.
    The obvious answer for [SkFresh]/[SkBound]/[SkReset] is -ENOTCONN,
    and the errno is right — those are TCP_CLOSE.  But [inet_shutdown]'s

      case TCP_CLOSE:
              err = -ENOTCONN;
              fallthrough;
      default:
              WRITE_ONCE(sk->sk_shutdown, sk->sk_shutdown | how);

    RETURNS THE ERROR AND STILL APPLIES THE SHUTDOWN.  ([WRITE_ONCE] from
    v6.4; v6.1-v6.3 spell the same store plainly.)  And the bit it sets
    is OBSERVABLE ON THE VERY NEXT READ: net/ipv4/tcp.c
    [tcp_recvmsg_locked] tests, in this order,
    [sock_flag(sk, SOCK_DONE)], then [sk->sk_err], then
    [if (sk->sk_shutdown & RCV_SHUTDOWN) break;], and only THEN
    [if (sk->sk_state == TCP_CLOSE) { copied = -ENOTCONN; break; }].
    RCV_SHUTDOWN shadows the TCP_CLOSE arm.  So on a real kernel

      shutdown(fresh_socket, SHUT_RD)  ->  -ENOTCONN
      read(fresh_socket, buf, n)       ->  0        (not -ENOTCONN)

    where without the shutdown that read is -ENOTCONN.  [State.SockState]
    carries no shutdown bits, so a spec that answered -ENOTCONN here
    would have to DROP them, and the next [read_spec] on that fd would
    then answer -ENOTCONN where Linux answers 0 — a confidently wrong
    answer one call later, which is precisely the class [Equivalence]'s
    [modeled] cannot see.  A right errno bought with a wrong successor
    state is not worth having; failing closed is.  The same argument
    covers SHUT_RD/SHUT_RDWR on a listener (they run [tcp_disconnect],
    which purges the accept queue and unbinds) and every [how] on
    [SkConnected] (the [default:] arm sets the bits and [tcp_shutdown]
    may send a FIN, moving ESTABLISHED to FIN_WAIT1 or CLOSE_WAIT to
    LAST_ACK).

    Closing any of that means giving [State.SockState] the two shutdown
    bits and teaching [read_spec] to consult them.  That is a real
    extension, not a guess, and it is deliberately not made here. *)
Definition shutdown_spec (fd how : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match sock_fd m fd with
  | inr e => err_ret e
  | inl sk =>
      if negb (shut_how_ok how) then err_ret EINVAL   (* inet_shutdown, before lock_sock *)
      else
        (* Spelled out rather than wildcarded, for [sock_fd]'s reason one
           level down: a socket state added to [State.SockState] must break
           this and force an answer, not inherit a decline.  Every arm but
           the listener's SHUT_WR declines over the same missing thing —
           the two shutdown bits [State.SockState] does not carry — and the
           kernel path that sets them is what differs per state. *)
        match sk with
        | SkFresh           => unmodeled              (* TCP_CLOSE: -ENOTCONN, bits set *)
        | SkBound           => unmodeled              (* still TCP_CLOSE; bind moves nothing *)
        | SkListening =>
            if (bv_unsigned how =? SHUT_WR)%Z
            then ret_only (Z_to_bv 64 0)              (* case TCP_LISTEN: break, nothing written *)
            else unmodeled                            (* SHUT_RD/SHUT_RDWR: tcp_disconnect *)
        | SkConnected _ _ _ => unmodeled              (* default: the bits, maybe a FIN *)
        | SkReset _ _       => unmodeled              (* tcp_done: TCP_CLOSE again *)
        end
  end.

(* =========================================================================
   The socket write path: sendto (206), sendmsg (211)

   MSG_NOSIGNAL IS REQUIRED, AND IT IS CHECKED FIRST.  Everything about
   these two specs follows from one line of the kernel, so it is worth
   stating before anything else.  net/core/stream.c [sk_stream_error]
   (v6.10-v6.15):

       if (err == -EPIPE)
               err = sock_error(sk) ? : -EPIPE;
       if (err == -EPIPE && !(flags & MSG_NOSIGNAL))
               send_sig(SIGPIPE, current, 0);

   Read both conditions.  SIGPIPE is raised IF AND ONLY IF the syscall's
   final return value is exactly -EPIPE AND the flag is clear — if
   [sk_err] held -ECONNRESET the first line replaces the errno and no
   signal is sent, and a partial send never reaches this function at all
   (net/ipv4/tcp.c [tcp_sendmsg_locked]'s [do_error:] does
   [if (copied + copied_syn) goto out;], returning the count and
   discarding the error).

   write(2) and writev(2) can never clear the hazard, so they stay
   [unmodeled] on a socket, permanently (see [Fs.ReadWrite.write_spec]).
   NOT because net/socket.c [sock_write_iter] sets only MSG_DONTWAIT — at
   v6.18.46 it also raises MSG_NOSIGNAL, out of [IOCB_NOSIGNAL], and
   MSG_EOR for SOCK_SEQPACKET.  The reason is that neither call can set
   [IOCB_NOSIGNAL]: include/linux/fs.h [iocb_flags] ORs only IOCB_APPEND,
   IOCB_DIRECT, IOCB_DSYNC and IOCB_SYNC, and RWF_NOSIGNAL reaches a
   kiocb only through [kiocb_set_rw_flags], which no write(2) or
   writev(2) path calls.  So the flag is not in reach of these two
   syscalls, which is the thing that matters, and it is one step further
   away than "not passed on".

   net/socket.c
   [__sys_sendto] and [___sys_sendmsg] both do [msg.msg_flags = flags]
   straight from the syscall argument, so for these two calls THE FLAG IS
   SOMETHING THE SPEC CAN READ.  That is the whole reason a socket write
   path is modelable at all.

   ORDER.  [Fs.Open.openat_spec] follows the kernel's own check order, and
   this spec deliberately does not: Linux consults MSG_NOSIGNAL last, at
   the bottom of the TCP layer, and this gate runs first, before the fd
   and before the buffer.  Three reasons, none of them tidiness:

   - A FINER GATE IS NOT EXPRESSIBLE HERE.  [Checks.ExecutableSpecs]'s
     [check_syscall_complete_unmodeled] and [check_syscall_err_iff] make
     one [Unmodeled] at an [(i, m)] forbid every [Ok] at that same
     [(i, m)]: an arm is receptive or declining, never both.  A reset
     connection can legally answer a partial count, -ECONNRESET, or
     -EPIPE-and-death from one state, so "decline only the arm that
     kills" is not a spec this development can write.  The whole region
     has to decline when the flag is clear.
   - IT DOES NOT DEPEND ON THE INPUT SPACE STAYING WIDE.  A gate placed
     after the fd would be sound today only because [Run.valid_input]
     places no constraint on [m_net]; the moment one excluded
     reset-at-offset-zero, a target could drop MSG_NOSIGNAL from a send
     and stay equivalent while Linux let it die.  A leading gate has no
     such coupling.
   - IT IS THE ONE GATE A READER MUST NOT MOVE, so it is where a reader
     looks first.

   What it costs is coverage, and the cost is named: a send whose flags
   are 0 is [unmodeled] even for shapes Linux answers safely and without
   any signal — -EBADF on a closed fd, -ENOTSOCK on stdout, -EFAULT on a
   bad range, and an ordinary successful send on a healthy connection.
   None is a shape a defensive reference program contains, and the last
   is not a real loss: [Equivalence.strong_universal_T] quantifies over
   every input including the reset one, so a [flags = 0] send fails the
   theorem whatever this spec's ordering.

   STANDING PRECONDITION.  SIGPIPE is the only signal reachable on this
   path.  What would falsify that is SIGIO: net/socket.c
   [sock_wake_async] raises it on a socket with
   [kill_fasync(&wq->fasync_list, SIGIO, band)], its default action is
   Term, and a model that answered such a send would be claiming a
   survival Linux does not grant.  (SIGURG travels the same list from
   that function's SOCK_WAKE_URG arm, but its default action is Ign and
   fs/fcntl.c [kill_fasync_rcu] suppresses it outright unless [F_SETSIG]
   set a nonzero [signum] -- [if (!(sig == SIGURG && fown->signum == 0))]
   -- so SIGIO is the half that carries the hazard.)

   LINUX NEEDS TWO INDEPENDENT SETTINGS FOR THAT, and this model closes
   each on its own, so the claim does not rest on a single decline.

   - THE SOCKET MUST BE ON A FASYNC LIST.  include/net/sock.h
     [sk_wake_async] reaches [sock_wake_async] only under
     [sock_flag(sk, SOCK_FASYNC)], and net/socket.c [sock_fasync] --
     registered as [socket_file_ops.fasync] -- is what sets that flag and
     builds the list.  Exactly two syscalls call it: [F_SETFL] with
     FASYNC in [arg], through fs/fcntl.c [setfl]'s
     [((arg ^ filp->f_flags) & FASYNC) && filp->f_op->fasync]; and the
     FIOASYNC ioctl (0x5452), through fs/ioctl.c [ioctl_fioasync].  BOTH
     ARE DECLINED HERE.  [Fs.Fcntl.setfl_acted_on] carries FASYNC even
     though the kernel's [SETFL_MASK] does not, so
     [Fs.Fcntl.setfl_noop_on] is false for any [arg] naming the bit and
     [Fs.Fcntl.fcntl_spec] answers [unmodeled];
     [setfl_noop_declines_fasync] below is that step mechanized rather
     than asserted.  FIOASYNC is not in [Fs.Ioctl.tty_only_request], so
     [Fs.Ioctl.ioctl_spec] declines it -- the modeled requests there are
     terminal-only and every one answers -ENOTTY, changing nothing.  Nor
     can the bit arrive at open time:
     [Fs.Fcntl.modeled_open_flags_clear_of_setfl] proves every word
     [Fs.Open.modeled_open_flags] admits is disjoint from
     [setfl_acted_on], and neither SOCK_CLOEXEC nor SOCK_NONBLOCK -- the
     only two bits [socket_spec], [socketpair_spec] and [accept4_spec]
     above let past [SOCK_TYPE_MASK] -- is FASYNC.  (Of those two,
     SOCK_NONBLOCK is separately DECLINED by the first and third; it is
     not by the second, which needs no gate because it hands back no
     descriptor.  That difference is immaterial here and load-bearing in
     [Fs.Fcntl.socket_f_flags], which states it.)
   - THE FILE MUST HAVE AN OWNER, and this half is structurally prior to
     the first rather than a second chance at it.  [struct fown_struct]
     is allocated LAZILY, and the only callers of fs/fcntl.c
     [file_f_owner_allocate] are [f_setown], [f_setown_ex] and
     [f_owner_sig] -- that is, [F_SETOWN], [F_SETOWN_EX] and [F_SETSIG],
     plus the FIOSETOWN / SIOCSPGRP ioctls, which net/socket.c
     [sock_ioctl] routes into that same [f_setown].  Setting FASYNC alone
     never allocates one, so [kill_fasync_rcu] takes its
     [if (!fown) goto next] and [send_sigio] -- whose own guard is
     [if (!pid) goto out_unlock_fown] -- is never entered.
     [Fs.Fcntl.fcntl_spec] models EXACTLY THREE COMMANDS -- [F_SETFD],
     the provably empty [F_SETFL] above, and an [F_GETFL] restricted to
     the fd kinds [Fs.Fcntl.getfl_f_flags] can derive a flag word for --
     and answers [unmodeled] for every other one; none of those ioctls
     is in [Fs.Ioctl.tty_only_request].
   - NO HANDLER CAN BE INSTALLED FOR EITHER SIGNAL, which is a third gate
     and not a restatement of the two above:
     [Kernel.Signal.sigaction_accepted] admits SIGINT and SIGTERM and
     nothing else, so [rt_sigaction(SIGIO, ...)] fails closed.  It is
     recorded here because a reader checking this claim will look for it,
     not because the claim leans on it.

   THE CLAIM IS OVER TWO MODELED SETS, and that is the form to keep true:
   {[F_SETFD], [F_SETFL], [F_GETFL]} for fcntl, and
   [Fs.Ioctl.tty_only_request] for ioctl.  ADDING A COMMAND TO EITHER
   BREAKS THIS SENTENCE -- an [F_SETOWN] arm, an [F_SETFL] that admitted
   FASYNC, or a FIOASYNC arm reopens the route directly.  [F_GETFL]
   clears both gates:
   fs/fcntl.c [do_fcntl]'s arm for it is [err = filp->f_flags; break;],
   whose whole body is that load, so it calls neither [sock_fasync] nor
   [file_f_owner_allocate].  Reaching one of those two functions is the
   test a new arm has to be put to; being a read is not the test, and
   the check is per arm rather than per shape.

   Only the FASYNC step is mechanized.  The command-set step is prose
   because a "[fcntl_spec] answers [unmodeled] outside these three
   commands" lemma has to invert the [Monad.Sys]
   relation, which needs [Checks.Sys.Prelude]'s [sys_unfold] and
   [inv_ok]; Checks sits ABOVE Sys, so that lemma's home is
   [Checks.Examples] and not this file.

   THIS PREMISE IS STATED OVER A COMMAND SET, NOT OVER A SYSCALL.
   [fcntl] (25) is modeled ([Sys.Fs.Fcntl], with an arm in
   [Sys.SyscallTable]), and a premise that named a whole syscall could
   go false without naming what had changed.

   (Linux v6.18.46 throughout: fs/fcntl.c [SETFL_MASK], [setfl],
   [send_sigio], [kill_fasync_rcu], [file_f_owner_allocate], [f_setown];
   fs/ioctl.c [ioctl_fioasync]; net/socket.c [sock_fasync],
   [sock_wake_async], [sock_ioctl]; include/net/sock.h [sk_wake_async].)
   ========================================================================= *)

(** The FASYNC half of the STANDING PRECONDITION above, mechanized rather
    than asserted: no [F_SETFL] this model answers can carry the bit that
    would put a socket on a fasync list.

    [Fs.Fcntl.setfl_acted_on] is a SUPERSET of the kernel's [SETFL_MASK].
    fs/fcntl.c (v6.18.46) defines that macro as
    [(O_APPEND | O_NONBLOCK | O_NDELAY | O_DIRECT | O_NOATIME)], with
    FASYNC deliberately OUTSIDE it -- the bit is written by the
    [->fasync] callback ([fasync_add_entry] / [fasync_remove_entry]),
    not by [setfl]'s closing masked assignment -- and
    [setfl_acted_on] adds it back so the arm's soundness does not depend
    on which [file_operations] the fd's filesystem defines.  That is
    [Fs.Fcntl]'s reason.  THIS remark is what turns the same constant
    into a guard for the claim above: dropping FASYNC from
    [setfl_acted_on] stops this proof, rather than silently reopening the
    SIGIO route. *)
Remark setfl_noop_declines_fasync : forall (e : FdEntry) (arg : word),
  setfl_noop_on e arg = true ->
  Z.land (bv_unsigned arg) FASYNC = 0%Z.
Proof.
  intros e arg H. unfold setfl_noop_on in H.
  destruct e; try discriminate;
    apply Z.eqb_eq in H;
    replace FASYNC with (Z.land setfl_acted_on FASYNC)
      by (vm_compute; reflexivity);
    rewrite Z.land_assoc, H; apply Z.land_0_l.
Qed.

(** MSG_NOSIGNAL (include/linux/socket.h, v6.10-v6.15). *)
Definition MSG_NOSIGNAL : Z := 0x4000%Z.

(** The [flags] argument is [unsigned int] in both
    [SYSCALL_DEFINE6(sendto)] and [SYSCALL_DEFINE3(sendmsg)], so the
    kernel sees only its low 32 bits — the same ABI truncation
    [Syscall.fd32] and [Syscall.cmd32] apply, at the same boundary. *)
Definition sendflags32 (fl : word) : word := abi_low32 fl.

(** THE FIRST GATE: the flag word is EXACTLY MSG_NOSIGNAL, and nothing
    else is modeled.

    Not "MSG_NOSIGNAL is among the bits set".  Every other MSG_* flag
    changes what the call means — MSG_DONTWAIT turns a wait into
    -EAGAIN, MSG_MORE corks, MSG_OOB sends urgent data, MSG_ZEROCOPY
    changes what the buffer is for — and none of them is modeled, so a
    flag word carrying one is declined rather than silently treated as a
    plain send.  Note that Linux IGNORES unknown flag bits on the TCP
    send path rather than rejecting them, so a permissive reading here
    would be a confident wrong answer for every bit this model does not
    interpret. *)
Definition send_flags_modeled (fl : word) : bool :=
  Z.eqb (bv_unsigned (sendflags32 fl)) MSG_NOSIGNAL.

(** The state of the connection as the SEND path sees it: the send
    either goes out, or answers a pending peer error once, or answers
    -EPIPE because there is no connection to send on. *)
Inductive SendState :=
  | SendGoes (chan : word)          (* ESTABLISHED or CLOSE_WAIT *)
  | SendErr (e : Z) (peer : PeerAddr) (chan : word)  (* one pending error *)
  | SendDead.                       (* no connection: -EPIPE, port or no port *)

(** How each socket state answers a send.

    - fresh, bound or listening, and a connection whose error has
      already been delivered: -EPIPE, and -EPIPE only.  There is NO
      -ENOTCONN on the TCP send path at all —
      net/core/stream.c [sk_stream_wait_connect] returns -EPIPE for every
      state outside SYN_SENT/SYN_RECV, and [tcp_sendmsg_locked] reaches it
      whenever the state is outside [TCPF_ESTABLISHED | TCPF_CLOSE_WAIT].
      (read(2) on the same socket IS -ENOTCONN; the two directions
      differ.)  With MSG_NOSIGNAL set that -EPIPE carries no signal,
      which is the entire point.
    - a pending RST or retransmit timeout: reported ONCE, because
      include/net/sock.h [sock_error] consumes it with an [xchg] — and it
      is consumed by whichever of read and send reaches it first, which
      is why the send transitions the socket exactly as a read does.
    - A FRESH SOCKET IS NOT A SPECIAL CASE, and the reason is worth
      recording because the shape of the call suggests it should be.
      net/ipv4/af_inet.c [inet_sendmsg] does run [inet_send_prepare]
      before it reaches TCP, and [inet_send_prepare] does answer -EAGAIN
      when it has to autobind and [inet_autobind]'s [get_port] fails.
      But it autobinds only under [!sk->sk_prot->no_autobind], and
      net/ipv4/tcp_ipv4.c's [tcp_prot] sets [.no_autobind = true]
      (v6.10-v6.15, and on linux-6.10.y / linux-6.11.y / linux-6.12.y).
      That branch is therefore DEAD for every socket [socket_spec] can
      create: [inet_send_prepare] returns 0 without looking at the port,
      [tcp_sendmsg_locked] sees TCP_CLOSE — outside
      [TCPF_ESTABLISHED | TCPF_CLOSE_WAIT] — and calls
      [sk_stream_wait_connect], which answers -EPIPE.  That helper's own
      -EAGAIN arm ([if (!*timeo_p) return -EAGAIN;]) sits BELOW its
      -EPIPE test and so is unreachable from TCP_CLOSE.  A send on a
      never-bound socket is -EPIPE, deterministically; admitting -EAGAIN
      alongside it would make this model answer an errno Linux cannot
      produce here, which is the permissive direction and the one that
      breaks soundness.
      ([listen_spec] is NOT this situation.  [listen]'s autobind is
      [inet_csk_listen_start]'s own [get_port] call, which no
      [no_autobind] flag guards, so its -EADDRINUSE branch is live and
      stays under [alt].)
    - CLOSE_WAIT: THE SEND SUCCEEDS.  The peer's FIN shuts down only the
      receive half, and CLOSE_WAIT is inside [tcp_sendmsg_locked]'s mask.
      This is the case a model gets wrong by assuming a closed peer
      means a closed connection. *)
Definition send_state (sk : SockState) : SendState :=
  match sk with
  | SkConnected peer ch NRst      => SendErr ECONNRESET peer ch
  | SkConnected peer ch NTimedOut => SendErr ETIMEDOUT peer ch
  | SkConnected _ ch NFin         => SendGoes ch   (* CLOSE_WAIT: sends go out *)
  | SkConnected _ ch (NCons _ _)  => SendGoes ch
  | SkReset _ _                   => SendDead
  | SkBound | SkListening         => SendDead
  | SkFresh                       => SendDead      (* no autobind for TCP *)
  end.

(** The body both calls share once their arguments have been reduced to
    "these bytes, on this socket".

    [bs] is the gatherable source — the readable prefix for [sendto],
    the gathered iovecs for [sendmsg] — and [total] is what the caller
    asked to send, so that a zero-length request is told apart from a
    request whose buffer is unreadable.

    THE LEDGER IS TWO PIECES, and both callers supply them.  [pre] is
    what the call has ALREADY copied out of user memory before reaching
    here — nothing for [sendto], the 56-byte header plus the iovec
    descriptors for [sendmsg] — and it is recorded on EVERY arm,
    including the ones that move no payload byte, because the kernel
    really did read those bytes before it looked at the connection.
    [acc] turns a delivered payload length into the ranges it came out
    of: the flat buffer for [sendto], the gathered prefix's segments for
    [sendmsg].  Splitting them is what lets one body serve two calls
    whose sources have different shapes; the alternative is two copies
    of the short-send rule.

    A SHORT SEND IS REAL, and it is the same rule
    [Fs.ReadWrite.write_spec] uses on a channel: any nonempty prefix of
    the gatherable bytes, with the environment choosing only the length.
    Every error path in [tcp_sendmsg_locked] funnels through [do_error:],
    whose [if (copied + copied_syn) goto out;] discards the error and
    returns the partial count, and the ordinary in-flight cases (a full
    send buffer under SO_SNDTIMEO, a signal) do the same.

    A SEND NEVER RETURNS 0 FOR A NONZERO REQUEST: either at least one
    byte was copied, or the answer is a negative errno.  That is why the
    chosen prefix is [1 <= length ds], and why an unreadable buffer is
    -EFAULT rather than a zero-length success.

    A ZERO-LENGTH REQUEST returns 0 — [tcp_sendmsg_locked]'s copy loop
    does not run, [copied] stays 0 and [out:] returns it — but only
    after the connection state has been consulted, which is why this is
    decided here and not before [send_state].  It records [pre] and
    nothing more: no payload byte is read, so the ledger carries no
    zero-length payload range, exactly as
    [Fs.ReadWrite.write_spec]'s zero-count file arm does not. *)
Definition send_bytes (pre : list (word * nat)) (acc : nat -> list (word * nat))
    (total : word) (bs : list byte) (ch : word) : Sys SyscallEffect :=
  if w_is0 total then record_copyins pre (ret_only (Z_to_bv 64 0))
  else if Nat.eqb (length bs) 0 then record_copyins pre (err_ret EFAULT)
  else
    ds <- choose (fun ds : list byte =>
                    (1 <= Z.of_nat (length ds))%Z
                    /\ (Z.of_nat (length ds) <= bv_unsigned total)%Z
                    /\ ds = firstn (length ds) bs) ;;
    emit (map (WriteEv ch) ds) ;;   (* one event per byte, on the CONNECTION's
                                       channel — the same alphabet a channel
                                       write emits, on a different channel *)
    record_copyins (pre ++ acc (length ds)) (ret_only (len_word ds)).

(** The socket half of both calls: dispatch on the connection's state,
    then send.  [total] and [bs] are the caller's; [fd] and [m] are
    needed to record an error's consumption. *)
Definition send_on_socket (pre : list (word * nat)) (acc : nat -> list (word * nat))
    (fd : word) (sk : SockState) (total : word) (bs : list byte) (m : Model)
    : Sys SyscallEffect :=
  match send_state sk with
  | SendDead => record_copyins pre (err_ret EPIPE)
      (* every no-connection state, the fresh socket included: TCP does
         not autobind on send, so there is no second errno to union in *)
  | SendErr e peer ch =>
      record_copyins pre
        (set_fds (fd_insert (m_fds m) fd (FdSocket (SkReset peer ch))) ;;
         err_ret e)
      (* consumed here exactly as [socket_pending_error] consumes it on
         the read side: one [sk_err], one [xchg], whichever direction
         gets there first.  The NEXT send is then -EPIPE, which is the
         classic two-step a program sees after a peer reset *)
  | SendGoes ch => send_bytes pre acc total bs ch
  end.

(** [sendto fd buf len flags addr addrlen].

    net/socket.c [__sys_sendto], v6.10-v6.15.

    THE MODEL GATES COME FIRST, all three of them, before any answer is
    committed to: the flag word (see the section header), a destination
    address, and a transfer this model cannot evaluate.

    A DESTINATION ADDRESS IS UNMODELED.  On a connected TCP socket
    [tcp_sendmsg_locked] reads [msg->msg_name] only under [tp->repair] and
    TCP Fast Open, so Linux validates the address with
    [move_addr_to_kernel] — -EINVAL outside [0, 128], -EFAULT if
    unreadable — and then ignores it.  Modeling "validated and
    discarded" means modeling [move_addr_to_kernel]'s two errnos for a
    value nothing reads; declining is smaller and loses only the
    [sendto(fd, .., addr, .., len)] spelling of a call every program
    writes as [send].  [addrlen] carries no condition: when [addr] is
    NULL the kernel never reads it.

    THEN THE KERNEL'S OWN ORDER, WHICH IS NOT write(2)'s.  [__sys_sendto]
    calls [import_ubuf] BEFORE it resolves the fd, so the buffer
    range is judged before the fd: [sendto(-1, unmapped, n, ...)] is
    -EFAULT and not -EBADF, the opposite of [write]. That is what
    [Uaccess.access_ok_zero] decides here — it is exactly [import_ubuf]'s
    [access_ok] verdict, applied to the whole call rather than only to
    its zero-length case.

    THEN THE FD: not open is -EBADF, open on anything but a socket is
    -ENOTSOCK ([sock_from_file]).  Neither can carry a signal, so
    neither needs the flag gate to have run — but it has, so a
    [flags = 0] call never reaches them.

    NOTHING IS RECORDED IN THE LEDGER BEFORE THE PAYLOAD, which is why
    [send_on_socket]'s [pre] is empty here.  [import_ubuf] is an
    [access_ok] RANGE test and copies no byte; the copy is
    [tcp_sendmsg_locked]'s, past the connection state.  So a -EBADF, an
    -ENOTSOCK and an -EPIPE all leave the ledger empty, and only a
    delivering send puts the prefix it actually moved into it.

    THE FD-RESOLUTION HELPER IS NOT ONE NAME ACROSS THIS WINDOW, which
    is why the comments below name the step and not the helper.  Both
    [__sys_sendto] and [__sys_sendmsg] call [sockfd_lookup_light] up to
    v6.12 mainline; the [CLASS(fd, f)] scope-guard refactor replaced it
    with [fd_empty] plus [sock_from_file] at v6.13, and that refactor
    was BACKPORTED, so linux-6.12.y already carries the new form while
    the v6.12 tag does not.  Nothing observable moves: both spellings
    answer -EBADF and then -ENOTSOCK, in that order, and neither changes
    position relative to [import_ubuf].

    [fd] arrives already truncated to 32 bits (see [Syscall.fd32]). *)
Definition sendto_spec (fd buf count flags addrp addrlen : word)
    : Sys SyscallEffect :=
  let _ := addrlen in                            (* never read: with [addr] NULL
                                                    the kernel does not look at
                                                    it, and a non-NULL [addr] is
                                                    declined below *)
  if negb (send_flags_modeled flags) then unmodeled
  else if negb (w_is0 addrp) then unmodeled
  else if negb (modeled_rw_count count) then unmodeled  (* see [Uaccess.rw_bytes_max] *)
  else
  i <- input ;;
  m <- get_model ;;
  (* THE BUFFER IS JUDGED BEFORE THE FD, AND THE NESTING IS THE CLAIM.
     [__sys_sendto] calls [import_ubuf] and only then resolves the fd
     ([sockfd_lookup_light] to v6.12 mainline, [CLASS(fd, f)] plus
     [fd_empty] from v6.13 and in linux-6.12.y), so
     [sendto(-1, unmapped, n, ...)] is -EFAULT
     and NOT -EBADF — the opposite of [Fs.ReadWrite.write_spec], and the
     opposite of [sendmsg_spec] below, which resolves its fd BEFORE
     copying its header.  The two calls are not the same call with
     different arguments and a later refactor must not align them.  This
     [Uaccess.access_ok_zero] is [import_ubuf]'s own [access_ok] verdict,
     so the fd match must stay INSIDE it. *)
  access_ok_zero buf count
    (match fd_lookup (m_fds m) fd with
     | None => err_ret EBADF                     (* fd not open: real -EBADF *)
     | Some (FdSocket sk) =>
         send_on_socket [] (fun n => [(buf, n)]) fd sk count
           (readable_bytes (in_mem i) buf count) m
     | Some _ => err_ret ENOTSOCK                (* not a socket: real -ENOTSOCK *)
     end).

(* -------------------------------------------------------------------- *)

(** [struct user_msghdr] on LP64 (include/linux/socket.h): seven fields,
    56 bytes, each 8-byte aligned.  [msg_namelen] and [msg_flags] are
    [int] and [unsigned int] and so occupy the low half of their slots,
    which is why the model reads whole words and compares against zero
    rather than decoding a signed 32-bit field it never uses. *)
Definition MSGHDR_SIZE : Z := 56%Z.

(** [sendmsg fd msg flags].

    net/socket.c [__sys_sendmsg] -> [copy_msghdr_from_user] ->
    [__copy_msghdr] -> [____sys_sendmsg], v6.10-v6.15.

    THE FLAG WORD COMES FROM THE SYSCALL ARGUMENT, NOT FROM THE
    STRUCTURE, and getting this backwards is the single easiest way to
    lose the whole guarantee.  [____sys_sendmsg] does

        flags |= (msg_sys->msg_flags & allowed_msghdr_flags);
        ...
        msg_sys->msg_flags = flags;

    and [__sys_sendmsg] passes [allowed_msghdr_flags = 0], so the first
    line contributes nothing and the second overwrites the field.  A
    [sendmsg(fd, &msg, 0)] whose [msg.msg_flags] is MSG_NOSIGNAL
    therefore TAKES SIGPIPE.  This spec reads [flags] and never the
    field, and the field is required to be zero only so that a program
    setting it cannot believe it did something.

    WHAT IS DECLINED, and why each is a gap rather than an errno:

    - a non-NULL [msg_name] — as for [sendto], validated and then
      ignored on a connected socket;
    - a non-zero [msg_control] or [msg_controllen] — ancillary data on a
      TCP socket reaches [ip_cmsg_send], whose vocabulary
      (IP_TTL, IP_PKTINFO, ...) this model has no representation for;
      note [____sys_sendmsg] answers -ENOBUFS for
      [msg_controllen > INT_MAX].  That test is the first thing INSIDE
      [____sys_sendmsg] and nowhere near first in the call: the
      MSG_CMSG_COMPAT gate's -EINVAL, the fd lookup's -EBADF,
      [sock_from_file]'s -ENOTSOCK, [copy_msghdr_from_user]'s -EFAULT on
      the 56-byte header, and [__copy_msghdr]'s -EINVAL / -EMSGSIZE all
      precede it, as does [import_iovec].  Either way it is an answer
      only reachable through a shape already declined here;
    - a [msg_iovlen] in the heap-backed range, for [readv]'s reason: the
      kernel keeps UIO_FASTIOV (8) descriptors on the stack and may fail
      the temporary allocation for more before reading any of them, and
      an optional -ENOMEM cannot be honestly unioned with a delivery.

    WHAT IS ANSWERED: an unreadable header is -EFAULT
    ([copy_from_user] of the whole 56 bytes, before any field is read);
    a [msg_iovlen] above UIO_MAXIOV is -EMSGSIZE, which is
    [__copy_msghdr]'s own errno and NOT [writev]'s -EINVAL; and past
    that the call is [writev]'s gather on the connection, sharing
    [State.copy_iovecs_aux] so that an unreadable descriptor is -EFAULT
    and a negative [iov_len] is -EINVAL, whichever comes first by index.

    THE LEDGER IS EVERY BYTE THE KERNEL REALLY READ, in the order it
    read them: the 56-byte header first — recorded from the point
    [copy_from_user] SUCCEEDED, so the -EFAULT above carries nothing —
    then the descriptor array as far as
    [State.copy_iovecs_accesses] walked it, then the payload prefix the
    send actually moved.  The -EMSGSIZE arm therefore carries the header
    alone and the two import errnos carry the header and the descriptors
    they touched, which is what makes those three answers distinguishable
    from one another by more than their errno.

    ORDER, AND IT IS THE OPPOSITE OF [sendto_spec]'s.  [__sys_sendmsg]
    looks the fd up FIRST and only then calls [___sys_sendmsg], which
    copies the header — where [__sys_sendto] imports its buffer before
    the fd.  So [sendmsg] on a closed fd with an unreadable [msg] is
    -EBADF while the analogous [sendto] is -EFAULT.  Two calls that look
    like each other and are not. *)
Definition sendmsg_spec (fd msgp flags : word) : Sys SyscallEffect :=
  (* [flags] IS THE SYSCALL ARGUMENT, AND IT IS THE ONLY THING READ HERE.
     Do not reach for [msg.msg_flags]: [____sys_sendmsg] does

         flags |= (msg_sys->msg_flags & allowed_msghdr_flags);
         ...
         msg_sys->msg_flags = flags;

     and [__sys_sendmsg] passes [allowed_msghdr_flags = 0], so the field
     contributes nothing and is then OVERWRITTEN by the argument.  A
     spec that consulted it would answer "MSG_NOSIGNAL was set, so no
     signal" for a [sendmsg(fd, &msg, 0)] that really does take SIGPIPE
     — unsound in the one direction this whole file exists to prevent.
     The field is checked nowhere below for the same reason. *)
  if negb (send_flags_modeled flags) then unmodeled
  else
  i <- input ;;
  m <- get_model ;;
  (* THE FD IS RESOLVED BEFORE THE HEADER IS COPIED, AND THAT IS THE
     OPPOSITE OF [sendto_spec].  [__sys_sendmsg] resolves the fd
     ([sockfd_lookup_light] to v6.12 mainline, [CLASS(fd, f)] plus
     [fd_empty] from v6.13 and in linux-6.12.y) and only then calls
     [___sys_sendmsg], which is where [copy_msghdr_from_user] lives — so
     [sendmsg] on a closed fd with an unreadable [msg] is -EBADF, while
     the analogous [sendto] is -EFAULT.  Order is behavior here: a later
     refactor that hoists the header read out to share it with [sendto]
     changes both answers. *)
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF
  | Some (FdChannel _) | Some (FdFile _ _)
  | Some (FdFileW _ _) | Some (FdFileA _ _) | Some (FdFileRW _ _)
  | Some FdDir
  | Some (FdPipe _ _)
  | Some (FdDevNull _ _)
  | Some FdUrandom =>          (* not a socket: [sock_from_file] is one comparison
                                  against [socket_file_ops], and a pipe end and the
                                  two device kinds all fail it *)
      err_ret ENOTSOCK
  | Some (FdSocket sk) =>
  match read_bytes_map (in_mem i) msgp (Z_to_bv 64 MSGHDR_SIZE) with
  | None => err_ret EFAULT     (* copy_from_user of the header: real -EFAULT *)
  | Some _ =>
      (* Six of the seven fields.  [msg_flags] at offset 48 is READ BY
         NOTHING, deliberately — see the note at the head of this
         definition. *)
      match read_u64 (in_mem i) msgp,
            read_u64 (in_mem i) (msgp + Z_to_bv 64 8),
            read_u64 (in_mem i) (msgp + Z_to_bv 64 16),
            read_u64 (in_mem i) (msgp + Z_to_bv 64 24),
            read_u64 (in_mem i) (msgp + Z_to_bv 64 32),
            read_u64 (in_mem i) (msgp + Z_to_bv 64 40) with
      | Some name, Some namelen, Some iov, Some iovlen, Some ctl, Some ctllen =>
          let _ := namelen in
          let _ := ctl in
          if negb (w_is0 name) then unmodeled
            (* A DESTINATION ADDRESS, declined for [sendto_spec]'s reason.
               [msg_namelen] carries no condition of its own: when
               [msg_name] is NULL, [__copy_msghdr] forces the length to 0
               BEFORE its sign test, so a NULL name with a negative
               length is an ordinary send rather than -EINVAL. *)
          else if (IOV_MAX <? bv_unsigned iovlen)%Z
          then record_copyins [(msgp, Z.to_nat MSGHDR_SIZE)] (err_ret EMSGSIZE)
            (* [__copy_msghdr]: [if (msg->msg_iovlen > UIO_MAXIOV) return
               -EMSGSIZE;] — NOT writev's -EINVAL, and decided on the
               full 64-bit field, which is [__kernel_size_t] here rather
               than the [unsigned] readv/writev truncate *)
          else if (UIO_FASTIOV <? bv_unsigned iovlen)%Z then unmodeled
            (* the heap-backed range: see [Fs.ReadWrite.readv_heap_gap] *)
          else
          match copy_iovecs_aux (in_mem i) iov (word_to_nat iovlen) with
          | ImpFault =>
              record_copyins ([(msgp, Z.to_nat MSGHDR_SIZE)]
                              ++ copy_iovecs_accesses (in_mem i) iov
                                   (word_to_nat iovlen))
                (err_ret EFAULT)                 (* unreadable descriptor *)
          | ImpInval =>
              record_copyins ([(msgp, Z.to_nat MSGHDR_SIZE)]
                              ++ copy_iovecs_accesses (in_mem i) iov
                                   (word_to_nat iovlen))
                (err_ret EINVAL)                 (* iov_len negative as ssize_t *)
          | ImpOk iovs0 =>
              if negb (w_is0 ctllen) then unmodeled
            (* ANCILLARY DATA, DECIDED WHERE THE KERNEL DECIDES IT.  The
               gate is on the LENGTH, not the pointer: [____sys_sendmsg]
               guards the whole control block with [else if (ctl_len)],
               so a non-NULL [msg_control] with [msg_controllen] 0 is
               never dereferenced and is a plain send.  Declining on the
               pointer would refuse a call Linux answers.

               AND IT SITS AFTER THE IMPORT, not before, because that is
               the kernel's order: [___sys_sendmsg] calls
               [sendmsg_copy_msghdr] -- which runs [__copy_msghdr] and
               [import_iovec], and so answers -EMSGSIZE, -EFAULT and
               -EINVAL -- and only then calls [____sys_sendmsg], whose
               first act on the control block is [ctl_len =
               msg_sys->msg_controllen].  So a call carrying BOTH a
               non-zero [msg_controllen] and an [iovlen] over [IOV_MAX]
               is -EMSGSIZE, not a decline; the import speaks first.
               (net/socket.c, [___sys_sendmsg] and [____sys_sendmsg];
               [__copy_msghdr]'s [msg_iovlen > UIO_MAXIOV] is where the
               -EMSGSIZE comes from.  This two-call split, and
               [____sys_sendmsg] reading [msg_controllen] only after it,
               is unchanged v5.15 through v6.18-rc1.) *)
              else if negb (iovs_total (cap_iovecs iovs0) <=? rw_bytes_max)%Z
              then unmodeled                     (* see [Uaccess.rw_bytes_max] *)
              else
              send_on_socket
                ([(msgp, Z.to_nat MSGHDR_SIZE)]
                 ++ copy_iovecs_accesses (in_mem i) iov (word_to_nat iovlen))
                (fun n => iov_prefix_accesses (cap_iovecs iovs0) n)
                fd sk
                (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))
                (writev_gathered (in_mem i) iovs0) m
          end
      | _, _, _, _, _, _ =>
          record_copyins [(msgp, Z.to_nat MSGHDR_SIZE)] (err_ret EFAULT)
          (* unreachable: the whole header read above; the arm is what
             Coq requires of a total match *)
      end
  end
  end.

(* =========================================================================
   socketpair (199), recvfrom (207), recvmsg (212)

   The three entry points that need no existing socket.  socketpair
   creates a pair and always fails for AF_INET, writing two descriptor
   numbers first; recvfrom and recvmsg resolve a descriptor that this
   model declines when it IS a socket.  What separates the two recv arms
   is ORDER: recvfrom validates its buffer before the descriptor,
   recvmsg resolves the descriptor before it reads the header.
   ========================================================================= *)

(** The descriptor gate of [__sys_recvfrom] (net/socket.c:2287-2291,
    Linux v6.18.46; [__sys_recvmsg]'s is :2920-2924; up to v6.12
    [sockfd_lookup_light] gave the same two answers, which v6.13 inlined
    through [CLASS(fd, f)]): -EBADF when
    the descriptor is not open, -ENOTSOCK when it is open and is not a
    socket.  Both recv-family arms end here.

    EVERY NON-SOCKET fd kind takes -ENOTSOCK, because [sock_from_file]
    returns NULL unless the file's [f_op] is [socket_file_ops].  The
    arms are written out rather than folded into a wildcard ON PURPOSE:
    a new [State.FdEntry] constructor must not inherit an answer by
    default, so adding one is a compile error here rather than a silent
    -ENOTSOCK.  A SOCKET is [None]: these two entry points decline it,
    for the reason [recvfrom_spec] gives. *)
Definition sockfd_lookup_errno (fds : list (word * FdEntry)) (fd : word)
    : option Z :=
  match fd_lookup fds fd with
  | None => Some EBADF
  | Some (FdChannel _) => Some ENOTSOCK
  | Some (FdFile _ _) => Some ENOTSOCK
  | Some (FdFileW _ _) => Some ENOTSOCK
  | Some (FdFileA _ _) => Some ENOTSOCK
  | Some (FdFileRW _ _) => Some ENOTSOCK
  | Some FdDir => Some ENOTSOCK
  | Some (FdPipe _ _) => Some ENOTSOCK
      (* The new constructor this comment's "must not inherit an answer
         by default" was written for, taking the answer EXPLICITLY:
         [sock_from_file] returns NULL unless [f_op] is
         [socket_file_ops], and a pipe end's is [pipeanon_fops]
         (fs/pipe.c [create_pipe_files], v6.18.46), so -ENOTSOCK is
         exact rather than inherited *)
  | Some (FdDevNull _ _) => Some ENOTSOCK
      (* and /dev/null's is [null_fops] (drivers/char/mem.c), so the
         same comparison fails and the same -ENOTSOCK is exact *)
  | Some FdUrandom => Some ENOTSOCK
      (* and /dev/urandom's is [urandom_fops] (drivers/char/random.c) *)
  | Some (FdSocket _) => None
  end.

(** That answer as a spec: the errno, or the decline a socket takes.
    [unmodeled] sits here as a WHOLE BRANCH and never under an [alt],
    which is what keeps [Ok] and [Unmodeled] from both being admissible
    at one input — the shape [check_syscall_complete_unmodeled] makes
    impossible. *)
Definition recv_fd_answer (fds : list (word * FdEntry)) (fd : word)
    : Sys SyscallEffect :=
  match sockfd_lookup_errno fds fd with
  | Some e => err_ret e
  | None => unmodeled
  end.

(* ---- socketpair (199) --------------------------------------------------- *)

(** [type] is an [int], so only its low 32 bits reach the kernel (see
    [Syscall.abi_low32]), and [Z.ldiff] is this file's spelling of C's
    [x & ~y] — the same two masks [socket_spec] clears with it, on the
    same field.  Clearing bits of a nonnegative value keeps it
    nonnegative, so these are the bits the kernel tests with none of C's
    sign extension to reproduce. *)
Definition socketpair_flags_ok (type : word) : bool :=
  Z.eqb (Z.ldiff (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
                 (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0.

(** The socket type after [type &= SOCK_TYPE_MASK] — what [sock_create]
    sees, and always in [0, 15]. *)
Definition socketpair_base_type (type : word) : Z :=
  Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK.

(** The (family, type, protocol) triples the model judges: AF_INET with
    SOCK_STREAM or SOCK_DGRAM at the default protocol.  Both reach
    [inet_create] and succeed there, so both arrive at
    [sock1->ops->socketpair] and both are the -EOPNOTSUPP below.

    Everything else is [unmodeled], and each exclusion is a kernel fact
    rather than a shrug.  AF_UNIX SUCCEEDS and would hand back a PAIR of
    sockets connected to each other, which [State.SockState] cannot
    express: its [SkConnected] names one peer and one channel, and
    nothing in it stands for a second socket in this same process on the
    other end.
    SOCK_RAW reaches [inet_create]'s CAP_NET_RAW test and so depends on
    the process's capabilities, which the model does not track.  A
    nonzero protocol reaches [inet_create]'s own range test and then its
    [inetsw] match, so it can answer -EINVAL or -EPROTONOSUPPORT, and a
    masked type outside [1, 3] can answer -EINVAL (type >= SOCK_MAX = 11)
    or -ESOCKTNOSUPPORT (type 0, whose [inetsw] list is empty) — all
    AFTER both writes have landed, so admitting them would mean modeling
    three more errnos for shapes no program issues. *)
Definition socketpair_modeled_b (family type protocol : word) : bool :=
  ((Z.eqb (bv_unsigned (abi_low32 family)) AF_INET)
   && (Z.eqb (socketpair_base_type type) SOCK_STREAM
       || Z.eqb (socketpair_base_type type) SOCK_DGRAM)
   && Z.eqb (bv_unsigned (abi_low32 protocol)) 0)%bool.

(** The two descriptors [__sys_socketpair] reserves, or [None] when
    [State.alloc_fd]'s scan bound is exhausted — the same unreachable
    case [Fs.File.lowest_fd]'s freeness conjunct exists for, answered by
    declining rather than by inventing a number.  Both are reserved
    before either is written, so the second is the lowest free
    descriptor ABOVE the first ([State.alloc_fd2]). *)
Definition socketpair_fds (fds : list (word * FdEntry)) : option (word * word) :=
  match fd_lookup fds (alloc_fd fds), fd_lookup fds (alloc_fd2 fds) with
  | None, None => Some (alloc_fd fds, alloc_fd2 fds)
  | _, _ => None
  end.

(** The two [put_user(fd, &usockvec[k])] stores: two separate 4-byte
    little-endian [int] writes, at [sv] and [sv + 4], in that order.
    Each is a single [sw] with an extable fixup on riscv64
    (arch/riscv/include/asm/uaccess.h), so an [int] write is
    all-or-nothing. *)
Definition socketpair_writes (sv fd1 fd2 : word) : list (word * list byte) :=
  [(sv, word_le4 fd1); (sv + Z_to_bv 64 4, word_le4 fd2)].

(** The errnos socketpair can return BEFORE either [put_user] runs, so
    with [usockvec] untouched: the two [get_unused_fd_flags] calls,
    which fail with -EMFILE past RLIMIT_NOFILE or sysctl_nr_open
    (fs/file.c [alloc_fd]) and with -ENOMEM on a failed fdtable
    expansion.  Neither condition is one this model tracks, so both are
    offered as environment choices, exactly as [Fs.Open.openat_errnos]
    is. *)
Definition socketpair_reserve_errnos : list Z := [EMFILE; ENOMEM].

(** The errnos it can return AFTER both writes have landed, for the
    modeled triples: -ENFILE when [sock_alloc] cannot take a sockfs
    inode ([__sock_create], net/socket.c) and -ENOMEM when [sk_alloc]
    fails inside [inet_create] (net/ipv4/af_inet.c).  They carry the
    writes, because the writes came first.

    Every other errno on that path is an ARGUMENT gate the modeled triple
    has already passed, EXCEPT the two LSM hooks:
    [security_socket_create] runs inside each [sock_create]
    ([__sock_create] calls it before [sock_alloc]) and
    [security_socket_socketpair] runs once both sockets exist, so an
    enforcing policy answers -EACCES with [usockvec] already written.
    This set does not admit that, which makes the model NARROWER than
    Linux here and never wider.

    THE -ENOMEM IS VERSION-DEPENDENT, and this is the value for the
    kernels this model covers.  [inet_create] sets [err = -ENOMEM]
    immediately before [sk_alloc] only from v5.14, where commit
    ca746c55a7e6 ("net: Return the correct errno code") replaced the
    -ENOBUFS that had stood there since well before v4.15; the stable
    branches that predate it — 4.19.y, 5.4.y and 5.10.y — still answer
    -ENOBUFS.  The modeled window is mainline v6.10 through v6.15 (see
    [Fs.ReadWrite.readv_spec]), entirely on the -ENOMEM side, so
    -ENOBUFS is out of scope here rather than an errno this set is
    missing. *)
Definition socketpair_create_errnos : list Z := [ENFILE; ENOMEM].

(** The outcome once the 8-byte destination is known writable: a
    reservation errno with [usockvec] untouched, or the two writes
    carrying -EOPNOTSUPP or one of the post-write errnos. *)
Definition socketpair_written (sv fd1 fd2 : word) : Sys SyscallEffect :=
  alt (e <- errno_from socketpair_reserve_errnos ;; err_ret e)
    (alt (e <- errno_from socketpair_create_errnos ;;
          pure (mkEffect (errno_ret e) (socketpair_writes sv fd1 fd2) []))
         (pure (mkEffect (errno_ret EOPNOTSUPP)
                         (socketpair_writes sv fd1 fd2) []))).

(** The outcome once the FIRST [put_user]'s own 4-byte range is one
    every riscv64 [access_ok] refuses: that store fails, so -EFAULT
    joins the two reservation errnos and nothing is written on any
    path. *)
Definition socketpair_faulted : Sys SyscallEffect :=
  alt (e <- errno_from socketpair_reserve_errnos ;; err_ret e) (err_ret EFAULT).

(** WHEN BOTH [put_user]s ARE KNOWN TO LAND: the whole 8-byte
    destination passes riscv64's own [access_ok] AND is mapped end to
    end.  Both conjuncts are needed and neither implies the other — a
    range [access_ok] accepts may have nothing mapped in it, and a
    range that reads back may be one [access_ok] refuses.

    THE FIRST CONJUNCT IS THE ONE WORTH EXPLAINING, because the walk
    below cannot stand alone.  [State.read_bytes_map] advances in WORD
    arithmetic and WRAPS at 2^64 (exactly as [State.read_bytes_aux], the
    shape its proofs use, steps [a + 1]), while
    the range test on the other branch sums
    [buf + count] in [Z].  So [sv] in the last seven bytes
    of the address space walks off the top, comes back at 0, and reads
    in full: at [sv = 2^64 - 4] the walk covers the four bytes below
    2^64 and the four at 0, answers
    [Some], and without the first conjunct the arm below would return
    [socketpair_written] with both descriptor numbers stored.  Linux answers -EFAULT there and
    writes nothing: [__sys_socketpair] runs
    [put_user(fd1, &usockvec[0])] before any [sock_create] (net/socket.c,
    [__sys_socketpair]; byte-identical v6.10 through the kernel of
    record, stable v6.18.46 / 1f99e9ab748f), and riscv64's [put_user] is
    [access_ok(p, sizeof *p) ? __put_user(x, p) : -EFAULT]
    (arch/riscv/include/asm/uaccess.h, [put_user]), whose test refuses
    [[2^64 - 4, 2^64)].  That last step is a statement about
    [pmlen = 0], for the reason [State.access_okb]'s note gives: riscv64's
    [access_ok] untags first, and a tagged address whose raw range wraps
    can untag to one that does not.
    Nothing in this model raises [pmlen].  So the walk alone gives a WRONG ANSWER
    and not a decline.  Nothing upstream constrains
    [sv]: [socketpair_flags_ok] and [socketpair_modeled_b] read only
    [family], [type] and [protocol].

    [State.access_okb] is the model's transcription of [__access_ok],
    [(size <= TASK_SIZE) && (addr <= TASK_SIZE - size)]
    (include/asm-generic/access_ok.h, [__access_ok]).  That is the
    predicate the range question goes through on this architecture:
    riscv64 overrides [access_ok] and not [__access_ok]
    (arch/riscv/include/asm/uaccess.h, [access_ok]).  It is written as a
    SUBTRACTION, so the wrapping sum is never formed, and its limit is
    the kernel of record's [TASK_SIZE] ([State.TASK_SIZE]).
    [Checks.Cases.Uaccess] argues at length why the kernel's predicate
    rather than a bare no-wrap test, and the second witness there —
    [2^63] with a count of 8, which does NOT wrap and which [access_ok]
    refuses anyway — applies here unchanged.

    THE WIDTH IS 8, NOT 4, AND THAT IS NOT THE 4 BELOW.  This conjunct
    guards the arm that says BOTH stores landed, so it must be the
    conjunction of both stores' own [access_ok] calls.  That it IS that
    conjunction is [access_okb_both_stores] below rather than a sentence
    here, because it is a universally quantified claim about
    [State.access_okb] and three sample addresses cannot settle one.

    What the lemma buys is the step the wrap makes non-obvious.
    [&usockvec[1]] is [sv + 4] in WORD arithmetic, in Linux as in
    [socketpair_writes], so [access_okb (sv + 4) 4] ON ITS OWN is TRUE
    for a wrapping [sv]: at [sv = 2^64 - 4] the second store's address
    is 0, which every [access_ok] accepts.  What rules the wrap out is
    the FIRST store's test, and the lemma says the two together leave
    exactly [access_okb sv 8].  It inherits that predicate's scope:
    where [State.access_okb] parts company with the kernel of record,
    both stores part company with it together and this conjunct stays
    exactly their conjunction.

    The 4 in the [else] branch answers a DIFFERENT question — whether
    the FIRST store is refused — and the band between them, [sv] in
    [[TASK_SIZE - 7, TASK_SIZE - 4]], is where the first store passes
    its own [access_ok] and the second is refused: Linux answers -EFAULT
    with [fd1] written if that top page is mapped and nothing written if
    it is not (it need not be: the stack ends at [STACK_TOP - rnd]), a
    PARTIAL outcome
    this model does not express, so it declines there. *)
(** WHY AT THE CALLER.
    The wrapping shape belongs to [State.read_bytes_map] and the range test
    rather than to any caller, and a
    caller-side repair has to be paid for on each arm and again in the
    checker and the witness: the guard
    below is spelled three times, here and in [Checks.Sys] and in
    [Checks.Witness].

    It is still the right place for it.  The definition-level fix is a
    fourth [IMAGE_WF] conjunct bounding a segment's extent, which
    this tree does
    not have, because it changes what [Equivalence.strong_universal]
    quantifies over.  Without it the choice is not "caller or
    definition" but "caller or leave a wrong answer standing", and the
    zero-delivery arms make the same choice: they put
    [access_okb] in front.  Spelling it the same way here is also what
    keeps a later definition-level fix cheap. *)
Definition socketpair_dest_writable (mp : word -> option byte) (sv : word)
    : bool :=
  (access_okb sv 8
   && match read_bytes_map mp sv (Z_to_bv 64 8) with
      | Some _ => true
      | None => false
      end)%bool.

(** THE WIDTH, AS A CHECK.  The two [put_user]s carry separate
    [access_ok] calls over their own 4-byte ranges, at [sv] and at the
    WORD sum [sv + 4]; [access_okb sv 8] is their conjunction at every
    [sv], the wrapping ones included.  Holds for any limit in
    [[8, 2^64)], so it survives a change to [State.TASK_SIZE]. *)
Lemma access_okb_both_stores (sv : word) :
  (access_okb sv 4 && access_okb (sv + Z_to_bv 64 4) 4)%bool
  = access_okb sv 8.
Proof.
  pose proof (bv_unsigned_in_range 64 sv) as [Hlo Hhi].
  unfold access_okb.
  destruct (Z.leb_spec (bv_unsigned sv) (TASK_SIZE - 4)) as [H4|H4];
    cbn [andb].
  - (* the first store passes, so [sv + 4] cannot have wrapped *)
    rewrite bv_add_unsigned, Z_to_bv_unsigned by lia.
    unfold bv_wrap, bv_modulus. cbn.
    rewrite Z.mod_small by (unfold TASK_SIZE in *; lia).
    destruct (Z.leb_spec (bv_unsigned sv + 4) (TASK_SIZE - 4));
      destruct (Z.leb_spec (bv_unsigned sv) (TASK_SIZE - 8));
      cbn; lia || reflexivity.
  - (* the first store is refused, and so is the 8-byte range *)
    destruct (Z.leb_spec (bv_unsigned sv) (TASK_SIZE - 8));
      [lia|reflexivity].
Qed.

(** [socketpair family type protocol usockvec].

    THE WHOLE POINT: for AF_INET this call ALWAYS FAILS, and it writes
    two descriptor numbers into [usockvec] before it does.
    [inet_stream_ops], [inet_dgram_ops] and [inet_sockraw_ops] all set
    [.socketpair = sock_no_socketpair] (net/ipv4/af_inet.c), and
    [sock_no_socketpair] (net/core/sock.c) is [return -EOPNOTSUPP;].
    [__sys_socketpair] reaches it only after
    [put_user(fd1, &usockvec[0])] and [put_user(fd2, &usockvec[1])] have
    both run, and its [out:] label then does [put_unused_fd] on both —
    so the call returns -EOPNOTSUPP with two CLOSED descriptor numbers
    already stored in the caller's array. *)
Definition socketpair_spec (family type protocol sv : word) : Sys SyscallEffect :=
  if negb (socketpair_flags_ok type) then err_ret EINVAL
  else if negb (socketpair_modeled_b family type protocol) then unmodeled
  else
  i <- input ;;
  m <- get_model ;;
  match socketpair_fds (m_fds m) with
  | None => unmodeled   (* [State.alloc_fd]'s scan bound exhausted: fail closed *)
  | Some (fd1, fd2) =>
      if socketpair_dest_writable (in_wmem i) sv
      then socketpair_written sv fd1 fd2
      else
        (* 4, NOT 8: the two [put_user]s carry SEPARATE [access_ok]
           calls over their own 4-byte ranges, so only the FIRST one's
           range being refused proves nothing was written.  At
           [sv = TASK_SIZE - 5] the 8-byte test fails while the first
           store's own range, ending at [TASK_SIZE - 1], passes: Linux
           answers -EFAULT, having stored [fd1] there if the top page is
           mapped and nothing if it is not — a PARTIAL outcome this model
           does not express either way, so the arm declines rather than
           guesses.  Gating on 4 leaves exactly
           that band, [[TASK_SIZE - 7, TASK_SIZE - 4]], [unmodeled]; the
           4 test IMPLIES the 8 test, so this arm answers a strict
           subset of the ranges it would otherwise — a narrowing, in the
           fail-closed direction.  At or above [TASK_SIZE - 3] the FIRST
           store is refused and -EFAULT with nothing written is right;
           the wrapping ranges are all in there, since a wrap needs
           [sv >= 2^64 - 7].

           The same branch is where a destination that is NOT wholly
           mapped arrives.  There too the model cannot rule out a
           partial write — the first page writable and the second not —
           and declines. *)
        if negb (access_okb sv 4) then socketpair_faulted
        else unmodeled   (* destination neither known-writable nor known-refused *)
  end.

(* ---- recvfrom (207) ----------------------------------------------------- *)

(** [recvfrom fd ubuf size flags src_addr addrlen].

    [__sys_recvfrom] (net/socket.c, Linux v5.10..v6.12 — the import
    helper was spelled [import_single_range] before v6.8, with the same
    prologue) opens with

      err = import_ubuf(ITER_DEST, ubuf, size, &msg.msg_iter);
      if (unlikely(err)) return err;
      sock = sockfd_lookup_light(fd, &err, &fput_needed);

    so THE BUFFER IS VALIDATED BEFORE THE DESCRIPTOR IS RESOLVED, and
    [recvfrom(-1, <kernel address>, 1, 0, NULL, NULL)] is -EFAULT rather
    than -EBADF.  That order is the whole content of this arm, and it is
    the opposite of [recvmsg]'s.

    THE OTHER THREE ARGUMENTS ARE NOT READ, and that is a kernel fact
    rather than an omission: [__sys_recvfrom] validates no flag at all
    (it has no [forbid_cmsg_compat] parameter and no equivalent test),
    and [src_addr]/[addrlen] are touched only by the [move_addr_to_user]
    at the very end, under [err >= 0 && addr != NULL] — unreachable when
    the descriptor is not a socket.  So MSG_PEEK, MSG_WAITALL,
    MSG_DONTWAIT and a non-NULL [src_addr] change nothing here, and the
    model reads none of them.  They become live the moment an fd kind is
    a socket, and the exhaustive match in [sockfd_lookup_errno] is what
    makes that a compile error rather than a silent inheritance.

    THE ARM IS DECIDED IN ADVANCE, AND IT IS [unmodeled] — and the
    reason belongs here, where whoever writes it will be reading, because
    a bare decline reads as a bigger claim than it is.  It declines the
    recvfrom/recvmsg ENTRY POINTS on a socket.  It does NOT say socket
    reading is unmodeled: [read] and [readv] on a connected socket are
    modeled, so a program that reads its socket the way dropbear reads
    its own — with [read], not [recv] — stays inside the surface.  And
    nothing real is shut out by it: dropbear calls none of [recvfrom],
    [recvmsg] or [socketpair], and the one caller that would, musl's DNS
    resolver (src/network/res_msend.c, through getaddrinfo), is already
    out of reach a step earlier: it opens its socket with
    [socket(AF_INET, SOCK_DGRAM|SOCK_CLOEXEC|SOCK_NONBLOCK, 0)] (:123,
    and AF_INET6 first where configured), and [socket_spec] declines
    SOCK_DGRAM.  So the
    resolver never obtains the descriptor it would call [recvmsg] on,
    and the decline costs [modeled] nothing a modeled program does.

    AND IT IS NOT [read]'s ARM, which is what makes that a real piece of
    work rather than an alias.  [sock_read_iter] (net/socket.c) opens
    with [if (!iov_iter_count(to)) return 0;] — "Match SYS5 behaviour" —
    so a zero-length [read] on a socket is 0 without reaching the
    protocol.  [__sys_recvfrom] has no such short-circuit, and the loop
    in [tcp_recvmsg_locked] (net/ipv4/tcp.c) does not exit early for a
    zero length either, because [sock_rcvlowat] (include/net/sock.h)
    ends [return v ?: 1;] — its [target] is 1 even at [len = 0], so a
    never-connected socket falls to the [TCP_CLOSE] arm's -ENOTCONN.
    [read(s, buf, 0)] is 0 where [recv(s, buf, 0, 0)] is -ENOTCONN, on
    the same socket in the same state.  Copying [read]'s socket arm here
    would get that backwards.

    [import_ubuf] clamps [size] to MAX_RW_COUNT (0x7ffff000) BEFORE its
    [access_ok], so an oversized count is never -EINVAL.  The clamp is
    invisible inside the modeled band: [Uaccess.modeled_rw_count]
    declines above [Uaccess.rw_bytes_max] = 2^17 for the reason given
    there, and 2^17 is far below MAX_RW_COUNT, so no modeled call is
    ever clamped.

    The buffer verdict is [Uaccess.access_ok_zero], which is exactly
    right for a call that moves no bytes: [import_ubuf]'s [access_ok]
    and nothing else. *)
Definition recvfrom_spec (fd buf size : word) : Sys SyscallEffect :=
  if negb (modeled_rw_count size) then unmodeled   (* see [Uaccess.rw_bytes_max] *)
  else
  i <- input ;;
  m <- get_model ;;
  access_ok_zero buf size (recv_fd_answer (m_fds m) fd).

(* ---- recvmsg (212) ------------------------------------------------------ *)

(** [recvmsg fd msg flags].

    [__sys_recvmsg] (net/socket.c, byte-identical v4.19..v6.12) is

      if (forbid_cmsg_compat && (flags & MSG_CMSG_COMPAT))
              return -EINVAL;
      sock = sockfd_lookup_light(fd, &err, &fput_needed);
      if (!sock) goto out;
      err = ___sys_recvmsg(sock, msg, &msg_sys, flags, 0);

    and [SYSCALL_DEFINE3(recvmsg, ...)] passes [forbid_cmsg_compat =
    true].  THE DESCRIPTOR IS RESOLVED BEFORE THE MESSAGE HEADER IS READ
    — [copy_msghdr_from_user] lives inside [___sys_recvmsg] — so
    [recvmsg(-1, <kernel address>, 0)] is -EBADF and
    [recvmsg(<open file>, <kernel address>, 0)] is -ENOTSOCK, with the
    56-byte [struct user_msghdr] never touched.  This model therefore
    does not read the [msg] pointer at all, and the dispatcher does not
    even bind it.

    Compare [recvfrom_spec], which imports its buffer first.  The two
    orders are opposite, and the pair of them is what these arms state.

    MSG_CMSG_COMPAT IS [unmodeled], AND THE REASON IS THE SAME ONE
    [access_ok] HAS.  The macro is [0x80000000] when CONFIG_COMPAT is
    set and [0] when it is not, so on a riscv64 kernel built with rv32
    emulation [recvmsg(fd, msg, 0x80000000)] is -EINVAL, and on one
    built without it the bit is inert and the call goes on to the
    descriptor.  Nothing a binary can observe says which kernel it is
    running on, so the model declines rather than picking one.  The
    bit is tested against the low 32 bits, since [flags] is an
    [unsigned int] (see [Syscall.abi_low32]).

    [msg_control], [msg_iovlen] and the iovec array behind [msg_iov] are
    all read by [copy_msghdr_from_user], which is downstream of the
    descriptor and so unreachable here.  Their validation — -EINVAL for
    a negative [msg_namelen], -EMSGSIZE past UIO_MAXIOV, the
    [import_iovec] errors — becomes live with the first socket fd kind,
    and so does the write-back of [msg_namelen], [msg_flags] and
    [msg_controllen] that a successful recvmsg performs.  musl's DNS
    resolver depends on two of those.  The socket arm here is [unmodeled]
    when it lands — for the reason [recvfrom_spec] gives, which applies
    to this entry point equally. *)
Definition recvmsg_spec (fd flags : word) : Sys SyscallEffect :=
  if negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags)) MSG_CMSG_COMPAT) 0)
  then unmodeled   (* CONFIG_COMPAT decides this one: fail closed *)
  else
  m <- get_model ;;
  recv_fd_answer (m_fds m) fd.
