(** * LinuxProcessSem.Checks.Sys.Net.Socket — the socket (198), bind (200),
      listen (201), accept (202), getsockname (204), getpeername (205),
      sendto (206), setsockopt (208), getsockopt (209), shutdown (210),
      sendmsg (211), accept4 (242) checkers, and their proofs

    Mirrors [Sys/Net/Socket.v], which answers to Linux [net/socket.c]:
    this file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Uaccess Fs.Open Fs.ReadWrite.

(** The other socket shape: an injected errno, or a fixed return with a
    new fd table.  [bind] and [listen] both use it, and both return 0, so
    the success return can never be mistaken for an errno; the
    completeness lemma below takes that as a hypothesis and each call
    site discharges it by evaluation. *)

Definition check_errno_or_success (es : list Z)
    (fds : list (word * FdEntry)) (r : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in es ret then CheckOk m []
      else if bv_eqb ret r then CheckOk (with_fds fds m) [] else CheckReject
  | _ => CheckReject
  end.

(** The acceptor for an [alt] whose SUCCESS SIDE ADMITS NOTHING, leaving
    the injected errno as the only outcome.  [accept] reaches it once
    [Net.Socket.conn_ix_exhausted] holds: the spec's success branch is
    [choose (fun _ => False)] there, so a returned descriptor is not
    admissible however it was allocated.  Note it is not
    [check_new_fd_result] with an empty [mk] — that would still accept
    [alloc_fd]'s value. *)
Definition check_errno_only (es : list Z) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in es ret then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

(** [check_errno_only] is exact for such an [alt].  The
    [choose (fun _ => False)] is what makes all three hold: it
    contributes no [Ok] and, being a [choose] rather than [unmodeled], no
    [Unmodeled] either. *)
Lemma check_errno_only_no_unmodeled : forall es eff m,
  check_errno_only es eff m <> CheckUnmodeled.
Proof.
  intros es eff m. unfold check_errno_only.
  destruct eff as [ret ws zs us cs copyins];
    destruct ws; destruct zs; destruct us; destruct cs; destruct copyins;
    try discriminate.
  destruct (errno_ret_in es ret); discriminate.
Qed.

Lemma check_errno_only_sound_ok : forall es (i : SyscallInput) eff m m' evs,
  check_errno_only es eff m = CheckOk m' evs ->
  alt (e <- errno_from es ;; err_ret e) (choose (fun _ => False))
      i m (Ok eff m' evs).
Proof.
  intros es i eff m m' evs H. unfold check_errno_only in H.
  destruct eff as [ret ws zs us cs copyins];
    destruct ws; destruct zs; destruct us; destruct cs; destruct copyins;
    try discriminate.
  destruct (errno_ret_in es ret) eqn:He; [|discriminate].
  inversion H; clear H; subst.
  apply errno_ret_in_true in He. destruct He as (er & HIn & ->).
  apply alt_l. eapply bind_ok0; [apply (choose_ok _ er); exact HIn|].
  apply pure_ok.
Qed.

Lemma check_errno_only_complete_ok : forall es (i : SyscallInput) eff m m' evs,
  alt (e <- errno_from es ;; err_ret e) (choose (fun _ => False))
      i m (Ok eff m' evs) ->
  check_errno_only es eff m = CheckOk m' evs.
Proof.
  intros es i eff m m' evs [Herr | Hno].
  - destruct Herr as (e & m1 & evs1 & evs2 & Hch & Hret & ->).
    unfold errno_from, choose in Hch.
    destruct Hch as (x & HIn & Heq). inversion Heq; clear Heq; subst.
    unfold err_ret, ret_only, pure in Hret. inversion Hret; clear Hret; subst.
    unfold check_errno_only. rewrite (errno_ret_in_intro _ _ HIn). reflexivity.
  - unfold choose in Hno. destruct Hno as (? & [] & _).
Qed.

(** The acceptor for an [alt] of ONE FIXED ERRNO and an INJECTED LIST:
    the shape [socket_spec] and [accept4_spec] take where a refusal of
    Linux's stands beside the allocation errnos that precede it
    ([Net.Socket.accept_notsock_errnos] and its neighbour, ported from
    main LPS #1536 `7cce061164`).  Neither side declines, so this
    acceptor never answers [CheckUnmodeled]. *)
Definition check_errno_or_list (e0 : Z) (es : list Z) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if orb (bv_eqb ret (errno_ret e0)) (errno_ret_in es ret)
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

Lemma check_errno_or_list_no_unmodeled : forall e0 es eff m,
  check_errno_or_list e0 es eff m <> CheckUnmodeled.
Proof.
  intros e0 es eff m. unfold check_errno_or_list.
  destruct eff as [ret ws zs us cs copyins];
    destruct ws; destruct zs; destruct us; destruct cs; destruct copyins;
    try discriminate.
  destruct (orb (bv_eqb ret (errno_ret e0)) (errno_ret_in es ret)); discriminate.
Qed.

Lemma check_errno_or_list_sound_ok :
  forall e0 es (i : SyscallInput) eff m m' evs,
  check_errno_or_list e0 es eff m = CheckOk m' evs ->
  alt (err_ret e0) (er <- errno_from es ;; err_ret er) i m (Ok eff m' evs).
Proof.
  intros e0 es i eff m m' evs H. unfold check_errno_or_list in H.
  destruct eff as [ret ws zs us cs copyins];
    destruct ws; destruct zs; destruct us; destruct cs; destruct copyins;
    try discriminate.
  destruct (bv_eqb ret (errno_ret e0)) eqn:He0; cbn [orb] in H.
  - inversion H; clear H; subst.
    apply bv_eqb_eq in He0. subst ret.
    apply alt_l. unfold err_ret, ret_only. apply pure_ok.
  - destruct (errno_ret_in es ret) eqn:He; [|discriminate].
    inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (er & HIn & ->).
    apply alt_r. eapply bind_ok0; [apply (choose_ok _ er); exact HIn|].
    unfold err_ret, ret_only. apply pure_ok.
Qed.

Lemma check_errno_or_list_e0 : forall e0 es m,
  check_errno_or_list e0 es (mkEffect (errno_ret e0) [] []) m = CheckOk m [].
Proof.
  intros e0 es m. unfold check_errno_or_list. cbn [eff_ret].
  rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma check_errno_or_list_in : forall e0 es e m,
  In e es -> check_errno_or_list e0 es (mkEffect (errno_ret e) [] []) m = CheckOk m [].
Proof.
  intros e0 es e m HIn. unfold check_errno_or_list. cbn [eff_ret].
  rewrite (errno_ret_in_intro _ _ HIn), orb_true_r. reflexivity.
Qed.

Lemma check_errno_or_list_complete_ok :
  forall e0 es (i : SyscallInput) eff m m' evs,
  alt (err_ret e0) (er <- errno_from es ;; err_ret er) i m (Ok eff m' evs) ->
  check_errno_or_list e0 es eff m = CheckOk m' evs.
Proof.
  intros e0 es i eff m m' evs [Hfix | Herr].
  - unfold err_ret, ret_only, pure in Hfix. inversion Hfix; clear Hfix; subst.
    unfold check_errno_or_list. cbn. rewrite bv_eqb_refl. reflexivity.
  - destruct Herr as (e & m1 & evs1 & evs2 & Hch & Hret & ->).
    unfold errno_from, choose in Hch.
    destruct Hch as (x & HIn & Heq). inversion Heq; clear Heq; subst.
    unfold err_ret, ret_only, pure in Hret. inversion Hret; clear Hret; subst.
    unfold check_errno_or_list. cbn.
    rewrite (errno_ret_in_intro _ _ HIn), orb_true_r. reflexivity.
Qed.

(** Every family's set is injectable: no member can be mistaken for the
    allocated descriptor. *)
Lemma socket_dgram_errnos_ok : forall fam,
  errnos_ok (socket_dgram_errnos fam) = true.
Proof.
  intros fam. unfold socket_dgram_errnos. destruct (Z.eqb fam AF_INET6); reflexivity.
Qed.

(** socket(2).  Every test is a pure function of the arguments and they
    are made in the kernel's order, because the order is what decides
    which errno a doubly-bad call gets; see [Net.Socket.socket_spec].
    The datagram shapes ([Net.Socket.socket_dgram_b]: AF_INET6 or
    AF_UNIX, SOCK_DGRAM, protocol 0) mint a [State.FdDgram] through the
    same fresh-descriptor acceptor the AF_INET stream arm uses, with
    the family's own errno set ([Net.Socket.socket_dgram_errnos]:
    AF_INET6 adds [inet6_create]'s -ENOBUFS). *)

Definition check_socket (domain type protocol : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  let tu := bv_unsigned (abi_low32 type) in
  let flagbits := Z.ldiff tu SOCK_TYPE_MASK in
  if negb (Z.eqb (Z.ldiff flagbits (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (Z.eqb (Z.land flagbits SOCK_NONBLOCK) 0)
  then CheckUnmodeled                    (* SOCK_NONBLOCK: no O_NONBLOCK notion *)
  else
    let ty  := Z.land tu SOCK_TYPE_MASK in
    let fam := sint32 domain in
    let pro := sint32 protocol in
    if orb (Z.ltb fam 0) (Z.leb NPROTO fam)
    then check_ret_only eff (errno_ret EAFNOSUPPORT) m []
    else if Z.leb SOCK_MAX ty then check_ret_only eff (errno_ret EINVAL) m []
    else if socket_dgram_b fam ty pro then
      check_new_fd_result (socket_dgram_errnos fam) eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd (FdDgram fam)) m)
    else if negb (Z.eqb fam AF_INET) then CheckUnmodeled
    else if Z.eqb ty SOCK_PACKET then CheckUnmodeled
      (* above the protocol range: __sock_create rewrites the family to
         PF_PACKET, so inet_create's IPPROTO_MAX check never runs — see
         [Net.Socket.socket_spec] *)
    else if orb (Z.ltb pro 0) (Z.leb IPPROTO_MAX pro)
    then check_errno_or_list EINVAL socket_alloc_errnos eff m
    else if Z.eqb ty SOCK_STREAM then
      if orb (Z.eqb pro IPPROTO_SCTP) (Z.eqb pro IPPROTO_MPTCP) then CheckUnmodeled
      else if negb (orb (Z.eqb pro IPPROTO_IP) (Z.eqb pro IPPROTO_TCP))
      then check_errno_or_list EPROTONOSUPPORT socket_alloc_errnos eff m
      else
        check_new_fd_result socket_errnos eff m
          (fun fd => with_fds (fd_insert (m_fds m) fd (FdSocket SkFresh)) m)
    else if orb (Z.eqb ty SOCK_DGRAM) (Z.eqb ty SOCK_RAW)
    then CheckUnmodeled                  (* SOCK_DGRAM / SOCK_RAW; SOCK_PACKET is above *)
    else if orb (Z.eqb ty SOCK_SEQPACKET) (Z.eqb ty SOCK_DCCP)
    then CheckUnmodeled                  (* sctp and dccp register these *)
    else check_errno_or_list ESOCKTNOSUPPORT socket_alloc_errnos eff m.

(** bind(2).  -EFAULT precedes the 16-byte minimum, which is why the
    address bytes are read before their length is judged against
    [SOCKADDR_IN_SIZE]. *)

Definition check_bind (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdSocket sk) =>
      let al := sint32 addrlen in
      if orb (Z.ltb al 0) (Z.ltb SOCKADDR_STORAGE_SIZE al)
      then check_ret_only eff (errno_ret EINVAL) m []
      else if Z.eqb al 0 then check_ret_only eff (errno_ret EINVAL) m []
      else
      match copy_bytes_map (in_mem i) addrp al with
      | None => check_ret_only eff (errno_ret EFAULT) m []
      | Some bs =>
          (* PAST THE COPY, and that is where the ledger starts.
             [move_addr_to_kernel] has really moved [al] bytes out of user
             memory by the time any of the arms below runs, so each of them
             expects [eff_copyins] to be exactly [(addrp, al)], while every
             arm ABOVE expects it empty: the two [addrlen]-range -EINVALs
             return before the copy is attempted and the -EFAULT arm is the
             copy FAILING, which transfers nothing.  This mirrors
             [Net.Socket.bind_spec]'s [record_copyins], and it is what makes
             the ledger discriminate rather than decorate — the two -EINVALs
             differ in nothing else. *)
          if Z.ltb al SOCKADDR_IN_SIZE
          then check_ret_only_copyins [(addrp, Z.to_nat al)] eff
                 (errno_ret EINVAL) m []
          else
            let fam  := sa_family_of bs in
            let port := sin_port_of bs in
            let a    := sin_addr_of bs in
            if negb (orb (Z.eqb fam AF_INET)
                         (andb (Z.eqb fam AF_UNSPEC) (Z.eqb a INADDR_ANY)))
            then check_ret_only_copyins [(addrp, Z.to_nat al)] eff
                   (errno_ret EAFNOSUPPORT) m []
            else if negb (Z.eqb a INADDR_ANY) then CheckUnmodeled
            else if negb (Z.eqb port 0) then CheckUnmodeled
              (* a specific address or port needs tables a one-process
                 model does not have; decline rather than guess.  No ledger
                 test here: an [Unmodeled] carries no effect at all, so
                 there is nothing for a ledger to be right or wrong about *)
            else
              match sk with
              | SkFresh =>
                  (* [check_errno_or_success] has no copy-in variant of its
                     own, and giving it one would duplicate [check_copyins]
                     for a single call site.  So the ledger is tested here
                     and the arm's own acceptor sees the effect with the
                     ledger stripped, which is exactly what
                     [check_ret_only_copyins] does internally. *)
                  check_copyins [(addrp, Z.to_nat al)] eff
                    (check_errno_or_success bind_errnos
                       (fd_insert (m_fds m) fd (FdSocket SkBound))
                       (Z_to_bv 64 0) (clear_copyins eff) m)
              | SkBound | SkListening
              | SkConnected _ _ (NCons _ _) | SkConnected _ _ NFin =>
                  check_ret_only_copyins [(addrp, Z.to_nat al)] eff
                    (errno_ret EINVAL) m []
              | SkConnected _ _ NRst | SkConnected _ _ NTimedOut
              | SkReset _ _ => CheckUnmodeled
                  (* a reset connection is unbound again and Linux
                     autobinds: see [Net.Socket.bind_spec] *)
              end
      end
  | Some (FdStream _ _ _) => CheckUnmodeled
      (* a stream-pair end is a socket: [unix_bind] parses a
         [sockaddr_un], which the model does not carry *)
  | Some (FdDgram _) => CheckUnmodeled
      (* a datagram socket is a socket too: [unix_bind] / [inet6_bind]
         claim an address [State.FdDgram] does not carry *)
  | Some _ => check_ret_only eff (errno_ret ENOTSOCK) m []
  end.

(** listen(2).  The backlog is only clamped, never refused, and nothing
    observes the clamped value. *)

Definition check_listen (fd backlog : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  let _ := backlog in
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdSocket sk) =>
      match sk with
      | SkConnected _ _ _ => check_ret_only eff (errno_ret EINVAL) m []
      | SkReset _ _ => check_ret_only eff (errno_ret EINVAL) m []
      | SkListening => check_ret_only eff (Z_to_bv 64 0) m []
      | SkBound =>
          check_ret_only eff (Z_to_bv 64 0)
            (with_fds (fd_insert (m_fds m) fd (FdSocket SkListening)) m) []
      | SkFresh =>
          (* the only arm that autobinds, and so the only one whose
             [get_port] can fail *)
          check_errno_or_success listen_errnos
            (fd_insert (m_fds m) fd (FdSocket SkListening))
            (Z_to_bv 64 0) eff m
      end
  | Some (FdStream _ _ _) => check_ret_only eff (errno_ret EINVAL) m []
      (* [unix_listen] on an unbound pair end *)
  | Some (FdDgram _) => CheckUnmodeled   (* a socket: [sock_no_listen], declined *)
  | Some _ => check_ret_only eff (errno_ret ENOTSOCK) m []
  end.

(** accept4(2), which accept(2) reaches with [flags = 0].  -EBADF comes
    before the flags are even looked at; the connection is taken off the
    environment's queue only on the success arm. *)

Definition check_accept4 (fd addrp addrlenp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let _ := addrlenp in                   (* untouched while [addrp] is NULL *)
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some e =>
      let fl := bv_unsigned (abi_low32 flags) in
      if negb (Z.eqb (Z.ldiff fl (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)
      then check_ret_only eff (errno_ret EINVAL) m []
      else if negb (Z.eqb (Z.land fl SOCK_NONBLOCK) 0) then CheckUnmodeled
      else
      match e with
      | FdSocket sk =>
          if negb (w_is0 addrp) then CheckUnmodeled
            (* [SyscallEffect] cannot express the write of the peer
               address; see [Net.Socket.accept4_spec] *)
          else
          match sk with
          | SkListening =>
              if conn_ix_exhausted (m_conn_ix m)
              then check_errno_only accept_errnos eff m
              else
              check_new_fd_result accept_errnos eff m
                (fun nfd =>
                   with_accepted
                     (fd_insert (m_fds m) nfd
                        (FdSocket (SkConnected (nq_peer (m_net m))
                                               (conn_channel (m_conn_ix m))
                                               (nq_script (m_net m))))) m)
          | _ => check_errno_or_list EINVAL accept_notlisten_errnos eff m
          end
      | FdStream _ _ _ => CheckUnmodeled   (* a socket: [unix_accept]'s allocations *)
      | FdDgram _ => CheckUnmodeled        (* a socket: [sock_no_accept], declined *)
      | _ => if negb (Z.ltb (bv_unsigned (alloc_fd (m_fds m))) NR_OPEN_DEFAULT)
             then CheckUnmodeled
             else check_errno_or_list ENOTSOCK accept_notsock_errnos eff m
      end
  end.

(** connect(2).  The arm order is NOT bind's: the address is copied
    before the file is resolved to a socket, so -ENOTSOCK sits BELOW the
    copy and carries its ledger, while -EBADF, the addrlen -EINVAL and
    -EFAULT sit above it and carry none.  See
    [Net.Socket.connect_spec]. *)

Definition check_connect (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some e =>
      let al := sint32 addrlen in
      if orb (Z.ltb al 0) (Z.ltb SOCKADDR_STORAGE_SIZE al)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      match move_addr_bytes (in_mem i) addrp al with
      | None => check_ret_only eff (errno_ret EFAULT) m []
      | Some bs =>
          let copied := if Z.eqb al 0 then [] else [(addrp, length bs)] in
          match e with
          | FdSocket sk =>
              if Z.ltb al SA_FAMILY_SIZE
              then check_ret_only_copyins copied eff (errno_ret EINVAL) m []
              else if Z.eqb (sa_family_of bs) AF_UNSPEC then
                match sk with
                | SkFresh =>
                    check_ret_only_copyins copied eff (Z_to_bv 64 0) m []
                | SkBound | SkListening
                | SkConnected _ _ _ | SkReset _ _ => CheckUnmodeled
                end
              else
                match sk with
                | SkListening | SkConnected _ _ _ | SkReset _ _ =>
                    check_ret_only_copyins copied eff (errno_ret EISCONN) m []
                | SkFresh | SkBound =>
                    if Z.ltb al SOCKADDR_IN_SIZE
                    then check_ret_only_copyins copied eff (errno_ret EINVAL) m []
                    else if negb (Z.eqb (sa_family_of bs) AF_INET)
                    then check_ret_only_copyins copied eff (errno_ret EAFNOSUPPORT) m []
                    else CheckUnmodeled
                end
          | FdStream _ _ _ => CheckUnmodeled   (* [unix_stream_connect]: a name lookup *)
          | FdDgram _ => CheckUnmodeled        (* a peer [State.FdDgram] does not carry *)
          | _ => check_ret_only_copyins copied eff (errno_ret ENOTSOCK) m []
          end
      end
  end.

(* --------------------------------------------------- errno-or-success *)

Lemma check_errno_or_success_sound_ok : forall es fds r i eff m m' evs,
  check_errno_or_success es fds r eff m = CheckOk m' evs ->
  alt (e <- errno_from es ;; err_ret e)
      (set_fds fds ;; ret_only r) i m (Ok eff m' evs).
Proof.
  intros es fds r i eff m m' evs H.
  unfold check_errno_or_success in H.
  destruct eff as [ret ws zs us cs copyins];
    destruct ws; destruct zs; destruct us; destruct cs; destruct copyins;
    try discriminate.
  destruct (errno_ret_in es ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
    apply pure_ok.
  - destruct (bv_eqb ret r) eqn:Hr; [|discriminate].
    apply bv_eqb_eq in Hr; subst r. inversion H; clear H; subst.
    apply alt_r. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_errno_or_success_no_unmodeled : forall es fds r eff m,
  check_errno_or_success es fds r eff m <> CheckUnmodeled.
Proof.
  intros es fds r eff m. unfold check_errno_or_success.
  destruct eff as [ret ws zs us cs copyins];
    destruct ws; destruct zs; destruct us; destruct cs; destruct copyins;
    try discriminate.
  destruct (errno_ret_in es ret); [discriminate|].
  destruct (bv_eqb ret r); discriminate.
Qed.

(** The success return must not read as one of the injectable errnos, or
    the errno arm would swallow it and report the wrong model.  Both call
    sites return 0 and discharge this by evaluation. *)

Lemma check_errno_or_success_complete_ok : forall es fds r i eff m m' evs,
  errno_ret_in es r = false ->
  alt (e <- errno_from es ;; err_ret e)
      (set_fds fds ;; ret_only r) i m (Ok eff m' evs) ->
  check_errno_or_success es fds r eff m = CheckOk m' evs.
Proof.
  intros es fds r i eff m m' evs Hne H. destruct H as [Herr|Hok].
  - sys_unfold. cbv beta iota zeta in Herr. inv_ok.
    unfold check_errno_or_success.
    match goal with
    | |- context [errno_ret_in ?es0 (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es0 e) by assumption
    end.
    reflexivity.
  - sys_unfold. cbv beta iota zeta in Hok. inv_ok.
    unfold check_errno_or_success. rewrite Hne, bv_eqb_refl. reflexivity.
Qed.

Lemma errno_or_success_no_unmodeled : forall es fds r i m,
  ~ alt (e <- errno_from es ;; err_ret e)
        (set_fds fds ;; ret_only r) i m Unmodeled.
Proof.
  intros es fds r i m H. destruct H as [H|H];
    sys_unfold; cbv beta iota zeta in H; inv_ok.
Qed.

(** The premise is unsatisfiable, so the conclusion is free. *)

Lemma check_errno_or_success_complete_unmodeled : forall es fds r i m eff,
  alt (e <- errno_from es ;; err_ret e)
      (set_fds fds ;; ret_only r) i m Unmodeled ->
  check_errno_or_success es fds r eff m = CheckUnmodeled.
Proof.
  intros es fds r i m eff H.
  exfalso. eapply errno_or_success_no_unmodeled; exact H.
Qed.

(* ---------------------------------------------------------------- socket *)

Lemma check_socket_sound_ok : forall domain type protocol eff m m' evs i,
  check_socket domain type protocol eff m = CheckOk m' evs ->
  socket_spec domain type protocol i m (Ok eff m' evs).
Proof.
  intros domain type protocol eff m m' evs i H.
  unfold check_socket in H. unfold socket_spec.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  cbv zeta in H.
  destruct (negb (Z.eqb (Z.ldiff (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0))
    eqn:E1; cbv beta iota zeta in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (negb (Z.eqb (Z.land (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_NONBLOCK) 0)) eqn:E2;
    cbv beta iota zeta in H |- *; [discriminate|].
  destruct (orb (Z.ltb (sint32 domain) 0) (Z.leb NPROTO (sint32 domain))) eqn:E3;
    cbv beta iota zeta in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (Z.leb SOCK_MAX (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)) eqn:E4;
    cbv beta iota zeta in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (socket_dgram_b (sint32 domain)
              (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
              (sint32 protocol)) eqn:Edg;
    cbv beta iota zeta in H |- *.
  { (* a datagram socket: the injected failure, or the lowest free fd *)
    unfold check_new_fd_result in H.
    destruct eff as [ret ws zs us cs copyins]; destruct ws as [|w ws'];
      destruct zs as [|z zs']; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
    destruct (errno_ret_in (socket_dgram_errnos (sint32 domain)) ret) eqn:He.
    - inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
      apply pure_ok.
    - destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
      destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
      inversion H; clear H; subst. apply bv_eqb_eq in Heq.
      apply alt_r.
      eapply bind_ok0; [apply (choose_ok _ ret); split; assumption|].
      cbv beta. eapply bind_ok0; [apply modify_ok|]. apply pure_ok. }
  destruct (negb (Z.eqb (sint32 domain) AF_INET)) eqn:E5;
    cbv beta iota zeta in H |- *; [discriminate|].
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_PACKET) eqn:E5p;
    cbv beta iota zeta in H |- *; [discriminate|].
  destruct (orb (Z.ltb (sint32 protocol) 0)
                (Z.leb IPPROTO_MAX (sint32 protocol))) eqn:E6;
    cbv beta iota zeta in H |- *.
  { eapply check_errno_or_list_sound_ok; exact H. }
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_STREAM) eqn:E7;
    cbv beta iota zeta in H |- *.
  - destruct (orb (Z.eqb (sint32 protocol) IPPROTO_SCTP)
                  (Z.eqb (sint32 protocol) IPPROTO_MPTCP)) eqn:E7s;
      cbv beta iota zeta in H |- *.
    { discriminate. }
    destruct (negb (orb (Z.eqb (sint32 protocol) IPPROTO_IP)
                        (Z.eqb (sint32 protocol) IPPROTO_TCP))) eqn:E7a;
      cbv beta iota zeta in H |- *.
    { eapply check_errno_or_list_sound_ok; exact H. }
    (* the injected failure, or the lowest free fd *)
    unfold check_new_fd_result in H.
    destruct eff as [ret ws zs us cs copyins]; destruct ws as [|w ws'];
      destruct zs as [|z zs']; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
    destruct (errno_ret_in socket_errnos ret) eqn:He.
    + inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
      apply pure_ok.
    + destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
      destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
      inversion H; clear H; subst. apply bv_eqb_eq in Heq.
      apply alt_r.
      eapply bind_ok0; [apply (choose_ok _ ret); split; assumption|].
      cbv beta. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DGRAM)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_RAW)) eqn:E8;
      cbv beta iota zeta in H |- *; [discriminate|].
    destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_SEQPACKET)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DCCP)) eqn:E8b;
      cbv beta iota zeta in H |- *; [discriminate|].
    eapply check_errno_or_list_sound_ok; exact H.
Qed.

Lemma check_socket_sound_unmodeled : forall domain type protocol eff m i,
  check_socket domain type protocol eff m = CheckUnmodeled ->
  socket_spec domain type protocol i m Unmodeled.
Proof.
  intros domain type protocol eff m i H.
  unfold check_socket in H. unfold socket_spec.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
  cbv zeta in H.
  destruct (negb (Z.eqb (Z.ldiff (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0))
    eqn:E1; cbv beta iota zeta in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (Z.eqb (Z.land (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_NONBLOCK) 0)) eqn:E2;
    cbv beta iota zeta in H |- *; [apply unmodeled_intro|].
  destruct (orb (Z.ltb (sint32 domain) 0) (Z.leb NPROTO (sint32 domain))) eqn:E3;
    cbv beta iota zeta in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (Z.leb SOCK_MAX (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)) eqn:E4;
    cbv beta iota zeta in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (socket_dgram_b (sint32 domain)
              (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
              (sint32 protocol)) eqn:Edg;
    cbv beta iota zeta in H |- *.
  { now apply check_new_fd_result_no_unmodeled in H. }
  destruct (negb (Z.eqb (sint32 domain) AF_INET)) eqn:E5;
    cbv beta iota zeta in H |- *; [apply unmodeled_intro|].
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_PACKET) eqn:E5p;
    cbv beta iota zeta in H |- *; [apply unmodeled_intro|].
  destruct (orb (Z.ltb (sint32 protocol) 0)
                (Z.leb IPPROTO_MAX (sint32 protocol))) eqn:E6;
    cbv beta iota zeta in H |- *.
  { now apply check_errno_or_list_no_unmodeled in H. }
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_STREAM) eqn:E7;
    cbv beta iota zeta in H |- *.
  - destruct (orb (Z.eqb (sint32 protocol) IPPROTO_SCTP)
                  (Z.eqb (sint32 protocol) IPPROTO_MPTCP)) eqn:E7s;
      cbv beta iota zeta in H |- *.
    { apply unmodeled_intro. }
    destruct (negb (orb (Z.eqb (sint32 protocol) IPPROTO_IP)
                        (Z.eqb (sint32 protocol) IPPROTO_TCP))) eqn:E7a;
      cbv beta iota zeta in H |- *.
    { now apply check_errno_or_list_no_unmodeled in H. }
    now apply check_new_fd_result_no_unmodeled in H.
  - destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DGRAM)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_RAW)) eqn:E8;
      cbv beta iota zeta in H |- *; [apply unmodeled_intro|].
    destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_SEQPACKET)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DCCP)) eqn:E8b;
      cbv beta iota zeta in H |- *; [apply unmodeled_intro|].
    now apply check_errno_or_list_no_unmodeled in H.
Qed.

Lemma check_socket_complete_ok : forall domain type protocol eff m m' evs i,
  socket_spec domain type protocol i m (Ok eff m' evs) ->
  check_socket domain type protocol eff m = CheckOk m' evs.
Proof.
  intros domain type protocol eff m m' evs i H.
  unfold socket_spec in H. unfold check_socket. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (negb (Z.eqb (Z.ldiff (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0))
    eqn:E1; hall E1; inv_ok.
  { cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (negb (Z.eqb (Z.land (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_NONBLOCK) 0)) eqn:E2;
    hall E2; inv_ok.
  destruct (orb (Z.ltb (sint32 domain) 0) (Z.leb NPROTO (sint32 domain))) eqn:E3;
    hall E3; inv_ok.
  { cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (Z.leb SOCK_MAX (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)) eqn:E4;
    hall E4; inv_ok.
  { cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (socket_dgram_b (sint32 domain)
              (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
              (sint32 protocol)) eqn:Edg; hall Edg.
  { inv_ok.
    - (* a datagram socket's injected failure *)
      unfold check_new_fd_result.
      match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    - (* a datagram socket at the lowest free fd *)
      unfold check_new_fd_result.
      rewrite errno_ret_in_alloc_fd by apply socket_dgram_errnos_ok.
      match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
      rewrite bv_eqb_refl. reflexivity. }
  inv_ok.
  destruct (negb (Z.eqb (sint32 domain) AF_INET)) eqn:E5; hall E5; inv_ok.
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_PACKET) eqn:E5p;
    hall E5p; inv_ok.
  destruct (orb (Z.ltb (sint32 protocol) 0)
                (Z.leb IPPROTO_MAX (sint32 protocol))) eqn:E6; hall E6; inv_ok.
  2:{ apply check_errno_or_list_in. cbn. auto. }
  { apply check_errno_or_list_e0. }
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_STREAM) eqn:E7;
    hall E7; inv_ok.
  - destruct (orb (Z.eqb (sint32 protocol) IPPROTO_SCTP)
                  (Z.eqb (sint32 protocol) IPPROTO_MPTCP)) eqn:E7s; hall E7s; inv_ok.
    destruct (negb (orb (Z.eqb (sint32 protocol) IPPROTO_IP)
                        (Z.eqb (sint32 protocol) IPPROTO_TCP))) eqn:E7a;
      hall E7a; inv_ok.
    2:{ apply check_errno_or_list_in. cbn. auto. }
    { apply check_errno_or_list_e0. }
    + (* injected failure *)
      unfold check_new_fd_result.
      match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    + (* success: the lowest free fd *)
      unfold check_new_fd_result.
      rewrite errno_ret_in_alloc_fd by reflexivity.
      match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
      rewrite bv_eqb_refl. reflexivity.
  - destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DGRAM)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_RAW)) eqn:E8;
      hall E8; inv_ok.
    destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_SEQPACKET)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DCCP)) eqn:E8b;
      hall E8b; inv_ok.
    2:{ apply check_errno_or_list_in. cbn. auto. }
    apply check_errno_or_list_e0.
Qed.

Lemma check_socket_complete_unmodeled : forall domain type protocol m i eff,
  socket_spec domain type protocol i m Unmodeled ->
  check_socket domain type protocol eff m = CheckUnmodeled.
Proof.
  intros domain type protocol m i eff H.
  unfold socket_spec in H. unfold check_socket. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (negb (Z.eqb (Z.ldiff (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0))
    eqn:E1; hall E1; inv_ok; try discriminate.
  destruct (negb (Z.eqb (Z.land (Z.ldiff (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_NONBLOCK) 0)) eqn:E2;
    hall E2; inv_ok; try discriminate; [reflexivity|].
  destruct (orb (Z.ltb (sint32 domain) 0) (Z.leb NPROTO (sint32 domain))) eqn:E3;
    hall E3; inv_ok; try discriminate.
  destruct (Z.leb SOCK_MAX (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)) eqn:E4;
    hall E4; inv_ok; try discriminate.
  destruct (socket_dgram_b (sint32 domain)
              (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK)
              (sint32 protocol)) eqn:Edg; hall Edg; inv_ok; try discriminate.
  destruct (negb (Z.eqb (sint32 domain) AF_INET)) eqn:E5; hall E5; inv_ok;
    try discriminate; [reflexivity|].
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_PACKET) eqn:E5p;
    hall E5p; inv_ok; try discriminate; [reflexivity|].
  destruct (orb (Z.ltb (sint32 protocol) 0)
                (Z.leb IPPROTO_MAX (sint32 protocol))) eqn:E6; hall E6; inv_ok;
    try discriminate.
  destruct (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_STREAM) eqn:E7;
    hall E7; inv_ok.
  - destruct (orb (Z.eqb (sint32 protocol) IPPROTO_SCTP)
                  (Z.eqb (sint32 protocol) IPPROTO_MPTCP)) eqn:E7s; hall E7s; inv_ok.
    { reflexivity. }
    destruct (negb (orb (Z.eqb (sint32 protocol) IPPROTO_IP)
                        (Z.eqb (sint32 protocol) IPPROTO_TCP))) eqn:E7a;
      hall E7a; inv_ok; discriminate.
  - destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DGRAM)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_RAW)) eqn:E8;
      hall E8; inv_ok; try discriminate; try reflexivity.
    destruct (orb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_SEQPACKET)
                  (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_TYPE_MASK) SOCK_DCCP)) eqn:E8b;
      hall E8b; inv_ok; try discriminate; reflexivity.
Qed.

(* ------------------------------------------------------------------ bind *)

(** The ledger bridge both [bind] directions need.  [record_copyins]
    APPENDS its ranges to whatever the wrapped spec already recorded; on
    every arm reached here the wrapped spec records nothing, so an
    observed effect is admissible exactly when its own ledger is the
    recorded range and the rest of it is what the arm produced.  Stated
    over [clear_copyins] so the arm's acceptor never has to know about
    the ledger. *)
Local Lemma record_copyins_of_cleared :
  forall reads (spec : Sys SyscallEffect) i m eff m' evs,
  eff_copyins eff = reads ->
  spec i m (Ok (clear_copyins eff) m' evs) ->
  record_copyins reads spec i m (Ok eff m' evs).
Proof.
  intros reads spec i m eff m' evs Hr H.
  replace eff with
    (with_copyins (reads ++ eff_copyins (clear_copyins eff)) (clear_copyins eff)).
  - now apply record_copyins_ok.
  - unfold clear_copyins, with_copyins.
    destruct eff as [ret ws zs us cs cis]; cbn in Hr |- *.
    rewrite app_nil_r, Hr. reflexivity.
Qed.

(** The other direction of the same bridge, for the completeness proofs:
    an effect whose ledger is the recorded range passes the test, so what
    is left to decide is the arm's own answer. *)
Local Lemma check_copyins_same : forall reads eff res,
  eff_copyins eff = reads -> check_copyins reads eff res = res.
Proof.
  intros reads eff res H. unfold check_copyins.
  rewrite H, (proj2 (access_ranges_eqb_eq reads reads) eq_refl). reflexivity.
Qed.

(** The goal a declined arm leaves on BOTH sides of a completeness proof
    for [CheckUnmodeled], closed only where it is literally that, so a
    [try] of it can never touch an arm still being taken apart. *)
Local Ltac unm_refl :=
  match goal with |- CheckUnmodeled = CheckUnmodeled => reflexivity end.


Lemma check_bind_sound_ok : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs ->
  bind_spec fd addrp addrlen i m (Ok eff m' evs).
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_bind in H. unfold bind_spec. cbv zeta in H.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *; try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         apply pure_ok).
  (* the socket arm *)
  destruct (orb (Z.ltb (sint32 addrlen) 0)
                (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
    cbv beta iota zeta in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (Z.eqb (sint32 addrlen) 0) eqn:E2; cbv beta iota zeta in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (copy_bytes_map (in_mem i) addrp (sint32 addrlen))
    as [bs|] eqn:Hrb; cbv beta iota zeta in H |- *.
  2: { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE) eqn:E3;
    cbv beta iota zeta in H |- *.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok. apply pure_ok. }
  destruct (negb (orb (Z.eqb (sa_family_of bs) AF_INET)
                      (andb (Z.eqb (sa_family_of bs) AF_UNSPEC)
                            (Z.eqb (sin_addr_of bs) INADDR_ANY)))) eqn:E4;
    cbv beta iota zeta in H |- *.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok. apply pure_ok. }
  destruct (negb (Z.eqb (sin_addr_of bs) INADDR_ANY)) eqn:E5;
    cbv beta iota zeta in H |- *; [discriminate|].
  destruct (negb (Z.eqb (sin_port_of bs) 0)) eqn:E6;
    cbv beta iota zeta in H |- *; [discriminate|].
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *.
  - (* fresh: the ledger, then the arm's acceptor on the stripped effect *)
    unfold check_copyins in H.
    destruct (access_ranges_eqb (eff_copyins eff)
                [(addrp, Z.to_nat (sint32 addrlen))]) eqn:Hr; [|discriminate].
    apply access_ranges_eqb_eq in Hr.
    apply record_copyins_of_cleared; [exact Hr|].
    now apply check_errno_or_success_sound_ok.
  - apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->);
      apply record_copyins_ok; apply pure_ok.
  - apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->);
      apply record_copyins_ok; apply pure_ok.
  - destruct rx; cbv beta iota zeta in H |- *; try discriminate;
      (apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->);
       apply record_copyins_ok; apply pure_ok).
  - discriminate.
Qed.

Lemma check_bind_sound_unmodeled : forall i fd addrp addrlen eff m,
  check_bind i fd addrp addrlen eff m = CheckUnmodeled ->
  bind_spec fd addrp addrlen i m Unmodeled.
Proof.
  intros i fd addrp addrlen eff m H.
  unfold check_bind in H. unfold bind_spec. cbv zeta in H.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *;
    try (now apply check_ret_only_no_unmodeled in H); try apply unmodeled_intro.
  destruct (orb (Z.ltb (sint32 addrlen) 0)
                (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
    cbv beta iota zeta in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (Z.eqb (sint32 addrlen) 0) eqn:E2; cbv beta iota zeta in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (copy_bytes_map (in_mem i) addrp (sint32 addrlen))
    as [bs|] eqn:Hrb; cbv beta iota zeta in H |- *.
  2: { now apply check_ret_only_no_unmodeled in H. }
  destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE) eqn:E3;
    cbv beta iota zeta in H |- *.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (negb (orb (Z.eqb (sa_family_of bs) AF_INET)
                      (andb (Z.eqb (sa_family_of bs) AF_UNSPEC)
                            (Z.eqb (sin_addr_of bs) INADDR_ANY)))) eqn:E4;
    cbv beta iota zeta in H |- *.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (negb (Z.eqb (sin_addr_of bs) INADDR_ANY)) eqn:E5;
    cbv beta iota zeta in H |- *;
    [apply record_copyins_unmodeled; apply unmodeled_intro|].
  destruct (negb (Z.eqb (sin_port_of bs) 0)) eqn:E6;
    cbv beta iota zeta in H |- *;
    [apply record_copyins_unmodeled; apply unmodeled_intro|].
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *.
  - unfold check_copyins in H.
    destruct (access_ranges_eqb (eff_copyins eff)
                [(addrp, Z.to_nat (sint32 addrlen))]); [|discriminate].
    now apply check_errno_or_success_no_unmodeled in H.
  - now apply check_ret_only_copyins_no_unmodeled in H.
  - now apply check_ret_only_copyins_no_unmodeled in H.
  - destruct rx; cbv beta iota zeta in H |- *;
      solve [ now apply check_ret_only_copyins_no_unmodeled in H
            | apply record_copyins_unmodeled; apply unmodeled_intro ].
  - apply record_copyins_unmodeled; apply unmodeled_intro.
Qed.

Lemma check_bind_complete_ok : forall i fd addrp addrlen eff m m' evs,
  bind_spec fd addrp addrlen i m (Ok eff m' evs) ->
  check_bind i fd addrp addrlen eff m = CheckOk m' evs.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold bind_spec in H. unfold check_bind. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok;
    try (cbn; try rewrite bv_eqb_refl; reflexivity).
  destruct (orb (Z.ltb (sint32 addrlen) 0)
                (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
    hall E1; inv_ok; [cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (Z.eqb (sint32 addrlen) 0) eqn:E2; hall E2; inv_ok;
    [cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (copy_bytes_map (in_mem i) addrp (sint32 addrlen))
    as [bs|] eqn:Hrb; hall Hrb; inv_ok;
    [|cbn; try rewrite bv_eqb_refl; reflexivity].
  destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE) eqn:E3; hall E3; inv_ok;
    [apply check_ret_only_copyins_ok_iff; now repeat split|].
  destruct (negb (orb (Z.eqb (sa_family_of bs) AF_INET)
                      (andb (Z.eqb (sa_family_of bs) AF_UNSPEC)
                            (Z.eqb (sin_addr_of bs) INADDR_ANY)))) eqn:E4;
    hall E4; inv_ok;
    [apply check_ret_only_copyins_ok_iff; now repeat split|].
  destruct (negb (Z.eqb (sin_addr_of bs) INADDR_ANY)) eqn:E5; hall E5; inv_ok.
  destruct (negb (Z.eqb (sin_port_of bs) 0)) eqn:E6; hall E6; inv_ok.
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *.
  2-3: (inv_ok; apply check_ret_only_copyins_ok_iff; now repeat split).
  3: (inv_ok; apply check_ret_only_copyins_ok_iff; now repeat split).
  2: (destruct rx; cbv beta iota zeta in *;
      inv_ok; apply check_ret_only_copyins_ok_iff; now repeat split).
  (* FRESH: the ledger is tested on the observed effect and the arm's own
     acceptor sees it stripped.  Both branches of the [alt] record nothing
     of their own, so the observed ledger is exactly the recorded range;
     that is what [check_copyins_same] needs, and it is only true once the
     branch is known, which is why the [alt] is split here. *)
  match goal with H : _ \/ _ |- _ => destruct H as [Herr|Hok] end; inv_ok;
    erewrite check_copyins_same by reflexivity;
    unfold check_errno_or_success, clear_copyins, with_copyins;
    cbn -[errno_ret_in errno_ret bind_errnos Z_to_bv bv_eqb].
  - (* the injected -EADDRINUSE *)
    match goal with
    | Hin : In _ bind_errnos |- _ => rewrite (errno_ret_in_intro _ _ Hin)
    end.
    reflexivity.
  - (* the bind that succeeded: 0 is not one of the injectable errnos *)
    replace (errno_ret_in bind_errnos (Z_to_bv 64 0)) with false
      by (vm_compute; reflexivity).
    rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma check_bind_complete_unmodeled : forall i fd addrp addrlen m eff,
  bind_spec fd addrp addrlen i m Unmodeled ->
  check_bind i fd addrp addrlen eff m = CheckUnmodeled.
Proof.
  intros i fd addrp addrlen m eff H.
  unfold bind_spec in H. unfold check_bind. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok; try discriminate; try unm_refl.
  destruct (orb (Z.ltb (sint32 addrlen) 0)
                (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
    hall E1; inv_ok; try discriminate.
  destruct (Z.eqb (sint32 addrlen) 0) eqn:E2; hall E2; inv_ok; try discriminate.
  destruct (copy_bytes_map (in_mem i) addrp (sint32 addrlen))
    as [bs|] eqn:Hrb; hall Hrb; inv_ok; try discriminate.
  destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE) eqn:E3; hall E3; inv_ok;
    try discriminate.
  destruct (negb (orb (Z.eqb (sa_family_of bs) AF_INET)
                      (andb (Z.eqb (sa_family_of bs) AF_UNSPEC)
                            (Z.eqb (sin_addr_of bs) INADDR_ANY)))) eqn:E4;
    hall E4; inv_ok; try discriminate.
  destruct (negb (Z.eqb (sin_addr_of bs) INADDR_ANY)) eqn:E5; hall E5; inv_ok;
    [reflexivity|].
  destruct (negb (Z.eqb (sin_port_of bs) 0)) eqn:E6; hall E6; inv_ok;
    [reflexivity|].
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *.
  2-3: (inv_ok; discriminate).
  3: reflexivity.
  2: (destruct rx; cbv beta iota zeta in *;
      solve [ inv_ok; discriminate | reflexivity ]).
  (* fresh: the [alt] admits no [Unmodeled] outcome, so the premise is
     unsatisfiable and the ledger never comes into it *)
  exfalso. inv_ok.
Qed.

(* ---------------------------------------------------------------- listen *)

Lemma check_listen_sound_ok : forall fd backlog eff m m' evs i,
  check_listen fd backlog eff m = CheckOk m' evs ->
  listen_spec fd backlog i m (Ok eff m' evs).
Proof.
  intros fd backlog eff m m' evs i H.
  unfold check_listen in H. unfold listen_spec. cbv zeta in H.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *; try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         apply pure_ok).
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *.
  - (* fresh: the autobind can fail with -EADDRINUSE *)
    now apply check_errno_or_success_sound_ok.
  - (* bound: [get_port] cannot fail *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - (* re-listen: the backlog only *)
    apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
Qed.

Lemma check_listen_sound_unmodeled : forall fd backlog eff m i,
  check_listen fd backlog eff m = CheckUnmodeled ->
  listen_spec fd backlog i m Unmodeled.
Proof.
  intros fd backlog eff m i H.
  unfold check_listen in H. unfold listen_spec. cbv zeta in H.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *;
    try (now apply check_ret_only_no_unmodeled in H);
    try apply unmodeled_intro.
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H;
    try (now apply check_ret_only_no_unmodeled in H).
  now apply check_errno_or_success_no_unmodeled in H.
Qed.

Lemma check_listen_complete_ok : forall fd backlog eff m m' evs i,
  listen_spec fd backlog i m (Ok eff m' evs) ->
  check_listen fd backlog eff m = CheckOk m' evs.
Proof.
  intros fd backlog eff m m' evs i H.
  unfold listen_spec in H. unfold check_listen. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok;
    try (cbn; try rewrite bv_eqb_refl; reflexivity).
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *.
  2-5: (inv_ok; cbn; try rewrite bv_eqb_refl; reflexivity).
  eapply (check_errno_or_success_complete_ok _ _ _ i);
    [vm_compute; reflexivity|eassumption].
Qed.

Lemma check_listen_complete_unmodeled : forall fd backlog m i eff,
  listen_spec fd backlog i m Unmodeled ->
  check_listen fd backlog eff m = CheckUnmodeled.
Proof.
  intros fd backlog m i eff H.
  unfold listen_spec in H. unfold check_listen. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok; try discriminate; try unm_refl.
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *.
  2-5: (inv_ok; discriminate).
  eapply (check_errno_or_success_complete_unmodeled _ _ _ i); eassumption.
Qed.

(* --------------------------------------------------------------- accept4 *)

Lemma check_accept4_sound_ok : forall fd addrp addrlenp flags eff m m' evs i,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs ->
  accept4_spec fd addrp addrlenp flags i m (Ok eff m' evs).
Proof.
  intros fd addrp addrlenp flags eff m m' evs i H.
  unfold check_accept4 in H. unfold accept4_spec. cbv zeta in H.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd;
    cbv beta iota zeta in H |- *.
  2: { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 flags))
                                 (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)) eqn:E1;
    cbv beta iota zeta in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags))
                                SOCK_NONBLOCK) 0)) eqn:E2;
    cbv beta iota zeta in H |- *; [discriminate|].
  destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af];
    cbv beta iota zeta in H |- *; try discriminate;
    try (destruct (negb (Z.ltb (bv_unsigned (alloc_fd (m_fds m))) NR_OPEN_DEFAULT));
         [discriminate | now apply check_errno_or_list_sound_ok]).
  destruct (negb (w_is0 addrp)) eqn:E3; cbv beta iota zeta in H |- *;
    [discriminate|].
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
    try (now apply check_errno_or_list_sound_ok).
  (* listening: the injected failure, or the connection at the head of the
     environment's queue -- and once the channel space is used up, the
     failure alone (see [Net.Socket.conn_ix_exhausted]) *)
  destruct (conn_ix_exhausted (m_conn_ix m)) eqn:Hex;
    cbv beta iota zeta in H |- *.
  { now apply check_errno_only_sound_ok. }
  unfold check_new_fd_result in H.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|w ws'];
    destruct zs as [|z zs']; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
  destruct (errno_ret_in accept_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (er & HIn & ->).
    apply alt_l. eapply bind_ok0; [apply (choose_ok _ er); exact HIn|].
    apply pure_ok.
  - destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
    destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq.
    apply alt_r.
    eapply bind_ok0; [apply (choose_ok _ ret); split; assumption|].
    cbv beta. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_accept4_sound_unmodeled : forall fd addrp addrlenp flags eff m i,
  check_accept4 fd addrp addrlenp flags eff m = CheckUnmodeled ->
  accept4_spec fd addrp addrlenp flags i m Unmodeled.
Proof.
  intros fd addrp addrlenp flags eff m i H.
  unfold check_accept4 in H. unfold accept4_spec. cbv zeta in H.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd;
    cbv beta iota zeta in H |- *.
  2: { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 flags))
                                 (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)) eqn:E1;
    cbv beta iota zeta in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags))
                                SOCK_NONBLOCK) 0)) eqn:E2;
    cbv beta iota zeta in H |- *; [apply unmodeled_intro|].
  destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af];
    cbv beta iota zeta in H |- *; try apply unmodeled_intro;
    try (destruct (negb (Z.ltb (bv_unsigned (alloc_fd (m_fds m))) NR_OPEN_DEFAULT))
           eqn:Ecap;
         [apply unmodeled_intro | now apply check_errno_or_list_no_unmodeled in H]).
  destruct (negb (w_is0 addrp)) eqn:E3; cbv beta iota zeta in H |- *;
    [apply unmodeled_intro|].
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
    try (now apply check_errno_or_list_no_unmodeled in H).
  destruct (conn_ix_exhausted (m_conn_ix m)) eqn:Hex;
    cbv beta iota zeta in H |- *.
  { now apply check_errno_only_no_unmodeled in H. }
  now apply check_new_fd_result_no_unmodeled in H.
Qed.

Lemma check_accept4_complete_ok : forall fd addrp addrlenp flags eff m m' evs i,
  accept4_spec fd addrp addrlenp flags i m (Ok eff m' evs) ->
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs.
Proof.
  intros fd addrp addrlenp flags eff m m' evs i H.
  unfold accept4_spec in H. unfold check_accept4. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    [|cbn; try rewrite bv_eqb_refl; reflexivity].
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 flags))
                                 (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)) eqn:E1;
    hall E1; inv_ok; [cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags))
                                SOCK_NONBLOCK) 0)) eqn:E2; hall E2; inv_ok.
  (* [cbn] must not reach the listening arm: that goal carries
     [alloc_fd]'s 4096-step fuel and [with_accepted], and normalising it
     costs gigabytes.  Select the arms that need it instead. *)
  destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af];
    cbv beta iota zeta in *; inv_ok.
  (* every non-socket kind, the pipe end (8), /dev/null (9), the eventfd
     (12) and the unnamed file (14) included, takes -ENOTSOCK; the
     stream-pair end (11) and the datagram socket (13) decline, so
     [inv_ok] has already closed them, and the eventfd and the unnamed
     file are the eleventh and twelfth goals left.
     THE INDICES MOVE WITH [State.FdEntry]: a constructor added ahead of
     [FdSocket] shifts every number here, and a stale selector silently
     addresses a different arm. *)
  1-6,8-12: (destruct (negb (Z.ltb (bv_unsigned (alloc_fd (m_fds m))) NR_OPEN_DEFAULT))
               eqn:Ecap; hall Ecap; inv_ok;
             [ apply check_errno_or_list_e0
             | apply check_errno_or_list_in; cbn; auto ]).
  destruct (negb (w_is0 addrp)) eqn:E3; hall E3; inv_ok.
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *.
  1-2,4-5: (inv_ok;
            [ apply check_errno_or_list_e0
            | apply check_errno_or_list_in; cbn; auto ]).
  destruct (conn_ix_exhausted (m_conn_ix m)) eqn:Hex;
    cbv beta iota zeta in *.
  { now apply (check_errno_only_complete_ok _ i). }
  inv_ok.
  - (* injected failure *)
    unfold check_new_fd_result.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - (* success: the lowest free fd, and one connection off the queue *)
    unfold check_new_fd_result.
    rewrite errno_ret_in_alloc_fd by reflexivity.
    match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
    rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma check_accept4_complete_unmodeled : forall fd addrp addrlenp flags m i eff,
  accept4_spec fd addrp addrlenp flags i m Unmodeled ->
  check_accept4 fd addrp addrlenp flags eff m = CheckUnmodeled.
Proof.
  intros fd addrp addrlenp flags m i eff H.
  unfold accept4_spec in H. unfold check_accept4. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    try discriminate.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 flags))
                                 (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK)) 0)) eqn:E1;
    hall E1; inv_ok; try discriminate.
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags))
                                SOCK_NONBLOCK) 0)) eqn:E2; hall E2; inv_ok;
    try discriminate; [reflexivity|].
  destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af];
    cbv beta iota zeta in *; inv_ok;
    try discriminate;
    try (destruct (negb (Z.ltb (bv_unsigned (alloc_fd (m_fds m))) NR_OPEN_DEFAULT))
           eqn:Ecap; hall Ecap; inv_ok; first [reflexivity | discriminate]).
  destruct (negb (w_is0 addrp)) eqn:E3; hall E3; inv_ok; try discriminate;
    [reflexivity|].
  destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *; inv_ok;
    try discriminate.
  destruct (conn_ix_exhausted (m_conn_ix m)) eqn:Hex;
    cbv beta iota zeta in *; inv_ok; discriminate.
Qed.

(* --------------------------------------------------------------- connect *)

Local Ltac connect_ret H :=
  apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->); apply pure_ok.
Local Ltac connect_ret_c H :=
  apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->);
  apply record_copyins_ok; apply pure_ok.

Lemma check_connect_sound_ok : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs ->
  connect_spec fd addrp addrlen i m (Ok eff m' evs).
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_connect in H. unfold connect_spec. cbv zeta in H.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *;
    [ | | | | | | | | | | | | | | connect_ret H ].
  all: destruct (orb (Z.ltb (sint32 addrlen) 0)
                     (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
       cbv beta iota zeta in H |- *; [ connect_ret H | ].
  all: destruct (move_addr_bytes (in_mem i) addrp (sint32 addrlen))
         as [bs|] eqn:Hrb; cbv beta iota zeta in H |- *; [ | connect_ret H ].
  all: destruct (Z.eqb (sint32 addrlen) 0) eqn:Ez;
       cbv beta iota zeta in H |- *.
  all: try connect_ret_c H.
  (* the stream-pair end and the datagram socket decline once past the copy *)
  all: try discriminate.
  (* the socket arm, both ledger shapes *)
  all: destruct (Z.ltb (sint32 addrlen) SA_FAMILY_SIZE) eqn:E3;
       cbv beta iota zeta in H |- *; [ connect_ret_c H | ].
  all: destruct (Z.eqb (sa_family_of bs) AF_UNSPEC) eqn:E4;
       cbv beta iota zeta in H |- *;
       destruct sk as [| | |peer ch rx|peer ch];
       cbv beta iota zeta in H |- *;
       try discriminate;
       try connect_ret_c H.
  all: destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE) eqn:E5;
       cbv beta iota zeta in H |- *; [ connect_ret_c H | ].
  all: destruct (negb (Z.eqb (sa_family_of bs) AF_INET)) eqn:E6;
       cbv beta iota zeta in H |- *; [ connect_ret_c H | discriminate ].
Qed.

Lemma check_connect_sound_unmodeled : forall i fd addrp addrlen eff m,
  check_connect i fd addrp addrlen eff m = CheckUnmodeled ->
  connect_spec fd addrp addrlen i m Unmodeled.
Proof.
  intros i fd addrp addrlen eff m H.
  unfold check_connect in H. unfold connect_spec. cbv zeta in H.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *;
    [ | | | | | | | | | | | | | | now apply check_ret_only_no_unmodeled in H ].
  all: destruct (orb (Z.ltb (sint32 addrlen) 0)
                     (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
       cbv beta iota zeta in H |- *;
       [ now apply check_ret_only_no_unmodeled in H | ].
  all: destruct (move_addr_bytes (in_mem i) addrp (sint32 addrlen))
         as [bs|] eqn:Hrb; cbv beta iota zeta in H |- *;
       [ | now apply check_ret_only_no_unmodeled in H ].
  all: destruct (Z.eqb (sint32 addrlen) 0) eqn:Ez;
       cbv beta iota zeta in H |- *.
  all: try (now apply check_ret_only_copyins_no_unmodeled in H).
  (* the stream-pair end and the datagram socket: declined past the copy,
     the ledger kept *)
  all: try (apply record_copyins_unmodeled; apply unmodeled_intro).
  all: destruct (Z.ltb (sint32 addrlen) SA_FAMILY_SIZE) eqn:E3;
       cbv beta iota zeta in H |- *;
       [ now apply check_ret_only_copyins_no_unmodeled in H | ].
  all: destruct (Z.eqb (sa_family_of bs) AF_UNSPEC) eqn:E4;
       cbv beta iota zeta in H |- *;
       destruct sk as [| | |peer ch rx|peer ch];
       cbv beta iota zeta in H |- *;
       try (now apply check_ret_only_copyins_no_unmodeled in H);
       try (apply record_copyins_unmodeled; apply unmodeled_intro).
  all: destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE) eqn:E5;
       cbv beta iota zeta in H |- *;
       [ now apply check_ret_only_copyins_no_unmodeled in H | ].
  all: destruct (negb (Z.eqb (sa_family_of bs) AF_INET)) eqn:E6;
       cbv beta iota zeta in H |- *;
       [ now apply check_ret_only_copyins_no_unmodeled in H
       | apply record_copyins_unmodeled; apply unmodeled_intro ].
Qed.

Lemma check_connect_complete_ok : forall i fd addrp addrlen eff m m' evs,
  connect_spec fd addrp addrlen i m (Ok eff m' evs) ->
  check_connect i fd addrp addrlen eff m = CheckOk m' evs.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold connect_spec in H. unfold check_connect. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok;
    [ | | | | | | | | | |
      (* the stream-pair end: past the copy the spec declines, so [inv_ok]
         closes that branch and only the two answers before it remain *)
      destruct (orb (Z.ltb (sint32 addrlen) 0)
                    (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
      hall E1; inv_ok; [ cbn; try rewrite bv_eqb_refl; reflexivity | ];
      destruct (move_addr_bytes (in_mem i) addrp (sint32 addrlen))
        as [bs|] eqn:Hrb; hall Hrb; inv_ok;
      cbn; try rewrite bv_eqb_refl; reflexivity
    |
    | (* the datagram socket: the same two answers, for the same reason *)
      destruct (orb (Z.ltb (sint32 addrlen) 0)
                    (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
      hall E1; inv_ok; [ cbn; try rewrite bv_eqb_refl; reflexivity | ];
      destruct (move_addr_bytes (in_mem i) addrp (sint32 addrlen))
        as [bs|] eqn:Hrb; hall Hrb; inv_ok;
      cbn; try rewrite bv_eqb_refl; reflexivity
    | (* the unnamed file: a non-socket kind, taken by the lines below *)
    | cbn; try rewrite bv_eqb_refl; reflexivity ].
  all: destruct (orb (Z.ltb (sint32 addrlen) 0)
                     (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
       hall E1; inv_ok; [ cbn; try rewrite bv_eqb_refl; reflexivity | ].
  all: destruct (move_addr_bytes (in_mem i) addrp (sint32 addrlen))
         as [bs|] eqn:Hrb; hall Hrb; inv_ok;
       [ | cbn; try rewrite bv_eqb_refl; reflexivity ].
  all: destruct (Z.eqb (sint32 addrlen) 0) eqn:Ez; hall Ez; inv_ok.
  all: try (apply check_ret_only_copyins_ok_iff; now repeat split).
  all: destruct (Z.ltb (sint32 addrlen) SA_FAMILY_SIZE) eqn:E3; hall E3; inv_ok;
       [ apply check_ret_only_copyins_ok_iff; now repeat split | ].
  all: destruct (Z.eqb (sa_family_of bs) AF_UNSPEC) eqn:E4; hall E4; inv_ok;
       destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *;
       inv_ok;
       try (apply check_ret_only_copyins_ok_iff; now repeat split).
  all: destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE) eqn:E5; hall E5; inv_ok;
       [ apply check_ret_only_copyins_ok_iff; now repeat split | ].
  all: destruct (negb (Z.eqb (sa_family_of bs) AF_INET)) eqn:E6; hall E6; inv_ok;
       apply check_ret_only_copyins_ok_iff; now repeat split.
Qed.

Lemma check_connect_complete_unmodeled : forall i fd addrp addrlen m eff,
  connect_spec fd addrp addrlen i m Unmodeled ->
  check_connect i fd addrp addrlen eff m = CheckUnmodeled.
Proof.
  intros i fd addrp addrlen m eff H.
  unfold connect_spec in H. unfold check_connect. sys_unfold.
  cbv iota zeta in H. cbv zeta. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok; try discriminate.
  all: destruct (orb (Z.ltb (sint32 addrlen) 0)
                     (Z.ltb SOCKADDR_STORAGE_SIZE (sint32 addrlen))) eqn:E1;
       hall E1; inv_ok; try discriminate.
  all: destruct (move_addr_bytes (in_mem i) addrp (sint32 addrlen))
         as [bs|] eqn:Hrb; hall Hrb; inv_ok; try discriminate.
  all: destruct (Z.eqb (sint32 addrlen) 0) eqn:Ez; hall Ez; inv_ok;
       try discriminate.
  (* the stream-pair end's and the datagram socket's decline, on both sides *)
  all: try unm_refl.
  all: destruct (Z.ltb (sint32 addrlen) SA_FAMILY_SIZE) eqn:E3; hall E3; inv_ok;
       try discriminate.
  all: destruct (Z.eqb (sa_family_of bs) AF_UNSPEC) eqn:E4; hall E4; inv_ok;
       destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in *;
       inv_ok; try discriminate; try reflexivity.
  all: destruct (Z.ltb (sint32 addrlen) SOCKADDR_IN_SIZE) eqn:E5; hall E5; inv_ok;
       try discriminate.
  all: destruct (negb (Z.eqb (sa_family_of bs) AF_INET)) eqn:E6; hall E6; inv_ok;
       try discriminate; reflexivity.
Qed.

(* ---------------------------------------------------------- socket calls *)

(** An effect that is a return, some stores and a copy-in ledger, and
    nothing else: the one shape every answer of a stream-pair end's
    address and option calls takes once the call has read user memory.
    [check_ret_only_copyins] is its special case with no stores. *)
Definition check_ret_writes_copyins (reads : list (word * nat))
    (eff : SyscallEffect) (r : word) (ws : list (word * list byte))
    (m' : Model) : check_result :=
  match eff with
  | mkEffectU ret ws' [] [] [] cis =>
      if bv_eqb ret r && writes_eqb ws' ws && access_ranges_eqb cis reads
      then CheckOk m' [] else CheckReject
  | _ => CheckReject
  end.

Lemma check_ret_writes_copyins_ok_iff : forall reads eff r ws m1 m' evs,
  check_ret_writes_copyins reads eff r ws m1 = CheckOk m' evs <->
  (eff = with_copyins reads (mkEffect r ws []) /\ m' = m1 /\ evs = []).
Proof.
  intros reads [ret ws' zs us cs cis] r ws m1 m' evs.
  unfold check_ret_writes_copyins, with_copyins.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
  destruct zs as [|z zs]; [destruct us as [|u us]; [destruct cs as [|c cs]|]|];
    cbv beta iota;
    try (split; [discriminate|intros (H1 & _ & _); discriminate H1]).
  destruct (bv_eqb ret r && writes_eqb ws' ws && access_ranges_eqb cis reads) eqn:E.
  - apply andb_true_iff in E as [E Ek]. apply andb_true_iff in E as [Er Ew].
    apply bv_eqb_eq in Er. apply writes_eqb_eq in Ew.
    apply access_ranges_eqb_eq in Ek. subst.
    split; [intro H; inversion H; auto|intros (_ & -> & ->); reflexivity].
  - split; [discriminate|]. intros (H1 & _ & _). inversion H1; subst.
    rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl),
      access_ranges_eqb_refl in E.
    discriminate.
Qed.

Lemma check_ret_writes_copyins_no_unmodeled : forall reads eff r ws m1,
  check_ret_writes_copyins reads eff r ws m1 <> CheckUnmodeled.
Proof.
  intros reads [ret ws' zs us cs cis] r ws m1. unfold check_ret_writes_copyins.
  destruct zs; [destruct us; [destruct cs|]|]; cbv beta iota; try discriminate.
  destruct (bv_eqb ret r && writes_eqb ws' ws && access_ranges_eqb cis reads);
    discriminate.
Qed.

(** [record_copyins] nested: the outer range comes first in the ledger,
    the inner one after it, and the arm inside records nothing.  The shape
    a stream-pair end's getsockopt has. *)
Local Lemma record_copyins_twice_ok :
  forall pre reads (spec : Sys SyscallEffect) i m r ws m' evs,
  spec i m (Ok (mkEffect r ws []) m' evs) ->
  record_copyins pre (record_copyins reads spec) i m
    (Ok (with_copyins (pre ++ reads) (mkEffect r ws [])) m' evs).
Proof.
  intros pre reads spec i m r ws m' evs H.
  pose proof (record_copyins_ok_empty reads spec i m (mkEffect r ws []) m' evs
                eq_refl H) as H1.
  exact (record_copyins_ok pre _ i m _ m' evs H1).
Qed.

(** The stream-pair acceptors below test what their specs test, in the
    same order, so a proof can walk both at once: split the acceptor's
    next test and the spec's is decided with it.  [case_chk_hyp] splits
    the acceptor in a hypothesis (the soundness direction),
    [case_chk_goal] the acceptor in the goal (completeness); each leaf is
    then one of the few shapes the [*_leaf] tactics close. *)
Local Ltac case_chk_hyp H :=
  match type of H with
  | (if ?b then _ else _) = _ => destruct b eqn:?
  | (match ?x with _ => _ end) = _ => destruct x eqn:?
  end; cbv beta iota in *.

Local Ltac case_chk_goal :=
  match goal with
  | |- (if ?b then _ else _) = _ => destruct b eqn:?
  | |- (match ?x with _ => _ end) = _ => destruct x eqn:?
  end; cbv beta iota in *.

Local Ltac chk_ok_leaf H :=
  first
  [ discriminate H
  | (apply check_ret_only_ok_iff in H as (-> & -> & ->);
     first [ apply pure_ok
           | eapply bind_ok0; [apply modify_ok|]; apply pure_ok ])
  | (apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->);
     apply record_copyins_ok_empty; [reflexivity|];
     first [ apply pure_ok
           | eapply bind_ok0; [apply modify_ok|]; apply pure_ok ])
  | (apply check_ret_writes_copyins_ok_iff in H as (-> & -> & ->);
     first [ apply record_copyins_twice_ok; apply pure_ok
           | apply record_copyins_ok_empty; [reflexivity|apply pure_ok] ]) ].

Local Ltac chk_unm_leaf H :=
  first
  [ apply unmodeled_intro
  | (apply record_copyins_unmodeled; apply unmodeled_intro)
  | (apply record_copyins_unmodeled; apply record_copyins_unmodeled;
     apply unmodeled_intro)
  | now apply check_ret_only_no_unmodeled in H
  | now apply check_ret_only_copyins_no_unmodeled in H
  | now apply check_ret_writes_copyins_no_unmodeled in H
  | discriminate H ].

(** An effect equation between a spec's effect, with its ledger built by
    [record_copyins], and the [with_copyins] form an acceptor's [_ok_iff]
    names.  The two differ only by projections of literal effects and by
    a trailing [++ []]. *)
Local Ltac eff_ledger_eq :=
  unfold with_copyins;
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins];
  rewrite ?app_nil_r; reflexivity.

Local Ltac spec_ok_leaf H :=
  sys_unfold; cbv beta iota zeta in H; inv_ok;
  (* [inv_ok] closes a leaf whose spec side cannot answer; the rest is
     run on what is left *)
  (first [ apply check_ret_only_ok_iff
         | apply check_ret_only_copyins_ok_iff
         | apply check_ret_writes_copyins_ok_iff ];
   split; [eff_ledger_eq | split; reflexivity]).

Local Ltac spec_unm_leaf H :=
  first [ unm_refl | (sys_unfold; cbv beta iota zeta in H; inv_ok) ].

(** [Net.Socket.stream_getname] as an acceptor, test for test in its
    order.  Past the read of [ulen] every answer carries that read in its
    ledger, and the stores are fixed by the input, so the acceptor names
    the one effect the spec admits. *)
Definition check_stream_getname (uaddr ulen : word) (i : SyscallInput)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb ulen 4) then check_ret_only eff (errno_ret EFAULT) m []
  else
  match read_bytes_map (in_mem i) ulen (Z_to_bv 64 4) with
  | None =>
      match read_bytes_map (in_mem i) ulen (Z_to_bv 64 1) with
      | None => check_ret_only eff (errno_ret EFAULT) m []
      | Some _ => CheckUnmodeled
      end
  | Some lbs =>
      let len := Z.min (sint32 (le_bytes_to_word lbs)) 2 in
      if (len <? 0)%Z
      then check_ret_writes_copyins [(ulen, 4%nat)] eff (errno_ret EINVAL) [] m
      else if negb (user_range_writable i ulen 4) then CheckUnmodeled
      else if Z.eqb len 0
      then check_ret_writes_copyins [(ulen, 4%nat)] eff (Z_to_bv 64 0)
             [(ulen, word_le4 (Z_to_bv 64 2))] m
      else if user_range_writable i uaddr len
      then check_ret_writes_copyins [(ulen, 4%nat)] eff (Z_to_bv 64 0)
             [(ulen, word_le4 (Z_to_bv 64 2));
              (uaddr, firstn (Z.to_nat len) unix_unnamed_addr)] m
      else match read_bytes_map (in_wmem i) uaddr (Z_to_bv 64 1) with
           | None =>
               check_ret_writes_copyins [(ulen, 4%nat)] eff (errno_ret EFAULT)
                 [(ulen, word_le4 (Z_to_bv 64 2))] m
           | Some _ => CheckUnmodeled
           end
  end.

Lemma check_stream_getname_sound_ok : forall uaddr ulen i eff m m' evs,
  check_stream_getname uaddr ulen i eff m = CheckOk m' evs ->
  stream_getname uaddr ulen i i m (Ok eff m' evs).
Proof.
  intros uaddr ulen i eff m m' evs H.
  unfold check_stream_getname in H. unfold stream_getname.
  cbv beta zeta in H |- *.
  repeat case_chk_hyp H.
  all: chk_ok_leaf H.
Qed.

Lemma check_stream_getname_sound_unmodeled : forall uaddr ulen i eff m,
  check_stream_getname uaddr ulen i eff m = CheckUnmodeled ->
  stream_getname uaddr ulen i i m Unmodeled.
Proof.
  intros uaddr ulen i eff m H.
  unfold check_stream_getname in H. unfold stream_getname.
  cbv beta zeta in H |- *.
  repeat case_chk_hyp H.
  all: chk_unm_leaf H.
Qed.

Lemma check_stream_getname_complete_ok : forall uaddr ulen i eff m m' evs,
  stream_getname uaddr ulen i i m (Ok eff m' evs) ->
  check_stream_getname uaddr ulen i eff m = CheckOk m' evs.
Proof.
  intros uaddr ulen i eff m m' evs H.
  unfold stream_getname in H. unfold check_stream_getname.
  cbv beta zeta in H |- *.
  repeat case_chk_goal.
  all: spec_ok_leaf H.
Qed.

Lemma check_stream_getname_complete_unmodeled : forall uaddr ulen i m eff,
  stream_getname uaddr ulen i i m Unmodeled ->
  check_stream_getname uaddr ulen i eff m = CheckUnmodeled.
Proof.
  intros uaddr ulen i m eff H.
  unfold stream_getname in H. unfold check_stream_getname.
  cbv beta zeta in H |- *.
  repeat case_chk_goal.
  all: spec_unm_leaf H.
Qed.

(** [Net.Socket.stream_setsockopt] as an acceptor.  The one arm that
    moves the model stores the value [State.sndbuf_after_set] or
    [State.rcvbuf_after_set] computes from the run's [m_kernel] — the
    same expression the spec stores, so the accepted model is the spec's
    to the bit. *)
Definition check_stream_setsockopt (fd id : word) (side : bool) (st : StreamEnd)
    (optname optval optlen : word) (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : check_result :=
  let on := bv_unsigned optname in
  if negb ((on =? SO_SNDBUF) || (on =? SO_RCVBUF))%Z then CheckUnmodeled
  else if (bv_unsigned optlen <? 4)%Z then check_ret_only eff (errno_ret EINVAL) m []
  else
  match copy_bytes_map (in_mem i) optval 4 with
  | None => check_ret_only eff (errno_ret EFAULT) m []
  | Some vbs =>
      let v := bv_unsigned (le_bytes_to_word vbs) in
      check_ret_only_copyins [(optval, 4%nat)] eff (Z_to_bv 64 0)
        (with_fds (fd_insert (m_fds m) fd
                     (FdStream id side
                        (if (on =? SO_SNDBUF)%Z
                         then se_set_sndbuf st (sndbuf_after_set (m_kernel m) v)
                         else se_set_rcvbuf st (rcvbuf_after_set (m_kernel m) v)))) m)
        []
  end.

Lemma check_stream_setsockopt_sound_ok :
  forall fd id side st optname optval optlen i eff m m' evs,
  check_stream_setsockopt fd id side st optname optval optlen i eff m = CheckOk m' evs ->
  stream_setsockopt fd id side st optname optval optlen i m i m (Ok eff m' evs).
Proof.
  intros fd id side st optname optval optlen i eff m m' evs H.
  unfold check_stream_setsockopt in H. unfold stream_setsockopt.
  cbv beta zeta in H |- *.
  repeat case_chk_hyp H.
  all: chk_ok_leaf H.
Qed.

Lemma check_stream_setsockopt_sound_unmodeled :
  forall fd id side st optname optval optlen i eff m,
  check_stream_setsockopt fd id side st optname optval optlen i eff m = CheckUnmodeled ->
  stream_setsockopt fd id side st optname optval optlen i m i m Unmodeled.
Proof.
  intros fd id side st optname optval optlen i eff m H.
  unfold check_stream_setsockopt in H. unfold stream_setsockopt.
  cbv beta zeta in H |- *.
  repeat case_chk_hyp H.
  all: chk_unm_leaf H.
Qed.

Lemma check_stream_setsockopt_complete_ok :
  forall fd id side st optname optval optlen i eff m m' evs,
  stream_setsockopt fd id side st optname optval optlen i m i m (Ok eff m' evs) ->
  check_stream_setsockopt fd id side st optname optval optlen i eff m = CheckOk m' evs.
Proof.
  intros fd id side st optname optval optlen i eff m m' evs H.
  unfold stream_setsockopt in H. unfold check_stream_setsockopt.
  cbv beta zeta in H |- *.
  repeat case_chk_goal.
  all: spec_ok_leaf H.
Qed.

Lemma check_stream_setsockopt_complete_unmodeled :
  forall fd id side st optname optval optlen i m eff,
  stream_setsockopt fd id side st optname optval optlen i m i m Unmodeled ->
  check_stream_setsockopt fd id side st optname optval optlen i eff m = CheckUnmodeled.
Proof.
  intros fd id side st optname optval optlen i m eff H.
  unfold stream_setsockopt in H. unfold check_stream_setsockopt.
  cbv beta zeta in H |- *.
  repeat case_chk_goal.
  all: spec_unm_leaf H.
Qed.

(** [Net.Socket.stream_getsockopt] as an acceptor, under the ledger
    [pre] its caller has already recorded ([Net.Socket.getsockopt_spec]'s
    own read of [optlen]).  Every answer past [sk_getsockopt]'s second
    read of [optlen] carries that read after [pre]. *)
Definition check_stream_getsockopt (pre : list (word * nat)) (st : StreamEnd)
    (optname optval optlenp : word) (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : check_result :=
  let on := bv_unsigned optname in
  if negb ((on =? SO_SNDBUF) || (on =? SO_RCVBUF))%Z then CheckUnmodeled
  else
  match copy_bytes_map (in_mem i) optlenp 4 with
  | None => check_ret_writes_copyins pre eff (errno_ret EFAULT) [] m
  | Some lbs =>
      let reads := pre ++ [(optlenp, 4%nat)] in
      let len := sint32 (le_bytes_to_word lbs) in
      if (len <? 0)%Z then check_ret_writes_copyins reads eff (errno_ret EINVAL) [] m
      else
      let len' := Z.min len 4 in
      let v := if (on =? SO_SNDBUF)%Z then se_sndbuf st else se_rcvbuf st in
      let vw := if Z.eqb len' 0 then []
                else [(optval, firstn (Z.to_nat len') (word_le4 (Z_to_bv 64 v)))] in
      if negb (Z.eqb len' 0 || user_range_writable i optval len')%bool then
        match read_bytes_map (in_wmem i) optval (Z_to_bv 64 1) with
        | None => check_ret_writes_copyins reads eff (errno_ret EFAULT) [] m
        | Some _ => CheckUnmodeled
        end
      else if user_range_writable i optlenp 4
      then check_ret_writes_copyins reads eff (Z_to_bv 64 0)
             (vw ++ [(optlenp, word_le4 (Z_to_bv 64 len'))]) m
      else match read_bytes_map (in_wmem i) optlenp (Z_to_bv 64 1) with
           | None => check_ret_writes_copyins reads eff (errno_ret EFAULT) vw m
           | Some _ => CheckUnmodeled
           end
  end.

Lemma check_stream_getsockopt_sound_ok :
  forall pre st optname optval optlenp i eff m m' evs,
  check_stream_getsockopt pre st optname optval optlenp i eff m = CheckOk m' evs ->
  record_copyins pre (stream_getsockopt st optname optval optlenp i) i m
    (Ok eff m' evs).
Proof.
  intros pre st optname optval optlenp i eff m m' evs H.
  unfold check_stream_getsockopt in H. unfold stream_getsockopt.
  cbv beta zeta in H |- *.
  repeat case_chk_hyp H.
  all: chk_ok_leaf H.
Qed.

Lemma check_stream_getsockopt_sound_unmodeled :
  forall pre st optname optval optlenp i eff m,
  check_stream_getsockopt pre st optname optval optlenp i eff m = CheckUnmodeled ->
  record_copyins pre (stream_getsockopt st optname optval optlenp i) i m Unmodeled.
Proof.
  intros pre st optname optval optlenp i eff m H.
  unfold check_stream_getsockopt in H. unfold stream_getsockopt.
  cbv beta zeta in H |- *.
  repeat case_chk_hyp H.
  all: chk_unm_leaf H.
Qed.

Lemma check_stream_getsockopt_complete_ok :
  forall pre st optname optval optlenp i eff m m' evs,
  record_copyins pre (stream_getsockopt st optname optval optlenp i) i m
    (Ok eff m' evs) ->
  check_stream_getsockopt pre st optname optval optlenp i eff m = CheckOk m' evs.
Proof.
  intros pre st optname optval optlenp i eff m m' evs H.
  unfold stream_getsockopt in H. unfold check_stream_getsockopt.
  cbv beta zeta in H |- *.
  repeat case_chk_goal.
  all: spec_ok_leaf H.
Qed.

Lemma check_stream_getsockopt_complete_unmodeled :
  forall pre st optname optval optlenp i m eff,
  record_copyins pre (stream_getsockopt st optname optval optlenp i) i m Unmodeled ->
  check_stream_getsockopt pre st optname optval optlenp i eff m = CheckUnmodeled.
Proof.
  intros pre st optname optval optlenp i m eff H.
  unfold stream_getsockopt in H. unfold check_stream_getsockopt.
  cbv beta zeta in H |- *.
  repeat case_chk_goal.
  all: spec_unm_leaf H.
Qed.

(** [Net.Socket.stream_shutdown] as an acceptor: one answer, 0, over the
    fd table the spec builds -- this end's bits, then the peer's mirrored
    ones -- spelled exactly as the spec spells it. *)
Definition check_stream_shutdown (fd id : word) (side : bool) (st : StreamEnd)
    (how : word) (eff : SyscallEffect) (m : Model) : check_result :=
  let rd := negb (Z.eqb (bv_unsigned how) SHUT_WR) in
  let wr := negb (Z.eqb (bv_unsigned how) SHUT_RD) in
  let fds1 := fd_insert (m_fds m) fd (FdStream id side (se_add_shut st rd wr)) in
  check_ret_only eff (Z_to_bv 64 0)
    (with_fds (match stream_peer fds1 id side with
               | None => fds1
               | Some (pfd, pst) =>
                   fd_insert fds1 pfd (FdStream id (negb side) (se_add_shut pst wr rd))
               end) m) [].

Lemma check_stream_shutdown_sound_ok : forall fd id side st how eff m m' evs i,
  check_stream_shutdown fd id side st how eff m = CheckOk m' evs ->
  stream_shutdown fd id side st how m i m (Ok eff m' evs).
Proof.
  intros fd id side st how eff m m' evs i H.
  unfold check_stream_shutdown in H. unfold stream_shutdown.
  cbv beta zeta in H |- *.
  chk_ok_leaf H.
Qed.

Lemma check_stream_shutdown_sound_unmodeled : forall fd id side st how eff m i,
  check_stream_shutdown fd id side st how eff m = CheckUnmodeled ->
  stream_shutdown fd id side st how m i m Unmodeled.
Proof.
  intros fd id side st how eff m i H.
  unfold check_stream_shutdown in H. cbv beta zeta in H.
  now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_stream_shutdown_complete_ok : forall fd id side st how eff m m' evs i,
  stream_shutdown fd id side st how m i m (Ok eff m' evs) ->
  check_stream_shutdown fd id side st how eff m = CheckOk m' evs.
Proof.
  intros fd id side st how eff m m' evs i H.
  unfold stream_shutdown in H. unfold check_stream_shutdown.
  cbv beta zeta in H |- *.
  spec_ok_leaf H.
Qed.

Lemma check_stream_shutdown_complete_unmodeled : forall fd id side st how m i eff,
  stream_shutdown fd id side st how m i m Unmodeled ->
  check_stream_shutdown fd id side st how eff m = CheckUnmodeled.
Proof.
  intros fd id side st how m i eff H.
  unfold stream_shutdown in H. cbv beta zeta in H.
  exfalso. sys_unfold. cbv beta iota zeta in H. inv_ok.
Qed.

(** getsockname (204), getpeername (205), setsockopt (208), getsockopt
    (209), shutdown (210).  [Net.Socket.sock_fd] answers every fd kind but
    a socket, identically for all five and before any other argument is
    examined: -EBADF on a closed fd, -ENOTSOCK on a channel, a file or a
    directory.  ON A SOCKET they share nothing, which is why there are
    five acceptors here and not one — see [Net.Socket.getsockname_spec]
    and its four neighbours for the kernel argument behind each arm, and
    for what each of them declines and why.  A stream-pair end
    ([Net.Socket.SoPair]) takes the [check_stream_*] acceptors above,
    and a datagram socket ([Net.Socket.SoInert]) declines in all five:
    it is a socket, so never -ENOTSOCK, and the model carries none of
    the state these calls read. *)
Definition check_getsockname (i : SyscallInput) (fd : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match sock_fd m fd with
  | SoErr e => check_ret_only eff (errno_ret e) m []
  | SoInet _ => CheckUnmodeled
  | SoPair _ _ _ => check_stream_getname (in_arg i 1) (in_arg i 2) i eff m
  | SoInert _ => CheckUnmodeled
  end.

Definition check_getpeername (i : SyscallInput) (fd : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match sock_fd m fd with
  | SoErr e => check_ret_only eff (errno_ret e) m []
  | SoInet sk =>
      match sk with
      | SkFresh           => check_ret_only eff (errno_ret ENOTCONN) m []
      | SkBound           => check_ret_only eff (errno_ret ENOTCONN) m []
      | SkListening       => check_ret_only eff (errno_ret ENOTCONN) m []
      | SkReset _ _       => check_ret_only eff (errno_ret ENOTCONN) m []
      | SkConnected _ _ _ => CheckUnmodeled
      end
  | SoPair _ _ _ => check_stream_getname (in_arg i 1) (in_arg i 2) i eff m
  | SoInert _ => CheckUnmodeled
  end.

Definition check_setsockopt (i : SyscallInput) (fd level optlen : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match sock_fd m fd with
  | SoErr e => check_ret_only eff (errno_ret e) m []
  | SoInet _ =>
      if int32_neg optlen then check_ret_only eff (errno_ret EINVAL) m []
      else if negb (sock_level_known level)
      then check_ret_only eff (errno_ret ENOPROTOOPT) m []
      else CheckUnmodeled
  | SoPair id side st =>
      if int32_neg optlen then check_ret_only eff (errno_ret EINVAL) m []
      else if negb (Z.eqb (bv_unsigned level) SOL_SOCKET)
      then check_ret_only eff (errno_ret EOPNOTSUPP) m []
      else check_stream_setsockopt fd id side st (in_arg i 2) (in_arg i 3) optlen
             i eff m
  | SoInert _ => CheckUnmodeled
  end.

(** The ledger here is the whole of what [check_ret_only] could not say.
    [do_sock_getsockopt] reads four bytes at [optlen] before it dispatches
    on the level, so the -EOPNOTSUPP arm expects [eff_copyins] to be
    exactly that range — and the fd errnos above expect it EMPTY, because
    [__sys_getsockopt] answers them before [do_sock_getsockopt] runs at
    all.  See [Net.Socket.getsockopt_spec] for the kernel argument, the
    backported version window, and why an unreadable [optlen] records
    nothing.  A stream-pair end records the same read first, ahead of
    the level test, and [check_stream_getsockopt] carries it as [pre]. *)
Definition check_getsockopt (i : SyscallInput) (fd level optlenp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match sock_fd m fd with
  | SoErr e => check_ret_only eff (errno_ret e) m []
  | SoInet _ =>
      if negb (sock_level_known level)
      then check_ret_only_copyins (getsockopt_optlen_read i optlenp) eff
             (errno_ret EOPNOTSUPP) m []
      else CheckUnmodeled
  | SoPair _ _ st =>
      if negb (Z.eqb (bv_unsigned level) SOL_SOCKET)
      then check_ret_only_copyins (getsockopt_optlen_read i optlenp) eff
             (errno_ret EOPNOTSUPP) m []
      else check_stream_getsockopt (getsockopt_optlen_read i optlenp) st
             (in_arg i 2) (in_arg i 3) optlenp i eff m
  | SoInert _ => CheckUnmodeled
  end.

Definition check_shutdown (fd how : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match sock_fd m fd with
  | SoErr e => check_ret_only eff (errno_ret e) m []
  | SoInet sk =>
      if negb (shut_how_ok how) then check_ret_only eff (errno_ret EINVAL) m []
      else
        match sk with
        | SkFresh           => CheckUnmodeled
        | SkBound           => CheckUnmodeled
        | SkListening =>
            if (bv_unsigned how =? SHUT_WR)%Z
            then check_ret_only eff (Z_to_bv 64 0) m []
            else CheckUnmodeled
        | SkConnected _ _ _ => CheckUnmodeled
        | SkReset _ _       => CheckUnmodeled
        end
  | SoPair id side st =>
      if negb (shut_how_ok how) then check_ret_only eff (errno_ret EINVAL) m []
      else check_stream_shutdown fd id side st how eff m
  | SoInert _ => CheckUnmodeled
  end.

(** All five follow one shape: split on [sock_fd] into its four answers
    -- the errno, the AF_INET socket, the stream-pair end, the declined
    datagram socket -- then on whatever that call's own arm branches
    on.  The leaves below are the errno and decline shapes every one of
    them reaches. *)
Local Ltac sock_leaf_ok H :=
  first
  [ (unfold unmodeled in H; discriminate H)
  | (unfold err_ret, ret_only, pure in H; inv_ok;
     apply check_ret_only_ok_iff; now repeat split) ].

Local Ltac sock_leaf_unm H :=
  first [ unm_refl | (unfold err_ret, ret_only, pure in H; discriminate H) ].

Lemma check_getsockname_sound_ok : forall fd eff m m' evs i,
  check_getsockname i fd eff m = CheckOk m' evs ->
  getsockname_spec fd i m (Ok eff m' evs).
Proof.
  intros fd eff m m' evs i H.
  unfold check_getsockname in H. unfold getsockname_spec.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - discriminate.
  - eapply bind_ok0; [apply input_ok|]. cbv beta.
    now apply check_stream_getname_sound_ok.
  - discriminate.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
Qed.

Lemma check_getsockname_sound_unmodeled : forall fd eff m i,
  check_getsockname i fd eff m = CheckUnmodeled -> getsockname_spec fd i m Unmodeled.
Proof.
  intros fd eff m i H.
  unfold check_getsockname in H. unfold getsockname_spec.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - apply unmodeled_intro.
  - eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply check_stream_getname_sound_unmodeled. exact H.
  - apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_getsockname_complete_ok : forall fd eff m m' evs i,
  getsockname_spec fd i m (Ok eff m' evs) ->
  check_getsockname i fd eff m = CheckOk m' evs.
Proof.
  intros fd eff m m' evs i H.
  unfold getsockname_spec in H. unfold check_getsockname.
  apply bind_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - sock_leaf_ok H.
  - apply input_bind_ok_inv in H. cbv beta in H.
    eapply check_stream_getname_complete_ok. exact H.
  - sock_leaf_ok H.
  - sock_leaf_ok H.
Qed.

Lemma check_getsockname_complete_unmodeled : forall fd m i eff,
  getsockname_spec fd i m Unmodeled -> check_getsockname i fd eff m = CheckUnmodeled.
Proof.
  intros fd m i eff H.
  unfold getsockname_spec in H. unfold check_getsockname.
  apply bind_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - reflexivity.
  - apply input_bind_unmodeled_inv in H. cbv beta in H.
    eapply check_stream_getname_complete_unmodeled. exact H.
  - reflexivity.
  - sock_leaf_unm H.
Qed.

Lemma check_getpeername_sound_ok : forall fd eff m m' evs i,
  check_getpeername i fd eff m = CheckOk m' evs ->
  getpeername_spec fd i m (Ok eff m' evs).
Proof.
  intros fd eff m m' evs i H.
  unfold check_getpeername in H. unfold getpeername_spec.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
      try discriminate;
      apply check_ret_only_ok_iff in H as (-> & -> & ->); apply pure_ok.
  - eapply bind_ok0; [apply input_ok|]. cbv beta.
    now apply check_stream_getname_sound_ok.
  - discriminate.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
Qed.

Lemma check_getpeername_sound_unmodeled : forall fd eff m i,
  check_getpeername i fd eff m = CheckUnmodeled -> getpeername_spec fd i m Unmodeled.
Proof.
  intros fd eff m i H.
  unfold check_getpeername in H. unfold getpeername_spec.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
      solve [ now apply check_ret_only_no_unmodeled in H | apply unmodeled_intro ].
  - eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply check_stream_getname_sound_unmodeled. exact H.
  - apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_getpeername_complete_ok : forall fd eff m m' evs i,
  getpeername_spec fd i m (Ok eff m' evs) ->
  check_getpeername i fd eff m = CheckOk m' evs.
Proof.
  intros fd eff m m' evs i H.
  unfold getpeername_spec in H. unfold check_getpeername.
  apply bind_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
      sock_leaf_ok H.
  - apply input_bind_ok_inv in H. cbv beta in H.
    eapply check_stream_getname_complete_ok. exact H.
  - sock_leaf_ok H.
  - sock_leaf_ok H.
Qed.

Lemma check_getpeername_complete_unmodeled : forall fd m i eff,
  getpeername_spec fd i m Unmodeled -> check_getpeername i fd eff m = CheckUnmodeled.
Proof.
  intros fd m i eff H.
  unfold getpeername_spec in H. unfold check_getpeername.
  apply bind_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
      sock_leaf_unm H.
  - apply input_bind_unmodeled_inv in H. cbv beta in H.
    eapply check_stream_getname_complete_unmodeled. exact H.
  - reflexivity.
  - sock_leaf_unm H.
Qed.

Lemma check_setsockopt_sound_ok : forall fd level optlen eff m m' evs i,
  check_setsockopt i fd level optlen eff m = CheckOk m' evs ->
  setsockopt_spec fd level optlen i m (Ok eff m' evs).
Proof.
  intros fd level optlen eff m m' evs i H.
  unfold check_setsockopt in H. unfold setsockopt_spec.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (int32_neg optlen) eqn:Hn; cbv beta iota in H |- *.
    { apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok. }
    destruct (negb (sock_level_known level)) eqn:Hl; cbv beta iota in H |- *;
      [|discriminate].
    apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
  - destruct (int32_neg optlen) eqn:Hn; cbv beta iota in H |- *.
    { apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok. }
    destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)) eqn:Hl;
      cbv beta iota in H |- *.
    { apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok. }
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    now apply check_stream_setsockopt_sound_ok.
  - discriminate.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
Qed.

Lemma check_setsockopt_sound_unmodeled : forall fd level optlen eff m i,
  check_setsockopt i fd level optlen eff m = CheckUnmodeled ->
  setsockopt_spec fd level optlen i m Unmodeled.
Proof.
  intros fd level optlen eff m i H.
  unfold check_setsockopt in H. unfold setsockopt_spec.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (int32_neg optlen) eqn:Hn; cbv beta iota in H |- *;
      [now apply check_ret_only_no_unmodeled in H|].
    destruct (negb (sock_level_known level)) eqn:Hl; cbv beta iota in H |- *;
      [now apply check_ret_only_no_unmodeled in H|apply unmodeled_intro].
  - destruct (int32_neg optlen) eqn:Hn; cbv beta iota in H |- *;
      [now apply check_ret_only_no_unmodeled in H|].
    destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)) eqn:Hl;
      cbv beta iota in H |- *;
      [now apply check_ret_only_no_unmodeled in H|].
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply check_stream_setsockopt_sound_unmodeled. exact H.
  - apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_setsockopt_complete_ok : forall fd level optlen eff m m' evs i,
  setsockopt_spec fd level optlen i m (Ok eff m' evs) ->
  check_setsockopt i fd level optlen eff m = CheckOk m' evs.
Proof.
  intros fd level optlen eff m m' evs i H.
  unfold setsockopt_spec in H. unfold check_setsockopt.
  apply bind_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (int32_neg optlen) eqn:Hn; cbv beta iota in H |- *;
      [sock_leaf_ok H|].
    destruct (negb (sock_level_known level)) eqn:Hl; cbv beta iota in H |- *;
      sock_leaf_ok H.
  - destruct (int32_neg optlen) eqn:Hn; cbv beta iota in H |- *;
      [sock_leaf_ok H|].
    destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)) eqn:Hl;
      cbv beta iota in H |- *; [sock_leaf_ok H|].
    apply input_bind_ok_inv in H. cbv beta in H.
    eapply check_stream_setsockopt_complete_ok. exact H.
  - sock_leaf_ok H.
  - sock_leaf_ok H.
Qed.

Lemma check_setsockopt_complete_unmodeled : forall fd level optlen m i eff,
  setsockopt_spec fd level optlen i m Unmodeled ->
  check_setsockopt i fd level optlen eff m = CheckUnmodeled.
Proof.
  intros fd level optlen m i eff H.
  unfold setsockopt_spec in H. unfold check_setsockopt.
  apply bind_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (int32_neg optlen) eqn:Hn; cbv beta iota in H |- *;
      [sock_leaf_unm H|].
    destruct (negb (sock_level_known level)) eqn:Hl; cbv beta iota in H |- *;
      sock_leaf_unm H.
  - destruct (int32_neg optlen) eqn:Hn; cbv beta iota in H |- *;
      [sock_leaf_unm H|].
    destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)) eqn:Hl;
      cbv beta iota in H |- *; [sock_leaf_unm H|].
    apply input_bind_unmodeled_inv in H. cbv beta in H.
    eapply check_stream_setsockopt_complete_unmodeled. exact H.
  - reflexivity.
  - sock_leaf_unm H.
Qed.

Lemma check_getsockopt_sound_ok : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs ->
  getsockopt_spec fd level optlenp i m (Ok eff m' evs).
Proof.
  intros i fd level optlenp eff m m' evs H.
  unfold check_getsockopt in H. unfold getsockopt_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (negb (sock_level_known level)) eqn:Hl;
      cbv beta iota zeta in H |- *; [|discriminate].
    apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
  - destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)) eqn:Hl;
      cbv beta iota zeta in H |- *.
    + apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
    + now apply check_stream_getsockopt_sound_ok.
  - discriminate.
  - apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->).
    apply pure_ok.
Qed.

Lemma check_getsockopt_sound_unmodeled : forall i fd level optlenp eff m,
  check_getsockopt i fd level optlenp eff m = CheckUnmodeled ->
  getsockopt_spec fd level optlenp i m Unmodeled.
Proof.
  intros i fd level optlenp eff m H.
  unfold check_getsockopt in H. unfold getsockopt_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (negb (sock_level_known level)) eqn:Hl;
      cbv beta iota zeta in H |- *;
      [now apply check_ret_only_copyins_no_unmodeled in H|].
    apply record_copyins_unmodeled. apply unmodeled_intro.
  - destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)) eqn:Hl;
      cbv beta iota zeta in H |- *;
      [now apply check_ret_only_copyins_no_unmodeled in H|].
    eapply check_stream_getsockopt_sound_unmodeled. exact H.
  - apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_getsockopt_complete_ok : forall i fd level optlenp eff m m' evs,
  getsockopt_spec fd level optlenp i m (Ok eff m' evs) ->
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs.
Proof.
  intros i fd level optlenp eff m m' evs H.
  unfold getsockopt_spec in H. unfold check_getsockopt.
  apply bind_input_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - (* [record_copyins] APPENDS, and the wrapped arm records nothing of
       its own, so the observed ledger is [reads ++ []] where the
       checker's test is against [reads] itself. *)
    destruct (negb (sock_level_known level)) eqn:Hl;
      cbv beta iota zeta in H |- *;
      apply record_copyins_ok_inv in H as (core & Hcore & ->).
    + unfold err_ret, ret_only, pure in Hcore. inv_ok.
      apply check_ret_only_copyins_ok_iff.
      split; [eff_ledger_eq|split; reflexivity].
    + unfold unmodeled in Hcore. discriminate Hcore.
  - destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)) eqn:Hl;
      cbv beta iota zeta in H |- *.
    + apply record_copyins_ok_inv in H as (core & Hcore & ->).
      unfold err_ret, ret_only, pure in Hcore. inv_ok.
      apply check_ret_only_copyins_ok_iff.
      split; [eff_ledger_eq|split; reflexivity].
    + eapply check_stream_getsockopt_complete_ok. exact H.
  - sock_leaf_ok H.
  - sock_leaf_ok H.
Qed.

Lemma check_getsockopt_complete_unmodeled : forall i fd level optlenp m eff,
  getsockopt_spec fd level optlenp i m Unmodeled ->
  check_getsockopt i fd level optlenp eff m = CheckUnmodeled.
Proof.
  intros i fd level optlenp m eff H.
  unfold getsockopt_spec in H. unfold check_getsockopt.
  apply bind_input_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (negb (sock_level_known level)) eqn:Hl;
      cbv beta iota zeta in H |- *; [|reflexivity].
    apply record_copyins_unmodeled_inv in H. sock_leaf_unm H.
  - destruct (negb (Z.eqb (bv_unsigned level) SOL_SOCKET)) eqn:Hl;
      cbv beta iota zeta in H |- *.
    + apply record_copyins_unmodeled_inv in H. sock_leaf_unm H.
    + eapply check_stream_getsockopt_complete_unmodeled. exact H.
  - reflexivity.
  - sock_leaf_unm H.
Qed.

Lemma check_shutdown_sound_ok : forall fd how eff m m' evs i,
  check_shutdown fd how eff m = CheckOk m' evs ->
  shutdown_spec fd how i m (Ok eff m' evs).
Proof.
  intros fd how eff m m' evs i H.
  unfold check_shutdown in H. unfold shutdown_spec.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (negb (shut_how_ok how)) eqn:Hh; cbv beta iota in H |- *.
    { apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok. }
    destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
      try discriminate.
    destruct (bv_unsigned how =? SHUT_WR)%Z eqn:Hw; cbv beta iota in H |- *;
      [|discriminate].
    apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
  - destruct (negb (shut_how_ok how)) eqn:Hh; cbv beta iota in H |- *.
    { apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok. }
    now apply check_stream_shutdown_sound_ok.
  - discriminate.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
Qed.

Lemma check_shutdown_sound_unmodeled : forall fd how eff m i,
  check_shutdown fd how eff m = CheckUnmodeled -> shutdown_spec fd how i m Unmodeled.
Proof.
  intros fd how eff m i H.
  unfold check_shutdown in H. unfold shutdown_spec.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (negb (shut_how_ok how)) eqn:Hh; cbv beta iota in H |- *;
      [now apply check_ret_only_no_unmodeled in H|].
    destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
      try apply unmodeled_intro.
    destruct (bv_unsigned how =? SHUT_WR)%Z eqn:Hw; cbv beta iota in H |- *;
      [now apply check_ret_only_no_unmodeled in H|apply unmodeled_intro].
  - destruct (negb (shut_how_ok how)) eqn:Hh; cbv beta iota in H |- *;
      [now apply check_ret_only_no_unmodeled in H|].
    eapply check_stream_shutdown_sound_unmodeled. exact H.
  - apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_shutdown_complete_ok : forall fd how eff m m' evs i,
  shutdown_spec fd how i m (Ok eff m' evs) ->
  check_shutdown fd how eff m = CheckOk m' evs.
Proof.
  intros fd how eff m m' evs i H.
  unfold shutdown_spec in H. unfold check_shutdown.
  apply bind_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (negb (shut_how_ok how)) eqn:Hh; cbv beta iota in H |- *;
      [sock_leaf_ok H|].
    destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
      try sock_leaf_ok H.
    destruct (bv_unsigned how =? SHUT_WR)%Z eqn:Hw; cbv beta iota in H |- *;
      sock_leaf_ok H.
  - destruct (negb (shut_how_ok how)) eqn:Hh; cbv beta iota in H |- *;
      [sock_leaf_ok H|].
    eapply check_stream_shutdown_complete_ok. exact H.
  - sock_leaf_ok H.
  - sock_leaf_ok H.
Qed.

Lemma check_shutdown_complete_unmodeled : forall fd how m i eff,
  shutdown_spec fd how i m Unmodeled -> check_shutdown fd how eff m = CheckUnmodeled.
Proof.
  intros fd how m i eff H.
  unfold shutdown_spec in H. unfold check_shutdown.
  apply bind_model_inv in H. cbv beta in H.
  destruct (sock_fd m fd) as [sk|id side st|fam|e] eqn:Hsf;
    cbv beta iota zeta in H |- *.
  - destruct (negb (shut_how_ok how)) eqn:Hh; cbv beta iota in H |- *;
      [sock_leaf_unm H|].
    destruct sk as [| | |peer ch rx|peer ch]; cbv beta iota zeta in H |- *;
      try sock_leaf_unm H.
    destruct (bv_unsigned how =? SHUT_WR)%Z eqn:Hw; cbv beta iota in H |- *;
      sock_leaf_unm H.
  - destruct (negb (shut_how_ok how)) eqn:Hh; cbv beta iota in H |- *;
      [sock_leaf_unm H|].
    eapply check_stream_shutdown_complete_unmodeled. exact H.
  - reflexivity.
  - sock_leaf_unm H.
Qed.

(* ------------------------------------------------------- sendto, sendmsg *)

(** [Net.Socket.send_on_socket] as an acceptor — the socket half both
    calls share, so the short-send rule is decided in ONE place.

    On [Net.Socket.SendGoes] the claimed return picks the delivered
    prefix, exactly as [Fs.ReadWrite.check_write] does on a channel, with
    one extra conjunct: [ret <= total].  [check_write] gets that bound for
    free ([readable_bytes_length_le]), but [sendmsg] arrives with a
    GATHERED source whose length is not related to the requested total by
    any lemma this file carries, and [Net.Socket.send_bytes] requires it.
    Testing it here keeps both callers honest and needs no lemma at all.

    THE LEDGER IS TESTED ON EVERY ARM, and [pre] is what makes the two
    callers differ: empty for [sendto], the header and the descriptors
    for [sendmsg].  An arm that moves no payload byte expects exactly
    [pre]; the delivering arm expects [pre] followed by the ranges the
    delivered prefix came out of.

    [SendErr] accepts the model with the error CONSUMED — [fd_insert]
    onto [SkReset] — because the spec consumes it, and a checker that
    accepted the unchanged model would let a program read the same reset
    twice. *)
Definition check_send_on_socket (pre : list (word * nat))
    (acc : nat -> list (word * nat)) (fd : word) (sk : SockState)
    (total : word) (bs : list byte) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match send_state sk with
  | SendGoes ch =>
      if w_is0 total then check_ret_only_copyins pre eff (Z_to_bv 64 0) m []
      else if Nat.eqb (length bs) 0
      then check_ret_only_copyins pre eff (errno_ret EFAULT) m []
      else
        match eff with
        | mkEffectU ret [] [] [] [] copyins =>
            if (1 <=? bv_unsigned ret)%Z
               && (bv_unsigned ret <=? Z.of_nat (length bs))%Z
               && (bv_unsigned ret <=? bv_unsigned total)%Z
            then
              (* nested, not a fourth [&&]: [vm_compute] evaluates every
                 [andb] operand, and this one converts [ret] to a unary
                 [nat] -- see [Fs.ReadWrite.check_write]'s channel arm *)
              if access_ranges_eqb copyins (pre ++ acc (Z.to_nat (bv_unsigned ret)))
              then CheckOk m (map (WriteEv ch)
                                (firstn (Z.to_nat (bv_unsigned ret)) bs))
              else CheckReject
            else CheckReject
        | _ => CheckReject
        end
  | SendErr e peer ch =>
      check_ret_only_copyins pre eff (errno_ret e)
        (with_fds (fd_insert (m_fds m) fd (FdSocket (SkReset peer ch))) m) []
  | SendDead => check_ret_only_copyins pre eff (errno_ret EPIPE) m []
  end.

(** [sendto]: the three gates, then [import_ubuf]'s range verdict, then
    the fd — and the fd match stays INSIDE [check_access_ok_zero],
    because that nesting is what makes [sendto(-1, unmapped, n, ...)]
    -EFAULT rather than -EBADF.  The flag gate is the UNION of the two
    socket kinds' flag sets, and each kind re-checks its own: exactly
    MSG_NOSIGNAL on an AF_INET socket, MSG_NOSIGNAL and MSG_DONTWAIT in
    any combination on a stream-pair end, whose send is
    [Fs.ReadWrite.check_stream_write]. *)
Definition check_sendto (i : SyscallInput) (fd buf count flags addrp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (send_flags_modeled flags || stream_send_flags_ok flags)%bool
  then CheckUnmodeled
  else if negb (w_is0 addrp) then CheckUnmodeled
  else if negb (modeled_rw_count count) then CheckUnmodeled
  else
    check_access_ok_zero buf count eff m
      (match fd_lookup (m_fds m) fd with
       | None => check_ret_only eff (errno_ret EBADF) m []
       | Some (FdSocket sk) =>
           if negb (send_flags_modeled flags) then CheckUnmodeled
           else
           check_send_on_socket [] (fun n => [(buf, n)]) fd sk count
             (readable_bytes (in_mem i) buf count) eff m
       | Some (FdStream id side st) =>
           if negb (stream_send_flags_ok flags) then CheckUnmodeled
           else check_stream_write id side st
                  (se_nonblock st || send_flag flags MSG_DONTWAIT)%bool
                  (send_flag flags MSG_NOSIGNAL) buf count i eff m
       | Some (FdDgram _) => CheckUnmodeled  (* a socket with no peer: declined *)
       | Some _ => check_ret_only eff (errno_ret ENOTSOCK) m []
       end).

(** [sendmsg]: the fd FIRST and the header second, the opposite nesting
    to [check_sendto] — deliberately not shared with it.  The expected
    ledger is spelled out arm by arm rather than accumulated by a wrapper,
    so that a reader can see at each answer exactly which user bytes the
    kernel had read by the time it gave that answer. *)
Definition check_sendmsg (i : SyscallInput) (fd msgp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (send_flags_modeled flags) then CheckUnmodeled
  else
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) | Some (FdFile _ _)
  | Some (FdFileW _ _) | Some FdDir
  | Some (FdFileA _ _) | Some (FdFileRW _ _)
  | Some (FdPipe _ _) | Some (FdDevNull _ _) | Some FdUrandom
  | Some (FdEventfd _) | Some (FdAnon _ _) =>
      check_ret_only eff (errno_ret ENOTSOCK) m []
  | Some (FdStream _ _ _) => CheckUnmodeled
      (* AF_UNIX [sendmsg] can carry SCM_RIGHTS: see [Specs.sendmsg_spec] *)
  | Some (FdDgram _) => CheckUnmodeled
      (* the stream-pair end's reason for AF_UNIX, and no peer or state
         for either family: see [Specs.sendmsg_spec] *)
  | Some (FdSocket sk) =>
      match copy_bytes_map (in_mem i) msgp MSGHDR_SIZE with
      | None => check_ret_only eff (errno_ret EFAULT) m []
      | Some _ =>
          match read_u64 (in_mem i) msgp,
                read_u64 (in_mem i) (msgp + Z_to_bv 64 8),
                read_u64 (in_mem i) (msgp + Z_to_bv 64 16),
                read_u64 (in_mem i) (msgp + Z_to_bv 64 24),
                read_u64 (in_mem i) (msgp + Z_to_bv 64 32),
                read_u64 (in_mem i) (msgp + Z_to_bv 64 40) with
          | Some name, Some _, Some iov, Some iovlen, Some _, Some ctllen =>
              if negb (w_is0 name) then CheckUnmodeled
              else if (IOV_MAX <? bv_unsigned iovlen)%Z
              then check_ret_only_copyins [(msgp, Z.to_nat MSGHDR_SIZE)] eff
                     (errno_ret EMSGSIZE) m []
              else if (UIO_FASTIOV <? bv_unsigned iovlen)%Z then CheckUnmodeled
              else
              match import_iovecs (in_mem i) iov iovlen with
              | ImpFault =>
                  check_ret_only_copyins
                    ([(msgp, Z.to_nat MSGHDR_SIZE)]
                     ++ import_iovecs_accesses (in_mem i) iov iovlen)
                    eff (errno_ret EFAULT) m []
              | ImpInval =>
                  check_ret_only_copyins
                    ([(msgp, Z.to_nat MSGHDR_SIZE)]
                     ++ import_iovecs_accesses (in_mem i) iov iovlen)
                    eff (errno_ret EINVAL) m []
              | ImpOk iovs0 =>
                  (* msg_controllen is decided HERE, where ____sys_sendmsg
                     decides it: after the descriptors are imported, not
                     before.  Ordering is behaviour -- a call with a
                     non-zero controllen AND iovlen over IOV_MAX answers
                     -EMSGSIZE above rather than declining here. *)
                  if negb (w_is0 ctllen) then CheckUnmodeled
                  else if negb (iovs_total (cap_iovecs iovs0) <=? rw_bytes_max)%Z
                  then CheckUnmodeled
                  else
                  check_send_on_socket
                    ([(msgp, Z.to_nat MSGHDR_SIZE)]
                     ++ import_iovecs_accesses (in_mem i) iov iovlen)
                    (fun n => iov_prefix_accesses (cap_iovecs iovs0) n)
                    fd sk
                    (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))
                    (writev_gathered (in_mem i) iovs0) eff m
              end
          | _, _, _, _, _, _ =>
              check_ret_only_copyins [(msgp, Z.to_nat MSGHDR_SIZE)] eff
                (errno_ret EFAULT) m []
          end
      end
  end.

(** The shared socket half, proved once.  [Net.Socket.send_on_socket] is
    run at the same model it captured, which is how both callers use
    it. *)

Lemma check_send_on_socket_sound_ok :
  forall pre acc fd sk total bs eff m m' evs i,
  check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs ->
  send_on_socket pre acc fd sk total bs m i m (Ok eff m' evs).
Proof.
  intros pre acc fd sk total bs eff m m' evs i H.
  unfold check_send_on_socket in H. unfold send_on_socket.
  destruct (send_state sk) as [ch|e peer ch|]; cbv beta iota zeta in H |- *.
  - (* SendGoes *)
    unfold send_bytes.
    destruct (w_is0 total) eqn:Ht.
    { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct (Nat.eqb (length bs) 0) eqn:Hb.
    { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
    destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
      destruct zs as [|? ?]; destruct us as [|? ?]; destruct cs as [|? ?];
      try discriminate.
    destruct ((1 <=? bv_unsigned ret)%Z
              && (bv_unsigned ret <=? Z.of_nat (length bs))%Z
              && (bv_unsigned ret <=? bv_unsigned total)%Z) eqn:Hc;
      [|discriminate].
    destruct (access_ranges_eqb copyins (pre ++ acc (Z.to_nat (bv_unsigned ret))))
      eqn:Hreads; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hc as [Hc12 H3].
    apply andb_true_iff in Hc12 as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply access_ranges_eqb_eq in Hreads. subst copyins.
    pose proof (word_unsigned_range ret) as Hr.
    set (ds := firstn (Z.to_nat (bv_unsigned ret)) bs) in *.
    assert (Hlen : Z.of_nat (length ds) = bv_unsigned ret)
      by (apply firstn_length_le_Z; lia).
    assert (Hlw : len_word ds = ret).
    { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
    replace (Z.to_nat (bv_unsigned ret)) with (length ds) by lia.
    rewrite <- Hlw.
    eapply bind_ok0.
    { apply (choose_ok _ ds). cbv beta. repeat split; [lia|lia|].
      assert (Hlnat : length ds = Z.to_nat (bv_unsigned ret)) by lia.
      rewrite Hlnat. reflexivity. }
    cbv beta.
    eapply bind_ok_eq; [apply emit_ok| |].
    { eapply record_copyins_ok_empty with (eff := mkEffect (len_word ds) [] []);
        [reflexivity|apply pure_ok]. }
    now rewrite app_nil_r.
  - (* SendErr: the pending error is consumed *)
    apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|].
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - (* SendDead *)
    apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
Qed.

(** Every arm of [check_send_on_socket] either accepts or rejects; none
    declines, which is what makes the two callers' [CheckUnmodeled]
    reachable only through THEIR OWN gates. *)
Lemma check_send_on_socket_no_unmodeled :
  forall pre acc fd sk total bs eff m,
  check_send_on_socket pre acc fd sk total bs eff m = CheckUnmodeled -> False.
Proof.
  intros pre acc fd sk total bs eff m H.
  unfold check_send_on_socket in H.
  destruct (send_state sk) as [ch|e peer ch|]; cbv beta iota zeta in H;
    try (now apply check_ret_only_copyins_no_unmodeled in H).
  destruct (w_is0 total); [now apply check_ret_only_copyins_no_unmodeled in H|].
  destruct (Nat.eqb (length bs) 0);
    [now apply check_ret_only_copyins_no_unmodeled in H|].
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?]; destruct cs as [|? ?];
    try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length bs))%Z
            && (bv_unsigned ret <=? bv_unsigned total)%Z);
    [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

(** [send_on_socket] never declines either, so the checker's totality
    above is matched on the spec side. *)
Lemma send_on_socket_no_unmodeled : forall pre acc fd sk total bs m i,
  send_on_socket pre acc fd sk total bs m i m Unmodeled -> False.
Proof.
  intros pre acc fd sk total bs m i H.
  unfold send_on_socket in H. sys_unfold.
  destruct (send_state sk) as [ch|e peer ch|]; cbv beta iota zeta in H; inv_ok.
  unfold send_bytes in H. sys_unfold.
  destruct (w_is0 total); cbv beta iota zeta in H; inv_ok.
  destruct (Nat.eqb (length bs) 0); cbv beta iota zeta in H; inv_ok.
Qed.

Lemma check_send_on_socket_complete_ok :
  forall pre acc fd sk total bs eff m m' evs i,
  send_on_socket pre acc fd sk total bs m i m (Ok eff m' evs) ->
  check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs.
Proof.
  intros pre acc fd sk total bs eff m m' evs i H.
  unfold send_on_socket in H. unfold check_send_on_socket. sys_unfold.
  destruct (send_state sk) as [ch|e peer ch|]; cbv beta iota zeta in H |- *;
    inv_ok;
    try (unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins];
         rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl);
         cbn; rewrite ?bv_eqb_refl; reflexivity).
  unfold send_bytes in H. sys_unfold.
  destruct (w_is0 total) eqn:Ht; cbv beta iota zeta in H |- *; inv_ok;
    [unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins];
     rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl);
     cbn; rewrite ?bv_eqb_refl; reflexivity|].
  destruct (Nat.eqb (length bs) 0) eqn:Hb; cbv beta iota zeta in H |- *; inv_ok;
    [unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins];
     rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl);
     cbn; rewrite ?bv_eqb_refl; reflexivity|].
  (* the environment's chosen prefix, replayed through the guard.  The
     checker's match on the effect is reducible only now, once [inv_ok]
     has put a literal there, and the projections in front of it need
     delta as well as iota. *)
  cbv beta iota zeta.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
  match goal with
  | Hpre : ?l = firstn (length ?l) bs |- _ =>
      pose proof (f_equal (@length _) Hpre) as Hfl;
      rewrite length_firstn in Hfl;
      pose proof (word_unsigned_range total) as Htr;
      assert (Hsm : (Z.of_nat (length l) < two_pow_64)%Z) by lia;
      rewrite (len_word_unsigned l Hsm);
      assert (Hnat : Z.to_nat (Z.of_nat (length l)) = length l) by lia;
      rewrite Hnat, <- Hpre
  end.
  rewrite !app_nil_r, !app_nil_l.
  bool_true.
  rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl).
  reflexivity.
Qed.

(* --- sendto --- *)

Lemma check_sendto_sound_ok :
  forall i fd buf count flags addrp addrlen eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs ->
  sendto_spec fd buf count flags addrp addrlen i m (Ok eff m' evs).
Proof.
  intros i fd buf count flags addrp addrlen eff m m' evs H.
  unfold check_sendto in H. unfold sendto_spec.
  destruct (negb (send_flags_modeled flags || stream_send_flags_ok flags)%bool) eqn:Hf;
    [discriminate|].
  destruct (negb (w_is0 addrp)) eqn:Ha; [discriminate|].
  destruct (negb (modeled_rw_count count)) eqn:Hc; [discriminate|].
  cbv zeta.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota zeta.
  ok_zero_cases H buf count;
    [ | apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
        apply pure_ok ].
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *; try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         apply pure_ok).
  - destruct (negb (send_flags_modeled flags)) eqn:Hs; cbv beta iota in H |- *;
      [discriminate|].
    now apply check_send_on_socket_sound_ok.
  - destruct (negb (stream_send_flags_ok flags)) eqn:Hs; cbv beta iota in H |- *;
      [discriminate|].
    eapply check_stream_write_sound_ok. exact H.
Qed.

Lemma check_sendto_sound_unmodeled :
  forall i fd buf count flags addrp addrlen eff m,
  check_sendto i fd buf count flags addrp eff m = CheckUnmodeled ->
  sendto_spec fd buf count flags addrp addrlen i m Unmodeled.
Proof.
  intros i fd buf count flags addrp addrlen eff m H.
  unfold check_sendto in H. unfold sendto_spec.
  destruct (negb (send_flags_modeled flags || stream_send_flags_ok flags)%bool) eqn:Hf;
    [apply unmodeled_intro|].
  destruct (negb (w_is0 addrp)) eqn:Ha; [apply unmodeled_intro|].
  destruct (negb (modeled_rw_count count)) eqn:Hc; [apply unmodeled_intro|].
  cbv zeta.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
  ok_zero_cases H buf count;
    [ | now apply check_ret_only_no_unmodeled in H ].
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *;
    try (now apply check_ret_only_no_unmodeled in H).
  - destruct (negb (send_flags_modeled flags)) eqn:Hs; cbv beta iota in H |- *;
      [apply unmodeled_intro|].
    now apply check_send_on_socket_no_unmodeled in H.
  - destruct (negb (stream_send_flags_ok flags)) eqn:Hs; cbv beta iota in H |- *;
      [apply unmodeled_intro|].
    eapply check_stream_write_sound_unmodeled. exact H.
  - apply unmodeled_intro.          (* the datagram socket *)
Qed.

Lemma check_sendto_complete_ok :
  forall i fd buf count flags addrp addrlen eff m m' evs,
  sendto_spec fd buf count flags addrp addrlen i m (Ok eff m' evs) ->
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs.
Proof.
  intros i fd buf count flags addrp addrlen eff m m' evs H.
  unfold sendto_spec in H. unfold check_sendto.
  cbv zeta in H.
  destruct (negb (send_flags_modeled flags || stream_send_flags_ok flags)%bool) eqn:Hf;
    [unfold unmodeled in H; inversion H|].
  destruct (negb (w_is0 addrp)) eqn:Ha;
    [unfold unmodeled in H; inversion H|].
  destruct (negb (modeled_rw_count count)) eqn:Hc;
    [unfold unmodeled in H; inversion H|].
  sys_unfold. cbv iota zeta in H. inv_ok.
  ok_zero_split buf count.
  2: { cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok;
    try (apply check_ret_only_ok_iff; now repeat split).
  - destruct (negb (send_flags_modeled flags)) eqn:Hs; hall Hs; inv_ok.
    eapply check_send_on_socket_complete_ok with (i := i). eassumption.
  - destruct (negb (stream_send_flags_ok flags)) eqn:Hs; hall Hs; inv_ok.
    eapply check_stream_write_complete_ok. eassumption.
Qed.

Lemma check_sendto_complete_unmodeled :
  forall i fd buf count flags addrp addrlen m eff,
  sendto_spec fd buf count flags addrp addrlen i m Unmodeled ->
  check_sendto i fd buf count flags addrp eff m = CheckUnmodeled.
Proof.
  intros i fd buf count flags addrp addrlen m eff H.
  unfold sendto_spec in H. unfold check_sendto.
  cbv zeta in H.
  destruct (negb (send_flags_modeled flags || stream_send_flags_ok flags)%bool) eqn:Hf;
    [reflexivity|].
  destruct (negb (w_is0 addrp)) eqn:Ha; [reflexivity|].
  destruct (negb (modeled_rw_count count)) eqn:Hc; [reflexivity|].
  sys_unfold. cbv iota zeta in H. inv_ok.
  (* the refused range answers -EFAULT and so cannot be a decline:
     [inv_ok] has already closed it.  What is left is the range that
     passes, where only the socket arm can decline *)
  ok_zero_split buf count.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok; try discriminate.
  - destruct (negb (send_flags_modeled flags)) eqn:Hs; hall Hs; inv_ok;
      [reflexivity|].
    exfalso. eapply send_on_socket_no_unmodeled with (i := i). eassumption.
  - destruct (negb (stream_send_flags_ok flags)) eqn:Hs; hall Hs; inv_ok;
      [reflexivity|].
    eapply check_stream_write_complete_unmodeled. eassumption.
  - reflexivity.                    (* the datagram socket *)
Qed.

(* --- sendmsg --- *)

(** The header's six reads are destructed together: 63 of the 64 shapes
    are the total-match -EFAULT arm both sides agree on, and only the
    all-[Some] one carries the call.  Keep the goal selectors below --
    a uniform [cbn] here delta-reduces [State.copy_iovecs_aux]'s fuel,
    which [State.import_iovecs] still reaches. *)
Lemma check_sendmsg_sound_ok : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs ->
  sendmsg_spec fd msgp flags i m (Ok eff m' evs).
Proof.
  intros i fd msgp flags eff m m' evs H.
  unfold check_sendmsg in H. unfold sendmsg_spec.
  destruct (negb (send_flags_modeled flags)) eqn:Hf; [discriminate|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *; try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         apply pure_ok).
  destruct (copy_bytes_map (in_mem i) msgp MSGHDR_SIZE) eqn:Hh;
    cbv beta iota zeta in H |- *;
    [|apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      apply pure_ok].
  destruct (read_u64 (in_mem i) msgp) as [name|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 8)) as [namelen|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 16)) as [iov|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 24)) as [iovlen|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 32)) as [ctl|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 40)) as [ctllen|];
    cbv beta iota zeta in H |- *;
    try (apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->);
         apply record_copyins_ok_empty; [reflexivity|apply pure_ok]).
  destruct (negb (w_is0 name)) eqn:Hn; [discriminate|].
  destruct ((IOV_MAX <? bv_unsigned iovlen)%Z) eqn:Hiv;
    [apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->);
     apply record_copyins_ok_empty; [reflexivity|apply pure_ok]|].
  destruct ((UIO_FASTIOV <? bv_unsigned iovlen)%Z) eqn:Hfa; [discriminate|].
  destruct (import_iovecs (in_mem i) iov iovlen) as [iovs0| |]
    eqn:Hci; cbv beta iota zeta in H |- *;
    [ | apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->);
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok]
      | apply check_ret_only_copyins_ok_iff in H; destruct H as (-> & -> & ->);
        apply record_copyins_ok_empty; [reflexivity|apply pure_ok] ].
  destruct (negb (w_is0 ctllen)) eqn:Hcl; [discriminate|].
  destruct (negb (iovs_total (cap_iovecs iovs0) <=? rw_bytes_max)%Z) eqn:Hmt;
    [discriminate|].
  now apply check_send_on_socket_sound_ok.
Qed.

Lemma check_sendmsg_sound_unmodeled : forall i fd msgp flags eff m,
  check_sendmsg i fd msgp flags eff m = CheckUnmodeled ->
  sendmsg_spec fd msgp flags i m Unmodeled.
Proof.
  intros i fd msgp flags eff m H.
  unfold check_sendmsg in H. unfold sendmsg_spec.
  destruct (negb (send_flags_modeled flags)) eqn:Hf; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    cbv beta iota zeta in H |- *;
    try (now apply check_ret_only_no_unmodeled in H); try apply unmodeled_intro.
  destruct (copy_bytes_map (in_mem i) msgp MSGHDR_SIZE) eqn:Hh;
    cbv beta iota zeta in H |- *;
    [|now apply check_ret_only_no_unmodeled in H].
  destruct (read_u64 (in_mem i) msgp) as [name|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 8)) as [namelen|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 16)) as [iov|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 24)) as [iovlen|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 32)) as [ctl|],
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 40)) as [ctllen|];
    cbv beta iota zeta in H |- *;
    try (now apply check_ret_only_copyins_no_unmodeled in H).
  destruct (negb (w_is0 name)) eqn:Hn; [apply unmodeled_intro|].
  destruct ((IOV_MAX <? bv_unsigned iovlen)%Z) eqn:Hiv;
    [now apply check_ret_only_copyins_no_unmodeled in H|].
  destruct ((UIO_FASTIOV <? bv_unsigned iovlen)%Z) eqn:Hfa;
    [apply unmodeled_intro|].
  destruct (import_iovecs (in_mem i) iov iovlen) as [iovs0| |]
    eqn:Hci; cbv beta iota zeta in H |- *;
    [ | now apply check_ret_only_copyins_no_unmodeled in H
      | now apply check_ret_only_copyins_no_unmodeled in H ].
  destruct (negb (w_is0 ctllen)) eqn:Hcl; [apply unmodeled_intro|].
  destruct (negb (iovs_total (cap_iovecs iovs0) <=? rw_bytes_max)%Z) eqn:Hmt;
    [apply unmodeled_intro|].
  now apply check_send_on_socket_no_unmodeled in H.
Qed.

Lemma check_sendmsg_complete_ok : forall i fd msgp flags eff m m' evs,
  sendmsg_spec fd msgp flags i m (Ok eff m' evs) ->
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs.
Proof.
  intros i fd msgp flags eff m m' evs H.
  unfold sendmsg_spec in H. unfold check_sendmsg.
  destruct (negb (send_flags_modeled flags)) eqn:Hf;
    [unfold unmodeled in H; inversion H|].
  sys_unfold. cbv iota zeta in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok;
    try (cbn; try rewrite bv_eqb_refl; reflexivity).
  destruct (copy_bytes_map (in_mem i) msgp MSGHDR_SIZE) eqn:Hh;
    hall Hh; inv_ok;
    [|cbn; try rewrite bv_eqb_refl; reflexivity].
  destruct (read_u64 (in_mem i) msgp) as [name|] eqn:R0,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 8)) as [namelen|] eqn:R1,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 16)) as [iov|] eqn:R2,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 24)) as [iovlen|] eqn:R3,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 32)) as [ctl|] eqn:R4,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 40)) as [ctllen|] eqn:R5;
    cbv beta iota zeta in *; inv_ok;
    try (unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins];
         rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl);
         cbn; rewrite ?bv_eqb_refl; reflexivity).
  destruct (negb (w_is0 name)) eqn:Hn; hall Hn; inv_ok.
  destruct ((IOV_MAX <? bv_unsigned iovlen)%Z) eqn:Hiv; hall Hiv; inv_ok;
    [unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins];
     rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl);
     cbn; rewrite ?bv_eqb_refl; reflexivity|].
  destruct ((UIO_FASTIOV <? bv_unsigned iovlen)%Z) eqn:Hfa; hall Hfa; inv_ok.
  destruct (import_iovecs (in_mem i) iov iovlen) as [iovs0| |]
    eqn:Hci; hall Hci; inv_ok;
    try (unfold check_ret_only_copyins, clear_copyins; cbn [with_copyins];
         rewrite app_nil_r, (proj2 (access_ranges_eqb_eq _ _) eq_refl);
         cbn; rewrite ?bv_eqb_refl; reflexivity).
  destruct (negb (w_is0 ctllen)) eqn:Hcl; hall Hcl; inv_ok.
  destruct (negb (iovs_total (cap_iovecs iovs0) <=? rw_bytes_max)%Z) eqn:Hmt;
    hall Hmt; inv_ok.
  eapply check_send_on_socket_complete_ok with (i := i). eassumption.
Qed.

Lemma check_sendmsg_complete_unmodeled : forall i fd msgp flags m eff,
  sendmsg_spec fd msgp flags i m Unmodeled ->
  check_sendmsg i fd msgp flags eff m = CheckUnmodeled.
Proof.
  intros i fd msgp flags m eff H.
  unfold sendmsg_spec in H. unfold check_sendmsg.
  destruct (negb (send_flags_modeled flags)) eqn:Hf; [reflexivity|].
  sys_unfold. cbv iota zeta in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
    hall Hfd; inv_ok; try discriminate; try unm_refl.
  destruct (copy_bytes_map (in_mem i) msgp MSGHDR_SIZE) eqn:Hh;
    hall Hh; inv_ok; try discriminate.
  destruct (read_u64 (in_mem i) msgp) as [name|] eqn:R0,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 8)) as [namelen|] eqn:R1,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 16)) as [iov|] eqn:R2,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 24)) as [iovlen|] eqn:R3,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 32)) as [ctl|] eqn:R4,
           (read_u64 (in_mem i) (msgp + Z_to_bv 64 40)) as [ctllen|] eqn:R5;
    cbv beta iota zeta in *; inv_ok; try discriminate.
  destruct (negb (w_is0 name)) eqn:Hn; hall Hn; inv_ok; [reflexivity|].
  destruct ((IOV_MAX <? bv_unsigned iovlen)%Z) eqn:Hiv; hall Hiv; inv_ok;
    try discriminate.
  destruct ((UIO_FASTIOV <? bv_unsigned iovlen)%Z) eqn:Hfa; hall Hfa; inv_ok;
    [reflexivity|].
  destruct (import_iovecs (in_mem i) iov iovlen) as [iovs0| |]
    eqn:Hci; hall Hci; inv_ok; try discriminate.
  destruct (negb (w_is0 ctllen)) eqn:Hcl; hall Hcl; inv_ok; [reflexivity|].
  destruct (negb (iovs_total (cap_iovecs iovs0) <=? rw_bytes_max)%Z) eqn:Hmt;
    hall Hmt; inv_ok; [reflexivity|].
  exfalso. eapply send_on_socket_no_unmodeled with (i := i). eassumption.
Qed.

(* =========================================================================
   socketpair (199), recvfrom (207), recvmsg (212)

   The [*_frame] lemmas belonging with these are in
   [Checks.VmMapsDisjoint], not here, because that is where the cascade
   over every checker lives: [check_socketpair_frame],
   [check_recvfrom_frame] and [check_recvmsg_frame] are applied there by
   name, and its [fail 1] arm means a dispatcher arm without one fails
   the build.  [check_recv_fd_answer_frame] sits beside them for the
   shared descriptor answer; the two recv proofs unfold
   [check_recv_fd_answer] rather than applying it, so nothing forces it
   to exist and nothing would catch its loss.
   ========================================================================= *)

(** [Specs.recv_fd_answer] as an acceptor: the errno, or the decline a
    socket fd takes at these two entry points. *)
Definition check_recv_fd_answer (fds : list (word * FdEntry)) (fd : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match sockfd_lookup_errno fds fd with
  | Some e => check_ret_only eff (errno_ret e) m []
  | None => CheckUnmodeled
  end.

(** The four directions for the shared descriptor answer, so recvfrom's
    and recvmsg's lemmas each state only what is theirs.  A socket fd
    declines on BOTH sides at once, which is what keeps the pair exact. *)
Lemma check_recv_fd_answer_sound_ok : forall fds fd eff m m' evs i,
  check_recv_fd_answer fds fd eff m = CheckOk m' evs ->
  recv_fd_answer fds fd i m (Ok eff m' evs).
Proof.
  intros fds fd eff m m' evs i H.
  unfold check_recv_fd_answer in H. unfold recv_fd_answer.
  destruct (sockfd_lookup_errno fds fd) as [e|]; [|discriminate].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok.
Qed.


Lemma check_recv_fd_answer_complete_ok : forall fds fd eff m m' evs i,
  recv_fd_answer fds fd i m (Ok eff m' evs) ->
  check_recv_fd_answer fds fd eff m = CheckOk m' evs.
Proof.
  intros fds fd eff m m' evs i H.
  unfold recv_fd_answer in H. unfold check_recv_fd_answer.
  destruct (sockfd_lookup_errno fds fd) as [e|];
    [|unfold unmodeled in H; discriminate].
  unfold err_ret, ret_only, pure in H. inv_ok.
  cbn. rewrite bv_eqb_refl. reflexivity.
Qed.


Lemma check_recv_fd_answer_complete_unmodeled : forall fds fd eff m i,
  recv_fd_answer fds fd i m Unmodeled ->
  check_recv_fd_answer fds fd eff m = CheckUnmodeled.
Proof.
  intros fds fd eff m i H.
  unfold recv_fd_answer in H. unfold check_recv_fd_answer.
  destruct (sockfd_lookup_errno fds fd) as [e|]; [|reflexivity].
  unfold err_ret, ret_only, pure in H. discriminate.
Qed.


Lemma check_recv_fd_answer_no_ok_unmodeled : forall fds fd eff m i,
  check_recv_fd_answer fds fd eff m = CheckUnmodeled ->
  recv_fd_answer fds fd i m Unmodeled.
Proof.
  intros fds fd eff m i H.
  unfold check_recv_fd_answer in H. unfold recv_fd_answer.
  destruct (sockfd_lookup_errno fds fd) as [e|];
    [now apply check_ret_only_no_unmodeled in H|apply unmodeled_intro].
Qed.

(** socketpair's answer once the 8-byte destination is known writable:
    either a reservation errno with [usockvec] untouched, or the two
    descriptor writes with -EOPNOTSUPP or one of the post-write errnos.
    Two shapes, and the write list is what tells them apart — which is
    the fact this whole arm exists to state.  See
    [Specs.socketpair_spec]. *)
Definition check_socketpair_written (sv fd1 fd2 : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU r [] [] [] [] [] =>
      if errno_ret_in socketpair_reserve_errnos r
      then CheckOk m [] else CheckReject
  | mkEffectU r ws [] [] [] [] =>
      if writes_eqb ws (socketpair_writes sv fd1 fd2)
         && (bv_eqb r (errno_ret EOPNOTSUPP)
             || errno_ret_in socketpair_create_errnos r)
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.


Lemma socketpair_written_no_unmodeled : forall sv fd1 fd2 i m,
  ~ socketpair_written sv fd1 fd2 i m Unmodeled.
Proof.
  intros sv fd1 fd2 i m H. unfold socketpair_written in H.
  unfold alt, errno_from, err_ret, ret_only, bind, choose, pure in H.
  destruct H as [H|[H|H]]; inv_ok.
Qed.


Lemma socketpair_faulted_no_unmodeled : forall i m,
  ~ socketpair_faulted i m Unmodeled.
Proof.
  intros i m H. unfold socketpair_faulted in H.
  unfold alt, errno_from, err_ret, ret_only, bind, choose, pure in H.
  destruct H as [H|H]; inv_ok.
Qed.

Lemma check_socketpair_written_sound_ok : forall sv fd1 fd2 eff m m' evs i,
  check_socketpair_written sv fd1 fd2 eff m = CheckOk m' evs ->
  socketpair_written sv fd1 fd2 i m (Ok eff m' evs).
Proof.
  intros sv fd1 fd2 [ret ws zs us cs cis] m m' evs i H.
  unfold check_socketpair_written in H. unfold socketpair_written.
  destruct zs as [|z zs]; [|destruct ws; discriminate].
  destruct us as [|u us]; [|destruct ws; discriminate].
  destruct cs as [|c cs]; [|destruct ws; discriminate].
  destruct cis as [|ci cis]; [|destruct ws; discriminate].
  destruct ws as [|w ws].
  - destruct (errno_ret_in socketpair_reserve_errnos ret) eqn:He; [|discriminate].
    inversion H; clear H; subst m' evs.
    apply errno_ret_in_true in He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0; [apply choose_ok; exact HIn|].
    cbv beta. apply pure_ok.
  - destruct (writes_eqb (w :: ws) (socketpair_writes sv fd1 fd2)
              && (bv_eqb ret (errno_ret EOPNOTSUPP)
                  || errno_ret_in socketpair_create_errnos ret)) eqn:Hg;
      [|discriminate].
    inversion H; clear H; subst m' evs.
    apply andb_true_iff in Hg as [Hws Hr].
    apply writes_eqb_eq in Hws. rewrite Hws.
    apply orb_true_iff in Hr as [Hr|Hr].
    + apply bv_eqb_eq in Hr; subst ret.
      apply alt_r, alt_r, pure_ok.
    + apply errno_ret_in_true in Hr as (e & HIn & ->).
      apply alt_r, alt_l.
      eapply bind_ok0; [apply choose_ok; exact HIn|]. cbv beta. apply pure_ok.
Qed.


Lemma check_socketpair_written_complete_ok : forall sv fd1 fd2 eff m m' evs i,
  socketpair_written sv fd1 fd2 i m (Ok eff m' evs) ->
  check_socketpair_written sv fd1 fd2 eff m = CheckOk m' evs.
Proof.
  intros sv fd1 fd2 eff m m' evs i H.
  unfold socketpair_written in H.
  unfold alt, errno_from, err_ret, ret_only, bind, choose, pure in H.
  unfold check_socketpair_written.
  destruct H as [H|[H|H]]; inv_ok.
  - cbv beta iota. rewrite (errno_ret_in_intro _ _ H). reflexivity.
  - unfold socketpair_writes. cbv beta iota.
    rewrite (proj2 (writes_eqb_eq _ _) eq_refl).
    rewrite (errno_ret_in_intro _ _ H), Bool.orb_true_r. reflexivity.
  - unfold socketpair_writes. cbv beta iota.
    rewrite (proj2 (writes_eqb_eq _ _) eq_refl), bv_eqb_refl. reflexivity.
Qed.


Lemma check_socketpair_written_no_unmodeled : forall sv fd1 fd2 eff m,
  check_socketpair_written sv fd1 fd2 eff m <> CheckUnmodeled.
Proof.
  intros sv fd1 fd2 [ret ws zs us cs cis] m. unfold check_socketpair_written.
  (* Flattened rather than nested: the cascade is over the effect's LIST
     FIELDS, and one more of them arrived with [eff_copyins]. *)
  destruct ws as [|w ws]; destruct zs; destruct us; destruct cs; destruct cis;
    try discriminate;
    [ destruct (errno_ret_in socketpair_reserve_errnos ret)
    | destruct (writes_eqb (w :: ws) (socketpair_writes sv fd1 fd2)
                && (bv_eqb ret (errno_ret EOPNOTSUPP)
                    || errno_ret_in socketpair_create_errnos ret)) ];
    discriminate.
Qed.

(** The same when the FIRST [put_user]'s own 4-byte range is one every
    riscv64 [access_ok] refuses: that store fails, so nothing is
    written on any path. *)
Definition check_socketpair_faulted (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU r [] [] [] [] [] =>
      if errno_ret_in socketpair_reserve_errnos r || bv_eqb r (errno_ret EFAULT)
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.


Lemma check_socketpair_faulted_sound_ok : forall eff m m' evs i,
  check_socketpair_faulted eff m = CheckOk m' evs ->
  socketpair_faulted i m (Ok eff m' evs).
Proof.
  intros [ret ws zs us cs cis] m m' evs i H.
  unfold check_socketpair_faulted in H. unfold socketpair_faulted.
  destruct ws as [|w ws]; [|discriminate].
  destruct zs as [|z zs]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct cis as [|ci cis]; [|discriminate].
  destruct (errno_ret_in socketpair_reserve_errnos ret
            || bv_eqb ret (errno_ret EFAULT)) eqn:Hr; [|discriminate].
  inversion H; clear H; subst m' evs.
  apply orb_true_iff in Hr as [Hr|Hr].
  - apply errno_ret_in_true in Hr as (e & HIn & ->).
    apply alt_l. eapply bind_ok0; [apply choose_ok; exact HIn|].
    cbv beta. apply pure_ok.
  - apply bv_eqb_eq in Hr; subst ret. apply alt_r, pure_ok.
Qed.


Lemma check_socketpair_faulted_complete_ok : forall eff m m' evs i,
  socketpair_faulted i m (Ok eff m' evs) ->
  check_socketpair_faulted eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H. unfold socketpair_faulted in H.
  unfold alt, errno_from, err_ret, ret_only, bind, choose, pure in H.
  unfold check_socketpair_faulted.
  destruct H as [H|H]; inv_ok.
  - cbv beta iota. rewrite (errno_ret_in_intro _ _ H). reflexivity.
  - cbv beta iota. rewrite bv_eqb_refl, Bool.orb_true_r. reflexivity.
Qed.


Lemma check_socketpair_faulted_no_unmodeled : forall eff m,
  check_socketpair_faulted eff m <> CheckUnmodeled.
Proof.
  intros [ret ws zs us cs cis] m. unfold check_socketpair_faulted.
  destruct ws; destruct zs; destruct us; destruct cs; destruct cis;
    try discriminate;
    destruct (errno_ret_in socketpair_reserve_errnos ret
              || bv_eqb ret (errno_ret EFAULT));
    discriminate.
Qed.


(** The AF_UNIX triple's outcome once the destination is known writable
    ([Specs.socketpair_unix_written]): a reservation errno with nothing
    written, a creation errno with both descriptors written, or the
    success, which writes both, returns 0 and installs the two
    [State.FdStream] ends.  The three differ in their stores or their
    return, and only the success moves the model, so the effect names
    the branch and the branch names the model.  ENOMEM is in both errno
    lists, and the write list is what says which one it came from. *)
Definition check_socketpair_unix_written (type sv fd1 fd2 : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let id := stream_new_id (m_fds m) in
  if stream_id_live (m_fds m) id then CheckUnmodeled
  else
  let kb := m_kernel m in
  let st := stream_fresh
              (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 type)) SOCK_NONBLOCK) 0))
              (sysctl_wmem_default kb) (sysctl_rmem_default kb) in
  match eff with
  | mkEffectU r [] [] [] [] [] =>
      if errno_ret_in socketpair_reserve_errnos r then CheckOk m [] else CheckReject
  | mkEffectU r ws [] [] [] [] =>
      if writes_eqb ws (socketpair_writes sv fd1 fd2) then
        if errno_ret_in socketpair_create_errnos r then CheckOk m []
        else if bv_eqb r (Z_to_bv 64 0)
        then CheckOk (with_fds (fd_insert (fd_insert (m_fds m) fd1 (FdStream id false st))
                                          fd2 (FdStream id true st)) m) []
        else CheckReject
      else CheckReject
  | _ => CheckReject
  end.

Lemma check_socketpair_unix_written_sound_ok :
  forall type sv fd1 fd2 eff m m' evs i,
  check_socketpair_unix_written type sv fd1 fd2 eff m = CheckOk m' evs ->
  socketpair_unix_written type sv fd1 fd2 m i m (Ok eff m' evs).
Proof.
  intros type sv fd1 fd2 [ret ws zs us cs cis] m m' evs i H.
  unfold check_socketpair_unix_written in H. unfold socketpair_unix_written.
  cbv zeta in H |- *.
  destruct (stream_id_live (m_fds m) (stream_new_id (m_fds m))) eqn:Hl;
    cbv beta iota in H |- *; [discriminate|].
  destruct zs as [|z zs]; [|destruct ws; discriminate].
  destruct us as [|u us]; [|destruct ws; discriminate].
  destruct cs as [|c cs]; [|destruct ws; discriminate].
  destruct cis as [|ci cis]; [|destruct ws; discriminate].
  destruct ws as [|w ws]; cbv beta iota in H.
  - destruct (errno_ret_in socketpair_reserve_errnos ret) eqn:He; [|discriminate].
    inversion H; clear H; subst m' evs.
    apply errno_ret_in_true in He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0; [apply choose_ok; exact HIn|].
    cbv beta. apply pure_ok.
  - destruct (writes_eqb (w :: ws) (socketpair_writes sv fd1 fd2)) eqn:Hws;
      [|discriminate].
    apply writes_eqb_eq in Hws. rewrite Hws.
    destruct (errno_ret_in socketpair_create_errnos ret) eqn:He.
    + inversion H; clear H; subst m' evs.
      apply errno_ret_in_true in He as (e & HIn & ->).
      apply alt_r, alt_l.
      eapply bind_ok0; [apply choose_ok; exact HIn|]. cbv beta. apply pure_ok.
    + destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:Hr; [|discriminate].
      apply bv_eqb_eq in Hr; subst ret.
      inversion H; clear H; subst m' evs.
      apply alt_r, alt_r.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_socketpair_unix_written_sound_unmodeled :
  forall type sv fd1 fd2 eff m i,
  check_socketpair_unix_written type sv fd1 fd2 eff m = CheckUnmodeled ->
  socketpair_unix_written type sv fd1 fd2 m i m Unmodeled.
Proof.
  intros type sv fd1 fd2 [ret ws zs us cs cis] m i H.
  unfold check_socketpair_unix_written in H. unfold socketpair_unix_written.
  cbv zeta in H |- *.
  destruct (stream_id_live (m_fds m) (stream_new_id (m_fds m))) eqn:Hl;
    cbv beta iota in H |- *; [apply unmodeled_intro|].
  exfalso.
  destruct ws as [|w ws]; destruct zs; destruct us; destruct cs; destruct cis;
    cbv beta iota in H; try discriminate H;
    repeat match type of H with
           | (if ?b then _ else _) = _ =>
               destruct b; cbv beta iota in H; try discriminate H
           end.
Qed.

Lemma check_socketpair_unix_written_complete_ok :
  forall type sv fd1 fd2 eff m m' evs i,
  socketpair_unix_written type sv fd1 fd2 m i m (Ok eff m' evs) ->
  check_socketpair_unix_written type sv fd1 fd2 eff m = CheckOk m' evs.
Proof.
  intros type sv fd1 fd2 eff m m' evs i H.
  unfold socketpair_unix_written in H. unfold check_socketpair_unix_written.
  cbv zeta in H |- *.
  destruct (stream_id_live (m_fds m) (stream_new_id (m_fds m))) eqn:Hl;
    cbv beta iota in H |- *; [unfold unmodeled in H; discriminate|].
  unfold alt, errno_from, err_ret, ret_only, bind, choose, pure, set_fds, modify in H.
  destruct H as [H|[H|H]]; inv_ok.
  - cbv beta iota.
    match goal with HIn : In _ socketpair_reserve_errnos |- _ =>
      rewrite (errno_ret_in_intro _ _ HIn) end.
    reflexivity.
  - unfold socketpair_writes. cbv beta iota.
    rewrite (proj2 (writes_eqb_eq _ _) eq_refl).
    match goal with HIn : In _ socketpair_create_errnos |- _ =>
      rewrite (errno_ret_in_intro _ _ HIn) end.
    reflexivity.
  - unfold socketpair_writes. cbv beta iota.
    rewrite (proj2 (writes_eqb_eq _ _) eq_refl).
    replace (errno_ret_in socketpair_create_errnos (Z_to_bv 64 0)) with false
      by (vm_compute; reflexivity).
    rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma check_socketpair_unix_written_complete_unmodeled :
  forall type sv fd1 fd2 eff m i,
  socketpair_unix_written type sv fd1 fd2 m i m Unmodeled ->
  check_socketpair_unix_written type sv fd1 fd2 eff m = CheckUnmodeled.
Proof.
  intros type sv fd1 fd2 eff m i H.
  unfold socketpair_unix_written in H. unfold check_socketpair_unix_written.
  cbv zeta in H |- *.
  destruct (stream_id_live (m_fds m) (stream_new_id (m_fds m))) eqn:Hl;
    cbv beta iota in H |- *; [reflexivity|].
  exfalso.
  unfold alt, errno_from, err_ret, ret_only, bind, choose, pure, set_fds, modify in H.
  destruct H as [H|[H|H]]; inv_ok.
Qed.

(** socketpair(2): the flag gate, then the triples the model judges --
    AF_INET's two, which end in -EOPNOTSUPP, and AF_UNIX's
    stream triple, which succeeds -- then the reservation and the
    destination, which every judged triple shares. *)
Definition check_socketpair (i : SyscallInput) (family type protocol sv : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (socketpair_flags_ok type)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (socketpair_modeled_b family type protocol
                || socketpair_unix_b family type protocol)%bool
  then CheckUnmodeled
  else
  match socketpair_fds (m_fds m) with
  | None => CheckUnmodeled
  | Some (fd1, fd2) =>
      if socketpair_dest_writable (in_wmem i) sv
      then (if socketpair_unix_b family type protocol
            then check_socketpair_unix_written type sv fd1 fd2 eff m
            else check_socketpair_written sv fd1 fd2 eff m)
      else
        (* 4, not 8, and the walk is guarded by [State.access_okb]
           before it is consulted: see [Specs.socketpair_spec]. *)
        if negb (access_okb sv 4)
        then check_socketpair_faulted eff m
        else CheckUnmodeled
  end.


Lemma check_socketpair_sound_ok : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs ->
  socketpair_spec family type protocol sv i m (Ok eff m' evs).
Proof.
  intros i family type protocol sv eff m m' evs H.
  unfold check_socketpair in H. unfold socketpair_spec.
  destruct (negb (socketpair_flags_ok type)) eqn:Hfl; cbv beta iota in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (socketpair_modeled_b family type protocol
                  || socketpair_unix_b family type protocol)%bool) eqn:Hmo;
    cbv beta iota in H |- *; [discriminate|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (socketpair_fds (m_fds m)) as [[fd1 fd2]|] eqn:Hfds;
    cbv beta iota in H |- *; [|discriminate].
  destruct (socketpair_dest_writable (in_wmem i) sv) eqn:Hmem;
    cbv beta iota in H |- *.
  - destruct (socketpair_unix_b family type protocol) eqn:Hu;
      cbv beta iota in H |- *.
    + now apply check_socketpair_unix_written_sound_ok.
    + now apply check_socketpair_written_sound_ok.
  - destruct (negb (access_okb sv 4)) eqn:Ho; cbv beta iota in H |- *;
      [|discriminate].
    now apply check_socketpair_faulted_sound_ok.
Qed.


Lemma check_socketpair_sound_unmodeled : forall i family type protocol sv eff m,
  check_socketpair i family type protocol sv eff m = CheckUnmodeled ->
  socketpair_spec family type protocol sv i m Unmodeled.
Proof.
  intros i family type protocol sv eff m H.
  unfold check_socketpair in H. unfold socketpair_spec.
  destruct (negb (socketpair_flags_ok type)) eqn:Hfl; cbv beta iota in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (socketpair_modeled_b family type protocol
                  || socketpair_unix_b family type protocol)%bool) eqn:Hmo;
    cbv beta iota in H |- *; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (socketpair_fds (m_fds m)) as [[fd1 fd2]|] eqn:Hfds;
    cbv beta iota in H |- *; [|apply unmodeled_intro].
  destruct (socketpair_dest_writable (in_wmem i) sv) eqn:Hmem;
    cbv beta iota in H |- *.
  - destruct (socketpair_unix_b family type protocol) eqn:Hu;
      cbv beta iota in H |- *.
    + eapply check_socketpair_unix_written_sound_unmodeled. exact H.
    + now apply check_socketpair_written_no_unmodeled in H.
  - destruct (negb (access_okb sv 4)) eqn:Ho; cbv beta iota in H |- *;
      [now apply check_socketpair_faulted_no_unmodeled in H
      |apply unmodeled_intro].
Qed.


Lemma check_socketpair_complete_ok :
  forall i family type protocol sv eff m m' evs,
  socketpair_spec family type protocol sv i m (Ok eff m' evs) ->
  check_socketpair i family type protocol sv eff m = CheckOk m' evs.
Proof.
  intros i family type protocol sv eff m m' evs H.
  unfold socketpair_spec in H. unfold check_socketpair.
  destruct (negb (socketpair_flags_ok type)) eqn:Hfl; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inv_ok.
    apply check_ret_only_ok_iff. now repeat split. }
  destruct (negb (socketpair_modeled_b family type protocol
                  || socketpair_unix_b family type protocol)%bool) eqn:Hmo;
    cbv beta iota in H |- *; [unfold unmodeled in H; discriminate|].
  apply bind_input_model_inv in H. cbv beta in H.
  destruct (socketpair_fds (m_fds m)) as [[fd1 fd2]|] eqn:Hfds;
    cbv beta iota in H |- *; [|unfold unmodeled in H; discriminate].
  destruct (socketpair_dest_writable (in_wmem i) sv) eqn:Hmem;
    cbv beta iota in H |- *.
  - destruct (socketpair_unix_b family type protocol) eqn:Hu;
      cbv beta iota in H |- *.
    + eapply check_socketpair_unix_written_complete_ok. exact H.
    + now apply check_socketpair_written_complete_ok in H.
  - destruct (negb (access_okb sv 4)) eqn:Ho;
      cbv beta iota in H |- *; [|unfold unmodeled in H; discriminate].
    now apply check_socketpair_faulted_complete_ok in H.
Qed.


Lemma check_socketpair_complete_unmodeled :
  forall i family type protocol sv m eff,
  socketpair_spec family type protocol sv i m Unmodeled ->
  check_socketpair i family type protocol sv eff m = CheckUnmodeled.
Proof.
  intros i family type protocol sv m eff H.
  unfold socketpair_spec in H. unfold check_socketpair.
  destruct (negb (socketpair_flags_ok type)) eqn:Hfl; cbv beta iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate. }
  destruct (negb (socketpair_modeled_b family type protocol
                  || socketpair_unix_b family type protocol)%bool) eqn:Hmo;
    cbv beta iota in H |- *; [reflexivity|].
  apply bind_input_model_inv in H. cbv beta in H.
  destruct (socketpair_fds (m_fds m)) as [[fd1 fd2]|] eqn:Hfds;
    cbv beta iota in H |- *; [|reflexivity].
  destruct (socketpair_dest_writable (in_wmem i) sv) eqn:Hmem;
    cbv beta iota in H |- *.
  - destruct (socketpair_unix_b family type protocol) eqn:Hu;
      cbv beta iota in H |- *.
    + eapply check_socketpair_unix_written_complete_unmodeled. exact H.
    + now apply socketpair_written_no_unmodeled in H.
  - destruct (negb (access_okb sv 4)) eqn:Ho;
      cbv beta iota in H |- *; [|reflexivity].
    now apply socketpair_faulted_no_unmodeled in H.
Qed.

(* ------------------------------------------------------------- recvfrom *)

(** recvfrom: the buffer's range verdict first (the kernel imports it
    before it resolves the descriptor), then the descriptor.  A
    stream-pair end is answered by [Fs.ReadWrite.check_stream_read]
    under the two declines [Specs.recvfrom_spec] keeps -- a flag other
    than MSG_DONTWAIT, and a source address to fill -- with the file's
    O_NONBLOCK or the call's MSG_DONTWAIT as the read's [nonblock].
    Every other descriptor moves no byte, so [check_recv_fd_answer]
    under [check_access_ok_zero] is exactly the right acceptor there.
    See [Specs.recvfrom_spec]. *)
Definition check_recvfrom (i : SyscallInput) (fd buf size : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (modeled_rw_count size) then CheckUnmodeled
  else check_access_ok_zero buf size eff m
         (match fd_lookup (m_fds m) fd with
          | Some (FdStream id side st) =>
              if negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 (in_arg i 3)))
                                      MSG_DONTWAIT) 0)
              then CheckUnmodeled
              else if negb (w_is0 (in_arg i 4)) then CheckUnmodeled
              else check_stream_read fd id side st
                     (se_nonblock st
                      || negb (Z.eqb (Z.land (bv_unsigned (abi_low32 (in_arg i 3)))
                                             MSG_DONTWAIT) 0))%bool
                     buf size i eff m
          | _ => check_recv_fd_answer (m_fds m) fd eff m
          end).


Lemma check_recvfrom_sound_ok : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs ->
  recvfrom_spec fd buf size i m (Ok eff m' evs).
Proof.
  intros i fd buf size eff m m' evs H.
  unfold check_recvfrom in H. unfold recvfrom_spec.
  destruct (negb (modeled_rw_count size)) eqn:Hc; cbv beta iota in H |- *;
    [discriminate|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  ok_zero_cases H buf size.
  - destruct (fd_lookup (m_fds m) fd)
      as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
      cbv beta iota zeta in H |- *;
      try (now apply check_recv_fd_answer_sound_ok).
    destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 (in_arg i 3)))
                                   MSG_DONTWAIT) 0)) eqn:Hfl;
      cbv beta iota in H |- *; [discriminate|].
    destruct (negb (w_is0 (in_arg i 4))) eqn:Ha; cbv beta iota in H |- *;
      [discriminate|].
    eapply check_stream_read_sound_ok. exact H.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok.
Qed.


Lemma check_recvfrom_sound_unmodeled : forall i fd buf size eff m,
  check_recvfrom i fd buf size eff m = CheckUnmodeled ->
  recvfrom_spec fd buf size i m Unmodeled.
Proof.
  intros i fd buf size eff m H.
  unfold check_recvfrom in H. unfold recvfrom_spec.
  destruct (negb (modeled_rw_count size)) eqn:Hc; cbv beta iota in H |- *;
    [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  ok_zero_cases H buf size.
  - destruct (fd_lookup (m_fds m) fd)
      as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
      cbv beta iota zeta in H |- *;
      try (eapply check_recv_fd_answer_no_ok_unmodeled; exact H).
    destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 (in_arg i 3)))
                                   MSG_DONTWAIT) 0)) eqn:Hfl;
      cbv beta iota in H |- *; [apply unmodeled_intro|].
    destruct (negb (w_is0 (in_arg i 4))) eqn:Ha; cbv beta iota in H |- *;
      [apply unmodeled_intro|].
    eapply check_stream_read_sound_unmodeled. exact H.
  - now apply check_ret_only_no_unmodeled in H.
Qed.


Lemma check_recvfrom_complete_ok : forall i fd buf size eff m m' evs,
  recvfrom_spec fd buf size i m (Ok eff m' evs) ->
  check_recvfrom i fd buf size eff m = CheckOk m' evs.
Proof.
  intros i fd buf size eff m m' evs H.
  unfold recvfrom_spec in H. unfold check_recvfrom.
  destruct (negb (modeled_rw_count size)) eqn:Hc; cbv beta iota in H |- *;
    [unfold unmodeled in H; discriminate|].
  apply bind_input_model_inv in H. cbv beta in H.
  unfold access_ok_zero in H. unfold check_access_ok_zero.
  destruct (access_okb buf (bv_unsigned size)) eqn:Hok;
    cbv beta iota in H |- *.
  - destruct (fd_lookup (m_fds m) fd)
      as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
      cbv beta iota zeta in H |- *;
      try (eapply check_recv_fd_answer_complete_ok; exact H).
    destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 (in_arg i 3)))
                                   MSG_DONTWAIT) 0)) eqn:Hfl;
      cbv beta iota in H |- *; [unfold unmodeled in H; discriminate|].
    destruct (negb (w_is0 (in_arg i 4))) eqn:Ha; cbv beta iota in H |- *;
      [unfold unmodeled in H; discriminate|].
    eapply check_stream_read_complete_ok. exact H.
  - unfold err_ret, ret_only, pure in H. inv_ok.
    apply check_ret_only_ok_iff. now repeat split.
Qed.


Lemma check_recvfrom_complete_unmodeled : forall i fd buf size m eff,
  recvfrom_spec fd buf size i m Unmodeled ->
  check_recvfrom i fd buf size eff m = CheckUnmodeled.
Proof.
  intros i fd buf size m eff H.
  unfold recvfrom_spec in H. unfold check_recvfrom.
  destruct (negb (modeled_rw_count size)) eqn:Hc; cbv beta iota in H |- *;
    [reflexivity|].
  apply bind_input_model_inv in H. cbv beta in H.
  unfold access_ok_zero in H. unfold check_access_ok_zero.
  destruct (access_okb buf (bv_unsigned size)) eqn:Hok;
    cbv beta iota in H |- *.
  - destruct (fd_lookup (m_fds m) fd)
      as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |id side st|ctx|fam|aid af]|] eqn:Hfd;
      cbv beta iota zeta in H |- *;
      try (eapply check_recv_fd_answer_complete_unmodeled; exact H).
    destruct (negb (Z.eqb (Z.ldiff (bv_unsigned (abi_low32 (in_arg i 3)))
                                   MSG_DONTWAIT) 0)) eqn:Hfl;
      cbv beta iota in H |- *; [reflexivity|].
    destruct (negb (w_is0 (in_arg i 4))) eqn:Ha; cbv beta iota in H |- *;
      [reflexivity|].
    eapply check_stream_read_complete_unmodeled. exact H.
  - unfold err_ret, ret_only, pure in H. discriminate.
Qed.

(* -------------------------------------------------------------- recvmsg *)

(** recvmsg: MSG_CMSG_COMPAT is fail-closed (its value is a kernel
    configuration), and otherwise the descriptor alone decides — the
    message header is never read.  See [Specs.recvmsg_spec]. *)
Definition check_recvmsg (fd flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags)) MSG_CMSG_COMPAT) 0)
  then CheckUnmodeled
  else check_recv_fd_answer (m_fds m) fd eff m.


Lemma check_recvmsg_sound_ok : forall fd flags eff m m' evs i,
  check_recvmsg fd flags eff m = CheckOk m' evs ->
  recvmsg_spec fd flags i m (Ok eff m' evs).
Proof.
  intros fd flags eff m m' evs i H.
  unfold check_recvmsg in H. unfold recvmsg_spec.
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags))
                                MSG_CMSG_COMPAT) 0)) eqn:Hf;
    cbv beta iota in H |- *; [discriminate|].
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  now apply check_recv_fd_answer_sound_ok.
Qed.


Lemma check_recvmsg_sound_unmodeled : forall fd flags eff m i,
  check_recvmsg fd flags eff m = CheckUnmodeled ->
  recvmsg_spec fd flags i m Unmodeled.
Proof.
  intros fd flags eff m i H.
  unfold check_recvmsg in H. unfold recvmsg_spec.
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags))
                                MSG_CMSG_COMPAT) 0)) eqn:Hf;
    cbv beta iota in H |- *; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  now eapply check_recv_fd_answer_no_ok_unmodeled; exact H.
Qed.


Lemma check_recvmsg_complete_ok : forall fd flags eff m m' evs i,
  recvmsg_spec fd flags i m (Ok eff m' evs) ->
  check_recvmsg fd flags eff m = CheckOk m' evs.
Proof.
  intros fd flags eff m m' evs i H.
  unfold recvmsg_spec in H. unfold check_recvmsg.
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags))
                                MSG_CMSG_COMPAT) 0)) eqn:Hf;
    cbv beta iota in H |- *; [unfold unmodeled in H; discriminate|].
  apply bind_model_inv in H.
  now apply check_recv_fd_answer_complete_ok in H.
Qed.


Lemma check_recvmsg_complete_unmodeled : forall fd flags m eff i,
  recvmsg_spec fd flags i m Unmodeled ->
  check_recvmsg fd flags eff m = CheckUnmodeled.
Proof.
  intros fd flags m eff i H.
  unfold recvmsg_spec in H. unfold check_recvmsg.
  destruct (negb (Z.eqb (Z.land (bv_unsigned (abi_low32 flags))
                                MSG_CMSG_COMPAT) 0)) eqn:Hf;
    cbv beta iota in H |- *; [reflexivity|].
  apply bind_model_inv in H.
  now eapply check_recv_fd_answer_complete_unmodeled; exact H.
Qed.
