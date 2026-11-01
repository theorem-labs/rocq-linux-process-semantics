(** * LinuxProcessSem.Checks.Cases.Net.Socket — worked examples over socket (198),
      bind (200), listen (201), accept (202), connect (203),
      getsockname (204), getpeername (205), sendto (206), setsockopt (208),
      getsockopt (209), shutdown (210), sendmsg (211), accept4 (242)

    Mirrors [Sys/Net/Socket.v], which answers to Linux [net/socket.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export Prelude.

(* -------------------------------------------------------------------------
   Sockets: the claims no live run can show
   ------------------------------------------------------------------------- *)

(** WRITING A CONNECTED SOCKET IS NEVER ADMITTED — no execution, no
    input, no buffer.  It is a lemma for two reasons.  It is UNIVERSALLY
    QUANTIFIED, where a live run exhibits one execution.  And a guest
    cannot reach the arm on its own: reaching it needs a CONNECTED
    socket.  [connect] (203) is dispatched, but it cannot produce one:
    [Net.Socket.connect_spec] declines the connection ATTEMPT, so no
    modeled execution ever holds a connected socket it dialled.

    What keeps the connected states out is the TRANSFER, not the
    signal.  On [SkConnected] the send either goes out -- a short count
    chosen from the gatherable bytes, which is [Net.Socket.send_bytes]'s
    business -- or reports a pending peer error ONCE and rewrites the
    descriptor (include/net/sock.h [sock_error]), and neither raises
    SIGPIPE: [sk_stream_error] replaces the errno with [sock_error]'s
    before it tests for -EPIPE (net/core/stream.c :192-195, v6.18.46).

    A socket with NO connection ([State.sock_send_dead]: fresh, bound,
    listening or reset-and-consumed) IS answered, and that is why the
    hypothesis below is here: [vfs_write]'s [access_ok] gives -EFAULT,
    and past it [sk_stream_wait_connect] gives -EPIPE and
    [sk_stream_error] sends SIGPIPE, which [ReadWrite.raise_sigpipe]
    records as a death ([State.with_killed], [Run.sstep_killed]) or,
    with signal 13 blocked, as a pending signal and the -EPIPE.  The
    model used to decline those too, because a spec could not say "the
    process died"; it can now.  A later change that admits a write to a
    CONNECTED socket breaks this lemma, which is the point of stating
    it. *)
Lemma socket_write_never_admitted : forall fd buf count i m sk o,
  fd_lookup (m_fds m) fd = Some (FdSocket sk) ->
  sock_send_dead sk = false ->
  write_spec fd buf count i m o -> o = Unmodeled.
Proof.
  intros fd buf count i m sk o Hfd Hlive Hspec.
  destruct o as [y m2 evs|]; [|reflexivity]. exfalso.
  unfold write_spec, bind, input, get_model, unmodeled in Hspec.
  destruct Hspec as (x & m1 & evs1 & evs2 & Hin & Hrest & _).
  injection Hin as -> -> ->.
  destruct Hrest as (x' & m1' & evs1' & evs2' & Hgm & Hrest' & _).
  injection Hgm as -> -> ->.
  rewrite Hfd in Hrest'. cbv iota in Hrest'.
  rewrite Hlive in Hrest'. cbn [negb] in Hrest'. discriminate.
Qed.

(** The same for the vectored form, AT EVERY COUNT.  There is no bound
    on [iovcnt] here, and that is the whole content of the lemma: the
    socket arm of [Specs.writev_spec] is [Specs.writev_buf_gap] before
    the count or the array is looked at, so no count — over [IOV_MAX] or
    not — reaches an answer. *)
Lemma socket_writev_never_admitted : forall fd iov iovcnt i m sk o,
  fd_lookup (m_fds m) fd = Some (FdSocket sk) ->
  writev_spec fd iov iovcnt i m o -> o = Unmodeled.
Proof.
  intros fd iov iovcnt i m sk o Hfd Hspec.
  destruct o as [y m2 evs|]; [|reflexivity]. exfalso.
  unfold writev_spec, bind, input, get_model in Hspec.
  destruct Hspec as (x & m1 & evs1 & evs2 & Hin & Hrest & _).
  injection Hin as -> -> ->.
  destruct Hrest as (x' & m1' & evs1' & evs2' & Hgm & Hrest' & _).
  injection Hgm as -> -> ->.
  rewrite Hfd in Hrest'. cbv iota in Hrest'.
  unfold writev_buf_gap, unmodeled in Hrest'. discriminate.
Qed.

(** A SOCKET PASSES THE [FMODE_READ] GATE.  Answering [None] here would
    compile instantly, need no new arm downstream, and green the whole
    readv proof stack — while turning [readv] on a socket into a FALSE
    -EBADF: a modeled wrong answer rather than a modeling gap, invisible
    to [Equivalence.modeled] and unreachable by any fail-closed arm.
    net/socket.c:sock_alloc_file creates every socket file with
    [O_RDWR | (flags & O_NONBLOCK)], so FMODE_READ is always set.  One
    line, stated because the mistake is silent. *)
Lemma socket_is_readable : forall sk,
  readable_fd (FdSocket sk) = Some (RdSocket sk).
Proof. reflexivity. Qed.

(** THE CHANNEL SEPARATION, with its bound made explicit rather than
    left implicit.  [conn_channel ix] is [ix + 3] in a 64-bit word, so
    below the wrap two connections never share a channel and no
    connection is reported on stdin's (0), stdout's (1) or stderr's (2).
    AT the wrap both fail: at [ix = 2 ^ 64 - 3] the next connection is
    reported on channel 0, and a target could then read that connection
    where the source read stdin and produce the same trace.  Nothing in
    the model bounds the number of accepts — [Run.run]'s [lim] is the
    allocation budget in bytes, not a step count — so the hypothesis is
    a real restriction and not a formality.

    [Net.Socket.accept4_spec]'s guard is what DISCHARGES it: it refuses
    to hand a connection over from [ix = 2^64 - 3] on, so every index the
    model actually issues a channel at satisfies this hypothesis.
    [guarded_conn_channel_not_std] and [guarded_conn_channel_injective]
    below are these two with the hypothesis replaced by the guard's own
    test, and are the forms to cite. *)
Lemma conn_channel_unsigned : forall ix,
  (bv_unsigned ix < 2 ^ 64 - 3)%Z ->
  bv_unsigned (conn_channel ix) = (bv_unsigned ix + 3)%Z.
Proof.
  intros ix H. unfold conn_channel.
  pose proof (bv_unsigned_in_range 64 ix) as Hr.
  change (bv_modulus 64) with (2 ^ 64)%Z in Hr.
  rewrite bv_add_unsigned, Z_to_bv_small, bv_wrap_small
    by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  reflexivity.
Qed.

Lemma conn_channel_injective : forall ix1 ix2,
  (bv_unsigned ix1 < 2 ^ 64 - 3)%Z ->
  (bv_unsigned ix2 < 2 ^ 64 - 3)%Z ->
  conn_channel ix1 = conn_channel ix2 -> bv_unsigned ix1 = bv_unsigned ix2.
Proof.
  intros ix1 ix2 H1 H2 Heq.
  pose proof (conn_channel_unsigned _ H1). pose proof (conn_channel_unsigned _ H2).
  rewrite Heq in *. lia.
Qed.

Lemma conn_channel_not_std : forall ix,
  (bv_unsigned ix < 2 ^ 64 - 3)%Z ->
  (2 < bv_unsigned (conn_channel ix))%Z.
Proof.
  intros ix H. rewrite (conn_channel_unsigned _ H).
  pose proof (bv_unsigned_in_range 64 ix). lia.
Qed.

(* -------------------------------------------------------------------------
   Sockets: an ACCEPTED socket, and the MEMBERSHIP of accept's errno set

   A guest cannot dial an accepted socket itself, since [connect] (203)
   declines the connection ATTEMPT.  A live run where a connection
   arrives shows a successful accept, not the errno set, so each errno
   below is presented to the checker by hand.  The listening socket is
   built here for the same reason — the set is folded over without a
   run.

   These cases are what pins WHICH errnos [Specs.accept_errnos] holds.
   [Checks/Progress.v]'s receptivity witness takes the errno side of
   the [alt] and needs only that the list is NON-EMPTY, and
   non-emptiness is not membership — so without these cases a model
   that hung an arbitrary errno off accept would pass every theorem in
   the proof stack.
   ------------------------------------------------------------------------- *)

(** A model whose fd 3 is a LISTENING socket, written out rather than
    reached.  fds 0-2 are the standard channels, exactly as
    [State.init_model] leaves them, so the descriptor an accept has to
    hand back is 4 — a fact about this table, not a number chosen to
    make a case pass.

    [State.mkModel] leaves the accept queue at [State.net_silent] and
    the handed-over count at 0, which is what an unaccepted listening
    socket wants; the credentials are set to [demo_creds] so this model
    runs as the same ordinary user every other worked example does. *)
Definition listening_socket_model : Model :=
  with_creds demo_creds
    (mkModel
       [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
         (3, FdSocket SkListening) ]
       (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None).

(** The model a successful accept must leave behind.  The new
    descriptor carries the head connection's peer and its script, on the
    channel [Specs.conn_channel] names for it (3 — the first channel
    that is not stdio); the queue has advanced past the connection just
    taken; and the handed-over count is 1.  [State.fd_insert] prepends,
    which is why the new entry heads the table.

    Those last two are exactly what [State.with_accepted] does and the
    only way to say them — it is the sole setter that advances the queue
    and bumps [m_conn_ix], and the fd table it is given here is written
    out in full rather than derived. *)
Definition accepted_socket_model : Model :=
  with_accepted
    [ (4, FdSocket (SkConnected (mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0)) 3 NFin));
      (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdSocket SkListening) ]
    listening_socket_model.

(** accept4(3, NULL, NULL, 0) — syscall 242, the arm that takes its
    flags from a4 rather than pinning them to 0 — answering [r]. *)
Definition accept4_answering (m : Model) (r : word) : check_result :=
  check_syscall (mkInput 242 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect r [] []) m.

(** THE ACCEPTED STATE, reached.  Everything the success arm builds is
    pinned in one equality: the descriptor, the peer, the channel, the
    remaining script, the advanced queue, and the bumped count. *)
Example accept_hands_over_the_head_connection :
  accept4_answering listening_socket_model 4 = CheckOk accepted_socket_model [].
Proof. check_eq. Qed.

(** Was a return ADMITTED?  [CheckOk] and nothing else — a
    [CheckUnmodeled] is the model declining to answer, not accepting. *)
Definition accept4_admits (r : word) : bool :=
  match accept4_answering listening_socket_model r with
  | CheckOk _ _ => true
  | _ => false
  end.

(** THE MEMBERSHIP OF [Specs.accept_errnos], pinned as a SET and not as
    a head.  Of every value the model's error window can encode —
    [Prelude.errnos_ok] admits exactly 1..4095 — the accept arm
    accepts these THREE and refuses the other 4092.  Dropping an errno
    from the list breaks this case, and so does adding one: that is the
    difference between pinning a set and naming its head, and it is what
    stops an arbitrary errno from being hung off accept unnoticed.
    The order here is [filter]'s, hence numeric (12, 23, 24), not the
    order [Specs.accept_errnos] is written in. *)
Example accept_errno_set_is_exactly_these_three :
  filter (fun e => accept4_admits (errno_ret e)) (map Z.of_nat (seq 1 4095))
  = [ENOMEM; ENFILE; EMFILE].
Proof. vm_compute. reflexivity. Qed.

(** The success side is a set of one, pinned the same way: over every
    descriptor [State.alloc_fd]'s 4096-candidate scan could name, only
    the lowest free one is admitted.  Four of the 4096 (0, 1, 2, 3) are
    refused earlier still, because they are already open — a return that
    reissues a live descriptor is rejected before it is compared with
    the allocator's answer. *)
Example accept_success_return_is_exactly_the_lowest_free_fd :
  filter (fun n => accept4_admits (Z_to_bv 64 n)) (map Z.of_nat (seq 0 4096))
  = [4%Z].
Proof. vm_compute. reflexivity. Qed.

(** The three spelled out one at a time — the enumeration above in the
    form a reader checks by eye.  An admitted errno leaves the model
    ALONE: no descriptor is handed out and the connection stays at the
    head of the queue, because steps 1 through 7 of [do_accept] reach
    [reqsk_queue_remove] only once every error exit is past. *)
Example accept_errno_arms_leave_the_queue_alone :
  accept4_answering listening_socket_model (errno_ret ENOMEM)
    = CheckOk listening_socket_model []
  /\ accept4_answering listening_socket_model (errno_ret EMFILE)
    = CheckOk listening_socket_model []
  /\ accept4_answering listening_socket_model (errno_ret ENFILE)
    = CheckOk listening_socket_model [].
Proof. split; [|split]; check_eq. Qed.

(** Three errnos a real accept CAN return and this model must not.
    -EAGAIN is a non-blocking socket's, and the model has no notion of
    one ([SOCK_NONBLOCK] is declined as unmodeled rather than recorded);
    -EINTR needs a signal, and there are none; -EOPNOTSUPP is for a
    socket type that cannot accept, and only AF_INET/SOCK_STREAM sockets
    ever enter the fd table.  Each is refused, and refusing them is what
    makes the list above a set rather than a lower bound. *)
Example accept_refuses_errnos_outside_the_set :
  accept4_answering listening_socket_model (errno_ret EAGAIN) = CheckReject
  /\ accept4_answering listening_socket_model (errno_ret EINTR) = CheckReject
  /\ accept4_answering listening_socket_model (errno_ret EOPNOTSUPP)
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** The arms AROUND the accepted state, in the kernel's order.  The
    socket accept just handed over is not TCP_LISTEN, so accepting it is
    -EINVAL; a channel fd is -ENOTSOCK; an unknown fd is -EBADF, decided
    by [fdget] BEFORE the flags are looked at (fd 9 here carries a flag
    bit that would otherwise be -EINVAL); an unknown flag bit is
    -EINVAL; and [SOCK_CLOEXEC] is accepted and ignored, so it lands on
    the same accepted state as no flags at all. *)
Example accept_arms_around_the_accepted_state :
  check_syscall (mkInput 242 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) accepted_socket_model
    = CheckOk accepted_socket_model []
  /\ check_syscall (mkInput 242 [1; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTSOCK) [] []) listening_socket_model
     = CheckOk listening_socket_model []
  /\ check_syscall (mkInput 242 [9; 0; 0; 1; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) listening_socket_model
     = CheckOk listening_socket_model []
  /\ check_syscall (mkInput 242 [3; 0; 0; 1; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) listening_socket_model
     = CheckOk listening_socket_model []
  /\ check_syscall (mkInput 242 [3; 0; 0; 524288; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 4 [] []) listening_socket_model
     = CheckOk accepted_socket_model [].
Proof. split; [|split; [|split; [|split]]]; check_eq. Qed.

(** The two arguments the model DECLINES rather than guesses stay
    [CheckUnmodeled] on a listening socket — the state where an errno or
    a descriptor would otherwise be admissible.  Neither is an errno,
    and neither may become one by accident: [SOCK_NONBLOCK] marks the
    new file O_NONBLOCK, which the model cannot represent, and a
    non-NULL address argument would report a peer address the model
    cannot predict. *)
Example accept_declined_arguments_are_unmodeled :
  check_syscall (mkInput 242 [3; 0; 0; 2048; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 4 [] []) listening_socket_model = CheckUnmodeled
  /\ check_syscall (mkInput 242 [3; 4096; 4104; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 4 [] []) listening_socket_model = CheckUnmodeled
  (* AND THE FLAG BIT THAT IS ACCEPTED, so the two declines above read as
     a boundary rather than as accept4 having gone quiet.  Both are
     [CheckUnmodeled], so on their own they survive any change that only
     ever declines MORE -- the flag word growing a third refused bit, or
     the whole arm going unmodeled -- which is the change this lemma
     exists to notice.  [SOCK_CLOEXEC] is the neighbour in the same
     word: accepted, ignored, and landing on the accepted state. *)
  /\ check_syscall (mkInput 242 [3; 0; 0; 524288; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 4 [] []) listening_socket_model
     = CheckOk accepted_socket_model [].
Proof. split; [|split]; check_eq. Qed.


(* -------------------------------------------------------------------------
   Sockets: the channel space runs out before it wraps

   All of these are here for reason 4 at the top of [Checks/Examples.v] —
   the environment cannot be made to produce them — with reason 3 on top:
   [State.m_conn_ix] is model-internal state, and driving it to the value
   these cases pin needs 2^64 successful accepts, which no real run can
   perform and no observation of a real run would reveal if it could.
   ------------------------------------------------------------------------- *)

(** WHAT THE GUARD PREVENTS, stated first so the rest of the group reads
    as a fix rather than as arithmetic.  At [ix = 2^64 - 3] the channel
    [Net.Socket.conn_channel] names is 0 — STDIN's — and at the two
    indices after it, stdout's and stderr's.  A target could then read a
    CONNECTION where the source read STANDARD INPUT and emit the same
    trace, so [Equivalence.equiv] would hold between two programs that do
    different things and [Equivalence.strong_universal_T] would be
    satisfied by a target that is not equivalent.  That is what makes
    this an unsoundness in the top-level theorem rather than a caveat on
    a helper lemma. *)
Example conn_channel_at_the_wrap_is_stdin_stdout_stderr :
  bv_unsigned (conn_channel (Z_to_bv 64 (two_pow_64 - 3))) = 0%Z
  /\ bv_unsigned (conn_channel (Z_to_bv 64 (two_pow_64 - 2))) = 1%Z
  /\ bv_unsigned (conn_channel (Z_to_bv 64 (two_pow_64 - 1))) = 2%Z.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(** [Net.Socket.conn_ix_exhausted] is exactly the complement of the
    hypothesis [conn_channel_not_std] and [conn_channel_injective] carry,
    which is what turns those two from lemmas with an assumption into
    lemmas about every index [accept] will still hand a connection over
    at.  The guard tests this at the hand-over itself, so the separation
    is POINTWISE and needs no run-level induction to state. *)
Lemma conn_ix_not_exhausted_lt : forall ix,
  conn_ix_exhausted ix = false -> (bv_unsigned ix < two_pow_64 - 3)%Z.
Proof. intros ix H. unfold conn_ix_exhausted in H. now apply Z.leb_gt in H. Qed.

Lemma guarded_conn_channel_not_std : forall ix,
  conn_ix_exhausted ix = false -> (2 < bv_unsigned (conn_channel ix))%Z.
Proof.
  intros ix H. apply conn_channel_not_std.
  apply conn_ix_not_exhausted_lt in H. unfold two_pow_64 in H. exact H.
Qed.

Lemma guarded_conn_channel_injective : forall ix1 ix2,
  conn_ix_exhausted ix1 = false -> conn_ix_exhausted ix2 = false ->
  conn_channel ix1 = conn_channel ix2 -> bv_unsigned ix1 = bv_unsigned ix2.
Proof.
  intros ix1 ix2 H1 H2. apply conn_channel_injective;
    [apply conn_ix_not_exhausted_lt in H1 | apply conn_ix_not_exhausted_lt in H2];
    unfold two_pow_64 in *; assumption.
Qed.

(** [listening_socket_model] with the counter parked at the last index
    the guard refuses to hand over at.  Written through [State.mkModelOf]
    rather than reached, because reaching it is the 2^64 accepts nothing
    can perform; every other field is the listening model's, so the ONLY
    difference between this fixture and [listening_socket_model] is the
    counter — which is what makes the two case groups below a comparison
    of the guard and not of two unrelated states. *)
Definition exhausted_listening_model : Model :=
  mkModelOf (m_fd listening_socket_model) (m_vm listening_socket_model)
    (mkIoState (m_stdin listening_socket_model) (m_urandom listening_socket_model)
               (m_net listening_socket_model)
               (Z_to_bv 64 (two_pow_64 - 3)))
    (m_fsys listening_socket_model) (m_proc listening_socket_model)
    (m_lim listening_socket_model) (m_time listening_socket_model).

(** The same model ONE INDEX BELOW the guard: the last index at which a
    connection is still handed over. *)
Definition last_usable_listening_model : Model :=
  mkModelOf (m_fd listening_socket_model) (m_vm listening_socket_model)
    (mkIoState (m_stdin listening_socket_model) (m_urandom listening_socket_model)
               (m_net listening_socket_model)
               (Z_to_bv 64 (two_pow_64 - 4)))
    (m_fsys listening_socket_model) (m_proc listening_socket_model)
    (m_lim listening_socket_model) (m_time listening_socket_model).

(** THE REJECTION.  At the wrap the model refuses the descriptor, and it
    refuses it for EVERY value [State.alloc_fd]'s 4096-candidate scan
    could name, not merely for the one this table's allocator would
    return.  A kernel that answered any of them would be answering
    truthfully — Linux has no such counter and would hand fd 4 over — so
    this is the model NARROWING rather than reporting a kernel fault,
    which is the direction the fail-closed rule asks for and the reason
    the failure mode is a refusal to certify rather than a wrong channel.

    Compare [accept_success_return_is_exactly_the_lowest_free_fd], which
    is the same [filter] over the same 4096 candidates on the same fd
    table and returns [[4]].  The two differ in the counter alone. *)
Definition accept4_admits_at (m : Model) (r : word) : bool :=
  match accept4_answering m r with
  | CheckOk _ _ => true
  | _ => false
  end.

(** The other verdict this group has to separate: DECLINING is not
    rejecting, and the guard must produce the second and never the
    first. *)
Definition accept4_declines_at (m : Model) (r : word) : bool :=
  match accept4_answering m r with
  | CheckUnmodeled => true
  | _ => false
  end.

Example accept_at_the_wrap_hands_over_no_descriptor_at_all :
  filter (fun n => accept4_admits_at exhausted_listening_model (Z_to_bv 64 n))
         (map Z.of_nat (seq 0 4096))
  = [].
Proof. vm_compute. reflexivity. Qed.

Example accept_at_the_wrap_rejects_the_allocated_fd :
  accept4_answering exhausted_listening_model 4 = CheckReject.
Proof. check_eq. Qed.

(** NOT VACUOUS, and this is the case that proves it: one index lower the
    very same [filter] over the very same candidates returns [[4]] again,
    and the connection is handed over on channel [2^64 - 1] — the LAST
    channel that is not a standard stream.  Without this pair the group
    above would pass just as well against a fixture that had broken
    [accept] outright. *)
Example accept_one_below_the_wrap_still_hands_over :
  filter (fun n => accept4_admits_at last_usable_listening_model (Z_to_bv 64 n))
         (map Z.of_nat (seq 0 4096))
  = [4%Z].
Proof. vm_compute. reflexivity. Qed.

Example accept_one_below_the_wrap_uses_the_last_free_channel :
  bv_unsigned (conn_channel (Z_to_bv 64 (two_pow_64 - 4)))
  = (two_pow_64 - 1)%Z.
Proof. vm_compute. reflexivity. Qed.

(** THE ARM STILL ANSWERS.  The guard empties the SUCCESS side of the
    [alt] and nothing else, so all three injected errnos are still
    admitted and each leaves the model exactly as it found it — the
    queue not advanced, the counter not bumped.  That is why
    [Checks.Progress.receptive] is untouched: [accept] has an outcome at
    the wrap, and refusing to hand a connection over is not the same as
    having nothing to say.

    It is also why the spec spells the empty branch [choose (fun _ =>
    False)] and not [unmodeled]: the sibling of this [alt] answers a
    concrete errno at the very same (input, model), and
    [check_syscall_err_iff] holds against a TOTAL checker, so an arm that
    both answers and declines there is not statable. *)
Example accept_at_the_wrap_still_answers_its_errnos :
  accept4_answering exhausted_listening_model (errno_ret ENOMEM)
    = CheckOk exhausted_listening_model []
  /\ accept4_answering exhausted_listening_model (errno_ret EMFILE)
    = CheckOk exhausted_listening_model []
  /\ accept4_answering exhausted_listening_model (errno_ret ENFILE)
    = CheckOk exhausted_listening_model [].
Proof. split; [|split]; check_eq. Qed.

(** And the errno SET is unchanged at the wrap: the guard must not widen
    it.  Same enumeration over the whole 1..4095 error window that
    [accept_errno_set_is_exactly_these_three] runs on the unexhausted
    model, so a guard that had quietly turned the arm into "any errno"
    breaks here. *)
Example accept_at_the_wrap_errno_set_is_still_exactly_these_three :
  filter (fun e => accept4_admits_at exhausted_listening_model (errno_ret e))
         (map Z.of_nat (seq 1 4095))
  = [ENOMEM; ENFILE; EMFILE].
Proof. vm_compute. reflexivity. Qed.

(** THE ARM DOES NOT DECLINE.  A [CheckUnmodeled] at the wrap would be a
    different bug from the one the guard prevents — the model leaving
    the modeled surface at an accept it had been answering — and the
    [choose] rather
    than [unmodeled] is what rules it out.  Pinned over the whole 4096
    descriptor scan and the whole error window at once. *)
Example accept_at_the_wrap_never_declines :
  filter (fun n => accept4_declines_at exhausted_listening_model (Z_to_bv 64 n))
         (map Z.of_nat (seq 0 4096))
  = []
  /\ filter (fun e => accept4_declines_at exhausted_listening_model (errno_ret e))
            (map Z.of_nat (seq 1 4095))
     = [].
Proof. split; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   Sockets: the wrong ANSWERS, pinned so they stay out

   Everything below is a wrong answer a spec can easily give: a
   modeled answer Linux does not give -- not a gap.  That is the worst
   kind of defect here: [Equivalence.modeled] cannot see a wrong [Ok],
   so a source calling one of these would be certified against an
   outcome no kernel produces.  None of the three is reachable by a live
   run, for the reason recorded next to each, and the
   soundness/completeness proofs cannot catch a regression either --
   they prove checker = spec, so a change that moves BOTH in step
   still satisfies them.  Hence lemmas, in the hand-built style the
   accept4 cases above use.
   ------------------------------------------------------------------------- *)

(** [socket domain type protocol] answering [r].  Fds 0-3 are taken in
    [listening_socket_model], so a SUCCESS would have to be fd 4 --
    which none of these cases is. *)
Definition socket_answering (dom ty pro r : word) : check_result :=
  check_syscall (mkInput 198 [dom; ty; pro; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect r [] []) listening_socket_model.

(** SOCK_PACKET IS DECIDED ABOVE THE PROTOCOL RANGE, and this is the
    case that says so.  net/socket.c [__sock_create] rewrites the family
    to PF_PACKET for [PF_INET, SOCK_PACKET] before [pf->create], so
    [inet_create]'s [IPPROTO_MAX] test -- the only place that range
    exists in the kernel -- never runs, and
    net/packet/af_packet.c [packet_create] casts the protocol straight
    to a [__be16] ethertype without checking it at all.  Answering
    -EINVAL for [socket(AF_INET, SOCK_PACKET, -1)] would therefore be a
    modeled answer Linux never gives: it gives -EPERM without
    CAP_NET_RAW, and success with it.
    No live run can pin this: the privileged answer depends on the
    CAPABILITY of whoever runs the program, which is not part of any
    claim this repository makes. *)
Example socket_packet_declines_at_every_protocol :
  socket_answering 2 10 0 (errno_ret EINVAL) = CheckUnmodeled
  /\ socket_answering 2 10 4294967295 (errno_ret EINVAL) = CheckUnmodeled
  /\ socket_answering 2 10 263 (errno_ret EINVAL) = CheckUnmodeled
  /\ socket_answering 2 10 4294967295 (errno_ret EPERM) = CheckUnmodeled
  (* AND SOCK_DGRAM AT THE SAME PROTOCOL, STILL ANSWERING.  The four
     above are all [CheckUnmodeled], so on their own they stay green
     under any change that declines MORE -- the DGRAM/RAW arm moving
     above the protocol range with SOCK_PACKET, which is exactly the
     over-wide fix the lemma below this one guards against.  Holding the
     protocol fixed and moving only the TYPE across the boundary is what
     makes that failure land HERE, in the lemma that names the
     boundary. *)
  /\ socket_answering 2 2 4294967295 (errno_ret EINVAL)
     = CheckOk listening_socket_model [].
Proof. split; [|split; [|split; [|split]]]; check_eq. Qed.

(** THE ASYMMETRY THAT MAKES THE FIX NARROW.  SOCK_DGRAM and SOCK_RAW
    are NOT rewritten -- [__sock_create]'s rewrite is conditioned on
    [type == SOCK_PACKET] alone -- so they keep family AF_INET all the
    way into [inet_create] and its protocol range really does answer
    -EINVAL for them.  Moving the whole DGRAM/RAW/PACKET arm above the
    range check, rather than SOCK_PACKET only, would break these two:
    that is why this case sits next to the one above. *)
Example socket_dgram_and_raw_still_take_the_protocol_range :
  socket_answering 2 2 4294967295 (errno_ret EINVAL)
    = CheckOk listening_socket_model []
  /\ socket_answering 2 3 263 (errno_ret EINVAL)
    = CheckOk listening_socket_model []
  /\ socket_answering 2 2 0 (errno_ret EINVAL) = CheckUnmodeled.
Proof. split; [|split]; check_eq. Qed.

(** THE KERNEL-BUILD ANSWERS, declined rather than asserted.  Whether
    {SOCK_STREAM, IPPROTO_SCTP}, {SOCK_STREAM, IPPROTO_MPTCP}, a
    SOCK_SEQPACKET entry or a SOCK_DCCP one is registered is a property
    of the KERNEL BUILD -- net/sctp, net/mptcp and net/dccp each add
    theirs through [inet_register_protosw] when built -- so neither
    success nor an errno is the model's to give.
    No live run can pin these either: on a kernel built with
    CONFIG_MPTCP, protocol 262 SUCCEEDS, and which kernel a run uses is
    not part of the claim. *)
Example socket_kernel_build_answers_are_declined :
  socket_answering 2 1 132 (errno_ret EPROTONOSUPPORT) = CheckUnmodeled
  /\ socket_answering 2 1 262 (errno_ret EPROTONOSUPPORT) = CheckUnmodeled
  /\ socket_answering 2 5 0 (errno_ret ESOCKTNOSUPPORT) = CheckUnmodeled
  /\ socket_answering 2 6 0 (errno_ret ESOCKTNOSUPPORT) = CheckUnmodeled
  (* AND THE PURE ARGUMENT ERRORS, STILL ANSWERED, one per errno.  The
     four above are all [CheckUnmodeled] and describe where the
     build-dependent set ENDS; they do not fail when someone moves that
     end.  A change that declined every unregistered protocol, or every
     type without an [inetsw] list, leaves all four green and turns
     these two red -- which is the whole reason they are in this lemma
     rather than only in the one below it. *)
  /\ socket_answering 2 1 17 (errno_ret EPROTONOSUPPORT)
     = CheckOk listening_socket_model []
  /\ socket_answering 2 4 0 (errno_ret ESOCKTNOSUPPORT)
     = CheckOk listening_socket_model [].
Proof. split; [|split; [|split; [|split; [|split]]]]; check_eq. Qed.

(** THE NEIGHBOURS THAT ARE STILL ANSWERED, so the four declines above
    read as a boundary and not as socket() having gone quiet.  A
    protocol with no [inetsw] entry under SOCK_STREAM is
    -EPROTONOSUPPORT, and a type whose list is empty on every build
    (4 = SOCK_RDM, and 0) is -ESOCKTNOSUPPORT. *)
Example socket_still_answers_its_pure_argument_errors :
  socket_answering 2 1 17 (errno_ret EPROTONOSUPPORT)
    = CheckOk listening_socket_model []
  /\ socket_answering 2 4 0 (errno_ret ESOCKTNOSUPPORT)
    = CheckOk listening_socket_model []
  /\ socket_answering 2 0 0 (errno_ret ESOCKTNOSUPPORT)
    = CheckOk listening_socket_model [].
Proof. split; [|split]; check_eq. Qed.

(** THE DATAGRAM SHAPES ARE ANSWERED WITH A DESCRIPTOR.
    [Net.Socket.socket_dgram_b]: AF_INET6 (10) or AF_UNIX (1), type
    SOCK_DGRAM (2), protocol 0, mint a [State.FdDgram] of that family at
    the lowest free fd ([sock_map_fd]), or fail with the family's own
    injected errnos ([Net.Socket.socket_dgram_errnos]).  The model has
    three channels, so the descriptor is 3.
    ADMISSION REASON: model-internal -- a run shows the descriptor
    number, not which family the model recorded, nor that -ENOBUFS is
    admitted for AF_INET6 alone. *)
Definition dgram_socket_model : Model :=
  with_creds demo_creds
    (mkModel
       [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2) ]
       (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None).

Definition dgram_socket (dom ty pro r : word) : check_result :=
  check_syscall (mkInput 198 [dom; ty; pro; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect r [] []) dgram_socket_model.

Definition dgram_after (fam : Z) : Model :=
  with_fds (fd_insert (m_fds dgram_socket_model) 3 (FdDgram fam))
    dgram_socket_model.

Example socket_dgram_answers_with_a_descriptor :
  dgram_socket 10 2 0 3 = CheckOk (dgram_after AF_INET6) []
  /\ dgram_socket 1 2 0 3 = CheckOk (dgram_after AF_UNIX) []
  (* SOCK_CLOEXEC is admitted and ignored *)
  /\ dgram_socket 10 (2 + 524288) 0 3 = CheckOk (dgram_after AF_INET6) []
  (* the lowest free fd and no other *)
  /\ dgram_socket 1 2 0 4 = CheckReject
  (* [inet6_create]'s -ENOBUFS, for AF_INET6 and not for AF_UNIX *)
  /\ dgram_socket 10 2 0 (errno_ret ENOBUFS) = CheckOk dgram_socket_model []
  /\ dgram_socket 1 2 0 (errno_ret ENOBUFS) = CheckReject
  /\ dgram_socket 1 2 0 (errno_ret EMFILE) = CheckOk dgram_socket_model []
  /\ dgram_socket 10 2 0 (errno_ret ENFILE) = CheckOk dgram_socket_model [].
Proof. repeat split; check_eq. Qed.

(** ...AND EVERY OTHER SHAPE OF THOSE FAMILIES STAYS DECLINED, with the
    gates above them still answering: an explicit protocol (17,
    IPPROTO_UDP), a connection type (SOCK_STREAM, SOCK_SEQPACKET),
    SOCK_NONBLOCK, and SOCK_DGRAM under AF_INET; and the flag -EINVAL
    and the type range still decided first. *)
Example socket_dgram_neighbours :
  dgram_socket 10 2 17 3 = CheckUnmodeled
  /\ dgram_socket 10 1 0 3 = CheckUnmodeled
  /\ dgram_socket 1 5 0 3 = CheckUnmodeled
  /\ dgram_socket 10 (2 + 2048) 0 3 = CheckUnmodeled
  /\ dgram_socket 2 2 0 3 = CheckUnmodeled
  /\ dgram_socket 10 (2 + 1048576) 0 (errno_ret EINVAL)
     = CheckOk dgram_socket_model []
  /\ dgram_socket 10 11 0 (errno_ret EINVAL) = CheckOk dgram_socket_model [].
Proof. repeat split; check_eq. Qed.

(** A model whose fd 3 is a socket the peer has RESET and whose error
    has already been delivered, and its unreset twin.  Everything else
    matches [listening_socket_model].

    The reset one goes through [State.with_accepted] rather than a bare
    fd table because a connected socket can only have come FROM an
    accept: one connection has been handed over, so the queue has
    advanced and [m_conn_ix] is 1, and the channel the connection sits
    on is [conn_channel 0] = 3. *)
Definition reset_socket_model : Model :=
  with_accepted
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdSocket (SkReset (mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0)) 3)) ]
    listening_socket_model.

Definition fresh_socket_model : Model :=
  with_creds demo_creds
    (mkModel
       [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
         (3, FdSocket SkFresh) ]
       (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None).

(** Sixteen readable bytes at 4096 holding [struct sockaddr_in] for
    AF_INET, port 0, INADDR_ANY -- the one address [bind_spec] accepts.
    [sa_family_t] is host order, so AF_INET (2) is the single nonzero
    byte; port and address are network order and both zero. *)
Definition sockaddr_in_any_mem : word -> option byte :=
  fun a =>
    if andb (Z.leb 4096 (bv_unsigned a)) (Z.ltb (bv_unsigned a) 4112)
    then Some (if bv_eqb a 4096 then Z_to_bv 8 2 else Z_to_bv 8 0)
    else None.

(** [bind(3, addrp, addrlen)] answering [r] with the copy-in ledger
    [cis].  The address and the length are arguments because the two
    sides of the copy have to be reachable from one place: the ledger is
    what tells them apart, and an example that only ever supplies 16
    readable bytes could never show that.  [mkEffectU] rather than
    [mkEffect] for the same reason -- [mkEffect] hardcodes an EMPTY
    ledger. *)
Definition bind_answering_at (m : Model) (addrp addrlen r : word)
    (cis : list (word * nat)) : check_result :=
  check_syscall (mkInput 200 [3; addrp; addrlen; 0; 0; 0]
                   sockaddr_in_any_mem (fun _ => None))
    (mkEffectU r [] [] [] [] cis) m.

(** [bind(3, <that address>, 16)] answering [r].  Sixteen readable bytes
    at 4096 are copied, so the admissible effect carries that range. *)
Definition bind_answering (m : Model) (r : word) : check_result :=
  bind_answering_at m 4096 16 r [(4096, 16%nat)].

(** THIS INPUT REALLY REACHES THE SOCKET-STATE MATCH, which is what
    stops the case below from passing vacuously.  On a FRESH socket the
    very same call is answered -- so the [CheckUnmodeled] below is the
    state arm declining, not the length, fault, family, address or port
    check refusing the address on the way in. *)
Example bind_input_reaches_the_state_match :
  bind_answering fresh_socket_model 0 <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

(** BIND ON A CONNECTION THE PEER HAS RESET IS DECLINED, not -EINVAL.
    [tcp_done] ran [tcp_set_state(sk, TCP_CLOSE)], whose TCP_CLOSE arm
    calls [inet_put_port] -- and net/core/sock.c [sk_clone_lock] cleared
    SOCK_BINDPORT_LOCK on the accepted child, so the guard never saves
    it -- leaving [inet_num] zero.  Both conjuncts of [__inet_bind]'s
    [sk->sk_state != TCP_CLOSE || inet->inet_num] are then false and
    LINUX AUTOBINDS AND RETURNS 0.  Answering -EINVAL is a modeled
    answer Linux does not give.
    A guest cannot reach this on its own: reaching a reset connection
    needs a successful [accept], which needs an inbound connection.
    [connect] (203) is dispatched, but it cannot supply one, because
    [Net.Socket.connect_spec] declines the connection ATTEMPT, and an
    outbound connection is not what [accept] draws from in any case. *)
Example bind_on_a_reset_connection_declines :
  bind_answering reset_socket_model (errno_ret EINVAL) = CheckUnmodeled
  /\ bind_answering reset_socket_model 0 = CheckUnmodeled.
Proof. split; check_eq. Qed.

(** THE COPY-IN LEDGER MARKS WHERE THE COPY HAPPENED, and this is the
    example that makes that claim falsifiable rather than decorative.

    [move_addr_to_kernel] (net/socket.c, v6.12) is
    [if (ulen == 0) return 0; if (copy_from_user(kaddr, uaddr, ulen)) return -EFAULT;],
    so a [bind] with [0 < addrlen <= 128] over readable memory really has
    moved [addrlen] bytes before anything looks at the address, and one
    with [addrlen] out of that range, or [addrlen == 0], or an unreadable
    address, has moved nothing.  [bind_spec] records the range from the
    successful copy DOWNWARDS; [check_bind] expects it on exactly those
    arms.

    The two halves below are the two sides of that line, and they are
    stated in both directions on purpose.  Accepting-with-a-ledger alone
    would be satisfied just as well by a model that recorded a ledger
    everywhere, which is the mistake this example exists to catch.

    WHAT A MUTATION THAT DROPS THE LEDGER DOES -- deleting
    [record_copyins] from [bind_spec] and the
    [check_ret_only_copyins]/[check_copyins] tests from [check_bind]:

    - every conjunct in the FIRST group fails.  The two [CheckOk]s become
      [CheckReject] (the checker would demand an empty ledger and the
      effect carries one) and the two [CheckReject]s become [CheckOk] (a
      dropped ledger would be admitted).
    - every conjunct in the SECOND group still holds, unchanged.  Those
      arms return before the copy, so an empty ledger is right either
      way.

    That asymmetry is the point: the second group is what stops the first
    from being satisfied by a model that ledgers unconditionally, and the
    first is what stops the second from being satisfied by one that never
    ledgers at all.

    No live run can show this: a run observes what the kernel
    returned, and no kernel return says whether [copy_from_user] ran. *)
Example bind_copyin_ledger_marks_the_copy :
  (* PAST the copy: the ledger is required.  A fresh socket at 16 bytes
     reaches the state match, and 8 bytes reaches [inet_bind_sk]'s
     -EINVAL -- both after [move_addr_to_kernel] has copied. *)
  bind_answering_at fresh_socket_model 4096 16 (errno_ret EADDRINUSE)
    [(4096, 16%nat)] = CheckOk fresh_socket_model []
  /\ bind_answering_at fresh_socket_model 4096 16 (errno_ret EADDRINUSE) []
       = CheckReject
  /\ bind_answering_at fresh_socket_model 4096 8 (errno_ret EINVAL)
       [(4096, 8%nat)] = CheckOk fresh_socket_model []
  /\ bind_answering_at fresh_socket_model 4096 8 (errno_ret EINVAL) []
       = CheckReject
  (* BEFORE the copy: the ledger is forbidden.  [addrlen == 0] copies
     nothing and returns 0 from [move_addr_to_kernel]; [addrlen > 128] is
     refused by its range test; and an unreadable address is the copy
     itself failing, which transfers nothing. *)
  /\ bind_answering_at fresh_socket_model 4096 0 (errno_ret EINVAL) []
       = CheckOk fresh_socket_model []
  /\ bind_answering_at fresh_socket_model 4096 0 (errno_ret EINVAL)
       [(4096, 0%nat)] = CheckReject
  /\ bind_answering_at fresh_socket_model 4096 129 (errno_ret EINVAL) []
       = CheckOk fresh_socket_model []
  /\ bind_answering_at fresh_socket_model 4096 129 (errno_ret EINVAL)
       [(4096, 129%nat)] = CheckReject
  /\ bind_answering_at fresh_socket_model 8192 16 (errno_ret EFAULT) []
       = CheckOk fresh_socket_model []
  /\ bind_answering_at fresh_socket_model 8192 16 (errno_ret EFAULT)
       [(8192, 16%nat)] = CheckReject.
Proof. repeat split; check_eq. Qed.

(** [getsockopt(3, level, 4, optval, optlenp)] answering [r] with the
    copy-in ledger [cis].  [optlenp] is an argument for
    [bind_answering_at]'s reason: the two sides of the copy have to be
    reachable from one place, and only the ledger tells them apart.
    [sockaddr_in_any_mem] is reused purely as a MEMORY MAP here -- what
    matters is that [4096, 4112) is readable and everything else is not,
    so 4096 is a readable four-byte [optlen], 8192 an unreadable one, and
    4109 one that STRADDLES the boundary with three readable bytes. *)
Definition getsockopt_answering (m : Model) (level optlenp r : word)
    (cis : list (word * nat)) : check_result :=
  check_syscall (mkInput 209 [3; level; 4; 4096; optlenp; 0]
                   sockaddr_in_any_mem (fun _ => None))
    (mkEffectU r [] [] [] [] cis) m.

(** THE [optlen] READ HAPPENS BEFORE THE LEVEL DISPATCH AND AFTER THE FD,
    and this is what makes that falsifiable.

    [do_sock_getsockopt] (net/socket.c) runs [security_socket_getsockopt]
    and then [copy_from_sockptr(&max_optlen, optlen, sizeof(int))] with
    no level test in between, so every -EOPNOTSUPP has moved four bytes.
    [__sys_getsockopt] resolves the descriptor before it calls that
    function at all, so -EBADF has moved none.  The result of the copy is
    discarded, which is exactly why no live run can see this: the errno
    is the same whatever is at [optlen], and no kernel return says
    whether [copy_from_user] ran.

    STATED IN BOTH DIRECTIONS, for [bind_copyin_ledger_marks_the_copy]'s
    reason.  Accepting-with-a-ledger alone is satisfied by a model that
    ledgers unconditionally; refusing-a-ledger alone by one that never
    ledgers.  Only the two together pin the boundary -- and the boundary
    is the whole content of the rule, since the errno does not depend
    on it.

    It also pins the DECISION in [getsockopt_spec] that an unreadable
    [optlen] records nothing.  Rows 3-6 are that decision; without them a
    spec that recorded the range unconditionally would pass every proof,
    because [getsockopt_optlen_read] is shared by the
    spec, the checker and the witness and moves all three at once.

    ROW 5-6 ARE THE NAMED RESIDUE, not an accident: a real
    [copy_from_user] copies partially, so Linux touches the page under
    4109 before faulting on 4112, while the model records nothing.  That
    under-records by at most one page, which
    [State.syscall_effect_accesses] can only under-CHARGE, never
    over-charge.  If that residue is ever closed, these two rows are what
    has to change, and they say so here rather than in a comment nothing
    checks. *)
Example getsockopt_optlen_ledger_marks_the_read :
  (* PAST the fd, on an unknown level: the four bytes are required. *)
  getsockopt_answering fresh_socket_model 17 4096 (errno_ret EOPNOTSUPP)
    [(4096, 4%nat)] = CheckOk fresh_socket_model []
  /\ getsockopt_answering fresh_socket_model 17 4096 (errno_ret EOPNOTSUPP)
       [] = CheckReject
  (* An UNREADABLE [optlen] is the copy failing, which transfers nothing
     -- and the errno is unchanged, because its result is discarded. *)
  /\ getsockopt_answering fresh_socket_model 17 8192 (errno_ret EOPNOTSUPP)
       [] = CheckOk fresh_socket_model []
  /\ getsockopt_answering fresh_socket_model 17 8192 (errno_ret EOPNOTSUPP)
       [(8192, 4%nat)] = CheckReject
  (* A range straddling the mapped boundary is unreadable AS A WHOLE. *)
  /\ getsockopt_answering fresh_socket_model 17 4109 (errno_ret EOPNOTSUPP)
       [] = CheckOk fresh_socket_model []
  /\ getsockopt_answering fresh_socket_model 17 4109 (errno_ret EOPNOTSUPP)
       [(4109, 4%nat)] = CheckReject
  (* BEFORE the fd verdict: -EBADF never reached [do_sock_getsockopt],
     so a ledger there is a read the kernel did not perform.  fd 9 is not
     open in this model; the arguments are otherwise a good getsockopt. *)
  /\ check_syscall (mkInput 209 [9; 17; 4; 4096; 4096; 0]
                     sockaddr_in_any_mem (fun _ => None))
       (mkEffectU (errno_ret EBADF) [] [] [] [] []) fresh_socket_model
     = CheckOk fresh_socket_model []
  /\ check_syscall (mkInput 209 [9; 17; 4; 4096; 4096; 0]
                     sockaddr_in_any_mem (fun _ => None))
       (mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 4%nat)])
       fresh_socket_model
     = CheckReject
  (* A KNOWN level is the option table, declined whatever the ledger --
     so neither row above is the level test in disguise. *)
  /\ getsockopt_answering fresh_socket_model 6 4096 (errno_ret EOPNOTSUPP)
       [(4096, 4%nat)] = CheckUnmodeled
  /\ getsockopt_answering fresh_socket_model 6 4096 (errno_ret EOPNOTSUPP)
       [] = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(* -------------------------------------------------------------------------
   READ ON A CONNECTED SOCKET.  Everything below is invisible to the
   proofs, which is why it is written out here.

   Invisible: soundness and completeness prove CHECKER = SPEC, so they
   hold just as well when the two regress TOGETHER.  Swapping
   -ECONNRESET for -ETIMEDOUT, dropping the [set_fds] that retires the
   connection to [SkReset] — making the error sticky rather than
   one-shot — or loosening the [choose] bound on a delivered [NCons]
   would leave every proof green.  These cases are what fails.
   ------------------------------------------------------------------------- *)

(** A writable 16-byte landing zone at 4096 for the read's destination.
    It has to be WRITABLE: with an unmapped buffer [Specs.read_spec]'s
    queued-bytes arm answers -EFAULT ahead of the protocol, and a case
    pinned there would be pinning the destination, not the socket. *)
Definition sock_read_buf : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4112 then Some 0 else None.

(** The peer every connected model here talks to. *)
Definition demo_peer : PeerAddr := mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0).

(** A model whose fd 4 is a CONNECTED socket running script [rx], with
    fd 3 still LISTENING behind it — exactly the shape an accept
    leaves, which is why it is [accepted_socket_model] generalised over
    the script rather than a table invented for these cases:
    [connected_socket_model NFin] IS that model.

    THE DESCRIPTOR AND THE CHANNEL ARE DELIBERATELY DIFFERENT — fd 4,
    channel 3 = [Specs.conn_channel 0].  A model that put the
    connection on fd 3 would make the two coincide, and then the
    delivered-byte case below could not tell an event emitted on the
    CONNECTION's channel from one emitted on the DESCRIPTOR: both would
    read [ReadEv 3].  Since the whole point of [Specs.conn_channel] is
    that it is NOT the fd — [State.lowest_fd] reissues a closed
    descriptor, so after a [close] an accepted socket would otherwise
    report on another stream's channel — a case that cannot separate
    them does not pin the property it is named for. *)
Definition connected_socket_model (rx : NetStream) : Model :=
  with_accepted
    [ (4, FdSocket (SkConnected demo_peer 3 rx));
      (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdSocket SkListening) ]
    listening_socket_model.

(** The state a socket read LEAVES BEHIND when it touches the fd table.
    [State.fd_insert] reseats the descriptor at the HEAD; fd 4 already
    leads here, so the order is unchanged and only the entry differs. *)
Definition retired_socket_model (e : FdEntry) : Model :=
  with_accepted
    [ (4, e); (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdSocket SkListening) ]
    listening_socket_model.

(** [read(4, 4096, 16)] answering [r] with write ledger [ws]. *)
Definition read_answering (m : Model) (r : word)
    (ws : list (word * list byte)) : check_result :=
  check_syscall (mkInput 63 [4; 4096; 16; 0; 0; 0] (fun _ => None) sock_read_buf)
    (mkEffect r ws []) m.

(** THE PEER'S RST, DELIVERED ONCE.  -ECONNRESET is the answer and the
    connection retires to [SkReset] in the SAME step, because
    [sock_error] consumes the pending error with an [xchg] and
    [tcp_done] sets [sk_shutdown = SHUTDOWN_MASK].  The second conjunct
    catches a swap of the two protocol errnos; the third catches an arm
    that answered the error without retiring the connection. *)
Example read_on_rst_delivers_econnreset_and_retires :
  read_answering (connected_socket_model NRst) (errno_ret ECONNRESET) []
    = CheckOk (retired_socket_model (FdSocket (SkReset demo_peer 3))) []
  /\ read_answering (connected_socket_model NRst) (errno_ret ETIMEDOUT) []
    = CheckReject
  /\ read_answering (connected_socket_model NRst) (Z_to_bv 64 0) []
    = CheckReject.
Proof. split; [check_eq | split; vm_compute; reflexivity]. Qed.

(** THE CONNECTION THAT TIMED OUT, the same shape on the same
    transition.  Pinning both is what makes the pair a SWAP test: each
    case refuses the other's errno. *)
Example read_on_timeout_delivers_etimedout_and_retires :
  read_answering (connected_socket_model NTimedOut) (errno_ret ETIMEDOUT) []
    = CheckOk (retired_socket_model (FdSocket (SkReset demo_peer 3))) []
  /\ read_answering (connected_socket_model NTimedOut) (errno_ret ECONNRESET) []
    = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** THE ERROR IS ONE-SHOT, NOT STICKY.  A retired connection reads as
    end-of-stream, and re-answering either protocol error is refused.
    This is the case that fails if the [set_fds] above is dropped: with
    the connection left in [SkConnected _ _ NRst] the error would repeat
    forever, which is a plausible answer Linux does not give. *)
Example read_on_a_retired_connection_is_end_of_stream :
  read_answering (retired_socket_model (FdSocket (SkReset demo_peer 3)))
      (Z_to_bv 64 0) []
    = CheckOk (retired_socket_model (FdSocket (SkReset demo_peer 3))) []
  /\ read_answering (retired_socket_model (FdSocket (SkReset demo_peer 3)))
       (errno_ret ECONNRESET) []
    = CheckReject
  /\ read_answering (retired_socket_model (FdSocket (SkReset demo_peer 3)))
       (errno_ret ETIMEDOUT) []
    = CheckReject.
Proof. split; [check_eq | split; vm_compute; reflexivity]. Qed.

(** THE PEER'S FIN reads 0 and leaves the socket alone — sticky, unlike
    the two errors. *)
Example read_on_fin_is_end_of_stream_and_sticky :
  read_answering (connected_socket_model NFin) (Z_to_bv 64 0) []
    = CheckOk (connected_socket_model NFin) []
  /\ read_answering (connected_socket_model NFin) (Z_to_bv 64 1)
       [(4096, [Z_to_bv 8 65])]
    = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A DELIVERED BYTE: the return, the write ledger, the event on the
    CONNECTION's channel, and the advanced script, all in one equality.
    THE EVENT IS [ReadEv 3] WHILE THE DESCRIPTOR READ IS 4 — that gap is
    the point of the case, and it is what a model with the connection on
    fd 3 could not state.

    The second conjunct is the [choose] bound: the script holds ONE
    byte, so a two-byte delivery is refused however well-formed its
    ledger looks.  A spec that dropped the [net_take] agreement
    conjunct would admit it. *)
Example read_on_a_byte_delivers_it_and_advances :
  read_answering (connected_socket_model (NCons (Z_to_bv 8 65) NFin))
      (Z_to_bv 64 1) [(4096, [Z_to_bv 8 65])]
    = CheckOk (retired_socket_model
                 (FdSocket (SkConnected demo_peer 3 NFin)))
        [ReadEv 3 (Z_to_bv 8 65)]
  /\ read_answering (connected_socket_model (NCons (Z_to_bv 8 65) NFin))
       (Z_to_bv 64 2) [(4096, [Z_to_bv 8 65; Z_to_bv 8 66])]
    = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** THE SAME DELIVERY AT A COUNT OVER THE WRITE SIDE'S CEILING.
    [read]'s socket arm does not carry [Uaccess.modeled_rw_count], the
    128 KiB ceiling of the write side, because it does not need it:
    [State.net_take_z] walks the script in [positive] and the delivery
    is bounded by the script, not by the count.  It carries
    [Uaccess.modeled_rw_range], so a count over the ceiling at an
    addressable buffer is JUDGED and only an out-of-range one
    declines.

    [read_answering] fixes the count at 16, so this states the call
    itself.  The buffer is [sock_read_buf]'s sixteen writable bytes and
    the script holds one byte, which is why the answer is the same
    one-byte delivery as above: the count is not what bounds it.

    The second conjunct is the same [choose] bound as above, still
    binding at this count — a zero-byte answer to a nonzero request is
    refused, so the first conjunct is not merely one admissible outcome
    among any number of them. *)
Example read_over_rw_bytes_max_is_judged :
  check_syscall
    (mkInput 63 [4; 4096; Z_to_bv 64 (rw_bytes_max + 1); 0; 0; 0]
       (fun _ => None) sock_read_buf)
    (mkEffect (Z_to_bv 64 1) [(4096, [Z_to_bv 8 65])] [])
    (connected_socket_model (NCons (Z_to_bv 8 65) NFin))
  = CheckOk (retired_socket_model (FdSocket (SkConnected demo_peer 3 NFin)))
      [ReadEv 3 (Z_to_bv 8 65)]
  /\ check_syscall
       (mkInput 63 [4; 4096; Z_to_bv 64 (rw_bytes_max + 1); 0; 0; 0]
          (fun _ => None) sock_read_buf)
       (mkEffect (Z_to_bv 64 0) [] [])
       (connected_socket_model (NCons (Z_to_bv 8 65) NFin))
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(* =========================================================================
   connect (203) — the arms, the two orderings, and the ledger boundary
   ========================================================================= *)

(** WHY THESE ARE WRITTEN OUT BY HAND.  Two of connect's states cannot
    be built by a binary on its own: [SkConnected] and [SkReset] need a
    successful [accept], which needs an inbound connection.  The cases
    below state connect's arms and the ledger boundary.

    Sixteen readable bytes at 8192 holding [struct sockaddr_in] for
    AF_INET, port 80, 127.0.0.1 — a well-formed address, so what stops
    the call is always the fd or the state and never the address. *)
Definition connect_addr_mem : word -> option byte :=
  fun a => if      bv_eqb a 8192 then Some 2      (* sin_family lo: AF_INET *)
           else if bv_eqb a 8193 then Some 0      (* sin_family hi *)
           else if bv_eqb a 8194 then Some 0      (* sin_port hi *)
           else if bv_eqb a 8195 then Some 80     (* sin_port lo *)
           else if bv_eqb a 8196 then Some 127    (* sin_addr *)
           else if bv_eqb a 8197 then Some 0
           else if bv_eqb a 8198 then Some 0
           else if bv_eqb a 8199 then Some 1
           else if andb (Z.ltb 8199 (bv_unsigned a))
                        (Z.ltb (bv_unsigned a) 8208)
           then Some 0                            (* sin_zero *)
           else None.

(** The same 16 bytes with [sin_family] set to AF_UNIX (1), which is
    what makes the -EAFNOSUPPORT case below different from a truncation. *)
Definition connect_unix_family_mem : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 1 else connect_addr_mem a.

(** [sin_family] AF_UNSPEC (0), the disconnect request. *)
Definition connect_unspec_mem : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 0 else connect_addr_mem a.

(** connect(fd, addrp, addrlen) — syscall 203 — against model [m],
    answering [r], with [mp] as the readable memory, claiming NO
    copy-from-user range.  Use this for the arms ABOVE the copy. *)
Definition connect_answering (mp : word -> option byte)
    (m : Model) (fd addrp addrlen r : word) : check_result :=
  check_syscall (mkInput 203 [fd; addrp; addrlen; 0; 0; 0] mp (fun _ => None))
    (mkEffect r [] []) m.

(** The same call claiming a copy-from-user range of [n] bytes at
    [addrp].  Use this for the arms BELOW the copy — which, because
    [__sys_connect] copies before [__sys_connect_file] resolves the
    socket, includes -ENOTSOCK.  Splitting the two spellings is what
    makes the ledger boundary visible in each example rather than
    hidden in a shared helper: an example that uses the wrong one is
    [CheckReject], and that is the point. *)
Definition connect_answering_c (mp : word -> option byte)
    (m : Model) (fd addrp addrlen : word) (n : nat) (r : word)
    : check_result :=
  check_syscall (mkInput 203 [fd; addrp; addrlen; 0; 0; 0] mp (fun _ => None))
    (with_copyins [(addrp, n)] (mkEffect r [] [])) m.

(** A socket bound to INADDR_ANY:0 and NOT listened on. *)
Definition bound_socket_model : Model :=
  with_creds demo_creds
    (mkModel
       [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
         (3, FdSocket SkBound) ]
       (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None).

(** -EISCONN ON A LISTENING SOCKET, which is the answer worth a case of
    its own: [listen] leaves [sock->state] at SS_UNCONNECTED and moves
    only [sk->sk_state], so [__inet_stream_connect]'s SS_UNCONNECTED arm
    returns the -EISCONN it pre-loaded rather than falling through.
    -EINVAL is the plausible guess and it is REFUSED here, which is what
    makes this case discriminate. *)
Example connect_on_a_listening_socket_is_eisconn :
  connect_answering_c connect_addr_mem listening_socket_model 3 8192 16 16
    (errno_ret EISCONN) = CheckOk listening_socket_model []
  /\ connect_answering_c connect_addr_mem listening_socket_model 3 8192 16 16
       (errno_ret EINVAL) = CheckReject.
Proof. split; check_eq. Qed.

(** THE ANSWER DOES NOT CARRY WITHOUT ITS COPY.  The same arm, offered
    an effect that claims no copy-from-user range, is REJECTED — which
    is what makes [record_copyins]'s placement above the -ENOTSOCK arm a
    checked fact rather than a comment. *)
Example connect_eisconn_must_carry_its_copy :
  connect_answering connect_addr_mem listening_socket_model 3 8192 16
    (errno_ret EISCONN) = CheckReject.
Proof. check_eq. Qed.

(** -EISCONN ON AN ACCEPTED SOCKET too, from the arm above it:
    [__inet_accept] ends with [newsock->state = SS_CONNECTED]. *)
Example connect_on_an_accepted_socket_is_eisconn :
  connect_answering_c connect_addr_mem accepted_socket_model 4 8192 16 16
    (errno_ret EISCONN) = CheckOk accepted_socket_model [].
Proof. check_eq. Qed.

(** A RESET CONNECTION IS -EISCONN TOO.  net/ipv4/tcp.c [tcp_done] moves
    [sk->sk_state] to TCP_CLOSE and leaves [sock->state] at SS_CONNECTED,
    so the switch still takes its SS_CONNECTED arm — which is why
    -EISCONN survives the peer's error, and why AF_UNSPEC on it is
    declined rather than answered 0 as it is on a fresh socket. *)
Example connect_on_a_reset_connection_is_eisconn :
  connect_answering_c connect_addr_mem reset_socket_model 3 8192 16 16
    (errno_ret EISCONN) = CheckOk reset_socket_model []
  /\ connect_answering_c connect_addr_mem reset_socket_model 3 8192 16 16
       (errno_ret EINVAL) = CheckReject
  /\ connect_answering_c connect_addr_mem reset_socket_model 3 8192 16 16 0
     = CheckReject
  /\ connect_answering_c connect_unspec_mem reset_socket_model 3 8192 2 2 0
     = CheckUnmodeled.
Proof. repeat split; (reflexivity || check_eq). Qed.

(** ...and the answer is the same for every shape the peer's script can
    take.  This is the case that fails the day someone mirrors
    [bind_spec]'s [rx] split into connect, where it does not belong:
    bind reads [inet_num], which [tcp_done] zeroes, and connect reads
    [sock->state], which it does not touch. *)
Example connect_is_eisconn_whatever_the_peer_has_left_to_say :
  connect_answering_c connect_addr_mem (connected_socket_model NFin) 4 8192 16 16
    (errno_ret EISCONN) = CheckOk (connected_socket_model NFin) []
  /\ connect_answering_c connect_addr_mem (connected_socket_model NRst) 4 8192 16 16
       (errno_ret EISCONN) = CheckOk (connected_socket_model NRst) []
  /\ connect_answering_c connect_addr_mem (connected_socket_model NTimedOut) 4 8192 16 16
       (errno_ret EISCONN) = CheckOk (connected_socket_model NTimedOut) []
  /\ connect_answering_c connect_addr_mem
       (connected_socket_model (NCons (Z_to_bv 8 65) NFin)) 4 8192 16 16
       (errno_ret EISCONN)
     = CheckOk (connected_socket_model (NCons (Z_to_bv 8 65) NFin)) [].
Proof. repeat split; check_eq. Qed.

(** THE ORDERING THAT IS NOT BIND'S.  [__sys_connect] copies the address
    BEFORE [__sys_connect_file] resolves the file to a socket, so an
    unreadable address on a NON-SOCKET descriptor is -EFAULT.  The same
    call to [bind] is -ENOTSOCK, because [__sys_bind] resolves the
    socket first.  Both halves are pinned: swapping the two answers is
    exactly the mistake this case exists to catch.  The -EFAULT carries
    no ledger, because that arm IS the copy failing. *)
Example connect_faults_before_it_reaches_enotsock :
  connect_answering (fun _ => None) listening_socket_model 1 8192 16
    (errno_ret EFAULT) = CheckOk listening_socket_model []
  /\ connect_answering (fun _ => None) listening_socket_model 1 8192 16
       (errno_ret ENOTSOCK) = CheckReject
  /\ check_syscall (mkInput 200 [1; 8192; 16; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTSOCK) [] []) listening_socket_model
     = CheckOk listening_socket_model [].
Proof. repeat split; check_eq. Qed.

(** -ENOTSOCK still wins when the address IS readable, so the case above
    is about the order and not about -ENOTSOCK being unreachable.  And
    it carries the ledger, because the copy already happened — the one
    place connect's ledger differs from bind's. *)
Example connect_on_a_channel_fd_is_enotsock :
  connect_answering_c connect_addr_mem listening_socket_model 1 8192 16 16
    (errno_ret ENOTSOCK) = CheckOk listening_socket_model []
  /\ connect_answering connect_addr_mem listening_socket_model 1 8192 16
       (errno_ret ENOTSOCK) = CheckReject.
Proof. split; check_eq. Qed.

(** -EBADF comes first of all, before the address is touched: an
    unreadable address on a closed descriptor is still -EBADF, and it
    claims no copy. *)
Example connect_on_a_closed_fd_is_ebadf :
  connect_answering (fun _ => None) listening_socket_model 9 8192 16
    (errno_ret EBADF) = CheckOk listening_socket_model []
  /\ connect_answering_c connect_addr_mem listening_socket_model 9 8192 16 16
       (errno_ret EBADF) = CheckReject.
Proof. split; check_eq. Qed.

(** THE THREE LENGTH THRESHOLDS, in the order the kernel applies them.
    [move_addr_to_kernel] rejects > 128 and < 0; [__inet_stream_connect]
    rejects < 2; [tcp_v4_connect] rejects < 16.  A length of 0 copies
    nothing and cannot fault, so it lands on the 2-byte minimum rather
    than on -EFAULT — checked with an address that is not readable at
    all — and it records nothing. *)
Example connect_length_thresholds :
  connect_answering connect_addr_mem listening_socket_model 3 8192 129
    (errno_ret EINVAL) = CheckOk listening_socket_model []
  /\ connect_answering connect_addr_mem listening_socket_model 3 8192
       (Z_to_bv 64 (2 ^ 32 - 1)) (errno_ret EINVAL)
     = CheckOk listening_socket_model []
  /\ connect_answering (fun _ => None) listening_socket_model 3 8192 0
       (errno_ret EINVAL) = CheckOk listening_socket_model []
  /\ connect_answering connect_addr_mem listening_socket_model 3 8192 1
       (errno_ret EFAULT) = CheckReject.
Proof. repeat split; check_eq. Qed.

(** ON A FRESH SOCKET the 16-byte minimum and the family check are
    reachable, and they are [tcp_v4_connect]'s — so a 4-byte address is
    -EINVAL and a full-length AF_UNIX address is -EAFNOSUPPORT, NOT
    -EINVAL. *)
Example connect_on_a_fresh_socket_reaches_tcp_v4_connect :
  connect_answering_c connect_addr_mem fresh_socket_model 3 8192 4 4
    (errno_ret EINVAL) = CheckOk fresh_socket_model []
  /\ connect_answering_c connect_unix_family_mem fresh_socket_model 3 8192 16 16
       (errno_ret EAFNOSUPPORT) = CheckOk fresh_socket_model []
  /\ connect_answering_c connect_unix_family_mem fresh_socket_model 3 8192 16 16
       (errno_ret EINVAL) = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE ATTEMPT IS DECLINED, and declining is not the same as refusing:
    a well-formed AF_INET connect on a fresh socket is [CheckUnmodeled],
    which is the model saying it has no answer — not [CheckReject],
    which would be the model rejecting a trace Linux produces.  Every
    return is declined alike, so no errno can be smuggled in on this
    arm: 0, -ECONNREFUSED and -ETIMEDOUT all land here.  This is the pin
    [State.ECONNREFUSED] exists for. *)
Example connect_attempt_is_declined_not_refused :
  connect_answering_c connect_addr_mem fresh_socket_model 3 8192 16 16 0
    = CheckUnmodeled
  /\ connect_answering_c connect_addr_mem fresh_socket_model 3 8192 16 16
       (errno_ret ECONNREFUSED) = CheckUnmodeled
  /\ connect_answering_c connect_addr_mem fresh_socket_model 3 8192 16 16
       (errno_ret ETIMEDOUT) = CheckUnmodeled.
Proof. repeat split; reflexivity. Qed.

(** AF_UNSPEC IS A DISCONNECT, and only the fresh socket's is answered.
    [tcp_disconnect] has one return statement and it is [return 0]; on a
    socket with no port, no queue and no connection every branch inside
    it is dead, so the call returns 0 and leaves the model alone.  On a
    LISTENING socket the same call would run [inet_csk_listen_stop] and
    destroy the accept queue, which [SockState] cannot say — declined. *)
Example connect_af_unspec_is_a_disconnect :
  connect_answering_c connect_unspec_mem fresh_socket_model 3 8192 2 2 0
    = CheckOk fresh_socket_model []
  /\ connect_answering_c connect_unspec_mem listening_socket_model 3 8192 2 2 0
     = CheckUnmodeled
  /\ connect_answering_c connect_unspec_mem accepted_socket_model 4 8192 2 2 0
     = CheckUnmodeled.
Proof. repeat split; (reflexivity || check_eq). Qed.

(** THE BOUND SOCKET, which is the state worth a case of its own because
    it groups with the FRESH one and not with the listening one.  What
    [__inet_stream_connect]'s SS_UNCONNECTED arm tests is
    [sk->sk_state != TCP_CLOSE], and [bind] moves the PORT without
    moving that — [__inet_bind] never calls [tcp_set_state] — so a bound
    socket is still TCP_CLOSE and still reaches [tcp_v4_connect].  A
    regrouping by "has this socket had a setup call" rather than by "can
    tcp_v4_connect still run" would move [SkBound] into the -EISCONN arm
    and go unnoticed without this.  Both arms it belongs to are pinned:
    the length and family checks it reaches, and the AF_UNSPEC
    disconnect it declines — where its reason is its own, since the port
    [__inet_bind] took is exactly what [tcp_disconnect] might release. *)
Example connect_on_a_bound_socket_is_not_eisconn :
  connect_answering_c connect_addr_mem bound_socket_model 3 8192 4 4
    (errno_ret EINVAL) = CheckOk bound_socket_model []
  /\ connect_answering_c connect_addr_mem bound_socket_model 3 8192 4 4
       (errno_ret EISCONN) = CheckReject
  /\ connect_answering_c connect_unix_family_mem bound_socket_model 3 8192 16 16
       (errno_ret EAFNOSUPPORT) = CheckOk bound_socket_model []
  /\ connect_answering_c connect_addr_mem bound_socket_model 3 8192 16 16 0
     = CheckUnmodeled
  /\ connect_answering_c connect_unspec_mem bound_socket_model 3 8192 2 2 0
     = CheckUnmodeled.
Proof. repeat split; (reflexivity || check_eq). Qed.

(** AF_UNSPEC IS READ BEFORE THE STATE SWITCH, and this is where that
    shows.  A 2-byte AF_UNSPEC address on a LISTENING socket is declined
    — the -EISCONN arm never sees it — while the same 2 bytes with
    [sin_family] AF_INET are -EISCONN on that socket and -EINVAL on a
    fresh one, from the 16-byte minimum a step further down.  The two
    orderings crossing, in one case. *)
Example connect_af_unspec_precedes_the_state_switch :
  connect_answering_c connect_unspec_mem listening_socket_model 3 8192 2 2
    (errno_ret EISCONN) = CheckUnmodeled
  /\ connect_answering_c connect_addr_mem listening_socket_model 3 8192 2 2
       (errno_ret EISCONN) = CheckOk listening_socket_model []
  /\ connect_answering_c connect_addr_mem fresh_socket_model 3 8192 2 2
       (errno_ret EINVAL) = CheckOk fresh_socket_model [].
Proof. repeat split; (reflexivity || check_eq). Qed.

(* -------------------------------------------------------------------------
   Socket options and addresses (204, 205, 208, 209, 210)

   All five resolve the fd first (net/socket.c, CLASS(fd, f) then
   sock_from_file in each __sys_* entry, v6.18.46), so no argument
   changes the answer.  The shapes below -- a level no dispatcher has an
   arm for, an unknown optname under SOL_SOCKET, a NULL or unmapped user
   pointer -- are stated on a closed fd and on non-socket fds, where the
   fd decides.
   ------------------------------------------------------------------------- *)

(** One fd of each NON-SOCKET kind, and [State.FdEntry] has FOUR of
    them: stdin (channel) at 0, a read-only file at 3, a write-only file
    at 4 and a directory at 5.  Sockets get their own model below. *)
Definition socket_call_model : Model :=
  with_creds demo_creds
    (mkModel
       [ (0, FdChannel 0); (3, FdFile [102] 0); (4, FdFileW [103] 0);
         (5, FdDir) ]
       (mkVmMaps [] [] 0 0 demo_limit) IEof
       [([102], [104; 105]); ([103], [])] None None None).

(** NO NON-SOCKET FD KIND IS A SOCKET, on all five calls.
    [sock_from_file] tests the file's [f_op] for [socket_file_ops]
    and nothing else, so a channel, a readable file, a writable file, an
    append file, a READ-WRITE file, a directory and a pipe end all answer
    -ENOTSOCK alike; the model says so in [Net.Socket.sock_fd]'s seven
    non-socket arms.
    (The fixture below exercises the first three and the directory; the
    pipe end's is pinned in [Checks.Cases.Fs.Pipe], where the model that
    can hold one lives.  The append fd's is pinned by neither, and does
    not need to be: [Net.Socket.sock_fd]'s arms are one -ENOTSOCK per
    kind with no state read, so the fixture is showing the SHAPE rather
    than enumerating it.)
    The second conjunct is
    what makes this bind: were any of those arms ever to answer
    something else -- -EBADF, say, as an unopened fd does -- the first
    conjunct would stop holding, and were one to admit a SUCCESS the
    third would. *)
Example socket_calls_decline_every_non_socket_fd_kind :
  Forall (fun fd =>
    Forall (fun no =>
      check_syscall (mkInput no [fd; 999; 999; 4096; 4; 0]
                       (fun _ => None) (fun _ => None))
        (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
      = CheckOk socket_call_model []
      /\ check_syscall (mkInput no [fd; 999; 999; 4096; 4; 0]
                         (fun _ => None) (fun _ => None))
           (mkEffect (errno_ret EBADF) [] []) socket_call_model
         = CheckReject
      /\ check_syscall (mkInput no [fd; 999; 999; 4096; 4; 0]
                         (fun _ => None) (fun _ => None))
           (mkEffect (Z_to_bv 64 0) [] []) socket_call_model
         = CheckReject)
      [204; 205; 208; 209; 210])
    [0; 3; 4; 5].
Proof. repeat constructor; check_eq. Qed.

(** Nothing past the descriptor changes the answer.  On 208 and 209 the
    argument below is a LEVEL no protocol registers, with an optname to
    match, and the level is what would decide: on a socket its test
    fires first, so the set side's -ENOPROTOOPT comes from
    [ip_setsockopt] and the get side's -EOPNOTSUPP from
    [do_ip_getsockopt] (both net/ipv4/ip_sockglue.c), and the optname is
    never reached.  On 204 and 205 that same register is [addr], and on
    210 it is a [how] outside {0,1,2}.  Every one of them sits behind
    the lookup, so none is admissible here.  Both the closed and the
    live fd, both halves. *)
Example socket_calls_unknown_level_never_beats_the_fd :
  Forall (fun no =>
    check_syscall (mkInput no [9; 999; 999; 4096; 4; 0]
                     (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model
    = CheckOk socket_call_model []
    /\ check_syscall (mkInput no [3; 999; 999; 4096; 4; 0]
                       (fun _ => None) (fun _ => None))
         (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
       = CheckOk socket_call_model []
    /\ check_syscall (mkInput no [3; 999; 999; 4096; 4; 0]
                       (fun _ => None) (fun _ => None))
         (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_call_model
       = CheckReject)
    [204; 205; 208; 209; 210].
Proof. repeat constructor; check_eq. Qed.

(** setsockopt's NEGATIVE optlen is -EINVAL, but the check lives in
    [do_sock_setsockopt] (net/socket.c), which runs only once
    the fd has resolved to a socket.  So a closed fd is
    -EBADF and a live non-socket fd is -ENOTSOCK, and the -EINVAL a
    reader of the man page would expect is inadmissible in both.  That
    ordering is v6.7 and later: up to v6.6 the check sat in
    [__sys_setsockopt] ahead of the lookup, and the first line below was
    -EINVAL. *)
Example setsockopt_negative_optlen_never_beats_the_fd :
  check_syscall (mkInput 208 [9; 1; 2; 4096; Z_to_bv 64 (2 ^ 64 - 1); 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) socket_call_model
  = CheckOk socket_call_model []
  /\ check_syscall (mkInput 208 [3; 1; 2; 4096; Z_to_bv 64 (2 ^ 64 - 1); 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
     = CheckOk socket_call_model []
  /\ check_syscall (mkInput 208 [3; 1; 2; 4096; Z_to_bv 64 (2 ^ 64 - 1); 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) socket_call_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** A NULL address pointer and a NULL in/out length change nothing
    either: [move_addr_to_user] (net/socket.c) reads the length, and
    [sk_getsockopt] (net/core/sock.c) reads the option length, and both
    run after the lookup.  So the -EFAULT they would earn on a socket is
    inadmissible here. *)
Example socket_calls_null_pointers_never_beat_the_fd :
  Forall (fun no =>
    check_syscall (mkInput no [3; 0; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
    = CheckOk socket_call_model []
    /\ check_syscall (mkInput no [3; 0; 0; 0; 0; 0]
                       (fun _ => None) (fun _ => None))
         (mkEffect (errno_ret EFAULT) [] []) socket_call_model
       = CheckReject)
    [204; 205; 209].
Proof. repeat constructor; check_eq. Qed.

(** THE TWO WAVE-2 KINDS ON EVERY SOCKET CALL.  A datagram socket
    ([State.FdDgram]: fd 3 is AF_INET6, fd 4 AF_UNIX) IS a socket --
    [sock_alloc_file] gave it [socket_file_ops] -- so no call answers it
    -ENOTSOCK, and every one declines it: [Net.Socket.SoInert] in the
    five option and address calls, [Net.Socket.sockfd_lookup_errno]'s
    [None] in the two receives, and an explicit arm in bind, listen,
    accept/accept4, connect, sendto and sendmsg.  An eventfd
    ([State.FdEventfd], fd 5) is NOT a socket -- its [f_op] is
    [eventfd_fops] -- and every call answers it -ENOTSOCK, with an
    -EBADF refused.
    ADMISSION REASON: model-internal -- a decline is not observable in a
    run, and which fd kinds the wildcards reach is the model's own
    bookkeeping.

    The arguments carry a 1-byte buffer at 4096 and flag words of 0,
    except connect, which takes a 0-byte address (the copy succeeds and
    the descriptor decides), and sendmsg, which takes MSG_NOSIGNAL
    (16384), the one flag word it answers. *)
Definition wave2_kinds_model : Model :=
  with_creds demo_creds
    (mkModel
       [ (0, FdChannel 0); (3, FdDgram AF_INET6); (4, FdDgram AF_UNIX);
         (5, FdEventfd (mkEventfdCtx 0 false false)) ]
       (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None).

Definition wave2_call (no fd : word) (args : list word) (r : word)
    : check_result :=
  check_syscall (mkInput no (fd :: args) (fun _ => None) (fun _ => None))
    (mkEffect r [] []) wave2_kinds_model.

Example datagram_declines_and_eventfd_is_not_a_socket :
  Forall (fun c =>
    wave2_call (fst c) 3 (snd c) (errno_ret ENOTSOCK) = CheckUnmodeled
    /\ wave2_call (fst c) 4 (snd c) (errno_ret ENOTSOCK) = CheckUnmodeled
    /\ wave2_call (fst c) 5 (snd c) (errno_ret ENOTSOCK)
       = CheckOk wave2_kinds_model []
    /\ wave2_call (fst c) 5 (snd c) (errno_ret EBADF) = CheckReject)
  [ (200, [4096; 16; 0; 0; 0]); (201, [1; 0; 0; 0; 0]);
    (202, [0; 0; 0; 0; 0]); (203, [4096; 0; 0; 0; 0]);
    (204, [4096; 4100; 0; 0; 0]); (205, [4096; 4100; 0; 0; 0]);
    (206, [4096; 1; 0; 0; 0]); (207, [4096; 1; 0; 0; 0]);
    (208, [1; 2; 4096; 4; 0]); (209, [1; 2; 4096; 4100; 0]);
    (210, [2; 0; 0; 0; 0]); (211, [4096; 16384; 0; 0; 0]);
    (212, [4096; 0; 0; 0; 0]); (242, [0; 0; 0; 0; 0]) ].
Proof. repeat constructor; check_eq. Qed.

(* ..........................................................................
   The five ON A SOCKET.  Every claim below is derived from kernel
   source, and the version window for each is in [Sys/Net/Socket.v]
   beside the arm it justifies.
   .......................................................................... *)

(** One fd per [State.SockState] constructor, written out rather than
    reached: fresh at 6, bound at 7, listening at 8, connected at 9,
    reset at 10.  9 and 10 carry the SAME peer on purpose -- the two are
    told apart by the STATE, never by the address. *)
Definition socket_states_model : Model :=
  with_creds demo_creds
    (mkModel
       [ (0, FdChannel 0); (3, FdFile [102] 0);
         (6, FdSocket SkFresh); (7, FdSocket SkBound); (8, FdSocket SkListening);
         (9, FdSocket (SkConnected (mkPeer (Z_to_bv 32 16909060) (Z_to_bv 16 443)) 3 NFin));
         (10, FdSocket (SkReset (mkPeer (Z_to_bv 32 16909060) (Z_to_bv 16 443)) 3)) ]
       (mkVmMaps [] [] 0 0 demo_limit) IEof
       [([102], [104; 105])] None None None).

(** GETPEERNAME IS THE ARM [SkReset] EXISTS FOR.  [inet_getname] with
    [peer = 1] refuses on [!inet_dport] -- fresh, bound and listening --
    OR on [sk_state] in [TCPF_CLOSE | TCPF_SYN_SENT], which is where
    [tcp_done] left a socket the peer reset.  A CONSUMED FIN leaves
    TCP_CLOSE_WAIT instead, which is in neither disjunct, so the
    connected socket at fd 9 -- whose script is already [NFin] --
    SUCCEEDS on a real kernel and is declined here rather than answered.
    The two fds differ only in their constructor, and the model gives
    them different answers: that is the claim. *)
Example getpeername_enotconn_covers_reset_but_not_close_wait :
  Forall (fun fd =>
    check_syscall (mkInput 205 [fd; 4096; 4104; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
    = CheckOk socket_states_model [])
    [6; 7; 8; 10]
  /\ check_syscall (mkInput 205 [9; 4096; 4104; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
     = CheckUnmodeled.
Proof. split; [repeat constructor; check_eq | vm_compute; reflexivity]. Qed.

(** And the accepting half is not vacuous: on the RESET socket a claimed
    success -- the 16 bytes [move_addr_to_user] would have reported -- is
    inadmissible.  (On the connected socket no answer is inadmissible,
    because the model declines there; a decline rejects nothing, which
    is exactly why the decline must be the honest one.) *)
Example getpeername_success_on_a_reset_socket_is_rejected :
  check_syscall (mkInput 205 [10; 4096; 4104; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 16 [] []) socket_states_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** GETSOCKNAME DECLINES ON EVERY SOCKET STATE, including the fresh one
    whose answer really is 0.0.0.0:0.  [inet_getname] with [peer = 0]
    has no error return at all, so the only answer available is a
    success that writes a [sockaddr_in] -- and past [SkFresh] the port is
    an ephemeral one [inet_csk_find_open_port] drew at random.  Stating
    the decline as a lemma is what stops a later change from quietly
    inventing an address. *)
Example getsockname_declines_on_every_socket_state :
  Forall (fun fd =>
    check_syscall (mkInput 204 [fd; 4096; 4104; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
      (mkEffect 16 [] []) socket_states_model
    = CheckUnmodeled)
    [6; 7; 8; 9; 10].
Proof. repeat constructor; vm_compute; reflexivity. Qed.

(** SETSOCKOPT AND GETSOCKOPT DISAGREE ON AN UNKNOWN LEVEL, and the
    disagreement is real: the set side walks [ip_setsockopt], whose
    first statement is [if (level != SOL_IP) return -ENOPROTOOPT;],
    while the get side walks [do_ip_getsockopt], whose first statement is
    [if (level != SOL_IP) return -EOPNOTSUPP;].  Two functions, one
    file, two errnos.  Each rejects the other's, which is the half that
    makes this non-vacuous -- inventing symmetry here is the obvious
    mistake, and it is a rejected one. *)
Example unknown_level_is_enoprotoopt_setting_and_eopnotsupp_getting :
  check_syscall (mkInput 208 [6; 999; 2; 4096; 4; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
  = CheckOk socket_states_model []
  /\ check_syscall (mkInput 208 [6; 999; 2; 4096; 4; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
     = CheckReject
  /\ check_syscall (mkInput 209 [6; 999; 2; 4096; 4104; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
     = CheckOk socket_states_model []
  /\ check_syscall (mkInput 209 [6; 999; 2; 4096; 4104; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** A NEGATIVE [optlen] BEATS THE LEVEL, because [do_sock_setsockopt]
    tests it first -- before the LSM hook, before the BPF hook, before
    any dispatch.  So the same call that is -ENOPROTOOPT at length 4 is
    -EINVAL at length -1, and -ENOPROTOOPT there is inadmissible.
    [getsockopt] has no such check: its length is a USER POINTER read
    downstream of the level, so the unknown level still wins. *)
Example negative_optlen_beats_the_unknown_level :
  check_syscall (mkInput 208 [6; 999; 2; 4096; Z_to_bv 64 (2 ^ 64 - 1); 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) socket_states_model
  = CheckOk socket_states_model []
  /\ check_syscall (mkInput 208 [6; 999; 2; 4096; Z_to_bv 64 (2 ^ 64 - 1); 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** A KNOWN LEVEL IS DECLINED on both calls -- the option table itself is
    not modeled, at SOL_SOCKET (1), SOL_IP (0) or SOL_TCP (6). *)
Example a_known_level_is_declined :
  Forall (fun level =>
    check_syscall (mkInput 208 [6; level; 2; 4096; 4; 0]
                     (fun _ => None) (fun _ => None))
      (mkEffect 0 [] []) socket_states_model
    = CheckUnmodeled
    /\ check_syscall (mkInput 209 [6; level; 2; 4096; 4104; 0]
                       (fun _ => None) (fun _ => None))
         (mkEffect 0 [] []) socket_states_model
       = CheckUnmodeled)
    [0; 1; 6]
  (* AND THE UNKNOWN LEVEL, STILL ANSWERED, on both calls.  Every
     conjunct of the [Forall] is a decline, so the list on its own stays
     green if [setsockopt] and [getsockopt] stop answering ANY level --
     including the [ip_setsockopt] / [do_ip_getsockopt] pair above,
     which is the one thing these two calls do answer.  Level 999 is the
     same fd, the same option and the same model state, one level
     outside the declined set. *)
  /\ check_syscall (mkInput 208 [6; 999; 2; 4096; 4; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
     = CheckOk socket_states_model []
  /\ check_syscall (mkInput 209 [6; 999; 2; 4096; 4104; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
     = CheckOk socket_states_model [].
Proof.
  split; [repeat constructor; vm_compute; reflexivity
         |split; check_eq].
Qed.

(** SHUTDOWN'S -EINVAL IS EXACT ON EVERY SOCKET STATE, and it is the
    only shutdown answer that is.  [inet_shutdown] does [how++] and
    rejects [(how & ~SHUTDOWN_MASK) || !how] BEFORE [lock_sock] and
    before any write to [sk_shutdown], so the socket is left bit for bit
    unchanged -- which is what lets a model with no shutdown bits answer
    it at all.  [how = -1] is caught by [!how] after the increment; 3
    and 99 by the mask. *)
Example shutdown_rejects_a_bad_how_on_every_socket_state :
  Forall (fun fd =>
    Forall (fun how =>
      check_syscall (mkInput 210 [fd; how; 0; 0; 0; 0]
                       (fun _ => None) (fun _ => None))
        (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [])
      [3; 99; Z_to_bv 64 (2 ^ 64 - 1); Z_to_bv 64 (2 ^ 31 - 1)])
    [6; 7; 8; 9; 10].
Proof. repeat constructor; check_eq. Qed.

(** SHUT_WR ON A LISTENING SOCKET IS 0 AND CHANGES NOTHING.  The
    [case TCP_LISTEN:] arm is [if (!(how & RCV_SHUTDOWN)) break;], and
    for SHUT_WR the incremented [how] is 2, so the [break] fires and the
    [default:] arm -- the one that ORs the bits and calls
    [sk_prot->shutdown] -- never runs.  The model state comes back
    identical, which is the whole content of "changes nothing".  A
    -ENOTCONN or an -EINVAL here is inadmissible. *)
Example shut_wr_on_a_listener_is_zero_and_a_no_op :
  check_syscall (mkInput 210 [8; 1; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) socket_states_model
  = CheckOk socket_states_model []
  /\ check_syscall (mkInput 210 [8; 1; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
     = CheckReject
  /\ check_syscall (mkInput 210 [8; 1; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) socket_states_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** AND -ENOTCONN IS DECLINED, NOT ANSWERED, on the TCP_CLOSE states --
    the most load-bearing decline in this file.  The errno is right:
    [inet_shutdown]'s [case TCP_CLOSE:] sets [err = -ENOTCONN].  But it
    then FALLS THROUGH into [default:] and ORs the bits into
    [sk_shutdown] anyway, and net/ipv4/tcp.c [tcp_recvmsg_locked] tests
    [sk_shutdown & RCV_SHUTDOWN] BEFORE its [TCP_CLOSE -> -ENOTCONN]
    arm.  So after [shutdown(fresh, SHUT_RD)] a real [read] returns 0
    where it would otherwise return -ENOTCONN.  [State.SockState] has
    nowhere to put those bits, so answering the errno would buy a right
    return at the price of a wrong successor state -- and the next read
    would be confidently wrong.  Declining costs one fail-closed run;
    answering costs a lie one syscall later. *)
Example shutdown_declines_where_it_would_have_to_drop_the_bits :
  Forall (fun fd =>
    Forall (fun how =>
      check_syscall (mkInput 210 [fd; how; 0; 0; 0; 0]
                       (fun _ => None) (fun _ => None))
        (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled)
      [0; 1; 2])
    [6; 7; 9; 10]
  /\ Forall (fun how =>
       check_syscall (mkInput 210 [8; how; 0; 0; 0; 0]
                        (fun _ => None) (fun _ => None))
         (mkEffect 0 [] []) socket_states_model
       = CheckUnmodeled)
       [0; 2]
  (* AND THE TWO SHUTDOWN ANSWERS THAT SURVIVE, so the declines above
     read as a boundary and not as [shutdown] having gone quiet.  Both
     [Forall]s are uniformly [CheckUnmodeled], so on their own they stay
     green under any change that declines MORE -- the bad-[how] gate
     going unmodeled, or the TCP_LISTEN [break] arm going with it, which
     is the change this lemma exists to notice.  The two pinned here are
     the immediate neighbours of the declines: [how = 3] on a declining
     fd, one step outside the mask, and [how = 1] on fd 8, one step
     along from the [how] values the second [Forall] declines there. *)
  /\ check_syscall (mkInput 210 [6; 3; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) socket_states_model
     = CheckOk socket_states_model []
  /\ check_syscall (mkInput 210 [8; 1; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) socket_states_model
     = CheckOk socket_states_model [].
Proof.
  split; [repeat constructor; vm_compute; reflexivity
         |split; [repeat constructor; vm_compute; reflexivity
                 |split; check_eq]].
Qed.

(* -------------------------------------------------------------------------
   The SEND path: the accepting half

   The cases here pin the whole of [Net.Socket.SendGoes] and
   [Net.Socket.SendErr] -- the short-send prefix rule, the per-byte
   [WriteEv] alphabet on the CONNECTION's channel, the once-only
   -ECONNRESET and the SkConnected -> SkReset transition it leaves
   behind.

   The connected socket is [accepted_socket_model] above -- fd 4, the
   head connection's peer, channel 3, script [NFin].  Reusing it rather
   than writing a fresh fixture is deliberate: [NFin] is CLOSE_WAIT, the
   state a model gets wrong by reading "peer closed" as "connection
   closed", and [Net.Socket.send_state] maps it to [SendGoes].  So the
   send examples run on a socket the accept examples PROVE is reachable.
   ------------------------------------------------------------------------- *)

(** An 8-byte little-endian field at [base], as address/byte pairs, and
    a memory view over such a list.  Written this way because a
    [struct msghdr] is seven of them and [mem_ab]'s
    one-[bv_eqb]-per-byte shape does not scale to 72 bytes. *)
Definition u64_at (base v : Z) : list (Z * Z) :=
  map (fun k => ((base + Z.of_nat k)%Z,
                 (Z.shiftr v (8 * Z.of_nat k) mod 256)%Z)) (seq 0 8).

Definition mem_of (l : list (Z * Z)) : word -> option byte :=
  fun a => match find (fun p => Z.eqb (fst p) (bv_unsigned a)) l with
           | Some (_, v) => Some (Z_to_bv 8 v)
           | None => None
           end.

(** The two bytes both calls send, at 4096: "ab", exactly [mem_ab]'s. *)
Definition send_payload : list (Z * Z) := [(4096%Z, 97%Z); (4097%Z, 98%Z)].

(** A [struct msghdr] at 8192 naming one iovec at 8320, which names the
    payload.  The seven fields are at the offsets
    [Net.Socket.sendmsg_spec] reads them from: name 0, namelen 8, iov 16,
    iovlen 24, control 32, controllen 40, and FLAGS AT 48 -- whose value
    is this definition's parameter precisely so a case can set it and
    watch nothing happen. *)
Definition send_msghdr_mem (struct_flags : Z) : word -> option byte :=
  mem_of (u64_at 8192 0
       ++ u64_at 8200 0
       ++ u64_at 8208 8320
       ++ u64_at 8216 1
       ++ u64_at 8224 0
       ++ u64_at 8232 0
       ++ u64_at 8240 struct_flags
       ++ u64_at 8320 4096
       ++ u64_at 8328 2
       ++ send_payload).

(** [sendto(4, "ab", 2, MSG_NOSIGNAL, NULL, 0)] answering [r] with the
    copy-in ledger [cis].  The ledger is an argument for
    [bind_answering_at]'s reason: it is what tells the arms that read
    the payload apart from the arms that answer before it, and
    [State.mkEffect] hardcodes an EMPTY one. *)
Definition sendto_answering_with (m : Model) (r : word)
    (cis : list (word * nat)) : check_result :=
  check_syscall (mkInput 206 [4; 4096; 2; 16384; 0; 0] (mem_of send_payload)
                   (fun _ => None)) (mkEffectU r [] [] [] [] cis) m.

(** The errno form: a send that answers before it copies anything
    carries an empty ledger. *)
Definition sendto_answering (m : Model) (r : word) : check_result :=
  sendto_answering_with m r [].

(** THE SEND GOES OUT, ON THE CONNECTION'S OWN CHANNEL.  Channel 3, not
    stdout's 1 -- [Net.Socket.conn_channel] starts at 3 because 0-2 are
    stdio, and a send that emitted on the wrong channel would be
    indistinguishable from a write to stdout in the trace.  One
    [WriteEv] per byte, and the model is left ALONE: a send on a live
    connection changes no descriptor.

    THE LEDGER IS THE TWO BYTES IT ACTUALLY MOVED, and it is what makes
    a dropped [record_copyins] visible: without it the admissible effect
    would be the one carrying an EMPTY ledger, and the case below would
    stop holding in both directions at once. *)
Example send_emits_on_the_connections_channel :
  sendto_answering_with accepted_socket_model 2 [(4096, 2%nat)]
  = CheckOk accepted_socket_model [WriteEv 3 97; WriteEv 3 98]
  /\ sendto_answering accepted_socket_model 2 = CheckReject.
Proof. split; check_eq. Qed.

(** A SHORT SEND IS REAL, and it is a prefix.  Every error path in
    tcp_sendmsg_locked funnels through [do_error:], whose
    [if (copied + copied_syn) goto out;] returns the count and discards
    the error, so one byte of a two-byte send is an ordinary answer --
    and its ledger is the ONE byte it read, not the two the call named.
    What is NOT admissible: more than was readable-and-requested, and a
    zero-byte answer to a nonzero request -- a send either moves a byte
    or reports an errno, it never reports 0. *)
Example send_short_is_a_prefix_and_zero_is_not :
  sendto_answering_with accepted_socket_model 1 [(4096, 1%nat)]
  = CheckOk accepted_socket_model [WriteEv 3 97]
  /\ sendto_answering_with accepted_socket_model 3 [(4096, 3%nat)] = CheckReject
  /\ sendto_answering accepted_socket_model 0 = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** AN ERRNO-ENCODED RETURN THROUGH THE SEND ARM EVALUATES: -EINTR on a
    live connection is rejected -- the only accepting shape on
    [SendGoes] is a delivered prefix -- and closing it by [check_eq]
    pins that [check_send_on_socket] converts [ret] to a unary [nat]
    only under its range test, as [Fs.ReadWrite.check_write]'s channel
    arm does; a flat chain that converted it first would not finish on
    this statement. *)
Example send_errno_return_rejected :
  sendto_answering accepted_socket_model (errno_ret EINTR) = CheckReject.
Proof. check_eq. Qed.

(** MSG_NOSIGNAL IS THE FIRST GATE, ahead of the fd and ahead of the
    buffer.  A flagless send is declined even though this fd, this
    buffer and this count are all fine -- that is the deliberate
    departure from the kernel's order, which consults the flag last.
    MSG_NOSIGNAL|MSG_DONTWAIT is declined too: the word must be EXACTLY
    MSG_NOSIGNAL, because every other MSG_* changes what the call means
    and Linux ignores unknown bits rather than rejecting them, so a
    permissive reading would be a confidently wrong answer. *)
Example send_flag_word_must_be_exactly_nosignal :
  check_syscall (mkInput 206 [4; 4096; 2; 0; 0; 0] (mem_of send_payload)
                   (fun _ => None)) (mkEffectU 2 [] [] [] [] [(4096, 2%nat)])
    accepted_socket_model
  = CheckUnmodeled
  /\ check_syscall (mkInput 206 [4; 4096; 2; 16448; 0; 0] (mem_of send_payload)
                     (fun _ => None)) (mkEffectU 2 [] [] [] [] [(4096, 2%nat)])
       accepted_socket_model
     = CheckUnmodeled
  (* AND THE EXACT WORD, STILL GOING OUT.  The two declines above are
     both [CheckUnmodeled], so on their own they stay green if the gate
     widens to refuse MSG_NOSIGNAL as well -- [sendto] going quiet
     altogether, which is the one change this lemma exists to notice.
     The same fd, buffer, count and ledger with flags = MSG_NOSIGNAL is
     the point on the other side of the gate. *)
  /\ sendto_answering_with accepted_socket_model 2 [(4096, 2%nat)]
     = CheckOk accepted_socket_model [WriteEv 3 97; WriteEv 3 98].
Proof. split; [|split]; check_eq. Qed.

(** A model whose fd 4 carries a connection with a PENDING RESET, and
    the model the first send after it must leave behind.  [SkReset]
    records that the error has been consumed: [include/net/sock.h]'s
    [sock_error] takes it with an [xchg], and it is taken by whichever
    of read and send reaches it first -- which is why a send transitions
    the socket exactly as a read does.  Both are [accepted_socket_model]
    with fd 4 rewritten, so the queue and the handed-over count stay
    what an accept really left. *)
Definition reset_pending_socket_model : Model :=
  with_fds
    [ (4, FdSocket (SkConnected (mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0)) 3 NRst));
      (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdSocket SkListening) ]
    accepted_socket_model.

Definition reset_consumed_socket_model : Model :=
  with_fds
    [ (4, FdSocket (SkReset (mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0)) 3));
      (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdSocket SkListening) ]
    accepted_socket_model.

(** THE TWO-STEP RESET, exactly as the code produces it.  The first send
    after a peer RST is -ECONNRESET and REWRITES THE DESCRIPTOR; the
    next is -EPIPE, because the error is gone.  Neither carries a
    signal: [sk_stream_error]'s [sock_error] replaces the errno before
    the flag is consulted, so only the second call is even a candidate,
    and MSG_NOSIGNAL is set.  Both leave the ledger EMPTY: Linux answers
    from the connection state without copying a byte of the buffer. *)
Example send_consumes_the_pending_reset_once :
  sendto_answering reset_pending_socket_model (errno_ret ECONNRESET)
  = CheckOk reset_consumed_socket_model []
  /\ sendto_answering reset_consumed_socket_model (errno_ret EPIPE)
     = CheckOk reset_consumed_socket_model []
  /\ sendto_answering reset_pending_socket_model (errno_ret EPIPE)
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** [sendmsg(4, &msg, MSG_NOSIGNAL)] with the header at 8192 lands on
    the same connection, the same channel and the same events as the
    [sendto] above: one gather of one iovec is one send.

    ITS LEDGER IS THREE RANGES, IN THE ORDER THE KERNEL READ THEM: the
    56-byte header, the one 16-byte iovec descriptor, then the two
    payload bytes.  That is the whole reason [sendto]'s ledger is one
    range and this one is not -- the two calls read different things
    before they reach the same send. *)
Example sendmsg_gathers_onto_the_same_channel :
  check_syscall (mkInput 211 [4; 8192; 16384; 0; 0; 0] (send_msghdr_mem 0)
                   (fun _ => None))
    (mkEffectU 2 [] [] [] []
       [(8192, 56%nat); (8320, 16%nat); (4096, 2%nat)]) accepted_socket_model
  = CheckOk accepted_socket_model [WriteEv 3 97; WriteEv 3 98].
Proof. check_eq. Qed.

(** THE SINGLE EASIEST WAY TO GET THIS FEATURE WRONG, pinned in both
    directions.  [msg_flags] at offset 48 is READ BY NOTHING:
    [____sys_sendmsg] does
    [flags |= (msg_sys->msg_flags & allowed_msghdr_flags);] with
    [allowed_msghdr_flags] passed as 0 and then OVERWRITES the field
    with the argument, so the struct's copy cannot contribute.

    - argument MSG_NOSIGNAL, struct field 0: ACCEPTED, unchanged from
      the case above -- the field being clear takes nothing away.
    - argument 0, struct field MSG_NOSIGNAL: DECLINED.  This is the
      case that matters.  A spec reading the field would conclude "the
      flag is set, so no signal" and answer [CheckOk] for a call that
      really does take SIGPIPE and kill the process -- a wrong MODELED
      answer, which makes [strong_equiv] false rather than merely
      unprovable, and the one direction [modeled] cannot see. *)
Example sendmsg_reads_the_argument_never_the_struct_field :
  check_syscall (mkInput 211 [4; 8192; 16384; 0; 0; 0]
                   (send_msghdr_mem 0) (fun _ => None))
    (mkEffectU 2 [] [] [] []
       [(8192, 56%nat); (8320, 16%nat); (4096, 2%nat)]) accepted_socket_model
  = CheckOk accepted_socket_model [WriteEv 3 97; WriteEv 3 98]
  /\ check_syscall (mkInput 211 [4; 8192; 0; 0; 0; 0]
                     (send_msghdr_mem 16384) (fun _ => None))
       (mkEffectU 2 [] [] [] []
          [(8192, 56%nat); (8320, 16%nat); (4096, 2%nat)]) accepted_socket_model
     = CheckUnmodeled.
Proof. split; check_eq. Qed.

(** THE FD IS RESOLVED BEFORE THE HEADER, THE OPPOSITE OF [sendto].
    [__sys_sendmsg] resolves the fd and only then calls [___sys_sendmsg],
    where [copy_msghdr_from_user] lives -- so an unreadable [msg] on a
    CLOSED fd is -EBADF, while the analogous [sendto] with an unreadable
    buffer on a closed fd is -EFAULT.  Two calls that look like each
    other and are not, and the nesting is the claim: a refactor that
    hoisted the header read out to share it with [sendto] would change
    both answers and this case would stop compiling.  Both answers
    precede any copy, so both ledgers are empty. *)
Example sendmsg_resolves_the_fd_before_the_header :
  check_syscall (mkInput 211 [9; 8192; 16384; 0; 0; 0] (fun _ => None)
                   (fun _ => None)) (mkEffect (errno_ret EBADF) [] [])
    accepted_socket_model
  = CheckOk accepted_socket_model []
  /\ check_syscall (mkInput 211 [1; 8192; 16384; 0; 0; 0] (send_msghdr_mem 0)
                     (fun _ => None)) (mkEffect (errno_ret ENOTSOCK) [] [])
       accepted_socket_model
     = CheckOk accepted_socket_model [].
Proof. split; check_eq. Qed.

(** THE qemu DIVERGENCE ON THE SEND PATH.  An unmapped but
    in-range buffer is a RANGE that [import_ubuf]'s [access_ok] passes,
    so Linux resolves the fd and only then touches the buffer: on a
    connected socket [tcp_sendmsg_locked]'s copy faults and the call is
    -EFAULT with nothing recorded, and on a socket with no connection
    [sk_stream_wait_connect] answers -EPIPE without copying a byte.
    qemu's [do_sendto] locks the whole buffer first and answers -EFAULT
    in both cases.  The model follows Linux: [State.access_okb] passes
    the range, the fd resolves, and [send_bytes] faults on the empty
    readable prefix — so on the connected socket the two agree for
    different reasons, and -EPIPE is refused; the never-connected
    socket is where they part.

    THE ADDRESS is 46912512909312 = 0x2AAAABAAE000, unmapped here.  It
    is in range (2^45 < [State.TASK_SIZE]), so the range verdict is the
    kernel's, and the copy fault is what is left.  Descriptor 4
    is the accepted connection in [accepted_socket_model].

    THE THIRD CONJUNCT IS THE CONTROL: the same unmapped buffer on a
    LISTENING socket is -EPIPE, ledger empty, so what separates the two
    answers is the socket's state and not the buffer. *)
Example sendto_unmapped_buffer_in_range_faults_on_the_copy :
  check_syscall (mkInput 206 [4; 46912512909312; 1; 16384; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) accepted_socket_model
  = CheckOk accepted_socket_model []
  /\ check_syscall (mkInput 206 [4; 46912512909312; 1; 16384; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EPIPE) [] []) accepted_socket_model
     = CheckReject
  /\ check_syscall (mkInput 206 [3; 46912512909312; 1; 16384; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EPIPE) [] []) listening_socket_model
     = CheckOk listening_socket_model [].
Proof. split; [|split]; check_eq. Qed.

(* ---------------- socketpair (199), recvfrom (207), recvmsg (212) ------

   These cases check the order claims these arms make. *)

(** Everything writable, nothing readable: enough for a destination
    verdict, and it leaves [in_mem] out of the picture. *)
Definition wmem_open : word -> option byte := fun _ => Some 0.

(** An OPEN descriptor that is not a socket is -ENOTSOCK, never -EBADF,
    on both — and neither call delivers a byte, so any write at all is
    refused.  The MSG_CMSG_COMPAT bit is fail-closed: its value is
    0x80000000 on a CONFIG_COMPAT kernel and 0 on one without, and
    nothing a binary can observe says which it is running on. *)
Example recv_on_a_non_socket_descriptor :
  check_syscall (mkInput 207 [1; 4096; 8; 0; 0; 0] (fun _ => None) wmem_open)
    (mkEffect (errno_ret ENOTSOCK) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 207 [1; 4096; 8; 0; 0; 0] (fun _ => None) wmem_open)
       (mkEffect (errno_ret ENOTSOCK) [(4096, [97])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 212 [1; 4096; 0; 0; 0; 0] (fun _ => None) wmem_open)
       (mkEffect (errno_ret ENOTSOCK) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 212 [1; 4096; Z_to_bv 64 (2 ^ 31); 0; 0; 0]
                     (fun _ => None) wmem_open)
       (mkEffect (errno_ret ENOTSOCK) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled.
Proof. split; [|split; [|split]]; check_eq. Qed.

(** THE ARM THIS SECTION ARGUES ABOUT MOST, AND THE ONLY CASE THAT
    REACHES IT.  Everything above runs on a channel or an absent
    descriptor.  [sockfd_lookup_errno] answers [None] for an [FdSocket],
    which [recv_fd_answer] turns into [unmodeled] -- a DECLINE, and not
    the -ENOTSOCK every other open fd kind takes.

    THE OFFERED EFFECT IS -ENOTSOCK ON PURPOSE.  Both halves demand
    [CheckUnmodeled] while being handed exactly the answer the arm would
    give if it were folded into the wildcard above it, so flipping
    [Some (FdSocket _) => None] to [Some ENOTSOCK] turns both into
    [CheckOk] and breaks this example.  Nothing else would notice: the
    soundness and completeness lemmas in [Checks.ExecutableSpecs] are
    biconditionals over [sockfd_lookup_errno]'s definition, so they hold
    whichever answer it gives.

    Both socket STATES are used, fresh at 6 and connected at 9, because
    the decline is about the fd KIND and must not depend on the state: a
    connected socket has bytes to deliver and is still declined at these
    two entry points, which is what makes [read]/[readv] the modeled way
    to read one. *)
Example recv_declines_a_socket_descriptor :
  check_syscall (mkInput 207 [6; 4096; 8; 0; 0; 0] (fun _ => None) wmem_open)
    (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model
  = CheckUnmodeled
  /\ check_syscall (mkInput 212 [9; 4096; 0; 0; 0; 0] (fun _ => None) wmem_open)
       (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model
     = CheckUnmodeled
  (* AND THE OTHER FD KINDS, STILL ANSWERING -ENOTSOCK, on the same
     model.  Both declines above are [CheckUnmodeled], so on their own
     they stay green if [sockfd_lookup_errno] answers [None] for EVERY
     open fd -- the wildcard collapsing the other way, which is as
     plausible a wrong fix as the one the paragraph above rules out and
     is invisible to the two conjuncts that only name sockets.  The
     channel at fd 0 and the regular file at fd 3 are the boundary: not
     a socket, so not declined. *)
  /\ check_syscall (mkInput 207 [0; 4096; 8; 0; 0; 0] (fun _ => None) wmem_open)
       (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model
     = CheckOk socket_states_model []
  /\ check_syscall (mkInput 212 [3; 4096; 0; 0; 0; 0] (fun _ => None) wmem_open)
       (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model
     = CheckOk socket_states_model [].
Proof. split; [|split; [|split]]; check_eq. Qed.

(** THE ORDER, both ways.  The same closed descriptor and the same
    unreachable pointer get -EFAULT from recvfrom, which imports the
    user buffer before it resolves the descriptor, and -EBADF from
    recvmsg, which resolves the descriptor before it reads the message
    header.  Each answer is refused where the other belongs. *)
Example recv_argument_order_is_opposite :
  check_syscall (mkInput 207 [999; Z_to_bv 64 (2 ^ 63); 1; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 207 [999; Z_to_bv 64 (2 ^ 63); 1; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 212 [999; Z_to_bv 64 (2 ^ 63); 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 212 [999; Z_to_bv 64 (2 ^ 63); 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject.
Proof. split; [|split; [|split]]; check_eq. Qed.

(** THE TRAP.  socketpair(AF_INET, SOCK_STREAM, 0, sv) fails with
    -EOPNOTSUPP and has ALREADY written the two reserved descriptor
    numbers into sv — 3 and 4 here, the two lowest free ones past
    stdin/stdout/stderr.  The three refusals say the write is doing
    work: a target that skipped it, wrote different numbers, or turned
    the failure into a success is refused. *)
Example socketpair_writes_the_descriptors_before_it_fails :
  check_syscall (mkInput 199 [2; 1; 0; 4096; 0; 0] (fun _ => None) wmem_open)
    (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3;0;0;0]); (4100, [4;0;0;0])] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 199 [2; 1; 0; 4096; 0; 0] (fun _ => None) wmem_open)
       (mkEffect (errno_ret EOPNOTSUPP) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 199 [2; 1; 0; 4096; 0; 0] (fun _ => None) wmem_open)
       (mkEffect (errno_ret EOPNOTSUPP) [(4096, [4;0;0;0]); (4100, [5;0;0;0])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 199 [2; 1; 0; 4096; 0; 0] (fun _ => None) wmem_open)
       (mkEffect 0 [(4096, [3;0;0;0]); (4100, [4;0;0;0])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject.
Proof. split; [|split; [|split]]; check_eq. Qed.

(** The flag-bit check runs BEFORE the two descriptors are reserved, so
    -EINVAL leaves sv alone — and it is answered for every family, not
    just the modeled ones.  AF_UNIX SOCK_DGRAM (family 1, type 2) hands
    back two connected MESSAGE sockets, which no [State.FdEntry]
    expresses: fail closed.  (AF_UNIX SOCK_STREAM is the pair the model
    does hold; [Checks.Cases.Net.StreamPair] pins its success.) *)
Example socketpair_flag_check_precedes_the_writes :
  check_syscall (mkInput 199 [2; 257; 0; 4096; 0; 0] (fun _ => None) wmem_open)
    (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 199 [2; 257; 0; 4096; 0; 0] (fun _ => None) wmem_open)
       (mkEffect (errno_ret EINVAL) [(4096, [3;0;0;0]); (4100, [4;0;0;0])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 199 [1; 257; 0; 4096; 0; 0] (fun _ => None) wmem_open)
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 199 [1; 2; 0; 4096; 0; 0] (fun _ => None) wmem_open)
       (mkEffect 0 [(4096, [3;0;0;0]); (4100, [4;0;0;0])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled.
Proof. split; [|split; [|split]]; check_eq. Qed.

(** THE DESTINATION VERDICT, AND THE GATE IT TURNS ON.  With [sv]
    unwritable the spec cannot say the two numbers landed, so it asks
    instead whether the FIRST [put_user]'s own 4-byte range is one
    [access_ok] refuses.  Both sides of that question, because only the
    pair pins the width:

    - [sv = TASK_SIZE] is refused at the first store, so -EFAULT with
      nothing written is the answer, and a target that wrote anything
      there is refused;
    - [sv = TASK_SIZE - 5] is NOT: the first store's own 4-byte range
      ends at [TASK_SIZE - 1], inside the address space, while the
      second's ends at [TASK_SIZE + 3], past it.  Linux answers -EFAULT
      with [fd1] stored if that page is mapped and nothing stored if it
      is not — a PARTIAL outcome the model does not express, so it
      declines.

    The second case is the one with teeth.  The gate reads
    [access_okb sv 4]; written over 8 — the whole destination, which is
    the obvious way to write it — it would fail here too and this example
    would answer -EFAULT instead of declining.  So this is the check that
    fails if the width is widened. *)
Example socketpair_declines_the_partial_destination :
  check_syscall (mkInput 199 [2; 1; 0; Z_to_bv 64 TASK_SIZE; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 199 [2; 1; 0; Z_to_bv 64 TASK_SIZE; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [(Z_to_bv 64 TASK_SIZE, [3;0;0;0])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 199 [2; 1; 0; Z_to_bv 64 (TASK_SIZE - 5); 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled.
Proof. split; [|split]; check_eq. Qed.

(** THE DESTINATION THAT WALKS OFF THE TOP OF THE ADDRESS SPACE.  Three
    groups, and the reason all of them are here is the THIRD of the
    four listed at the top of [Checks.Examples]: they pin model-internal
    state and a model constant.  The state is [in_wmem]; an Sv48
    kernel maps nothing at or above 2^47, so every address a real run
    can map is one [access_ok] accepts and the walk and the range test
    never disagree there.  The constant is
    [State.TASK_SIZE].  They disagree in the DEFINITION, which is
    what matters: [Equivalence.strong_universal] quantifies over the
    image freely and nothing constrains [sv] — [socketpair_flags_ok] and
    [socketpair_modeled_b] read only [family], [type] and [protocol].

    THE WITNESS GROUPS BELOW use a memory that maps EXACTLY its own
    range and nothing else, which is what makes their walk Examples
    tight.  The contrast is [wmem_open], which answers [Some] for any
    address at all, so an Example over it could not tell a wrapping
    destination from any other.  The LAST
    group, [socketpair_dest_width_is_eight], runs over [wmem_open] on
    purpose and says so in place: it measures the [TASK_SIZE] test, so the
    mapping has to be settled for all three of its destinations at once
    rather than being a second thing that varies. *)

(** The last four bytes of the address space, so the 8-byte walk covers
    them and then the four at 0. *)
Definition socketpair_wrap_sv : word := Z_to_bv 64 (2 ^ 64 - 4).

Definition socketpair_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 4)%Z || (2 ^ 64 - 4 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

(** THE MUTATION TEST, MADE PERMANENT rather than performed once, in the
    form [Checks.Cases.Uaccess.wrap_would_pass_without_the_conjunct]
    takes.  This is what [socketpair_spec] would consult without its
    [State.access_okb] conjunct: the walk, which WRAPS because
    [State.read_bytes_map] advances in word arithmetic, and which reads
    all eight bytes back off a memory that maps only those eight.  It
    says "writable", and the spec would answer [socketpair_written] with
    both descriptor numbers stored — where
    Linux's first [put_user] is refused by [access_ok] and the call is
    -EFAULT with nothing written.

    Pinning it beside the guard is what stops the two Examples below from
    going vacuous: either would also pass if [socketpair_wrap_sv] stopped
    wrapping or [socketpair_wrap_mem] stopped mapping the range, and then
    they would be testing nothing.  With this beside them the pair can
    only both hold when the range really is mapped end to end AND the
    guard declines it anyway. *)
Example socketpair_wrap_would_pass_the_bare_walk :
  read_bytes_map socketpair_wrap_mem socketpair_wrap_sv (Z_to_bv 64 8) <> None.
Proof. vm_compute. discriminate. Qed.

(** The guard declines it, because [State.access_okb] — the model's
    transcription of [__access_ok], written as a subtraction so the
    wrapping sum is never formed — refuses the range on its
    [addr <= TASK_SIZE - size] half.  Delete the conjunct from
    [Specs.socketpair_dest_writable] and this Example fails. *)
Example socketpair_wrap_dest_is_not_writable :
  socketpair_dest_writable socketpair_wrap_mem socketpair_wrap_sv = false.
Proof. vm_compute. reflexivity. Qed.

(** THE ONE THAT MATTERS, at the checker: -EFAULT with nothing written is
    the answer, and the write the bare walk would admit is refused.  The
    second half is the negative direction — the effect it rejects is
    exactly the one Linux cannot produce and the bare walk would accept,
    two descriptor numbers stored at [2^64 - 4] and, after the word
    wrapped, at 0. *)
Example socketpair_wrapping_destination_is_efault :
  check_syscall (mkInput 199 [2; 1; 0; socketpair_wrap_sv; 0; 0]
                   (fun _ => None) socketpair_wrap_mem)
    (mkEffect (errno_ret EFAULT) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 199 [2; 1; 0; socketpair_wrap_sv; 0; 0]
                     (fun _ => None) socketpair_wrap_mem)
       (mkEffect (errno_ret EOPNOTSUPP)
                 [(socketpair_wrap_sv, [3;0;0;0]); (0, [4;0;0;0])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject.
Proof. split; check_eq. Qed.

(** PAST [TASK_SIZE], WHERE THE RANGE DOES NOT WRAP AND IS STILL
    REFUSED.  This is the case that discriminates the guard, exactly as
    [Checks.Cases.Uaccess.high_range_is_refused] does for the shared one:
    [sv = 2^63] with an 8-byte destination sums to 2^63 + 8, comfortably
    under 2^64, so the walk visits the bytes the sum names and a bare
    no-wrap test would admit it.  riscv64's [access_ok] refuses it
    anyway, because [__access_ok] tests [addr <= TASK_SIZE - size].
    Without this pair the three Examples above pass under either
    spelling.  The boundary itself is [socketpair_dest_width_is_eight]
    below, which measures the WIDTH of the conjunct. *)
Definition socketpair_high_mem : word -> option byte :=
  fun a => if ((2 ^ 63 <=? bv_unsigned a)%Z && (bv_unsigned a <? 2 ^ 63 + 8)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

(** The control, in the same shape and for the same reason as
    [socketpair_wrap_would_pass_the_bare_walk] above: the range really is
    mapped end to end, so the guard Example beside it cannot pass by the
    memory quietly stopping short. *)
Example socketpair_high_range_reads :
  read_bytes_map socketpair_high_mem (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 8)
    <> None.
Proof. vm_compute. discriminate. Qed.

(** And it does NOT wrap — its [Z] sum is 2^63 + 8, under 2^64 — so a
    bare no-wrap test would have admitted it.  This Example is about the
    WITNESS and not about the guard: it is what makes
    [socketpair_past_long_max_is_not_writable] below read as a statement
    about [TASK_SIZE] rather than about the wrap, and it is that one,
    not this one, that fails when the conjunct is deleted. *)
Example socketpair_high_range_would_pass_a_no_wrap_test :
  (two_pow_64 <=? bv_unsigned (Z_to_bv 64 (2 ^ 63))
                 + bv_unsigned (Z_to_bv 64 8))%Z = false.
Proof. vm_compute. reflexivity. Qed.

Example socketpair_past_long_max_is_not_writable :
  socketpair_dest_writable socketpair_high_mem (Z_to_bv 64 (2 ^ 63)) = false.
Proof. vm_compute. reflexivity. Qed.

Example socketpair_past_long_max_at_the_checker :
  check_syscall (mkInput 199 [2; 1; 0; Z_to_bv 64 (2 ^ 63); 0; 0]
                   (fun _ => None) socketpair_high_mem)
    (mkEffect (errno_ret EFAULT) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 199 [2; 1; 0; Z_to_bv 64 (2 ^ 63); 0; 0]
                     (fun _ => None) socketpair_high_mem)
       (mkEffect (errno_ret EOPNOTSUPP)
                 [(Z_to_bv 64 (2 ^ 63), [3;0;0;0]);
                  (Z_to_bv 64 (2 ^ 63 + 4), [4;0;0;0])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject.
Proof. split; check_eq. Qed.

(** THE WIDTH OF THE CONJUNCT IS 8, AND THIS IS WHAT PINS IT.  Three
    adjacent destinations, one step apart at the top of what
    [State.access_okb] accepts, over [wmem_open] so that the MAPPING is
    settled for all three and the only thing separating them is the
    [TASK_SIZE] test:

    - [TASK_SIZE - 8] is the LAST [sv] whose two 4-byte stores are
      BOTH accepted, so the spec still answers with both writes.  This is
      the positive half: the conjunct costs the walk nothing it was ever
      entitled to.  A target that answered -EFAULT there instead is
      refused.

    - [TASK_SIZE - 7] is the first where the SECOND store is refused
      and the first is not, so Linux writes [fd1] (the page is mapped
      here) and returns -EFAULT — a PARTIAL write this model cannot
      express — and the model declines.  Narrow the conjunct to 4 and
      this case turns into two writes, which Linux never produces.
    - [TASK_SIZE - 3] is the first where the FIRST store is refused,
      so nothing is written and -EFAULT is the whole answer.

    With [State.TASK_SIZE] the kernel of record's own limit, the three
    bullets are flat claims about Linux at three addresses under Sv48.
    The middle one is the case with teeth, and it is the reason the
    conjunct is [access_okb sv 8] rather than [access_okb sv 4]; widen it
    to 16 and the first case falls through instead.

    NOTE WHAT THE FIRST CASE ASSUMES.  It has a destination MAPPED in the
    last eight bytes under [TASK_SIZE], where a real process's stack top
    can sit ([State.sp_window_hi] is the same number), so the shape is
    reachable and not only expressible.  [wmem_open] is the map that
    makes it so. *)
Example socketpair_dest_width_is_eight :
  check_syscall (mkInput 199 [2; 1; 0; Z_to_bv 64 (TASK_SIZE - 8); 0; 0]
                   (fun _ => None) wmem_open)
    (mkEffect (errno_ret EOPNOTSUPP)
              [(Z_to_bv 64 (TASK_SIZE - 8), [3;0;0;0]);
               (Z_to_bv 64 (TASK_SIZE - 4), [4;0;0;0])] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 199 [2; 1; 0; Z_to_bv 64 (TASK_SIZE - 8); 0; 0]
                     (fun _ => None) wmem_open)
       (mkEffect (errno_ret EFAULT) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 199 [2; 1; 0; Z_to_bv 64 (TASK_SIZE - 7); 0; 0]
                     (fun _ => None) wmem_open)
       (mkEffect (errno_ret EOPNOTSUPP)
                 [(Z_to_bv 64 (TASK_SIZE - 7), [3;0;0;0]);
                  (Z_to_bv 64 (TASK_SIZE - 3), [4;0;0;0])] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled
  /\ check_syscall (mkInput 199 [2; 1; 0; Z_to_bv 64 (TASK_SIZE - 3); 0; 0]
                     (fun _ => None) wmem_open)
       (mkEffect (errno_ret EFAULT) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [].
Proof. split; [|split; [|split]]; check_eq. Qed.

(** PAIR 4 — A WRITE TO A SOCKET WITH NO CONNECTION IS ANSWERED, WHERE
    IT USED TO BE REFUSED PERMANENTLY, AND A CONNECTED SOCKET IS STILL
    REFUSED (OSSV-266).

    [Sys.Fs.ReadWrite.write_spec]'s socket arm used to answer
    [unmodeled] for every socket, and its comment said the refusal was
    PERMANENT: answering -EPIPE and continuing would assert that the
    process SURVIVED, which is a confidently wrong answer where Linux
    kills it.  The model can now say the true thing.  net/core/stream.c
    [sk_stream_wait_connect] :60-88 fails a send on a socket that is
    not connected, and [sk_stream_error] :190-198 answers -EPIPE and
    sends SIGPIPE; write(2) cannot suppress it, because MSG_NOSIGNAL
    reaches net/socket.c [sock_write_iter] only from [IOCB_NOSIGNAL]
    (:1193-1194), which include/linux/fs.h [iocb_flags] never sets
    (Linux v6.18.46, commit 1f99e9ab748f).

    The first conjunct is the new answer on a FRESH socket -- one
    [socket(2)] has minted and nothing has connected --
    [State.sock_send_dead] true: -EPIPE and a death by signal 13.  The
    second is the same on a RESET connection, the other shape
    [sock_send_dead] admits.  The third is the neighbouring case STILL
    REFUSED, and it is refused for a reason this revision did not
    touch: on [SkConnected] the send either goes out as a short count
    or blocks, and the model carries no send buffer to decide which, so
    it fails closed there as it always did.  The fourth is the
    discrimination in the other direction: the killing answer is
    refused on the connected socket, so the arm has not become
    constantly killing. *)
Example write_socket_with_no_connection_is_answered :
  check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model
  = CheckOk (with_killed (Z_to_bv 64 13) fresh_socket_model) []
  /\ check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret EPIPE) [] []) reset_socket_model
     = CheckOk (with_killed (Z_to_bv 64 13) reset_socket_model) []
  /\ check_syscall (mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
       (connected_socket_model NFin)
     = CheckUnmodeled
  /\ check_syscall (mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret EPIPE) [] []) (connected_socket_model NFin)
     = CheckUnmodeled.
Proof. split; [|split; [|split]]; check_eq. Qed.

(* =========================================================================
   THE FOUR USER READS THAT WALKED OFF THE TOP OF THE ADDRESS SPACE

   bind's address, connect's address, getsockopt's four-byte [optlen] and
   sendmsg's fifty-six-byte header each called [State.read_bytes_map]
   bare.  That walk advances in WORD arithmetic and WRAPS at 2^64, so a
   pointer in the last bytes of the address space read the bytes below
   the wrap and then the bytes from 0 on, said [Some], and the arm then
   ANSWERED the call on them — a wrong answer, not a decline.  Each now
   goes through [State.copy_bytes_map], which is [State.access_okb] and
   then that same walk, the shape [socketpair_dest_writable] spells for
   its destination above.

   EACH GROUP IS A PAIR, and both halves are needed.  The wrapping call
   is refused — and a NEIGHBOURING ordinary call at the top of what
   [State.access_okb] accepts is still answered, so the guard is not a
   blanket refusal of every high address.  A third Example per group
   pins that the walk alone really would have passed, in the form
   [socketpair_wrap_would_pass_the_bare_walk] takes: without it the
   refusal would also hold if the memory quietly stopped mapping the
   range, and the pair would be testing nothing.

   THE MEMORIES MAP EXACTLY THEIR OWN RANGE and nothing else, for that
   reason.  [wmem_open] would answer [Some] at every address and could
   not tell a wrapping pointer from any other.
   ========================================================================= *)

(* ---- bind (200): the address ------------------------------------------- *)

(** Eight bytes below the top and eight from 0: the 16-byte
    [struct sockaddr] walk covers both halves.  The byte at the base is
    AF_INET (2, host order) and every other is zero, so the address
    decodes to AF_INET / port 0 / INADDR_ANY — the ONE address
    [bind_spec] accepts.  That is deliberate: before the guard this call
    did not merely fault late, it SUCCEEDED and bound the socket. *)
Definition bind_wrap_addrp : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition bind_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 8)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (if bv_eqb a bind_wrap_addrp then Z_to_bv 8 2 else Z_to_bv 8 0)
           else None.

Example bind_wrap_would_pass_the_bare_walk :
  read_bytes_map bind_wrap_mem bind_wrap_addrp (Z_to_bv 64 16) <> None.
Proof. vm_compute. discriminate. Qed.

Example bind_wrap_address_is_not_copyable :
  copy_bytes_map bind_wrap_mem bind_wrap_addrp 16 = None.
Proof. vm_compute. reflexivity. Qed.

(** -EFAULT with nothing copied is the answer, and the success the bare
    walk admitted is refused.  [move_addr_to_kernel] (net/socket.c,
    [move_addr_to_kernel]) copies with [copy_from_user], whose
    [access_ok] refuses this range (include/asm-generic/access_ok.h,
    [__access_ok]). *)
Example bind_wrapping_address_is_efault :
  check_syscall (mkInput 200 [3; bind_wrap_addrp; 16; 0; 0; 0]
                   bind_wrap_mem (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model
  = CheckOk fresh_socket_model []
  /\ check_syscall (mkInput 200 [3; bind_wrap_addrp; 16; 0; 0; 0]
                     bind_wrap_mem (fun _ => None))
       (mkEffectU (Z_to_bv 64 0) [] [] [] [] [(bind_wrap_addrp, 16%nat)])
       fresh_socket_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** THE NEIGHBOUR, and the half that says the rule still works: the last
    sixteen bytes [State.access_okb] accepts, mapped end to end, with
    the same address in them.  The call is still judged — the
    -EADDRINUSE [inet_csk_get_port] can always answer is accepted with
    the copy-in ledger — and -EFAULT is refused there. *)
Definition bind_top_addrp : word := Z_to_bv 64 (TASK_SIZE - 16).

Definition bind_top_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 16 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (if bv_eqb a bind_top_addrp then Z_to_bv 8 2 else Z_to_bv 8 0)
           else None.

Example bind_at_the_top_still_answers :
  check_syscall (mkInput 200 [3; bind_top_addrp; 16; 0; 0; 0]
                   bind_top_mem (fun _ => None))
    (mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(bind_top_addrp, 16%nat)])
    fresh_socket_model
  = CheckOk fresh_socket_model []
  /\ check_syscall (mkInput 200 [3; bind_top_addrp; 16; 0; 0; 0]
                     bind_top_mem (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- connect (203): the address ---------------------------------------- *)

(** The same wrap, with every byte zero: [sa_family] is AF_UNSPEC, which
    on a fresh socket is [tcp_disconnect] on a socket with nothing to
    disconnect and RETURNS 0.  So this call too was answered, and
    answered with a success, before the guard. *)
Definition connect_wrap_addrp : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition connect_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 8)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example connect_wrap_would_pass_the_bare_walk :
  read_bytes_map connect_wrap_mem connect_wrap_addrp (Z_to_bv 64 16) <> None.
Proof. vm_compute. discriminate. Qed.

Example connect_wrap_address_is_not_copyable :
  copy_bytes_map connect_wrap_mem connect_wrap_addrp 16 = None.
Proof. vm_compute. reflexivity. Qed.

Example connect_wrapping_address_is_efault :
  check_syscall (mkInput 203 [3; connect_wrap_addrp; 16; 0; 0; 0]
                   connect_wrap_mem (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model
  = CheckOk fresh_socket_model []
  /\ check_syscall (mkInput 203 [3; connect_wrap_addrp; 16; 0; 0; 0]
                     connect_wrap_mem (fun _ => None))
       (mkEffectU (Z_to_bv 64 0) [] [] [] [] [(connect_wrap_addrp, 16%nat)])
       fresh_socket_model
     = CheckReject.
Proof. split; check_eq. Qed.

Definition connect_top_addrp : word := Z_to_bv 64 (TASK_SIZE - 16).

Definition connect_top_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 16 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example connect_at_the_top_still_answers :
  check_syscall (mkInput 203 [3; connect_top_addrp; 16; 0; 0; 0]
                   connect_top_mem (fun _ => None))
    (mkEffectU (Z_to_bv 64 0) [] [] [] [] [(connect_top_addrp, 16%nat)])
    fresh_socket_model
  = CheckOk fresh_socket_model []
  /\ check_syscall (mkInput 203 [3; connect_top_addrp; 16; 0; 0; 0]
                     connect_top_mem (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** ---- connect (203): the ZERO LENGTH, WHICH THE RANGE TEST MUST NOT SEE

    [move_addr_to_kernel] is
    [if (ulen < 0 || ulen > 128) return -EINVAL;
     if (ulen == 0) return 0;
     if (copy_from_user(...)) return -EFAULT;] (net/socket.c), so a
    zero-length address RETURNS BEFORE [copy_from_user] and the pointer
    is never looked at: [connect(fd, p, 0)] is never -EFAULT, for any
    [p].  [State.access_okb a 0] is
    [(0 <=? TASK_SIZE) && (bv_unsigned a <=? TASK_SIZE)], FALSE above
    the limit, so routing the zero through [State.copy_bytes_map] made
    this call -EFAULT — a wrong answer, not a decline, and the one the
    guard itself introduced.  [Net.Socket.move_addr_bytes] is the fix.

    THE PAIR.  The first two conjuncts are the case the model used to
    get wrong, on a socket and on a channel fd — the two different
    answers a zero length has, which is why connect cannot borrow
    [bind_spec]'s single -EINVAL arm — and each refuses -EFAULT beside
    it.  The last two are the CONTROL at the SAME pointer with ONE byte
    asked for: there [copy_from_user] really does run, [access_ok]
    really does refuse the range, and -EFAULT is still the only answer.
    A fix that dropped the range test instead of ordering the zero
    ahead of it would pass the first half and fail this one.

    Every arm here is ABOVE the ledger or records nothing, so
    [connect_answering] is the right spelling throughout: a zero-length
    address reads no user byte. *)
(** THE CAUSE, pinned so the repair cannot be undone by accident: the
    range test REFUSES a zero-length range above the limit, and the
    unguarded copy therefore answers [None] there, which is why
    [Net.Socket.move_addr_bytes] has to decide the zero before the pair
    is consulted.  The control beside it is the same test at the same
    length one byte below [State.TASK_SIZE], where it passes — so this
    is a statement about the LIMIT and not about zero lengths. *)
Example zero_length_range_above_the_limit_is_refused :
  access_okb connect_wrap_addrp 0 = false
  /\ copy_bytes_map (fun _ => None) connect_wrap_addrp 0 = None
  /\ access_okb (Z_to_bv 64 TASK_SIZE) 0 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Example connect_zero_length_never_faults :
  connect_answering (fun _ => None) listening_socket_model
    3 connect_wrap_addrp 0 (errno_ret EINVAL) = CheckOk listening_socket_model []
  /\ connect_answering (fun _ => None) listening_socket_model
       3 connect_wrap_addrp 0 (errno_ret EFAULT) = CheckReject
  /\ connect_answering (fun _ => None) listening_socket_model
       1 connect_wrap_addrp 0 (errno_ret ENOTSOCK) = CheckOk listening_socket_model []
  /\ connect_answering (fun _ => None) listening_socket_model
       1 connect_wrap_addrp 0 (errno_ret EFAULT) = CheckReject
  /\ connect_answering (fun _ => None) listening_socket_model
       3 connect_wrap_addrp 1 (errno_ret EFAULT) = CheckOk listening_socket_model []
  /\ connect_answering (fun _ => None) listening_socket_model
       3 connect_wrap_addrp 1 (errno_ret EINVAL) = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE ZERO LENGTH IS UNCHANGED WHERE IT WAS ALREADY RIGHT, which is
    what says the repair is an ORDERING and not a new acceptance: at a
    readable pointer well below [State.TASK_SIZE] the answer is the same
    -EINVAL it always was, and a success is still refused. *)
Example connect_zero_length_below_the_limit_is_unchanged :
  connect_answering connect_addr_mem listening_socket_model 3 8192 0
    (errno_ret EINVAL) = CheckOk listening_socket_model []
  /\ connect_answering connect_addr_mem listening_socket_model 3 8192 0 0
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- getsockopt (209): the four-byte [optlen] --------------------------- *)

(** Two bytes below the top and two from 0.  Here the ERRNO does not
    move — [do_sock_getsockopt] discards what it read — so what the bare
    walk got wrong was the LEDGER: it claimed four bytes had left user
    memory on a call where [copy_from_user]'s [access_ok] refused the
    range and moved none, and [eff_copyins] charges a first touch
    against the backing limit. *)
Definition getsockopt_wrap_optlenp : word := Z_to_bv 64 (2 ^ 64 - 2).

Definition getsockopt_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 2)%Z || (2 ^ 64 - 2 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example getsockopt_wrap_would_pass_the_bare_walk :
  read_bytes_map getsockopt_wrap_mem getsockopt_wrap_optlenp (Z_to_bv 64 4)
    <> None.
Proof. vm_compute. discriminate. Qed.

Example getsockopt_wrap_optlen_is_not_copyable :
  copy_bytes_map getsockopt_wrap_mem getsockopt_wrap_optlenp 4 = None.
Proof. vm_compute. reflexivity. Qed.

Example getsockopt_wrapping_optlen_records_nothing :
  check_syscall (mkInput 209 [3; 17; 4; 4096; getsockopt_wrap_optlenp; 0]
                   getsockopt_wrap_mem (fun _ => None))
    (mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] []) fresh_socket_model
  = CheckOk fresh_socket_model []
  /\ check_syscall (mkInput 209 [3; 17; 4; 4096; getsockopt_wrap_optlenp; 0]
                     getsockopt_wrap_mem (fun _ => None))
       (mkEffectU (errno_ret EOPNOTSUPP) [] [] [] []
                  [(getsockopt_wrap_optlenp, 4%nat)])
       fresh_socket_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** The neighbour: the last four bytes [State.access_okb] accepts,
    mapped, where the ledger IS required. *)
Definition getsockopt_top_optlenp : word := Z_to_bv 64 (TASK_SIZE - 4).

Definition getsockopt_top_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 4 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example getsockopt_at_the_top_still_records :
  check_syscall (mkInput 209 [3; 17; 4; 4096; getsockopt_top_optlenp; 0]
                   getsockopt_top_mem (fun _ => None))
    (mkEffectU (errno_ret EOPNOTSUPP) [] [] [] []
               [(getsockopt_top_optlenp, 4%nat)])
    fresh_socket_model
  = CheckOk fresh_socket_model []
  /\ check_syscall (mkInput 209 [3; 17; 4; 4096; getsockopt_top_optlenp; 0]
                     getsockopt_top_mem (fun _ => None))
       (mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] []) fresh_socket_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- sendmsg (211): the fifty-six-byte header --------------------------- *)

(** Eight bytes below the top and forty-eight from 0, all zero: the
    whole [struct user_msghdr] reads back, with a NULL [msg_name], no
    descriptors and no control block, so before the guard this call was
    answered as an ordinary zero-length send rather than faulting.
    [copy_msghdr_from_user] (net/socket.c, [copy_msghdr_from_user])
    answers -EFAULT instead, because its [copy_from_user] tests
    [access_ok] over the whole 56 bytes. *)
Definition sendmsg_wrap_msgp : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition sendmsg_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 48)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example sendmsg_wrap_would_pass_the_bare_walk :
  read_bytes_map sendmsg_wrap_mem sendmsg_wrap_msgp (Z_to_bv 64 MSGHDR_SIZE)
    <> None.
Proof. vm_compute. discriminate. Qed.

Example sendmsg_wrap_header_is_not_copyable :
  copy_bytes_map sendmsg_wrap_mem sendmsg_wrap_msgp MSGHDR_SIZE = None.
Proof. vm_compute. reflexivity. Qed.

(** -EFAULT with an empty ledger is the whole answer, and the
    zero-length send the bare walk admitted — which would have recorded
    the header as copied — is refused.  The flags are MSG_NOSIGNAL,
    which is the only value [send_flags_modeled] admits, so that this
    example measures the header read and not the flag gate. *)
Example sendmsg_wrapping_header_is_efault :
  check_syscall (mkInput 211 [4; sendmsg_wrap_msgp; 16384; 0; 0; 0]
                   sendmsg_wrap_mem (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) accepted_socket_model
  = CheckOk accepted_socket_model []
  /\ check_syscall (mkInput 211 [4; sendmsg_wrap_msgp; 16384; 0; 0; 0]
                     sendmsg_wrap_mem (fun _ => None))
       (mkEffectU (Z_to_bv 64 0) [] [] [] []
                  [(sendmsg_wrap_msgp, Z.to_nat MSGHDR_SIZE)])
       accepted_socket_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** THE NEIGHBOUR FOR sendmsg IS THE WORKED SEND ABOVE
    ([sendmsg_gathers_onto_the_same_channel]): an ordinary header at
    8192 naming one descriptor at 8320 and two payload bytes at 4096 is
    still answered, with the same three-range ledger.  It is restated
    here as the positive half of this pair, and it also pins the import:
    the descriptor array and the payload now go through
    [State.import_iovecs], which adds the array's own [access_ok] and
    the per-segment one, and this says those tests cost an ordinary call
    nothing. *)
Example sendmsg_ordinary_header_still_sends :
  check_syscall (mkInput 211 [4; 8192; 16384; 0; 0; 0] (send_msghdr_mem 0)
                   (fun _ => None))
    (mkEffectU 2 [] [] [] []
       [(8192, 56%nat); (8320, 16%nat); (4096, 2%nat)]) accepted_socket_model
  = CheckOk accepted_socket_model [WriteEv 3 97; WriteEv 3 98]
  /\ check_syscall (mkInput 211 [4; 8192; 16384; 0; 0; 0] (send_msghdr_mem 0)
                     (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) accepted_socket_model
     = CheckReject.
Proof. split; check_eq. Qed.
