(** * LinuxProcessSem.Sys.Fs.ReadWrite — read (63), write (64), pread64 (67), pwrite64 (68), writev (66), readv (65), lseek (62)

    This file answers to Linux [fs/read_write.c]: it holds what the
    kernel defines there, and nothing else.  Which file a spec belongs
    in is therefore not a judgement call — look up where the kernel
    defines the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** write's injectable failure, and it has exactly one: the PAGE a
    write into an empty pipe has to get before it can copy.

    [anon_pipe_write] (fs/pipe.c, Linux v6.18.46) skips its merge path
    for an empty pipe — the guard is [if (chars && !was_empty)] (:478)
    — and the ring loop then opens with
    [page = anon_pipe_get_page(pipe); if (unlikely(!page)) { if (!ret)
    ret = -ENOMEM; break; }] (:515-519).  [anon_pipe_get_page] hands
    back a cached [pipe->tmp_page] when there is one and otherwise
    [alloc_page(GFP_HIGHUSER | __GFP_ACCOUNT)], which can fail — under
    memory pressure, or on a memory cgroup at its limit, since
    [__GFP_ACCOUNT] charges the page.  Nothing in the model's state
    decides which, so the answer is the ENVIRONMENT's, exactly as
    [Open.openat_errnos], [Pipe.pipe2_errnos] and [Net.Socket.socket_errnos]
    are: the arm offers it beside the answer the state does determine,
    and [Run.injected_table] registers it so a statement may read the
    family as forced-only instead.

    [break] with [ret] still 0 means NO byte was copied and the pipe is
    untouched, so the errno stands alone — there is no short count to
    pair it with.  A write that MERGES allocates nothing and cannot
    reach it ([State.pipe_needs_page]).

    THE OTHER -ENOMEM ON THIS FILE'S SYSCALLS IS NOT HERE.
    [__import_iovec] allocates for 9 through [IOV_MAX] descriptors and
    may answer -ENOMEM there too (lib/iov_iter.c); [readv] declines that
    band outright ([readv_heap_iovecb]) and [writev]'s header records it
    as unrepresented.  Those are shapes the model refuses to judge, not
    answers it offers, so they add nothing to this list. *)
Definition write_errnos : list Z := [ENOMEM].

(** The zero-fill a call forces on the model is one the model can
    represent: [endpoint], the byte position the call opens the file out
    to, lies at most [Uaccess.rw_bytes_max] past the current end.  Linux leaves
    the region between as a sparse hole for free; the model holds the
    file as a flat byte list and has to BUILD those bytes, so the
    distance — not the file — is what is bounded.

    Two calls extend a file that way, a write past end-of-file and a
    GROWING [ftruncate], and they are bounded by one comparison here
    rather than by two copies of it.  Their guards below differ only in
    which position each measures and in the carve-out each makes, and
    each keeps its own name so a caller's error message still says which
    syscall was declined. *)
Definition modeled_zero_fill (endpoint : Z) (data : list byte) : bool :=
  (endpoint - Z.of_nat (length data) <=? rw_bytes_max)%Z.

(** The hole this write opens past end-of-file is one the model can
    represent.  A write past the end zero-fills the gap
    ([Fs.file_write]), and the model holds a file as a flat byte list,
    so the hole is bytes it has to BUILD — where on Linux a hole in a
    sparse file costs nothing.  A zero-length write opens no hole at all
    ([file_write]'s [[]] arm leaves the file alone, as Linux does), so
    it is judged at any offset. *)
Definition modeled_file_gap (data : list byte) (off : word)
    (bs : list byte) : bool :=
  match bs with
  | [] => true
  | _ :: _ => modeled_zero_fill (bv_unsigned off) data
  end.

Lemma file_gap_in_range : forall data off bs,
  (bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
  negb (modeled_file_gap data off bs) = false.
Proof.
  intros data off bs H. unfold modeled_file_gap, modeled_zero_fill.
  destruct bs as [|b bs]; [reflexivity|].
  rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

(** An APPEND write opens no hole, which is why [write_spec]'s
    [FdFileA] arm carries no [modeled_file_gap] guard where the
    [FdFileW] arm needs one.  The position such a write uses is the
    file's own length, so the distance the model would have to zero-fill
    is at most zero: [bv_unsigned (len_word data)] is
    [Z.of_nat (length data)] reduced mod [2 ^ 64], which never exceeds
    [Z.of_nat (length data)] itself.  Stated as a remark rather than
    left to a reader comparing two arms. *)
(** Where an append write leaves [f_pos], and the zero-length case is
    the whole reason this is a definition rather than an expression.

    A DELIVERING append write ends at the new end of file, [ki_pos + n]
    with [ki_pos] the old size.  A ZERO-LENGTH one leaves [f_pos]
    EXACTLY WHERE IT WAS, and not because the arithmetic happens to
    agree — it does not, since the offset can sit anywhere an [lseek]
    put it.  Two things in Linux say so, and the first is enough:
    [generic_write_checks] (mm/filemap.c) opens with
    [if (!iov_iter_count(from)) return 0;] BEFORE its
    [if (iocb->ki_flags & IOCB_APPEND) iocb->ki_pos = i_size_read(inode);],
    so a zero-count write never even computes the append position; and
    [new_sync_write] (fs/read_write.c) writes the position back only
    under [if (ret > 0 && ppos)], so a 0 return copies nothing back.
    Linux v6.18.46.

    The [FdFileW] arm needs no such definition because [off + len_word bs]
    is already [off] when [bs] is empty.  Here the two are different
    words, which is what makes an unconditional end-of-file assignment a
    confidently wrong answer at [count = 0] rather than a harmless
    restatement: [lseek(fd, 0, SEEK_CUR)] afterwards would report the
    file's size where Linux reports the untouched offset. *)
Definition append_new_pos (data bs : list byte) (off : word) : word :=
  match bs with
  | [] => off                              (* zero-length: f_pos untouched *)
  | _ :: _ => len_word data + len_word bs  (* the new end of file *)
  end.

Remark append_opens_no_gap : forall (data bs : list byte),
  modeled_file_gap data (len_word data) bs = true.
Proof.
  intros data bs. destruct bs as [|b bs']; [reflexivity|].
  unfold modeled_file_gap, modeled_zero_fill, len_word.
  apply Z.leb_le. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  pose proof (Z.mod_le (Z.of_nat (length data)) (bv_modulus 64)
                (Nat2Z.is_nonneg _) (bv_modulus_pos 64)).
  unfold rw_bytes_max. lia.
Qed.

(** [read fd buf count].

    The DESTINATION prefix [buf, buf+n) must be writable-mapped
    ([in_wmem]) for exactly the [n] bytes actually DELIVERED — the
    analogue of the kernel's copy_to_user check, which only touches the
    bytes it copies.  Real Linux: read(fd, buf, 100) on a file holding
    3 bytes with buf+50 unmapped returns 3 and never touches buf+50, so
    demanding the whole [count] be writable would reject runs a real
    kernel produces.  Bytes beyond the delivered prefix are never
    inspected; a zero-byte read ([count = 0], EOF) checks nothing.

    Channel (stdin): the bytes come from the run's INPUT STREAM
    ([State.InputStream], threaded in [m_stdin]) — not from an
    environment choice.  If the stream has ended ([IEof]) the read
    returns 0 (end-of-file), consuming nothing; this is STICKY by
    construction, since [IEof] has no successor.  Otherwise the read
    delivers a NONEMPTY PREFIX of the remaining stream, of at most
    [count] bytes: WHICH bytes is determined by the input, only HOW MANY
    is nondeterministic — short reads are real, a terminal can deliver
    fewer bytes than asked.  The delivered bytes are written to [buf],
    the stream advances past them, and each is recorded in the trace as
    one [ReadEv] (see State.event).  A delivery whose prefix is not
    writable is not admissible (no byte can land there); if not even ONE
    byte can land, no delivery is possible at all — and, since end-of-input
    is not an available alternative either, the read returns -EFAULT: the
    copy_to_user failure with zero bytes copied, a real kernel return
    rather than a modeling gap.  Nothing is written and nothing is
    consumed from the stream.  [count = 0] returns 0 without implying EOF
    (POSIX).

    File: fully deterministic — the bytes come from the interpreted file
    system at the fd's offset, truncated at end-of-file, and the offset
    advances.  When the delivered prefix is not fully writable-mapped,
    its FIRST byte decides:
    - not even that byte can land: -EFAULT, again a real kernel return
      (the same copy_to_user failure), with no bytes delivered and the
      offset unchanged;
    - a strict, nonempty writable prefix: [unmodeled] (fail closed).
      Linux returns the bytes the copy reported before it faulted, and
      that count is the copy routine's rounded progress rather than the
      writable prefix — the argument is on the partial-destination note
      above [readv_imported], which applies to [read] verbatim.
    The CHANNEL arm carries the same decline: a pipe whose queued bytes
    do not all fit in the writable prefix answers [-EFAULT] or a
    whole-buffer count depending on how the writer's writes were merged
    into pipe buffers (fs/pipe.c [anon_pipe_read], same note), so a
    destination that cannot hold the [min] of the clamped count and the
    remaining stream is [unmodeled] there too, even though a short
    delivery is otherwise among its outcomes.
    No trace events: file contents are observed
    at exit only.  A zero-byte file read (at end-of-file, or
    [count = 0]) has the same effect shape as a zero-byte channel read
    ([Uaccess.delivered_writes]) and never inspects the destination — so a read
    at end-of-file into an unmapped buffer still returns 0 (mm/shmem.c
    [shmem_file_read_iter] copies nothing at or past [i_size], v6.18.46).

    Ordering: -EBADF / -EISDIR are decided before the destination, so
    [read] on a closed fd with an unmapped buffer is -EBADF, not -EFAULT
    ([vfs_read], fs/read_write.c at v6.18.46, tests [FMODE_READ] before
    [access_ok], and [access_ok] before the fd's content is consulted —
    the order every [access_okb] premise in theories/Common rests on).  A regular file
    also faces [rw_verify_area]'s position test there, which this arm
    does NOT model — [rw_pos_einvalb] is applied by [readv_imported]
    only.  This is a known gap: past [LLONG_MAX] the scalar arm answers
    0 where Linux answers -EINVAL.

    Nonexistent fd, or an fd not open for reading (stdout/stderr, a
    write-only file): -EBADF (checked before the buffer and before the
    [count = 0] shortcut, as Linux checks FMODE_READ first).  That
    stdout/stderr are not readable is an ASSUMPTION about the stdio the
    process was handed, not a fact about the fd number — Linux reads the
    direction off the description's [FMODE_*] bits.  [fd]
    arrives already truncated to 32 bits (see [Syscall.fd32]).

    The COUNT is judged as Linux judges it, not through
    [Uaccess.rw_bytes_max].  In
    order, decided after the fd checks Linux makes first
    (fs/read_write.c [vfs_read], v6.18.46):

    - [access_ok(buf, count)] on the count the call named:
      [State.access_okb], -EFAULT for any range whose exact end is past
      [State.TASK_SIZE] = 2^47, which includes every [count] that is
      negative as [ssize_t] (never -EINVAL; see the order argument at
      [Uaccess.rw_bytes_max]);
    - then the transfer: Linux clamps it at [MAX_RW_COUNT] before the
      read ([State.rw_count_clamp]), so what a file read delivers is the
      bytes at the offset truncated at end-of-file AND at the clamp, and
      a channel read delivers at most the clamped count.  Below the
      clamp — every count under 2^31 — the clamp is a no-op and the
      grow-by-doubling reader's 256 KiB call is an ordinary full
      transfer.

    EVERY ARM ASKS [access_ok] ON THE NAMED COUNT, and which arm asks
    it where is said once, at [Uaccess.modeled_rw_range].  The channel,
    file, directory, /dev/null and /dev/urandom arms ask it first and
    answer -EFAULT, so they need no gate of their own.  The SOCKET and
    PIPE arms put [Uaccess.modeled_rw_range] in front of it, the same
    one-sided gate the write arms carry: judged up to
    [Uaccess.rw_bytes_max], judged above it when the range is inside
    the address space, declined above it when it is not, where Linux
    answers -EFAULT.  Below that gate they ask [access_ok] on every
    path that answers.

    The fd's OFFSET carries no bound: a read at or past end-of-file
    delivers nothing whatever the offset, and [Fs.file_read] answers
    that directly.

    On a DIRECTORY fd there is no transfer to bound and so no count
    guard at all, but there is still an [access_ok] one:
    -EISDIR is decided without touching the destination, and a range
    past [State.TASK_SIZE] is -EFAULT ahead of it. *)
(** [rw_verify_area]'s position test (fs/read_write.c, v6.18.46):
    [(loff_t)(pos + count) < 0] is [-EINVAL] for a file whose operations
    lack [FOP_UNSIGNED_OFFSET].  [pos] is a non-negative [loff_t] here
    (every modeled offset is under [2^63]; [lseek_dest]) and [count] is
    at most [MAX_RW_COUNT] on the vectored path and at most
    [State.TASK_SIZE] on the scalar one (a larger one fails [access_ok]
    first), so the sum cannot wrap 64 bits and is negative exactly when
    it reaches [2^63].  REACHABLE:
    [lseek(fd, LLONG_MAX, SEEK_SET)] succeeds on tmpfs, whose
    [s_maxbytes] is [MAX_LFS_FILESIZE = LLONG_MAX] (mm/shmem.c
    [shmem_fill_super], include/linux/fs.h), and a nonempty read at that
    offset is this [-EINVAL], where an offset merely past end-of-file is
    0.  The scalar [read] reaches the same test with its UNCLAMPED count
    ([vfs_read] calls [rw_verify_area] before the [MAX_RW_COUNT]
    clamp); only the vectored arm applies this predicate. *)
Definition rw_pos_einvalb (off : word) (count : Z) : bool :=
  (2 ^ 63 - 1 <? bv_unsigned off + count)%Z.

(** A READ THAT REPORTS THE PEER'S ERROR, and consumes it.

    All of this is Linux v6.12.  include/net/sock.h [sock_error] reads
    the pending error with an [xchg], so the read that reports it is the
    only one that sees it.
    The read AFTER it returns 0, and precisely because
    net/ipv4/tcp.c [tcp_done] sets [sk_shutdown = SHUTDOWN_MASK] while
    tcp_recvmsg_locked tests [sk_shutdown & RCV_SHUTDOWN] IMMEDIATELY
    ABOVE the [sk_state == TCP_CLOSE] arm that answers -ENOTCONN.  Get
    that order wrong and the model says -ENOTCONN where Linux says 0.
    (SOCK_DONE plays no part here — the RST path never sets it.)  That
    is why the socket moves to [SkReset] — which reads exactly as a
    consumed [NFin] does, and is a separate constructor only because the
    two are different TCP states for a sender.  See [State.SockState].

    No byte moves, so the destination is never touched and the only
    thing left to decide about it is the range verdict [vfs_read] made
    before dispatching — hence [access_ok_zero].  Note that on the
    -EFAULT branch of that verdict the state is NOT advanced: the
    protocol is never reached, so the error stays pending, exactly as on
    Linux. *)
Definition socket_pending_error (e : Z) (fd : word) (peer : PeerAddr)
    (ch : word) (buf count : word) (i : SyscallInput) (m : Model)
    : Sys SyscallEffect :=
  access_ok_zero buf count
    (set_fds (fd_insert (m_fds m) fd (FdSocket (SkReset peer ch))) ;;
     err_ret e).

(** A READ OF /dev/urandom, shared by the [read] and [pread64] arms on
    [State.FdUrandom] once each has made the test Linux makes ahead of
    the device ([vfs_read]'s [access_ok], and for pread64
    [rw_verify_area]'s position test).  It answers exactly [count]
    bytes taken from the front of the run's DECLARED stream
    ([State.m_urandom], seeded from [State.in_urandom]) and advances the
    stream past them.  Nothing is chosen and nothing reaches the trace:
    the bytes are an input of the run, the same on both sides of an
    equivalence.

    WHY THE WHOLE COUNT, from drivers/char/random.c at v6.18.46:
    [urandom_read_iter] is [get_random_bytes_user] over the imported
    iterator, which returns 0 on an empty request and otherwise fills
    the request — the first 32 bytes straight from the key, the rest
    in 64-byte ChaCha blocks — stopping early only where
    [copy_to_iter] copies short.  It never waits: [urandom_read_iter]
    warns about an unseeded pool and reads anyway ([try_to_generate_
    entropy], then the read), so there is no -EINTR and no -EAGAIN on
    this device, unlike [random_read_iter]'s [wait_for_random_bytes]
    and unlike [getrandom]'s.  The one short answer Linux has here is
    the loop's [signal_pending] test at every page boundary
    ([ret % PAGE_SIZE == 0]), which stops a request past 4096 bytes at a
    page multiple when a signal is pending — a signal-interrupted
    transfer, and it is REJECTED rather than declined for the same
    reason as every other read arm: whether one was pending is not a function of
    the call's arguments, so no gate can be written, and this model
    admits no signal that is not the process's own.

    THE DESTINATION, in the order [get_random_bytes_user] decides it:
    a request none of whose bytes can land is -EFAULT ([copy_to_iter]
    copies nothing and [ret ? ret : -EFAULT] fires); one whose range is
    admitted but not wholly writable copies a prefix whose length is
    the copy routine's rounded progress, which this model does not
    describe — declined, as every read arm declines it.  Both are
    tested against [in_wmem], the writable map, exactly as the channel
    arm tests them.

    THE COUNT IS JUDGED AS LINUX JUDGES IT, through [State.rw_count_clamp]
    — the [MAX_RW_COUNT] clamp [vfs_read] applies before the read — and
    carries no ceiling of its own, as no read arm does:
    the count the device transfers is the clamped count, which is [count]
    itself below 2^31.  The unary numerals the checker builds are bounded
    by the DELIVERY rather than by the request: [stream_take_z] stops at
    the declared stream's end, and the whole-range [read_bytes_map] below
    is over the delivered length, which the stream-length test has just
    equated to the clamp — the channel arm's spelling, for the channel
    arm's reason.

    THE STREAM RUNNING OUT is a DECLINE, not a short read: a finite
    declared stream that ends before the request is met is an
    environment that stopped answering, and Linux's device never does
    ([get_random_bytes_user] loops until the iterator is empty).  So
    the arm answers only when the stream holds the whole clamped count,
    and [IEof] short of it is [unmodeled] — the program is asking for
    bytes the declaration did not supply.  Tested ahead of the
    whole-range writability, so that the numeral built for that test
    is the delivery's. *)
Definition read_urandom (buf count : word) (i : SyscallInput) (m : Model)
    : Sys SyscallEffect :=
  if w_is0 count then ret_only (Z_to_bv 64 0)
    (* [get_random_bytes_user]'s [if (unlikely(!iov_iter_count(iter))) return 0] *)
  else
  match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
  | None => err_ret EFAULT                       (* not one byte can land: [copy_to_iter]
                                                    copies nothing, -EFAULT *)
  | Some _ =>
      let r := stream_take_z (m_urandom m) (rw_count_clamp count) in
      if negb (Z.eqb (Z.of_nat (length (fst r))) (rw_count_clamp count))
      then unmodeled                             (* the declared stream ran out *)
      else
      match read_bytes_map (in_wmem i) buf (len_word (fst r)) with
      | None => unmodeled                        (* a partially writable destination: the
                                                    short count is the copy routine's *)
      | Some _ =>
          set_urandom (snd r) ;;
          pure (mkEffect (len_word (fst r)) [(buf, fst r)] [])
      end
  end.

(** [read] on a /proc/sys file opened O_RDONLY ([State.OProcFile]):
    from 0 to [count] bytes of the ENVIRONMENT's choice, or any errno.

    KERNEL PATH, read at v6.18.44:
      fs/read_write.c [ksys_read], [vfs_read]: read at v6.18.44; identical at v6.18.46.
      fs/proc/proc_sysctl.c [proc_sys_read], [proc_sys_call_handler],
        [sysctl_perm], [test_perm], [grab_header]: read at v6.18.44; identical at v6.18.46.

    [vfs_read] tests FMODE_READ (set: the open was O_RDONLY) and
    FMODE_CAN_READ (set: [proc_sys_file_operations] has a [.read_iter],
    and a /proc/sys DIRECTORY's table has [.read = generic_read_dir]),
    then [access_ok(buf, count)], whose -EFAULT is the one answer this
    arm decides by itself and decides FIRST, as every read arm here does.
    Past [rw_verify_area] and the [MAX_RW_COUNT] clamp, [proc_sys_read]
    is [proc_sys_call_handler(iocb, iter, 0)]: [grab_header]'s error for
    an unregistered table, -EPERM from [sysctl_perm], -EINVAL for a
    table without a handler, -ENOMEM, the BPF cgroup sysctl hook's
    verdict, then [table->proc_handler] itself, which may fill at most
    [count] bytes of a kernel buffer and set [count] to what it filled,
    and finally ONE [copy_to_iter] of those bytes, which answers -EFAULT
    when it copies short.  A directory under /proc/sys answers
    [generic_read_dir]'s -EISDIR instead.

    WHY EVERY ERRNO ([Syscall.errno_any]).  The handler is the sysctl
    table's own function, one per entry under /proc/sys, and the BPF
    hook runs whatever program is attached; neither has an errno set
    this model can enumerate.

    WHY THE BYTES ARE THE ENVIRONMENT'S.  The model holds no contents
    for a sysctl ([State.OpaqueFd]), so any [bs] of length at most
    [count] is admitted, and the next read is admitted afresh: nothing
    pins the second read to the rest of the first's text.  That is a
    PRECISION gap (SCOPE.md, "Known gaps in precision"), the shape
    [Drivers.Char.Random.getrandom_spec]'s bytes have.  The delivery is
    a file read's: no trace event, the copy-out ledger is
    [Uaccess.delivered_writes].

    THE COUNT GATE IS [Uaccess.modeled_rw_count], getrandom's, and for
    getrandom's reason: the bytes are chosen rather than read out of a
    list the model holds, so nothing else bounds the range the writable
    test below walks.  At or below [Uaccess.rw_bytes_max] the
    [MAX_RW_COUNT] clamp is the identity, so [count] is the clamped
    count.  A larger count is declined.

    THE DESTINATION.  A [copy_to_iter] that copies a prefix and then
    faults has written bytes this model cannot place, and answers
    -EFAULT; so the arm answers only where that cannot happen.  The
    whole [count] range writable: every delivery lands.  Not one byte
    writable: a nonempty delivery copies nothing and is -EFAULT (in
    [errno_any]), and an empty one is 0.  Anything between is declined,
    because whether the handler's output reaches the unwritable part is
    the environment's. *)
Definition read_proc_spec (buf count : word) : Sys SyscallEffect :=
  if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
    (* [vfs_read]'s [access_ok], before the handler runs *)
  else if negb (modeled_rw_count count) then unmodeled
    (* see above: the count gate *)
  else
  i <- input ;;
  match read_bytes_map (in_wmem i) buf count with
  | Some _ =>
      alt (e <- errno_any ;; err_ret e)
          (bs <- choose (fun bs : list byte =>
                           (Z.of_nat (length bs) <= bv_unsigned count)%Z) ;;
           pure (mkEffect (len_word bs) (delivered_writes buf bs) []))
  | None =>
      match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
      | None => alt (e <- errno_any ;; err_ret e) (ret_only (Z_to_bv 64 0))
          (* nothing can land: an empty delivery is 0, a nonempty one
             [copy_to_iter]'s -EFAULT *)
      | Some _ => unmodeled
          (* a partially writable destination: see above *)
      end
  end.

(** Neither this spec nor [write_spec] has an -EINTR outcome, so an
    interrupted transfer is REJECTED rather than declined. *)
Definition read_spec (fd buf count : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* fd not open: real -EBADF, not a modeling gap *)
  | Some (FdFileW _ _) => err_ret EBADF          (* fd open write-only: real -EBADF *)
  | Some (FdFileA _ _) => err_ret EBADF          (* and so is an append fd: O_APPEND rides on
                                                    O_WRONLY here, so FMODE_READ is clear *)
  | Some (FdChannel ch) =>
      if negb (w_is0 ch) then err_ret EBADF      (* channels 1/2 are write-only BY ASSUMPTION
                                                    (piped stdio), not by the fd number *)
      else
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_read]'s [access_ok(buf, count)] on the count the call
           NAMED, before the fd's content is consulted and before the
           clamp below: a range whose exact end is past [State.TASK_SIZE]
           is -EFAULT whatever stdin holds and however much of the
           range is mapped.  See [State.access_okb] *)
      else
      if w_is0 count then ret_only (Z_to_bv 64 0)
        (* count = 0: return 0, no EOF implied; the range verdict above
           is the whole of what Linux checks on it *)
      else
        match m_stdin m with
        | IEof => ret_only (Z_to_bv 64 0)      (* end of input: return 0, no byte moves.
                                                    Sticky: [IEof] has no successor *)
        | ICons _ _ =>
            match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
            | None => err_ret EFAULT                 (* not one byte of the destination is
                                                    writable-mapped: real -EFAULT, nothing
                                                    delivered and nothing consumed *)
            | Some _ =>
            match read_bytes_map (in_wmem i) buf
                    (len_word (fst (stream_take_z (m_stdin m) (rw_count_clamp count)))) with
            | None => unmodeled                      (* the destination holds the first byte
                                                    but not everything the stream could
                                                    supply to this count: the pipe's answer
                                                    turns on its buffer boundaries — fail
                                                    closed, see [readv_imported]'s note *)
            | Some _ =>
                (* deliver a nonempty prefix of the remaining input, at most
                   the CLAMPED count ([State.rw_count_clamp]: the kernel
                   caps the transfer at [MAX_RW_COUNT] before the read, so
                   no delivery may exceed the clamp even when [count]
                   does), landing in a writable prefix (a short read is
                   real); the stream advances past exactly those bytes *)
                bs <- choose (fun bs : list byte =>
                                (1 <= Z.of_nat (length bs))%Z
                                /\ (Z.of_nat (length bs) <= rw_count_clamp count)%Z
                                /\ fst (stream_take (m_stdin m) (length bs)) = bs
                                /\ read_bytes_map (in_wmem i) buf (len_word bs) <> None) ;;
                set_stdin (snd (stream_take (m_stdin m) (length bs))) ;;
                emit (map (ReadEv ch) bs) ;;     (* record each delivered byte in the trace *)
                pure (mkEffect (len_word bs) [(buf, bs)] [])
            end
            end
        end
  | Some (FdDevNull rd _) =>
      if negb rd then err_ret EBADF              (* opened O_WRONLY: [vfs_read]'s FMODE_READ test,
                                                    fs/read_write.c, before the device is reached *)
      else
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_read]'s [access_ok] on the count the call NAMED, ahead of
           [rw_verify_area] and the clamp, as on every kind *)
      else ret_only (Z_to_bv 64 0)
        (* [read_null] (drivers/char/mem.c, v6.18.46) is [return 0]: no
           byte lands, [f_pos] does not move, no ledger.  The
           [rw_verify_area] between the range test and the read cannot
           fire — [f_pos] is 0 on this kind and a count of 2^63 or more
           already failed [access_ok] *)
  | Some FdUrandom =>
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_read]'s [access_ok] on the count the call NAMED, ahead
           of the clamp and the device, as on every kind; FMODE_READ is
           set on every descriptor of this kind (the open admits
           O_RDONLY alone), so there is no -EBADF to decide first.
           [rw_verify_area]'s position test cannot fire: [f_pos] is 0
           on this kind ([noop_llseek] and [urandom_read_iter] never
           move it) and a count of 2^63 or more already failed
           [access_ok] *)
      else read_urandom buf count i m
        (* [urandom_read_iter] (drivers/char/random.c, v6.18.46): the
           whole count from the declared stream — see [read_urandom] *)
  | Some FdDir =>
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_read] runs [access_ok] before it dispatches to the
           directory's [.read], so a range past [State.TASK_SIZE] is
           -EFAULT ahead of the -EISDIR (fs/read_write.c [vfs_read],
           then fs/libfs.c [generic_read_dir], v6.18.46) *)
      else err_ret EISDIR                        (* read(2) on a directory fd: real -EISDIR,
                                                    resolved before any buffer access *)
  | Some (FdSocket sk) =>
      if negb (modeled_rw_range buf count) then unmodeled
        (* THE GATE COMES FIRST, and it is [Uaccess.modeled_rw_range] —
           [Uaccess.rw_bytes_max] OR Linux's own range test: at or below
           [Uaccess.rw_bytes_max] a read is judged, above it a read whose
           range is inside the user address space is JUDGED (with the
           transfer clamped below), and above it a read whose range
           leaves the address space is DECLINED where Linux answers
           -EFAULT.  That decline is about how much the model judges, and
           it stays.

           BELOW THE GATE EVERY PATH ASKS [vfs_read]'s [access_ok] ON THE
           NAMED COUNT (fs/read_write.c, [vfs_read]), and it is asked in
           two places rather than once, on purpose.  The five paths that
           move no byte — zero count, [NFin], [NRst] and [NTimedOut]
           through [socket_pending_error], [SkReset], never connected —
           ask it through [access_ok_zero], which is the same test.  The
           one that moves bytes, [NCons], asks it at its own head.  One
           test above the state dispatch would leave those five wrappers
           deciding nothing.

           [NCons] used not to ask it, on the argument that the test
           would make every socket read's judgement depend on a
           stack-layout fact the model does not carry.  That argument was
           false rather than outweighed: [State.access_okb] compares [buf]
           and [count] with the literal [State.TASK_SIZE] and reads no
           model state at all.  What the arm paid for it was a guard on
           every path but the one that moves bytes: a delivered read
           where Linux answers -EFAULT — [read(sock, TASK_SIZE - 4, 8)]
           with two bytes queued delivered them — and, at a destination
           straddling 2^64, a delivery into bytes the walk reached by
           wrapping ([State.copy_bytes_map]'s note has the wrap).
           Decided after the fd, as Linux does *)
      else
      if w_is0 count then
        access_ok_zero buf count (ret_only (Z_to_bv 64 0))
        (* ZERO LENGTH SHORT-CIRCUITS BEFORE THE PROTOCOL (v6.12).
           net/socket.c [sock_read_iter] opens with
           [if (!iov_iter_count(to)) return 0;], so [read(fd, buf, 0)] is
           0 on ANY socket — listening, fresh, or one whose peer has
           reset.  (recv(2) has no such short-circuit and answers
           -ENOTCONN instead; the model does not have recv.)  The range
           still faces [access_ok] in [vfs_read] — see [access_ok_zero] *)
      else
      match sk with
      | SkConnected peer ch rx =>
          match rx with
          | NFin =>
              access_ok_zero buf count (ret_only (Z_to_bv 64 0))
              (* the peer's FIN has been consumed in sequence: 0, no byte
                 moves, and STICKY — [NFin] has no successor.
                 net/ipv4/tcp_input.c [tcp_fin] sets RCV_SHUTDOWN and
                 SOCK_DONE, and tcp_recvmsg_locked tests SOCK_DONE BEFORE
                 sk_err, so END-OF-STREAM DOMINATES A LATER ERROR: once
                 EOF has been observed a subsequent RST cannot turn this
                 back into an error *)
          | NRst => socket_pending_error ECONNRESET fd peer ch buf count i m
          | NTimedOut => socket_pending_error ETIMEDOUT fd peer ch buf count i m
          | NCons _ _ =>
              if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
                (* [vfs_read]'s [access_ok] on the count the call NAMED,
                   before [sock_read_iter] (net/socket.c) is reached: a
                   range whose exact end is past [State.TASK_SIZE] is
                   -EFAULT with nothing delivered and nothing consumed,
                   however much of it the memory backs.

                   THIS IS THE GUARD ON THE WALKS BELOW — the one-byte
                   probe, the delivered-length walk and the [choose] side
                   condition that repeats it — which are the bare
                   [State.read_bytes_map] as on the channel and file arms.
                   The test is on [count]; each walk covers at most the
                   delivered prefix, whose length is at most
                   [State.rw_count_clamp count] and so at most [count].  So
                   [buf + len <= buf + count <= TASK_SIZE] and no walk can
                   pass the top of the user address space, let alone wrap.
                   [State.copy_bytes_map] here would be a guard that can
                   never fire *)
              else
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => err_ret EFAULT               (* not one byte of the destination is
                                                    writable-mapped: real -EFAULT, nothing
                                                    delivered and nothing consumed *)
              | Some _ =>
              match read_bytes_map (in_wmem i) buf
                      (len_word (fst (net_take_z rx (rw_count_clamp count)))) with
              | None => unmodeled                    (* first byte writable, but not every
                                                    queued byte this count could take: the
                                                    skb boundaries decide — fail closed.
                                                    [State.rw_count_clamp], not the raw count:
                                                    [vfs_read] (fs/read_write.c:566-567,
                                                    v6.18.46) caps the transfer at
                                                    [MAX_RW_COUNT] before it dispatches to
                                                    [sock_read_iter] (net/socket.c), so no
                                                    more than the clamp can be asked of the
                                                    destination *)
              | Some _ =>
                  (* Deliver a nonempty prefix of what the peer has left
                     to say, at most the CLAMPED count bytes, landing in
                     a writable prefix.  SHORT READS ARE REAL and the caller has no
                     control over the length.  ONE CALL DRAINS WHATEVER
                     IS QUEUED IN SEQUENCE, capped at the clamped count:
                     tcp_recvmsg_locked walks sk_receive_queue copying
                     [used = min(skb->len - offset, len)] per buffer,
                     and [target] (1 by default) governs only whether to
                     BLOCK for more, not when to stop copying.  So the
                     length is a function of the peer's segmentation and
                     timing, and any value in [1, count] is possible.
                     Queued bytes also PREEMPT a pending error, which
                     holds here by representation: the error is only ever
                     the head of the script, so every byte before it is
                     delivered first. *)
                  bs <- choose (fun bs : list byte =>
                                  (1 <= Z.of_nat (length bs))%Z
                                  /\ (Z.of_nat (length bs) <= rw_count_clamp count)%Z
                                  /\ fst (net_take rx (length bs)) = bs
                                  /\ read_bytes_map (in_wmem i) buf (len_word bs) <> None) ;;
                  set_fds (fd_insert (m_fds m) fd
                             (FdSocket (SkConnected peer ch
                                          (snd (net_take rx (length bs)))))) ;;
                  emit (map (ReadEv ch) bs) ;;     (* one event per delivered byte, on the
                                                    CONNECTION's channel — not stdin's *)
                  pure (mkEffect (len_word bs) [(buf, bs)] [])
              end
              end
          end
      | SkReset _ _ =>
          access_ok_zero buf count (ret_only (Z_to_bv 64 0))
          (* the peer's error has already been delivered once, and
             net/ipv4/tcp.c [tcp_done] set [sk_shutdown = SHUTDOWN_MASK];
             tcp_recvmsg_locked tests [sk_shutdown & RCV_SHUTDOWN]
             IMMEDIATELY ABOVE the TCP_CLOSE arm below, so the answer is
             0 and NOT the -ENOTCONN this socket's state would otherwise
             suggest *)
      | _ =>
          (* fresh, bound or listening: net/ipv4/tcp.c [tcp_recvmsg_locked]
             answers -ENOTCONN for a socket that never reached
             TCP_ESTABLISHED, decided without touching the destination —
             so the range verdict is all that is left *)
          access_ok_zero buf count (err_ret ENOTCONN)
      end
  | Some (FdFile p off) =>
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_read]'s [access_ok], exactly as on the channel arm.  [off]
           has no guard of its own here: a read at or past end-of-file
           delivers nothing, and [Fs.file_read] answers that without
           walking [off].  What that leaves out is [rw_verify_area]'s
           [(loff_t)(pos + count) < 0 -> -EINVAL] on a file whose
           [fop_flags] lack [FOP_UNSIGNED_OFFSET] (fs/read_write.c,
           v6.18.46), reachable through an [lseek] to an offset just
           under 2^63 *)
      else
      match fs_lookup (m_fs m) p with
      | None => unmodeled   (* an FdFile always points into the fs; see openat *)
      | Some data =>
          (* deterministic: bytes come from the file at [off], truncated
             at EOF and at the kernel's [MAX_RW_COUNT] clamp
             ([State.rw_count_clamp]; a no-op below 2^31).  DETERMINISTIC
             ON THE PREMISE THAT [p] NAMES A REGULAR FILE, which nothing
             establishes: for a path the kernel resolves to a character
             device this returns the recorded bytes where Linux returns
             end-of-file. *)
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count)) in
          match read_bytes_map (in_wmem i) buf (len_word bs) with
          | None =>
              (* the DELIVERED prefix is not fully writable-mapped, and it is
                 nonempty (a zero-length range always reads) *)
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => err_ret EFAULT               (* not even the first delivered byte can
                                                    land: real -EFAULT, offset unchanged *)
              | Some _ => unmodeled                  (* partially writable destination: the
                                                    count is the copy loop's rounded progress
                                                    — fail closed, see [readv_imported] *)
              end
          | Some _ =>
              let deliver :=
                set_fds (fd_insert (m_fds m) fd (FdFile p (off + len_word bs))) ;;  (* advance offset *)
                pure (mkEffect (len_word bs) (delivered_writes buf bs) []) in  (* no trace events for files *)
              deliver
                (* [bs] may be empty (count = 0, or at or past end-of-file):
                   the destination is then never touched, and the range
                   verdict above is all Linux checked on it *)
          end
      end
  | Some (FdFileRW p off) =>
      (* THE [FdFile] ARM ABOVE, WORD FOR WORD, with the entry written
         back under this kind.  An O_RDWR description reads exactly as a
         read-only one does: [vfs_read] tests FMODE_READ, which
         [ACC_MODE(O_RDWR)] supplies, and nothing below that test looks
         at the access mode again (fs/read_write.c, Linux v6.18.46).
         What the shared [f_pos] then means for the NEXT write is
         [write_spec]'s [FdFileRW] arm; here it is only advanced. *)
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_read]'s [access_ok], exactly as on the channel arm.  [off]
           has no guard of its own here: a read at or past end-of-file
           delivers nothing, and [Fs.file_read] answers that without
           walking [off].  What that leaves out is [rw_verify_area]'s
           [(loff_t)(pos + count) < 0 -> -EINVAL] on a file whose
           [fop_flags] lack [FOP_UNSIGNED_OFFSET] (fs/read_write.c,
           v6.18.46), reachable through an [lseek] to an offset just
           under 2^63 *)
      else
      match fs_lookup (m_fs m) p with
      | None => unmodeled   (* an FdFileRW always points into the fs; see openat *)
      | Some data =>
          (* deterministic: bytes come from the file at [off], truncated
             at EOF and at the kernel's [MAX_RW_COUNT] clamp
             ([State.rw_count_clamp]; a no-op below 2^31).  DETERMINISTIC
             ON THE PREMISE THAT [p] NAMES A REGULAR FILE, which nothing
             establishes: for a path the kernel resolves to a character
             device this returns the recorded bytes where Linux returns
             end-of-file. *)
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count)) in
          match read_bytes_map (in_wmem i) buf (len_word bs) with
          | None =>
              (* the DELIVERED prefix is not fully writable-mapped, and it is
                 nonempty (a zero-length range always reads) *)
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => err_ret EFAULT               (* not even the first delivered byte can
                                                    land: real -EFAULT, offset unchanged *)
              | Some _ => unmodeled                  (* partially writable destination: the
                                                    count is the copy loop's rounded progress
                                                    — fail closed, see [readv_imported] *)
              end
          | Some _ =>
              let deliver :=
                set_fds (fd_insert (m_fds m) fd (FdFileRW p (off + len_word bs))) ;;  (* advance offset *)
                pure (mkEffect (len_word bs) (delivered_writes buf bs) []) in  (* no trace events for files *)
              deliver
                (* [bs] may be empty (count = 0, or at or past end-of-file):
                   the destination is then never touched, and the range
                   verdict above is all Linux checked on it *)
          end
      end
  | Some (FdPipe id w) =>
      if w then err_ret EBADF                    (* the WRITE end is O_WRONLY: real -EBADF, decided
                                                    before the destination, as Linux checks
                                                    FMODE_READ first *)
      else
      if negb (modeled_rw_range buf count) then unmodeled
        (* THE SOCKET ARM'S GATE, read the same way: judged at or below
           [Uaccess.rw_bytes_max], judged above it when the range is
           inside the user address space, and declined above it when the
           range is not.  Below it every path that answers asks
           [vfs_read]'s [access_ok] on the NAMED count, in two places for
           the reason the socket arm's note gives: the zero-count and
           end-of-file paths, which move no byte, through
           [access_ok_zero]; the delivering path at its own head.  The
           delivering path used not to, at the cost that note names.  The
           would-block decline is reached before the test, which costs
           only how much the model judges.

           IT IS NOT THE TIGHTER [Uaccess.modeled_rw_count], which
           would decline an ordinary [read(pipefd, buf, 1 << 20)] outright.
           Nothing about a pipe needs that: a pipe read delivers
           at most the queue, which the one-slot rule already holds
           under [PIPE_BUF].  A delivery spelled
           [firstn (word_to_nat count) q] would build the
           count as a unary numeral before it looked at the queue;
           [State.pipe_take] takes the minimum against the queue first,
           so the numeral is bounded by the queue and the count is
           free. *)
      else
      if w_is0 count then
        access_ok_zero buf count (ret_only (Z_to_bv 64 0))
        (* "Null read succeeds": [anon_pipe_read] returns 0 for a
           zero-length request at fs/pipe.c:277-279, BEFORE the
           [mutex_lock] at :282, so it never consults the queue or the
           writers — a zero-length read of an empty pipe with a live
           writer does not block.  Only the [access_ok] on the range is
           left, exactly as on the other kinds *)
      else
      match pipe_lookup (m_pipes m) id with
      | None => unmodeled   (* an FdPipe always names a live table entry; see [Pipe.pipe2_spec] *)
      | Some ([], _) =>
          (* everything this arm asserts is fs/pipe.c [anon_pipe_read]
             (:269), the [read_iter] [pipeanon_fops] installs on both ends
             of an anonymous pipe (:1259); v6.18.46 throughout, and see
             [Pipe.pipe2_spec]'s header for why the FIFO pair is not the
             one to read *)
          if pipe_end_live (m_fds m) id true then unmodeled
            (* AN EMPTY PIPE WITH A LIVE WRITER HAS NO ANSWER HERE.
               [anon_pipe_read] falls past [if (!pipe->writers) break]
               (:370-371) to the [wait_event_interruptible_exclusive] at
               :388 and sleeps until a writer supplies bytes or the last
               writer closes; the model has no blocking and no O_NONBLOCK
               (which would make this -EAGAIN, :374-378), so it declines
               rather than invent one.  Fail closed *)
          else access_ok_zero buf count (ret_only (Z_to_bv 64 0))
            (* END OF FILE.  With no writer left, [anon_pipe_read]
               returns 0 without waiting — the [if (!pipe->writers) break]
               at :370-371, reached with [ret] still 0.  This is what makes
               [close] of the write end observable *)
      | Some ((b :: bs0) as q, used) =>
          (* deterministic: the head of the queue, truncated at the
             CLAMPED count ([State.rw_count_clamp]: [vfs_read],
             fs/read_write.c:566-567, v6.18.46, caps the transfer at
             [MAX_RW_COUNT] before it dispatches to [anon_pipe_read],
             fs/pipe.c).
             [anon_pipe_read] then walks the ring until it has that many
             bytes or runs out ([total_len -= chars] then [if
             (!total_len) break] and [if (!pipe_empty(head, tail))
             continue], :363-367), so the length is exactly [min count
             (length q)] — never short of it, and never interruptible
             once a byte has moved ([if (ret) break] at :372-373
             precedes the only wait, :388).  [State.pipe_take] is that
             [min], taken in [Z] so a large count costs nothing.
             No trace events: pipe bytes are internal to the process *)
          if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
            (* [vfs_read]'s [access_ok] on the count the call NAMED,
               before [anon_pipe_read] (fs/pipe.c) is reached: -EFAULT
               with the queue untouched, however much of the range the
               memory backs.  THIS IS THE GUARD ON THE TWO WALKS BELOW:
               the test is on [count], and each walk covers at most [del],
               whose length is at most [State.rw_count_clamp count] and so
               at most [count], so [buf + len <= buf + count <= TASK_SIZE]
               and neither walk can pass the top *)
          else
          let del := pipe_take q (rw_count_clamp count) in
          match read_bytes_map (in_wmem i) buf (len_word del) with
          | None =>
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => err_ret EFAULT           (* not even the first delivered byte can land:
                                                    real -EFAULT, and the queue is untouched *)
              | Some _ => unmodeled              (* partially writable destination: the pipe's
                                                    answer turns on its buffer boundaries and the
                                                    copy's rounded count — fail closed, see the
                                                    note above [readv_imported] *)
              end
          | Some _ =>
              set_pipes (pipe_insert (m_pipes m) id
                           (pipe_consume (q, used) (length del))) ;;
              pure (mkEffect (len_word del) (delivered_writes buf del) [])
              (* the queue keeps what the delivery did not take:
                 [State.pipe_consume_of_take] is that this is the same
                 queue [word_to_nat count] would have left *)
          end
      end
  | Some (FdOpaque (OProcFile _)) => read_proc_spec buf count
      (* a /proc/sys file opened O_RDONLY: see [read_proc_spec] *)
  | Some (FdOpaque (OProcPath _)) => unmodeled
      (* FAIL-CLOSED: [ksys_read]'s [CLASS(fd_pos, f)] refuses an O_PATH
         file (fs/read_write.c and fs/file.c, read at v6.18.44; identical at v6.18.46), which is
         -EBADF; not written *)
  | Some (FdOpaque (OEventFd _)) => unmodeled
      (* FAIL-CLOSED: [eventfd_read] (fs/eventfd.c, read at v6.18.44; identical at v6.18.46)
         answers from the counter, which the model does not hold *)
  | Some (FdOpaque (ONsFile _)) => unmodeled
      (* FAIL-CLOSED: the object behind the handle may be of any type,
         and a read's answer depends on it ([State.ONsFile]) *)
  end.

(** [write fd buf count].

    The source bytes available to the write are the READABLE PREFIX of
    the buffer, as Linux does: copy_from_user copies until the first
    unmapped byte.  Not even the first byte readable (and [count > 0]):
    -EFAULT, a real kernel error return, not a model hole.  [count = 0]
    writes nothing and returns 0 without touching [buf].

    Channel (stdout/stderr): the write delivers a NONEMPTY PREFIX of the
    readable prefix, of the environment's choosing — SHORT WRITES are
    real: a pipe with a nearly-full buffer, or a terminal, can accept
    fewer bytes than offered, and the program sees the short return.
    WHICH bytes move is determined by the buffer, only HOW MANY is
    nondeterministic (the mirror image of the channel read's short
    delivery).  One [WriteEv] per delivered byte; a full delivery of the
    whole readable prefix remains admissible.

    This OVER-APPROXIMATES, deliberately.  Linux does not fall short on
    every channel.  A blocking pipe write of at most PIPE_BUF (4096; the
    [PIPE_BUF] definition in include/uapi/linux/limits.h) is atomic.  The
    optional pre-loop merge either copies the whole write or errors: that
    is the [chars && !was_empty] branch of [anon_pipe_write] in
    fs/pipe.c.  If merging is unavailable, the ordinary loop of the same
    function either returns EPIPE or an allocation error before copying,
    encounters a copy fault without publishing the copied bytes, copies
    the whole request into one new pipe page when a slot exists, or
    reaches its signal and wait checks before copying anything.  Linux
    v6.18.46, commit 1f99e9ab748f.
    None of these paths can produce a short POSITIVE return, signal
    interruption included.

    A regular file is weaker, but still not the channel rule: a buffered
    write returns short only after a partial copy, and only on -EINTR
    from [fatal_signal_pending] (mm/filemap.c:4049) or on an error out
    of [write_begin]/[write_end] (:4056, :4071) — ENOSPC, EIO, ENOMEM,
    EDQUOT.  An ordinary catchable signal does not truncate it, and
    RLIMIT_FSIZE is not a short-return path at all: it clamps the count
    before the write, or returns -EFBIG (fs/read_write.c:1745-1750).

    The model cannot tell these cases apart — it classifies fds 1 and 2
    as [FdChannel] unconditionally, without knowing whether the far end
    is a pipe, a terminal, or a file — so it admits the short return
    everywhere.  This is a known soundness gap against the syscall-modeling
    priority: for a blocking pipe write of at most PIPE_BUF, the model admits
    a positive short return Linux cannot produce.  Giving BOTH binaries the
    same widened outcome set may make [equiv] coarser, but it does not make
    the claimed behavior faithful.

    A SECOND thing this arm cannot see is whether the channel still
    HAS a reader.  Linux kills the process there rather than answering
    a count, and this arm answers a success.

    File: fully deterministic — the whole readable prefix lands in the
    interpreted file system at the fd's offset (zero-filling any gap
    past end-of-file); the offset advances by the delivered length; no
    events.  (Short writes are a channel behavior: a regular-file write
    falls short only under the conditions listed above — a fatal signal,
    or ENOSPC/EIO/ENOMEM/EDQUOT out of the page-cache write — none of
    which the model has, so admitting them here would be a new rule with
    no kernel behavior behind it.  The ENOSPC half is a real short
    return that this arm therefore REJECTS.)

    Nonexistent fd, or an fd not open for writing (stdin, a read-only
    file): -EBADF (checked before the source buffer, as Linux checks
    FMODE_WRITE first).  That stdin is not writable is an ASSUMPTION
    about the stdio the process was handed, not a fact about the fd
    number.  [fd]
    arrives already truncated to 32 bits (see [Syscall.fd32]).

    THE COUNT IS NOT CAPPED AT [Uaccess.rw_bytes_max]:
    [State.readable_bytes] spends neither stack depth nor
    a length-sized unary numeral on the count a call names.  The gate,
    decided after the fd checks Linux makes first,
    is [Uaccess.modeled_rw_range]: at or below [Uaccess.rw_bytes_max] the gate
    admits the call, and above it the gate is Linux's own range test
    ([State.access_okb]), with an out-of-range write above the constant
    DECLINED rather than answered.  Below the gate every judging arm asks
    [vfs_write]'s own [access_ok] on the named count and answers -EFAULT;
    [Uaccess.modeled_rw_range] says which arm asks it where.

    The transfer itself is then the kernel's: Linux clamps it at
    [MAX_RW_COUNT] before the write ([State.rw_count_clamp]), so the
    source prefix a write may move is [Uaccess.write_source] — the
    readable prefix of the CLAMPED range — and the delivered length is
    bounded by it.  Below the clamp, which is every count under 2^31,
    the clamp is a no-op.

    A file write opening a hole larger than [Uaccess.rw_bytes_max] past
    end-of-file is still [unmodeled] — fail closed, and the one bound of
    the model's own left on this path.  That quantity is not the count:
    it is the distance from end-of-file to the write's offset, bytes the
    model has to BUILD because it holds a file as a flat byte list where
    Linux leaves a sparse hole.  It is explained at [modeled_file_gap]
    and at [Uaccess.rw_bytes_max]. *)
(** * The three write arms of a FILE, and what they share

    [write] on a regular file has three descriptor kinds in this model --
    O_WRONLY, O_RDWR and O_APPEND -- and Linux runs ONE [vfs_write] for
    all three.  The differences between them are exactly four, and every
    one of them is a kernel fact rather than a modelling convenience:

    - the LEADING KERNEL TESTS.  The append arm models [vfs_write]'s
      [access_ok] and [rw_verify_area]; the other two model [access_ok]
      and not [rw_verify_area], and rely on [modeled_file_gap] declining
      first for that one, which is a known divergence from Linux.
      That is a difference between the ARMS, not between the kernels, so
      it has to stay visible at each arm rather than move in here.
    - the GAP GUARD, which the append arm does not need and does not have
      ([append_opens_no_gap]).
    - the DESTINATION: [off] for the two positional kinds,
      [len_word data] for the append one.
    - the ENTRY WRITTEN BACK, which carries the kind.

    Everything else is common, and the three helpers below are that
    "everything else", named once so a fourth kind cannot arrive as a
    copy that drifts.  A change to one arm's count gate that missed the
    copy beside it would answer the same
    [write] on the same count two ways, by nothing but the fd.  Reading
    the shared shape out of a helper makes that particular drift
    unstateable.

    The channel and pipe arms do NOT go through these: they share the
    count gate and [vfs_write]'s [access_ok] and nothing else -- no file,
    no gap, no offset written back, and a ledger of their own -- so each
    spells the two tests in place. *)

(** THE COUNT GATE, and it is the FIRST thing every file write arm does.

    [Uaccess.modeled_rw_range] is the disjunction
    [modeled_rw_count count || access_okb buf count], so it is a gate on
    whether the MODEL will judge this call at all, not a kernel test.  It
    has to stay AHEAD of the arm's own kernel tests: its left disjunct is
    what admits a small count at an unaddressable buffer, and that is the
    call on which every file arm's [access_ok] then produces the real
    -EFAULT.  An arm that ran a kernel test first would be answering for
    a call the model had not yet agreed to judge. *)
Definition write_range_gate (buf count : word) (k : Sys SyscallEffect)
  : Sys SyscallEffect :=
  if negb (modeled_rw_range buf count) then unmodeled else k.

(** The ledger and the return, shared by all three file arms.

    A zero-length write reads no user byte, so its ledger is EMPTY rather
    than a singleton zero-length range; a delivering one records the
    prefix it actually read.  The return is the delivered length in both
    cases. *)
Definition write_ledger (buf count : word) (bs : list byte)
  : Sys SyscallEffect :=
  if w_is0 count
  then ret_only (len_word bs)
  else record_copyins [(buf, length bs)] (ret_only (len_word bs)).

(** The tail every file write arm shares: the source bytes, the -EFAULT
    on an unreadable buffer AND THE FILE THAT -EFAULT STILL EXTENDS, the
    zero-count range verdict, and the ledger.

    [place bs] is the KIND's own middle and [fault] is its other one.
    [place] answers [None] where that kind declines -- an fd whose path
    is not in the file system, or a hole the model would have to build
    -- and otherwise the state update, which is where the destination
    and the written-back entry live.  The update is handed the ledger as
    its CONTINUATION rather than building one: it cannot vary the
    ledger, the -EFAULT or the zero-count wrapper, because it is given
    the first already built and never sees the other two.

    A FAULTING SOURCE IS NOT A NO-OP ON THE FILE, and [fault] is why
    this is not simply [err_ret EFAULT].  [generic_perform_write]
    (mm/filemap.c) calls [a_ops->write_begin] BEFORE the copy, copies
    with [copy_folio_from_iter_atomic] -- which moves 0 bytes when no
    byte of the buffer is there -- and then calls
    [a_ops->write_end(iocb, mapping, pos, bytes, copied, folio, fsdata)]
    with [copied = 0] anyway.  [shmem_write_end] (mm/shmem.c) opens with
    [if (pos + copied > inode->i_size) i_size_write(inode, pos + copied);],
    so the file comes out extended to [pos] exactly; the loop then takes
    [status == 0], finds [fault_in_iov_iter_readable] unable to fault
    the range in, sets [status = -EFAULT] and breaks, and
    [if (!written) return status;] returns it.  So Linux answers -EFAULT
    AND leaves the file longer, and [fault] carries the kind's own
    version of that: [None] where the hole it opens is one the model
    will not build ([modeled_zero_fill]), and otherwise
    [Fs.file_extend].  [f_pos] does not move -- [new_sync_write]
    (fs/read_write.c) writes a position back only under [if (ret > 0 &&
    ppos)] -- so no [fault] update writes the descriptor back.  Linux
    v6.18.46 throughout.

    [Uaccess.write_source] is the readable prefix of the CLAMPED range:
    Linux clamps at [MAX_RW_COUNT] before the write, so a delivering
    write moves at most that much and the model's answer is exact below
    it.  The -EFAULT is guarded by [negb (w_is0 count)] because a
    zero-length write touches no byte and so cannot fault on the buffer;
    what remains for it is the RANGE verdict, which is
    [Uaccess.access_ok_zero].  A zero-length write extends nothing
    either: [generic_write_checks] returns at
    [if (!iov_iter_count(from)) return 0;] before [write_begin] is
    reached at all.

    Every arm that reaches this tail has asked [vfs_write]'s [access_ok]
    on the named count first, so the walk [Uaccess.write_source] makes
    never leaves the user address space: it covers at most
    [State.rw_count_clamp count] bytes, which is at most [count], and
    [buf + count <= State.TASK_SIZE].

    THE [access_ok_zero] IN THE BODY THEREFORE DECIDES NOTHING, AND IT IS
    KEPT.
    The helper has three callers, [write_spec]'s [FdFileW], [FdFileRW]
    and [FdFileA] arms, and each asks [access_okb buf (bv_unsigned count)]
    under [write_range_gate] before it calls the helper.  [access_ok_zero]
    is that same test, so on every caller it passes.  For [FdFileA] this
    was already true before the other two arms asked.  [pwrite64] and
    [writev] are not callers: they share [write_fault_extend] and not
    this tail.  The test stays as the helper's own guarantee, so a
    future caller that does not ask first still gets Linux's answer on a
    zero-length write. *)
Definition write_file_tail (mp : word -> option byte) (buf count : word)
    (fault : option (Sys SyscallEffect -> Sys SyscallEffect))
    (place : list byte -> option (Sys SyscallEffect -> Sys SyscallEffect))
  : Sys SyscallEffect :=
  let bs := write_source mp buf count in
  if negb (w_is0 count) && Nat.eqb (length bs) 0
  then
    match fault with
    | None => unmodeled
    | Some upd => upd (err_ret EFAULT)
    end
  else
    let deliver :=
      match place bs with
      | None => unmodeled
      | Some upd => upd (write_ledger buf count bs)
      end in
    if w_is0 count then access_ok_zero buf count deliver else deliver.

(** WHAT A WRITE TO A FAR END WITH NO READER DOES TO THE PROCESS.

    Linux sends SIGPIPE and sets the syscall's return to -EPIPE, in that
    order and unconditionally: fs/pipe.c [anon_pipe_write] does
    [send_sig(SIGPIPE, current, 0); ret = -EPIPE;] at :460-465 and again
    at :501-506, and net/core/stream.c [sk_stream_error] does
    [if (err == -EPIPE && !(flags & MSG_NOSIGNAL)) send_sig(SIGPIPE, current, 0);]
    at :190-198.  Neither raises a signal write(2) can suppress:
    [IOCB_NOSIGNAL] is not among the flags [iocb_flags]
    (include/linux/fs.h) sets, and MSG_NOSIGNAL reaches
    net/socket.c [sock_write_iter] only from it (:1193-1194).  Linux
    v6.18.46, commit 1f99e9ab748f.

    WHICH OF THE TWO THE PROCESS SEES IS THE MASK'S DECISION, and that
    is the whole of this function.  SIGPIPE's default action is
    TERMINATE ([Uapi.SIGPIPE] says why), so with the signal unblocked
    kernel/signal.c [get_signal] runs on the way back to user space and
    reaches [do_group_exit]: the -EPIPE is never returned, and what the
    world sees is a death by signal 13.  With the signal BLOCKED,
    [send_signal_locked] leaves it in [task->pending.signal],
    [recalc_sigpending] leaves TIF_SIGPENDING clear, the return to user
    space takes no signal, and the program reads -EPIPE -- which is why
    the errno is this function's answer on BOTH branches, and why the
    pending bit has to be recorded: an [rt_sigprocmask] that later
    uncovers signal 13 kills there
    ([Kernel.Signal.sigmask_deliver_model]).

    THE DISPOSITION IS A LAUNCH DECLARATION, and it is the FIRST test
    here.  Nothing inside the modeled surface can change it --
    [Kernel.Signal.rt_sigaction_spec] declines every install for signal
    13 -- but the launcher can: `signal(SIGPIPE, SIG_IGN)` before
    execve survives it, because fs/exec.c [begin_new_exec] calls
    kernel/signal.c [flush_signal_handlers] with [force_default = 0],
    which resets handlers and leaves SIG_DFL and SIG_IGN alone (Linux
    v6.18.46, commit 1f99e9ab748f).  [State.in_sigpipe_default] is that
    declaration and [State.m_sigpipe_default] reads it.  WITH SIG_IGN
    THE PROCESS NEVER DIES, by either of two kernel routes, and the
    model collapses both into leaving the state alone.  UNBLOCKED:
    kernel/signal.c [prepare_signal] returns [!sig_ignored(p, sig,
    force)], [sig_ignored] falls through to [sig_task_ignored], and
    the signal is dropped before [__send_signal_locked] queues
    anything.  BLOCKED: [sig_ignored] answers false for a blocked
    signal on purpose ("the signal handler may change by the time it
    is unblocked"), so it IS queued -- but the [rt_sigprocmask] that
    later uncovers it reaches [get_signal]'s
    [if (ka->sa.sa_handler == SIG_IGN) continue], which discards it
    there instead.  Either way no state this model carries differs
    afterwards: the only thing that could tell the two apart is
    [sigpending], which this model has no call for.  So the branch
    answers -EPIPE over an UNCHANGED model, which is what every
    program that ignores SIGPIPE is written to read, and nothing is
    recorded as pending -- [Kernel.Signal.sigmask_deliver_model] stays
    out of it.  [Run.valid_input] pins the declaration to SIG_DFL;
    [Run.valid_input_sigpipe_ignored] is the other world.

    NO LEDGER AND NO EVENT.  Both kernel sites raise the signal before
    any byte is copied out of user memory, so the call reads nothing
    and emits nothing; [State.with_killed] and
    [State.with_sigpipe_pending] rebuild [State.ProcState] alone, so the
    file system, the fd table and the address space are untouched.  When
    the branch kills, [Run.sstep_killed] discards the effect this
    returns -- exactly as [Run.sstep_exit] discards an [exit]'s -- so
    the -EPIPE is unobservable there, which is the point. *)
Definition raise_sigpipe (m : Model) : Model :=
  if negb (m_sigpipe_default m)
  then m                         (* SIG_IGN: discarded, never queued *)
  else if sigpipe_blocked (m_sigmask m)
  then with_sigpipe_pending m
  else with_killed (Z_to_bv 64 SIGPIPE) m.

Definition sigpipe_write : Sys SyscallEffect :=
  modify raise_sigpipe ;;
  err_ret EPIPE.
(** The faulting-source post-state of a write whose bytes would have
    landed at [off] in [p]: the file extended to [off], the descriptor
    untouched, or [None] where the hole is one the model will not build.

    The POSITIONAL arms pass this -- [write]'s two, [writev]'s two and
    [pwrite64]'s shared one -- so the kernel statement [write_file_tail]
    cites is written once.  The APPEND arms pass [write_fault_keep]
    below instead, and the difference is the kernel's arithmetic rather
    than a second rule. *)
Definition write_fault_extend (fs : Fs) (p : path) (off : word)
    : option (Sys SyscallEffect -> Sys SyscallEffect) :=
  match fs_lookup fs p with
  | None => None                 (* a file fd always points into the fs; see openat *)
  | Some data =>
      if negb (modeled_zero_fill (bv_unsigned off) data) then None
        (* the same hole [modeled_file_gap] bounds for a DELIVERING
           write, measured at the same offset: the model holds a file as
           a flat byte list and would have to build those zeros *)
      else Some (fun k => set_fs (fs_set fs p (file_extend data off)) ;; k)
  end.

(** An APPEND write's faulting source leaves the file alone, and that
    is [shmem_write_end]'s own test rather than an omission: the
    position an append write uses IS [i_size]
    ([generic_write_checks]'s [iocb->ki_pos = i_size_read(inode)]), so
    [pos + copied > inode->i_size] is false at [copied = 0] and no new
    size is written.  [file_extend_at_eof] is that statement in the
    model's terms -- extending a file to its own length is the identity
    -- so this is [write_fault_extend] at the append position with the
    [fs_set] it would perform proved away. *)
Definition write_fault_keep : Sys SyscallEffect -> Sys SyscallEffect :=
  fun k => k.

Remark file_extend_at_eof : forall data,
  (word_to_nat (len_word data) <= length data)%nat ->
  file_extend data (len_word data) = data.
Proof. intros data H. apply file_extend_within, H. Qed.

Definition write_spec (fd buf count : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* fd not open: real -EBADF, not a modeling gap *)
  | Some (FdFile _ _) => err_ret EBADF           (* fd open read-only: real -EBADF *)
  | Some FdUrandom => err_ret EBADF             (* every descriptor of this kind is O_RDONLY —
                                                    the open declines the write words — so
                                                    [vfs_write]'s FMODE_WRITE test (fs/read_write.c,
                                                    v6.18.46) answers before the buffer is looked at.
                                                    Linux's own [random_write_iter] is reachable only
                                                    through a descriptor this model never mints *)
  | Some (FdDevNull _ wr) =>
      if negb wr then err_ret EBADF              (* opened O_RDONLY: [vfs_write]'s FMODE_WRITE test,
                                                    fs/read_write.c, before the buffer *)
      else
      write_range_gate buf count
        (* the count rule every judging write arm applies
           ([Uaccess.modeled_rw_range]); it decides nothing here that
           the range test below does not, and is kept so that the arms
           of this spec agree on one rule *)
        (access_ok_zero buf count
           (ret_only (Z_to_bv 64 (rw_count_clamp count))))
        (* [vfs_write]'s [access_ok] over the WHOLE named range — the
           one test Linux makes on the buffer — then [write_null]
           (drivers/char/mem.c, v6.18.46) returns the count [vfs_write]
           clamped at [MAX_RW_COUNT] without reading a byte.  NOT the
           file arms' shape: no readable prefix is taken, so an unmapped
           in-range buffer is a full count here where a file would be
           -EFAULT, and NO copy-in is recorded, because none happens.
           [access_ok_zero] is that range test by another name; it is
           not only for a zero count *)
  | Some (FdChannel ch) =>
      if w_is0 ch then err_ret EBADF             (* channel 0 is read-only BY ASSUMPTION (piped
                                                    stdio), not by the fd number;
                                                    ordered before the buffer, as Linux checks
                                                    FMODE_WRITE first *)
      else
      if negb (modeled_rw_range buf count) then unmodeled
        (* a write above [Uaccess.rw_bytes_max] whose range leaves the
           user address space: fail closed, after the fd checks Linux
           makes first — see [Uaccess.modeled_rw_range] *)
      else
      if w_is0 count
      then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
             (* [count = 0] moves no byte and so never touches [buf],
                which leaves only the range verdict — see
                [Uaccess.access_ok_zero] *)
      else
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_write]'s [access_ok] on the count the call NAMED
           (fs/read_write.c, [vfs_write]), after the gate and before the
           source is read.  Without it a write whose named range
           [access_ok] refuses was judged by its readable prefix — a short
           write where Linux answers -EFAULT — and at a buffer straddling
           2^64 by bytes the walk reached by wrapping
           ([State.readable_bytes] steps [a + 1] in the word;
           [State.copy_bytes_map]'s note has the wrap).  THIS IS THE GUARD
           ON [Uaccess.write_source] BELOW: it walks at most
           [State.rw_count_clamp count] bytes, at most [count], so
           [buf + len <= buf + count <= TASK_SIZE].
           IT IS ALSO THE TEST THE NO-READER ARM BELOW NEEDS, which is
           why that arm no longer carries one of its own *)
      else
      if negb (m_channel_reader m) then
        (* THE FAR END HAS NO READER.  [State.in_channel_reader] says
           the launch put a pipe or a socket on the other side of this
           descriptor and its reader has gone -- `prog | head -1` once
           `head` has had its line.  Linux raises SIGPIPE and sets
           -EPIPE (fs/pipe.c [anon_pipe_write] :460-465 when the far
           end is a pipe, net/core/stream.c [sk_stream_error] :190-198
           when it is a socket), and under the default disposition the
           process DIES; see [raise_sigpipe], which is where the mask
           decides between the death and the errno.

           AFTER THE ZERO-COUNT BRANCH, because fs/pipe.c returns 0 for
           a zero-length write at :454-456, BEFORE the [mutex_lock] at
           :458 and therefore before the [if (!pipe->readers)] test at
           :460: a zero-length write to a pipe whose reader is gone is
           0, not -EPIPE, and raises no signal.

           AND BEHIND [access_ok], which is the order fs/read_write.c
           fixes: [vfs_write] runs
           [if (unlikely(!access_ok(buf, count))) return -EFAULT;]
           before it calls [f_op->write_iter], so a buffer whose NAMED
           range leaves the user address space is -EFAULT whatever is
           on the other end of the descriptor, and only a call that
           gets past it reaches the readers test.  That test is now the
           arm's own, immediately above, rather than a second copy
           here: the reader-present path below faces it too, which is
           the one thing that changed under this arm since this note
           was written -- that path no longer takes a readable prefix
           on a range [access_ok] refuses, so the looseness this note
           refused to inherit is gone rather than avoided.
           Linux v6.18.46, commit 1f99e9ab748f *)
        sigpipe_write
      else
      let bs := write_source (in_mem i) buf count in
      if Nat.eqb (length bs) 0
      then err_ret EFAULT                        (* nothing readable at [buf]: real -EFAULT *)
      else
        (* deliver a nonempty prefix of the readable prefix (a short
           write is real); which bytes is fixed by the buffer, only how
           many is the environment's choice *)
        ds <- choose (fun ds : list byte =>
                        (1 <= Z.of_nat (length ds))%Z
                        /\ (Z.of_nat (length ds) <= rw_count_clamp count)%Z
                        /\ ds = firstn (length ds) bs) ;;
        emit (map (WriteEv ch) ds) ;;            (* record each delivered byte *)
        record_copyins [(buf, length ds)]
          (ret_only (len_word ds))               (* the (possibly short) delivered length *)
  | Some FdDir => err_ret EBADF                  (* directory fds are O_RDONLY: write is real -EBADF,
                                                    checked before the source buffer as Linux does *)
  | Some (FdSocket sk) =>
      if negb (sock_send_dead sk) then unmodeled
        (* A DELIVERING SOCKET WRITE IS STILL UNMODELED, and this is
           what is left of the arm that used to decline every socket.
           [State.sock_send_dead] is false only for [SkConnected],
           where the send either goes out -- a short count chosen from
           the gatherable bytes, which is [Net.Socket.send_bytes]'s
           business and needs that file's machinery -- or reports a
           pending peer error ONCE and REWRITES the descriptor
           (include/net/sock.h [sock_error] consumes it with an
           [xchg]).  Neither raises a signal: [sk_stream_error] replaces
           the errno with [sock_error]'s before it tests for -EPIPE
           (net/core/stream.c :192-195), so a reset connection's FIRST
           write is -ECONNRESET and carries none.  What keeps those
           states out is the transfer, not the signal, which is why this
           decline is now bounded and not permanent *)
      else
      if negb (modeled_rw_range buf count) then unmodeled
        (* the count rule every judging arm of this spec applies, after
           the fd check Linux makes first -- see
           [Uaccess.modeled_rw_range] *)
      else
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_write]'s [access_ok] over the NAMED range, which
           fs/read_write.c runs before [f_op->write_iter] and therefore
           before anything the socket decides *)
      else sigpipe_write
      (* THE SOCKET HAS NO CONNECTION TO SEND ON, which is every state
         but [SkConnected]: TCP has no -ENOTCONN on the send path at
         all.  net/core/stream.c [sk_stream_wait_connect] (:60-88)
         answers -EPIPE for every state outside SYN_SENT and SYN_RECV,
         and net/ipv4/tcp.c [tcp_sendmsg_locked] reaches it whenever the
         state is outside [TCPF_ESTABLISHED | TCPF_CLOSE_WAIT].  That
         -EPIPE then goes through [sk_stream_error] (:190-198), whose
         [if (err == -EPIPE && !(flags & MSG_NOSIGNAL)) send_sig(SIGPIPE, ...)]
         fires because write(2) cannot set MSG_NOSIGNAL: the flag
         reaches net/socket.c [sock_write_iter] only from
         [IOCB_NOSIGNAL] (:1193-1194), and include/linux/fs.h
         [iocb_flags] ORs only IOCB_APPEND, IOCB_DIRECT, IOCB_DSYNC and
         IOCB_SYNC -- RWF_NOSIGNAL reaches a kiocb through
         [kiocb_set_rw_flags], which no write(2) or writev(2) path
         calls.  So the process takes SIGPIPE and, at the default
         disposition, DIES; [raise_sigpipe] is where the mask decides
         between that death and the -EPIPE.  SIGPIPE is in none of
         SIG_KERNEL_IGNORE_MASK, SIG_KERNEL_STOP_MASK or
         SIG_KERNEL_COREDUMP_MASK (include/linux/signal.h), so under
         SIG_DFL kernel/signal.c [get_signal] reaches [do_group_exit]
         and the whole thread group dies.  Linux v6.18.46, commit
         1f99e9ab748f.

         A ZERO-LENGTH WRITE IS NOT AN ESCAPE, which is why no
         zero-count branch precedes this: [sock_write_iter] has no
         zero-count short-circuit of the kind [sock_read_iter] has, so
         [write(sockfd, buf, 0)] on a socket with no connection reaches
         [tcp_sendmsg_locked] and takes the same -EPIPE and the same
         signal.  That is the one place this arm differs in SHAPE from
         the pipe and channel arms, and the difference is Linux's.

         WHAT THIS REPLACED.  The arm used to decline every socket
         write permanently, on the argument that a spec's outcomes are
         [Ok] and [Unmodeled] only ([Monad.Sys]), so "the process died"
         could not be stated and answering -EPIPE would assert the
         process SURVIVED -- a confidently wrong answer of exactly the
         class [Equivalence.modeled] cannot see.  The model now has a
         death that is not [exit] ([State.with_killed],
         [Run.sstep_killed]), so the argument no longer holds and the
         answer is the kernel's.  The sendto/sendmsg path keeps its own
         MSG_NOSIGNAL gate, where the flag is an argument a spec can
         read ([Net.Socket.send_flags_modeled]) *)
  | Some (FdFileW p off) =>
      (* ONE LEADING KERNEL TEST, [vfs_write]'s [access_ok], and not the
         second.  This note used to say the arm models neither
         [vfs_write]'s [access_ok] nor [rw_verify_area]; the [access_ok]
         half of that is withdrawn.  Without it a write whose named range
         [access_ok] refuses was judged by its readable prefix — a short
         or full write where Linux answers -EFAULT, and at a buffer
         straddling 2^64 a write of bytes the walk reached by wrapping
         ([State.copy_bytes_map]'s note has the wrap).

         TAKING [access_ok] WITHOUT [rw_verify_area] CANNOT INVERT THEIR
         ORDER.  [vfs_write] (fs/read_write.c) runs [access_ok] FIRST and
         [rw_verify_area] second; the inversion the append arm's note
         warns of — -EINVAL where Linux answers -EFAULT — needs the later
         test without the earlier one, and this arm has the earlier one
         without the later.  [rw_verify_area] is still not modeled here,
         and the arm rests on [modeled_file_gap] below declining first for
         it: a known divergence from Linux where that test would fire.
         The append arm below models both, for the reason it gives
         there. *)
      write_range_gate buf count
        (if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
         else
         write_file_tail (in_mem i) buf count
           (write_fault_extend (m_fs m) p off)
             (* a source that faults still extends the file to [off]:
                see [write_file_tail] *)
           (fun bs =>
           match fs_lookup (m_fs m) p with
           | None => None                        (* an FdFileW always points into the fs; see openat *)
           | Some data =>
               if negb (modeled_file_gap data off bs) then None
                 (* a hole past end-of-file too large to zero-fill as a byte
                    list; Linux makes the file sparse for free — see
                    [modeled_file_gap]; the tail's -EFAULT measures the
                    same hole at the same offset *)
               else
               Some (fun k =>
                 set_fs (fs_set (m_fs m) p (file_write data off bs)) ;;
                   (* the prefix lands AT [off] *)
                 set_fds (fd_insert (m_fds m) fd
                            (FdFileW p (off + len_word bs))) ;;      (* advance *)
                 k)
           end))
  | Some (FdFileRW p off) =>
      (* THE [FdFileW] ARM ABOVE with the entry written back under this
         kind, and it is the SAME two helpers rather than a copy of that
         arm's body: an O_RDWR description writes exactly as an O_WRONLY
         one does, so a difference between the two could only ever be a
         drift.  The bytes land AT [f_pos], because nothing sets
         IOCB_APPEND ([iocb_flags], include/linux/fs.h) and so
         [generic_write_checks] (mm/filemap.c) leaves [ki_pos] alone --
         the one thing that separates this from the [FdFileA] arm below.
         The offset it advances is the SAME one [read_spec]'s [FdFileRW]
         arm advances, which is the whole content of the kind.  Linux
         v6.18.46.

         IT INHERITS THE O_WRONLY ARM'S KERNEL TESTS TOO: [access_ok]
         and not [rw_verify_area], resting on [modeled_file_gap]
         declining first for the second, with the same known
         divergence. *)
      write_range_gate buf count
        (if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
         else
         write_file_tail (in_mem i) buf count
           (write_fault_extend (m_fs m) p off) (fun bs =>
           match fs_lookup (m_fs m) p with
           | None => None                        (* an FdFileRW always points into the fs; see openat *)
           | Some data =>
               if negb (modeled_file_gap data off bs) then None
               else
               Some (fun k =>
                 set_fs (fs_set (m_fs m) p (file_write data off bs)) ;;
                 set_fds (fd_insert (m_fds m) fd
                            (FdFileRW p (off + len_word bs))) ;;
                 k)
           end))
  | Some (FdFileA p off) =>
      (* THE OFFSET IS NOT READ, and that is the whole of what separates
         this arm's middle from the two above.  [iocb_flags]
         (include/linux/fs.h) turns the fd's O_APPEND into IOCB_APPEND,
         and [generic_write_checks] (mm/filemap.c) then assigns
         [iocb->ki_pos = i_size_read(inode)], discarding the position
         [ksys_write] had loaded from [f_pos] (Linux v6.18.46).  So the
         bytes land at the CURRENT end of the file however far an
         [lseek] moved [f_pos], and [f_pos] is left at the new end.
         Everything else -- the count gate, the -EFAULT on an
         unreadable buffer, the zero-count range verdict, the ledger --
         is [write_range_gate] and [write_file_tail], the same two the
         arms above call.

         NO [modeled_file_gap] GUARD, and that is not an omission: the
         position IS the current length, so the hole this write opens is
         empty ([append_opens_no_gap] below proves the guard would be
         [true] at every call).  It is the one thing an append write
         cannot ask the model to build.

         DROPPING THAT GUARD IS WHY [rw_pos_einvalb] IS HERE, and the
         leading kernel tests below are the one place this arm is not
         the [FdFileW] arm above with the position moved.
         [rw_verify_area] (fs/read_write.c) is handed [&file->f_pos] by
         [vfs_write] and runs BEFORE the iterator, so its
         [(loff_t)(pos + count) < 0] test reads the fd's REAL position
         even on an append fd — [generic_write_checks] (mm/filemap.c)
         overrides [ki_pos] only once the write is under way.  The
         [FdFileW] and [FdFileRW] arms do not model that test, and
         rest on the argument that [modeled_file_gap] declines
         first, so no run reaches it.  THIS arm has no
         [modeled_file_gap], so nothing would decline first: an
         [lseek(fd, LLONG_MAX, SEEK_SET)] followed by a one-byte write
         would be answered as an append where Linux answers -EINVAL,
         which is a wrong modeled answer rather than a gap.  The
         [writev] arm below keeps the same test for the same reason and
         says so at greater length.

         AND THE [access_ok] THAT PRECEDES IT, which is not optional once
         the position test is modeled.  [vfs_write] runs
         [if (unlikely(!access_ok(buf, count))) return -EFAULT;] BEFORE
         it calls [rw_verify_area], so a buffer whose named range passes
         [State.TASK_SIZE] is -EFAULT whatever the position is.  An arm
         that answered the LATER test without the EARLIER one would
         invert their order and report -EINVAL where Linux reports
         -EFAULT — the [pwrite64] and [pread64] arms below encode the
         same pair in the same order for the same reason.

         BOTH SIT INSIDE [write_range_gate] AND NOT BEFORE IT.
         [Uaccess.modeled_rw_range] is the DISJUNCTION
         [modeled_rw_count count || access_okb buf count], so it passes
         on a small count at an unaddressable buffer — where [access_okb]
         is false and Linux answers -EFAULT.  The gate decides whether
         the model judges this call at all; the tests below are
         [vfs_write]'s own, and produce a real errno on a path the gate
         has already admitted.  Reversing the two would run a kernel test
         for a call the model had not agreed to judge, and dropping the
         [access_ok] would answer that call as a delivering append — a
         wrong modeled answer rather than a gap.

         This is where the append arm stops matching the [FdFileW] one
         in a second place: that arm models [access_ok] and not
         [rw_verify_area], resting on [modeled_file_gap] for the second,
         which is a known divergence.  Modelling [rw_verify_area] here
         without [access_ok] would have been the worst of the three, so
         the arm takes both.  Linux v6.18.46. *)
      write_range_gate buf count
        (if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
         else if rw_pos_einvalb off (bv_unsigned count) then err_ret EINVAL
         else
         write_file_tail (in_mem i) buf count (Some write_fault_keep)
           (* a faulting source leaves an APPEND write's file alone:
              see [write_fault_keep] *)
           (fun bs =>
           match fs_lookup (m_fs m) p with
           | None => None                        (* an FdFileA always points into the fs; see openat *)
           | Some data =>
               Some (fun k =>
                 set_fs (fs_set (m_fs m) p
                           (file_write data (len_word data) bs)) ;;   (* at end-of-file *)
                 set_fds (fd_insert (m_fds m) fd
                            (FdFileA p (append_new_pos data bs off))) ;;
                   (* [f_pos] follows a DELIVERING write to the new end of
                      file, and a zero-length one not at all — see
                      [append_new_pos], which is where that asymmetry is
                      argued *)
                 k)
           end))
  | Some (FdPipe id w) =>
      if negb w then err_ret EBADF               (* the READ end is O_RDONLY: real -EBADF, decided
                                                    before the source buffer, as Linux checks
                                                    FMODE_WRITE first *)
      else
      if negb (modeled_rw_range buf count) then unmodeled
        (* see [Uaccess.modeled_rw_range], as on the channel arm *)
      else
      if w_is0 count
      then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
        (* "Null write succeeds": [anon_pipe_write] returns 0 for a
           zero-length request at fs/pipe.c:454-456, BEFORE the
           [mutex_lock] at :458 and therefore before the
           [if (!pipe->readers)] test at :460, so a zero-length write to a
           pipe whose reader is gone is 0 — NOT -EPIPE, and no SIGPIPE
           (v6.18.46) *)
      else
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_write]'s [access_ok] on the count the call NAMED
           (fs/read_write.c, [vfs_write]), which runs before
           [anon_pipe_write] (fs/pipe.c) and so before its readers test: a
           refused range is -EFAULT with no SIGPIPE and the pipe
           untouched.  THIS IS THE GUARD ON [Uaccess.write_source] BELOW,
           by the channel arm's argument, so the wholly-readable decline
           further down is left with exactly a source [access_ok] admits
           and the memory does not wholly back *)
      else
      if negb (pipe_end_live (m_fds m) id false) then
        (* NO READER LEFT.  fs/pipe.c [anon_pipe_write] takes
           [if (!pipe->readers) { send_sig(SIGPIPE, current, 0); ret = -EPIPE; goto out; }]
           at :460-465, and the loop repeats the pair at :501-506
           (Linux v6.18.46, commit 1f99e9ab748f).  [send_sig] carries
           no suppressing flag here: the [(iocb->ki_flags & IOCB_NOSIGNAL) == 0]
           guard is true for write(2), which cannot set that kiocb flag.
           Under the default disposition the process DIES by signal 13;
           [raise_sigpipe] is where the mask decides between that death
           and the -EPIPE a program with signal 13 blocked reads back.

           DECIDED AFTER the zero-count branch above, which is :454-456
           returning 0 BEFORE the [mutex_lock] at :458 and so before
           this test, and after [write_range_gate]'s count rule.  AND
           AFTER [access_ok], immediately above: [vfs_write] refuses a
           range that leaves the user address space before it calls
           [f_op->write_iter], so a refused range is -EFAULT and not a
           death.  No byte of the source is read on this path, exactly
           as on Linux, so the ledger stays empty.

           AND DECIDED ABOVE THE -ENOMEM ALTERNATIVE of the page
           allocation further down this arm.  THIS ORDER IS BEHAVIOUR AND
           MUST NOT BE SWAPPED.  [anon_pipe_write] tests
           [if (!pipe->readers)] at :460 before it takes the mutex-held
           path at all, and repeats the test at the TOP of each loop
           iteration (:501-506, with [break]) — both strictly before
           [page = anon_pipe_get_page(pipe)] at :515 and its
           [ret = -ENOMEM] at :517-519 (Linux v6.18.46, commit
           1f99e9ab748f).  So a write to a pipe with no reader NEVER
           reaches the allocation and can never answer -ENOMEM: it
           raises signal 13 and answers -EPIPE.  If the [pipe_needs_page]
           alternative below were moved above this test, the model would
           answer a memory failure, and let the process live, where Linux
           kills it.

           THIS USED TO FAIL CLOSED, on the argument that the model had
           no signals and no death that is not [exit].  It has both now
           ([State.with_killed], [Run.sstep_killed]), so the pipe write
           is answered instead of declined, and a program that closes a
           pipe's read end and writes is a program proofs can cover *)
        sigpipe_write
      else
      match pipe_lookup (m_pipes m) id with
      | None => unmodeled   (* an FdPipe always names a live table entry; see [Pipe.pipe2_spec] *)
      | Some st =>
          if negb (pipe_write_room st (bv_unsigned count)) then unmodeled
            (* A WRITE THAT NEEDS A SECOND RING SLOT HAS NO ANSWER HERE.
               Past one slot the pipe's fullness — and so whether
               [anon_pipe_write] sleeps at fs/pipe.c:573 — depends on the
               ring accounting the model does not carry; see
               [State.pipe_write_room], which also explains why a
               byte-counted capacity would be wrong.
               Decided before the source buffer only in the model: on
               Linux the two are independent, since a declining call here
               is one the model refuses to judge at all *)
          else
          let bs := write_source (in_mem i) buf count in
            (* [pipe_write_room] above has already bounded [count] by
               PIPE_BUF, so the clamp inside [Uaccess.write_source] is a
               no-op here and the unary [word_to_nat count] below is
               bounded by that guard rather than by the request *)
          if negb (Nat.eqb (length bs) (word_to_nat count)) then unmodeled
            (* THE SOURCE MUST BE WHOLLY READABLE.  A short
               [copy_page_from_iter] does not simply shorten the transfer
               the way it does on a file: [anon_pipe_write] answers
               -EFAULT only while NOTHING has been committed yet, and the
               short COUNT once something has.  Both of its copy sites
               fault BEFORE they publish, so neither loses bytes into the
               pipe (fs/pipe.c, v6.18.46).  The merge site copies at :488
               and on a short copy takes [ret = -EFAULT; goto out]
               (:489-492) without reaching [buf->len += ret] (:494), so the
               partial bytes sit past [buf->offset + buf->len], where
               [anon_pipe_read] never looks and the next merge overwrites
               them.  The fresh-page site copies at :522 and on a short
               copy hands the page back with [anon_pipe_put_page] and
               breaks (:523-528) without reaching [pipe->head = head + 1]
               (:530), so the ring is untouched — but its errno is
               [if (!ret) ret = -EFAULT] (:525-526), which yields -EFAULT
               only when [ret] is still 0 and otherwise returns what
               earlier iterations transferred.

               NAMING THE BOUND, because it is not the kernel that forces
               this decline.  Under [pipe_write_room] above the transfer
               reaches exactly ONE of the two sites.  An empty queue
               skips the merge path, whose guard is [chars && !was_empty]
               (:478), and takes the fresh page on the first iteration.  A
               nonempty queue carries [used >= 1] ([State.pipe_append]
               sets the mark to the page fill and [State.pipe_consume]
               never lowers it), so the guard leaves [count < PAGE_SIZE],
               [chars] is the whole [count], and the room test
               [used + count <= PIPE_BUF] IS the kernel's
               [offset + chars <= PAGE_SIZE] (:480-483) — the merge
               succeeds and the loop is never entered.  Either way no
               earlier iteration exists to have moved bytes, and Linux's
               answer across the whole admitted band is a plain -EFAULT
               — or, on the empty-queue path, the -ENOMEM of the page
               allocation the arm below admits, which precedes the copy
               and leaves the pipe unchanged.
               Declining is therefore CONSERVATIVE: it costs
               priority 3 and nothing else.  It is kept rather than
               answered because that -EFAULT holds only while the capacity
               guard confines the write to one site, so a spec arm asserting
               it would be a second rule silently depending on a bound the
               model is meant to relax later; and because moving it is a
               change to the modeled surface owing its own conform and
               reject cases, exactly as the [modeled_rw_count] note on
               [read_spec]'s pipe arm records for the other bound here.
               Fail closed until then *)
          else
            let deliver :=
              set_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) ;;
                (* append; no trace events *)
              record_copyins [(buf, length bs)] (ret_only count) in
            if pipe_needs_page st
            then alt (e <- errno_from write_errnos ;; err_ret e) deliver
              (* [anon_pipe_get_page] came back NULL: see [write_errnos].
                 THIS ALTERNATIVE STAYS BELOW THE NO-READER TEST ABOVE and
                 must not be lifted above it: fs/pipe.c:460 and :501-506
                 test [!pipe->readers] before :515 reaches this
                 allocation, so a reader-less pipe answers -EPIPE and a
                 signal 13, never -ENOMEM (Linux v6.18.46, 1f99e9ab748f) *)
            else deliver
        (* NO SHORT POSITIVE RETURN, and deliberately not the channel
           arm's short write: with room in the ring and the whole source
           readable, [anon_pipe_write] copies everything before it
           reaches its only [signal_pending] test — that test is at
           fs/pipe.c:557-561, inside the branch [!pipe_full] at :510
           sends a full ring to — so a short POSITIVE return is
           unreachable — the argument [write_spec]'s channel arm already
           spells out for transfers at or below PIPE_BUF, here extended by
           the capacity guard above to every transfer the model admits.
           The delivered COUNT is therefore the whole request; what is
           not deterministic is whether the delivery happens at all,
           which is [write_errnos] above and the environment's.
           The whole source IS read, so the range goes in the copy-in
           ledger exactly as the channel and file arms record theirs *)
      end
  | Some (FdOpaque _) => unmodeled
      (* FAIL-CLOSED: an O_PATH file is [ksys_write]'s [CLASS(fd_pos, f)]
         -EBADF, a /proc/sys file opened O_RDONLY is [vfs_write]'s
         FMODE_WRITE -EBADF, and an eventfd's write adds to a counter the
         model does not hold (fs/read_write.c, fs/file.c, fs/eventfd.c,
         read at v6.18.44; identical at v6.18.46).  None is written. *)
  end.

(** * pread64 (67) and pwrite64 (68) — a transfer at a POSITION THE CALL NAMES

    Both live in fs/read_write.c at v6.18.46: [ksys_pread64] (:752-766)
    and [ksys_pwrite64] (:782-796), each reached from its own
    [SYSCALL_DEFINE4] (:768, :798).  The two functions are the same four
    tests with the direction swapped, so the two specs below share their
    shape and differ only where Linux differs.

    WHY THESE ARE SEPARATE SPECS RATHER THAN [read_spec] AND [write_spec]
    WITH AN OFFSET ARGUMENT.  Three of the four tests happen before
    [vfs_read] / [vfs_write] is called at all, and ORDER IS BEHAVIOR:

    1. [pos < 0] is -EINVAL (:755-756, :785-786) BEFORE the descriptor is
       fetched — the [CLASS(fd, f)(fd)] declaration is the next statement
       (:758, :788).  So [pread64(-1, buf, 1, -1)] is -EINVAL and not
       -EBADF, an ordering no spec that resolves the fd first can produce.
    2. An empty descriptor slot is -EBADF (:759-760, :789-790).
    3. [FMODE_PREAD] / [FMODE_PWRITE] clear is -ESPIPE (:762 and :765,
       :792 and :795), AHEAD of the [FMODE_READ] / [FMODE_WRITE] test
       [vfs_read] / [vfs_write] opens with (:556-557, :670-671).  That
       order is behavior too: a pread of a pipe's WRITE end is -ESPIPE,
       where [read] on that same descriptor is -EBADF.
    4. Only then [vfs_read] (:552) / [vfs_write] (:666) — [read_spec] /
       [write_spec]'s body with [pos] in place of the descriptor's own
       offset AND THAT OFFSET LEFT WHERE IT WAS.  [ksys_pread64] passes
       [&pos], the address of its own parameter, so the advance
       [vfs_read] makes lands in a stack slot the syscall then discards:
       a pread neither reads nor moves [file->f_pos].

    WHICH DESCRIPTORS CARRY THE BIT.  fs/open.c [do_dentry_open] sets
    [FMODE_LSEEK | FMODE_PREAD | FMODE_PWRITE] on every file it opens
    (:961), and only the file operations' [->open] may take them away;
    fs/open.c [stream_open] (:1656-1663) clears exactly those three plus
    [FMODE_ATOMIC_POS], at :1658.  So:

    - a regular file and a directory keep both bits — no filesystem this
      model reaches installs an [->open] that clears them, and the third
      clearing site, fs/open.c [nonseekable_open] (:1638-1641), belongs to
      drivers;
    - an anonymous pipe has neither, on BOTH ends: fs/pipe.c
      [create_pipe_files] runs [stream_open] on [res[0]] and on [res[1]]
      (:966-967);
    - a socket has neither: net/socket.c [sock_alloc_file] runs
      [stream_open] at :494.

    A CHANNEL IS JUDGED AS A PIPE, the assumption [lseek_spec] already
    answers -ESPIPE on and [Sys/Fs/Sync.v] answers -EINVAL on.  It is an
    assumption about the stdio the process was handed rather than a fact
    about the fd number, and a launcher that redirects stdin from a regular file falsifies
    it: there [pread64(0, …)] transfers bytes where this answers -ESPIPE.

    O_APPEND DOES NOT ARISE.  Linux's [pwrite64] ignores [pos] on an
    O_APPEND description — [generic_write_checks] overwrites
    [iocb->ki_pos] with [i_size_read(inode)] — which would be a second
    rule for this spec to carry.  It is unreachable instead:
    [Open.openat_spec] answers [unmodeled] for an O_APPEND flag word
    (pinned in Checks/Cases/Fs/Open.v, and [Open.open_ignored_flags]
    provably excludes the bit), so no description in this model has it. *)

(** [pos < 0], the first test in both [ksys_pread64] (fs/read_write.c:755)
    and [ksys_pwrite64] (fs/read_write.c:785).  [pos] arrives as an
    [loff_t] — signed 64-bit — so the test is [bv_signed], not a
    comparison on the unsigned word, and BOTH specs make it before the
    descriptor is looked up. *)
Definition ppos_einvalb (pos : word) : bool := (bv_signed pos <? 0)%Z.

(** [pread64 fd buf count pos].

    [read_spec]'s answer at [pos] rather than at the descriptor's own
    offset, and without moving that offset, on the two descriptor kinds
    [vfs_read] can be reached with through [FMODE_PREAD].  ANSWERED, in
    the order above:

    - [pos] negative as [loff_t]: -EINVAL, decided before the descriptor
      is resolved, so a CLOSED fd with a negative [pos] is -EINVAL;
    - no such descriptor: -EBADF;
    - a channel, either end of a pipe, or a socket: -ESPIPE;
    - a write-only file descriptor: -EBADF — [vfs_read]'s [FMODE_READ]
      test (fs/read_write.c:556-557), reached because a regular file
      keeps [FMODE_PREAD] whatever its access mode;
    - a range [access_ok] refuses: -EFAULT on the count the call NAMED
      (fs/read_write.c:560-561), before the file's contents are consulted
      and before the -EISDIR below, exactly as in [read_spec];
    - [pos + count] past [LLONG_MAX]: -EINVAL, [rw_verify_area]'s
      position test (fs/read_write.c:467-469) through [rw_pos_einvalb],
      applied to the UNCLAMPED count as [vfs_read] applies it — the
      [MAX_RW_COUNT] clamp is two statements later (:566-567).
      [read_spec] does NOT model this test
      (reaching it there needs an [lseek] to an offset just under
      [2^63]); here it is unavoidable and cheap, because [pos] IS an
      argument;
    - a directory: -EISDIR (fs/libfs.c [generic_read_dir]), after both
      range verdicts;
    - a regular file: the bytes at [pos] truncated at end-of-file and at
      [State.rw_count_clamp], delivered to [buf].  Fully deterministic,
      and THE MODEL IS UNCHANGED — no offset advances, so a conforming
      pread leaves the fd table exactly as it found it.

    UNMODELED (fail closed): [read_spec]'s destination-shape gap,
    verbatim — a delivered prefix that is nonempty, writable at its first
    byte and not writable throughout, where the count Linux returns is
    the copy routine's rounded progress rather than the writable prefix
    (the note above [readv_imported] applies here word for word).  Not
    even the first delivered byte writable is -EFAULT, a real kernel
    return.  A descriptor whose path is not in the interpreted file
    system is the same [unmodeled] [read_spec] has, and [openat]
    establishes it cannot happen. *)
Definition pread64_spec (fd buf count pos : word) : Sys SyscallEffect :=
  if ppos_einvalb pos then err_ret EINVAL
    (* [pos < 0] BEFORE the descriptor, in [ksys_pread64]: fs/read_write.c,
       Linux v6.18.46, commit 1f99e9ab748f *)
  else
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* empty slot: the [CLASS(fd, f)(fd)] declaration
                                                    in [ksys_pread64], fs/read_write.c *)
  | Some (FdChannel _) => err_ret ESPIPE         (* no FMODE_PREAD, BY THE PIPED-STDIO
                                                    ASSUMPTION — see the header *)
  | Some (FdPipe _ _) => err_ret ESPIPE          (* [stream_open] on both ends, from
                                                    [create_pipe_files] in fs/pipe.c.
                                                    Decided AHEAD of [vfs_read]'s [FMODE_READ], so
                                                    the WRITE end is -ESPIPE here where [read] on
                                                    it is -EBADF *)
  | Some (FdSocket _) => err_ret ESPIPE          (* [stream_open], from [sock_alloc_file] in
                                                    net/socket.c *)
  | Some (FdFileW _ _) => err_ret EBADF          (* a regular file keeps FMODE_PREAD, so this
                                                    reaches [vfs_read] and fails its FMODE_READ
                                                    test: fs/read_write.c *)
  | Some (FdFileA _ _) => err_ret EBADF          (* and so does an append fd: O_APPEND rides on
                                                    O_WRONLY here, so FMODE_READ is clear and the
                                                    same test answers.  Where the write lands never
                                                    comes up, because nothing reads *)
  | Some (FdDevNull rd _) =>
      if negb rd then err_ret EBADF              (* FMODE_PREAD is set on a character device
                                                    ([do_dentry_open] sets it and [memory_open]
                                                    clears nothing, fs/open.c and
                                                    drivers/char/mem.c, v6.18.46), so this reaches
                                                    [vfs_read] and fails its FMODE_READ test *)
      else
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
      else
      if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
        (* [rw_verify_area]'s position test applies: [null_fops] is not
           a stream and does not carry FOP_UNSIGNED_OFFSET, so a
           [pos + count] past LLONG_MAX is -EINVAL, as on a file *)
      else ret_only (Z_to_bv 64 0)               (* [read_null]: 0, nothing touched *)
  | Some FdUrandom =>
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* FMODE_PREAD is set on the device ([do_dentry_open] sets it,
           [memory_open] clears nothing; fs/open.c, drivers/char/mem.c,
           v6.18.46), so this reaches [vfs_read], whose FMODE_READ test
           every descriptor of this kind passes, then its [access_ok] *)
      else
      if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
        (* [rw_verify_area]'s position test on the named [pos], as for
           /dev/null: [urandom_fops] is not a stream and carries no
           FOP_UNSIGNED_OFFSET *)
      else read_urandom buf count i m
        (* then [urandom_read_iter], which reads no position: the same
           bytes off the same stream a plain [read] would take *)
  | Some FdDir =>
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_read]'s [access_ok] runs before it dispatches to the
           directory's [.read], as in [read_spec]'s directory arm *)
      else
      if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
        (* [rw_verify_area] too runs before that dispatch: a directory is
           not [FMODE_STREAM], so its [ppos] is non-NULL and the position
           test applies (fs/read_write.c:459-470) *)
      else err_ret EISDIR
  | Some (FdFile p _) | Some (FdFileRW p _) =>
      (* ONE ARM FOR TWO KINDS, and nothing here has to tell them apart:
         a positional read consults no [f_pos] and advances none, so the
         only thing the access mode decides is whether [vfs_read]'s
         FMODE_READ test passes, and it passes for both.  The [FdFileW]
         and [FdFileA] arms above are where it does not. *)
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
      else
      if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
      else
      match fs_lookup (m_fs m) p with
      | None => unmodeled   (* a file fd always points into the fs; see openat *)
      | Some data =>
          (* the bytes at [pos], truncated at end-of-file and at the
             kernel's [MAX_RW_COUNT] clamp; the fd's own offset is NOT
             consulted and NOT advanced *)
          let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count)) in
          match read_bytes_map (in_wmem i) buf (len_word bs) with
          | None =>
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => err_ret EFAULT           (* not even the first delivered byte can land:
                                                    real -EFAULT, nothing delivered *)
              | Some _ => unmodeled              (* partially writable destination: fail closed,
                                                    see [readv_imported] *)
              end
          | Some _ =>
              pure (mkEffect (len_word bs) (delivered_writes buf bs) [])
              (* no state change at all, and no trace events: file
                 contents are observed at exit only *)
          end
      end
  | Some (FdOpaque _) => unmodeled
      (* FAIL-CLOSED: an O_PATH file is [ksys_pread64]'s [CLASS(fd, f)]
         -EBADF (fs/read_write.c and fs/file.c, read at v6.18.44; identical at v6.18.46); a
         positional read of an eventfd or a /proc/sys file is not
         written, and an [ONsFile]'s object is of unknown type.  None of
         the four answers is. *)
  end.

(** [pwrite64 fd buf count pos].

    [write_spec]'s FILE arm at [pos], without moving the descriptor's
    offset.  The three descriptor kinds whose write arms make
    [write_spec] hard — a channel (short writes it cannot rule out), a
    pipe (SIGPIPE, ring capacity) and a socket (SIGPIPE, permanently
    unmodeled) — never reach the transfer here: none of them carries
    [FMODE_PWRITE], so all three are -ESPIPE, decided two statements
    earlier.  ANSWERED:

    - [pos] negative as [loff_t]: -EINVAL, before the descriptor;
    - no such descriptor: -EBADF;
    - a channel, either end of a pipe, or a socket: -ESPIPE;
    - a read-only file descriptor, or a directory: -EBADF, [vfs_write]'s
      [FMODE_WRITE] test (fs/read_write.c:670-671).  A directory reaches
      that test rather than -EISDIR, and reaches it holding
      [FMODE_PWRITE], since [do_dentry_open] set the bit for it too;
    - a range [access_ok] refuses: -EFAULT (fs/read_write.c:674-675).
      [write_spec] does NOT make this test — it judges a write by its
      readable prefix, a known divergence — and this arm does, because the argument for leaving it out there
      (an unreadable buffer is already the -EFAULT) does not survive a
      count whose range merely ENDS past [State.TASK_SIZE];
    - [pos + count] past [LLONG_MAX]: -EINVAL, [rw_verify_area]
      (fs/read_write.c:467-469), on the unclamped count;
    - a regular file opened for writing, AT ANY COUNT: the readable
      prefix of the CLAMPED range lands at [pos], zero-filling any hole
      past end-of-file ([Fs.file_write]), and the return is that
      prefix's length.  DETERMINISTIC — a regular-file write falls short
      only under conditions the model does not have, the argument
      [write_spec] spells out.  The descriptor's offset does not move.

    THE COUNT IS NOT CAPPED AT [Uaccess.rw_bytes_max], and this arm
    has no count gate at all: the -EFAULT test two statements
    above already decides this arm's range, and
    [Uaccess.rw_range_of_access_ok] is the proof that the
    disjunctive gate [write] carries would be constantly true here.  So
    the arm has no decline of its own, and it answers
    the ordinary [pwrite64(fd, buf, 1 << 20, 0)] that Linux answers.

    The transfer is then the kernel's, exactly as [write]'s is: Linux
    clamps a scalar write at [MAX_RW_COUNT] before the write operation
    ([State.rw_count_clamp]; [vfs_write], fs/read_write.c:680-681,
    v6.18.46 — reached from [ksys_pwrite64], fs/read_write.c:782-796),
    so the source prefix is [Uaccess.write_source] and an over-clamp
    count is a SHORT write, not an error.  Below 2^31 the clamp is a
    no-op.

    UNMODELED (fail closed): a hole past end-of-file larger than
    [modeled_zero_fill] can build.  That is [write_spec]'s decline and
    for its reasons, but it matters more here: [pos] is an argument, so
    a single call can NAME an offset far past the end where [write] has
    to walk one there through [lseek].  [modeled_file_gap] is what keeps
    [Fs.file_write]'s unary conversion of that offset bounded by the
    file's own length plus a constant, and it is
    tested on [pos] here exactly as it is tested on the fd's offset
    there, so pwrite reaches no offset a chain of writes could not. *)
Definition pwrite64_spec (fd buf count pos : word) : Sys SyscallEffect :=
  if ppos_einvalb pos then err_ret EINVAL
    (* [pos < 0] BEFORE the descriptor, in [ksys_pwrite64]: fs/read_write.c,
       Linux v6.18.46, commit 1f99e9ab748f *)
  else
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* empty slot: the [CLASS(fd, f)(fd)] declaration
                                                    in [ksys_pwrite64], fs/read_write.c *)
  | Some (FdChannel _) => err_ret ESPIPE         (* no FMODE_PWRITE, BY THE PIPED-STDIO
                                                    ASSUMPTION — see the header.  This is where
                                                    the channel's short-write over-approximation
                                                    stops being reachable at all *)
  | Some (FdPipe _ _) => err_ret ESPIPE          (* [stream_open] on both ends, from
                                                    [create_pipe_files] in fs/pipe.c.
                                                    A pwrite to a pipe whose
                                                    reader is gone is -ESPIPE and raises NO
                                                    SIGPIPE: [anon_pipe_write] is never reached *)
  | Some (FdSocket _) => err_ret ESPIPE          (* [stream_open], from [sock_alloc_file] in
                                                    net/socket.c.  The -EPIPE-and-SIGPIPE that
                                                    [write_spec]'s socket arm answers is
                                                    unreachable through pwrite *)
  | Some (FdFile _ _) => err_ret EBADF           (* fd open read-only: [vfs_write]'s FMODE_WRITE
                                                    test, fs/read_write.c *)
  | Some FdUrandom => err_ret EBADF             (* FMODE_PWRITE is set on the device, so this
                                                    reaches [vfs_write]'s FMODE_WRITE test, which a
                                                    read-only descriptor fails: -EBADF before the
                                                    buffer or the position is looked at *)
  | Some (FdDevNull _ wr) =>
      if negb wr then err_ret EBADF              (* FMODE_PWRITE is set on the device, so the
                                                    same FMODE_WRITE test answers *)
      else
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
      else
      if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
        (* [rw_verify_area] on the named [pos], as for pread *)
      else ret_only (Z_to_bv 64 (rw_count_clamp count))
        (* [write_null] (drivers/char/mem.c, v6.18.46): the clamped
           count, no byte read, no ledger — [write_spec]'s arm without
           the range gate, which [access_ok] above makes redundant.
           CHOSEN, not an oversight: [write] on this kind declines above
           [Uaccess.rw_bytes_max] at an out-of-range buffer where this
           arm answers -EFAULT, the same difference the file kinds
           carry between the two syscalls *)
  | Some FdDir => err_ret EBADF                  (* a directory is O_RDONLY: the same FMODE_WRITE
                                                    test, and NOT -EISDIR *)
  | Some (FdFileA _ _) => unmodeled
      (* AN APPEND FD IS THE ONE KIND WHOSE ANSWER IS NOT THE [FdFileW]
         ARM BELOW, and the difference is the whole point of this
         syscall.  [iocb_flags] (include/linux/fs.h, Linux v6.18.46,
         commit 1f99e9ab748f) turns O_APPEND into IOCB_APPEND, and
         [generic_write_checks] (mm/filemap.c, same commit) then runs
         [if (iocb->ki_flags & IOCB_APPEND) iocb->ki_pos =
         i_size_read(inode);] -- so the [pos] [pwrite64] named is
         DISCARDED and the bytes land at end-of-file.  Linux does this on
         purpose and POSIX does not require it; either way it is what the
         pinned tree does.

         Answering it with the arm below would put the bytes at [pos],
         which is a wrong modeled behaviour rather than a missing one, so
         this fails closed instead.  What a real arm would have to be is
         [write_spec]'s [FdFileA] case with [pos] dropped, kept behind
         [ksys_pwrite64]'s own -EINVAL and -ESPIPE gates
         (fs/read_write.c, [ksys_pwrite64]); that is a modelling change
         with its own argument to make, not something this decline
         prejudges.  No example can reach it: an [FdFileA] is minted only
         by [Open.openat_append_spec] (both append words), and no
         example opens a file in append mode and then pwrites
         it. *)
  | Some (FdFileW p _) | Some (FdFileRW p _) =>
      (* ONE ARM FOR TWO KINDS, and one arm rather than two copies is the
         point: a positional write neither reads nor moves [f_pos], so the
         access mode decides only [vfs_write]'s FMODE_WRITE test, which
         O_RDWR passes as O_WRONLY does.  There is nothing left for a
         second arm to say, and so nothing for it to drift on.  The
         [FdFileA] arm above is separate for the opposite reason: there
         the access mode is the same and the POSITION is not.

         THE READ-WRITE KIND THEREFORE INHERITS THIS ARM'S COUNT RULE,
         whatever it is, and sharing the arm is what keeps the two kinds
         from ever disagreeing about it.  See the gate note below. *)
      if negb (access_okb buf (bv_unsigned count)) then err_ret EFAULT
        (* [vfs_write]'s [access_ok] on the count the call NAMED:
           fs/read_write.c:674-675 *)
      else
      if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
        (* [rw_verify_area], before the write operation and on the
           UNCLAMPED count, the order fs/read_write.c:677-681 has *)
      else
      let bs := write_source (in_mem i) buf count in
        (* NO COUNT GATE.  [write]'s arms carry
           [Uaccess.modeled_rw_range]; this one would carry it for
           nothing, because [access_ok] has already been tested above and
           [Uaccess.rw_range_of_access_ok] turns that into the
           gate's second disjunct.  So the range question is asked once,
           by Linux's own test, and the size question is not asked at
           all.

           [Uaccess.write_source] rather than [State.readable_bytes] is
           the other half: it is the readable prefix of the range Linux
           CLAMPS at [MAX_RW_COUNT] ([State.rw_count_clamp]), so an
           over-clamp count is a short write here as it is for [write],
           and no unary numeral bigger than the clamp is built. *)
      if negb (w_is0 count) && Nat.eqb (length bs) 0
      then
        (* NOTHING READABLE AT [buf]: a real -EFAULT, and a file left
           LONGER.  [generic_perform_write] (mm/filemap.c) runs
           [write_begin] and then [write_end] with [copied = 0] even
           when the atomic copy moved nothing, and [shmem_write_end]
           (mm/shmem.c) extends the file in
           [if (pos + copied > inode->i_size) i_size_write(inode, pos +
           copied);] -- here to [pos] exactly.  [write_file_tail] holds
           the same statement for [write] and [writev], and this spec
           reaches it through [write_fault_extend], which declines the
           hole the model will not build.  The descriptor's own offset
           is not touched, and would not be even on a delivering write:
           [ksys_pwrite64] passes [&pos], a stack slot it discards *)
        match write_fault_extend (m_fs m) p pos with
        | None => unmodeled
        | Some upd => upd (err_ret EFAULT)
        end
      else
      match fs_lookup (m_fs m) p with
      | None => unmodeled   (* a file fd always points into the fs; see openat *)
      | Some data =>
          if negb (modeled_file_gap data pos bs) then unmodeled
            (* a hole past end-of-file too large to zero-fill as a byte
               list — see [modeled_file_gap], and the pwrite-specific note
               in this spec's header *)
          else
          set_fs (fs_set (m_fs m) p (file_write data pos bs)) ;;  (* write the prefix at [pos] *)
          if w_is0 count
          then ret_only (len_word bs)
            (* a zero-length write reads no user byte, so its ledger is
               empty rather than a singleton zero-length range *)
          else record_copyins [(buf, length bs)] (ret_only (len_word bs))
      end
  | Some (FdOpaque _) => unmodeled
      (* FAIL-CLOSED, as [pread64_spec]'s arm: none of the four answers
         is written *)
  end.

(** [IOV_MAX] (= Linux UIO_MAXIOV) and [MAX_RW_COUNT] are in State.v,
    beside the iovec-import helpers that test them. *)

(** writev's and readv's [iovcnt] reach the kernel as a full 64-bit
    register, declared [unsigned long] at the syscall boundary, and reach
    [__import_iovec] through [import_iovec]'s [unsigned nr_segs]
    (lib/iov_iter.c, v6.18.46): only the low 32 bits are validated and
    used.  writev(fd, iov, 2^32 + 2) really writes 2 iovecs, writev(fd,
    iov, 2^32) transfers nothing and returns 0, and a count whose low 32
    bits exceed [IOV_MAX] — every negative [int] count included — is
    -EINVAL.  Commits bc917be8 and 0504c074 (Al Viro, first released in
    v4.1) put the [unsigned] boundary there; qemu-user's [lock_iovec]
    validates the raw 64-bit count instead, and the model rejects its
    -EINVAL for a count over [IOV_MAX] whose low 32 bits are in range. *)
Definition iovcnt32 (iovcnt : word) : word := abi_low32 iovcnt.

(** A writev buffer-shape gap: the model cannot describe this transfer, so
    it DECLINES.  One name for every writev decline, as [readv_buf_gap] is
    for readv.  (An unreadable iovec array or source buffer is NOT routed
    here: those are a genuine -EFAULT / short write via [gather_prefix].) *)
Definition writev_buf_gap : Sys SyscallEffect := unmodeled.

(** [writev fd iov iovcnt], in the order stable Linux v6.18.46 decides it
    (fs/read_write.c [do_writev] -> [vfs_writev] -> lib/iov_iter.c
    [import_iovec] -> [__import_iovec], then [rw_verify_area] and the
    write operation):

    1. [do_writev]: [fdget_pos] on the fd truncated to 32 bits
       ([Syscall.fd32]); an empty slot is -EBADF.
    2. [vfs_writev]: [FMODE_WRITE] clear is -EBADF — stdin BY ASSUMPTION
       (piped stdio), a
       read-only file, a directory (O_RDONLY), a pipe's READ end.
       [FMODE_CAN_WRITE] clear is -EINVAL and never fires on a modeled fd.
    3. The import, which is [State.import_iovecs] — the same function
       readv imports through, since [vfs_writev] and [vfs_readv] call the
       same [import_iovec]: the count on its low 32 bits, zero segments
       reading nothing, over [IOV_MAX] -EINVAL, the descriptors in index
       order with an unreadable field -EFAULT ahead of a negative
       [iov_len]'s -EINVAL, [access_ok] on every entry's uncapped length
       (a single descriptor caps at [MAX_RW_COUNT] first), then the
       aggregate cap.  Counts 9 through [IOV_MAX] may also return -ENOMEM
       from the temporary allocation, which this arm does not represent.
    4. A zero aggregate returns 0 before [rw_verify_area] and before the
       write operation, on every fd kind — the destination is never
       consulted, so a pipe write end answers it too, ahead of the
       vectored-pipe decline below.
    5. [rw_verify_area]: for a file with a position — the [FdFileW] arm,
       since pipes are [FMODE_STREAM] — [(loff_t)(pos + count) < 0] is
       -EINVAL ([rw_pos_einvalb]).
    6. The write operation.  Source readability follows [write_spec]'s
       copy_from_user discipline across the flattened sequence: Linux
       consumes the iovecs in order and faults mid-stream, so the bytes
       AVAILABLE to the write are the GATHERABLE PREFIX
       ([State.gather_prefix]) — everything before the first unreadable
       source byte — over the CAPPED vector ([State.cap_iovecs]).  Nothing
       gatherable while something was requested: -EFAULT.  On a channel
       the write delivers a NONEMPTY PREFIX of the gatherable prefix, of
       the environment's choosing, exactly as [write_spec] does; on a file
       exactly the gatherable prefix, advancing the offset.  A vectored
       write to a pipe or a socket declines ([write_spec]'s socket
       argument; the pipe atomicity argument is per transfer, not per
       vector).

    So a writev's trace equals the trace of the equivalent [write] — and
    of the equivalent SEQUENCE of writes, one per iovec, since byte-level
    events erase chunking (this is why musl's stdio flushing through
    writev costs nothing; see Checks/Examples.v).  The transfer bound is
    [write]'s, and it is the KERNEL's: the aggregate is capped at
    [MAX_RW_COUNT] by [State.cap_iovecs], the same clamp
    [__import_iovec]'s loop applies, and no bound of the model's own
    sits in front of it.  The hole a file write may open past
    end-of-file is [write]'s too ([modeled_file_gap]), decided after the
    import, which is where Linux learns the lengths.  A write never
    returns an error-encoded count: the aggregate cap keeps the returned
    length under [MAX_RW_COUNT], which is what the [addr_is_error_b]
    arms below rely on. *)
(** * The three writev arms of a FILE, and what they share

    The same three descriptor kinds [write_spec] has, and the same
    division of labour: [writev_file_arm] below is everything the three
    share, and [place] is the kind's own middle.  The differences are
    narrower here than on the scalar side, because a vectored write has
    no count argument of its own:

    - NO COUNT GATE.  The aggregate is capped at [MAX_RW_COUNT] by
      [State.cap_iovecs] — the kernel's own clamp, applied during the
      import — so there is no [Uaccess.modeled_rw_range] and no bound of
      the model's own in front of it.
    - [rw_verify_area]'s POSITION TEST IS SHARED, and on all three kinds
      it reads the fd's REAL [f_pos].  That is the surprising half of the
      append arm and it is stated there.
    - the GAP GUARD, the DESTINATION and the ENTRY WRITTEN BACK vary, as
      they do for [write], and for the same reasons.

    Reading the shared shape out of a helper is what makes the append
    arm's kept [rw_pos_einvalb] a fact about the kernel rather than a
    line three copies of one arm happen to agree on. *)

(** The ledger and the return, shared by all three file writev arms: the
    prefix of the CAPPED vector the write actually read, and its length.
    A zero aggregate never reaches here — [writev_file_arm] returns 0
    above it, without inspecting a source byte. *)
Definition writev_ledger (iovs : list (word * word)) (bs : list byte)
  : Sys SyscallEffect :=
  record_copyins (iov_prefix_accesses (cap_iovecs iovs) (length bs))
                 (ret_only (len_word bs)).

(** The shape every file writev arm shares: the import and its access
    ledger, the import's two errnos, the zero-aggregate 0,
    [rw_verify_area]'s position test on [off], the -EFAULT when nothing
    is gatherable, the error-encoded-length decline, and the ledger.

    [place bs] is the KIND's own middle: [None] where that kind declines,
    otherwise the state update carrying the destination and the
    written-back entry, handed the shared ledger as its continuation.  It
    is not passed the imported vector: the ledger is the only thing that
    reads it, and the ledger is built here.  [fault] is its other
    middle, and it is [write_file_tail]'s: a gathered prefix of nothing
    is -EFAULT with the file STILL EXTENDED to the write's offset,
    because [generic_perform_write] (mm/filemap.c) reaches
    [a_ops->write_end(..., copied = 0, ...)] and [shmem_write_end]
    (mm/shmem.c) answers it with
    [if (pos + copied > inode->i_size) i_size_write(inode, pos + copied);].
    A vectored write reaches the same [vfs_write] body as a scalar one,
    so this is one kernel statement and not two.  Linux v6.18.46.

    THE [addr_is_error_b] DECLINE SITS BEHIND [place] and not in front of
    it: after the kind's own
    guards and before its update.  It is unreachable under the aggregate
    cap in any case — the note on this spec's header says why it is kept —
    and every decline around it is the same [writev_buf_gap], so the
    position is not observable. *)
Definition writev_file_arm (mp : word -> option byte)
    (iov iovcnt off : word)
    (fault : option (Sys SyscallEffect -> Sys SyscallEffect))
    (place : list byte -> option (Sys SyscallEffect -> Sys SyscallEffect))
  : Sys SyscallEffect :=
  record_copyins (import_iovecs_accesses mp iov (iovcnt32 iovcnt))
  (match import_iovecs mp iov (iovcnt32 iovcnt) with
   | ImpFault => err_ret EFAULT
   | ImpInval => err_ret EINVAL
   | ImpOk iovs0 =>
       let total := iovs_total (cap_iovecs iovs0) in
       let bs := writev_gathered mp iovs0 in
       if Z.eqb total 0 then ret_only (Z_to_bv 64 0)   (* zero aggregate: 0, offset unchanged *)
       else if rw_pos_einvalb off total then err_ret EINVAL  (* [rw_verify_area], before the write *)
       else if Nat.eqb (length bs) 0
       then match fault with
            | None => writev_buf_gap
            | Some upd => upd (err_ret EFAULT)
            end
       else
         match place bs with
         | None => writev_buf_gap
         | Some upd =>
             if addr_is_error_b (len_word bs) then writev_buf_gap
             else upd (writev_ledger iovs0 bs)
         end
   end).

Definition writev_spec (fd iov iovcnt : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* fd not open: real -EBADF *)
  | Some (FdFile _ _) => err_ret EBADF           (* fd open read-only: real -EBADF *)
  | Some FdDir => err_ret EBADF                  (* directory fds are O_RDONLY *)
  | Some (FdSocket _) => writev_buf_gap           (* A VECTORED SOCKET WRITE IS UNMODELED, and
                                                    unlike the scalar arm it stays so for every
                                                    socket state: [write_spec]'s socket arm answers
                                                    the no-connection states because the transfer
                                                    is the only thing in the way there, and here
                                                    the gathered transfer is in the way too.  No
                                                    soundness claim rests on the difference: a
                                                    decline is sound under either *)
  | Some (FdChannel ch) =>
      if w_is0 ch then err_ret EBADF             (* channel 0 is read-only BY ASSUMPTION *)
      else
        record_copyins
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
        | ImpFault => err_ret EFAULT             (* unreadable descriptor, or a failed access_ok *)
        | ImpInval => err_ret EINVAL             (* count over IOV_MAX, or a negative iov_len *)
        | ImpOk iovs0 =>
            let total := iovs_total (cap_iovecs iovs0) in
            let bs := writev_gathered (in_mem i) iovs0 in
            if Z.eqb total 0 then ret_only (Z_to_bv 64 0)   (* zero aggregate: 0, no buffer inspected *)
            else if negb (m_channel_reader m) then sigpipe_write
              (* THE FAR END HAS NO READER, and writev takes the same
                 path write does: fs/read_write.c [do_writev] imports
                 the iovec array -- which is why the ledger above keeps
                 its entry on this branch -- then [vfs_writev] reaches
                 [f_op->write_iter], which for a pipe is
                 [anon_pipe_write] and takes [send_sig(SIGPIPE, ...)]
                 and -EPIPE at fs/pipe.c:460-465, and for a socket is
                 [sock_write_iter] and reaches net/core/stream.c
                 [sk_stream_error] :190-198.  AFTER the zero-aggregate
                 branch for the scalar arm's reason (fs/pipe.c:454-456
                 returns 0 before the readers test), and with no
                 [access_ok] test of its own, because [import_iovecs]
                 above has already made it and answered [ImpFault] if
                 it failed.  Linux v6.18.46, commit 1f99e9ab748f.

                 WITHOUT THIS ARM [writev] WOULD BE UNSOUND WHERE
                 [write] IS NOT: it would answer a byte count and let
                 the program run on for a launch the input says has no
                 reader, which asserts the process SURVIVED *)
            else if Nat.eqb (length bs) 0 then err_ret EFAULT  (* not even the first byte readable *)
            else if addr_is_error_b (len_word bs) then writev_buf_gap
                 (* unreachable under the aggregate cap; see above *)
            else
              ds <- choose (fun ds : list byte =>
                              (1 <= Z.of_nat (length ds))%Z
                              /\ (Z.of_nat (length ds) < two_pow_64)%Z
                              /\ addr_is_error_b (len_word ds) = false
                              /\ ds = firstn (length ds) bs) ;;
              emit (map (WriteEv ch) ds) ;;      (* the per-byte events of the equivalent write *)
              record_copyins
                (iov_prefix_accesses (cap_iovecs iovs0) (length ds))
                (ret_only (len_word ds))          (* the (possibly short) delivered length *)
        end)
  | Some (FdFileW p off) =>
      writev_file_arm (in_mem i) iov iovcnt off
        (write_fault_extend (m_fs m) p off) (fun bs =>
        match fs_lookup (m_fs m) p with
        | None => None                  (* an FdFileW always points into the fs (see openat) *)
        | Some data =>
            if negb (modeled_file_gap data off bs) then None
              (* a hole past end-of-file too large to zero-fill, as in [write_spec] *)
            else
            Some (fun k =>
              set_fs (fs_set (m_fs m) p (file_write data off bs)) ;;
                (* as the equivalent write *)
              set_fds (fd_insert (m_fds m) fd
                         (FdFileW p (off + len_word bs))) ;;   (* advance offset *)
              k)
        end)
  | Some (FdFileRW p off) =>
      (* THE [FdFileW] ARM ABOVE with the entry written back under this
         kind, through the SAME [writev_file_arm]: everything the two
         arms do turns on [f_pos] and on nothing else the access mode
         reaches — [rw_verify_area]'s position test, the destination of
         the gathered bytes, and the advance — so the only thing this arm
         may state for itself is the entry.  The [FdFileA] arm below is
         the one that differs, and it differs in the destination. *)
      writev_file_arm (in_mem i) iov iovcnt off
        (write_fault_extend (m_fs m) p off) (fun bs =>
        match fs_lookup (m_fs m) p with
        | None => None                  (* an FdFileRW always points into the fs (see openat) *)
        | Some data =>
            if negb (modeled_file_gap data off bs) then None
            else
            Some (fun k =>
              set_fs (fs_set (m_fs m) p (file_write data off bs)) ;;
              set_fds (fd_insert (m_fds m) fd
                         (FdFileRW p (off + len_word bs))) ;;
              k)
        end)
  | Some (FdFileA p off) =>
      (* The [FdFileW] arm with one line moved and one line kept, and the
         line that is KEPT is the surprising one.  [rw_verify_area]
         (fs/read_write.c) is handed [&file->f_pos] by
         [vfs_writev]/[do_iter_write] and runs BEFORE the iterator, so
         its [(loff_t)(pos + count) < 0] test reads the fd's REAL
         position even on an append fd -- [generic_write_checks]
         overrides [ki_pos] only once the write is under way
         (mm/filemap.c).  A [lseek(fd, LLONG_MAX, SEEK_SET)] on an
         append fd therefore still turns the next nonempty writev into
         -EINVAL, and that test lives in [writev_file_arm] BECAUSE it is
         shared: this arm is the reason it is stated on [off] rather than
         on the destination.  What MOVES is the destination: the bytes go
         to [len_word data], not to [off] -- and with it the
         [modeled_file_gap] guard, which an append write cannot fail
         ([append_opens_no_gap]) and so does not carry.  Linux v6.18.46
         throughout. *)
      writev_file_arm (in_mem i) iov iovcnt off
        (Some write_fault_keep) (fun bs =>
        match fs_lookup (m_fs m) p with
        | None => None                  (* an FdFileA always points into the fs (see openat) *)
        | Some data =>
            Some (fun k =>
              set_fs (fs_set (m_fs m) p
                        (file_write data (len_word data) bs)) ;;
              set_fds (fd_insert (m_fds m) fd
                         (FdFileA p (append_new_pos data bs off))) ;;
                (* the zero-aggregate case returned above without touching
                   anything, so [bs] is nonempty here and this is the
                   end-of-file arm of [append_new_pos]; naming the helper
                   keeps the two write arms reading alike *)
              k)
        end)
  | Some FdUrandom => err_ret EBADF             (* O_RDONLY, always: [vfs_writev]'s FMODE_WRITE
                                                    test (fs/read_write.c, v6.18.46), before the
                                                    iovec array is imported *)
  | Some (FdDevNull _ wr) =>
      if negb wr then err_ret EBADF              (* O_RDONLY: [vfs_writev]'s FMODE_WRITE test,
                                                    before the import *)
      else
        record_copyins
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
        | ImpFault => err_ret EFAULT             (* [import_iovec]'s own -EFAULT and -EINVAL, the
                                                    descriptor array being the ONLY user memory
                                                    this call reads *)
        | ImpInval => err_ret EINVAL
        | ImpOk iovs0 =>
            ret_only (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))
            (* [write_iter_null] (drivers/char/mem.c, v6.18.46) advances
               the iterator by [iov_iter_count] and returns it: the
               aggregate the import capped at [MAX_RW_COUNT]
               ([cap_iovecs]), 0 included — [vfs_writev] returns at
               [if (!tot_len) goto out] with the same 0.  The buffers
               are never read, so no per-segment copy-in joins the
               ledger *)
        end)
  | Some (FdPipe _ w) =>
      if negb w then err_ret EBADF               (* the READ end is O_RDONLY: real -EBADF, before
                                                    any iovec is inspected *)
      else
        record_copyins
          (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
        | ImpFault => err_ret EFAULT
        | ImpInval => err_ret EINVAL
        | ImpOk iovs0 =>
            if Z.eqb (iovs_total (cap_iovecs iovs0)) 0 then ret_only (Z_to_bv 64 0)
              (* zero aggregate: decided above the file kind, so no pipe
                 state enters it — [vfs_writev] returns at
                 [if (!tot_len) goto out] before [anon_pipe_write], whose
                 [!pipe->readers] SIGPIPE test is therefore never reached *)
            else writev_buf_gap
              (* VECTORED PIPE WRITES ARE UNMODELED: the atomicity
                 argument that makes the scalar arm deterministic is
                 stated per transfer, not per vector.  Fail closed *)
        end)
  | Some (FdOpaque _) => unmodeled
      (* FAIL-CLOSED: an O_PATH file is [do_writev]'s [CLASS(fd_pos, f)]
         -EBADF, a /proc/sys file opened O_RDONLY is [vfs_writev]'s
         FMODE_WRITE -EBADF, and an eventfd's write adds to a counter the
         model does not hold (fs/read_write.c, fs/eventfd.c, read at
         v6.18.44; identical at v6.18.46).  None is written. *)
  end.


(** WHICH KERNEL THIS IS A MODEL OF.

    Stable Linux v6.18.46, riscv64 — one tree, the one every claim in
    this file is read from, and the order below is that tree's order
    (fs/read_write.c [do_readv] -> [vfs_readv] -> lib/iov_iter.c
    [import_iovec] -> [__import_iovec], then [rw_verify_area] and the
    read operation):

    1. [do_readv]: [fdget_pos] on the fd truncated to 32 bits
       ([Syscall.fd32]); an empty slot is [-EBADF].
    2. [vfs_readv]: [FMODE_READ] clear is [-EBADF]; [FMODE_CAN_READ]
       clear is [-EINVAL].  The second never fires on a modeled fd:
       fs/open.c [do_dentry_open] and fs/file_table.c [alloc_file] set
       it whenever the file operations carry [.read] or [.read_iter],
       and every kind here does — a directory has
       [.read = generic_read_dir] (fs/libfs.c), a pipe
       [pipeanon_fops.read_iter], a socket [socket_file_ops.read_iter],
       a regular file its filesystem's [.read_iter].  See [readable_fd].
    3. [__import_iovec]: a count of one takes [__import_iovec_ubuf]
       ahead of every other test; otherwise [iovec_from_user] answers 0
       segments with nothing read, a count over [UIO_MAXIOV] with
       [-EINVAL], allocates for 9 through 1024 (an optional [-ENOMEM],
       declined here — [readv_heap_iovecb]), and copies the descriptors
       in index order; then a second loop applies [access_ok] to every
       entry's UNCAPPED length and clamps the aggregate at
       [MAX_RW_COUNT].  All of this is [State.import_iovecs], which
       carries the per-function argument.  The count reaches
       [__import_iovec] through an [unsigned] parameter
       ([import_iovec]'s [nr_segs]), so only its low 32 bits are ever
       consulted ([iovcnt32]): [2^32 + 2] imports two segments,
       [-1] is [2^32 - 1] and [-EINVAL].
    4. [vfs_readv]: a zero aggregate returns 0 before [rw_verify_area]
       and before the read operation — on a directory, on a socket that
       never connected, at any offset.
    5. [rw_verify_area]: for a file with a position (everything but the
       [FMODE_STREAM] kinds — pipes and sockets, whose [file_ppos] is
       NULL), [(loff_t)(pos + count) < 0] is [-EINVAL] unless
       [unsigned_offsets], which is [FOP_UNSIGNED_OFFSET] on the file
       operations — set by a handful of drivers and by fs/proc/base.c
       for [/proc/PID/mem], by no filesystem the model reaches.  See
       [rw_pos_einvalb].  The LSM and fanotify hooks in
       the same function are an ENVIRONMENT PREMISE: nothing in the
       modeled configuration denies a read.
    6. The read operation.  A directory's is [generic_read_dir], which
       is [return -EISDIR] and never looks at the destination.  For the
       kinds that copy, the destination decides — see [readv_imported].

    Two things are NOT admitted, because both are qemu-user's
    behaviour rather than any Linux's: a [-EINVAL] for a raw count over
    [IOV_MAX] decided before the fd (Linux truncates the count and
    resolves the fd first), and a 0 or [-EFAULT] decided by locking the
    destination vector before the read (Linux touches the destination
    only as far as the copy goes).

    POINTER MASKING.  riscv64's [access_ok] untags its address
    (arch/riscv/include/asm/uaccess.h, under CONFIG_RISCV_ISA_SUPM), and
    [State.access_okb] does not.  The untagging is the identity at
    [PMLEN = 0], which every [execve] establishes and which only two
    unmodeled syscalls can change; the argument, its citations, and the
    closed-world assumption it rests on are on [State.access_okb]. *)

(** The fd kinds a readv reaches once the [FMODE_READ] gate has passed.
    Naming them keeps [readv_imported] total without carrying an arm for
    a case the gate has already excluded. *)
Inductive ReadableFd : Type :=
  | RdChannel (chan : word)
  | RdFile (p : path) (offset : word)
  (** The same file at the same offset, through an O_RDWR description.
      A SEPARATE CONSTRUCTOR RATHER THAN [RdFile], because
      [readv_imported] WRITES THE ENTRY BACK: folding an O_RDWR fd into
      [RdFile] would advance it correctly and store it under the
      read-only kind, silently turning the descriptor into one a later
      write answers -EBADF on.  That is a modeled wrong answer produced
      by a read, which is the hardest kind to notice. *)
  | RdFileRW (p : path) (offset : word)
  | RdDir
  | RdSocket (sk : SockState)
  | RdPipe (id : word)
  | RdDevNull
  (** /dev/null opened for reading.  It carries nothing because the
      read arm consults nothing: [read_iter_null] returns 0. *)
  | RdUrandom.
  (** /dev/urandom, which is only ever open for reading.  It carries
      nothing because the stream it would read is the model's
      ([State.m_urandom]), not the descriptor's. *)

(** [FMODE_READ] (fs/read_write.c [vfs_readv]'s first test, v6.18.46):
    an fd not open for reading is [-EBADF], decided BEFORE the iovec
    array is imported.  Of the channels only stdin is readable — an
    ASSUMPTION about the stdio the process was handed rather than a fact
    about the fd number, and the one [readv_spec] shares with
    [read_spec].
    [FdFileW] is the model's O_WRONLY fd, and a pipe's WRITE end is the
    third thing this gate turns away.

    A SOCKET PASSES THIS GATE, and answering [None] for it here would be
    the worst single mistake available in the socket change.  It
    compiles instantly, it needs no new arm anywhere downstream, it
    greens the whole readv proof stack — and it turns [readv] on a
    socket into a FALSE -EBADF: a confidently wrong MODELED answer, not
    a modeling gap, so [modeled] cannot see it and no fail-closed arm
    catches it.  net/socket.c [sock_alloc_file] creates every socket file
    with [O_RDWR | (flags & O_NONBLOCK)], so FMODE_READ is always set;
    the gate must let a socket through and the read specs must answer
    for it.  [RdSocket] carries the socket's state so they can.

    A PIPE'S READ END PASSES IT FOR THE SAME REASON, and the write end
    is the one case here where [None] is the kernel's own answer rather
    than a shortage of state: fs/pipe.c [create_pipe_files] opens
    [res[0]] O_RDONLY and [res[1]] O_WRONLY, so -EBADF on the write end
    is exact.  [RdPipe] carries the pipe id, which is what the read specs
    need to reach the queue in [m_pipes]. *)
Definition readable_fd (e : FdEntry) : option ReadableFd :=
  match e with
  | FdChannel ch => if w_is0 ch then Some (RdChannel ch) else None
  | FdFile p off => Some (RdFile p off)
  | FdFileRW p off => Some (RdFileRW p off)
    (* O_RDWR carries FMODE_READ, so the gate must let it through, and
       [RdFileRW] is what keeps the write-back on the right kind *)
  | FdDir => Some RdDir
  | FdSocket sk => Some (RdSocket sk)
  | FdFileW _ _ => None
  | FdFileA _ _ => None
    (* an append fd is O_WRONLY too, so this is the kernel's own -EBADF
       and not a shortage of state *)
  | FdPipe id w => if w then None else Some (RdPipe id)
    (* a pipe's READ end really is open for reading, so the gate must let
       it through and the write end must not: [readv] on the write end is
       the kernel's -EBADF, not a modeling gap.  What [readv] then does
       with the read end is a separate decision — see [readv_imported] *)
  | FdDevNull rd _ => if rd then Some RdDevNull else None
    (* the access mode the open granted IS FMODE_READ, so the gate is
       exact in both directions: a write-only /dev/null gets
       [vfs_readv]'s -EBADF *)
  | FdUrandom => Some RdUrandom
    (* opened O_RDONLY by construction, so FMODE_READ is set on every
       descriptor of the kind *)
  | FdOpaque _ => None
    (* NOT AN -EBADF: [readv_spec] declines [State.FdOpaque] in its
       [None] branch, through [State.fd_is_opaque], because [None] here means
       [vfs_readv]'s -EBADF and that is the kernel's answer only for the
       O_PATH object ([do_readv]'s [CLASS(fd_pos, f)], fs/read_write.c,
       v6.18.44; identical at v6.18.46); a /proc/sys file and an eventfd are open for reading *)
  end.

(** Linux keeps eight iovecs on the syscall stack ([UIO_FASTIOV],
    include/uapi/linux/uio.h).  For counts 9 through [IOV_MAX],
    lib/iov_iter.c [iovec_from_user] (v6.18.46) allocates a temporary
    array with [kmalloc_array] and may fail with [-ENOMEM] before it
    reads a descriptor or applies [access_ok].  The model does not
    represent this allocation choice, so it fails closed on the whole
    heap-backed range.  The fd and [FMODE_READ] gates in [readv_spec]
    run first; counts above [IOV_MAX] are [-EINVAL] without allocating,
    and a count of one never allocates at all. *)
Definition UIO_FASTIOV : Z := 8%Z.

Definition readv_heap_iovecb (iovcnt : word) : bool :=
  let n := bv_unsigned (iovcnt32 iovcnt) in
  ((UIO_FASTIOV <? n)%Z && (n <=? IOV_MAX)%Z)%bool.

(** A readv destination-shape gap: the model cannot describe this
    delivery, so it DECLINES.  The input-side analogue of
    [writev_buf_gap].  [Checks.Sys.Fs.ReadWrite.check_readv_gap] is the
    single checker-side counterpart of this and of [readv_heap_gap]. *)
Definition readv_buf_gap : Sys SyscallEffect := unmodeled.

(** Fail closed on the heap-backed count band ([readv_heap_iovecb]).  A
    DISTINCT NAME for a distinct reason to decline — the optional
    [-ENOMEM] of the temporary iovec allocation, not an unrepresentable
    buffer shape — but deliberately not a second copy of the policy: one
    body, so the two cannot drift apart the way the [MAX_RW_COUNT] cap
    did between readv and writev. *)
Definition readv_heap_gap : Sys SyscallEffect := readv_buf_gap.

(** A PARTIALLY WRITABLE DESTINATION IS UNDESCRIBED, for every fd kind
    that copies, and this is why.

    The copy is one primitive everywhere — lib/iov_iter.c [_copy_to_iter]
    stepping [copy_to_user_iter] over each segment — and a fault inside
    it is reported by arch/riscv/lib/uaccess.S
    [fallback_scalar_usercopy_sum_enabled]'s fixup (v6.18.46), which
    returns the bytes NOT copied as [end - a0]; the caller's count is the
    length minus that.  Below 71 bytes that routine stores byte by byte
    and the count is exact.  From 71 bytes it aligns the destination and
    runs either an eight-word block loop, which advances [a0] by 64
    bytes only after all eight stores, or a shift-copy loop advancing
    per word, then a byte tail; a fault inside the block loop therefore
    counts up to 56 bytes FEWER than were stored.  Which loop runs
    depends on the alignment of the destination against the source
    folio, and with CONFIG_RISCV_ISA_V (defconfig) a copy of 768 bytes
    or more may take [__asm_vector_usercopy] instead, whose fixup is
    element-exact.  So the count a fault produces is the writable prefix
    rounded down by the copy routine's phase, and the bytes between the
    count and the fault ARE in user memory, uncounted.  The model knows
    the fault address; it does not model the copy routine.

    What the fd kinds then do with that count:

    - a regular file (mm/shmem.c [shmem_file_read_iter] for tmpfs,
      mm/filemap.c [filemap_read] for ext4 and cached 9p) sets
      [-EFAULT] and stops when a folio copies short, and returns the
      bytes already read if there are any, else the error; the position
      advances by the reported count;
    - a pipe (fs/pipe.c [anon_pipe_read]) copies pipe buffer by pipe
      buffer with [copy_page_to_iter]; a short copy of the FIRST buffer
      is [-EFAULT] with the copied bytes stored and NOTHING consumed
      ([buf->offset] moves only after a full copy), a short copy of a
      later buffer returns the whole buffers before it.  How the queued
      bytes are split into buffers is the writers' history, which the
      model does not carry;
    - a TCP socket (net/ipv4/tcp.c [tcp_recvmsg_locked],
      net/core/datagram.c [__skb_datagram_iter]) is the pipe's shape at
      skb granularity: a short copy is [-EFAULT] if nothing was counted
      yet and the count so far otherwise, with the iterator reverted but
      the stored bytes left in place.

    So the rule, with [w] the writable prefix of the capped scatter and
    [need] the bytes the source can supply now — [min] of the aggregate
    and the remaining stream, which for a pipe or socket the model can
    only bound by its whole remaining script:

    - [w = 0]: [-EFAULT], nothing stored, nothing consumed, the offset
      unchanged.  Exact for every kind above.
    - [w >= need]: the delivery — exactly [need] for a file, any
      nonempty prefix for a pipe or socket.
    - [0 < w < need]: [readv_buf_gap].  Fail closed.

    Zero-length entries take no part in [w]: [iterate_iovec] skips a
    segment with no bytes left ([if (likely(part))]) and never touches
    its base, which [State.scatter_iovecs] mirrors. *)

(** Execute readv once [State.import_iovecs] has accepted the descriptor
    array.  [iovs0] is the array as imported; the aggregate cap is
    applied here ([State.cap_iovecs]), and everything below reads the
    CAPPED vector — entries past [MAX_RW_COUNT] survive at length zero,
    so they still occupy an index but can carry no bytes.

    A zero aggregate returns 0 before anything else ([vfs_readv]:
    [tot_len = iov_iter_count(&iter)], then a jump past the operation
    when it is zero), which is why an all-zero vector on a directory is
    0 and not [-EISDIR].  The partial-destination rule above is applied
    on every kind that copies; the directory never copies. *)
Definition readv_imported (fd : word) (r : ReadableFd)
    (iovs0 : list (word * word)) (i : SyscallInput) (m : Model)
    : Sys SyscallEffect :=
  let iovs := cap_iovecs iovs0 in
  let total := iovs_total iovs in
  if Z.eqb total 0 then ret_only (Z_to_bv 64 0)
  else
  match r with
  | RdChannel ch =>
      match m_stdin m with
      | IEof => ret_only (Z_to_bv 64 0)   (* sticky EOF: the stream never refills *)
      | ICons _ _ =>
          match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
          | None => err_ret EFAULT        (* first delivered byte unwritable *)
          | Some _ =>
              match scatter_iovecs (in_wmem i) iovs
                      (fst (stream_take_z (m_stdin m) total)) with
              | None => readv_buf_gap     (* writable prefix, unwritable tail: the
                                             pipe's answer depends on its buffer
                                             boundaries and on the copy loop's
                                             phase — fail closed *)
              | Some _ =>
                  (* A channel read may deliver any nonempty prefix of the
                     stream that fits: the length is the environment's
                     choice, and the ledger is forced to the canonical
                     in-order scatter of exactly those bytes. *)
                  bs <- choose (fun bs : list byte =>
                                  (1 <= Z.of_nat (length bs))%Z /\
                                  (Z.of_nat (length bs) <= total)%Z /\
                                  fst (stream_take (m_stdin m) (length bs)) = bs /\
                                  scatter_iovecs (in_wmem i) iovs bs <> None) ;;
                  match scatter_iovecs (in_wmem i) iovs bs with
                  | Some writes =>
                      set_stdin (snd (stream_take (m_stdin m) (length bs))) ;;  (* consume exactly what was delivered *)
                      emit (map (ReadEv ch) bs) ;;                              (* one event per byte *)
                      pure (mkEffect (len_word bs) writes [])
                  | None => choose (fun _ => False)
                      (* unreachable: the chosen [bs] scatters by construction.
                         Coq requires the arm; it admits no outcome. *)
                  end
              end
          end
      end
  | RdSocket sk =>
      match sk with
      | SkConnected peer ch rx =>
          match rx with
          | NFin => ret_only (Z_to_bv 64 0)   (* the peer's FIN: 0, and sticky *)
          | NRst =>
              set_fds (fd_insert (m_fds m) fd (FdSocket (SkReset peer ch))) ;;
              err_ret ECONNRESET                (* delivered once, then end-of-stream *)
          | NTimedOut =>
              set_fds (fd_insert (m_fds m) fd (FdSocket (SkReset peer ch))) ;;
              err_ret ETIMEDOUT
          | NCons _ _ =>
              match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
              | None => err_ret EFAULT        (* first delivered byte unwritable *)
              | Some _ =>
                  match scatter_iovecs (in_wmem i) iovs
                          (fst (net_take_z rx total)) with
                  | None => readv_buf_gap     (* writable prefix, unwritable tail:
                                                 the skb boundaries decide — fail
                                                 closed *)
                  | Some _ =>
                      (* Exactly the channel rule, on the connection's script:
                         the length is the environment's choice and the ledger
                         is forced to the canonical in-order scatter of those
                         bytes.  Nothing about the vector reaches the protocol
                         — tcp_recvmsg_locked sees only an [iov_iter] and its
                         total — so a socket readv and a socket read of the
                         same total admit the same lengths. *)
                      bs <- choose (fun bs : list byte =>
                                      (1 <= Z.of_nat (length bs))%Z /\
                                      (Z.of_nat (length bs) <= total)%Z /\
                                      fst (net_take rx (length bs)) = bs /\
                                      scatter_iovecs (in_wmem i) iovs bs <> None) ;;
                      match scatter_iovecs (in_wmem i) iovs bs with
                      | Some writes =>
                          set_fds (fd_insert (m_fds m) fd
                                     (FdSocket (SkConnected peer ch
                                                  (snd (net_take rx (length bs)))))) ;;
                          emit (map (ReadEv ch) bs) ;;   (* one event per byte, on the
                                                            connection's channel *)
                          pure (mkEffect (len_word bs) writes [])
                      | None => choose (fun _ => False)
                          (* unreachable: the chosen [bs] scatters by construction.
                             Coq requires the arm; it admits no outcome. *)
                      end
                  end
              end
          end
      | SkReset _ _ => ret_only (Z_to_bv 64 0)  (* error already delivered: reads as EOF *)
      | _ => err_ret ENOTCONN                 (* fresh, bound or listening *)
      end
  | RdPipe _ => readv_buf_gap
      (* VECTORED PIPE READS ARE UNMODELED, the mirror of [writev_spec]'s
         pipe arm and for the same reason.  The -EBADF ordering above is
         still exact: [readable_fd] answers the write end before this
         point.  Fail closed through [readv_buf_gap] *)
  | RdDevNull => ret_only (Z_to_bv 64 0)
      (* [read_iter_null] (drivers/char/mem.c, v6.18.46) is [return 0],
         reached through [do_iter_readv_writev] because [null_fops]
         carries [.read_iter]; no destination byte is touched and
         [f_pos], pinned at 0, cannot make [rw_verify_area] fire.  The
         zero-aggregate case above answered the same 0 first *)
  | RdUrandom => readv_buf_gap
      (* FAIL-CLOSED, though derivable.  A real answer is
         [urandom_read_iter] (drivers/char/random.c, v6.18.46) over the
         imported iterator: the capped aggregate's worth of bytes off
         the front of [State.m_urandom], scattered across the segments
         the way the channel arm's [scatter_iovecs] scatters stdin's,
         with the same partial-destination decline.  Not written, so the
         vectored read declines through [readv_buf_gap] rather than
         guess at a scatter; [read_urandom] is the scalar answer *)
  | RdDir => err_ret EISDIR
      (* fs/libfs.c [generic_read_dir] (v6.18.46), reached through
         fs/read_write.c [do_loop_readv_writev] because a directory's
         operations carry [.read] and no [.read_iter]: [-EISDIR] on the
         first entry, the destination never consulted.  Everything the
         destination could have said was said at import: an entry
         outside the address space is [-EFAULT] there, an entry inside
         it imports whether or not it is mapped.  PREMISE: the
         directory's position is 0, so [rw_verify_area]'s position test
         above cannot fire — [FdDir] tracks no position because nothing
         modeled moves it ([lseek_spec] declines on a directory, and
         [Readdir.getdents64_spec] declines every listing and answers the
         rest with [filldir64]'s -EINVAL, which leaves [f_pos] where it
         found it); give either an arm
         and this -EISDIR needs the test in front of it, since ext4's
         [ext4_dx_readdir] parks an exhausted listing at
         [EXT4_HTREE_EOF_64BIT] = LLONG_MAX *)
  | RdFile p off =>
      match fs_lookup (m_fs m) p with
      | None => readv_buf_gap      (* an FdFile always points into the fs; see openat *)
      | Some data =>
          if rw_pos_einvalb off total then err_ret EINVAL
              (* [rw_verify_area], ahead of the read operation *)
          else
          (* files are deterministic: exactly the bytes at the offset *)
          let bs := file_read data off (Z_to_bv 64 total) in
          match scatter_iovecs (in_wmem i) iovs bs with
          | Some writes =>
              if addr_is_error_b (len_word bs) then readv_buf_gap
                  (* a read never returns an error-encoded count.  The
                     aggregate cap puts [length bs] under [MAX_RW_COUNT],
                     so this cannot fire; it is what lets the checker
                     conclude the return is not an errno without a
                     separate bound lemma. *)
              else
              set_fds (fd_insert (m_fds m) fd
                         (FdFile p (off + len_word bs))) ;;   (* advance by the delivery *)
              pure (mkEffect (len_word bs) writes [])
          | None =>
              match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
              | None => err_ret EFAULT                 (* nothing deliverable: -EFAULT *)
              | Some _ => readv_buf_gap                (* writable prefix, unwritable tail *)
              end
          end
      end
  | RdFileRW p off =>
      (* THE [RdFile] ARM ABOVE, WORD FOR WORD, with the entry written
         back under the O_RDWR kind -- the reason [ReadableFd] carries
         two file constructors at all. *)
      match fs_lookup (m_fs m) p with
      | None => readv_buf_gap      (* an FdFileRW always points into the fs; see openat *)
      | Some data =>
          if rw_pos_einvalb off total then err_ret EINVAL
              (* [rw_verify_area], ahead of the read operation *)
          else
          (* files are deterministic: exactly the bytes at the offset *)
          let bs := file_read data off (Z_to_bv 64 total) in
          match scatter_iovecs (in_wmem i) iovs bs with
          | Some writes =>
              if addr_is_error_b (len_word bs) then readv_buf_gap
                  (* a read never returns an error-encoded count.  The
                     aggregate cap puts [length bs] under [MAX_RW_COUNT],
                     so this cannot fire; it is what lets the checker
                     conclude the return is not an errno without a
                     separate bound lemma. *)
              else
              set_fds (fd_insert (m_fds m) fd
                         (FdFileRW p (off + len_word bs))) ;;   (* advance by the delivery *)
              pure (mkEffect (len_word bs) writes [])
          | None =>
              match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
              | None => err_ret EFAULT                 (* nothing deliverable: -EFAULT *)
              | Some _ => readv_buf_gap                (* writable prefix, unwritable tail *)
              end
          end
      end
  end.

(** [readv fd iov iovcnt]: scatter the bytes a [read] of the same total
    would deliver across the imported destination vectors, in order.

    DELIVERY.  The vectors are filled in index order, each to its own
    [iov_len], with zero-length entries skipped entirely and producing no
    ledger entry ([State.scatter_iovecs]).  So a readv's trace equals the
    trace of the equivalent [read] -- byte-level events erase the
    chunking -- and the write ledger is CANONICAL: for a given delivered
    byte string there is exactly one admissible ledger, which is what
    lets a check reject a split, shifted or padded one.

    NONDETERMINISM.  A channel readv may deliver any NONEMPTY prefix of
    the stream up to the aggregate capacity; which one is the
    environment's choice, and the model admits them all.  A file readv is
    DETERMINISTIC: exactly the bytes at the offset, and the offset
    advances by the delivery.

    STICKY EOF.  Once the stream is [IEof] a channel readv returns 0 and
    consumes nothing, on that call and every later one -- the input is an
    explicit stream and nothing refills it.

    [-EFAULT].  Three of them, in the kernel's order: an unreadable
    descriptor array or descriptor, then an entry whose range leaves the
    user address space ([State.access_okb], zero-length entries
    included), both from the import and before any byte moves; then, on
    the kinds that copy, a first DELIVERED byte that cannot be written.
    A zero-length entry with an unmapped but in-range base is simply
    skipped.

    ORDER, all from [do_readv], [vfs_readv] and [__import_iovec]: fd
    existence, then read mode, then the count band, then descriptor
    readability, negative lengths and [access_ok], then the aggregate
    cap, a zero aggregate, the position test, and finally the read
    operation.  The count is judged on its low 32 bits ([iovcnt32]) and
    counts 9 through 1024 are declined before a descriptor byte is read
    ([readv_heap_iovecb]). *)
Definition readv_spec (fd iov iovcnt : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                (* fd not open: real -EBADF, not a modeling gap *)
  | Some e =>
      match readable_fd e with
      | None =>
          if fd_is_opaque e then unmodeled   (* see [readable_fd]'s [FdOpaque] arm *)
          else err_ret EBADF                 (* FMODE_READ, ahead of the import *)
          (* EVERY OTHER [None] IS A REAL -EBADF, including the pipe end
             that reaches it.  [readable_fd] hands the read end a
             [RdPipe] ([create_pipe_files] opens it O_RDONLY), so the
             only pipe end left in this arm is the WRITE end, which is
             O_WRONLY and whose -EBADF is the kernel's own answer rather
             than a modeling gap *)
      | Some r =>
          if readv_heap_iovecb iovcnt then readv_heap_gap
          else
            record_copyins
              (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
            | ImpFault => err_ret EFAULT   (* unreadable descriptor, or a failed access_ok *)
            | ImpInval => err_ret EINVAL   (* count over IOV_MAX, or a negative iov_len *)
            | ImpOk iovs0 => readv_imported fd r iovs0 i m
            end)
      end
  end.

(** The whence-selected origin: 0, the fd's current offset, or the file
    size.  [None] for a whence the model does not interpret — which,
    once [lseek_spec] has rejected everything past [SEEK_MAX], means
    exactly SEEK_DATA (3) and SEEK_HOLE (4): real filesystems answer
    those (with a filesystem-dependent notion of what a hole is), so
    they are unmodeled here rather than -EINVAL. *)
(** [len] is the recorded file's length, which presumes the path names a
    regular file with a length at all: on a character device
    [null_lseek] pins the offset at 0 for every whence, where this
    repositions. *)
Definition lseek_base (whence : word) (cur len : word) : option word :=
  if Z.eqb (bv_unsigned whence) SEEK_SET then Some (Z_to_bv 64 0)
  else if Z.eqb (bv_unsigned whence) SEEK_CUR then Some cur
  else if Z.eqb (bv_unsigned whence) SEEK_END then Some len
  else None.

(** Resolve the destination offset: [base] plus the SIGNED 64-bit
    displacement [off] ([bv_signed], the two's-complement reading).
    [None] when the resulting offset would be negative (Linux: -EINVAL)
    or exceed LLONG_MAX (Linux: -EOVERFLOW; the model folds both into
    -EINVAL — an offset at 2^63 is unreachable through the modeled file
    system anyway).  The sum is exact in [Z], so no wrap can occur. *)
Definition lseek_dest (base off : word) : option word :=
  let d := (bv_unsigned base + bv_signed off)%Z in
  if ((0 <=? d) && (d <? 2 ^ 63))%Z then Some (Z_to_bv 64 d) else None.

(** [lseek fd offset whence].  Real repositioning of the fd's file
    offset — the same offset read and write advance — with
    SEEK_SET/SEEK_CUR/SEEK_END semantics; returns (and records) the new
    offset.  Offsets beyond end-of-file are legal, as on Linux: a later
    read there reports end-of-file (returns 0), and a later nonempty
    write zero-fills the gap (sparse-file semantics; see
    [Fs.file_write]).
    A negative or unrepresentable result is a real -EINVAL
    ([lseek_dest]).  Channels are unseekable streams: -ESPIPE, as for a
    pipe.  Nonexistent fd: -EBADF.  [fd] and [whence] both arrive
    already truncated to 32 bits (see [Syscall.fd32] and [Syscall.whence32]).

    THE ARGUMENT CHECKS ARE ORDERED AS THE KERNEL ORDERS THEM
    ([ksys_lseek], fs/read_write.c): the fd is resolved first (-EBADF),
    THEN [whence <= SEEK_MAX] is tested (-EINVAL), and only then does
    the answer depend on what the fd names.  So [lseek(pipe, 0, 42)] is
    -EINVAL, not -ESPIPE, and [lseek(<closed fd>, 0, 42)] is -EBADF, not
    -EINVAL.

    Directory fds: real lseek on a directory fd SUCCEEDS (getdents64
    positioning), but [FdDir] tracks no offset, so the model cannot
    judge the call — [unmodeled], fail closed, NOT an errno return.  A
    whence past [SEEK_MAX] is still -EINVAL there, as on Linux.

    A zero-LENGTH write at an offset past end-of-file (which only lseek
    can produce) leaves the file untouched, as on Linux; [Fs.file_write]
    zero-extends only for a nonempty write. *)
Definition lseek_spec (fd off whence : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* fd not open: real -EBADF, not a modeling gap *)
  | Some e =>
      if (SEEK_MAX <? bv_unsigned whence)%Z then
        (if fd_is_opaque e then unmodeled else err_ret EINVAL)
        (* FAIL-CLOSED ON THE OPAQUE KINDS, AHEAD OF THE -EINVAL:
           [ksys_lseek] resolves [CLASS(fd_pos, f)] before it reads
           [whence], so an O_PATH file is -EBADF for every whence; the
           eventfd and /proc/sys objects take the -EINVAL, and an
           [ONsFile]'s answer depends on its object of unknown type
           (fs/read_write.c, read at v6.18.44; identical at v6.18.46);
           the split is not written *)
        (* whence past SEEK_HOLE: real -EINVAL, and the kernel answers it
           BEFORE the fd's kind is consulted — so this precedes -ESPIPE *)
      else
      match e with
      | FdChannel _ => err_ret ESPIPE            (* channels are unseekable streams *)
      | FdSocket _ => err_ret ESPIPE            (* A SOCKET HAS NO OFFSET, EVER.  net/socket.c's
                                                    [socket_file_ops] carries no [.llseek], so
                                                    fs/file_table.c [alloc_file] never sets
                                                    FMODE_LSEEK (and sock_alloc_file's
                                                    [stream_open] clears it again), and
                                                    fs/read_write.c [vfs_llseek] answers -ESPIPE
                                                    for any file lacking that mode.  The -EINVAL
                                                    above still wins: ksys_lseek tests
                                                    [whence <= SEEK_MAX] BEFORE calling
                                                    vfs_llseek, so [lseek(sockfd, 0, 99)] is
                                                    -EINVAL, not -ESPIPE *)
      | FdPipe _ _ => err_ret ESPIPE             (* a real pipe, and the reason channels answer this.
                                                    The deciding test is [FMODE_LSEEK], not a null
                                                    [.llseek] read directly: [vfs_llseek]
                                                    (fs/read_write.c:385-390, v6.18.46) returns
                                                    -ESPIPE when the bit is absent (:387-388),
                                                    and [file_init_path] (fs/file_table.c:356,
                                                    v6.18.46) sets it only for a table that
                                                    supplies the method ([if (fop->llseek)],
                                                    :364-365).  An anonymous pipe misses it
                                                    TWICE.  First, the file-scope initializer
                                                    [static const struct file_operations
                                                    pipeanon_fops] in fs/pipe.c -- the table
                                                    [create_pipe_files] installs on both ends --
                                                    has no [.llseek] line at all.  Second,
                                                    [create_pipe_files] then runs [stream_open]
                                                    (fs/open.c) on both ends, and [stream_open]
                                                    CLEARS [FMODE_LSEEK] outright.  Linux
                                                    v6.18.46, commit 1f99e9ab748f.
                                                    Spelling the bit out matters because the
                                                    table half is the one whose SPELLING has
                                                    moved: older kernels wrote
                                                    [.llseek = no_llseek] here, and [no_llseek]
                                                    was [NULL] rather than a method, so "the
                                                    table supplies no llseek" reads the same
                                                    either way *)
      | FdDevNull _ _ => ret_only (Z_to_bv 64 0)   (* [null_lseek] (drivers/char/mem.c, v6.18.46) is
                                                    [return file->f_pos = 0] for EVERY whence and
                                                    offset — SEEK_DATA and SEEK_HOLE included, since
                                                    [vfs_llseek] dispatches to it once FMODE_LSEEK is
                                                    set, which [do_dentry_open] does for a table
                                                    that has an [.llseek].  Nothing to record: the
                                                    position it pins is the one the entry already
                                                    has none of *)
      | FdUrandom => ret_only (Z_to_bv 64 0)       (* [noop_llseek] (fs/read_write.c, v6.18.46), the
                                                    [.llseek] of [urandom_fops], is [return
                                                    file->f_pos] for EVERY whence and offset, and
                                                    [f_pos] is 0 on this kind: [urandom_read_iter]
                                                    never touches [kiocb.ki_pos], so [new_sync_read]
                                                    writes back the 0 it started from, [pread64]
                                                    reads through its own position, and no other
                                                    modeled arm moves it.  A dup'd or inherited
                                                    descriptor shares the same 0.  FMODE_LSEEK is
                                                    set because the table has an [.llseek], so
                                                    [vfs_llseek] dispatches rather than -ESPIPE *)
      | FdDir => unmodeled                           (* real lseek on a directory fd succeeds, but [FdDir]
                                                    tracks no offset, so the model cannot judge the
                                                    call: unmodeled, fail closed *)
      | FdFile p cur =>
          match fs_lookup (m_fs m) p with
          | None => unmodeled   (* an FdFile always points into the fs; see openat *)
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => unmodeled                    (* SEEK_DATA/SEEK_HOLE: real filesystems answer
                                                    these, with a filesystem-dependent notion of a
                                                    hole — unmodeled, fail closed *)
              | Some base =>
                  match lseek_dest base off with
                  | None => err_ret EINVAL       (* negative/unrepresentable result: real -EINVAL *)
                  | Some r =>
                      set_fds (fd_insert (m_fds m) fd (FdFile p r)) ;;  (* record the new offset *)
                      ret_only r
                  end
              end
          end
      | FdFileRW p cur =>
          (* NOR ON O_RDWR, and this arm is where "the two directions
             share one [f_pos]" becomes observable: the position an
             [lseek] sets here is the one the next read AND the next
             write both start from ([read_spec] and [write_spec]'s
             [FdFileRW] arms).  [generic_file_llseek] reads
             [file->f_pos] and the file's size and nothing else
             (fs/read_write.c, Linux v6.18.46). *)
          match fs_lookup (m_fs m) p with
          | None => unmodeled   (* an FdFileRW always points into the fs; see openat *)
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => unmodeled                    (* SEEK_DATA/SEEK_HOLE: see above *)
              | Some base =>
                  match lseek_dest base off with
                  | None => err_ret EINVAL       (* negative/unrepresentable result: real -EINVAL *)
                  | Some r =>
                      set_fds (fd_insert (m_fds m) fd (FdFileRW p r)) ;;  (* record the new offset *)
                      ret_only r
                  end
              end
          end
      | FdFileW p cur =>
          (* lseek does not depend on the access mode: a write-only file fd
             repositions exactly like a read-only one *)
          match fs_lookup (m_fs m) p with
          | None => unmodeled   (* an FdFileW always points into the fs; see openat *)
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => unmodeled                    (* SEEK_DATA/SEEK_HOLE: see above *)
              | Some base =>
                  match lseek_dest base off with
                  | None => err_ret EINVAL       (* negative/unrepresentable result: real -EINVAL *)
                  | Some r =>
                      set_fds (fd_insert (m_fds m) fd (FdFileW p r)) ;;  (* record the new offset *)
                      ret_only r
                  end
              end
          end
      | FdFileA p cur =>
          (* NOR ON THE APPEND FLAG.  [ksys_lseek] reaches
             [generic_file_llseek], which moves [f_pos] out of
             [file->f_pos] and the file's size alone; nothing on that
             path reads O_APPEND, and [do_dentry_open] never clears it
             either (fs/read_write.c, fs/open.c, Linux v6.18.46).  So an
             append fd repositions and REPORTS exactly like the
             write-only fd above -- what O_APPEND changes is where the
             next WRITE lands, and [write_spec]'s [FdFileA] arm is where
             that is recorded.  Answering here rather than declining is
             what makes the position observable at all, and so is what
             puts [File.dup_modeled_entry]'s [FdFileA] arm on the
             declining side. *)
          match fs_lookup (m_fs m) p with
          | None => unmodeled   (* an FdFileA always points into the fs; see openat *)
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => unmodeled                    (* SEEK_DATA/SEEK_HOLE: see above *)
              | Some base =>
                  match lseek_dest base off with
                  | None => err_ret EINVAL       (* negative/unrepresentable result: real -EINVAL *)
                  | Some r =>
                      set_fds (fd_insert (m_fds m) fd (FdFileA p r)) ;;  (* record the new offset *)
                      ret_only r
                  end
              end
          end
      | FdOpaque _ => unmodeled
          (* FAIL-CLOSED: an O_PATH file is [ksys_lseek]'s -EBADF for every
             whence; an eventfd's [eventfd_fops] has [.llseek = noop_llseek]
             and a /proc/sys file's [proc_sys_file_operations] has
             [.llseek = default_llseek] over a size the model does not hold
             (fs/read_write.c [ksys_lseek], fs/eventfd.c [eventfd_fops],
             fs/proc/proc_sysctl.c [proc_sys_file_operations]: read at
             v6.18.44; identical at v6.18.46); an [ONsFile]'s object is of
             unknown type.  None of the four answers is written. *)
      end
  end.
