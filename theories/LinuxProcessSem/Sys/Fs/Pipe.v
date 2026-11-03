(** * LinuxProcessSem.Sys.Fs.Pipe — pipe2 (59)

    Answers to Linux [fs/pipe.c]: this file holds the specs for the
    syscalls defined there, and no others.

    The pipe STATE — [State.PipeBuf], [State.pipe_write_room],
    [State.pipe_append], [State.pipe_consume], [State.pipe_end_live] —
    lives in [State.v] beside the rest of the model, because the fd-kind
    arms that read it are spread across [Fs/ReadWrite.v] (read, write,
    readv, writev, lseek), [Fs/Open.v] (close, ftruncate),
    [Fs/Sync.v] (fsync) and [Fs/Ioctl.v] (ioctl).  What is here is the
    one syscall that CREATES a pipe. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess Fs.File.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** The flag bits [__do_pipe_flags] accepts: its opening
    [if (flags & ~(O_CLOEXEC | O_NONBLOCK | O_DIRECT | O_NOTIFICATION_PIPE))]
    (fs/pipe.c:987-988, v6.18.46).  Everything else is a deterministic
    -EINVAL, raised BEFORE the pipe is made and before the user pointer is
    touched.  [O_NOTIFICATION_PIPE] is spelled [O_EXCL]
    (include/uapi/linux/watch_queue.h:9, v6.18.46). *)
Definition pipe2_flags_mask : Z :=
  (O_CLOEXEC + O_NONBLOCK + O_DIRECT + O_EXCL)%Z.

(** pipe2's injectable failures: environment conditions the model does
    not track.  [-EMFILE] at RLIMIT_NOFILE (and pipe2 needs TWO free
    descriptors, so it can hit it where an [openat] would not),
    [-ENFILE] at the system file limit — which is also where a failed
    [alloc_pipe_info] surfaces, since [get_pipe_inode] returns NULL for
    both (fs/pipe.c:886-898, v6.18.46) and [create_pipe_files] turns that
    one NULL into [-ENFILE] (:932-933) — and [-ENOMEM] out of growing the
    fd table.  Like
    [Open.openat_errnos], this alternative also keeps the spec receptive
    when no free fd exists. *)
Definition pipe2_errnos : list Z := [EMFILE; ENFILE; ENOMEM].

(** [pipe2 fildes flags]: make a pipe and write its two descriptors —
    read end first — through [fildes].  THE MODEL'S FIRST FD WHOSE
    CONTENTS COME FROM THE PROGRAM: everything else an fd names is
    supplied by the environment (a channel) or by the file system.

    Kernel source for everything below is fs/pipe.c at v6.18.46 (commit
    1f99e9ab748f): [SYSCALL_DEFINE2(pipe2)] at :1054, [do_pipe2] at
    :1032, [__do_pipe_flags] at :982, [create_pipe_files] at :926,
    [pipe_release] at :725, and the transfer pair [anon_pipe_read] at
    :269 and [anon_pipe_write] at :431.

    THE PAIR IS NAMED [anon_pipe_*] BECAUSE THAT IS WHAT EXISTS HERE, and
    the older names are a trap rather than a synonym: at v6.18.46
    [pipe_read] and [pipe_write] survive only inside three comments
    (:76, :1068, :1071), and the functions were split in two — an
    anonymous pair, [pipe_read]/[pipe_write]'s successors, and a FIFO
    pair [fifo_pipe_read] at :407 / [fifo_pipe_write] at :604 that wraps
    them with a timestamp update.  Which pair a descriptor gets is
    decided by its file-operations table: [pipefifo_fops] (:1246-1255)
    takes the FIFO pair, [pipeanon_fops] (:1257-1266) the anonymous one.
    [create_pipe_files] installs [pipeanon_fops] on both ends (:946,
    :957), so every claim in this file and in the pipe arms it points at
    is about [anon_pipe_read]/[anon_pipe_write], never the FIFO wrappers.

    ORDER, as [do_pipe2] has it:

    - FLAGS FIRST (:987-988), before anything else and before the user
      pointer is read: a bit outside [pipe2_flags_mask] is [-EINVAL], so
      [pipe2(unmapped, 1)] is [-EINVAL] and never [-EFAULT].  Of the four
      accepted bits the model interprets only their ABSENCE: [flags = 0]
      is the whole modeled surface (it is what a [pipe(2)] call becomes
      on riscv64, which has no [pipe] syscall — musl's src/unistd/pipe.c
      issues [pipe2(fd, 0)]), and any nonzero accepted combination is
      [unmodeled].  Each of the four would need something the model does
      not have: [O_CLOEXEC] an execve, [O_NONBLOCK] the [-EAGAIN]
      answers this spec's whole design declines, [O_DIRECT] packet mode
      (where a read DISCARDS the tail of a packet it did not take), and
      [O_NOTIFICATION_PIPE] a kernel built with CONFIG_WATCH_QUEUE —
      [create_pipe_files] calls [watch_queue_init] for that bit (:935-942)
      and the stub the option compiles out to returns [-ENOPKG]
      (include/linux/watch_queue.h:126-128, v6.18.46), so even the failure
      is configuration-dependent.
    - THEN THE DESCRIPTORS (:994-1006).  [__do_pipe_flags] takes the read
      end first and the write end second, each the lowest free number
      ([get_unused_fd_flags] -> [alloc_fd], scanning [open_fds] from 0),
      so [fd[0] < fd[1]] and the write end is allocated with the read end
      already reserved.
    - THEN THE COPY-OUT (:1040), and only then [fd_install] (:1047-1048).
      The eight bytes go out as ONE [copy_to_user] of [int fildes[2]], so
      the effect is one contiguous range, not two.  A failed copy is
      [-EFAULT] with NOTHING installed: [do_pipe2] [fput]s both files and
      [put_unused_fd]s both reservations (:1041-1045), so the call is
      atomic — the fd table is exactly as it was.  The model therefore
      answers [-EFAULT] and changes nothing.
      A PARTIALLY writable destination is [unmodeled] instead: the kernel
      copies a prefix before it faults, and how much depends on the
      architecture's uaccess loop, so the model will not say what is in
      those bytes.
    - ONE INVERSION OF THAT ORDER, named rather than assumed away.  The
      term tests the destination's writability BEFORE it allocates, so on
      the wholly-unwritable branch it offers [-EFAULT] beside the
      injected [pipe2_errnos].  Linux runs [__do_pipe_flags] first, so a
      task with fewer than two free descriptors answers [-EMFILE] and
      never attempts the copy — the model admits an answer that kernel
      would not give in that one state.  It is over-permissive, not
      unsound: [-EMFILE] is admitted there too, so no real trace is
      refused.  Reaching it needs RLIMIT_NOFILE exhausted AND an
      unwritable [fildes] in the same call, so it is recorded
      the way [openat] records the [-EMFILE] a real kernel can raise
      before path resolution rather than being restructured around.

    WHAT A PIPE COSTS THE THEOREM.  Nothing observable: pipe bytes are
    not events, and [State.event] gains no constructor, so two runs that
    differ only in what a pipe holds are equivalent exactly as before.
    What changes is coverage — programs that create and use a pipe move
    from [unmodeled] to modeled, and the parts that stay [unmodeled] are
    named where they arise: a read of an empty pipe with a live writer
    (it would block), a
    write needing a second ring slot (see [State.pipe_write_room]), a
    faulting source or a partially writable destination, and every
    vectored pipe transfer.  A source binary that reaches any of those
    fails [Equivalence.modeled], so the task is REJECTED rather than
    vacuously satisfied.

    A WRITE TO A PIPE WITH NO READER IS NOT ON THAT LIST ANY MORE.  It
    used to be, on the argument that SIGPIPE's default action ends the
    process and the model had no death that is not [exit].  It has one
    ([State.with_killed], [Run.sstep_killed]), so
    [Fs.ReadWrite.write_spec]'s pipe arm answers the call -- a death by
    signal 13, or -EPIPE where the launch mask blocks it -- and a
    program that closes a pipe's read end and writes is a program a
    proof can cover.

    WHY A PIPE IS THE FIRST FD KIND TO COST ANYTHING HERE.  Every fd kind
    before it either always has an answer (a channel, a file) or never
    transfers (a directory).  A pipe is the first whose answer can depend
    on what the OTHER end does next, and that is the whole of the gap
    above: each declined arm is a place where the model would have to
    know something about a peer it does not represent.

    WHAT WOULD CLOSE IT: a model of blocking, which means a notion of a
    call that has no answer until the other end acts; or at minimum a
    model of [O_NONBLOCK], whose
    [-EAGAIN] answers are a function of the pipe state alone, plus a way
    for a program to ASK for them.  There are two such ways and neither
    is available today: [pipe2]'s own [O_NONBLOCK] is inside the accepted
    mask but any nonzero flag word is [unmodeled] (above), and [fcntl]
    answers [F_SETFL] only where it provably changes nothing — the
    [F_SETFL] that would actually set [O_NONBLOCK] declines, and the
    [F_GETFL] that [setnonblocking] issues first declines ahead of it
    (see [Fs.Fcntl.fcntl_spec] and [Fs.Fcntl.setfl_noop_on]).

    That is a measured gap on a real target's common path, not a
    hypothetical.  dropbear 2026.94 sets its pipes non-blocking as a
    matter of course, through one helper: [setnonblocking]
    (src/dbutil.c), called on the parent-side ends of the three pipes
    [spawn_command] (src/dbutil.c) creates, and on BOTH ends of the
    signal self-pipe ([ses.signal_pipe], src/common-session.c).  dropbear
    uses no [pipe2] flags, no [socketpair], no [accept4] and no
    SOCK_NONBLOCK, so every non-blocking PIPE OR SOCKET it holds went
    through that helper after the fact (it does open a regular file
    O_NONBLOCK directly, in src/svr-authpubkey.c, which is not one) — which means the [F_GETFL] decline is
    what it stops at, before any pipe arm here is reached.

    [flags] arrives already truncated to 32 bits (see
    [Syscall.pipe_flags32]), because pipe2's flag word is an [int]. *)
Definition pipe2_spec (fildes flags : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags) pipe2_flags_mask) 0)
  then err_ret EINVAL          (* a bit outside the accepted mask: real -EINVAL, before
                                  the pipe is made and before [fildes] is touched *)
  else if negb (w_is0 flags) then unmodeled
                               (* an accepted but uninterpreted flag: fail closed *)
  else
  let id := pipe_new_id (m_pipes m) in
  match pipe_lookup (m_pipes m) id with
  | Some _ => unmodeled        (* the id-space wrapped: see [State.pipe_new_id].
                                  Unreachable, and fail closed rather than alias *)
  | None =>
      let injected := (e <- errno_from pipe2_errnos ;; err_ret e) in
      if negb (access_okb fildes 8) then alt injected (err_ret EFAULT)
      (* [copy_to_user] IS [access_ok] AND THEN THE COPY, and this is the
         [access_ok] half.  Without it nothing bounds [fildes] before the
         walk below: [State.read_bytes_map] advances with WRAPPING [bv]
         addition, so a [fildes] near 2^64 walks off the top and back in
         at 0, and if an [mp] backs both halves the walk answers [Some]
         and this spec returns SUCCESS — a pipe made and two descriptors
         installed — on a range Linux's [access_ok] refuses outright.
         [State.access_okb] sums in [Z] and so refuses it.

         Same shape and same repair as [Net.Socket.socketpair_dest_writable],
         whose comment carries the argument; do not re-derive it here.
         ONE DIFFERENCE, and it is what lets this arm answer where that
         one declines: [do_pipe2] copies both descriptors with a SINGLE
         [copy_to_user] of [int fildes[2]] (fs/pipe.c:1040, v6.18.46), so
         there is one [access_ok] over the whole 8 bytes rather than
         socketpair's two [put_user]s over 4 each.  A refused range
         therefore copies NOTHING — no partial write to rule out — and
         [-EFAULT] with the model unchanged is Linux's answer rather than
         a fail-closed stand-in.  [do_pipe2] then [fput]s both files and
         [put_unused_fd]s both reservations (:1041-1045), which is why
         nothing is installed. *)
      else match read_bytes_map (in_wmem i) fildes (Z_to_bv 64 8) with
      | Some _ =>
          alt injected
              (fdr <- lowest_fd (m_fds m) ;;         (* read end: the lowest free fd *)
               let fds1 := fd_insert (m_fds m) fdr (FdPipe id false) in
               fdw <- lowest_fd fds1 ;;              (* write end: the next lowest *)
               set_fds (fd_insert fds1 fdw (FdPipe id true)) ;;
               set_pipes (pipe_insert (m_pipes m) id ([], 0%Z)) ;;  (* an empty queue *)
               pure (mkEffect (Z_to_bv 64 0) [(fildes, pipe_fd_bytes fdr fdw)] []))
      | None =>
          match read_bytes_map (in_wmem i) fildes (Z_to_bv 64 1) with
          | None => alt injected (err_ret EFAULT)
              (* not one byte of the destination is writable: real -EFAULT,
                 with no pipe made and no descriptor installed *)
          | Some _ => unmodeled
              (* a writable prefix and an unwritable tail: [copy_to_user]
                 leaves an architecture-dependent number of bytes behind.
                 Fail closed *)
          end
      end
  end.
