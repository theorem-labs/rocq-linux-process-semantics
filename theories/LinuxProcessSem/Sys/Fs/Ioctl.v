(** * LinuxProcessSem.Sys.Fs.Ioctl — ioctl (29)

    This file answers to Linux [fs/ioctl.c]: it holds what the kernel
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
  Syscall Uapi.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** A request no file that is not a terminal implements, and so one
    every fd this model can produce answers -ENOTTY.

    SCOPE.  Mainline Linux v5.15 through v6.14, riscv64.  The floor is
    where the claim first holds for every far end an [FdChannel] could
    name (see SOCKETS below); the cap is the last tag read.  v6.15
    changes [vfs_ioctl]'s RETURN TYPE ([long] to [int]) and nothing
    else -- same body, still exported -- so what stops at v6.14 is the
    reading, not the behaviour.

    WHY THE ANSWER IS A CONSTANT.  [SYSCALL_DEFINE3(ioctl, ...)]
    resolves the fd, calls [security_file_ioctl], then tries the request
    two ways and gives up:

      error = do_vfs_ioctl(fd_file(f), fd, cmd, arg);
      if (error == -ENOIOCTLCMD)
              error = vfs_ioctl(fd_file(f), cmd, arg);

    [do_vfs_ioctl] is the fd-generic half: a fixed switch, whose
    [S_ISREG] default arm runs a nested second switch, [file_ioctl]
    (FIBMAP and the preallocate commands).  Both fall out at
    -ENOIOCTLCMD.  Membership is an explicit LIST, not a magic-letter
    test -- six of the outer arms are 0x54xx (FIONCLEX 0x5450, FIOCLEX
    0x5451, FIOASYNC 0x5452, FIOQSIZE 0x5460, FIONBIO 0x5421, FIONREAD
    0x541B) and the rest spread over magic 0, 'X', 'f', 0x94 and 0x15 --
    so nothing about a request's number predicts whether it lands here.
    The list grew by exactly two inside the window, FS_IOC_GETFSUUID and
    FS_IOC_GETFSSYSFSPATH, which v5.15 lacks and v6.14 has; no terminal
    request was ever in either switch, at either end.  This is also why
    FIONBIO is NOT -ENOTTY and is left unmodeled below: it is handled
    right here, for every file type.

    So all eight fall to [vfs_ioctl], byte-identical across the window:

      int error = -ENOTTY;
      if (!filp->f_op->unlocked_ioctl)
              goto out;
      error = filp->f_op->unlocked_ioctl(filp, cmd, arg);
      if (error == -ENOIOCTLCMD)
              error = -ENOTTY;

    What matters is not where these requests ARE implemented but that no
    fd this model can produce reaches a handler that claims them.  A
    regular file's ext4 [__ext4_ioctl] (fs/ext4/ioctl.c) returns -ENOTTY
    from its default arm; a pipe's [pipe_ioctl] (fs/pipe.c) returns
    -ENOIOCTLCMD, which the code above maps to -ENOTTY; a file with no
    [unlocked_ioctl] at all takes the first branch.  The handlers that
    DO claim them are scattered -- TIOCGWINSZ/TIOCSWINSZ in [tty_ioctl]
    (drivers/tty/tty_io.c), TIOCSCTTY/TIOCNOTTY in
    drivers/tty/tty_jobctrl.c, TCGETS/TCSETS in [tty_mode_ioctl]
    (drivers/tty/tty_ioctl.c) reached through the line discipline, and
    TIOCGPTN/TIOCSPTLCK in the pty master (drivers/tty/pty.c) -- and
    none of them answers -ENOTTY, which is exactly why the model must
    never hand one of these to a terminal.  That it does not is an
    ASSUMPTION rather than a theorem -- see below.

    SOCKETS.  Before v5.15 a socket was a counterexample: [sock_do_ioctl]
    (net/socket.c) fell through to an unconditional
    [copy_from_user(&ifr, argp, sizeof(struct ifreq))], so TCGETS on a
    socket was -EFAULT rather than -ENOTTY whenever the third argument
    was not 40 readable bytes.  v5.15 gates that on
    [is_socket_ioctl_cmd(cmd)] and returns -ENOTTY instead, which is
    where this scope's floor comes from.

    LSM.  [security_file_ioctl] runs before either half and takes [cmd],
    so a policy may answer first -- SELinux returns -EACCES for a
    request outside the domain's [allow ... ioctl] set.  The constant
    below is therefore a null-LSM claim.

    ASSUMPTION.  The model classifies ALL THREE standard descriptors --
    fds 0, 1 and 2 ([State.init_model]) -- as [FdChannel] without
    knowing whether the far end is a pipe, a terminal or a file, and
    this arm answers on any of them: [tty_only_request] is gated only on
    [fd_lookup] finding the fd, with no case on which one it is.  Each
    direction earns its agnosticism by WIDENING: on 1 and 2 through
    [ReadWrite.write_spec], which admits a short return, and on 0 through
    [ReadWrite.read_spec], which admits a short read or end-of-input.  Either way
    the widened outcome set covers every far end.  A single
    deterministic -ENOTTY cannot be earned the same way, because on a
    real terminal TCGETS SUCCEEDS.  For TIOCGWINSZ alone that would be inert:
    musl uses the answer only to pick a buffering mode, and byte-level
    trace events erase chunking.  It is NOT inert for TCGETS/TCSETS/
    TIOCSCTTY, which a program branches on.  So this arm assumes the
    run's standard descriptors are not terminals -- an obligation on the
    environment.

    OUT-OF-TREE MEASUREMENT (not a checked fact; nothing in this
    repository re-derives it).  Corpus: the eight requests below, issued
    on a regular file, a directory, both ends of a pipe, a unix stream
    socket and a unix datagram socket, over tmpfs, overlayfs, procfs and
    devtmpfs.  Kernel: Linux 7.0.14 aarch64 (past the
    scope above, so this corroborates rather than establishes).  Method:
    a native C program issuing each request with a 4096-byte argument
    and reporting errno.  Result: -ENOTTY everywhere, and -EBADF on a
    descriptor that is not open.  One exception, over virtiofs: see
    WHERE THIS STOPS.

    WHERE THIS STOPS.  The arm assumes the fd's filesystem answers an
    unimplemented request itself.  FUSE does not -- [fuse_do_ioctl]
    (fs/fuse/ioctl.c) forwards the request to the userspace server, so
    the answer is that server's to pick.  Over virtiofs, TIOCSPTLCK
    really is -EPERM.  That is an environment this model does not
    describe: [Fs.v]'s interpreted file system has one kind of file and
    it is an ordinary one.  It is left as an obligation on the
    environment rather than modeled, because narrowing the arm would mean
    dropping the one request [openpty] cannot do without. *)
Definition tty_only_request (req : word) : bool :=
  bv_eqb req TCGETS     || bv_eqb req TCSETS    || bv_eqb req TIOCSCTTY ||
  bv_eqb req TIOCGWINSZ || bv_eqb req TIOCSWINSZ || bv_eqb req TIOCNOTTY ||
  bv_eqb req TIOCGPTN   || bv_eqb req TIOCSPTLCK.

(** [ioctl fd req ...]: modeled for the terminal-only requests of
    [tty_only_request], every one of them answered with -ENOTTY — the
    model's channels and files are never terminals.  The answer is a
    constant because the kernel's is: a request no file implements is
    refused the same way whatever the file is.  Any other request on an
    open fd is unmodeled: [unmodeled] (fail closed).

    The open-fd arms are ENUMERATED rather than matched with a wildcard,
    and that is load-bearing.  "-ENOTTY on every open fd" is exact only
    while no [FdEntry] can be a terminal, which is a property of the REST
    of the model, not of this arm.  A wildcard would let a later
    constructor inherit -ENOTTY silently, and that has a cost: on a real
    terminal TCGETS SUCCEEDS, so the model would refuse what a real
    kernel does.  Enumerating makes the match
    non-exhaustive when a constructor is added, so the build stops and
    whoever adds it has to answer for [ioctl] deliberately.

    Deliberately still unmodeled, and each for its own reason:
      - FIONREAD/TIOCINQ succeeds, with an answer that depends on the
        fd's kind (bytes left in a file, bytes queued in a pipe);
      - FIONBIO succeeds and CHANGES the file's O_NONBLOCK state, and
        FIOCLEX/FIONCLEX succeed and change the descriptor's
        close-on-exec flag; this model carries neither piece of state;
      - every request that writes its result through the third argument.
        [ioctl_spec] does not take that argument, so the modeled ones
        are exactly those whose whole observable effect is the return
        value.  -ENOTTY writes nothing, which is why they qualify.

    The fd is resolved FIRST, exactly as the kernel does:
    [SYSCALL_DEFINE3(ioctl, ...)] opens with the fd fetch and returns
    -EBADF before it ever looks at the request, so a closed or
    never-opened fd is -EBADF whatever the request is.  (The fetch is
    respelled inside the scope above -- [f.file] becomes [fd_file(f)],
    and v6.13 replaces [fdget] with [CLASS(fd, f)] and [fd_empty]; a
    stable series past those backports carries the later spelling in an
    earlier v6.12.y.  Nothing here depends on which spelling it is.)  [fd] arrives
    already truncated to 32 bits (see [Syscall.fd32]) and [req] likewise (see
    [Syscall.cmd32]).

    A SOCKET GETS THE SAME ANSWER, and since this arm matches the entry
    opaquely it is spelled out rather than inherited.  The citations
    below are v6.12.
    TIOCGWINSZ (0x5413) on a socket reaches fs/ioctl.c [do_vfs_ioctl],
    matches none of its cases, and — a socket inode being S_ISSOCK, not
    S_ISREG — falls through to -ENOIOCTLCMD without ever reaching a tty
    handler.  net/socket.c [sock_ioctl] then takes its default arm into
    [sock_do_ioctl], which tries [inet_ioctl] -> [tcp_ioctl] (also
    -ENOIOCTLCMD) and finishes with
    [if (!is_socket_ioctl_cmd(cmd)) return -ENOTTY;].
    [_IOC_TYPE(0x5413)] is 0x54 while SOCK_IOC_TYPE is 0x89, so the
    answer is -ENOTTY.  It is decided from the REQUEST ALONE — no
    dependence on the socket's state — and no user memory is read or
    written on the way, so even a wild third argument is harmless.
    Every other socket ioctl (FIONREAD/SIOCINQ, SIOCGIFCONF, the
    SIOCDEVPRIVATE range) stays unmodeled, as on every other fd kind. *)
Definition ioctl_spec (fd req : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* fd not open: real -EBADF, before the request is examined *)
  | Some (FdChannel _) | Some (FdFile _ _) | Some (FdFileW _ _)
  | Some (FdFileA _ _) | Some (FdFileRW _ _) | Some FdDir
  | Some (FdSocket _)
  (* A STREAM-PAIR END IS A SOCKET FILE TOO, and reaches the same
     [sock_ioctl] default arm: [sock_do_ioctl] calls [unix_ioctl]
     (net/unix/af_unix.c, v6.18.46), whose switch knows SIOCOUTQ,
     SIOCINQ, SIOCUNIXFILE and SIOCATMARK -- none of them among the eight
     of [tty_only_request] -- and answers the rest -ENOIOCTLCMD, which
     [is_socket_ioctl_cmd] then turns into -ENOTTY exactly as for TCP *)
  | Some (FdStream _ _ _)
  (* A PIPE END TAKES THE SAME ANSWER, and this is the one fd kind for
     which the header's argument was already written out: [pipe_ioctl]
     (fs/pipe.c:619) answers -ENOIOCTLCMD from its default arm (:653-654),
     which [vfs_ioctl] maps to -ENOTTY.  Re-checked at v6.18.46 rather
     than inherited: none of
     the eight requests in [tty_only_request] is FIONREAD or an
     IOC_WATCH_QUEUE command, so all eight take that default arm; and
     none of them appears in [do_vfs_ioctl]'s switch (fs/ioctl.c), so
     the fd-generic half does not claim them first -- its FIONREAD arm,
     the one case that could reach a pipe, is not in the eight.  This
     arm is pattern-conformance, not a new claim: it is the same
     -ENOTTY the four other open-fd kinds get, for the same reason the
     header gives, and every request outside the eight stays
     [unmodeled] here as everywhere else. *)
  | Some (FdPipe _ _)
  (* THE NULL DEVICE TAKES THE SAME ANSWER, and it is the one open-fd
     kind that reaches it through [vfs_ioctl]'s FIRST branch rather
     than through -ENOIOCTLCMD: [null_fops] (drivers/char/mem.c,
     v6.18.46) has no [.unlocked_ioctl] at all, so [vfs_ioctl]
     (fs/ioctl.c) takes its [goto out] with the initialiser
     [error = -ENOTTY] never overwritten.  What has to be checked
     before that is the fd-generic half, and it does not claim these
     requests: none of the eight of [tty_only_request] appears in
     [do_vfs_ioctl]'s switch, and the null device's inode is a
     character device rather than [S_ISREG], so the default arm does
     not hand them to [file_ioctl] either — all eight fall out at
     -ENOIOCTLCMD and are answered by [vfs_ioctl].  The requests
     [do_vfs_ioctl] DOES claim on this kind (FIONBIO, FIOCLEX and
     their kin) change state this model does not carry and stay
     [unmodeled] here, as on every other kind.

     WHY THE ARM IS WORTH ANSWERING RATHER THAN DECLINING: musl's
     [__fdopen] issues TIOCGWINSZ on a freshly opened writable stream
     to pick a buffering mode, so if this kind declined on every
     request, a program that [fopen]s the null device for writing would
     leave the modeled surface one syscall after the open.

     This is pattern-conformance with the other open-fd kinds, not a
     new claim: the same -ENOTTY for the same eight requests, resting
     on the same premise about the image that the rest of the kind
     rests on (the node at that path is the null device, so the table
     installed is [null_fops]). *)
  | Some (FdDevNull _ _) =>
      if tty_only_request req then err_ret ENOTTY else unmodeled
  | Some FdUrandom => unmodeled
      (* FAIL-CLOSED, on every request.  Unlike /dev/null this table
         HAS an [.unlocked_ioctl]: [random_ioctl] (drivers/char/random.c,
         v6.18.46) answers RNDGETENTCNT with the pool's entropy count,
         the RNDADD* and RNDCLEARPOOL requests need CAP_SYS_ADMIN, and
         everything else is -EINVAL — none of which reaches the tty
         -ENOTTY, since [do_vfs_ioctl] hands the tty requests to the
         driver, which answers -EINVAL for them.  A real answer would
         be derived from that switch over a request word and a
         capability set; neither is written, so declined. *)
  end.
