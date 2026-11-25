(** * LinuxProcessSem.Sys.Fs.Ioctl — ioctl (29)

    This file answers to Linux [fs/ioctl.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

    Ported from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** A request no file that is not a terminal implements, and so one
    every fd this model can produce answers -ENOTTY.

    SCOPE.  The supported kernels, v6.16 to v6.18.46 (SCOPE.md).  This
    header was first read over mainline v5.15 through v6.14; v5.15 is
    where the claim first holds for every far end an [FdChannel] could
    name (see SOCKETS below).  v6.15 changed [vfs_ioctl]'s RETURN TYPE
    ([long] to [int]); at v6.18.46 it is also [static] and no longer
    exported.  Its body at v6.16, v6.17 and v6.18.46 is the one quoted
    below, and [do_vfs_ioctl] and [file_ioctl] (fs/ioctl.c) have the same
    arms at all three, none of them a terminal request.

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

    So every request of [tty_only_request] falls to [vfs_ioctl],
    byte-identical across the window:

      int error = -ENOTTY;
      if (!filp->f_op->unlocked_ioctl)
              goto out;
      error = filp->f_op->unlocked_ioctl(filp, cmd, arg);
      if (error == -ENOIOCTLCMD)
              error = -ENOTTY;

    What matters is not where these requests ARE implemented but that no
    fd this model can produce reaches a handler that claims them.  A
    regular file of tmpfs or ramfs, the file systems of the configuration
    of record whose regular files hold bytes (SCOPE.md), has no
    [unlocked_ioctl] ([shmem_file_operations] in mm/shmem.c,
    [ramfs_file_operations] in fs/ramfs/file-mmu.c) and takes the first
    branch, as does any other file with no [unlocked_ioctl]; a pipe's
    [pipe_ioctl] (fs/pipe.c) returns -ENOIOCTLCMD, which the code above
    maps to -ENOTTY.  The handlers that
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
    where the claim first holds; v6.16, v6.17 and v6.18.46 keep the gate
    in [sock_do_ioctl] (net/socket.c).

    LSM.  [security_file_ioctl] runs before either half and takes [cmd].
    The configuration of record builds no LSM (SCOPE.md), so it is the
    stub of include/linux/security.h that answers 0 and no policy
    answers first; an SELinux one, on a kernel that built it, would
    return -EACCES for a request outside the domain's [allow ... ioctl]
    set.

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
    environment, which SCOPE.md's "Assumptions that the model does not
    check" states for fds 0, 1 and 2 with the far ends a launch may put
    there.

    OUT-OF-TREE MEASUREMENT (not a checked fact; nothing in this
    repository re-derives it).  Corpus: the first eight requests below,
    without the five musl termios requests after them, issued
    on a regular file, a directory, both ends of a pipe, a unix stream
    socket and a unix datagram socket, over tmpfs, overlayfs, procfs and
    devtmpfs.  Kernel: Linux 7.0.14 aarch64 (past the
    scope above, so this corroborates rather than establishes).  Method:
    a native C program issuing each request with a 4096-byte argument
    and reporting errno.  Result: -ENOTTY everywhere, and -EBADF on a
    descriptor that is not open.  One exception, over virtiofs:
    TIOCSPTLCK was -EPERM there.  overlayfs and virtiofs are file
    systems the configuration of record does not build (SCOPE.md), so
    those rows bear on no supported kernel.

    WHERE THIS STOPS.  The arm assumes the fd's file system answers an
    unimplemented request itself, and every file system of the
    configuration of record that holds the model's files and folders
    does: tmpfs and ramfs install no [unlocked_ioctl] on a regular file
    or a folder.  FUSE, whose [fuse_do_ioctl] (fs/fuse/ioctl.c) forwards
    the request to a userspace server, is not built (no
    [CONFIG_FUSE_FS], SCOPE.md), and neither is virtiofs, which runs on
    it.  [Fs.v]'s interpreted file system has one kind of file and it
    is an ordinary one. *)
Definition tty_only_request (req : word) : bool :=
  bv_eqb req TCGETS     || bv_eqb req TCSETS    || bv_eqb req TIOCSCTTY ||
  bv_eqb req TIOCGWINSZ || bv_eqb req TIOCSWINSZ || bv_eqb req TIOCNOTTY ||
  bv_eqb req TIOCGPTN   || bv_eqb req TIOCSPTLCK ||
  (* musl's [tcsetattr] (TCSADRAIN, TCSAFLUSH), [tcdrain], [tcflush] and
     [tcgetpgrp].  Read at v6.18.46 like the eight: [do_vfs_ioctl]
     (fs/ioctl.c:492-580) names none of them, the tmpfs and ramfs file
     and folder tables and [null_fops] have no [unlocked_ioctl],
     [pipe_ioctl] (fs/pipe.c:619-656) knows FIONREAD and the watch-queue
     requests only, and on a socket [sock_ioctl]'s own cases are SIOC and
     FIO requests of type 0x89 (net/socket.c:1282-1380, its FIOGETOWN and
     SIOCGPGRP are 0x8903 and 0x8904, not TIOCGPGRP), [unix_ioctl],
     [tcp_ioctl] and [udp_ioctl] know SIOCINQ, SIOCOUTQ and their kin,
     and [sock_do_ioctl] answers -ENOTTY for type 0x54
     (net/socket.c:1264-1265) *)
  bv_eqb req TCSETSW    || bv_eqb req TCSETSF   || bv_eqb req TCSBRK ||
  bv_eqb req TCFLSH     || bv_eqb req TIOCGPGRP.

(** THE INTERFACE NAME [dev_ioctl] LOOKS UP IS "lo", read off the 40
    bytes [ifr] that [get_user_ifreq] copied in.  [dev_ioctl]
    (net/core/dev_ioctl.c, Linux v6.18.46) first forces
    [ifr_name[IFNAMSIZ-1] = 0], then cuts the name at its first ':'
    ([strchr], then [*colon = 0]) -- the alias syntax "lo:1" -- and
    [dev_get_by_name_rcu] compares the resulting NUL-terminated string.
    So the name looked up is "lo" exactly when byte 0 is 'l' (0x6c),
    byte 1 is 'o' (0x6f), and byte 2 ends the string: a NUL, or the ':'
    the cut turns into one.  Nothing past byte 2 is read; byte 15 is
    the only one [dev_ioctl] could have changed, and index 2 is not it. *)
Definition ifreq_names_lo (ifr : list byte) : bool :=
  match ifr with
  | b0 :: b1 :: b2 :: _ =>
      (Z.eqb (bv_unsigned b0) 108 && Z.eqb (bv_unsigned b1) 111
       && (Z.eqb (bv_unsigned b2) 0 || Z.eqb (bv_unsigned b2) 58))%bool
  | _ => false
  end.

(** The 40 bytes [put_user_ifreq] copies back after a SIOCGIFINDEX that
    found its device: the caller's own bytes but two edits [dev_ioctl]
    leaves in the kernel copy.  Byte 15 is 0 ([ifr_name[IFNAMSIZ-1] =
    0] is never undone; a ':' cut IS undone, by [*colon = ':'] before
    the return).  Bytes 16 to 19 are [ifr_ifindex], the [int] at the
    start of the [ifr_ifru] union, set by [dev_ifsioc_locked] to the
    device's index: [idx], little-endian.  Bytes 20 to 39, the rest of
    the union, go back as they came in. *)
Definition ifreq_with_index (ifr : list byte) (idx : Z) : list byte :=
  firstn 15 ifr ++ [Z_to_bv 8 0] ++ word_le4 (Z_to_bv 64 idx) ++ skipn 20 ifr.

(** [ioctl(fd, SIOCGIFINDEX, argp)] on an unconnected datagram socket
    ([State.FdDgram]).  The path, Linux v6.18.46:

    - [sock_ioctl] (net/socket.c) matches none of its own cases on
      0x8933 (it is outside the SIOCDEVPRIVATE and wireless ranges and
      none of the switch's labels) and takes [sock_do_ioctl], which
      asks the protocol first.  AF_UNIX's [unix_ioctl]
      (net/unix/af_unix.c) knows SIOCOUTQ, SIOCINQ, SIOCUNIXFILE and
      SIOCATMARK and answers the rest -ENOIOCTLCMD.  AF_INET6's
      [inet6_ioctl] (net/ipv6/af_inet6.c) knows the routing and address
      requests, and its default hands the rest to [sk_ioctl]
      (net/core/sock.c), whose [sock_ioctl_out] asks [udp_ioctl]
      (net/ipv4/udp.c, [udpv6_prot]'s [.ioctl]), which knows SIOCOUTQ
      and SIOCINQ and answers -ENOIOCTLCMD.  So both families fall to
      [is_socket_ioctl_cmd] (include/linux/netdevice.h), which admits
      0x8933 ([_IOC_TYPE] 0x89 = SOCK_IOC_TYPE).
    - [get_user_ifreq] (net/socket.c) is one [copy_from_user] of the
      whole 40-byte [struct ifreq]: if any byte cannot be read, -EFAULT,
      with nothing changed and nothing written.  ([in_compat_syscall()]
      is false for a native riscv64 call.)
    - [dev_ioctl] (net/core/dev_ioctl.c) cuts the name as
      [ifreq_names_lo] says, calls [dev_load] -- which loads nothing for
      a device that exists -- and [dev_ifsioc_locked], which looks the
      name up in the caller's network namespace: -ENODEV for no such
      device, else [ifr_ifindex = dev->ifindex] and 0.
    - On 0, [put_user_ifreq] copies the 40 bytes back
      ([ifreq_with_index]); a destination that takes none of them is
      -EFAULT with nothing written, and the call is otherwise 0.  A
      destination that takes some and not all declines: [copy_to_user]
      would leave a prefix behind, as everywhere a copy can stop part
      way.

    THE NAME "lo" IS THE ONLY ONE ANSWERED, and only through an
    ENVIRONMENT ASSUMPTION: THE NETWORK NAMESPACE'S LOOPBACK DEVICE IS
    NAMED "lo".  Given it, "lo" names the loopback -- interface names
    are unique within a namespace, alternative names included -- and the
    loopback's index is [LOOPBACK_IFINDEX], 1: [loopback_net_init]
    (drivers/net/loopback.c) creates it under that name in every
    namespace and stops the kernel ([BUG_ON], :222) if the index is not
    1 (include/net/flow.h:25).  The assumption is needed because the
    device can be RENAMED after creation, and another device can then
    take the name; SCOPE.md lists it among the assumptions the model
    does not check.  Every other name declines: which interfaces exist
    is the environment's, so neither an index nor -ENODEV can be
    asserted for it. *)
Definition siocgifindex_spec (argp : word) (i : SyscallInput) : Sys SyscallEffect :=
  match copy_bytes_map (in_mem i) argp IFREQ_SIZE with
  | None => err_ret EFAULT                     (* [get_user_ifreq]: nothing read, nothing changed *)
  | Some ifr =>
      record_copyins [(argp, Z.to_nat IFREQ_SIZE)]
        (if negb (ifreq_names_lo ifr) then unmodeled
           (* any other name: the interface table is the environment's *)
         else
         match read_bytes_map (in_wmem i) argp (Z_to_bv 64 IFREQ_SIZE) with
         | Some _ =>
             pure (mkEffect (Z_to_bv 64 0)
                     [(argp, ifreq_with_index ifr LOOPBACK_IFINDEX)] [])
         | None =>
             match read_bytes_map (in_wmem i) argp (Z_to_bv 64 1) with
             | None => err_ret EFAULT          (* [put_user_ifreq]: nothing lands *)
             | Some _ => unmodeled             (* lands a prefix: fail closed *)
             end
         end)
  end.

(** [ioctl fd req ...]: modeled for the terminal-only requests of
    [tty_only_request], every one of them answered with -ENOTTY — the
    model's channels and files are never terminals — but on
    /dev/urandom, whose driver answers them -EINVAL.  The answer is a
    constant because the kernel's is: a request no file implements is
    refused the same way whatever the file is.  One more request is
    modeled on one kind: SIOCGIFINDEX on an unconnected datagram socket
    ([State.FdDgram]), for the name "lo" only ([siocgifindex_spec]).
    Any other request on an open fd is unmodeled: [unmodeled] (fail
    closed).

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
      - every request that writes its result through the third argument,
        but SIOCGIFINDEX on a datagram socket.  The terminal requests
        qualify because -ENOTTY writes nothing; SIOCGIFINDEX qualifies
        because its write-back is the caller's own 40 bytes with one
        known index in them, which [siocgifindex_spec] reads off the
        third argument ([in_arg i 2], the full [unsigned long]).

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
  | Some (FdChannel _)
  (* A CHANNEL: every far end SCOPE.md lets fds 0, 1 and 2 have answers
     these requests -ENOTTY, so a pipe's write end and an O_RDWR socket
     agree here.  A pipe end through [pipe_ioctl]'s default arm
     (fs/pipe.c:653-654) and [vfs_ioctl]'s rewrite; a socket through
     [sock_ioctl]'s default arm (net/socket.c:1375-1376) into
     [sock_do_ioctl], where [inet_ioctl] (net/ipv4/af_inet.c:1000-1005)
     reaches [tcp_ioctl]'s -ENOIOCTLCMD (net/ipv4/tcp.c:682-683) and
     [unix_ioctl] its own (net/unix/af_unix.c:3380-3381), and
     [is_socket_ioctl_cmd] turns either into -ENOTTY
     (net/socket.c:1261-1265), Linux v6.18.46 *)
  | Some (FdFile _ _) | Some (FdFileW _ _)
  | Some (FdFileA _ _) | Some (FdFileRW _ _) | Some (FdDir _)
  | Some (FdSocket _)
  (* A STREAM-PAIR END IS A SOCKET FILE TOO, and reaches the same
     [sock_ioctl] default arm: [sock_do_ioctl] calls [unix_ioctl]
     (net/unix/af_unix.c, v6.18.46), whose switch knows SIOCOUTQ,
     SIOCINQ, SIOCUNIXFILE and SIOCATMARK -- none of them in
     [tty_only_request] -- and answers the rest -ENOIOCTLCMD, which
     [is_socket_ioctl_cmd] then turns into -ENOTTY exactly as for TCP *)
  | Some (FdStream _ _ _)
  (* AN EVENTFD TAKES THE SAME ANSWER by [vfs_ioctl]'s first branch, as
     /dev/null does below: [eventfd_fops] (fs/eventfd.c, v6.18.46) has no
     [.unlocked_ioctl], so [error = -ENOTTY] stands.  [do_vfs_ioctl]
     (fs/ioctl.c) claims none of [tty_only_request], and its default arm hands a
     request to [file_ioctl] only for [S_ISREG] inodes that are not
     [IS_ANON_FILE] -- and [alloc_anon_inode] (fs/libfs.c) gives the
     shared anonymous inode no type bits at all *)
  | Some (FdEventfd _)
  (* A PIPE END TAKES THE SAME ANSWER, and this is the one fd kind for
     which the header's argument was already written out: [pipe_ioctl]
     (fs/pipe.c:619) answers -ENOIOCTLCMD from its default arm (:653-654),
     which [vfs_ioctl] maps to -ENOTTY.  Re-checked at v6.18.46 rather
     than inherited: none of
     the requests in [tty_only_request] is FIONREAD or an
     IOC_WATCH_QUEUE command, so all of them take that default arm; and
     none of them appears in [do_vfs_ioctl]'s switch (fs/ioctl.c), so
     the fd-generic half does not claim them first -- its FIONREAD arm,
     the one case that could reach a pipe, is not among them.  This
     arm is pattern-conformance, not a new claim: it is the same
     -ENOTTY the four other open-fd kinds get, for the same reason the
     header gives, and every request outside [tty_only_request] stays
     [unmodeled] here as everywhere else. *)
  | Some (FdPipe _ _)
  (* THE NULL DEVICE TAKES THE SAME ANSWER, and it is the one open-fd
     kind that reaches it through [vfs_ioctl]'s FIRST branch rather
     than through -ENOIOCTLCMD: [null_fops] (drivers/char/mem.c,
     v6.18.46) has no [.unlocked_ioctl] at all, so [vfs_ioctl]
     (fs/ioctl.c) takes its [goto out] with the initialiser
     [error = -ENOTTY] never overwritten.  What has to be checked
     before that is the fd-generic half, and it does not claim these
     requests: none of [tty_only_request] appears in
     [do_vfs_ioctl]'s switch, and the null device's inode is a
     character device rather than [S_ISREG], so the default arm does
     not hand them to [file_ioctl] either — all of them fall out at
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
     new claim: the same -ENOTTY for the same requests, resting
     on the same premise about the image that the rest of the kind
     rests on (the node at that path is the null device, so the table
     installed is [null_fops]). *)
  | Some (FdDevNull _ _) =>
      if tty_only_request req then err_ret ENOTTY else unmodeled
  | Some (FdUrandom _ _) =>
      if tty_only_request req then err_ret EINVAL else unmodeled
      (* THE TERMINAL REQUESTS ARE -EINVAL HERE, NOT -ENOTTY.  Unlike
         /dev/null this table HAS an [.unlocked_ioctl]: [urandom_fops]
         (drivers/char/random.c:1572-1581, Linux v6.18.46) installs
         [random_ioctl] at :1575.  [do_vfs_ioctl] (fs/ioctl.c:492-580)
         names no request of [tty_only_request] and the inode is a
         character device, not [S_ISREG], so it answers -ENOIOCTLCMD, and
         on that answer the syscall body (fs/ioctl.c:595-597) hands the
         request to [vfs_ioctl] (fs/ioctl.c:44-56), which calls the
         table's [unlocked_ioctl] (:51).  The switch of [random_ioctl]
         (drivers/char/random.c:1492-1553) names only the RND* requests,
         and its default arm answers -EINVAL (:1550-1551), which
         [vfs_ioctl] passes through: it rewrites -ENOIOCTLCMD alone
         (:52-53).  No memory is read or written.
         musl's [__fdopen] issues TIOCGWINSZ on a stream opened for
         writing, so [fopen("/dev/urandom", "w")] reaches this.
         EVERY OTHER REQUEST STAYS DECLINED: RNDGETENTCNT answers the
         pool's entropy count, which the model does not carry;
         RNDADDTOENTCNT, RNDADDENTROPY and RNDRESEEDCRNG test
         CAP_SYS_ADMIN and change the pool ([random_ioctl],
         drivers/char/random.c:1503-1536 and :1543-1549); RNDZAPENTCNT
         and RNDCLEARPOOL change nothing ("No longer has any effect",
         drivers/char/random.c:1537-1542) but answer -EPERM without
         CAP_SYS_ADMIN and 0 with it, and the model carries no
         credentials to tell the two apart; and [do_vfs_ioctl]'s own
         requests (FIONBIO, FIOCLEX and their kin) change state this
         model does not carry *)
  | Some (FdDgram _) =>
      if tty_only_request req then err_ret ENOTTY
        (* the socket answer above, reached through [unix_ioctl] (AF_UNIX)
           or [inet6_ioctl] -> [sk_ioctl] -> [udp_ioctl] (AF_INET6), each
           -ENOIOCTLCMD for all of them, which [is_socket_ioctl_cmd] turns
           into -ENOTTY: see [siocgifindex_spec] for the path *)
      else if bv_eqb req SIOCGIFINDEX then
        (i <- input ;; siocgifindex_spec (in_arg i 2) i)
      else unmodeled
  end.
