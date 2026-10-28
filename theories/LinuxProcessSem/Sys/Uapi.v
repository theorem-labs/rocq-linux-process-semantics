(** * LinuxProcessSem.Sys.Uapi — the constants the userspace ABI fixes

    Every other file under [Sys/] answers to one kernel SOURCE file;
    this one answers to a kernel HEADER, [include/uapi/], and holds what
    the specs share rather than any one syscall's behaviour.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

Definition O_WRONLY  : Z := 1%Z.
(** O_RDWR has TWO readers, and they arrive at it from opposite ends.

    It is the access mode [Open.rdwr_open_word] admits, minting a
    [State.FdFileRW]; and, separately, it is the WHOLE of a socket's
    [f_flags].  net/socket.c [sock_alloc_file] builds the file with
    [alloc_file_pseudo(..., O_RDWR | (flags & O_NONBLOCK), &socket_file_ops)],
    so a socket created without SOCK_NONBLOCK has exactly this word and
    nothing else — no O_LARGEFILE, which the open SYSCALL ENTRY POINTS
    add with [force_o_largefile()] and which nothing on the socket
    creation path does.  [Fcntl.socket_f_flags] is that derivation, and
    it is a fact about how a SOCKET is created rather than about the
    constant, so the open arms below cannot disturb it. *)
Definition O_RDWR    : Z := 2%Z.
Definition O_CREAT   : Z := 64%Z.
Definition O_EXCL    : Z := 128%Z.
Definition O_TRUNC   : Z := 512%Z.
Definition O_CLOEXEC : Z := 524288%Z.
(** musl's syscall layer ORs O_LARGEFILE into EVERY open it issues
    (src/internal/syscall.h); it is meaningless on a 64-bit ABI, so it
    is accepted and ignored like O_CLOEXEC. *)
Definition O_LARGEFILE : Z := 32768%Z.

(** O_NONBLOCK: 2048.  riscv64 takes the asm-generic ABI
    (include/uapi/asm-generic/fcntl.h), where the value is unchanged
    from v4.9 through v6.17 and O_NDELAY is an alias of it throughout.
    riscv supplies no asm/fcntl.h of its own to override it — checked at
    v5.10 and v6.17, and only meaningful from v4.15, which is where
    arch/riscv first exists.  Accepted and IGNORED like
    O_CLOEXEC and O_LARGEFILE, but for a reason that is a property of
    this model's FILE SYSTEM rather than of the flag, so it is spelled
    out here and has to be re-checked whenever that file system grows.
    [Open.open_ignored_flags] is the mask that carries it.

    WHAT THE KERNEL DOES WITH IT.  It reaches [f_flags] and stays there.
    Plain openat masks its flag word with VALID_OPEN_FLAGS
    ([build_open_how], fs/open.c) and openat2 rejects anything outside
    that set instead ([build_open_flags]); O_NONBLOCK is in the set
    either way.  From v5.6, where openat2 split those two, the only bits
    [build_open_flags] strips are O_CLOEXEC and, on the older branches,
    the kernel-internal FMODE_NONOTIFY.  That is scoped to v5.6 and
    later on purpose: at v5.4 [build_open_flags] also does
    [flags &= VALID_OPEN_FLAGS] itself, and its O_PATH arm does
    [flags &= O_DIRECTORY | O_NOFOLLOW | O_PATH], which DOES drop
    O_NONBLOCK; v4.9 has no VALID_OPEN_FLAGS at all.  Then
    [do_dentry_open] clears O_CREAT, O_EXCL, O_NOCTTY and O_TRUNC from
    [f_flags] once the file's [->open] has run, and O_NONBLOCK is not in
    that list, so the description really does record it.  That clearing
    line is identical at v4.9, v5.10, v6.1, v6.6 and v6.17, and on
    stable 6.6.y and 6.1.y.

    WHY RECORDING IT COSTS THIS MODEL NOTHING.  Three ways a program
    could tell, all closed:

    - READ THE FLAG WORD BACK, which means fcntl(F_GETFL).  fcntl (25)
      is modeled and F_GETFL IS one of the commands it answers — but
      only on the fd kind whose flag word the model can derive, which is
      [State.FdSocket] ([Fcntl.getfl_f_flags]).  [Open.openat_spec] never
      mints one: the fd this bullet is about is an [FdFile], [FdFileW],
      [FdFileA], [FdFileRW], [FdDir], [FdDevNull] or [FdUrandom], and F_GETFL
      declines on every one of them FOR THE
      REASON THIS BULLET IS ABOUT — the ignored bit is part of the answer, so the
      read fails closed inside the spec rather than at the dispatch.
      The two facts moved together on purpose: [Fcntl.getfl_f_flags]
      enumerates its fd kinds, so recording O_NONBLOCK on an [FdEntry]
      is what would let the file kinds be answered, and it is the same
      change that would retire this bullet.

    - THE OPEN ITSELF ANSWERS -EAGAIN.  [do_dentry_open] calls
      [break_lease] with the UNSTRIPPED [f_flags], before the clearing
      line above, and [__break_lease] (fs/locks.c) answers -EWOULDBLOCK
      — which is EAGAIN — when [mode & O_NONBLOCK].  Unreachable here
      rather than merely unlikely: [break_lease] (include/linux/filelock.h)
      returns 0 outright unless the inode already carries a lease, a
      lease is taken with fcntl(F_SETLEASE), one of the commands
      [Fcntl.fcntl_spec] declines, and the model runs ONE process, so
      nothing else can hold one either.  Checked at v4.9, v5.10, v6.1,
      v6.6 and v6.17: the call precedes the clearing line and passes
      [f_flags] at all five, and the [list_empty] bail sits directly
      above the O_NONBLOCK test in [__break_lease].  The inode helper
      is spelled [locks_inode] up to v6.1 and [file_inode] from v6.6.

    - A TRANSFER ANSWERS -EAGAIN, which needs an object that could have
      blocked.  Every path [Open.openat_spec] resolves here is a regular
      file in the interpreted file system or one of the two directory
      references "." and ".." ([Fs.Open.path_is_dirref]) — never a pipe,
      a socket, a terminal or any
      other character device.  On a regular file every -EAGAIN in
      [generic_file_read_iter] and [filemap_get_pages] (mm/filemap.c) is
      conditioned on IOCB_NOWAIT, IOCB_NOIO or, from v6.17, IOCB_WAITQ;
      those bits come only from RWF_NOWAIT via [kiocb_set_rw_flags],
      which is defined in include/linux/fs.h — fs/read_write.c holds its
      call site and no definition — and which read(2) and write(2) never
      pass; and [iocb_flags] (include/linux/fs.h) maps only O_APPEND,
      O_DIRECT, O_DSYNC and __O_SYNC, not O_NONBLOCK.  That mapping has
      held from v4.19 through v6.17, mainline and stable alike.

      ONE EXCEPTION, ON BRANCHES BEFORE v5.15.  There a regular-file
      read(2)/write(2) COULD answer -EAGAIN from [f_flags] alone, nowhere
      near mm/filemap.c: [rw_verify_area] (fs/read_write.c) called
      [locks_mandatory_area] (then in fs/locks.c), which reads
      [filp->f_flags & O_NONBLOCK] directly and lets [posix_lock_inode]
      return -EAGAIN without FL_SLEEP.  It needed
      CONFIG_MANDATORY_FILE_LOCKING and an -o mand mount.  Mandatory
      locking was removed at v5.15: fs/locks.c defines [locks_mandatory_area]
      at v4.9, v4.19, v5.4, v5.10 and v5.14, and not at v5.15, v6.1, v6.17
      or v6.18.46.  So the paragraph above is a claim about
      v5.15 and later, not about every branch this file names elsewhere.

    THAT IS CONDITIONAL ON THE FILE SYSTEM KEEPING THAT SHAPE.  Should
    [Open.openat_spec] ever resolve a path to a FIFO, a socket or a
    character device, O_NONBLOCK stops being ignorable — on a FIFO it
    decides whether the open itself blocks or answers -ENXIO — and
    belongs back OUT of [Open.open_ignored_flags], not widened further.
    The same trigger governs O_NOCTTY's argument in
    [Open.modeled_open_flags]: 9p's [dotl_oflag_map] forwards BOTH flags
    to the server, so a file system growing past regular files and "."
    puts the two back in question together. *)
Definition O_NONBLOCK : Z := 2048%Z.

(** O_DIRECTORY: 0200000.  riscv64 takes the asm-generic ABI
    (include/uapi/asm-generic/fcntl.h, Linux v6.18.46) and supplies no
    asm/fcntl.h of its own to override the value.

    THE ONE OPEN FLAG THIS MODEL INTERPRETS BEYOND THE ACCESS MODE, and
    it cannot be ignored the way [Open.open_ignored_flags]'s three bits
    are: it changes which answers the call gives.  The bit does not stay
    in [f_flags] to be read back later.  [build_open_flags] (fs/open.c)
    turns it into the LOOKUP_DIRECTORY bit of the lookup flags, and
    [do_open] (fs/namei.c) then answers -ENOTDIR for a resolved dentry
    that [d_can_lookup] (include/linux/dcache.h) refuses.

    WHERE THAT TEST SITS is what makes the errno independent of what the
    name turned out to be: inside [do_open] (fs/namei.c), after the
    O_CREAT block and before [may_open] (fs/namei.c), which is itself
    before [vfs_open] (fs/open.c).  So a FIFO whose open would otherwise
    block for a peer, a device node whose file operations would run, and
    a plain file all answer -ENOTDIR without either of the two later
    steps being reached.  Linux v6.18.46. *)
Definition O_DIRECTORY : Z := 65536%Z.

Definition AT_FDCWD  : word := Z_to_bv 64 (-100).   (* -100 in two's complement *)

(** AT_FDCWD as it reaches openat's dirfd test, i.e. after the [int dfd]
    truncation the dispatcher applies ([Syscall.fd32]): the low 32 bits of -100.
    A program passes AT_FDCWD in a register sign-extended to 64 bits
    ([AT_FDCWD] itself), and the kernel then compares only the low half,
    so [openat(2^32 - 100, ...)] names the working directory too. *)
Definition AT_FDCWD32 : word := fd32 AT_FDCWD.

(** [(uid_t)-1], after the [Syscall.uid32] narrowing.  No process can
    hold it — [make_kuid] maps it to [INVALID_UID]
    (include/linux/uidgid.h) and [Run.valid_id] excludes it — so
    [setuid] and [setgid] reject it with -EINVAL, and [setresuid] and
    [setresgid] read it as "leave this id alone". *)
Definition ID_MINUS_ONE : word := Z_to_bv 64 4294967295.

(** AT_SYMLINK_NOFOLLOW, the flag that turns [stat] into [lstat]
    (include/uapi/linux/fcntl.h). *)
Definition AT_SYMLINK_NOFOLLOW : Z := 256%Z.

(** AT_EACCESS (0x200), the flag that asks [faccessat2] to answer with
    the EFFECTIVE ids rather than the real ones
    (include/uapi/linux/fcntl.h).  It is read once, by
    [access_need_override_creds], which returns false outright when it
    is set and so skips the [access_override_creds] that copies uid/gid
    over fsuid/fsgid (fs/open.c).  Under F_OK the choice is
    unobservable, which is what lets [Fs.Open.faccessat2_spec] answer
    with it set; [Fs.Open.faccessat2_spec] carries the argument. *)
Definition AT_EACCESS : Z := 512%Z.

(** AT_EMPTY_PATH (0x1000), the flag that makes [getname_flags] accept
    an empty pathname and resolve the dirfd itself
    (include/uapi/linux/fcntl.h).  [do_faccessat] turns it into
    LOOKUP_EMPTY (fs/open.c).  It is one of the three flags
    [faccessat2] accepts, so it is not an -EINVAL, and
    [Fs.Open.modeled_access_flags] declines it rather than guessing. *)
Definition AT_EMPTY_PATH : Z := 4096%Z.

(** [S_IRWXO] (0o7): the mask [do_faccessat] validates its [mode]
    against, and the reason the R_OK/W_OK/X_OK values are the low three
    bits.  Linux passes [mode] STRAIGHT THROUGH as a permission mask —
    [inode_permission(..., mode | MAY_ACCESS)] — which works only
    because R_OK, W_OK and X_OK have the same numeric values as
    MAY_READ, MAY_WRITE and MAY_EXEC (4/2/1, include/linux/fs.h).  A
    [mode] with any bit outside this mask is a deterministic -EINVAL,
    decided by the FIRST statement of [do_faccessat], before the flag
    word, before the creds and before the pathname is fetched — see
    [Fs.Open.faccessat_spec] (Linux include/uapi/linux/stat.h; the value
    is unchanged across every branch this file names). *)
Definition S_IRWXO : Z := 7%Z.

(** "." (the working directory), one of the two paths that name a
    directory without a lookup.  The other is [Fs.Namei.dotdot_path];
    [Fs.Open.path_is_dirref] is the pair, and its comment says why they
    get the same answers.  The interpreted fs has no directory
    structure, so no path OTHER than those two resolves to a directory.

    It sits here rather than with a syscall because more than one spec
    resolves it: [openat] opens it as a directory fd, [newfstatat]
    declines it for want of metadata, and no file under [Sys/] imports
    another. *)
Definition dot_path : path := [Z_to_bv 8 46].

(** "/dev/null", the one DEVICE path the model answers.  It sits here
    for the reason [dot_path] does: [Fs.Open.openat_devnull_spec] opens
    it, [Fs.Stat.fstat_devnull_spec] keys the descriptor's stat pin
    under it, and no file under [Sys/] imports the other.  The
    assumption the name rests on — the image's /dev/null is the null
    device, character major 1 minor 3 — is stated once, at the openat
    arm. *)
Definition devnull_path : path :=
  [Z_to_bv 8 47; Z_to_bv 8 100; Z_to_bv 8 101; Z_to_bv 8 118; Z_to_bv 8 47;
   Z_to_bv 8 110; Z_to_bv 8 117; Z_to_bv 8 108; Z_to_bv 8 108].

(** "/dev/urandom", the second device path the model answers, here for
    the reason [devnull_path] is: [Fs.Open.openat_urandom_spec] opens
    it and [Fs.Stat.fstat_urandom_spec] keys the descriptor's stat pin
    under it.  The assumption the name rests on — the image's
    /dev/urandom is the random device, character major 1 minor 9 — is
    stated once, at the openat arm. *)
Definition urandom_path : path :=
  [Z_to_bv 8 47; Z_to_bv 8 100; Z_to_bv 8 101; Z_to_bv 8 118; Z_to_bv 8 47;
   Z_to_bv 8 117; Z_to_bv 8 114; Z_to_bv 8 97; Z_to_bv 8 110; Z_to_bv 8 100;
   Z_to_bv 8 111; Z_to_bv 8 109].

(* =========================================================================
   Sockets: constants, argument decoding, and the trace channel
   ========================================================================= *)

(** Address families and socket types.  riscv64 has no [asm/socket.h] and
    no [asm/errno.h] of its own — arch/riscv/include/uapi/asm/Kbuild
    generates only unistd_32.h and unistd_64.h — so every constant here
    is the asm-generic one, at v6.12. *)
Definition AF_UNSPEC : Z := 0%Z.
Definition AF_INET   : Z := 2%Z.
Definition NPROTO    : Z := 46%Z.    (* = AF_MAX, include/linux/socket.h *)

Definition SOCK_STREAM    : Z := 1%Z.
Definition SOCK_DGRAM     : Z := 2%Z.
Definition SOCK_RAW       : Z := 3%Z.
Definition SOCK_SEQPACKET : Z := 5%Z.
Definition SOCK_DCCP      : Z := 6%Z.
Definition SOCK_PACKET    : Z := 10%Z.
Definition SOCK_MAX       : Z := 11%Z.  (* = SOCK_PACKET + 1, include/linux/net.h *)

(** [SOCK_TYPE_MASK] is 0xf: the low four bits of [type] are the socket
    type and the rest are flags (include/linux/net.h). *)
Definition SOCK_TYPE_MASK : Z := 15%Z.

(** [SOCK_CLOEXEC] and [SOCK_NONBLOCK] are ARCH-DEPENDENT in general —
    include/linux/net.h defines them only [#ifndef ARCH_HAS_SOCKET_TYPES],
    and mips/parisc/sparc/alpha override them.  riscv64 does not, and has
    no [asm/fcntl.h] either, so both fall through to the asm-generic
    O_ flags: [SOCK_CLOEXEC = O_CLOEXEC = 02000000] and
    [SOCK_NONBLOCK = O_NONBLOCK = 04000]. *)
Definition SOCK_CLOEXEC  : Z := 524288%Z.   (* 0o2000000 *)
Definition SOCK_NONBLOCK : Z := 2048%Z.     (* 0o4000 *)

(** [IPPROTO_MAX] is the TRAILING ENUMERATOR of the [IPPROTO_*] enum in
    include/uapi/linux/in.h, not a round number: the last named member is
    [IPPROTO_MPTCP = 262], so [IPPROTO_MAX] is 263.  It was 256 only up
    to v5.5; [IPPROTO_MPTCP] arrived in v5.6 and the value has been 263
    from v5.6 through v6.12.  Getting this wrong makes protocols 256-262
    answer -EINVAL where Linux answers -EPROTONOSUPPORT. *)
Definition IPPROTO_IP    : Z := 0%Z.
Definition IPPROTO_TCP   : Z := 6%Z.
Definition IPPROTO_SCTP  : Z := 132%Z.
Definition IPPROTO_MPTCP : Z := 262%Z.
Definition IPPROTO_MAX   : Z := 263%Z.

(** The three address lengths the socket calls test, in the order the
    kernel applies them:

    - [SOCKADDR_STORAGE_SIZE], the largest address [move_addr_to_kernel]
      will copy (include/uapi/linux/socket.h);
    - [SA_FAMILY_SIZE], [sizeof (sa_family_t)] — an [unsigned short] —
      which is [__inet_stream_connect]'s
      [addr_len < sizeof(uaddr->sa_family)] and so precedes its state
      switch;
    - [SOCKADDR_IN_SIZE], [sizeof (struct sockaddr_in)], the smallest
      [inet_bind_sk] accepts (include/uapi/linux/in.h) and the one
      [tcp_v4_connect] applies AFTER that switch.

    The middle one is connect's alone: bind reaches [inet_bind_sk]
    directly and never tests it.  A 4-byte address passes it and is then
    refused by the third. *)
Definition SOCKADDR_STORAGE_SIZE : Z := 128%Z.
Definition SA_FAMILY_SIZE        : Z := 2%Z.
Definition SOCKADDR_IN_SIZE      : Z := 16%Z.

(** The three option LEVELS an AF_INET/SOCK_STREAM socket has a handler
    for, and [shutdown]'s three directions.

    [SOL_SOCKET] is the odd one out: it is not an [IPPROTO_*] value but
    a constant of its own, from include/uapi/asm-generic/socket.h, which
    riscv64 uses unchanged.  The other two are [IPPROTO_IP] and
    [IPPROTO_TCP] above — SOL_IP and SOL_TCP are the SAME NUMBERS (0 and
    6) under other names (include/uapi/linux/in.h), so they are not
    defined again here; [Net.Socket.sock_level_known] names them as the
    levels.

    [SHUT_RD]/[SHUT_WR]/[SHUT_RDWR] are the members of the unnumbered
    [enum sock_shutdown_cmd] in include/linux/net.h, declared in that
    order with no initialisers, hence 0/1/2 (unchanged v6.1 through
    v6.19).  They are NOT the [RCV_SHUTDOWN]/[SEND_SHUTDOWN] bits of
    include/net/sock.h (1/2/3, with [SHUTDOWN_MASK = 3]) — [inet_shutdown]
    converts between the two with a [how++], and mistaking one set for
    the other is exactly how a model gets [shutdown]'s validation
    backwards. *)
Definition SOL_SOCKET : Z := 1%Z.
Definition SHUT_RD    : Z := 0%Z.
Definition SHUT_WR    : Z := 1%Z.
Definition SHUT_RDWR  : Z := 2%Z.

Definition SEEK_SET : Z := 0%Z.
Definition SEEK_CUR : Z := 1%Z.
Definition SEEK_END : Z := 2%Z.

(** The largest whence the kernel accepts at all: SEEK_HOLE.
    [ksys_lseek] tests [whence <= SEEK_MAX] AFTER resolving the fd and
    BEFORE [vfs_llseek], so the -EINVAL for a whence past it precedes
    every per-file-kind answer — including a pipe's -ESPIPE. *)
Definition SEEK_MAX : Z := 4%Z.

(** mmap prot/flags ABI constants (asm-generic, as on riscv64:
    include/uapi/asm-generic/mman-common.h, Linux v6.12). *)
Definition PROT_READ     : Z := 1%Z.
Definition PROT_WRITE    : Z := 2%Z.
Definition PROT_NONE     : Z := 0%Z.
(** mprotect's two stack-extension modifiers (include/uapi/asm-generic/
    mman-common.h).  They are not permissions: [do_mprotect_pkey] masks
    them out of [prot] before anything else looks at it, and only their
    conjunction is an argument error (see [Mprotect.mprotect_grows_conflict_b]). *)
Definition PROT_GROWSDOWN : Z := 0x01000000%Z.
Definition PROT_GROWSUP   : Z := 0x02000000%Z.
Definition MAP_PRIVATE   : Z := 2%Z.
Definition MAP_FIXED     : Z := 16%Z.             (* 0x10 *)
Definition MAP_ANONYMOUS : Z := 32%Z.             (* 0x20 *)
Definition MAP_HUGETLB   : Z := 262144%Z.         (* 0x40000 *)

(** MAP_FIXED_NOREPLACE, from the same arch-generic header riscv64
    inherits: [#define MAP_FIXED_NOREPLACE 0x100000]
    (include/uapi/asm-generic/mman-common.h:31, Linux v6.18.46).  It
    asks for placement at [addr] exactly, as MAP_FIXED does, but for a
    refusal rather than a replacement when any page of the range is
    already mapped; [do_mmap] (mm/mmap.c:361-362 and :410-412, Linux
    v6.18.46) is where both halves are decided, and
    [Mmap.mmap_noreplace_flags_b] carries the reading. *)
Definition MAP_FIXED_NOREPLACE : Z := 1048576%Z.  (* 0x100000 *)

(** mremap ABI flag bits (asm-generic, as on riscv64):
    [#define MREMAP_MAYMOVE 1] (include/uapi/linux/mman.h:9, v6.12).  The
    value is architecture-independent — riscv64 has no
    arch/riscv/include/uapi/asm/mman.h of its own, and neither
    include/uapi/asm-generic/mman.h nor mman-common.h redefines any
    MREMAP_ bit, so this uapi header is the sole definition. *)
Definition MREMAP_MAYMOVE : Z := 1%Z.

(** madvise advice values (asm-generic, as on riscv64):
    [#define MADV_DONTNEED 4] (include/uapi/asm-generic/mman-common.h:49,
    Linux v6.18.46).  Architecture-independent for the same reason the
    MREMAP_ bits are: riscv64 carries no uapi mman.h of its own, and the
    arch-generic mman.h defines no MADV_ value, so mman-common.h is the
    sole definition.  [Mm.Madvise.madvise_dontneed_b] is the one reader. *)
Definition MADV_DONTNEED : Z := 4%Z.

(** getrandom flag bits (include/uapi/linux/random.h). *)
Definition GRND_NONBLOCK : Z := 1%Z.
Definition GRND_RANDOM   : Z := 2%Z.

(** The ioctl requests that only a terminal implements.

    TIOCGWINSZ is the one a musl-linked binary reaches on its own:
    [__fdopen], [__stdout_write] and [isatty] probe the terminal window
    size to pick stdio's buffering mode.  The rest are what a program
    that expects to own a pty asks for — [tcgetattr] and
    [tcsetattr(TCSANOW)], the other half of the window-size pair, the
    controlling-terminal pair [TIOCSCTTY]/[TIOCNOTTY], and the two
    requests musl's [openpty] issues on /dev/ptmx.  Every one of them is
    on the path a Dropbear SSH server takes to hand a session a
    terminal.

    Values are the asm-generic ones, which riscv64 uses unchanged: riscv
    has no arch/riscv/include/uapi/asm/ioctls.h, and
    include/uapi/asm-generic/Kbuild lists ioctls.h as mandatory, so the
    port gets the generic header verbatim.  It is byte-identical for all
    eight across Linux v5.10-v6.14
    (include/uapi/asm-generic/ioctls.h). *)
Definition TCGETS      : word := Z_to_bv 64 21505.  (* 0x5401 *)
Definition TCSETS      : word := Z_to_bv 64 21506.  (* 0x5402 *)
Definition TIOCSCTTY   : word := Z_to_bv 64 21518.  (* 0x540E *)
Definition TIOCGWINSZ  : word := Z_to_bv 64 21523.  (* 0x5413 *)
Definition TIOCSWINSZ  : word := Z_to_bv 64 21524.  (* 0x5414 *)
Definition TIOCNOTTY   : word := Z_to_bv 64 21538.  (* 0x5422 *)
Definition TIOCGPTN    : word := Z_to_bv 64 2147767344.  (* 0x80045430 *)
Definition TIOCSPTLCK  : word := Z_to_bv 64 1074025521.  (* 0x40045431 *)

(** The fcntl commands, from [include/uapi/asm-generic/fcntl.h] — riscv64
    supplies no arch override, so these are its values.  [F_GETLK] and
    friends are the 64-bit spellings (5/6/7).  The 12/13/14 numbering is
    guarded by [#if __BITS_PER_LONG == 32 || defined(__KERNEL__)], so a
    64-bit kernel does define those names — but [do_fcntl] has no arm for
    them and they fall to its [default: break], returning the -EINVAL its
    [long err] was initialised to.  Declining them is therefore the same
    answer [Fcntl.fcntl_spec] gives every unrecognized command. *)
Definition F_GETFD  : word := Z_to_bv 64 1.
Definition F_SETFD  : word := Z_to_bv 64 2.
Definition F_GETFL  : word := Z_to_bv 64 3.
Definition F_SETFL  : word := Z_to_bv 64 4.

(** The [flock] operations, from that same header
    ([include/uapi/asm-generic/fcntl.h], Linux v6.18.46, commit
    1f99e9ab748f).  They are a MIXED word rather than an enumeration:
    LOCK_NB is a modifier OR'd into one of the other three, which is why
    [Fs.Locks.flock_base] strips it before comparing.

    LOCK_MAND is here because the kernel still READS it, not because
    anything sets it.  Mandatory flocks were removed, and what replaced
    them is not a rejection: [SYSCALL_DEFINE2(flock)] (fs/locks.c) opens
    with [if (cmd & LOCK_MAND) ... return 0;], so the bit turns the whole
    call into a no-op that succeeds — ahead of the operation check, ahead
    of the descriptor lookup, and so ahead of every errno flock has.  A
    model that only knew the three operations would answer -EINVAL there,
    which is the confident wrong answer this constant exists to prevent.

    The header keeps LOCK_READ, LOCK_WRITE and LOCK_RW beside it; they
    are not named here because nothing in fs/locks.c reads them at
    v6.18.46 — they reach [flock_translate_cmd]'s [switch] as ordinary
    unrecognized words and are -EINVAL, which is what the general rule
    already gives.  LOCK_MAND is the one whose bit is tested. *)
Definition LOCK_SH   : Z := 1%Z.
Definition LOCK_EX   : Z := 2%Z.
Definition LOCK_NB   : Z := 4%Z.
Definition LOCK_UN   : Z := 8%Z.
Definition LOCK_MAND : Z := 32%Z.

(** The file STATUS flag bits [setfl] (fs/fcntl.c) reads, from that same
    header.  [Fcntl.setfl_acted_on] is their union and carries the
    argument for why each one is in it — in particular why FASYNC, which
    [SETFL_MASK] omits, belongs there all the same.  O_NONBLOCK (04000)
    is one of them; it is defined above, with the open flags that ignore
    it, because it is one bit of one ABI and so one constant. *)
(** O_APPEND is read by TWO things, like O_DIRECT below:
    [Fcntl.setfl_acted_on], for which it is a status bit F_SETFL really
    changes, and [Open.append_create_flags], the open shape that mints a
    [State.FdFileA].  The two readings are coupled rather than
    independent — the append open is the one admitted shape whose
    residue meets [setfl_acted_on], and [Fcntl.setfl_noop_on]'s
    [FdFileA] arm is what keeps that sound. *)
Definition O_APPEND   : Z := 1024%Z.     (* 02000    *)
Definition FASYNC     : Z := 8192%Z.     (* 020000   *)
(** O_DIRECT is read by TWO things: [Fcntl.setfl_acted_on], for which it
    is a status bit F_SETFL really changes, and
    [Fs.Pipe.pipe2_flags_mask], which names it among the bits pipe2
    ACCEPTS -- what separates a real -EINVAL from a decline. *)
Definition O_DIRECT   : Z := 16384%Z.    (* 040000   *)
Definition O_NOATIME  : Z := 262144%Z.   (* 01000000 *)

(** [RLIMIT_CORE], the maximum size of a core dump (Linux v6.10-v6.15,
    include/uapi/asm-generic/resource.h, byte-identical at all six tags). *)
Definition RLIMIT_CORE : Z := 4%Z.

(** The POSIX clock ids the model interprets
    (include/uapi/linux/time.h, Linux v6.10-v6.15 and v6.18.46; the id
    block is byte-identical across all of them).  A clock id gets a name
    here when some spec TESTS it, not when it exists: the ids nothing
    tests are deliberately left unnamed, because a constant only a
    comment reads is dead weight.
    [Kernel.Time.PosixTimers.clock_gettime_spec] names the ids it
    declines in prose rather than as constants.

    [clock_gettime], [clock_getres], and [timerfd_create] each cover
    different sets of IDs.  Do not read this list as the clocks every
    spec supports. *)
Definition CLOCK_REALTIME : Z := 0%Z.
Definition CLOCK_MONOTONIC : Z := 1%Z.
Definition CLOCK_PROCESS_CPUTIME_ID : Z := 2%Z.
Definition CLOCK_THREAD_CPUTIME_ID : Z := 3%Z.
Definition CLOCK_MONOTONIC_RAW : Z := 4%Z.
Definition CLOCK_REALTIME_COARSE : Z := 5%Z.
Definition CLOCK_MONOTONIC_COARSE : Z := 6%Z.
Definition CLOCK_BOOTTIME : Z := 7%Z.
Definition CLOCK_REALTIME_ALARM : Z := 8%Z.
Definition CLOCK_BOOTTIME_ALARM : Z := 9%Z.
Definition CLOCK_SGI_CYCLE : Z := 10%Z.
Definition CLOCK_TAI : Z := 11%Z.

(** [TFD_CREATE_FLAGS], the only flag bits [timerfd_create] accepts.

    include/linux/timerfd.h (Linux v6.18.46) defines
    [TFD_SHARED_FCNTL_FLAGS (TFD_CLOEXEC | TFD_NONBLOCK)] and then
    [TFD_CREATE_FLAGS TFD_SHARED_FCNTL_FLAGS] -- the create mask IS the
    shared-fcntl mask, so one constant serves.  The two members are
    [O_CLOEXEC] and [O_NONBLOCK] themselves, which fs/timerfd.c asserts
    at build time rather than assuming: [SYSCALL_DEFINE2(timerfd_create)]
    opens with [BUILD_BUG_ON(TFD_CLOEXEC != O_CLOEXEC)] and
    [BUILD_BUG_ON(TFD_NONBLOCK != O_NONBLOCK)].  Spelling the value as
    [Z.lor O_CLOEXEC O_NONBLOCK] rather than as 526336 is therefore not a
    convenience: it is the kernel's own definition, and the two
    [BUILD_BUG_ON]s are what license reusing the [O_] constants for it.

    [TFD_TIMER_ABSTIME] and [TFD_TIMER_CANCEL_ON_SET] belong to
    [TFD_SETTIME_FLAGS] and are NOT accepted here -- passing either to
    [timerfd_create] is -EINVAL.  They go unnamed because
    [timerfd_settime] has no arm. *)
Definition TFD_CREATE_FLAGS : Z := Z.lor O_CLOEXEC O_NONBLOCK.

(** [EFD_SEMAPHORE], the one flag bit [eventfd2] accepts that no other
    anon-inode create call does.

    include/uapi/linux/eventfd.h (Linux v6.18.46) defines it as
    [(1 << 0)] beside [EFD_CLOEXEC O_CLOEXEC] and
    [EFD_NONBLOCK O_NONBLOCK]; fs/eventfd.c's [do_eventfd] asserts all
    three at build time rather than assuming them, opening with
    [BUILD_BUG_ON(EFD_CLOEXEC != O_CLOEXEC)],
    [BUILD_BUG_ON(EFD_NONBLOCK != O_NONBLOCK)] and
    [BUILD_BUG_ON(EFD_SEMAPHORE != (1 << 0))].

    The three [EFD_] names were not always in the same header: at v6.1
    and earlier all three sit in include/linux/eventfd.h, and the uapi
    header carrying them is there from at least v6.6.  The VALUES are
    identical across that move, so nothing here turns on which header a
    reader opens -- but the path in a citation does, which is why the
    move is stated rather than left for the next reader to rediscover. *)
Definition EFD_SEMAPHORE : Z := 1%Z.

(** [EFD_FLAGS_SET], the only flag bits [eventfd2] accepts.

    include/linux/eventfd.h (Linux v6.18.46) defines
    [EFD_SHARED_FCNTL_FLAGS (O_CLOEXEC | O_NONBLOCK)] and then
    [EFD_FLAGS_SET (EFD_SHARED_FCNTL_FLAGS | EFD_SEMAPHORE)], so the
    create mask is the shared-fcntl mask WIDENED BY ONE BIT -- which is
    what separates it from [TFD_CREATE_FLAGS], where the create mask IS
    the shared-fcntl mask and nothing more.

    THAT ONE BIT IS THE WHOLE DIFFERENCE between the two masks, and it
    is why they are two constants rather than one shared name.  Bit 0 is
    [EFD_SEMAPHORE] to [eventfd2] and is [TFD_TIMER_ABSTIME] --
    [timerfd_settime]'s flag, not [timerfd_create]'s -- to
    [timerfd_create], which refuses it.  So [eventfd2(0, 1)] hands back
    a descriptor and [timerfd_create(CLOCK_MONOTONIC, 1)] is -EINVAL,
    and a model that spelled one gate with the other's mask would be
    wrong on exactly one input each way. *)
Definition EFD_FLAGS_SET : Z := Z.lor (Z.lor O_CLOEXEC O_NONBLOCK) EFD_SEMAPHORE.

(** The range [ktime_t] represents, in nanoseconds.

    Linux carries kernel time as [ktime_t], a signed 64-bit nanosecond
    count — [typedef s64 ktime_t] in include/linux/types.h (not
    ktime.h, whose surrounding helpers do change across the range:
    v6.14 adds [us_to_ktime]).  The typedef itself is unchanged at
    v6.10-v6.15.  So 2^63 nanoseconds — about 292 years — is the first
    value it cannot hold.

    Every time spec below the header layer needs this bound, for a
    different quantity: [Kernel.Time.PosixTimers] as the ceiling on a
    recorded [CLOCK_MONOTONIC] reading, and [Kernel.Time.Hrtimer] as
    the ceiling on where a sleep may carry that reading.  It is here
    rather than with either of them because it is a fact about the
    type, not about a syscall. *)
Definition CLOCK_NS_ENVELOPE : Z := (2 ^ 63)%Z.

(** The largest value [ktime_t] holds:
    [#define KTIME_MAX ((s64)~((u64)1 << 63))] (include/linux/time64.h
    at v6.18.46, which is where both constants are defined —
    include/linux/ktime.h uses them without redefining them), i.e.
    2^63 - 1, one nanosecond below [CLOCK_NS_ENVELOPE].

    It is the value [ktime_add_safe] (kernel/time/hrtimer.c) SATURATES
    to, which is the one place the two constants must not be confused.
    That function's saturation arm reads [res = ktime_set(KTIME_SEC_MAX,
    0)], and its comment says it is using "the maximum timeout which we
    can return to user space in a timespec" — but [ktime_set]
    (include/linux/ktime.h) opens with
    [if (unlikely(secs >= KTIME_SEC_MAX)) return KTIME_MAX;], and the
    test is [>=], so passing exactly [KTIME_SEC_MAX] takes that early
    return.  The saturation value is therefore [KTIME_MAX], NOT
    [KTIME_SEC_MAX * 10^9] — the code does not do what its own comment
    describes, and the difference is the 854775807 ns between them.
    [Kernel.Time.Hrtimer.nanosleep_clock] needs the value the code
    produces.  Both functions read as quoted at v6.18.46. *)
Definition KTIME_MAX : Z := (2 ^ 63 - 1)%Z.

(** The largest whole second [ktime_t] can hold:
    [#define KTIME_SEC_MAX (KTIME_MAX / NSEC_PER_SEC)] over
    [#define KTIME_MAX ((s64)~((u64)1 << 63))] (include/linux/time64.h;
    the whole constant block is byte-identical at v6.10-v6.15), i.e.
    (2^63 - 1) / 10^9 = 9223372036.

    Two readers need it, for different reasons:
    [Time.gettimeofday_spec] as the ceiling on a wall-clock
    reading, and [timespec_ktime] just below as the point where
    [ktime_set] stops converting a request and starts clamping. *)
Definition KTIME_SEC_MAX : Z := 9223372036%Z.

(** Two little-endian 8-byte fields, read OUT of the bytes the kernel
    wrote.

    THE NAMES ARE STRUCT-NEUTRAL because three structs have this shape
    on riscv64.  [struct __kernel_timespec] { [__kernel_time64_t
    tv_sec]; [long long tv_nsec] } and [struct __kernel_old_timeval]
    { [__kernel_long_t tv_sec]; [__kernel_long_t tv_usec] }
    (include/uapi/linux/time_types.h, byte-identical at v6.10-v6.15)
    are both 16 bytes of two 8-byte fields, differing only in the UNIT
    of the second one — nanoseconds against microseconds.  So the
    decoders are shared and only the per-struct predicates
    ([Kernel.Time.PosixTimers.timespec_ok_b],
    [Time.timeval_ok_b],
    [Kernel.Time.Hrtimer.timespec_valid_b]) differ.

    Reading the bytes, rather than encoding a chosen count into them,
    is deliberate: the bytes in the destination buffer are what the
    kernel actually produced, so
    every condition over them is stated about them directly.  The
    alternative — choose a count, encode it, and have the acceptor
    decode it back — would need the encode/decode round-trip as a proof
    obligation to say the same thing. *)
Definition tv_sec_of (bs : list byte) : Z :=
  bytes_le_to_Z (firstn 8 bs).
Definition tv_frac_of (bs : list byte) : Z :=
  bytes_le_to_Z (skipn 8 bs).

(** A whole [struct __kernel_timespec] as a nanosecond count.  Computed
    in [Z], NOT in [word]: a wrapping sum would let an absurd [tv_sec]
    land back under the envelope and read as a small, admissible
    time. *)
Definition timespec_ns (bs : list byte) : Z :=
  (tv_sec_of bs * 1000000000 + tv_frac_of bs)%Z.

(** The same [struct __kernel_timespec] as the [ktime_t] the kernel
    converts it to, which is NOT the same number.

    [timespec64_to_ktime] is [ktime_set(ts.tv_sec, ts.tv_nsec)]
    (include/linux/ktime.h at v6.18.46, where both functions are
    defined), and [ktime_set] opens with

      [if (unlikely(secs >= KTIME_SEC_MAX)) return KTIME_MAX;]

    so the conversion STOPS at [KTIME_SEC_MAX] and hands back
    [KTIME_MAX] rather than a product.  The two disagree over the whole
    band [[KTIME_SEC_MAX, 2^63)] of seconds a [timespec64] can carry
    past [timespec64_valid], and they disagree AT the boundary too, in
    both directions: [KTIME_SEC_MAX] seconds converts to [KTIME_MAX]
    and not to [KTIME_SEC_MAX * 10^9], which is 854775807 ns lower.

    [tv_sec] is read unsigned here for [timespec_ns]'s reason, and the
    one caller ([Kernel.Time.Hrtimer.nanosleep_clock]) has already
    applied [timespec64_valid], which refuses a [tv_sec] at or past
    2^63 — so the band this function saturates over is exactly the band
    that predicate lets through. *)
Definition timespec_ktime (bs : list byte) : Z :=
  if (tv_sec_of bs <? KTIME_SEC_MAX)%Z then timespec_ns bs else KTIME_MAX.

(** The same total with [tv_sec] read as the SIGNED 64-bit field it
    actually is ([__kernel_time64_t] is [long long]).  [timespec_ns]
    reads it unsigned, which is what the two arms that report a TIME
    want — a negative second is not a time, and reading it unsigned
    turns it into a number far past their envelope, which is exactly
    the rejection they need.  [CLOCK_PROCESS_CPUTIME_ID] does not
    report a time, and a negative [tv_sec] is a shape it really emits,
    so [Kernel.Time.PosixTimers.cputime_ok_b] needs the signed reading.
    Computed in [Z] for [timespec_ns]'s reason: a wrapping sum would
    let an absurd [tv_sec] land back in range. *)
Definition timespec_ns_signed (bs : list byte) : Z :=
  ((if (tv_sec_of bs <? 2 ^ 63)%Z then tv_sec_of bs
    else tv_sec_of bs - 2 ^ 64) * 1000000000 + tv_frac_of bs)%Z.

(** [AT_REMOVEDIR] (0x200): the only flag [unlinkat] accepts.  Any other
    bit is a deterministic -EINVAL, decided before the pathname is
    fetched and before the dirfd is looked at — see [Fs.Namei.unlinkat_spec]
    (Linux include/uapi/linux/fcntl.h; the value is unchanged v6.10
    through v6.15, though the file was reorganised in v6.12). *)
Definition AT_REMOVEDIR : Z := 512%Z.

(** The longest single path COMPONENT every Linux filesystem in reach
    accepts (Linux include/uapi/linux/limits.h).  [fs/namei.c] itself has
    NO such check — the bound belongs to the filesystem, raised by
    [dir->i_op->lookup] ([simple_lookup] in fs/libfs.c on tmpfs and
    [ext4_lookup] in fs/ext4/namei.c on ext4, both -ENAMETOOLONG at 255;
    that guard is the FIRST statement of each function and is unchanged
    v6.10 through v6.16, though the bodies around it are not — ext4's
    changed at v6.11 and libfs's at v6.13, and ext4 reaches 255 through
    its own [EXT4_NAME_LEN] rather than through [NAME_MAX]).  So the
    model, which represents no filesystem type, declines a longer name
    rather than picking one filesystem's answer. *)
Definition NAME_MAX : nat := 255.

(** One second in nanoseconds (include/vdso/time64.h [NSEC_PER_SEC]),
    the bound [timespec64_valid] holds [tv_nsec] under. *)
Definition NSEC_PER_SEC : Z := 1000000000%Z.

(** [sizeof(sigset_t)] as the KERNEL declares it: [_NSIG] is 64, so the
    mask is 8 bytes.  [set_user_sigmask] rejects any other
    [sigsetsize] with -EINVAL.  Note this is the kernel's sigset, not
    glibc's 128-byte one. *)
Definition kernel_sigset_bytes : Z := 8%Z.

(** [rt_sigprocmask]'s [how], from include/uapi/asm-generic/signal-defs.h.
    riscv defines no [uapi/asm/signal.h] of its own, so the asm-generic
    values are the ones the riscv64 ABI uses.  Byte-identical across
    v6.1 - v6.17. *)
Definition SIG_BLOCK   : Z := 0%Z.
Definition SIG_UNBLOCK : Z := 1%Z.
Definition SIG_SETMASK : Z := 2%Z.

(** [sizeof(sigset_t)], the size [rt_sigprocmask] demands in its fourth
    argument and the number of bytes it copies.

    Eight, and derived rather than asserted: include/uapi/asm-generic/
    signal.h has [_NSIG 64], [_NSIG_BPW __BITS_PER_LONG] and
    [typedef struct { unsigned long sig[_NSIG / _NSIG_BPW]; } sigset_t],
    and riscv64's [__BITS_PER_LONG] is [__SIZEOF_POINTER__ * 8]
    (arch/riscv/include/uapi/asm/bitsperlong.h), i.e. 64, so [sigset_t]
    is one 64-bit word.  Both headers are byte-identical across v6.1 - v6.17.

    The same eight bytes as [kernel_sigset_bytes] above, which
    [set_user_sigmask]'s check on pselect6's sigmask argument names;
    the two are separate definitions, one for each spec that names the
    constant.

    NOT musl's userspace [sigset_t], which is 128 bytes
    (include/signal.h). *)
Definition NSIG_BYTES : Z := 8%Z.

(** [sigaltstack]'s three flag values, from include/uapi/linux/signal.h
    (Linux v6.18.46, commit 1f99e9ab748f).  riscv defines no
    [uapi/asm/signal.h] of its own, so these asm-generic values are the
    ones the riscv64 ABI uses.

    SS_AUTODISARM is the whole of [SS_FLAG_BITS] — that header defines
    [SS_FLAG_BITS] AS [SS_AUTODISARM], so the two are one constant and
    are not spelled twice here.  It is what [do_sigaltstack]
    (kernel/signal.c) masks off its [ss_flags] before comparing the rest
    against SS_DISABLE, SS_ONSTACK and 0, and what [on_sig_stack]
    (include/linux/sched/signal.h) tests to answer "not on the stack"
    without looking at the stack pointer. *)
Definition SS_ONSTACK    : Z := 1%Z.
Definition SS_DISABLE    : Z := 2%Z.
Definition SS_AUTODISARM : Z := 0x80000000%Z.     (* = SS_FLAG_BITS *)

(** [sizeof(stack_t)] on riscv64: [ss_sp](8) at 0, [ss_flags](4, an
    [int]) at 8, four bytes of padding, [ss_size](8, a
    [__kernel_size_t]) at 16 — 24 bytes.  The struct is the asm-generic
    one (include/uapi/asm-generic/signal.h, [typedef struct sigaltstack
    ... stack_t]), which riscv does not override.
    [SYSCALL_DEFINE2(sigaltstack)] (kernel/signal.c) copies exactly
    [sizeof(stack_t)] out of [uss] in ONE [copy_from_user], so
    readability is all-or-nothing across the whole 24 — the padding
    included, even though nothing reads it. *)
Definition SIGALTSTACK_BYTES : Z := 24%Z.
Definition SS_SP_OFF    : Z := 0%Z.
Definition SS_FLAGS_OFF : Z := 8%Z.
Definition SS_SIZE_OFF  : Z := 16%Z.

(** The smallest alternate stack [sigaltstack] accepts:
    [SYSCALL_DEFINE2(sigaltstack)] passes MINSIGSTKSZ as
    [do_sigaltstack]'s [min_ss_size], and riscv takes the asm-generic
    value 2048 (include/uapi/asm-generic/signal.h, guarded by
    [#if !defined MINSIGSTKSZ]; riscv supplies no [uapi/asm/signal.h] to
    define one first).  Anything smaller is -ENOMEM.  It is not the only
    lower bound the kernel applies — see [Kernel.Signal.sigaltstack_spec]
    for [sigaltstack_size_valid], which is the other one and is why that
    spec's success arm carries a premise. *)
Definition MINSIGSTKSZ : Z := 2048%Z.

(** The two signals a mask may never contain, as the bits they occupy in
    a [sigset_t]: [sigmask(sig)] is [1 << (sig - 1)]
    (include/linux/signal.h), SIGKILL is 9 and SIGSTOP is 19
    (include/uapi/asm-generic/signal.h), so the pair is bit 8 | bit 18 =
    0x40100.  [rt_sigprocmask] clears exactly these from the set it is
    handed, with
    [sigdelsetmask(&new_set, sigmask(SIGKILL)|sigmask(SIGSTOP))]
    (kernel/signal.c, [SYSCALL_DEFINE4(rt_sigprocmask)], Linux v6.18.46,
    commit 1f99e9ab748f), and answers 0: blocking either is silently
    ignored, NOT -EINVAL.  That is the opposite of [rt_sigaction], where
    [sig_kernel_only] is an error — see [Kernel.Signal.sig_kernel_only],
    which tests the same two signals for the other syscall's sake.

    THE STRIP IS THE WRAPPER'S, NOT [sigprocmask]'s.  The comment above
    [sigprocmask] in the same file says so in as many words: "Unlike the
    user-mode sys_sigprocmask(), the kernel interface happily blocks
    'unblockable' signals like SIGKILL and friends."  So a claim that
    every path clearing these bits runs through one function is FALSE;
    what is true is the enumeration in [Run.valid_sigmask]. *)
Definition sig_kernel_only_mask : Z := 262400%Z.

(** SIGABRT, and the bit it occupies in a [sigset_t].  6
    (include/uapi/asm-generic/signal.h), so [sigmask(SIGABRT)] is
    [1 << 5] = 32 (include/linux/signal.h, the same [sigmask] macro
    [sig_kernel_only_mask] is built from).  Its default disposition is
    SIG_CORE -- terminate the process and dump core
    (kernel/signal.c's [sig_kernel_coredump] over SIG_KERNEL_COREDUMP_MASK,
    Linux v6.18.46, commit 1f99e9ab748f) -- and the core dump itself is
    outside anything this model observes: [do_coredump] writes a file the
    process cannot see and [do_group_exit] ends the process either way.
    What reaches the trace is the DEATH and the signal number, which is
    what a waiting parent reads through WIFSIGNALED/WTERMSIG and a shell
    renders as 134. *)
Definition SIGABRT : Z := 6%Z.
Definition sigabrt_mask : Z := 32%Z.

(** [WNOHANG], the one wait4 option this model accepts
    (include/uapi/linux/wait.h, whose [W*] macro block is byte-identical
    in mainline from v3.10 — the oldest tag that still fetches — through
    v7.2; that header is where every [W*] macro lives, and
    include/linux/wait.h is wait-queue types and defines none of them).
    The FILE moved twice in that span, both times outside the block: an
    SPDX line at v4.14 and [P_PIDFD] at v5.4.  The other option bits
    Linux accepts — WUNTRACED, WCONTINUED, __WNOTHREAD, __WCLONE,
    __WALL — are not named here because no arm reads them: they select
    which children are eligible and which state changes are reportable,
    questions about children this model does not have.  Anything but
    WNOHANG declines; see [Kernel.Exit.wait4_spec]. *)
Definition WNOHANG : Z := 1%Z.
(** MSG_CMSG_COMPAT (include/linux/socket.h).  Its VALUE depends on the
    kernel's configuration: [0x80000000] under CONFIG_COMPAT and [0]
    without it, and the two give different answers for the same call —
    see [Net.Socket.recvmsg_spec]. *)
Definition MSG_CMSG_COMPAT : Z := 2147483648%Z.   (* 0x80000000 *)

(** [NR_OPEN_DEFAULT], the number of descriptor slots embedded in a
    [struct files_struct] (include/linux/fdtable.h,
    [#define NR_OPEN_DEFAULT BITS_PER_LONG], Linux v6.18.46, commit
    1f99e9ab748f) — 64 on the LP64 target this model compiles for, and 32
    on a 32-bit one, which is the one leg of the argument below that is
    arch-dependent.

    WHY A SPEC READS IT.  It is a FLOOR on the live descriptor table:
    every [struct fdtable] a task can reach has [max_fds >=
    NR_OPEN_DEFAULT].  There are three producers and no shrinker (all
    fs/file.c) — [init_files] is a static initializer at exactly this
    value; [dup_fd] starts the new table at the embedded [fdtab] and
    calls [alloc_fdtable] only under [while (open_files >
    new_fdt->max_fds)]; and [alloc_fdtable] returns a table no smaller
    than it was asked for.  Both writes of [max_fds] happen before the
    table is published with [rcu_assign_pointer], and nothing writes it
    in place.  [sane_fdtable_size] cannot ask for less either: every
    return is [NR_OPEN_DEFAULT] or [ALIGN(last + 1, BITS_PER_LONG)].

    The consequence [Fs.File.dup3_spec] uses: [expand_files(files, nr)]
    opens with [if (nr < fdt->max_fds) return 0;], so for [nr <
    NR_OPEN_DEFAULT] it returns 0 having allocated nothing — neither the
    -EMFILE of [nr >= sysctl_nr_open] nor the -ENOMEM of a failed
    [kvmalloc] is reachable.  The bound is a comment rather than an
    assertion on the kernel's side ([alloc_fdtable] documents its
    [slots_wanted > BITS_PER_LONG] precondition and does not check it),
    so it is the two call sites that hold it up.

    Its two readers use the floor for different things:
    [Fs.File.dup3_spec] for [expand_files], and
    [Fs.Select.pselect_nfds_max] for [core_sys_select]'s clamp to
    [max_fds].

    It says nothing about whether an operation SUCCEEDS: RLIMIT_NOFILE is
    a separate and earlier gate in every caller, which is why
    [dup3_spec] tests the limit before it reaches this. *)
Definition NR_OPEN_DEFAULT : Z := 64%Z.

(** [NGROUPS_MAX], the ceiling on a process's supplementary group list
    (include/uapi/linux/limits.h, [#define NGROUPS_MAX 65536]; the value
    has stood since before v2.6.12, the oldest commit in the tree).  The
    kernel enforces it where the list is WRITTEN — [setgroups] answers
    -EINVAL for a [gidsetsize] above it (kernel/groups.c,
    [SYSCALL_DEFINE2(setgroups)]) — so no [struct group_info] a process
    can hold is longer.  [Kernel.Groups.getgroups_spec] reads it as the
    bound that makes its own answer one an [int] return can carry. *)
Definition NGROUPS_MAX : Z := 65536%Z.

(** The scheduling policies [sched_setscheduler] takes, and the flag bit
    it lets a caller OR into them (include/uapi/linux/sched.h, Linux
    v6.18.46, commit 1f99e9ab748f).  4 is absent from the block on
    purpose — the header reserves it for an unimplemented SCHED_ISO and
    defines no name for it — so the six numbers below are not an
    interval and a membership test cannot be written as a range.

    [SCHED_EXT] is named for the opposite reason to the other five: no
    arm ANSWERS it.  [Kernel.Sched.Syscalls.sched_setscheduler_spec]
    declines it, and the constant exists so the decline can say which
    number it is declining.  See that spec for why: whether
    kernel/sched/sched.h's [valid_policy] admits 7 at all turns on
    CONFIG_SCHED_CLASS_EXT, and the model does not fix that config. *)
Definition SCHED_NORMAL   : Z := 0%Z.
Definition SCHED_FIFO     : Z := 1%Z.
Definition SCHED_RR       : Z := 2%Z.
Definition SCHED_BATCH    : Z := 3%Z.
Definition SCHED_IDLE     : Z := 5%Z.
Definition SCHED_DEADLINE : Z := 6%Z.
Definition SCHED_EXT      : Z := 7%Z.

(** The legacy "revert to SCHED_NORMAL on fork" bit, ORed into the
    policy word rather than passed separately
    (include/uapi/linux/sched.h).  [_sched_setscheduler]
    (kernel/sched/syscalls.c) strips it into
    [attr.sched_flags |= SCHED_FLAG_RESET_ON_FORK] before
    [__sched_setscheduler] reads the policy, which is why it has to be
    masked off a policy word before that word is compared against the
    six names above. *)
Definition SCHED_RESET_ON_FORK : Z := 0x40000000%Z.

(** The first priority [__sched_setscheduler] refuses: it answers
    -EINVAL for [attr->sched_priority > MAX_RT_PRIO-1], so 1..99 are the
    RT priorities and 0 is the only one a non-RT policy accepts
    (include/linux/sched/prio.h, [#define MAX_RT_PRIO 100]; the
    comparison is in kernel/sched/syscalls.c,
    [__sched_setscheduler]).  It is not a uapi constant — the number a
    program is told to use is [sched_get_priority_max(SCHED_FIFO)],
    which computes it — but the comparison the model transcribes is
    against this. *)
Definition MAX_RT_PRIO : Z := 100%Z.

(** [CLONE_VM], the bit that makes a new task share the caller's address
    space (include/uapi/linux/sched.h, Linux v6.18.46, commit
    1f99e9ab748f).

    Named here for ONE reader, and it is not in [Sys/]: it is the bit
    [Kernel.Futex.Syscalls]'s empty-waiter-set argument depends on
    nobody ever granting, and
    [Checks.Cases.Kernel.Futex.Syscalls] turns that dependency into a
    compile-time fact over both clone gates.  [Kernel.Fork] names the
    flag in prose throughout and needs no constant, because its gates
    are equalities on whole words rather than mask tests. *)
Definition CLONE_VM : Z := 256%Z.

(** The [futex] operation words this model answers, and the two bits
    that decorate them (include/uapi/linux/futex.h, Linux v6.18.46,
    commit 1f99e9ab748f).

    [SYSCALL_DEFINE6(futex)] (kernel/futex/syscalls.c) does not switch on
    [op] itself: [do_futex] splits it into a COMMAND, [op &
    FUTEX_CMD_MASK], and the two flag bits the mask removes,
    [FUTEX_PRIVATE_FLAG] and [FUTEX_CLOCK_REALTIME].  The mask is
    [~(FUTEX_PRIVATE_FLAG | FUTEX_CLOCK_REALTIME)], so every OTHER bit
    of [op] is part of the command and reaches the switch's [default:
    return -ENOSYS;].

    [FUTEX_PRIVATE_FLAG] is not decoration.  [futex_to_flags]
    (kernel/futex/futex.h) sets [FLAGS_SHARED] exactly when the bit is
    CLEAR, and that flag decides which key [get_futex_key]
    (kernel/futex/core.c) builds — the private path keys on
    [(current->mm, address)] and returns before it looks at a page at
    all, the shared path resolves the page and can key on an inode two
    processes share.  So the bit changes WHO can be waiting on the word,
    which is the whole of what [Kernel.Futex.Syscalls.futex_spec] needs
    to decide, and the two words below are the private ones. *)
Definition FUTEX_WAIT : Z := 0%Z.
Definition FUTEX_WAKE : Z := 1%Z.
Definition FUTEX_PRIVATE_FLAG : Z := 128%Z.
Definition FUTEX_WAIT_PRIVATE : Z := Z.lor FUTEX_WAIT FUTEX_PRIVATE_FLAG.
Definition FUTEX_WAKE_PRIVATE : Z := Z.lor FUTEX_WAKE FUTEX_PRIVATE_FLAG.

(** The width of a futex word, in bytes.

    [futex_size] (kernel/futex/futex.h) is [1 << (flags &
    FLAGS_SIZE_MASK)], and [futex_to_flags] hands the legacy [futex]
    entry point [FLAGS_SIZE_32] unconditionally — the size bits come
    only from the [futex2] flag word, which reaches the kernel through
    [futex_waitv] / [futex_wake] / [futex_wait], the numbers 449, 454
    and 455, none of which has an arm here.  [futex_flags_valid] refuses
    anything but [FLAGS_SIZE_32] anyway ("Only 32bit futexes are
    implemented -- for now").  So 4 is the width for every call this
    spec can see, and it is the width of BOTH things [get_futex_key]
    uses it for: the alignment the address must have, and the length
    [access_ok] is given. *)
Definition FUTEX_WORD_SIZE : Z := 4%Z.

(** [__NEW_UTS_LEN], the length of a [struct new_utsname] field WITHOUT
    its terminator (include/uapi/linux/utsname.h,
    [#define __NEW_UTS_LEN 64], Linux v6.18.46, commit 1f99e9ab748f).
    Every one of the struct's six members is declared
    [char field[__NEW_UTS_LEN + 1]], so the field a [uname] (160) copies
    out is 65 bytes wide and the string in it is at most 64 characters.
    [Kernel.Sys.uname_spec] reads it as the field stride; the +1 is what
    guarantees a terminator inside the field, which is the one thing that
    spec asserts about the four members it does not pin. *)
Definition NEW_UTS_LEN : Z := 64%Z.

(** [sizeof(struct new_utsname)]: six 65-byte [char] arrays, so 390 bytes
    with no padding anywhere — a struct of [char] arrays has alignment 1
    (include/uapi/linux/utsname.h, [struct new_utsname], Linux v6.18.46,
    commit 1f99e9ab748f).  This is the width of the SINGLE
    [copy_to_user(name, &tmp, sizeof(tmp))] in
    [SYSCALL_DEFINE1(newuname)] (kernel/sys.c), which is why
    [Kernel.Sys.uname_spec] gates one range of exactly this size rather
    than six.

    The member order is fixed by the same declaration and the spec
    depends on it: [sysname], [nodename], [release], [version],
    [machine], [domainname], at offsets 0, 65, 130, 195, 260 and 325. *)
Definition NEW_UTSNAME_SIZE : Z := 390%Z.

(** [PR_CAPBSET_READ], the one [prctl] option this model answers
    (include/uapi/linux/prctl.h, Linux v6.18.46, commit 1f99e9ab748f).
    It is NOT handled in kernel/sys.c's own [switch]: the LSM hook
    [security_task_prctl] runs first, and capability's implementation of
    it -- [cap_task_prctl] (security/commoncap.c) -- answers this option
    and returns before the syscall body's [switch] is reached.  See
    [Kernel.Sys.prctl_spec], which is where the whole argument lives. *)
Definition PR_CAPBSET_READ : Z := 23%Z.

(** [CAP_LAST_CAP], the highest capability number the kernel recognises:
    [CAP_CHECKPOINT_RESTORE], 40 (include/uapi/linux/capability.h, Linux
    v6.18.46, commit 1f99e9ab748f).  [cap_valid], defined in the same
    header as [((x) >= 0 && (x) <= CAP_LAST_CAP)], is what
    [cap_task_prctl] tests [PR_CAPBSET_READ]'s [arg2] against, and it is
    the ONLY thing separating the option's answer from -EINVAL.

    A VERSION FACT, and the narrowest claim in [Kernel.Sys.prctl_spec]:
    40 has been the last capability since v5.9 added
    [CAP_CHECKPOINT_RESTORE], and a kernel that adds a 41st moves the
    -EINVAL boundary this model pins.  That is the same standing pin
    every other constant here carries, stated because the boundary is
    what programs SEARCH FOR -- libcap's [cap_max_bits] binary-searches
    it -- so it is read by real code rather than merely available. *)
Definition CAP_LAST_CAP : Z := 40%Z.

(* =========================================================================
   struct stat, as fstat (80) and newfstatat (79) copy it out
   ========================================================================= *)

(** [sizeof(struct stat)] on riscv64.  riscv64 has no [asm/stat.h] of
    its own, so it takes the generic 64-bit layout
    (include/uapi/asm-generic/stat.h, Linux v6.18.46, commit
    1f99e9ab748f), whose members and offsets are

      unsigned long  st_dev         0
      unsigned long  st_ino         8
      unsigned int   st_mode       16
      unsigned int   st_nlink      20
      unsigned int   st_uid        24
      unsigned int   st_gid        28
      unsigned long  st_rdev       32
      unsigned long  __pad1        40
      long           st_size       48
      int            st_blksize    56
      int            __pad2        60
      long           st_blocks     64
      long           st_atime      72
      unsigned long  st_atime_nsec 80
      long           st_mtime      88
      unsigned long  st_mtime_nsec 96
      long           st_ctime     104
      unsigned long  st_ctime_nsec 112
      unsigned int   __unused4    120
      unsigned int   __unused5    124

    ALL 128 BYTES ARE DELIVERED, padding included.  [cp_new_stat]
    (fs/stat.c) zeroes its stack copy through [INIT_STRUCT_STAT_PADDING]
    — which riscv64 leaves at the generic [memset], only x86 overriding
    it — fills the members above, and hands the whole struct to a single
    [copy_to_user]. *)
Definition STAT_SIZE : Z := 128%Z.

(** Member offsets this file's predicates read.  Named rather than
    written inline because three of them are read twice, and because a
    layout error is the one mistake a reader cannot see in a numeral. *)
Definition ST_MODE_OFF : nat := 16%nat.
Definition ST_RDEV_OFF : nat := 32%nat.
Definition ST_PAD1_OFF : nat := 40%nat.
Definition ST_SIZE_OFF : nat := 48%nat.
Definition ST_BLKSIZE_OFF : nat := 56%nat.
Definition ST_PAD2_OFF : nat := 60%nat.
Definition ST_BLOCKS_OFF : nat := 64%nat.
Definition ST_UNUSED45_OFF : nat := 120%nat.

(** One little-endian member of a delivered [struct stat], as the
    unsigned value of its [n] bytes at [off].  riscv64 is
    little-endian, and every member above is a plain integer, so a
    member is exactly this.  A short buffer reads as the value of what
    bytes are there — the length is checked separately, by
    [stat_buf_wf]. *)
Definition stat_field_le (off n : nat) (bs : list byte) : Z :=
  bytes_le_to_Z (firstn n (skipn off bs)).

(** [S_IFMT] and the seven file types it selects
    (include/uapi/linux/stat.h, Linux v6.18.46, commit 1f99e9ab748f).
    [S_IFMT] is the mask; the seven values below are every type the mask
    can hold, and an inode always has exactly one of them —
    [inode_init_always] (fs/inode.c) is reached only through an
    allocation that a filesystem then gives a type, and every
    [init_special_inode]/[d_instantiate] path sets one. *)
Definition S_IFMT   : Z := 61440%Z.  (* 0170000 *)
Definition S_IFSOCK : Z := 49152%Z.  (* 0140000 *)
Definition S_IFLNK  : Z := 40960%Z.  (* 0120000 *)
Definition S_IFREG  : Z := 32768%Z.  (* 0100000 *)
Definition S_IFBLK  : Z := 24576%Z.  (* 0060000 *)
Definition S_IFDIR  : Z := 16384%Z.  (* 0040000 *)
Definition S_IFCHR  : Z :=  8192%Z.  (* 0020000 *)
Definition S_IFIFO  : Z :=  4096%Z.  (* 0010000 *)

(** The [S_IFMT] bits of a delivered [struct stat]'s [st_mode]. *)
Definition stat_ifmt (bs : list byte) : Z :=
  Z.land (stat_field_le ST_MODE_OFF 4 bs) S_IFMT.

(** Whether the kernel called the object a REGULAR FILE.  This is a
    question ABOUT THE ANSWER, not a claim by the model: the model does
    not know a path's type, and
    [Fs.Stat.fstat_spec] uses this only to decide whether its [st_size]
    obligation applies. *)
Definition stat_is_reg (bs : list byte) : bool :=
  Z.eqb (stat_ifmt bs) S_IFREG.

(** Whether [st_mode] names one of the seven types at all.  An
    all-zero [st_mode] is not one of them, which is what makes an
    all-zero [struct stat] — the shape a kernel that wrote nothing but
    claimed to have written would produce — inadmissible. *)
Definition stat_ifmt_valid (bs : list byte) : bool :=
  let t := stat_ifmt bs in
  (Z.eqb t S_IFSOCK || Z.eqb t S_IFLNK || Z.eqb t S_IFREG || Z.eqb t S_IFBLK
   || Z.eqb t S_IFDIR || Z.eqb t S_IFCHR || Z.eqb t S_IFIFO)%bool.

(** THE ENVELOPE EVERY DELIVERED [struct stat] MUST FALL IN, and it is
    everything [cp_new_stat] settles without consulting the inode:

    - the width is exactly [STAT_SIZE], the single [copy_to_user]'s;
    - [__pad1], [__pad2] and [__unused4]/[__unused5] are ZERO, because
      [INIT_STRUCT_STAT_PADDING] cleared the whole struct and no member
      assignment covers those bytes.  This is the part of the answer the
      model knows EXACTLY rather than nondeterministically, and it is
      what makes a poisoned or invented buffer rejectable;
    - [st_mode] names one of the seven file types.

    Nothing else is claimed here.  Which type it is, the permission
    bits, the ids, the inode, the device, the link count, the block
    size, the block count and the three timestamps are the environment's
    (see [Fs.Stat.fstat_spec]). *)
Definition stat_buf_wf (bs : list byte) : bool :=
  (Nat.eqb (length bs) 128
   && stat_ifmt_valid bs
   && Z.eqb (stat_field_le ST_PAD1_OFF 8 bs) 0
   && Z.eqb (stat_field_le ST_PAD2_OFF 4 bs) 0
   && Z.eqb (stat_field_le ST_UNUSED45_OFF 8 bs) 0)%bool.

(** THE ONE MEMBER THE MODEL DERIVES, and it is derived CONDITIONALLY.

    For a regular file [st_size] is the file's length: [generic_fillattr]
    (fs/stat.c) copies [inode->i_size] into [stat->size] and
    [cp_new_stat] copies that to [tmp.st_size], and for a regular file
    [i_size] is the number of bytes the file holds — which, for a path
    this model resolves, is the length of the byte list [Fs] carries.
    THAT PREMISE IS THE ONE [ReadWrite.read_spec] ALREADY MAKES, and no
    more: it is a claim about regular files, and the implication below
    is how it is stated without extending it.

    The implication is what keeps the arm from FALSELY REJECTING.
    A path the model
    resolves can be one Linux calls a character device, where the true answer
    is S_IFCHR with [st_size] 0 while the model's byte list is not
    empty.  Asserting S_IFREG, or asserting the length unconditionally,
    rejects that conforming trace.  Under the implication the model
    simply says nothing about it, and still says something sharp about
    every file that really is regular.

    THE COMPARISON WRAPS AT 2^64, because [stat_field_le] reads eight
    bytes and a [list byte]'s length is an unbounded [nat].  A file that
    long is not constructible here — every write is bounded by
    [State.max_rw_count] and the initial image is a run input — so the
    wrap is unreachable rather than an approximation; it is written this
    way so the predicate is TOTAL, which is what
    [Checks.Witness.Fs.Stat]'s witness needs on the pinned branch. *)
Definition stat_size_ok (n : nat) (bs : list byte) : bool :=
  implb (stat_is_reg bs)
        (Z.eqb (stat_field_le ST_SIZE_OFF 8 bs)
               (bv_unsigned (Z_to_bv 64 (Z.of_nat n)))).

(** THE MEMBERS A [struct stat] OF /dev/null CARRIES FROM THE
    KERNEL, asserted outright rather than under an implication: the
    device is known to be a device, which is what the regular-file arm
    cannot say of a key.  [cp_new_stat] (fs/stat.c, Linux v6.18.46)
    copies what [generic_fillattr] read off the inode: [st_mode]'s type
    bits are S_IFCHR because [init_special_inode] (fs/inode.c) set them
    when the node was made; [st_rdev] is [new_encode_dev] of
    [MKDEV(1, 3)] (include/linux/kdev_t.h) — [(3 & 0xff) | (1 << 8)] —
    which is [DEVNULL_RDEV]; [st_size] is [i_size], 0 on a device
    inode nothing ever wrote through ([write_null] returns without
    touching the inode, drivers/char/mem.c), and [st_blocks] is
    [i_blocks], 0 for the same reason.  The two zeros are a consequence
    of the environment premise rather than a kernel invariant: a node
    made by mknod or devtmpfs and never resized carries them, and a
    crafted inode could carry another.

    NOT asserted here, and chosen once per descriptor by
    [Fs.Stat.fstat_devnull_spec]'s pin like every other member: the
    permission bits and the owner, which are the image's node's
    (devtmpfs takes 0666 and root from [mem_devnode], drivers/char/mem.c,
    but a container runtime makes its own node), the link count, the
    device and inode numbers, the block size and the timestamps. *)
Definition DEVNULL_RDEV : Z := 259%Z.

(** The members a [struct stat] of ANY of the model's character
    devices carries from the kernel, parameterised by the device
    number: [stat_devnull_ok] and [stat_urandom_ok] are its two
    instances, and the argument above is the argument for both. *)
Definition stat_chrdev_ok (rdev : Z) (bs : list byte) : bool :=
  (Z.eqb (stat_ifmt bs) S_IFCHR
   && Z.eqb (stat_field_le ST_RDEV_OFF 8 bs) rdev
   && Z.eqb (stat_field_le ST_SIZE_OFF 8 bs) 0
   && Z.eqb (stat_field_le ST_BLOCKS_OFF 8 bs) 0)%bool.

Definition stat_devnull_ok (bs : list byte) : bool := stat_chrdev_ok DEVNULL_RDEV bs.

(** /dev/urandom's [st_rdev]: [new_encode_dev] of [MKDEV(1, 9)]
    (include/linux/kdev_t.h, v6.18.46) — [(9 & 0xff) | (1 << 8)].  The
    zero [st_size] and [st_blocks] rest on the same environment
    premise the null device's do — a node made by mknod or devtmpfs
    and never resized; [random_write_iter] mixes into the pool and
    touches no inode member (drivers/char/random.c). *)
Definition URANDOM_RDEV : Z := 265%Z.

Definition stat_urandom_ok (bs : list byte) : bool := stat_chrdev_ok URANDOM_RDEV bs.

(** Byte-list equality, for comparing a delivered [struct stat] against
    a pin.  [Fs.path_eqb] is the same function over the same type; a
    second name is used because these bytes are not a path, and
    [Checks.Sys.Prelude.listN_eqb] is not visible from a spec file. *)
Fixpoint stat_bytes_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => (bv_eqb a b && stat_bytes_eqb r1 r2)%bool
  | _, _ => false
  end.

Lemma stat_bytes_eqb_eq : forall l1 l2, stat_bytes_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|a r1 IH]; destruct l2 as [|b r2]; cbn;
    try (split; congruence).
  rewrite Bool.andb_true_iff, bv_eqb_eq, IH.
  split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

Lemma stat_bytes_eqb_refl : forall l, stat_bytes_eqb l l = true.
Proof. intro l. apply stat_bytes_eqb_eq. reflexivity. Qed.

(** THE MEMBERS THAT MAY NOT CHANGE UNDER A RUN, so that two [fstat]s of
    one file cannot disagree about which file it is.  Bytes 0..47 —
    [st_dev], [st_ino], [st_mode], [st_nlink], [st_uid], [st_gid],
    [st_rdev] and [__pad1] — and bytes 56..63, [st_blksize] and
    [__pad2].

    WHY THESE AND NOT THE REST.  Each of the eight is settled by the
    inode or by its superblock, and no syscall in
    [Sys.SyscallTable.spec_table] moves one: there is no [chmod]/[fchmod]
    arm for the permission bits, no [chown] arm for the ids, no
    [link]/[linkat] arm for the link count, and a type, an inode number,
    a device and a block size do not change at all while the inode
    lives.  [unlinkat] (35) IS modeled and DOES drop [st_nlink], but it
    also removes the key, and [Fs.Stat.fstat_spec] declines a descriptor
    whose path [Fs] no longer holds, so no [fstat] observes the drop.

    WHAT IS DELIBERATELY LEFT FREE: [st_size] (which [write] and
    [ftruncate] move, and which [stat_size_ok] constrains instead),
    [st_blocks] (which moves with it, and is the filesystem's own
    allocation rather than a function of the length — a sparse file has
    fewer), and the three timestamp pairs (which every read and write
    moves).  Requiring any of those to repeat would reject a conforming
    trace.  The three besides [st_size] are then unconstrained ACROSS
    calls, which admits a run Linux would not produce.  That is a
    known over-approximation. *)
Definition stat_stable_eqb (b1 b2 : list byte) : bool :=
  (stat_bytes_eqb (firstn ST_PAD1_OFF b1) (firstn ST_PAD1_OFF b2)
   && stat_bytes_eqb (firstn 8 (skipn ST_PAD1_OFF b1))
                     (firstn 8 (skipn ST_PAD1_OFF b2))
   && stat_bytes_eqb (firstn 8 (skipn ST_BLKSIZE_OFF b1))
                     (firstn 8 (skipn ST_BLKSIZE_OFF b2)))%bool.

Lemma stat_stable_eqb_refl : forall b, stat_stable_eqb b b = true.
Proof.
  intro b. unfold stat_stable_eqb. now rewrite !stat_bytes_eqb_refl.
Qed.

(** TWO SLICES OF A DELIVERED [struct stat] READ THE SAME out of two
    buffers that agree on the region they fall in: wholly inside the
    first 48 bytes, or wholly at or past 56.  Those two regions are
    exactly what [stat_stable_eqb] compares and where every member
    [stat_buf_wf] looks at lives, so these two carry both predicates
    across a change confined to bytes 48..55. *)

Lemma stat_slice_head : forall off k (x y : list byte),
  (off + k <= 48)%nat -> firstn 48 x = firstn 48 y ->
  firstn k (skipn off x) = firstn k (skipn off y).
Proof.
  intros off k x y Hb Heq.
  assert (Hx : forall z : list byte,
             firstn k (skipn off z) = firstn k (skipn off (firstn 48 z))).
  { intro z. rewrite skipn_firstn_comm, firstn_firstn.
    replace (Nat.min k (48 - off)) with k by lia. reflexivity. }
  rewrite (Hx x), (Hx y), Heq. reflexivity.
Qed.

Lemma stat_slice_tail : forall off k (x y : list byte),
  (56 <= off)%nat -> skipn 56 x = skipn 56 y ->
  firstn k (skipn off x) = firstn k (skipn off y).
Proof.
  intros off k x y Hb Heq.
  replace off with ((off - 56) + 56)%nat by lia.
  rewrite <- !skipn_skipn, Heq. reflexivity.
Qed.

Lemma stat_field_le_head : forall off k x y,
  (off + k <= 48)%nat -> firstn 48 x = firstn 48 y ->
  stat_field_le off k x = stat_field_le off k y.
Proof.
  intros off k x y Hb Heq. unfold stat_field_le. f_equal.
  now apply stat_slice_head.
Qed.

Lemma stat_field_le_tail : forall off k x y,
  (56 <= off)%nat -> skipn 56 x = skipn 56 y ->
  stat_field_le off k x = stat_field_le off k y.
Proof.
  intros off k x y Hb Heq. unfold stat_field_le. f_equal.
  now apply stat_slice_tail.
Qed.

(** THE SAME [struct stat] WITH A DIFFERENT [st_size].  A file that is
    statted twice with a write in between must answer with the same
    device, inode, mode, link count, ids and block size and a NEW
    length, and this is one buffer that does: it exists so
    [Checks.Witness.Fs.Stat] can name an admissible answer on the pinned
    branch of [Fs.Stat.fstat_spec] without inventing the members the pin
    fixes.  It is not itself a claim about Linux — the spec CHOOSES from
    a set this is one member of, and the timestamps and [st_blocks] it
    copies over unchanged are exactly the members a real kernel would
    have moved. *)
Definition stat_set_size (n : nat) (bs : list byte) : list byte :=
  firstn 48 bs ++ Z_to_le_bytes 8 (Z.of_nat n) ++ skipn 56 bs.

Lemma stat_set_size_head : forall n bs,
  (48 <= length bs)%nat -> firstn 48 (stat_set_size n bs) = firstn 48 bs.
Proof.
  intros n bs Hlen. unfold stat_set_size.
  rewrite firstn_app, firstn_length_le by exact Hlen.
  rewrite firstn_all2 by (rewrite firstn_length_le by exact Hlen; lia).
  replace (48 - 48)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma stat_set_size_tail : forall n bs,
  (48 <= length bs)%nat -> skipn 56 (stat_set_size n bs) = skipn 56 bs.
Proof.
  intros n bs Hlen. unfold stat_set_size.
  rewrite skipn_app, firstn_length_le by exact Hlen.
  rewrite skipn_all2 by (rewrite firstn_length_le by exact Hlen; lia).
  replace (56 - 48)%nat with 8%nat by lia.
  rewrite skipn_app, length_Z_to_le_bytes.
  rewrite skipn_all2 by (rewrite length_Z_to_le_bytes; lia).
  replace (8 - 8)%nat with 0%nat by lia. rewrite skipn_0. reflexivity.
Qed.

Lemma stat_set_size_field : forall n bs,
  (48 <= length bs)%nat ->
  firstn 8 (skipn 48 (stat_set_size n bs)) = Z_to_le_bytes 8 (Z.of_nat n).
Proof.
  intros n bs Hlen. unfold stat_set_size.
  rewrite skipn_app, firstn_length_le by exact Hlen.
  rewrite skipn_all2 by (rewrite firstn_length_le by exact Hlen; lia).
  replace (48 - 48)%nat with 0%nat by lia. rewrite skipn_0, app_nil_l.
  rewrite firstn_app, length_Z_to_le_bytes.
  rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; lia).
  replace (8 - 8)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma stat_set_size_length : forall n bs,
  length bs = 128%nat -> length (stat_set_size n bs) = 128%nat.
Proof.
  intros n bs Hlen. unfold stat_set_size.
  rewrite !length_app, length_Z_to_le_bytes, length_firstn, length_skipn, Hlen.
  reflexivity.
Qed.

Lemma stat_set_size_wf : forall n bs,
  stat_buf_wf bs = true -> stat_buf_wf (stat_set_size n bs) = true.
Proof.
  intros n bs H.
  assert (Hall := H). unfold stat_buf_wf in Hall.
  apply andb_prop in Hall as [Hall Hu]; apply andb_prop in Hall as [Hall Hp2];
    apply andb_prop in Hall as [Hall Hp1]; apply andb_prop in Hall as [Hlen Hifmt].
  apply Nat.eqb_eq in Hlen.
  assert (Hhead : firstn 48 (stat_set_size n bs) = firstn 48 bs)
    by (apply stat_set_size_head; lia).
  assert (Htail : skipn 56 (stat_set_size n bs) = skipn 56 bs)
    by (apply stat_set_size_tail; lia).
  assert (Hifmt' : stat_ifmt (stat_set_size n bs) = stat_ifmt bs).
  { unfold stat_ifmt. f_equal.
    apply stat_field_le_head; [unfold ST_MODE_OFF; lia | exact Hhead]. }
  assert (Hq1 : stat_field_le ST_PAD1_OFF 8 (stat_set_size n bs)
                = stat_field_le ST_PAD1_OFF 8 bs)
    by (apply stat_field_le_head; [unfold ST_PAD1_OFF; lia | exact Hhead]).
  assert (Hq2 : stat_field_le ST_PAD2_OFF 4 (stat_set_size n bs)
                = stat_field_le ST_PAD2_OFF 4 bs)
    by (apply stat_field_le_tail; [unfold ST_PAD2_OFF; lia | exact Htail]).
  assert (Hq3 : stat_field_le ST_UNUSED45_OFF 8 (stat_set_size n bs)
                = stat_field_le ST_UNUSED45_OFF 8 bs)
    by (apply stat_field_le_tail; [unfold ST_UNUSED45_OFF; lia | exact Htail]).
  unfold stat_buf_wf.
  rewrite (stat_set_size_length n bs Hlen), Nat.eqb_refl.
  unfold stat_ifmt_valid in Hifmt |- *. cbv zeta in Hifmt |- *.
  rewrite Hifmt', Hq1, Hq2, Hq3, Hifmt, Hp1, Hp2, Hu. reflexivity.
Qed.

Lemma stat_set_size_stable : forall n bs,
  length bs = 128%nat -> stat_stable_eqb (stat_set_size n bs) bs = true.
Proof.
  intros n bs Hlen. unfold stat_stable_eqb, ST_PAD1_OFF, ST_BLKSIZE_OFF.
  assert (Hhead : firstn 48 (stat_set_size n bs) = firstn 48 bs)
    by (apply stat_set_size_head; lia).
  assert (Htail : skipn 56 (stat_set_size n bs) = skipn 56 bs)
    by (apply stat_set_size_tail; lia).
  assert (H40 : firstn 40 (stat_set_size n bs) = firstn 40 bs).
  { pose proof (stat_slice_head 0 40 (stat_set_size n bs) bs ltac:(lia) Hhead) as Hh.
    rewrite !skipn_0 in Hh. exact Hh. }
  assert (H4048 : firstn 8 (skipn 40 (stat_set_size n bs)) = firstn 8 (skipn 40 bs))
    by (apply stat_slice_head; [lia | exact Hhead]).
  assert (H56 : firstn 8 (skipn 56 (stat_set_size n bs)) = firstn 8 (skipn 56 bs))
    by (apply stat_slice_tail; [lia | exact Htail]).
  rewrite H40, H4048, H56, !stat_bytes_eqb_refl. reflexivity.
Qed.

Lemma stat_set_size_size_ok : forall n bs,
  length bs = 128%nat -> stat_size_ok n (stat_set_size n bs) = true.
Proof.
  intros n bs Hlen. unfold stat_size_ok.
  destruct (stat_is_reg (stat_set_size n bs)); [|reflexivity].
  cbn [implb]. apply Z.eqb_eq. unfold stat_field_le, ST_SIZE_OFF.
  rewrite (stat_set_size_field n bs) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite bytes_le_to_Z_of_le_bytes by lia. reflexivity.
Qed.

Lemma stat_buf_wf_length : forall bs, stat_buf_wf bs = true -> length bs = 128%nat.
Proof.
  intros bs H. unfold stat_buf_wf in H.
  apply andb_prop in H as [H _]; apply andb_prop in H as [H _];
    apply andb_prop in H as [H _]; apply andb_prop in H as [H _].
  now apply Nat.eqb_eq in H.
Qed.
