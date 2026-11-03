(** * LinuxProcessSem.Sys.Fs.Fcntl — fcntl (25)

    This file answers to Linux [fs/fcntl.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

    It imports [Fs.Open] rather than restating anything: the F_SETFL
    arm below is sound only because of which flag words
    [Open.modeled_open_flags] admits — and the F_GETFL arm leans on the
    same set from the other side, since it is [openat] NOT admitting
    O_RDWR that keeps [socket_f_flags] a claim about sockets alone.  The
    pair
    [modeled_open_flags_clear_of_setfl] /
    [open_ignored_flags_clear_of_setfl_current] proves that over
    [Open.wr_create_flags], [Open.is_excl_create] and
    [Open.open_ignored_flags] themselves.  [Fs.Open] importing [Fs.File]
    and [Fs.ReadWrite] is the same arrangement. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Fs.Open.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** The file STATUS flags [F_SETFL] acts on.  [setfl] (fs/fcntl.c) reads
    [arg] in six places.  Five of them look at one named bit each, and
    this constant is their union:

      O_APPEND    the [((arg ^ f_flags) & O_APPEND) && IS_APPEND(inode)]
                  -EPERM test, and [SETFL_MASK];
      O_NOATIME   the [(arg & O_NOATIME) && !(f_flags & O_NOATIME)]
                  ownership -EPERM test, and [SETFL_MASK];
      O_DIRECT    the [(arg & O_DIRECT) && !FMODE_CAN_ODIRECT] -EINVAL
                  test, and [SETFL_MASK];
      O_NONBLOCK  [SETFL_MASK].  O_NDELAY is the same bit on this ABI, so
                  the [if (O_NONBLOCK != O_NDELAY)] SunOS fixup above it
                  is dead code here;
      FASYNC      the [((arg ^ f_flags) & FASYNC) && f_op->fasync]
                  callback.  FASYNC is NOT in [SETFL_MASK], so a constant
                  copied from that macro alone would be the wrong set;
                  including it is what keeps this arm's soundness from
                  depending on which file operations the fd's filesystem
                  happens to define.

    THE SIXTH READ IS THE ONE A MASK CANNOT COVER: [setfl] hands the
    WHOLE, unmasked [arg] to [filp->f_op->check_flags(arg)] and returns
    whatever that answers.  So "[arg] names none of the five bits" does
    not by itself give [return 0] — it needs the separate fact that the
    callback cannot refuse.  In the whole kernel exactly two
    [file_operations] set it, [nfs_file_operations] and
    [nfs4_file_operations], both to [nfs_check_flags], whose entire body
    is [if ((flags & (O_APPEND | O_DIRECT)) == (O_APPEND | O_DIRECT))
    return -EINVAL;] — a rule stated over two bits that are BOTH inside
    the mask, so an [arg] this spec accepts satisfies it.  ext4, tmpfs,
    overlayfs and fuse leave [check_flags] NULL.  The arm is therefore
    sound on an NFS-mounted working directory too, but it is sound for
    that reason and not because of the mask.

    Every OTHER bit of [arg] is discarded by the closing
    [f_flags = (arg & SETFL_MASK) | (f_flags & ~SETFL_MASK)] and changes
    nothing observable — there is no [arg & ~valid] test anywhere in
    [setfl], so an unknown bit is never -EINVAL.  That is what makes the
    modeled arm below possible at all, and it is load-bearing that the
    test is a MASK rather than [arg = 0]: musl ORs O_LARGEFILE into the
    [arg] of every [F_SETFL] it issues ([fcntl], src/fcntl/fcntl.c, musl
    1.2.6), so an equality test would decline every musl call.

    (Linux v6.10-v6.15, fs/fcntl.c, [SETFL_MASK] / [setfl] — byte-identical
    over that range, and over v6.16 as well.) *)
Definition setfl_acted_on : Z :=
  (O_APPEND + O_NONBLOCK + FASYNC + O_DIRECT + O_NOATIME)%Z.

(** Does this [F_SETFL] leave the open file description exactly as it
    found it?  Two conditions, and BOTH are needed.

    [arg] names none of the bits [setfl] reads.  Then no test in [setfl]
    can fire and the closing assignment is the identity, so the call is a
    plain [return 0] whatever the file is.  [arg] survives the ABI
    boundary whole — it is declared [unsigned long], unlike [fd] and
    [cmd] — but [do_fcntl] then narrows it with [int argi = (int)arg]
    before calling [setfl(fd, filp, argi)], so the kernel only ever sees
    its low 32 bits.  The test below is taken over the whole 64-bit value
    and agrees anyway, because every bit of [setfl_acted_on] lies below
    2^32: masking commutes with the truncation.  A test that compared
    [arg] against a CONSTANT rather than masking would not have that
    property.

    And the fd is one the model itself opened.  Two of [setfl]'s tests
    read the file's CURRENT flags as well as [arg] —
    [((arg ^ filp->f_flags) & O_APPEND) && IS_APPEND(inode)] and
    [((arg ^ filp->f_flags) & FASYNC) && filp->f_op->fasync] — and once
    [arg] is clear of both bits, each reduces to "is this bit set in
    [f_flags]?".  (A third test names current flags too,
    [(arg & O_NOATIME) && !(filp->f_flags & O_NOATIME)], but [arg] closes
    that one on its own.)  So the arm needs O_APPEND and FASYNC clear in
    [f_flags], and for a file, directory or write-created fd that is a
    THEOREM rather than an assumption, in two parts because
    [Open.modeled_open_flags] has two: it strips
    [Open.open_ignored_flags] and then requires O_RDONLY or one of the
    write-create words, so such a word is a residue disjoint from
    the whole of [setfl_acted_on] ([modeled_open_flags_clear_of_setfl])
    together with ignored bits disjoint from those two
    ([open_ignored_flags_clear_of_setfl_current]).  Nothing else in the
    modeled surface can set either bit afterwards.

    THAT THEOREM COVERS EVERY ADMITTED WORD BUT THOSE CARRYING
    O_APPEND, and those are why this predicate has an [FdFileA] arm.
    [Open.append_create_flags] and the [Open.is_excl_append_create]
    words are admitted by [Open.modeled_open_flags] and their residues
    are NOT disjoint from [setfl_acted_on]: each contains O_APPEND, a
    bit of it.  What keeps the arms above sound is therefore not that
    every admitted word is clear, but that the words that are not mint
    a DIFFERENT fd kind -- [Open.openat_append_spec], under both words,
    hands back [State.FdFileA], which this
    match declines outright.  The remark below is stated over the other
    words for that reason, and the [FdFileA] arm carries the argument
    for these.

    O_NONBLOCK IS ADMITTED AND DOES REACH [f_flags], which is why the
    second of those remarks is stated over the two bits rather than over
    [setfl_acted_on] — over [setfl_acted_on] it would be FALSE.
    [Open.open_ignored_flags] carries the bit, so
    [openat(p, O_RDONLY|O_NONBLOCK)] and
    [openat(p, O_WRONLY|O_CREAT|O_TRUNC|O_NONBLOCK)] both mint modeled
    fds; and unlike O_CLOEXEC, which [build_open_flags] strips
    ([u64 strip = O_CLOEXEC; ... flags &= ~strip;]), O_NONBLOCK is absent
    from [do_dentry_open]'s
    [f->f_flags &= ~(O_CREAT | O_EXCL | O_NOCTTY | O_TRUNC);], so the
    open file description really records it.  It costs this arm nothing,
    and the reason is not that the bit is clear but that [setfl] HAS NO
    ERROR PATH KEYED ON IT: the bit appears in that function only in
    [SETFL_MASK], in the dead [if (O_NONBLOCK != O_NDELAY)] SunOS fixup,
    and in the closing assignment.  The [return 0] therefore holds
    whether the fd carries it or not.  (Linux v6.18.46, fs/open.c
    [build_open_flags] and [do_dentry_open]; fs/fcntl.c [setfl].)

    WHAT THE CLOSING ASSIGNMENT DOES TO SUCH AN FD is the caveat this
    predicate's name does not carry.  With [arg] clear of SETFL_MASK the
    assignment is [f_flags = f_flags & ~SETFL_MASK], which CLEARS a set
    O_NONBLOCK: on an fd opened with it, the call is a no-op on the
    return value and on everything the model records, but not on the
    real open file description.  No modeled execution can tell —
    [Uapi.O_NONBLOCK]'s own note walks the three ways a program could
    read the bit back and closes all three — and the change runs toward
    the blocking description the model already ascribes to that fd
    rather than away from it.  Should [Open.openat_spec] ever resolve a
    FIFO, a socket or a character device, that note fails first and this
    paragraph with it.

    A CHANNEL fd is different, and this is why the arm declines there.
    fds 0/1/2 arrive from whoever ran the binary, with the flags that
    process chose: [prog >> log] hands the program a stdout carrying
    O_APPEND, which makes [F_SETFL] with those bits clear an
    APPEND-CLEARING call, and -EPERM if the file is append-only.  The
    model has no way to know, so it declines rather than committing to
    the 0. *)
(** THE ARMS ARE ENUMERATED, with no wildcard.  A wildcard
    [| _ => Z.eqb ... 0] would be extensionally right for [FdFile],
    [FdFileW], [FdDir] and [FdSocket] ([FdChannel] has its own arm
    above) and silently WRONG for a kind such as a pipe end: it would be
    told that F_SETFL changes
    nothing here, an unsound ACCEPT rather than a decline, with no
    compile error and no proof to break.  Listing the kinds makes the
    next constructor a compile error instead -- the same move
    [Select.bits_all_pollable] and [Net.Socket.sockfd_lookup_errno]
    already make, and for the same reason. *)
Definition setfl_noop_on (e : FdEntry) (arg : word) : bool :=
  match e with
  | FdChannel _ => false
  | FdFile _ _ | FdFileW _ _ | FdFileRW _ _ | FdDir | FdSocket _ =>
      Z.eqb (Z.land (bv_unsigned arg) setfl_acted_on) 0
  | FdFileA _ _ => false
      (* AN APPEND FD IS THE CASE THIS ARM WAS WARNED ABOUT, and it is
         the one kind here whose [f_flags] provably CARRIES a bit
         [setfl] reads.  [State.FdFileA] is minted by
         [Open.openat_append_spec], under either of its two flag words,
         each containing O_APPEND,
         and [do_dentry_open] (fs/open.c, v6.18.46) clears only
         O_CREAT|O_EXCL|O_NOCTTY|O_TRUNC from [f_flags], so the bit is
         still there when [setfl] runs.  Two things then go wrong at
         once for an [arg] the four arms above would call a no-op:

         - [((arg ^ filp->f_flags) & O_APPEND) && IS_APPEND(inode)] no
           longer reduces to "is the bit set in [f_flags]?" answered
           [false] -- the xor is NONZERO precisely because [arg] is
           clear of a bit [f_flags] holds, so the answer turns on
           [IS_APPEND(inode)], the inode's append-only attribute, which
           this model does not carry.  On an append-only file the call
           is -EPERM;
         - and where it is not, the closing
           [f_flags = (arg & SETFL_MASK) | (f_flags & ~SETFL_MASK)]
           CLEARS O_APPEND.  Every later write through that fd then
           lands at [f_pos] rather than at end-of-file, and the model
           would go on answering for an append fd -- a confident wrong
           write POSITION, not a gap.

         Neither is something an open arm can fix from its own side, so
         the decline lives here.  Closing it needs the
         [f_flags] word recorded on the [FdEntry] (the change
         [getfl_f_flags] below already names) TOGETHER with an
         [IS_APPEND] notion in [State.v]; the second is not optional,
         since without it the -EPERM half stays undecidable. *)
  | FdDevNull _ _ => false
      (* FAIL-CLOSED.  The argument the file arms rest on carries its
         own exclusion: the paragraph above says the O_NONBLOCK a
         no-op [setfl] would clear is unobservable "should
         [Open.openat_spec] ever resolve a FIFO, a socket or a
         character device, that note fails first" — and /dev/null is a
         character device [Open.openat_spec] resolves.  A real
         answer would have to be derived from [setfl] (fs/fcntl.c,
         v6.18.46) over an [f_flags] word this entry does not record,
         and from the fact that [null_fops] (drivers/char/mem.c) reads
         none of the bits [setfl] can set; neither is written down
         here, so this declines. *)
  | FdUrandom => false
      (* FAIL-CLOSED, for the /dev/null reason: a character device the
         open resolves, whose [f_flags] word the entry does not record.
         [urandom_fops] (drivers/char/random.c, v6.18.46) reads none of
         the bits [setfl] can set — [urandom_read_iter] tests neither
         O_NONBLOCK nor IOCB_NOWAIT, unlike [random_read_iter] — so a
         no-op answer is derivable, and it is not written. *)
  | FdPipe _ _ => false
      (* FAIL-CLOSED, on the [FdChannel] side of this predicate rather
         than the [FdFile] side, and NOT because the flags are unknown.
         The argument the other four arms rest on is that no bit
         [setfl] acts on can be set on the fd already -- for a file
         that is a theorem about [Open.modeled_open_flags].  A pipe end
         has one too, and this arm is a CHOICE rather than a gap:
         [Fs.Pipe.pipe2_spec] declines every nonzero flag word, so every
         [FdPipe] the model can build was created with flags 0, and
         O_NONBLOCK, O_DIRECT and FASYNC are all provably clear on it.
         Answering 0 here would be sound today.  It is not done because
         the theorem is a fact about the ONE constructor that exists
         rather than about the fd kind, and it evaporates the moment
         pipe2 admits a flag: that admission would have to remember to
         come back here, and nothing makes it.  The remaining text says
         what would then be wrong.  pipe2 takes all three bits
         (fs/pipe.c [__do_pipe_flags] admits
         O_CLOEXEC|O_NONBLOCK|O_DIRECT|O_NOTIFICATION_PIPE, v6.18.46).
         O_DIRECT is the sharp one: it is in neither
         [Open.open_ignored_flags] nor any modeled open, so the
         disjointness remark this file proves does not reach it, and on
         a pipe O_DIRECT is not inert -- it is the PACKET-MODE bit,
         [is_packetized] being exactly [(f_flags & O_DIRECT) != 0]
         (fs/pipe.c, v6.18.46), and O_DIRECT is inside [SETFL_MASK], so
         the closing assignment CLEARS it on an [arg] this predicate
         would call a no-op.  Answering 0 for such a call would leave
         the model asserting nothing changed while the description
         switched out of packet mode, a confident wrong answer at the
         next read rather than a gap.  [FASYNC] runs the same way and
         has no theorem here either: [pipeanon_fops] carries
         [.fasync = pipe_fasync], so [setfl]'s
         [((arg ^ f_flags) & FASYNC) && filp->f_op->fasync] test is
         live on a pipe end where the modeled opens make it dead.
         Answering anything but [false] here needs pipe2 to RECORD the
         creation flags rather than decline them, so that the argument
         rests on the entry instead of on the sole constructor. *)
  | FdOpaque _ => false
      (* FAIL-CLOSED.  On an O_PATH descriptor F_SETFL is not in
         [check_fcntl_cmd]'s allow-list, so [SYSCALL_DEFINE3(fcntl)]
         answers -EBADF before [setfl] runs (fs/fcntl.c, read at
         v6.18.44; identical at v6.18.46); an eventfd's, a /proc/sys
         file's and a signalfd's [f_flags] word is not on the entry, and
         the /proc/self/fd directory's is, but [F_GETFL] reads it there
         ([getfl_f_flags]), so a write to it would have to be recorded.
         None of the answers is written. *)
  end.

(** The arithmetic half of the argument above, mechanized rather than
    asserted, and in two remarks because the predicate it is about has
    two halves.  This one is the RESIDUE: what is left of an admitted
    flag word once [Open.open_ignored_flags] is stripped is disjoint from
    [setfl_acted_on], so no bit [setfl] reads comes from the SHAPE the
    open was asked for.  Stated over the named words rather than
    quantified because [Open.modeled_open_flags] is an equality against
    a NAMED list — so widening it with a word whose residue meets
    [setfl_acted_on] leaves this remark true and no longer SUFFICIENT,
    which is the thing that has to be noticed.  The widenings since
    fall on both sides of that test.
    O_DIRECTORY is outside [setfl_acted_on], and the disjunct below is
    what says so rather than a reader checking two octal constants
    against each other.  [Open.append_create_flags] and the
    [Open.is_excl_append_create] words are NOT: their residues contain
    O_APPEND, they are deliberately absent from the disjunction below,
    and what covers them is [setfl_noop_on]'s [FdFileA] arm rather than
    this proof.  The two have to be read together.

    THE SIX O_RDWR WORDS ARE IN THE DISJUNCTION, on the O_DIRECTORY side
    of that test: O_RDWR, O_CREAT, O_TRUNC and O_EXCL are all outside
    [setfl_acted_on], so [setfl_noop_on] can put [State.FdFileRW] with
    the four kinds it answers 0 for rather than with [FdFileA].

    THE TWO O_NOCTTY WORDS ARE NOT IN IT AND NEED NOT BE
    ([Open.procfd_noctty_word]): they mint only [State.OProcFdDir], an
    opaque kind on which [setfl_noop_on] answers [false]. *)
Remark modeled_open_flags_clear_of_setfl : forall fl,
  (fl = 0%Z \/ fl = wr_create_flags \/ is_excl_create fl = true
   \/ fl = O_DIRECTORY \/ rdwr_open_word fl = true
   \/ is_rdwr_excl_create fl = true) ->
  Z.land fl setfl_acted_on = 0%Z.
Proof.
  intros fl [-> | [-> | [H | [-> | [H | H]]]]]; try reflexivity.
  - unfold is_excl_create in H.
    apply Bool.orb_true_iff in H as [H | H]; apply Z.eqb_eq in H; subst;
      reflexivity.
  - unfold rdwr_open_word in H.
    repeat (apply Bool.orb_true_iff in H as [H | H]);
      apply Z.eqb_eq in H; subst; reflexivity.
  - unfold is_rdwr_excl_create in H.
    apply Bool.orb_true_iff in H as [H | H]; apply Z.eqb_eq in H; subst;
      reflexivity.
Qed.

(** The other side of the same test, mechanized for the same reason: the
    words absent from the disjunction above really do carry O_APPEND, so
    leaving them out is forced and not an oversight.  Adding either to
    the remark above breaks its proof. *)
Remark append_open_words_carry_o_append : forall fl,
  (fl = append_create_flags \/ is_excl_append_create fl = true) ->
  Z.land fl O_APPEND = O_APPEND.
Proof.
  intros fl [-> | H]; [reflexivity|].
  unfold is_excl_append_create in H.
  apply Bool.orb_true_iff in H as [H | H]; apply Z.eqb_eq in H; subst;
    reflexivity.
Qed.

(** ...and this one is the STRIPPED BITS, the half a residue argument
    cannot see.  [Open.open_ignored_flags] is O_CLOEXEC, O_LARGEFILE and
    O_NONBLOCK, and O_NONBLOCK is a bit of [setfl_acted_on] that reaches
    [f_flags] — so what holds here is not disjointness from
    [setfl_acted_on], which is false, but disjointness from the two bits
    an [arg]-clear [setfl] still reads out of the file's current flags.
    Widening [Open.open_ignored_flags] with O_APPEND or FASYNC breaks
    this proof; widening it with a bit [setfl] merely masks does not,
    which is the boundary the arm actually depends on. *)
Remark open_ignored_flags_clear_of_setfl_current :
  Z.land open_ignored_flags (O_APPEND + FASYNC)%Z = 0%Z.
Proof. vm_compute. reflexivity. Qed.

(** ...and the truncation half.  [do_fcntl] narrows with
    [int argi = (int)arg] before [setfl] sees it, so the kernel reads
    only [arg]'s low 32 bits; [setfl_noop_on] masks the full 64.  The two
    agree exactly because no bit of the mask reaches the high half, and
    a bit added there later would silently break that. *)
Remark setfl_acted_on_fits_32 : (setfl_acted_on < 2 ^ 32)%Z.
Proof. vm_compute. reflexivity. Qed.

(** THE WHOLE OF A SOCKET'S [f_flags], which is what makes F_GETFL
    answerable on one fd kind and no other.

    [F_GETFL] is [err = filp->f_flags] — verbatim, with no mask (Linux
    v6.18.46, fs/fcntl.c [do_fcntl]).  So answering it means knowing that
    word exactly, and for a socket the model does, by a four-step chain
    every link of which is at that same commit:

      net/socket.c [sock_alloc_file] builds the file with
      [alloc_file_pseudo(SOCK_INODE(sock), sock_mnt, dname,
      O_RDWR | (flags & O_NONBLOCK), &socket_file_ops)];
      fs/file_table.c [alloc_file_pseudo] passes that word to
      [alloc_file], which passes it to [alloc_empty_file], which reaches
      [init_file]'s [f->f_flags = flags];
      and nothing on the way back sets another bit OF [f_flags] —
      [sock_alloc_file]'s own [file->f_mode |= FMODE_NOWAIT],
      [stream_open] (fs/open.c) and [file_set_fsnotify_mode] are all
      writes to [f_mode].

    The [flags] word reaching [sock_alloc_file] is
    [type & ~SOCK_TYPE_MASK] narrowed to [O_CLOEXEC | O_NONBLOCK]
    ([__sys_socket]'s [sock_map_fd(sock, flags & (O_CLOEXEC |
    O_NONBLOCK))]) or the accept4 argument, which [__sys_accept4_file]
    hands on whole.  O_CLOEXEC therefore DOES arrive there — it is
    dropped by the [O_RDWR | (flags & O_NONBLOCK)] expression itself,
    not withheld from the call — and separately reaches
    [get_unused_fd_flags], where it becomes the fd table's
    close-on-exec bit and nothing else.  So a socket's [f_flags] is
    [O_RDWR] plus O_NONBLOCK if and only if SOCK_NONBLOCK was asked for.

    TWO GATES CLOSE THAT, NOT THREE, and the count is worth getting
    right because the third looks like a gate and is not.
    [Net.Socket.socket_spec] and [Net.Socket.accept4_spec] each answer
    [unmodeled] when SOCK_NONBLOCK is set, and they are the ONLY two
    specs that put a [State.FdSocket] on a NEW fd
    ([State.init_model] seeds channels alone).  Six other sites
    [fd_insert] an [FdSocket] — bind, listen, shutdown, and the reset
    and connect transitions in [Fs.ReadWrite] — but each replaces an
    entry that already held one, so they move [State.SockState] and
    never create a file.  [Net.Socket.socketpair_spec] does not gate the bit
    at all — [Net.Socket.socketpair_flags_ok] admits it, matching
    [__sys_socketpair], which really does accept SOCK_NONBLOCK and still
    return [sock_no_socketpair]'s -EOPNOTSUPP for AF_INET — and it does
    not need to, because every triple it models ends in that errno with
    no descriptor handed back.  THAT IS THE CONDITION THAT WOULD
    FALSIFY THIS: its own comment names AF_UNIX as the arm that WOULD
    succeed and hand back a pair, and such an arm would mint
    [State.FdSocket]s carrying [O_RDWR | O_NONBLOCK] unless it declined
    SOCK_NONBLOCK first.  Until then, every [State.FdSocket] the model
    can reach carries exactly this word.

    NOTE WHAT IS NOT HERE: O_LARGEFILE.  A path open gets it from the
    SYSCALL ENTRY POINT, not from [build_open_flags], which never
    mentions the flag: [SYSCALL_DEFINE3(open)],
    [SYSCALL_DEFINE4(openat)], [SYSCALL_DEFINE4(openat2)] and
    [SYSCALL_DEFINE2(creat)] each do [if (force_o_largefile()) flags |=
    O_LARGEFILE;] BEFORE calling it (fs/open.c) — the same reading
    [Open.v] already records.  A socket is created by [socket] and
    [accept4], which are not those entry points and share no code with
    them, so a socket's F_GETFL answer does NOT carry the bit. *)
Definition socket_f_flags : Z := O_RDWR.

(** ...and the reason a word DERIVED from the constructor stays correct
    for the life of the fd, which a stored word would not need.  The
    only modeled writer of a socket file's [f_flags] is the empty
    [F_SETFL] above, whose closing assignment is
    [f_flags = (arg & SETFL_MASK) | (f_flags & ~SETFL_MASK)].  With
    [socket_f_flags] disjoint from [setfl_acted_on] — a SUPERSET of
    SETFL_MASK, see [Net.Socket.setfl_noop_declines_fasync] — that
    assignment is the identity on it, so a later F_GETFL still answers
    [O_RDWR].

    The other writers Linux has are out of reach rather than inert, and
    both ioctls are named because a reader will look for them.
    fs/ioctl.c [ioctl_fionbio] writes the field itself
    ([filp->f_flags |= flag] under [filp->f_lock]); [ioctl_fioasync]
    does NOT — it calls [filp->f_op->fasync] and says so in a comment,
    and the write happens two frames down in fs/fcntl.c
    [fasync_add_entry] / [fasync_remove_entry].  The distinction does
    not matter to the conclusion and is recorded because getting it
    backwards is how a later reader concludes the wrong thing about
    which function to check.  FIONBIO (0x5421) and FIOASYNC (0x5452) are
    both outside [Ioctl.tty_only_request], so [Ioctl.ioctl_spec] answers
    [unmodeled] for each; [Ioctl.v]'s own comment lists FIONBIO as
    deliberately unmodeled for this state.
    Nothing else in [Specs.spec_table] holds a file at all: [dup] and
    [dup3] mint a second descriptor onto the same description without
    writing to it, and the socket calls write [struct sock], not
    [struct file].  ADDING A MODELED FIONBIO OR FIOASYNC ARM BREAKS THIS
    ARM, not merely this comment. *)
Remark socket_f_flags_clear_of_setfl :
  Z.land socket_f_flags setfl_acted_on = 0%Z.
Proof. vm_compute. reflexivity. Qed.

(** [f_flags] of a /proc/self/fd directory opened with the word [fl]
    ([State.OProcFdDir]).  [SYSCALL_DEFINE4(openat)] adds O_LARGEFILE
    ([force_o_largefile] holds on riscv64), [build_open_how] keeps the
    word ([flags & VALID_OPEN_FLAGS]; no O_PATH), [build_open_flags]
    strips O_CLOEXEC and sets [op->open_flag], [alloc_empty_file] and
    [init_file] copy it into [f_flags], and [do_dentry_open] clears
    O_CREAT, O_EXCL, O_NOCTTY and O_TRUNC.  [F_GETFL] returns the rest
    ([do_fcntl]'s [err = filp->f_flags]).  No modeled call writes the
    field afterwards: [setfl_noop_on] declines F_SETFL on the kind.

    THE WORD IS ONE [Open.openat_proc_spec] ADMITTED, and the formula is
    exact for those words and no others: O_RDONLY with any of
    O_DIRECTORY, O_NOCTTY, O_NONBLOCK, O_CLOEXEC and O_LARGEFILE, and no
    other bit, so neither the [VALID_OPEN_FLAGS] mask nor [__O_SYNC]'s
    O_DSYNC can change it.
      fs/open.c [SYSCALL_DEFINE4(openat)], [build_open_how],
        [build_open_flags], [do_dentry_open]: read at v6.18.44; identical at v6.18.46.
      fs/file_table.c [alloc_empty_file], [init_file]: read at v6.18.44; identical at v6.18.46.
      fs/fcntl.c [do_fcntl]: read at v6.18.44; identical at v6.18.46. *)
Definition procfd_dir_f_flags (fl : word) : Z :=
  Z.ldiff (Z.lor (bv_unsigned fl) O_LARGEFILE) (O_CLOEXEC + O_NOCTTY).

(** What [F_GETFL] answers, per fd kind: [Some w] where the model can
    derive [filp->f_flags] exactly, [None] where it cannot.

    ENUMERATED, no wildcard, but for a WEAKER reason than
    [setfl_noop_on]'s and it is worth not overstating: the catch-all a
    reader would naturally write here is [_ => None], which falls on the
    DECLINING side and would be sound.  What it would cost is that a new
    [FdEntry] constructor — a pipe end, a timerfd — would silently
    inherit a decline nobody decided on, and for a pipe the flag word IS
    derivable the way a socket's is, per END: fs/pipe.c
    [create_pipe_files] builds the write end with
    [O_WRONLY | (flags & (O_NONBLOCK | O_DIRECT))] and the read end with
    [O_RDONLY | (flags & O_NONBLOCK)].  Enumerating
    makes that a compile error and so a decision.  In [setfl_noop_on]
    a catch-all would fall on the accepting side and be unsound; both
    are enumerated, for reasons of different strength.

    The four [None] kinds decline for two DIFFERENT reasons, and the
    difference is what says whether the gap is closable:

    - [FdChannel] — fds 0/1/2 arrive from whoever ran the binary,
      carrying the flags that process chose ([prog >> log] hands the
      program an O_APPEND stdout).  The environment picks the answer, so
      the model cannot, and no change to this file would let it.  Same
      line [setfl_noop_on] draws.
    - [FdFile], [FdFileW], [FdFileA], [FdFileRW], [FdDir] — [Open.openat_spec] accepts and
      IGNORES [Open.open_ignored_flags], and one of its three bits,
      O_NONBLOCK, REACHES [f_flags] and stays there.  So
      [openat(p, O_RDONLY)] and [openat(p, O_RDONLY|O_NONBLOCK)] mint
      the SAME [FdEntry] and have DIFFERENT F_GETFL answers: the word is
      not a function of the constructor for these three, and the model
      discarded the bit the answer is partly made of.  The other two
      ignored bits are not a problem and it is worth saying why, because
      one of them is easy to get backwards.
      [force_o_largefile] is [!IS_ENABLED(CONFIG_ARCH_32BIT_OFF_T)]
      (include/linux/fcntl.h), true on every riscv64 kernel, so
      O_LARGEFILE is a constant the model could supply;
      [Open.ftruncate_spec] leans on exactly that fact.  And O_CLOEXEC
      never reaches [f_flags] at all: [build_open_flags] strips it
      ([u64 strip = O_CLOEXEC; ... flags &= ~strip;], then
      [op->open_flag = flags], fs/open.c) while only the UNSTRIPPED
      [how->flags] reaches [get_unused_fd_flags], where the bit becomes
      the fd table's close-on-exec flag and nothing else; [f_flags] is
      [op->open_flag] verbatim ([alloc_empty_file(op->open_flag, ...)],
      fs/namei.c, then fs/file_table.c [init_file]), so
      [do_dentry_open]'s [f_flags &= ~(O_CREAT|O_EXCL|O_NOCTTY|O_TRUNC)]
      never had O_CLOEXEC to clear, and [F_SETFL] cannot add it —
      [SETFL_MASK] is
      [O_APPEND|O_NONBLOCK|O_NDELAY|O_DIRECT|O_NOATIME] (fs/fcntl.c).
      Linux has behaved this way since commit c6f3d8111598 "don't leak
      O_CLOEXEC into ->f_flags" (v3.7-rc1); /proc/PID/fdinfo has to
      re-add the bit from the fd table to report it.  So
      [openat(p, O_RDONLY)] and [openat(p, O_RDONLY|O_CLOEXEC)] have
      IDENTICAL F_GETFL answers.
      THIS DECLINE IS THEREFORE CLOSABLE, and by one change: an open
      flag word recorded on the [FdEntry] rather than derived from the
      constructor.  That change would also retire [Uapi.O_NONBLOCK]'s
      first bullet; a close-on-exec field beside it is what would
      narrow [F_GETFD] from its two answers to one.

    (Linux v6.18.46 throughout: fs/fcntl.c [do_fcntl] case [F_GETFL];
    fs/open.c [build_open_flags] and [do_dentry_open]; fs/file_table.c
    [init_file]; net/socket.c [sock_alloc_file].) *)
Definition getfl_f_flags (e : FdEntry) : option word :=
  match e with
  | FdSocket _ => Some (Z_to_bv 64 socket_f_flags)
  | FdChannel _ | FdFile _ _ | FdFileW _ _ | FdDir => None
  | FdFileRW _ _ => None
      (* the same reason as the four above, and no new one: the answer
         would have to name the O_LARGEFILE and O_CLOEXEC bits the open
         accepted and did not record *)
  | FdFileA _ _ => None
      (* declined for the [FdFile] reason and one more.  The ignored
         O_NONBLOCK is discarded here exactly as it is for the three
         kinds above; on top of that, this is the kind [setfl_noop_on]
         declines outright, so answering F_GETFL while declining F_SETFL
         on it would introduce exactly the mismatch the [FdPipe] arm
         below refuses to introduce *)
  | FdDevNull _ _ => None
      (* DECLINED for the [FdFile] reason: the word is the access mode
         [Open.openat_spec] granted plus O_LARGEFILE, plus an O_NONBLOCK
         the open may have passed and did not record
         ([Open.open_ignored_flags]).  The access mode IS on the entry,
         so a real answer would be
         [(if rd && wr then O_RDWR else if wr then O_WRONLY else
         O_RDONLY) + O_LARGEFILE], from [do_fcntl]'s [F_GETFL] arm
         (fs/fcntl.c, v6.18.46) over the [f_flags] [build_open_flags]
         and [do_dentry_open] leave — but only once the O_NONBLOCK bit
         is recorded too, which is the change the [FdFile] bullet
         names.  Answering without it would report a word the kernel
         does not hold for an open that passed the bit. *)
  | FdUrandom => None
      (* DECLINED for the same reason.  The access mode is O_RDONLY by
         construction, so a real answer would be [O_RDONLY +
         O_LARGEFILE] plus the O_NONBLOCK the open did not record — the
         same missing bit, the same decline. *)
  | FdPipe _ _ => None
      (* DECLINED THOUGH DERIVABLE TODAY, and the asymmetry with the
         [FdSocket] arm above is the thing to justify rather than the
         decline.  The word really is a function of the constructor:
         fs/pipe.c [create_pipe_files] builds the write end with
         [O_WRONLY | (flags & (O_NONBLOCK | O_DIRECT))] and the read end
         with [O_RDONLY | (flags & O_NONBLOCK)] (v6.18.46), and
         [Fs.Pipe.pipe2_spec] answers [unmodeled] for any nonzero flag
         word — so every [FdPipe] the model can build has [f_flags] of
         O_WRONLY when [writer] and O_RDONLY otherwise, exactly.
         Answering that would be sound.

         WHAT SEPARATES IT FROM THE SOCKET is how likely the premise is
         to move, not its shape.  A socket's premise is that
         [Net.Socket.socket_spec] and [accept4_spec] decline
         SOCK_NONBLOCK, and that decline is FORCED by something larger
         than this file: the model has no non-blocking mode at all, and
         [State.EAGAIN] records that as a project decision, so admitting
         the bit is not a change anyone makes without noticing.
         [pipe2_spec]'s decline of every nonzero flag is interim
         narrowness of a different kind — it declines O_CLOEXEC too,
         which cannot reach [f_flags] — so the premise here is one a
         later widening moves casually, and the widening that matters
         (O_NONBLOCK, O_DIRECT) reaches [f_flags] while the harmless one
         does not.  A reader of that future change has no reason to come
         back here.

         And the arm one screen up declined for the same premise.
         [setfl_noop_on]'s [FdPipe] arm is [false] on an argument that
         says so in as many words; answering F_GETFL while declining
         F_SETFL on the same constructor, in the same file, would make
         the pair read as a considered distinction when it is not one.

         CLOSING THIS IS A PIPE2 CHANGE, not an fcntl one: [pipe2_spec]
         recording its creation flags on the [FdEntry] makes both arms
         rest on the entry rather than on the sole shape pipe2 currently
         admits, and this arm and [setfl_noop_on]'s should move
         together when it does. *)
  | FdOpaque (OProcFdDir fl _) => Some (Z_to_bv 64 (procfd_dir_f_flags fl))
      (* ANSWERED: the /proc/self/fd directory records the open word, and
         [procfd_dir_f_flags] derives [f_flags] from it.  musl's
         [fdopendir] (src/dirent/fdopendir.c, musl 1.2.6) reads it with
         [fcntl(fd, F_GETFL)] to refuse an O_PATH descriptor before it
         lists the directory, so bubblewrap's [fdwalk] needs it *)
  | FdOpaque _ => None
      (* DECLINED.  F_GETFL is in [check_fcntl_cmd]'s allow-list, so an
         O_PATH descriptor answers its [f_flags] (O_PATH and the bits
         [build_open_how] kept); an eventfd's word is [O_RDWR] plus the
         EFD_ bits [do_eventfd] passes on; a signalfd's is [O_RDWR] plus
         the SFD_NONBLOCK bit [do_signalfd4] passes on; a /proc/sys
         file's is the open word; an [ONsFile]'s depends on its unknown
         object.  The entry records none of the five words exactly
         (fs/fcntl.c, fs/open.c, fs/eventfd.c, fs/signalfd.c, read at
         v6.18.44; identical at v6.18.46). *)
  end.

(** [fcntl fd cmd arg]: modeled for four commands, and fail-closed on
    every other one.  Three of the four are answered on every fd kind —
    [F_GETFD] with BOTH of the answers Linux can give, because the model
    does not record the bit it reports; the fourth, [F_GETFL], is
    answered on the kinds whose flag word is a function of the entry,
    and [getfl_f_flags] above holds that argument.

    Dropbear is the reason this exists.  It is the only fcntl caller in
    reach: this repository's own reference binaries are static,
    [-nostartfiles] and issue raw syscalls, and musl's start-up, stdio,
    malloc and exit paths reach fcntl only through [fopen] modes
    containing 'a' or 'e' and through the dynamic linker, none of which
    a static no-stdio binary has.  Dropbear's server issues exactly three
    shapes: [F_SETFD]/FD_CLOEXEC on the child socket before [fexecve]
    ([main_noinetd], src/svr-main.c), and the [F_GETFL]/[F_SETFL] pair
    of [setnonblocking] (src/dbutil.c).  Both at v2026.94.  The only
    other [fcntl] call sites in the tree are src/cli-session.c and
    src/scpmisc.c, which are the client and scp rather than the server —
    named so the claim is one grep rather than something to take on
    trust.

    WHICH OF THE THREE STOPS A REAL TRACE, AND WHERE.  [setnonblocking]
    reads before it writes — [fcntl(fd, F_GETFL, 0)], then
    [fcntl(fd, F_SETFL, fl | O_NONBLOCK)] — and it runs early:
    [common_session_init] (src/common-session.c) calls it on [sock_in]
    and [sock_out] and then on both ends of its signal pipe, before any
    protocol byte, and it is the first statement of [svr_session] for
    every connection.  [spawn_command] (src/dbutil.c) is the same call on
    the no-pty `ssh host cmd` path.

    THE F_GETFL ARM MOVES THAT WALL BY ONE SYSCALL AND NO FURTHER, and
    saying so is the point of this paragraph.  On the daemon path
    [sock_in] is the fd [accept4] handed over, a [State.FdSocket], so the
    read answers — [O_RDWR], per [socket_f_flags].  The very next
    call is [fcntl(fd, F_SETFL, fl | O_NONBLOCK)], which this spec
    declines, so the trace stops one line later inside the same
    function, on the same fd.  What the arm buys is therefore not
    dropbear coverage: it is that the remaining gap is exactly one
    thing, the absence of a non-blocking mode, rather than two.  (On the
    inetd path [sock_in] is fd 0, an [FdChannel], and the F_GETFL still
    declines there — the environment chose that flag word.)

    THE FD IS RESOLVED FIRST, whatever [cmd] is.
    [SYSCALL_DEFINE3(fcntl, ...)] resolves the descriptor with
    [fdget_raw(fd)] and returns -EBADF before [cmd] is looked at, so a
    closed or never-opened fd is -EBADF even for a command the kernel
    does not recognize — the ordering [Ioctl.ioctl_spec] follows for the
    same reason.  (Linux v6.10-v6.15, fs/fcntl.c,
    [SYSCALL_DEFINE3(fcntl, ...)] / [do_fcntl]: the entry function was
    respelled twice over that range, [f.file] to [fd_file(f)] at v6.12
    and [fdget_raw]/[goto out] to [CLASS(fd_raw, f)] at v6.13, but
    [CLASS(fd_raw, ...)] IS [fdget_raw] and the fd-before-cmd order is
    the same text at every tag.  [setfl], [SETFL_MASK] and the four
    [F_GETFD]/[F_SETFD]/[F_GETFL]/[F_SETFL] arms are byte-identical
    across the whole range.)

    [fd] and [cmd] both arrive already truncated to 32 bits — riscv64
    selects [ARCH_HAS_SYSCALL_WRAPPER], so [__SYSCALL_DEFINEx] casts each
    register to the declared [unsigned int] with [__SC_CAST] — see
    [Syscall.fd32] and [Syscall.cmd32].

    [F_SETFD] answers 0, for ANY [arg].  The kernel's arm is
    [set_close_on_exec(fd, argi & FD_CLOEXEC)] followed by an
    unconditional 0 — there is no error path, and only bit 0 of [arg] is
    consulted, so [F_SETFD, 0xdeadbeef] SETS the flag and [F_SETFD, 2]
    CLEARS it rather than being an unknown-flag error.

    The close-on-exec bit the call sets is NOT recorded, and that is
    sound rather than sloppy.  The bit has four readers in the kernel:
    [F_GETFD]; [do_close_on_exec] on the [execve] path; [alloc_bprm]'s
    use of the DIRFD's bit to set BINPRM_FLAGS_PATH_INACCESSIBLE for
    [execveat]; and [/proc/<pid>/fdinfo/<fd>], which reports it as
    O_CLOEXEC in its [flags:] line.  (Nothing INHERITS it: [dup], [dup2],
    [dup3], [F_DUPFD] and [F_DUPFD_CLOEXEC] each derive the new
    descriptor's bit from their own argument, so a later [dup] cannot
    make it observable either.)  The first is modeled below and admits
    BOTH values, so it holds whichever bit the program set.  The second
    and third are unreachable because execve and execveat are not
    modeled syscalls.  The fourth is
    unreachable for a different reason worth stating, because it is not
    about fcntl: [Open.openat_spec] answers a DETERMINISTIC -ENOENT for a
    path absent from the model's file-system image, and this assumes the
    image holds no /proc tree — so a program that reads its own fdinfo is
    REJECTED at the openat, not silently mis-answered here.  That is a
    standing limit on the whole file-system model, not a hole this arm
    opens.

    So no modeled execution is constrained by the difference between
    setting the bit and not: [F_GETFD] admits the same two answers
    either way.  Recording it would buy one thing, an [F_GETFD] that
    answers one value rather than two.  The honest caveat is that the
    [F_SETFD] arm buys nothing for the program that motivated it: Dropbear's
    [F_SETFD] is the setup for a [fexecve] the model declines one syscall
    later, so a conforming fcntl here must not be read as coverage of the
    close-on-exec story.

    [F_GETFD] answers 0 or FD_CLOEXEC, EITHER ONE, on every fd kind.
    The kernel's arm is [err = get_close_on_exec(fd) ? FD_CLOEXEC : 0]
    (Linux v6.18.46, fs/fcntl.c [do_fcntl]) — a bit of the fd TABLE, not
    of the open file description, and one this model does not hold:
    [State.FdEntry] has no field for it, [F_SETFD] above writes nothing,
    and a descriptor minted with O_CLOEXEC ([Open.openat_spec],
    [File.dup3_spec]) or SOCK_CLOEXEC ([Net.Socket.socket_spec],
    [Net.Socket.accept4_spec]) is the same entry as one minted without.
    So the arm offers both answers as an [alt].  That is sound for every
    program, because Linux's answer is one of the two; what it gives up
    is precision, since a program that BRANCHES on the bit has both
    continuations admitted.  [arg] is not read, by the kernel or here,
    and a closed fd is still -EBADF because the lookup runs first.
    Narrowing the arm to one answer needs a field for the bit and an
    [F_SETFD] arm that writes it, and that is what would make the
    O_CLOEXEC and SOCK_CLOEXEC ignores WRONG rather than merely narrow —
    so those decisions still stand or fall together.

    [F_SETFL] answers 0 exactly when it provably changes nothing — see
    [setfl_noop_on] — and declines otherwise.  The declined half is the
    interesting one: it contains Dropbear's own
    [fcntl(fd, F_SETFL, fl | O_NONBLOCK)].  The model has no
    non-blocking mode.  [ReadWrite.read_spec] and [ReadWrite.write_spec]
    describe a blocking stream and never return -EAGAIN, and
    [State.EAGAIN] records that as a deliberate project decision rather
    than an oversight, so answering 0 here and then answering a later
    [read] as if the fd were still blocking would be a confident wrong
    answer at the read rather than an honest gap at the fcntl.  Declining
    puts the gap where the program actually left the modeled world.

    EVERY OTHER COMMAND DECLINES, as does [F_GETFL] on the kinds it
    cannot answer:

    - [F_GETFL] is answered on [State.FdSocket] and on the /proc/self/fd
      directory ([State.OProcFdDir]), and declined on every
      other fd kind.  [getfl_f_flags] above carries the whole argument
      — the derivation of a socket's flag word, why a channel's is the
      environment's, and why the [openat] kinds lose the answer to
      an ignored O_NONBLOCK — so it is not restated here.
    - [F_DUPFD] / [F_DUPFD_CLOEXEC] are [dup] in disguise: they mint a
      second descriptor onto one open file description, which the fd
      table cannot express (an [FdEntry] carries its own offset, so two
      entries would drift apart where the kernel's share).
      THIS DECLINE IS LOAD-BEARING OUTSIDE THIS FILE, and that is the
      part worth carrying here rather than leaving in [State.v].
      [State.pipe_end_live] decides whether a pipe still has a reader or
      a writer by SCANNING the fd table; Linux keeps [pipe->readers] /
      [pipe->writers] and decrements them in [pipe_release] by the
      file's [f_mode] (fs/pipe.c:730-733, v6.18.46).  ONLY THE WRITER
      DIRECTION IS A SOUNDNESS EXPOSURE: miss a writer and
      [ReadWrite.read_spec]'s pipe arm takes its end-of-file branch and
      answers 0, where [anon_pipe_read] would have slept at its
      [wait_event_interruptible_exclusive] (fs/pipe.c:388, past the
      [if (!pipe->writers) break] at :370-371).  That is a modeled
      answer Linux would not give.  Missing a READER only fires the
      write arm's guard, which is [unmodeled] — a coverage loss.
      WHAT A NEW ARM OWES is an argument that the table's nonemptiness
      still tracks those counters.  There are two ways to give one, and
      declining is only the first: [File.dup_modeled_entry] and
      [Kernel.Fork.clone_no_shared_file_b] each carry an explicit
      [| FdPipe _ _ => false], while [State.pipe_end_live]'s own header
      argues that an arm which COPIES the table entry would also be in
      step — Linux's counters are per [struct file] and a duplication
      creates no new one, so a second entry answers [true] while either
      survives and [false] once both are gone, at the same moment
      [pipe_release] runs.  What is NOT available is adding the arm and
      saying nothing.
      AND THAT IS EXACTLY WHAT THIS DECLINE DOES TODAY.  [F_DUPFD] never
      reaches [File.dup_modeled_entry] — its only callers are
      [File.dup_spec] and [File.dup3_spec] — so what refuses it is the
      [unmodeled] at the bottom of [fcntl_spec], which is not
      pipe-specific and knows nothing about pipes.  It holds by nothing
      having been added rather than by anything having been decided,
      which is why [State.pipe_end_live] calls it the weak route.  (It
      is stated without a number on purpose: how many routes there are
      is a fact about the modeled surface, so a count here goes false
      the moment one is added or declined, silently and while still
      reading well.)
      Widening any command that CANNOT produce a second reference to one
      open file description is free of this; [F_GETFL] above is the
      worked example, being a load of [f_flags] and nothing else, and
      [F_GETFD] a second, reading one bit of the fd table.  The
      test is that, not whether the command is a read.
    - the record locks ([F_GETLK]/[F_SETLK]/[F_SETLKW], which glibc's
      utmp helper uses), owner and signal commands, leases, [F_NOTIFY],
      the pipe-size and seal commands: none has any state behind it here.

    One environment condition is outside the modeled resolutions:
    [security_file_fcntl] runs before [do_fcntl] and an enforcing LSM can
    fail the call there, receiving the full untruncated [arg].  This spec
    commits to its answers absolutely rather than offering an
    [Syscall.errno_from] alternative the way [Open.openat_spec] does, so
    under such a kernel every modeled arm is a false REJECTION rather
    than a fail-closed gap.  That is deliberate and matches
    [Ioctl.ioctl_spec], which faces [security_file_ioctl] and takes the
    same position; the model describes a kernel with no LSM registering
    these hooks.  Separately, an O_PATH fd ([State.OProcPath], minted
    by [Open.openat_proc_spec]) answers -EBADF for any command outside
    the allow-list of [check_fcntl_cmd] ([SYSCALL_DEFINE3(fcntl)],
    fs/fcntl.c, read at v6.18.44; identical at v6.18.46): [F_SETFD] and
    [F_GETFD] are on the list, so their kind-blind answers below hold
    for it too, and [F_SETFL] (not on the list) and [F_GETFL] decline
    on it through [setfl_noop_on] and [getfl_f_flags]. *)
Definition fcntl_spec (fd cmd arg : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* fd not open: real -EBADF, before [cmd] is examined *)
  | Some e =>
      if bv_eqb cmd F_SETFD then ret_only (Z_to_bv 64 0)
        (* always 0; the bit it sets is not recorded *)
      else if bv_eqb cmd F_GETFD
      then alt (ret_only (Z_to_bv 64 0)) (ret_only FD_CLOEXEC)
        (* the unrecorded bit: either of [do_fcntl]'s two answers *)
      else if bv_eqb cmd F_SETFL && setfl_noop_on e arg
      then ret_only (Z_to_bv 64 0)               (* a provably empty F_SETFL: real 0 *)
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | Some fl => ret_only fl                 (* the whole of [filp->f_flags], derived *)
        | None => unmodeled                      (* a kind whose flag word this model discarded,
                                                    or never had *)
        end
      else unmodeled                             (* every other command, and every
                                                    F_SETFL that would change something *)
  end.
