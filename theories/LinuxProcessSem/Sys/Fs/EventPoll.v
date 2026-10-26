(** * LinuxProcessSem.Sys.Fs.EventPoll — epoll_create1 (20), epoll_ctl (21), epoll_pwait (22)

    This file answers to Linux [fs/eventpoll.c]: it holds what the
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
(** [Fs.Select] is imported for ONE reason, and it is a check rather
    than a dependency of the semantics: [fd_can_poll_is_select_pollable]
    below pins that this file's [fd_can_poll] and [Select]'s
    [bits_all_pollable] stay complementary.  Both read the same kernel
    fact off the same descriptor kinds, and nothing else would notice
    if one moved and the other did not. *)
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Fs.Select.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** WHICH KERNEL THIS IS A MODEL OF.

    Cited by function name.  Every body quoted below was read from the
    pinned tree itself — stable v6.18.46, commit
    1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, this repository's kernel
    of record — rather than from a mainline tag standing in for it.  The
    tags below WERE fetched, and only to bound the windows: every text
    that is CITED is the pinned commit's, and where a tag's text is named
    as differing, that difference was read off the tag itself.  That distinction
    is not pedantry here: [fs/eventpoll.c] is NOT frozen across the
    6.18.x series.  A rework lands between v6.18.39 and v6.18.40 (a
    rewritten file banner, [linux/seqlock.h], an [ep_deliver_event]
    delivery path, and [ep_remove_safe] renamed to [ep_remove]) which
    mainline v6.19 does not carry.  So "v6.18.x behaves like mainline
    v6.18" is FALSE for this file, and a window written as a mainline
    range would be wrong for two of the functions below.

      fs/eventpoll.c              [do_epoll_create],
                                  [SYSCALL_DEFINE1(epoll_create1, ...)],
                                  [SYSCALL_DEFINE4(epoll_ctl, ...)],
                                  [do_epoll_ctl], [ep_check_params],
                                  [do_epoll_wait], [do_epoll_pwait],
                                  [SYSCALL_DEFINE6(epoll_pwait, ...)],
                                  [ep_timeout_to_timespec], [ep_poll],
                                  [is_file_epoll], [eventpoll_fops],
                                  [EP_MAX_EVENTS], [EPOLLEXCLUSIVE_OK_BITS]
      include/linux/poll.h        [file_can_poll], [vfs_poll]
      include/linux/eventpoll.h   [ep_op_has_event]
      include/uapi/linux/eventpoll.h
                                  [struct epoll_event], [EPOLL_PACKED],
                                  [EPOLL_CLOEXEC], [EPOLL_CTL_*]
      kernel/signal.c             [set_user_sigmask]
      include/linux/uaccess.h     [_inline_copy_from_user]
      include/asm-generic/access_ok.h
                                  [__access_ok]

    WINDOWS, per function, ending at the pinned commit.  Each was read
    by fetching [fs/eventpoll.c] at the tag and comparing the function's
    own text; the bound given is the earliest tag that matches AND whose
    successors all match, so a later regression cannot hide inside one.

      v6.18.40 - v6.18.46   [do_epoll_ctl].  A STABLE-POINT bound, not a
                            mainline one, and the only difference from
                            mainline v6.18's text is the
                            [ep_remove_safe] -> [ep_remove] rename
                            inside the EPOLL_CTL_DEL arm.  Nothing this
                            file models reaches that arm (see
                            [epoll_ctl_outcome]), so the rename is
                            invisible here — but the TEXT is not
                            byte-identical, and this repository pins
                            text.
      v6.18 - v6.18.46      [ep_poll].  It survived the .40 rework
                            byte-for-byte, so this one IS a genuine
                            mainline bound.
      v6.15 - v6.18.46      [ep_check_params] and [do_epoll_wait].  A
                            text-identity floor over the probe set, and
                            NOT a claim about when [ep_check_params] was
                            introduced -- nobody established that.
      v6.12 - v6.18.46      [do_epoll_create].
      at least v5.15        [do_epoll_pwait], [ep_timeout_to_timespec].
      at least v5.10        [SYSCALL_DEFINE1(epoll_create1, ...)],
                            [SYSCALL_DEFINE4(epoll_ctl, ...)],
                            [file_can_poll], [EP_MAX_EVENTS],
                            [EPOLLEXCLUSIVE_OK_BITS].

    "AT LEAST" IS NOT "UNCHANGED SINCE", and the difference is stated
    rather than smoothed over: v5.10 and v5.15 are the floors of the
    probe set, not established boundaries.  Those functions are
    byte-identical at every tag fetched down to that floor and may well
    go back further; nobody looked.  A reader who needs a real lower
    bound for one of them has to fetch it, and this sentence is what
    tells them the number here will not answer the question.

    WHERE THE ORDERING COMES FROM.  Every ordering claim below is read
    off the bodies of the functions named above and nowhere else.  No
    man page documents error-check ordering — epoll_ctl.2's ERRORS
    section is alphabetical by errno name, which is house style and not
    precedence — so nothing here is taken from a man page, and an
    enumeration of what a call refuses is not a claim about what it
    checks first.

    ON riscv64 THERE IS NO [epoll_create] AND NO [epoll_wait].  The
    generic 64-bit syscall table carries [epoll_create1] (20),
    [epoll_ctl] (21) and [epoll_pwait] (22) only; glibc and musl both
    compile [epoll_create(size)] to [epoll_create1(0)] and
    [epoll_wait(...)] to [epoll_pwait(..., NULL, 0)].  So the
    [size <= 0] check in [SYSCALL_DEFINE1(epoll_create, int, size)] is
    unreachable here and is not modeled.

    WHAT THIS FILE DOES NOT MODEL, AND WHY THAT IS THE WHOLE DESIGN.
    [epoll_create1]'s SUCCESS arm is declined.  Everything else follows
    from that one decision, so it is worth stating in full rather than
    as a gap.

    An epoll instance is an interest set plus a ready list, and
    [ep_poll] reports READINESS over the descriptors in it.  This model
    fixes readiness by construction for exactly the descriptor kinds
    that [epoll_ctl] REFUSES: [Select.bits_all_pollable] can answer for
    a file or a directory because [vfs_poll] hands back the constant
    [DEFAULT_POLLMASK] to any file with no [->poll] method, and
    [do_epoll_ctl] rejects precisely those descriptors with -EPERM
    because [file_can_poll] tests that same NULL [->poll].  The two
    predicates partition the descriptor kinds, and epoll gets the half
    this model cannot observe: a pipe's readiness is a function of what
    the peer has written SO FAR, which is wall-clock arrival, and
    [m_stdin] says which bytes will EVENTUALLY arrive, not which have.
    So pselect6's argument does not extend to epoll — it inverts.

    THAT LEAVES A CHOICE, AND THE OBVIOUS ONE IS A TRAP.  A nullary
    [State.FdEntry] constructor for an epoll fd would compile, and every
    [epoll_ctl] that could populate an interest set would decline, so no
    reachable state would have a non-empty one, so [epoll_pwait] could
    answer 0 on the empty set.  Every step of that is true today.  It is
    still the wrong shape, because the 0 rests on a WHOLE-TREE ABSENCE
    claim — "no modeled transition populates an interest set" — that the
    next change to this file silently falsifies: model one successful
    [EPOLL_CTL_ADD] and [epoll_pwait] keeps answering 0 for a set that
    is not empty, with no check failing anywhere.  A nullary
    constructor has no field to condition that answer on.  So the
    interest set is not represented, no [FdEntry] constructor denotes an
    epoll instance, and [epoll_create1] declines the arm that would mint
    one.

    WHAT THAT BUYS, and it is more than it sounds.  Because no fd in a
    modeled state is an epoll instance, [is_file_epoll] is FALSE for
    every descriptor the model can hand these syscalls — so both
    [epoll_ctl] and [epoll_pwait] reach their [-EINVAL] arm on every
    input that gets that far, and neither has any reachable path into
    the interest-set machinery at all.  What remains unanswered is
    small and is named on the arm that answers it: [epoll_ctl] declines
    a CHANNEL target, because whether a channel has a [->poll] is the
    one thing [fd_can_poll] cannot decide; [epoll_pwait] declines a real
    signal mask and a user range whose [access_ok] verdict the model
    cannot settle, both of which [pselect6] already declines for the
    same reasons.  Every other input to either is answered.

    That reach is load-bearing on a fact about a different type, so
    it is guarded by one: [fd_can_poll] is enumerated over
    [State.FdEntry] with no wildcard, so a new constructor is a COMPILE
    ERROR here.  Whoever adds one has to classify it, and the arm they
    have to write is the arm that decides whether the paragraph above
    still holds.

    WHAT THE DECLINE COSTS.  It costs priority 3 and nothing else: a
    program that successfully creates an epoll fd yields [unmodeled] at
    that call, so [Equivalence.strong_universal_T] says nothing about it
    either way, rather than saying something wrong.  Source and target
    are judged against the same model, so no pair of programs is
    separated by this; the class of programs the theorem covers is
    smaller by exactly those that reach a successful [epoll_create1]. *)

(** [EPOLL_CLOEXEC], and it is [O_CLOEXEC] rather than a value of its
    own: [include/uapi/linux/eventpoll.h] defines it as [O_CLOEXEC], and
    [do_epoll_create] opens with [BUILD_BUG_ON(EPOLL_CLOEXEC !=
    O_CLOEXEC)] so the identity is compile-enforced upstream rather than
    conventional.  Spelled through [Uapi.O_CLOEXEC] here for the same
    reason. *)
Definition EPOLL_CLOEXEC : Z := O_CLOEXEC.

(** [EPOLL_CTL_DEL].  The other two opcodes are deliberately absent:
    nothing below compares against [EPOLL_CTL_ADD] or [EPOLL_CTL_MOD],
    because every arm that distinguishes them sits past the -EINVAL
    this model always reaches first.  Naming them here would be a
    constant with no consumer. *)
Definition EPOLL_CTL_DEL : Z := 2%Z.

(** [sizeof(struct epoll_event)] on riscv64, and it is 16 rather than
    12.  [EPOLL_PACKED] is [__attribute__((packed))] only under
    [#ifdef __x86_64__]; every other architecture, riscv64 included,
    gets the empty definition, so the [__u64 data] member takes its
    natural 8-byte alignment and the struct carries four bytes of
    padding at offsets 4..7.  [SYSCALL_DEFINE4(epoll_ctl, ...)] copies
    [sizeof(struct epoll_event)] bytes, so it copies the padding too:
    an [event] pointer with twelve readable bytes and an unreadable
    thirteenth is -EFAULT. *)
Definition epoll_event_bytes : Z := 16%Z.

(** [EP_MAX_EVENTS], which is [INT_MAX / sizeof(struct epoll_event)] —
    so it is a function of the 16 above and is 134217727 here, not the
    178956970 an x86-64 reader would compute from a packed 12. *)
Definition EP_MAX_EVENTS : Z := 134217727%Z.

(** [file_can_poll], per descriptor kind: does this file have a
    non-NULL [->poll] method?  [None] where the model cannot say.

    ENUMERATED ON PURPOSE, no wildcard, and this is the guard the header
    note above rests on.  A [_ => Some false] catch-all would be
    extensionally identical today for the kinds it covers and would
    silently absorb the next [State.FdEntry] constructor — answering
    -EPERM for a descriptor epoll would happily accept, which is a
    modeled WRONG ANSWER rather than a decline.  Worse, an
    epoll-instance constructor absorbed here would leave
    [epoll_ctl_outcome] and [epoll_pwait_outcome] asserting -EINVAL for
    an epfd that IS an epoll fd, silently converting this file's
    reach argument into a false one.  Listing the kinds makes a new
    constructor a compile error instead, at the site whose answer decides
    both.

    WHY THIS IS AN [option bool] AND NOT A [bool].  [FdChannel] is the
    reason, and it is the one arm where being able to say nothing is
    what keeps the file sound.  The model does not know what a channel's
    far end IS.  [Fs.Stat]'s [fstat] arm declines a channel because
    "S_IFIFO, S_IFSOCK and S_IFCHR are all live and nothing in the model
    chooses between them"; [Fs.Ioctl]'s answer is earned by WIDENING
    over "whether the far end is a pipe, a terminal or a file"; and
    [State.FdEntry]'s own note calls the direction "an ASSUMPTION about
    the environment rather than a fact about the fd number".  A pipe, a
    terminal and a socket all define [->poll]; a REGULAR FILE and
    /dev/null do not — [null_fops] (drivers/char/mem.c) carries
    [.llseek], [.read], [.write], [.read_iter], [.write_iter],
    [.splice_write] and [.uring_cmd], and no [.poll].  So a channel
    spans both answers, and committing to either is a guess: [Some true]
    would answer -EINVAL where Linux answers -EPERM for a file-backed
    or /dev/null channel, and [Some false] would do the reverse for a
    pipe.  That is not hypothetical: plain shell redirection gives a
    program a regular file or /dev/null on fd 0 or 1 — so the wrong answer is one a reference program's launcher
    can reach.

    It is tempting to answer [Some true] because pipes define [->poll]
    unconditionally.  Pipes do; that answers the wrong question.
    What is unknown is not whether a pipe polls but whether a channel is
    a pipe.

    THE THREE [Some false] ARMS ARE AN ENVIRONMENT OBLIGATION, and it is
    the SAME obligation [Select.bits_all_pollable] carries — stated there
    at length.  Briefly: no
    DIRECTORY [file_operations] in the tree defines [->poll], and neither
    do the REGULAR-FILE operations of the ordinary on-disk and in-memory
    filesystems, which take the [generic_file_*] set.  That does NOT
    extend to [S_IFREG] in general — procfs installs
    [.poll = proc_reg_poll] on every regular file it creates
    (fs/proc/inode.c), and sysctl, kernfs, debugfs, tracefs, securityfs,
    POSIX message queues, ocfs2 dlmfs and FUSE all install one on
    [S_IFREG] inodes.  So a model state holding an [FdFile] for
    "/proc/self/mounts" would answer -EPERM here where Linux accepts the
    descriptor.  [Fs.valid_fs] admits such an image, so the model does
    not discharge the obligation, exactly as for pselect6; it is
    a model-vs-Linux fidelity gap rather than a break in the equivalence,
    since source and target are judged against the same model.

    THE [FdSocket] AND [FdPipe] ARMS NEED NO OBLIGATION, and they are the
    only ones that do not.  A socket's file is minted by
    [sock_alloc_file] with [socket_file_ops] (net/socket.c), whose
    [.poll] is [sock_poll] unconditionally, on every address family and
    every configuration.  A pipe end gets [pipeanon_fops] when
    [create_pipe_files] (fs/pipe.c) mints it and [pipefifo_fops] when a
    FIFO is opened; BOTH carry [.poll = pipe_poll], so the distinction
    that matters for [fstat] does not matter here.

    What separates these two from [FdChannel] is not the kernel but the
    model: it KNOWS these descriptors are a socket and a pipe, because it
    minted them itself in [Net.Socket.socket_spec] and [Fs.Pipe]'s
    [pipe2] arm.  A channel is handed to the process by whoever ran it,
    so there is a far end to be unsure about; here there is none. *)
Definition fd_can_poll (e : FdEntry) : option bool :=
  match e with
  | FdFile _ _ | FdFileW _ _ | FdFileA _ _ | FdFileRW _ _
  | FdDir => Some false
  | FdSocket _ | FdPipe _ _ => Some true
  | FdChannel _ => None
  | FdDevNull _ _ => None
      (* FAIL-CLOSED, though the answer is exact and this file already
         states it: [null_fops] (drivers/char/mem.c, v6.18.46) has no
         [.poll], so [file_can_poll] is false and [epoll_ctl] ADD is
         -EPERM (fs/eventpoll.c) — the [Some false] the file kinds
         carry, with no environment obligation at all.  Declined until
         written. *)
  | FdUrandom => None
      (* FAIL-CLOSED, and the answer is again exact: [urandom_fops]
         (drivers/char/random.c, v6.18.46) has no [.poll] either
         ([random_fops] has one; the urandom table does not), so
         [file_can_poll] is false and [epoll_ctl] ADD is the same
         -EPERM.  Declined until written. *)
  end.

(** The complement claim, as a check rather than a sentence.

    [Select.bits_all_pollable] asks whether a descriptor has the CONSTANT
    [DEFAULT_POLLMASK]; [fd_can_poll] asks whether it has a [->poll]
    method at all.  [vfs_poll] returns [DEFAULT_POLLMASK] exactly when
    [->poll] is NULL, so a descriptor is [Select]-pollable exactly when
    this file can say [Some false] — not by coincidence but because the
    two read one kernel fact, and a descriptor kind whose [->poll] status
    changes has to move in both files at once.

    THE THREE-VALUED FORM IS WHAT MAKES THIS TRUE RATHER THAN NEARLY
    TRUE.  A bare complement ([bits_all_pollable = negb (fd_can_poll e)])
    would force [FdChannel] onto one side, and the two files DECLINE it
    for the same reason from opposite directions: [Select] cannot fix a
    channel's readiness, and this file cannot fix whether a channel has a
    [->poll] to fix readiness with.  Reading one decline as the other's
    positive answer is exactly the error this lemma rules out.

    Stated over a one-entry table at bit 0, which is what
    [bits_all_pollable] scrutinises.  A prose assertion of this would go
    stale silently the first time someone classified a kind differently
    in one file; this does not. *)
Example fd_can_poll_is_select_pollable :
  forall e, bits_all_pollable [(Z_to_bv 64 0, e)] 1%Z 1%nat = true
            <-> fd_can_poll e = Some false.
Proof. intros [| | | | | | | | |]; vm_compute; split; congruence. Qed.

(** ------------------------------------------------------------------
    epoll_create1 (20)
    ------------------------------------------------------------------ *)

(** [do_epoll_create]:

      if (flags & ~EPOLL_CLOEXEC)
              return -EINVAL;
      error = ep_alloc(&ep);
      ...
      fd = get_unused_fd_flags(O_RDWR | (flags & O_CLOEXEC));

    ORDER, and it is the only behaviour this arm has: the flag word is
    judged BEFORE [ep_alloc] and before any descriptor is reserved.  So
    a rejected [epoll_create1] allocates nothing, consumes no fd number,
    and cannot answer -ENOMEM or -EMFILE — the two errnos that follow it
    are unreachable on this path rather than merely unmodeled.

    [flags] is an [int] in [SYSCALL_DEFINE1(epoll_create1, int, flags)],
    so the register's high half is discarded before a bit is read; the
    dispatcher applies [Syscall.flag32] and this function sees the low
    32 bits.  The mask is taken over 32 bits accordingly: a [flags] of
    2^32 is 0 after truncation and is ACCEPTED, where a 64-bit mask
    would reject it.

    THE SUCCESS ARM IS DECLINED, for the reason the header note gives at
    length: minting an epoll fd needs a [State.FdEntry] constructor, and
    the only constructor available without a readiness notion is a
    nullary one whose correctness rests on an absence claim the next
    change falsifies.  So this syscall is modeled on its rejecting half
    and nowhere else, and a program that successfully creates an epoll
    fd leaves the modeled surface at that call. *)
Definition epoll_create1_outcome (flags32 : word) : option word :=
  if Z.eqb (Z.land (bv_unsigned flags32) (Z.lnot EPOLL_CLOEXEC mod 2 ^ 32)) 0
  then None                            (* a well-formed create: declined *)
  else Some (errno_ret EINVAL).

Definition epoll_create1_spec (flags32 : word) : Sys SyscallEffect :=
  match epoll_create1_outcome flags32 with
  | None => unmodeled
  | Some r => pure (mkEffect r [] [])
  end.

(** ------------------------------------------------------------------
    the shared [copy_from_user] verdict
    ------------------------------------------------------------------ *)

(** What a fixed-size [copy_from_user] does, in three answers.

    [_inline_copy_from_user] (include/linux/uaccess.h) runs
    [access_ok(from, n)] and jumps to its failure path when that fails,
    so the RANGE check comes first and a range it rejects faults without
    a byte being read.  riscv64 takes that branch rather than the
    [can_do_masked_user_access()] one: [masked_user_access_begin] is not
    defined in arch/riscv/include/asm/uaccess.h at the pinned commit, so
    [include/linux/uaccess.h] gives [can_do_masked_user_access()] the
    value 0 and the address is never clamped.

    Two answers: [true] when the range check passes ([State.access_okb],
    the kernel's own predicate with [State.TASK_SIZE] as its limit) and
    every byte is mapped; [false] — -EFAULT — when the range check fails,
    or when it passes and some byte is unmapped.

    THE [access_okb] CONJUNCT IS ALSO WHAT RULES OUT THE WRAP.
    [State.read_bytes_map] walks in WORD arithmetic and wraps at 2^64, so
    a 16-byte read at 2^64 - 8 would read eight bytes from the top of
    the address space and eight from address 0 and report success, where
    the kernel's [access_ok] rejects the range outright.  Testing the
    range before reading is what stops that here; a site that reads
    without this test can still wrap. *)
Definition copy_from_user_ok (mp : word -> option byte) (a : word) (len : Z)
    : bool :=
  (access_okb a len
   && match read_bytes_map mp a (Z_to_bv 64 len) with
      | Some _ => true
      | None => false
      end)%bool.

(** ------------------------------------------------------------------
    epoll_ctl (21)
    ------------------------------------------------------------------ *)

(** [ep_op_has_event(op)] is [op != EPOLL_CTL_DEL], and it decides
    whether the syscall entry copies the event struct at all.  [op] is
    an [int], so the comparison is over the low 32 bits: a register whose
    low half is 2 and whose high half is set is still [EPOLL_CTL_DEL] to
    the kernel, because [SYSCALL_DEFINE4] casts the argument to [int] on
    the way in and the high half is gone before [op] is ever compared.
    THIS FUNCTION does not narrow — it is handed an already-narrowed
    word.  [Syscall.int32], applied once in the dispatcher arm, is that
    cast, and is where every truncated argument here is narrowed. *)
Definition ep_op_has_event (op32 : word) : bool :=
  negb (Z.eqb (bv_unsigned op32) EPOLL_CTL_DEL).

(** [epoll_ctl epfd op fd event] — the one outcome the model admits, or
    [None] where it declines.

    The arms are in the kernel's own decision order, so reading them top
    to bottom is reading [SYSCALL_DEFINE4(epoll_ctl, ...)] and then
    [do_epoll_ctl] in sequence.

    1.  [SYSCALL_DEFINE4] copies the event struct BEFORE calling
        [do_epoll_ctl], hence before any descriptor is looked up:

          if (ep_op_has_event(op) &&
              copy_from_user(&epds, event, sizeof(struct epoll_event)))
                  return -EFAULT;

        So -EFAULT on a bad [event] pointer BEATS -EBADF on [epfd],
        -EBADF on the target, and -EPERM.  For [EPOLL_CTL_DEL] no copy
        happens and [event] is never dereferenced, however wild it is —
        [epds] is left uninitialised in that case and the DEL path never
        reads it.
    2.  [-EBADF] if [epfd] is not open.
    3.  [-EBADF] if the target is not open.
    4.  [-EPERM] if the target has no [->poll]:

          /* The target file descriptor must support poll */
          if (!file_can_poll(fd_file(tf)))
                  return -EPERM;

        This is the arm worth knowing, because it sits BEFORE the check
        that [epfd] is an epoll fd.  So [epoll_ctl] on two ordinary
        files answers -EPERM, not -EINVAL: the epfd's epoll-ness is not
        tested until step 5, and a reader who assumed -EINVAL wins
        because "epfd isn't an epoll fd" would have the errno wrong.
    5.  [-EINVAL] otherwise:

          error = -EINVAL;
          if (fd_file(f) == fd_file(tf) || !is_file_epoll(fd_file(f)))
                  goto error_tgt_fput;

        No [State.FdEntry] constructor denotes an epoll instance, so
        [is_file_epoll(fd_file(f))] is false for every descriptor
        reachable here and the SECOND disjunct always holds.  The first
        disjunct — the self-add check, which compares [struct file]
        identity and therefore also catches adding a [dup] of the epfd —
        is consequently never the reason, and the model needs no notion
        of description identity to get this errno right.

    EVERYTHING PAST STEP 5 IS UNREACHABLE, which is why none of it
    appears below: the [EPOLLEXCLUSIVE] rejections, [ep_take_care_of_-
    epollwakeup], [epoll_mutex_lock], the [ep_loop_check] -ELOOP, and
    the whole [switch (op)] with its -EEXIST and -ENOENT arms all sit
    behind a [goto error_tgt_fput] that step 5 has already taken.  An
    unrecognised [op] is likewise -EINVAL through step 5 rather than
    through the switch's fallthrough — the same errno by a different
    route, which is why [op] is read here only to decide whether the
    event struct is copied.

    THE CONTENTS OF THE EVENT STRUCT ARE NEVER USED, only its
    readability.  [epds->events] is read exclusively by the
    [EPOLLEXCLUSIVE] block and by [ep_insert]/[ep_modify], all
    unreachable.  So this arm needs the copy's VERDICT and not its
    bytes.

    THE COPY IS RECORDED although its bytes are unused.
    [State.eff_copyins] is not bookkeeping about which bytes an arm
    consulted: [State.syscall_effect_accesses] concatenates it with the
    write ledger and [Run.sstep_syscall] hands the result to
    [State.materialize_model_accesses], which charges a first touch of a
    page of a lazy anonymous reservation against [vm_backing_used],
    reads included ([State.v]'s first-access accounting: an abstract
    backing guarantee, which charges a user load the same way).  The
    kernel reads the 16 bytes at [event] with [copy_from_user]
    ([SYSCALL_DEFINE4(epoll_ctl)], fs/eventpoll.c:2663-2665, v6.18.46)
    before [do_epoll_ctl] runs, so every answer after a successful copy
    carries [(event, 16)] ([epoll_ctl_reads]), as the same read done by
    a load instruction would.  A failed copy records nothing, the
    convention [Kernel.Signal.rt_sigprocmask_spec] states.

    ONE ARM DECLINES, named where it is decided: step 4 on a CHANNEL
    target, where [fd_can_poll] cannot say whether the far end has a
    [->poll].  Every other step answers. *)
Definition epoll_ctl_outcome (i : SyscallInput) (m : Model)
    (epfd : word) (op32 : word) (tfd : word) (event : word) : option word :=
  let after_copy :=
    match fd_lookup (m_fds m) epfd with
    | None => Some (errno_ret EBADF)
    | Some _ =>
        match fd_lookup (m_fds m) tfd with
        | None => Some (errno_ret EBADF)
        | Some te =>
            match fd_can_poll te with
            | Some false => Some (errno_ret EPERM)
            | Some true => Some (errno_ret EINVAL)
            | None => None        (* a channel: see [fd_can_poll] *)
            end
        end
    end in
  if ep_op_has_event op32
  then if copy_from_user_ok (in_mem i) event epoll_event_bytes
       then after_copy
       else Some (errno_ret EFAULT)
  else after_copy.

(** The copy-from-user ledger of [epoll_ctl_outcome]'s answer: the event
    struct, exactly when the syscall entry copied it and the copy
    succeeded. *)
Definition epoll_ctl_reads (i : SyscallInput) (op32 event : word)
    : list (word * nat) :=
  if (ep_op_has_event op32
      && copy_from_user_ok (in_mem i) event epoll_event_bytes)%bool
  then [(event, Z.to_nat epoll_event_bytes)]
  else [].

Definition epoll_ctl_spec (epfd op32 tfd event : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match epoll_ctl_outcome i m epfd op32 tfd event with
  | None => unmodeled
  | Some r => pure (with_copyins (epoll_ctl_reads i op32 event) (mkEffect r [] []))
  end.

(** ------------------------------------------------------------------
    epoll_pwait (22)
    ------------------------------------------------------------------ *)

(** [set_user_sigmask], kernel/signal.c, in its own order:

      if (!umask)
              return 0;
      if (sigsetsize != sizeof(sigset_t))
              return -EINVAL;
      if (copy_from_user(&kmask, umask, sizeof(sigset_t)))
              return -EFAULT;

    NULL is tested BEFORE the size, so [epoll_pwait(..., NULL, 0)] —
    which is what musl's and glibc's [epoll_wait] compile to — installs
    nothing and never looks at the 0.  Modeling only the size-8 case
    would leave [epoll_wait] itself outside the modeled surface.

    [sigsetsize] is a [size_t] and is compared FULL WIDTH, so it is not
    narrowed by the dispatcher; a register whose low half is 8 and whose
    high half is set is the wrong size.  [Uapi.kernel_sigset_bytes] is
    the 8.

    A mask that WOULD BE INSTALLED is [unmodeled], not an answer: this
    model has no signals, so it cannot represent [current->blocked]
    changing, nor the [restore_saved_sigmask_unless] that puts it back.
    [Select.pselect_sigpack] declines the identical case for the
    identical reason. *)
Inductive EpollSigmask :=
  | EpSigNone        (* [umask] is NULL: nothing installed *)
  | EpSigBadSize     (* wrong [sigsetsize]: -EINVAL *)
  | EpSigFault       (* [umask] unreadable: -EFAULT *)
  | EpSigReal.       (* a mask that would be installed: unmodeled *)

Definition epoll_sigmask (mp : word -> option byte) (umask sigsetsize : word)
    : EpollSigmask :=
  if w_is0 umask then EpSigNone
  else if negb (Z.eqb (bv_unsigned sigsetsize) kernel_sigset_bytes)
       then EpSigBadSize
       else if copy_from_user_ok mp umask kernel_sigset_bytes
            then EpSigReal
            else EpSigFault.

(** [epoll_pwait epfd events maxevents timeout sigmask sigsetsize] — the
    one outcome the model admits, or [None].

    ORDER, read off [SYSCALL_DEFINE6(epoll_pwait, ...)],
    [do_epoll_pwait], [do_epoll_wait] and [ep_check_params]:

    1.  [ep_timeout_to_timespec(&to, timeout)] is an ARGUMENT to
        [do_epoll_pwait], so it runs first — and it cannot fail.  It is
        also the only reader of [timeout], and its result reaches only
        [ep_poll], which no modeled path enters.  So [timeout] is not an
        argument of this function at all: no arm below depends on it,
        including the arms that would sleep.
    2.  [set_user_sigmask] — the first fallible step, and it precedes
        the epfd lookup.  A bad sigmask therefore BEATS a bad [epfd].
    3.  [-EBADF] if [epfd] is not open.  Note this precedes the
        [maxevents] check, which is the reverse of the [epoll_ctl]
        ordering and is worth stating because the two files' checks look
        interchangeable and are not.
    4.  [-EINVAL] if [maxevents <= 0 || maxevents > EP_MAX_EVENTS].
        [maxevents] is an [int], read signed, and the [<= 0] test is
        short-circuited FIRST on purpose: [EP_MAX_EVENTS] has type
        [size_t] through its [sizeof], so the second comparison promotes
        [maxevents] to [unsigned long], and a negative value would
        convert to a huge unsigned one and pass.  The order inside that
        [||] is load-bearing upstream, and it is why the signed test
        comes first here too.
    5.  [-EFAULT] if [access_ok(events, maxevents * sizeof(struct
        epoll_event))] fails.  The product is computed in 64-bit
        unsigned arithmetic (the [int] promotes to [size_t]) and CANNOT
        overflow, because step 4 has already bounded [maxevents] by
        [INT_MAX / 16].  This is a pure RANGE check — Linux reads no byte
        and requires no mapping — and so is the model's:
        [State.access_okb] on the product, with no walk.
    6.  [-EINVAL] if [epfd] is not an epoll fd.  It is not, ever, for
        the reason the header note gives, so every call that reaches
        step 6 answers -EINVAL and [ep_poll] is unreachable.

    NOTHING IS WRITTEN ON ANY MODELED PATH.  [ep_poll] is the only
    writer of the [events] array, through [ep_send_events], and step 6
    stops short of it.  The [access_ok] of step 5 is a range verdict and
    not a store. *)
Definition epoll_pwait_outcome (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : word) : option word :=
  match epoll_sigmask (in_mem i) sigmask sigsetsize with
  | EpSigBadSize => Some (errno_ret EINVAL)
  | EpSigFault => Some (errno_ret EFAULT)
  | EpSigReal => None
  | EpSigNone =>
      match fd_lookup (m_fds m) epfd with
      | None => Some (errno_ret EBADF)
      | Some _ =>
          let n := sint32 maxevents32 in
          if (n <=? 0)%Z then Some (errno_ret EINVAL)
          else if (EP_MAX_EVENTS <? n)%Z then Some (errno_ret EINVAL)
          else
            if access_okb events (n * epoll_event_bytes)
            then Some (errno_ret EINVAL)
            else Some (errno_ret EFAULT)
      end
  end.

Definition epoll_pwait_spec (epfd events maxevents32 sigmask sigsetsize : word)
    : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | None => unmodeled
  | Some r => pure (mkEffect r [] [])
  end.
