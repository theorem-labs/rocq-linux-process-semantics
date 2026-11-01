(** * LinuxProcessSem.Sys.Syscall — the syscall calling convention

    Every other file under [Sys/] answers to one kernel SOURCE file;
    this one answers to a kernel HEADER, [include/linux/syscalls.h], and
    holds what the specs share rather than any one syscall's behaviour.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** Return [r] with no memory writes. *)
Definition ret_only (r : word) : Sys SyscallEffect := pure (mkEffect r [] []).

(** Fail with errno [e] (a0 = -e). *)
Definition err_ret (e : Z) : Sys SyscallEffect := ret_only (errno_ret e).

(** Attach the copy-from-user ranges at the point where the syscall has
    actually performed them.  Keeping this in the effect distinguishes two
    paths that return the same errno before and after a user-memory read. *)
Definition record_copyins (reads : list (word * nat))
    (spec : Sys SyscallEffect) : Sys SyscallEffect :=
  eff <- spec ;; pure (with_copyins (reads ++ eff_copyins eff) eff).

Lemma record_copyins_ok : forall reads spec i m eff m' evs,
  spec i m (Ok eff m' evs) ->
  record_copyins reads spec i m
    (Ok (with_copyins (reads ++ eff_copyins eff) eff) m' evs).
Proof.
  intros. unfold record_copyins, bind, pure.
  exists eff, m', evs, []. repeat split; try exact H.
  now rewrite app_nil_r.
Qed.

Lemma record_copyins_ok_empty : forall reads spec i m eff m' evs,
  eff_copyins eff = [] ->
  spec i m (Ok eff m' evs) ->
  record_copyins reads spec i m (Ok (with_copyins reads eff) m' evs).
Proof.
  intros reads spec i m eff m' evs Hempty H.
  replace (with_copyins reads eff) with
    (with_copyins (reads ++ eff_copyins eff) eff) by now rewrite Hempty, app_nil_r.
  now apply record_copyins_ok.
Qed.

(** [record_copyins_ok] with the recorded effect stated as an equation,
    so that a nested ledger ([record_copyins] around a spec that records
    its own) can be matched by conversion rather than by unification. *)
Lemma record_copyins_ok_eq : forall reads spec i m eff m' evs effc,
  effc = with_copyins (reads ++ eff_copyins eff) eff ->
  spec i m (Ok eff m' evs) ->
  record_copyins reads spec i m (Ok effc m' evs).
Proof. intros reads spec i m eff m' evs effc -> H. now apply record_copyins_ok. Qed.

Lemma record_copyins_unmodeled : forall reads spec i m,
  spec i m Unmodeled -> record_copyins reads spec i m Unmodeled.
Proof. intros. unfold record_copyins. now left. Qed.

Definition outcome_copyins (reads : list (word * nat))
    (o : outcome SyscallEffect) : outcome SyscallEffect :=
  match o with
  | Ok eff m evs => Ok (with_copyins (reads ++ eff_copyins eff) eff) m evs
  | Unmodeled => Unmodeled
  end.

Lemma record_copyins_outcome : forall reads spec i m o,
  spec i m o -> record_copyins reads spec i m (outcome_copyins reads o).
Proof.
  intros reads spec i m [eff m' evs|] H; cbn.
  - now apply record_copyins_ok.
  - now apply record_copyins_unmodeled.
Qed.

(** An errno drawn from a syscall's realistic injectable set.  Failure
    injection is constrained PER SYSCALL: a failure branch may return
    only errnos the call can produce on a real kernel (per its man
    page), never an arbitrary value in 1..4095 — e.g. mmap can never
    fail with -EBADF.  Each syscall with an injectable failure carries
    its own small list below. *)
Definition errno_from (es : list Z) : Sys Z := choose (fun e => In e es).

(** EVERY errno from 1 to 4095 BUT -EINTR.  The one exception to the
    per-syscall rule above, for an arm whose kernel path runs through
    code whose errnos cannot be enumerated with confidence (a namespace
    clone's per-namespace init functions, a procfs lookup, a sysctl
    handler).  Each arm that draws from it says why a list would not be
    safe; a missing errno makes the model reject a real behaviour, while
    this set only admits more than Linux gives.

    WHY NOT -EINTR.  A call answers -EINTR only when it is interrupted:
    the restart codes ([ERESTARTSYS], [ERESTARTNOHAND],
    [ERESTART_RESTARTBLOCK]; include/linux/errno.h) become -EINTR only
    in [arch_do_signal_or_restart] when [get_signal] hands it a signal
    with a handler to run (arch/riscv/kernel/signal.c), and the code that
    returns -EINTR itself does so on [signal_pending]
    (include/linux/sched/signal.h: a pending unblocked signal, or
    TIF_NOTIFY_SIGNAL).  In a modeled run neither happens: the model
    installs no handler ([rt_sigaction] declines every handler install),
    and SCOPE.md's assumption "Nothing outside the process makes a
    signal pending for it, or wakes it as if one were" ("Assumptions
    that the model does not check") rules out the three outside agents
    that set one without a handler: another process's signal, freezing
    ([freeze_task] for suspend and the cgroup v1 freezer;
    [cgroup_freeze_task] for the cgroup v2 freezer, kept pending by
    [recalc_sigpending_tsk]), and a livepatch transition's
    [set_notify_signal].  The process's own child's SIGCHLD is no such
    agent: at SIG_DFL [sig_ignored] discards it, and while blocked it
    does not make [signal_pending] true.  Admitting -EINTR here would
    let the environment interrupt a call that bwrap retries without
    bound ([TEMP_FAILURE_RETRY]) forever.
      arch/riscv/kernel/signal.c [arch_do_signal_or_restart], [handle_signal]: read at v6.18.44; identical at v6.18.46.
      include/linux/errno.h [ERESTARTSYS], [ERESTARTNOHAND], [ERESTART_RESTARTBLOCK]: read at v6.18.44; identical at v6.18.46.
      include/linux/sched/signal.h [signal_pending]: read at v6.18.44; identical at v6.18.46.
      kernel/freezer.c [freeze_task]: read at v6.18.44; identical at v6.18.46.
      kernel/cgroup/freezer.c [cgroup_freeze_task]: read at v6.18.44; identical at v6.18.46.
      kernel/livepatch/transition.c [klp_send_signals]: read at v6.18.44; identical at v6.18.46.
      kernel/signal.c [sig_ignored], [recalc_sigpending_tsk]: read at v6.18.44; identical at v6.18.46.

    THE WARRANT, AND WHEN IT LAPSES.  -EINTR is left out because Linux
    cannot give it to any call of a modeled run TODAY: the model runs no
    signal handlers ([rt_sigaction] declines every handler install), and
    SCOPE.md assumes no signal arrives from outside the process.  The
    model still ADMITS -EINTR in one older place,
    [Kernel.Time.Hrtimer.nanosleep_spec]'s interrupted sleep: a widening
    (it admits more than Linux gives, so it is sound), which
    [Run.injected_table]'s note keeps on purpose for the forced-only
    filter.  It is not a reason to admit -EINTR here, where admitting it
    would let a retry loop run forever.  Whoever adds the first call
    that can REALLY be interrupted, or a way for a signal to arrive (the
    planned namespace and mount model's wait call and signal readiness), invalidates this
    exclusion and must put -EINTR back, or prove that call cannot see
    it.  [Checks.Sys.Prelude.errno_any_b] is the acceptor side and must
    move with this definition. *)
Definition errno_any : Sys Z := choose (fun e => (1 <= e <= 4095)%Z /\ e <> EINTR).

(** Word-against-zero test, used all over the dispatcher. *)
Definition w_is0 (w : word) : bool := bv_eqb w (Z_to_bv 64 0).

(** A positive count is not zero — the fact every arm that has to tell a
    real transfer from an empty one reaches for. *)
Lemma w_is0_pos : forall w : word, (0 < bv_unsigned w)%Z -> w_is0 w = false.
Proof.
  intros w H. unfold w_is0, bv_eqb. apply Z.eqb_neq.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
Qed.

(** …and the converse, which is the direction an ARM reads it in: past
    a [w_is0] gate the length is positive, and a spec that goes on to
    record a range derived from it is recording real bytes. *)
Lemma w_is0_false_pos : forall w : word,
  w_is0 w = false -> (0 < bv_unsigned w)%Z.
Proof.
  intros w H. unfold w_is0, bv_eqb in H. apply Z.eqb_neq in H.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H.
  pose proof (bv_unsigned_in_range 64 w). lia.
Qed.

(** The low 32 bits of a register, zero-extended back into a [word] —
    the C conversion an [int] / [unsigned int] syscall parameter
    performs on the 64-bit register it is passed.

    NAME: deliberately NOT [low32].  [Riscv.Sem.low32] already denotes
    the ISA's narrowing ([bv_extract 0 32 : word -> bv 32], the low half
    as a 32-bit value), and files such as [Common/FileSim.v] import both
    this module and [Riscv.Sem]; one token for two different types would
    be a reading hazard in exactly the files an auditor must read.  The
    two agree up to the zero-extension this one performs:
    [abi_low32 w = zext 64 (Riscv.Sem.low32 w)].  It is spelled out here
    rather than defined that way so the syscall layer does not depend on
    the ISA layer. *)
Definition abi_low32 (w : word) : word := Z_to_bv 64 (bv_unsigned w mod 2 ^ 32).

(** THE FILE DESCRIPTOR ARGUMENT IS 32 BITS.  An fd reaches the kernel
    in a full 64-bit register, but every syscall entry point declares it
    [unsigned int] / [int], so the high half is DISCARDED before the fd
    table is ever consulted (fs/read_write.c, fs/open.c, fs/file.c,
    fs/fcntl.c):

      read/write   [SYSCALL_DEFINE3(read, unsigned int, fd, ...)]
      close        [SYSCALL_DEFINE1(close, unsigned int, fd)]
      lseek        [SYSCALL_DEFINE3(lseek, unsigned int, fd, ...)]
      readv/writev declared [unsigned long, fd], but resolved through
                   [fdget_pos(unsigned int fd)] — truncated all the same
      openat       [SYSCALL_DEFINE4(openat, int, dfd, ...)]
      ioctl        [SYSCALL_DEFINE3(ioctl, unsigned int, fd, ...)]
      fcntl        [SYSCALL_DEFINE3(fcntl, unsigned int, fd, ...)]
      readlinkat   [SYSCALL_DEFINE4(readlinkat, int, dfd, ...)]
      dup          [SYSCALL_DEFINE1(dup, unsigned int, fildes)]
      dup3         [SYSCALL_DEFINE3(dup3, unsigned int, oldfd,
                   unsigned int, newfd, int, flags)] — BOTH fds

    So [write(2^32 + 1, buf, n)] really writes to STDOUT, and
    [close(2^32)] really closes stdin — matching a bare 64-bit compare
    against the fd table would instead have reported -EBADF, admitting a
    behavior no kernel produces and missing the one it does.

    [fd32] is that conversion.  ZERO-extension (rather than sign-) is
    faithful here even though [int] fds are signed: the model's fd table
    only ever holds fds <= 4096 ([State.alloc_fd]), so a low half at or
    above 2^31 — a negative [int] — matches no entry either way and is
    -EBADF, exactly as on Linux.

    The truncation is applied ONCE, in [syscall_spec] (and mirrored in
    [Checks/ExecutableSpecs.check_syscall] and
    [Checks/Progress.syscall_spec_witness]), at the ABI boundary where
    the kernel performs it; each per-syscall spec below therefore
    receives an fd that is already 32-bit. *)
Definition fd32 (fd : word) : word := abi_low32 fd.

(** [fd32] is the identity on every fd the model can hold or hand out
    (all of them below 2^32), which is what proofs about concrete fds
    need to see through the dispatcher's truncation. *)
Lemma fd32_id : forall fd : word, (bv_unsigned fd < 2 ^ 32)%Z -> fd32 fd = fd.
Proof.
  intros fd H. unfold fd32, abi_low32.
  rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 fd); lia).
  apply Z_to_bv_bv_unsigned.
Qed.

(** The bound the per-binary proofs already carry for the fds they hold
    (below 2^31, so an fd is never an error-encoded return — see
    [Checks/Checks.Sys.Prelude.errno_ret_in_fd]) is more than enough. *)
Lemma fd32_lt31 : forall fd : word, (bv_unsigned fd < 2 ^ 31)%Z -> fd32 fd = fd.
Proof.
  intros fd H. apply fd32_id.
  assert (Hle : (2 ^ 31 <= 2 ^ 32)%Z) by (vm_compute; discriminate). lia.
Qed.

(** lseek's origin selector is [unsigned int] too
    ([SYSCALL_DEFINE3(lseek, unsigned int, fd, off_t, offset,
    unsigned int, whence)], fs/read_write.c), so the kernel compares
    only the low half against SEEK_SET/SEEK_CUR/SEEK_END:
    [lseek(fd, 0, 2^32 | SEEK_END)] really seeks to end-of-file.
    Matching the full register would demand -EINVAL — a return no
    kernel produces. *)
Definition whence32 (whence : word) : word := abi_low32 whence.

(** ioctl's request is [unsigned int] as well
    ([SYSCALL_DEFINE3(ioctl, unsigned int, fd, unsigned int, cmd,
    unsigned long, arg)], fs/ioctl.c), and so is fcntl's command
    ([SYSCALL_DEFINE3(fcntl, unsigned int, fd, unsigned int, cmd,
    unsigned long, arg)], fs/fcntl.c) and flock's operation
    ([SYSCALL_DEFINE2(flock, unsigned int, fd, unsigned int, cmd)],
    fs/locks.c, Linux v6.18.46, commit 1f99e9ab748f).  All three share
    this conversion; the [arg] beside the first two is [unsigned long]
    and is NOT truncated.

    For flock the narrowing is not cosmetic, because its command word is
    tested BITWISE rather than by equality: [cmd & LOCK_MAND] and
    [cmd & ~LOCK_NB] both read a 32-bit value, so a caller that leaves
    bit 37 set gets Linux's answer for the low half rather than the
    -EINVAL a full-register test would invent. *)
Definition cmd32 (cmd : word) : word := abi_low32 cmd.

(** [clockid_t] is an [int] — [typedef int __kernel_clockid_t]
    (include/uapi/asm-generic/posix_types.h), reaching the syscall as
    [typedef __kernel_clockid_t clockid_t] (include/linux/types.h) —
    and [SYSCALL_DEFINE2]'s [__SC_CAST] casts the register to it
    ([SYSCALL_DEFINE2(clock_gettime, const clockid_t, which_clock,
    struct __kernel_timespec __user *, tp)],
    kernel/time/posix-timers.c; the body is identical at v6.10-v6.15).
    So the kernel compares only the low half of the register.  Same
    treatment as [fd32]/[whence32]/[cmd32]; zero-extension is faithful
    because every id the model interprets is a small positive constant,
    and a low half at or above 2^31 — a negative [clockid_t] — matches
    no modeled id either way and declines.  What is being declined there
    is wider than it looks: [clockid_to_kclock]
    (kernel/time/posix-timers.c, v6.10-v6.15) sends a negative id to
    the dynamic-posix-clock (clockfd) handler ONLY when
    [(id & CLOCKFD_MASK) == CLOCKFD] — both constants in
    include/linux/posix-timers_types.h — i.e. [id & 7 == 3]; every OTHER
    negative id goes to [clock_posix_cpu], the per-process and
    per-thread CPU clocks, several of which SUCCEED and write a
    timespec — [clock_gettime(-6, tp)] is [MAKE_PROCESS_CPUCLOCK(0,
    CPUCLOCK_SCHED)] and returns 0 on Linux.  So the negative half of
    the id space is mostly a live clock family the model does not
    cover, not a uniformly failing one, and declining it is fail-closed
    rather than agreement with an [-EINVAL].  Applied ONCE, in
    [Sys.SyscallTable.spec_table], at the ABI boundary where the kernel
    performs it; [clock_gettime_spec] receives an already-truncated
    id. *)
Definition clockid32 (clkid : word) : word := abi_low32 clkid.

(** [setsockopt]'s [level] and [optlen], [getsockopt]'s [level] and
    [shutdown]'s [how] are each a plain [int] in their [SYSCALL_DEFINE]
    (net/socket.c), so only the low 32 bits reach the kernel's own
    tests, exactly as for [fd].  The tests those four arguments feed
    are all EQUALITY or SIGN tests against small constants, and this
    model states them over [bv_unsigned] of the low half: "negative as
    an [int]" is "at least 2^31", and "one of 0/1/2" is membership in
    the low half.  Truncating rather than comparing the whole register
    is the SAME correction [whence32] records — a caller that leaves
    garbage in the high half of [a4] gets Linux's answer, not an
    -EINVAL no kernel produces. *)
Definition int32 (w : word) : word := abi_low32 w.

(** A credential id argument is 32 BITS.  Every credential entry point
    declares its arguments [uid_t] / [gid_t]
    ([SYSCALL_DEFINE1(setuid, uid_t, uid)] and its siblings,
    kernel/sys.c), so the high half of the 64-bit register is discarded
    before the kernel looks at the value — the reason [setuid(2^32)]
    sets the uid to 0 rather than failing.  Applied ONCE, in the
    dispatcher, exactly like [fd32]: the specs take ids already
    narrowed, so no arm can compare a 64-bit register against
    [Uapi.ID_MINUS_ONE] by accident. *)
Definition uid32 (u : word) : word := abi_low32 u.

(** A syscall flag word declared [int] rather than [unsigned] — dup3's
    ([SYSCALL_DEFINE3(dup3, unsigned int, oldfd, unsigned int, newfd,
    int, flags)], fs/file.c), unlinkat's
    ([SYSCALL_DEFINE3(unlinkat, int, dfd, const char __user *, pathname,
    int, flag)], fs/namei.c) and most of the older *at() calls',
    newfstatat's included ([SYSCALL_DEFINE4(newfstatat, int, dfd,
    const char __user *, filename, struct stat __user *, statbuf,
    int, flag)], fs/stat.c) — so the kernel never sees its high half,
    and the high half is discarded before any bit of it is tested: for
    unlinkat, before the [flag & ~AT_REMOVEDIR] test.

    This is a convention of the older syscalls, not a rule, and not one
    dup3 introduced: setxattr (5), lsetxattr (6), fsetxattr (7),
    eventfd2 (19) and epoll_create1 (20) all precede dup3 (24) with an
    [int] flags word, while the newer additions declare theirs unsigned
    — statx takes [unsigned], and renameat2, fchmodat2, open_tree,
    move_mount, statmount and listmount take [unsigned int].  The
    truncation is what matters here and it is identical either way.

    This one is applied in BOTH places, unlike [fd32]/[whence32]/[cmd32],
    which are only ever applied at the dispatcher.  [Sys.SyscallTable]
    narrows at the arm for [newfstatat] and [timerfd_create], whose flag
    words are read by nothing else; [Fs.File.dup3_flags_ok] and
    [Sys.Fs.Namei]'s flag tests apply it themselves instead.  For dup3
    that is because it is the only thing separating the model from a
    full-width flag test there — see that definition. *)
Definition flag32 (flag : word) : word := abi_low32 flag.

(** Linux's [int] parameter [n], as the kernel reads it.  The register
    is 64 bits wide but [SYSCALL_DEFINE6(pselect6, int, n, ...)] casts it
    to [int] before any comparison, so the high half is discarded and the
    low half is read as two's complement (see [fd32] for the same rule on
    file descriptors). *)
Definition nfds32 (n : word) : word := abi_low32 n.

(** ppoll's [nfds] is [unsigned int]
    ([SYSCALL_DEFINE5(ppoll, struct pollfd __user *, ufds, unsigned int,
    nfds, ...)], fs/select.c), so the same 32-bit truncation applies and
    the result is read UNSIGNED.  Kept apart from [nfds32] above rather
    than shared with it: the two words are narrowed identically and read
    OPPOSITELY, and [do_sys_poll]'s first test — [nfds] against
    [rlimit(RLIMIT_NOFILE)] — is an unsigned comparison, so a register
    whose low half has bit 31 set is a huge count and not a negative
    one. *)
Definition unfds32 (nfds : word) : word := abi_low32 nfds.

Definition nfds_signed (n32 : word) : Z :=
  let v := bv_unsigned n32 in
  if (v <? 2 ^ 31)%Z then v else (v - 2 ^ 32)%Z.
(** [socket], [bind], [listen], [accept4] all take [int] arguments, and
    their range checks are SIGNED ([family < 0], [protocol < 0],
    [addrlen < 0]).  [abi_low32] gives the unsigned low 32 bits; this
    reads the same bits as a signed [int]. *)
Definition sint32 (w : word) : Z :=
  let u := bv_unsigned (abi_low32 w) in
  if (u <? 2 ^ 31)%Z then u else (u - 2 ^ 32)%Z.

(** rt_sigprocmask's [how] is [int]
    ([SYSCALL_DEFINE4(rt_sigprocmask, int, how, sigset_t __user *, nset,
    sigset_t __user *, oset, size_t, sigsetsize)], kernel/signal.c), so
    [sigprocmask]'s [switch (how)] compares only the low half against
    SIG_BLOCK, SIG_UNBLOCK and SIG_SETMASK.  Its [sigsetsize] is
    [size_t] and is deliberately NOT narrowed here: it is compared
    full-width, so a register whose low half is 8 is still the wrong
    size. *)
Definition how32 (how : word) : word := abi_low32 how.

(** wait4's [upid] is a [pid_t], which is an [int]
    ([SYSCALL_DEFINE4(wait4, pid_t, upid, int __user *, stat_addr, int,
    options, struct rusage __user *, ru)], kernel/exit.c), so the kernel
    compares only the low half of the register — exactly as [fd32] and
    [whence32] describe for their own arguments.  Applied ONCE, in the
    dispatcher's arm. *)
Definition pid32 (upid : word) : word := abi_low32 upid.

(** wait4's [options] is an [int] in the same prototype, and the
    kernel's validation is a bitwise test on it, so the high half is
    discarded before any bit is read. *)
Definition waitopts32 (options : word) : word := abi_low32 options.

(** pipe2's flag word is an [int]
    ([SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags)],
    fs/pipe.c), so only its low 32 bits reach the mask test. *)
Definition pipe_flags32 (flags : word) : word := abi_low32 flags.
