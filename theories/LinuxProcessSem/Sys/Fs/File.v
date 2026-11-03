(** * LinuxProcessSem.Sys.Fs.File — the fd table, dup (23), dup3 (24), close_range (436)

    This file answers to Linux [fs/file.c]: it holds what the kernel
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

(** The kernel returns the LOWEST free descriptor, as Linux does
    (e.g. after close(1), the next open returns fd 1) — computed by
    [State.alloc_fd].  The choice set is a singleton (no nondeterminism);
    the freeness conjunct only empties it in the unreachable case where
    [alloc_fd]'s scan bound (4096 fds) is exhausted, leaving just the
    errno alternative — as real kernels fail with -EMFILE at RLIMIT_NOFILE
    well before that.  [alloc_fd fds <= 4096] keeps an fd from ever being
    confused with an error-encoded return. *)
Definition lowest_fd (fds : list (word * FdEntry)) : Sys word :=
  choose (fun fd => fd_lookup fds fd = None /\ fd = alloc_fd fds).

(* =========================================================================
   Descriptor duplication: dup (23) / dup3 (24)
   ========================================================================= *)

(** WHAT DUPLICATION SHARES, AND WHAT THIS MODEL CAN NAME.

    [dup] and [dup3] install a second descriptor for the SAME OPEN FILE
    DESCRIPTION: [SYSCALL_DEFINE1(dup)] hands [fd_install] the very
    [struct file] pointer the old fd holds, and [do_dup2] stores that
    same pointer at [newfd] after a [get_file] (fs/file.c).  The file
    OFFSET [f_pos] and the status flags [f_flags] are fields of that
    [struct file] (include/linux/fs.h), so the two fds read and advance
    ONE offset; only the close-on-exec bit is per-descriptor, living in
    the descriptor table's [close_on_exec] bitmap rather than in the
    description (include/linux/fdtable.h, [struct fdtable],
    byte-identical v5.4..v7.2).

    This model keeps the offset INSIDE the per-fd entry
    ([State.FdEntry]: [FdFile p offset]), so it cannot name one
    description from two fds.  Duplication is therefore modeled exactly
    for the entries that carry NO per-description state, and declines
    for the two that do:

    - [FdChannel ch] carries only the channel id.  A channel's read
      position is the model-wide [m_stdin] and its writes are trace
      events, so two fds naming one channel already share everything a
      description shares: copying the entry IS the sharing.
    - [FdDir] is nullary, and no modeled arm observes a directory
      position: [ReadWrite.lseek_spec] declines on [FdDir], and
      [Readdir.getdents64_spec] declines every listing, answering only
      where the buffer has no room for an entry — which is the arm that
      moves no position.
    - [FdFile]/[FdFileW]/[FdFileRW] carry [offset], which read, readv,
      write, writev and lseek rewrite in place.  Copying such an entry would
      give the two fds INDEPENDENT offsets, so
      [fd2 = dup(fd1); read(fd1, b, 4); read(fd2, b, 4)] would deliver
      bytes 0..3 twice where Linux delivers 0..3 and then 4..7 — a
      confident wrong answer rather than a gap.  Duplicating a FILE fd
      is [unmodeled].  The fix is an open file description layer in
      [State.v], where an [FdEntry] names a description by id instead
      of carrying its mutable state.
    - [FdSocket] carries the connection's remaining receive script, and
      a read rewrites it in place — [ReadWrite.read_delivery_clamped]
      consumes the byte, and the -ECONNRESET and -ETIMEDOUT arms move
      the entry to [SkReset].  Copying it is the [FdFile] mistake with
      a different payload: the two fds would each report the peer's
      reset once, where Linux reports it once for the connection.  So
      duplicating a SOCKET fd is [unmodeled] too, and the same open
      file description layer fixes both. *)
Definition dup_modeled_entry (e : FdEntry) : bool :=
  match e with
  | FdChannel _ | FdDir => true
  | FdFile _ _ | FdFileW _ _ | FdSocket _ => false
  (* AN APPEND FD DECLINES WITH THEM, and this one is a CHOICE rather
     than the [FdFile] argument repeated.  A write through an
     [FdFileA] does not read [offset] at all -- it lands at
     [i_size_read(inode)] -- so copying the entry would NOT give the
     two fds independent write positions, and the [FdDir] argument
     ("every syscall that could observe the per-description state is
     already declined") would carry it if [ReadWrite.lseek_spec]
     declined this kind.  It does not: lseek repositions and REPORTS
     [f_pos] on an append fd exactly as on any other, so
     [fd2 = dup(fd1); lseek(fd1, 0, SEEK_SET); lseek(fd2, 0, SEEK_CUR)]
     answers 0 on Linux, where two copied entries would answer the old
     position.  That is the [FdFile] mistake with the read path removed,
     so this arm takes the [FdFile] answer, and it is the lseek arm and
     not the write arm that puts it there. *)
  | FdFileA _ _ => false
  | FdFileRW _ _ => false
  (* AN O_RDWR FD IS THE [FdFile] ARGUMENT UNCHANGED, and it is the
     kind that argument fits best rather than an extension of it: the
     entry carries one [offset] that read, readv, write, writev and
     lseek all rewrite in place, so copying it would give the two fds
     independent positions in BOTH directions.
     [fd2 = dup(fd1); read(fd1, b, 4); write(fd2, b, 4)] writes at 4 on
     Linux, where two copied entries write at 0.  The open file
     description layer named above is what fixes it here too. *)
  (* A PIPE END DECLINES, and it is NOT the [FdChannel] case even
     though [FdPipe] carries no offset either.  What a pipe end names
     is a [pipe_inode_info] with a reader and a writer COUNT, and
     [do_dup2]'s [get_file] adds a reference without touching either
     (fs/file.c, v6.18.46): after [dup] the pipe still has one writer,
     so closing ONE of the two write-end fds must NOT deliver EOF to
     the reader, where closing both must.  [FdChannel] has nothing of
     the kind to get wrong -- its position is the run's [m_stdin] and
     its writes are trace events, so copying the entry IS the sharing.
     Modeling a duplicated pipe end therefore needs an end COUNT, or
     the open file description layer the [FdFile] paragraph above
     already names; with neither, the number of live ends would have to
     be read off the fd table, and [dup] is exactly the operation that
     makes that reading wrong.
     So this fails closed rather than copying the entry. *)
  | FdPipe _ _ => false
  (* /dev/null IS THE [FdChannel] CASE WITH NOTHING TO SHARE AT ALL.
     [do_dup2]'s [get_file] (fs/file.c, v6.18.46) makes the new fd a
     second reference to the one [struct file], so the two share its
     [f_pos] and [f_flags]; what makes copying the entry exact is that
     no modeled arm can observe either on this kind.  [f_pos] is pinned
     at 0 by [null_lseek] and never advanced by [read_null] or
     [write_null] (drivers/char/mem.c), so [ReadWrite.lseek_spec]
     answers 0 through either fd whatever the other did; [f_flags] is
     read by nothing, since [Fcntl.getfl_f_flags] and
     [Fcntl.setfl_noop_on] both decline this kind; and there is no
     count to keep in step, because a device node has no reader or
     writer count for a close to move.  The access mode the entry
     carries is per [struct file] too, and a copy carries the same
     one.  So copying IS the sharing, as for a channel. *)
  | FdDevNull _ _ => true
  (* /dev/urandom COPIES TOO, and the argument is /dev/null's with one
     more thing to check.  The two fds share the one [struct file]
     ([do_dup2]'s [get_file]); its [f_pos] is pinned at 0 on this kind
     ([noop_llseek], fs/read_write.c, returns it and [urandom_read_iter],
     drivers/char/random.c, never moves the [kiocb]'s [ki_pos],
     include/linux/fs.h; all Linux v6.18.46), and
     [f_flags] is read by nothing modeled ([Fcntl.getfl_f_flags] and
     [Fcntl.setfl_noop_on] both decline the kind).  The one more thing
     is the BYTES: a read through either fd takes the front of the
     device's declared stream, [State.m_urandom], which is the model's
     and not the entry's — so two references and two separate opens
     read the same stream in the same order, exactly as two [struct
     file]s on the random device draw from one generator.  Copying the
     entry loses nothing. *)
  | FdUrandom => true
  (* THE FOUR OPAQUE OBJECTS DECLINE.  [SYSCALL_DEFINE1(dup)]'s
     [fget_raw] accepts an O_PATH file too (fs/file.c, read at
     v6.18.44; identical at v6.18.46), so Linux duplicates all four.
     Copying the entry would be exact for [OProcPath] (nothing modeled
     reads its [f_pos] or [f_flags]) and for [OProcFile] (each read's
     bytes are the environment's whatever the shared offset), and for an
     eventfd it would be a second reference to one counter, which no
     modeled arm reads.  An [ONsFile] is declined so that no arm of this
     model mints one.  None of that is needed, so it is not written. *)
  | FdOpaque _ => false
  end.

(** dup's injectable failures: fd-table exhaustion at RLIMIT_NOFILE
    (EMFILE, which also keeps the spec receptive when no free fd
    exists) and a descriptor table the kernel cannot grow (ENOMEM, from
    [alloc_fdtable], fs/file.c — its shape changed at v6.13, from a bare
    NULL to an ERR_PTR, but the errno set [alloc_fd] can raise did not).
    ENFILE is NOT among them: dup allocates no [struct file] — it takes
    a second reference to an existing one — so the system-wide
    open-file limit cannot bite.  EBADF is not injectable either: fd
    validity IS tracked. *)
Definition dup_errnos : list Z := [ENOMEM; EMFILE].

(** [dup oldfd]: a second descriptor for [oldfd]'s description, at the
    LOWEST free fd, returned.

    ORDER, from [SYSCALL_DEFINE1(dup, unsigned int, fildes)] (fs/file.c,
    byte-identical v5.9..v7.2): [fget_raw] runs FIRST, so a closed
    [oldfd] is -EBADF BEFORE any allocation — [dup] of a bad fd on a
    full table is -EBADF, never -EMFILE.  Only then does
    [get_unused_fd_flags(0)] take the lowest free slot ([lowest_fd],
    i.e. [State.alloc_fd]), which is where the two injectable failures
    live.  [fget_raw] (not [fget]) means an O_PATH fd is dup-able too;
    [dup_modeled_entry] declines the model's one O_PATH kind
    ([State.OProcPath]), so nothing turns on it.  The new
    descriptor's close-on-exec bit is cleared, [flags] being 0.

    [oldfd] arrives already truncated to 32 bits (see
    [Syscall.fd32]), so [dup(2^32)] duplicates stdin and [dup(-1)] is
    -EBADF. *)
Definition dup_spec (oldfd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) oldfd with
  | None => err_ret EBADF
  | Some e =>
      if negb (dup_modeled_entry e) then unmodeled
      else
        alt (er <- errno_from dup_errnos ;; err_ret er)  (* untracked env failure or no free fd *)
            (fd <- lowest_fd (m_fds m) ;;
             set_fds (fd_insert (m_fds m) fd e) ;;
             ret_only fd)
  end.

(** [(flags & ~O_CLOEXEC) == 0] — [ksys_dup3]'s first test, on the
    TRUNCATED word.

    The truncation ([Syscall.flag32]) is applied HERE rather than at
    the dispatcher, where [fd32]/[whence32]/[cmd32] are applied, because
    here it is the only thing separating this model from a kernel that
    tested the full 64-bit argument: [SYSCALL_DEFINE3(dup3, unsigned int,
    unsigned int, int flags)] discards the high half, so dup3(2, 1, 2^32)
    returns 1 (fs/file.c, v6.18.46).  A caller reaching
    [dup3_spec] without the truncation would answer -EINVAL there. *)
Definition dup3_flags_ok (flags : word) : bool :=
  Z.eqb (Z.ldiff (bv_unsigned (flag32 flags)) O_CLOEXEC) 0.

(** [dup3 oldfd newfd flags]: install [oldfd]'s description at [newfd],
    silently closing whatever [newfd] held, and return [newfd].

    ORDER, from [ksys_dup3] (fs/file.c, byte-identical v5.11..v7.2),
    followed exactly:

    1. [(flags & ~O_CLOEXEC) != 0] is -EINVAL, before anything else.
    2. [oldfd == newfd] is -EINVAL — unconditionally, and BEFORE any
       validity test, which is where dup3 differs from dup2 (dup2
       returns [newfd] unchanged for an open fd, and musl's riscv64
       dup2 answers that case itself with an [fcntl(F_GETFD)] probe
       rather than issuing dup3; it reads only the probe's sign, and
       both answers [Fcntl.fcntl_spec] admits there are nonnegative).
       The comparison is on the truncated fds, so [dup3(2^32, 0, 0)] is
       -EINVAL too.
    3. [newfd >= rlimit(RLIMIT_NOFILE)] is -EBADF.
    4. [expand_files] is CALLED next, but its result is not read yet.
    5. [oldfd] not open is -EBADF — tested BEFORE step 4's result, so a
       missing [oldfd] beats an [expand_files] failure.  Only then is
       that result read, and only its -EMFILE becomes -EBADF ([goto
       Ebadf]); its -ENOMEM is returned verbatim.

    STEP 3 IS ANSWERED FROM STATE, not argued around: [State.m_nofile]
    carries the soft RLIMIT_NOFILE the run was launched with (an input,
    like the launching uid — see [State.ProcInput]'s [in_nofile]), and
    this spec tests it where [ksys_dup3] does, before the [oldfd]
    lookup.  Both orders agree on the answer wherever both fire, since
    steps 3 and 5 are the same -EBADF; testing it in the kernel's place
    is what makes the case where they DISAGREE come out right, namely a
    process holding an fd at or above its own soft limit.  That is
    reachable — a parent lowers the limit and execs, and the fds already
    open stay open.

    The limit never moves during a run, which is what lets one field
    hold it and what makes this gate a test rather than a guess.  Why
    it cannot move is argued once, on [State.limst_nofile]; what it
    costs if that stops being true lands here.

    THAT ARGUMENT IS AN ABSENCE, so it is REGISTERED rather than only
    written down.  It holds while [setrlimit] (164) has no dispatcher
    arm, and [Checks.ProcessCreation]'s [setrlimit_unmodeled] and
    [setrlimit_checker_unmodeled] prove that it declines — so
    modelling 164 breaks those proofs instead of silently invalidating this
    gate.  [prlimit64] (261) is the writer that
    DOES have an arm, and no register can speak for it: it is closed by
    [Sys.prlimit64_spec] declining every resource but RLIMIT_CORE, so
    widening that arm is a change this file has to be re-read
    against.

    WHAT IS STILL DECLINED, AND WHY.  A free [newfd] at or above
    [Uapi.NR_OPEN_DEFAULT] and below the limit.  Linux answers it out of
    two facts this model does not carry — the descriptor table's current
    [max_fds] and the [sysctl_nr_open] ceiling — through [expand_files],
    which returns -EMFILE for [newfd >= sysctl_nr_open] (rewritten to
    -EBADF by step 5's [goto Ebadf]) and -ENOMEM for a [kvmalloc] that
    fails.  Both are reachable for any such [newfd] — [sysctl_nr_open]
    can be lowered to [BITS_PER_LONG] while a soft limit set earlier
    stays high — so the model can neither answer success nor pick an
    errno, and declines.  Closing it needs [sysctl_nr_open] as a second
    run input and the table's [max_fds] as state; nothing else.

    ONE THING THIS FILE DOES NOT FIX.  The model's own fd allocator
    ([lowest_fd], and every spec that calls it) hands out numbers
    without consulting the limit, so a modeled run can reach a state
    Linux would have refused with -EMFILE.  That is a divergence rather
    than a decline.

    A FREE [newfd] BELOW [Uapi.NR_OPEN_DEFAULT] IS ANSWERED, and
    deterministically.  That constant is a floor on the live table's
    [max_fds] (the argument is on [Uapi.NR_OPEN_DEFAULT]), so
    [expand_files] takes its [nr < fdt->max_fds] early return, allocates
    nothing, and neither of the two errnos above exists.  This is the
    ordinary redirection case — close a standard descriptor and dup3
    onto it — and it is deterministic for the same reason the
    already-open case is: [do_dup2]'s -EBUSY needs a descriptor reserved
    by another thread in a shared table, and the [filp_close] of the
    displaced description happens after the swap with its return value
    DISCARDED, so no error can come from the close.

    An already-open [newfd] needs no such bound: it is by construction
    below the table's [max_fds], so [expand_files] returns 0 for it
    too.

    O_CLOEXEC is accepted and IGNORED, as [Open.openat_spec] accepts and
    ignores it: close-on-exec is observable only through execve (221)
    and fcntl (25).  execve is outside [Specs.modeled_sysnos].  fcntl is
    IN it, and its [F_GETFD] reads the bit — but [Fcntl.fcntl_spec]
    answers that read with BOTH values, 0 and FD_CLOEXEC, and the one
    fcntl command that writes the bit, [F_SETFD], reports nothing.  So
    the bit's VALUE stays unobservable — whatever it is, the model admits
    the same two answers — and the decision to
    ignore O_CLOEXEC here stands or falls with [Fcntl.fcntl_spec]'s
    decision to admit both answers to [F_GETFD].  The displaced entry is
    dropped exactly as [Open.close_spec] drops one. *)
Definition dup3_newfd_under_limit (newfd : word) (m : Model) : bool :=
  Z.ltb (bv_unsigned newfd) (bv_unsigned (m_nofile m)).

Definition dup3_spec (oldfd newfd flags : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if negb (dup3_flags_ok flags) then err_ret EINVAL
  else if bv_eqb oldfd newfd then err_ret EINVAL
  else if negb (dup3_newfd_under_limit newfd m) then err_ret EBADF
  else
    match fd_lookup (m_fds m) oldfd with
    | None => err_ret EBADF
    | Some e =>
        if negb (dup_modeled_entry e) then unmodeled
        else
          match fd_lookup (m_fds m) newfd with
          | None =>
              (* free: answered only below the embedded table's floor *)
              if Z.ltb (bv_unsigned newfd) NR_OPEN_DEFAULT
              then set_fds (fd_insert (m_fds m) newfd e) ;; ret_only newfd
              else unmodeled
          | Some _ => set_fds (fd_insert (m_fds m) newfd e) ;; ret_only newfd
          end
    end.

(** The two returns above are [newfd] ZERO-extended, where [do_dup2]
    returns an [int] that sign-extends at or above 2^31.  Neither arm
    can reach that: the already-open one is bounded by [State.alloc_fd]'s
    4096, and the free one by the explicit [NR_OPEN_DEFAULT] test.  Note
    which fact is load-bearing — it is the two ARMS' own bounds and not
    the limit test, even though [Run.valid_nofile] does bound the limit
    to 2^31 - 64: that predicate constrains the equivalence theorem's
    inputs, while the extracted checker is handed a model directly and
    never sees it, so a caller may still reach this spec with any
    [unsigned long] in [State.m_nofile]. *)

(* =========================================================================
   close_range (436)
   ========================================================================= *)

(** The descriptor table with every fd in [[lo, hi]] removed and every
    other entry kept in its order: what [__range_close]'s loop leaves.
    The bounds are compared unsigned, as the kernel's [unsigned int]s
    are.  A model fd at or above 2^32 cannot exist (every fd the model
    hands out is below 2^31, see [Syscall.fd32]); were one present it
    would lie above any [hi] and stay. *)
Definition close_range_fds (lo hi : word) (fds : list (word * FdEntry))
    : list (word * FdEntry) :=
  List.filter (fun p => negb ((bv_unsigned lo <=? bv_unsigned (fst p))
                              && (bv_unsigned (fst p) <=? bv_unsigned hi))%Z)
              fds.

(** [close_range fd max_fd flags]: with [flags] 0, close every open
    descriptor from [fd] to [max_fd] inclusive and answer 0.

    fs/file.c [SYSCALL_DEFINE3(close_range)], [__range_close], [last_fd], [file_close_fd_locked], read at v6.18.44; identical at v6.18.46.
    include/uapi/linux/close_range.h [CLOSE_RANGE_UNSHARE], [CLOSE_RANGE_CLOEXEC], read at v6.18.44; identical at v6.18.46.

    THE KERNEL'S ORDER, all three arguments [unsigned int] (so the
    dispatcher hands this spec [fd32] of a0 and a1 and [flag32] of a2,
    and the register's high half is gone before any test):

      if (flags & ~(CLOSE_RANGE_UNSHARE | CLOSE_RANGE_CLOEXEC))
                                                   return -EINVAL;
      if (fd > max_fd)                             return -EINVAL;
      if ((flags & CLOSE_RANGE_UNSHARE) && <table shared>)
                                                   dup_fd ... (-ENOMEM, -EMFILE)
      if (flags & CLOSE_RANGE_CLOEXEC)  __range_cloexec(cur_fds, fd, max_fd);
      else                              __range_close(cur_fds, fd, max_fd);
      ...
      return 0;

    So an unknown flag bit is -EINVAL whatever the range, and [fd >
    max_fd] is -EINVAL whatever the two known flags say: both are
    answered, in that order, before this spec looks at a known flag.

    FLAGS 0 IS ANSWERED, deterministically.  [__range_close] clamps
    [max_fd] to [last_fd] = [max_fds - 1], the table's own end, and then
    for each [fd <= max_fd] takes the file out of its slot
    ([file_close_fd_locked]) and, if there was one, [filp_close]s it,
    DISCARDING the result.  No step can fail, so the answer is 0 for
    every range that passes the two tests, open descriptors or not; the
    clamp removes nothing the model holds, since every open fd is below
    [max_fds].  What changes is the table: every fd in [[fd, max_fd]]
    is gone ([close_range_fds]).  That is [Open.close_spec] applied to
    each open fd of the range in ascending order with its 0 discarded,
    and it is KIND-BLIND for the same reason that spec is: what a
    program can observe of a close is the descriptor leaving the table.
    In particular [Open.close_spec]'s pipe argument carries over
    unchanged -- [State.pipe_end_live] reads a pipe end's liveness off
    the fd table, so closing the last write end by range is what turns
    a later read of the drained pipe into end-of-file, exactly as one
    [close] does, and buffered bytes stay in [m_pipes].

    DECLINED: [CLOSE_RANGE_UNSHARE] or [CLOSE_RANGE_CLOEXEC] set, once
    the two -EINVAL tests have passed.  CLOEXEC sets the close-on-exec
    bit of each descriptor in the range instead of closing it, and the
    model records no close-on-exec bit (see [dup3_spec]'s O_CLOEXEC
    note), so it could neither store the effect nor answer a later
    [fcntl(F_GETFD)] from it.  UNSHARE copies a SHARED table first; the
    model's table is never shared (no [CLONE_FILES] clone is admitted),
    so it would act as flags 0 here, but nothing in scope issues it and
    the decline keeps the arm to the one shape argued above.

    The answer is 0 in a full register and the -EINVALs are [errno_ret];
    nothing is read from memory and nothing is written there. *)
Definition close_range_spec (fd max_fd flags : word) : Sys SyscallEffect :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags)
                          (Z.lor CLOSE_RANGE_UNSHARE CLOSE_RANGE_CLOEXEC)) 0)
  then err_ret EINVAL                     (* an unknown flag bit *)
  else if (bv_unsigned max_fd <? bv_unsigned fd)%Z then err_ret EINVAL
  else if negb (Z.eqb (bv_unsigned flags) 0) then unmodeled
  else
    m <- get_model ;;
    set_fds (close_range_fds fd max_fd (m_fds m)) ;;
    ret_only (Z_to_bv 64 0).
