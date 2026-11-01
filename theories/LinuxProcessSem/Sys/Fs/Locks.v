(** * LinuxProcessSem.Sys.Fs.Locks — flock (32)

    This file answers to Linux [fs/locks.c]: it holds what the kernel
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

(** [cmd & LOCK_MAND] — the FIRST test [SYSCALL_DEFINE2(flock)]
    (fs/locks.c, Linux v6.18.46, commit 1f99e9ab748f) performs, and the
    only one that answers before the descriptor is looked up at all.

    Mandatory flocks were removed from the kernel, and what replaced
    them is a SUCCESSFUL NO-OP rather than a rejection: the syscall
    logs [pr_warn_once] and returns 0.  So [flock(-1, LOCK_MAND)] is 0,
    not -EBADF, and [flock(fd, LOCK_MAND)] is 0 whatever the fd names
    and whatever locks are held.  Nothing is recorded because nothing
    happens — no [struct file_lock] is built and [flock_translate_cmd]
    is never reached.

    The bit is tested, not the whole word, so LOCK_MAND OR'd with any
    other operation is still this arm: [LOCK_MAND|LOCK_EX] takes no
    lock. *)
Definition flock_mand_b (cmd : word) : bool :=
  negb (Z.eqb (Z.land (bv_unsigned cmd) LOCK_MAND) 0).

(** [cmd & ~LOCK_NB] — the word [flock_translate_cmd] switches on.

    LOCK_NB is a MODIFIER, stripped before the operation is recognized,
    which is why an unrecognized operation and a recognized one differ
    only in these bits.  [cmd] arrives already narrowed to 32 bits (see
    [Syscall.cmd32]), so this is the kernel's own [unsigned int]
    arithmetic. *)
Definition flock_base (cmd : word) : Z :=
  Z.ldiff (bv_unsigned cmd) LOCK_NB.

(** The three operations [flock_translate_cmd] (fs/locks.c) maps to a
    lock type; every other word falls off the end of its [switch] and is
    -EINVAL, RETURNED BEFORE THE DESCRIPTOR IS RESOLVED.  That ordering
    is behavior: [flock(-1, 0)] is -EINVAL and not -EBADF. *)
Definition flock_cmd_ok_b (cmd : word) : bool :=
  let b := flock_base cmd in
  (Z.eqb b LOCK_SH || Z.eqb b LOCK_EX || Z.eqb b LOCK_UN)%bool.

(** Is this the UNLOCK operation?  Separated from the other two because
    it is the one the model can answer unconditionally — see
    [flock_spec]. *)
Definition flock_unlock_b (cmd : word) : bool := Z.eqb (flock_base cmd) LOCK_UN.

(** How many descriptors in the table name the path [p].

    THIS IS THE WHOLE OF THE MODEL'S LOCK STATE, and it is a count of
    OPENERS rather than a record of locks.  The argument in [flock_spec]
    turns on there being at most one [struct file] on the inode, not on
    which locks it holds, so no lock has to be recorded to make it.

    Every [FdEntry] constructor is named rather than wildcarded, for
    the reason [State.pipe_end_live] gives for the same shape: a later
    constructor able to name a file in [m_fs] must stop the build here
    instead of being counted as "not an opener" by falling through a
    catch-all.  The four that are skipped are skipped on a fact about
    what they are, not on convenience — a channel, a pipe end, a socket
    and a directory reference each live on an inode that is not a key of
    [Fs.Fs] at all, which is argued at [flock_spec]. *)
Fixpoint path_openers (fds : list (word * FdEntry)) (p : path) : nat :=
  match fds with
  | [] => 0
  | (_, FdFile q _)  :: r => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, FdFileW q _) :: r => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, FdFileA q _) :: r => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, FdFileRW q _) :: r => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, FdChannel _) :: r => path_openers r p
  | (_, FdDir)       :: r => path_openers r p
  | (_, FdSocket _)  :: r => path_openers r p
  | (_, FdPipe _ _)  :: r => path_openers r p
  | (_, FdDevNull _ _) :: r => path_openers r p   (* a device node is not a key of [Fs.Fs] *)
  | (_, FdUrandom) :: r => path_openers r p       (* nor is this one *)
  | (_, FdOpaque (ONsFile _)) :: r => S (path_openers r p)
    (* COUNTED FOR EVERY PATH: the object behind the handle may be any
       open file ([State.ONsFile]), the one being locked included, and a
       lock it holds would conflict, so [flock_sole_opener] fails and
       [flock_spec] declines while one is open *)
  | (_, FdOpaque _) :: r => path_openers r p
    (* nor is any of the other three opaque objects: a procfs name or an
       anonymous inode, and [Open.openat_spec] mints a file kind only for
       a slash-free name or a "/tmp/" key, never for a "/proc" one *)
  end.

(** Exactly one descriptor names [p].  Applied to a path just resolved
    out of the table, so the count is at least one and this says "no
    OTHER descriptor names it". *)
Definition flock_sole_opener (fds : list (word * FdEntry)) (p : path) : bool :=
  Nat.eqb (path_openers fds p) 1.

(** [flock fd cmd]: take, convert or release a whole-file advisory lock.

    THE ORDER IS THE KERNEL'S, and here it decides two answers rather
    than one.  [SYSCALL_DEFINE2(flock)] (fs/locks.c, Linux v6.18.46,
    commit 1f99e9ab748f) does, in this order: the LOCK_MAND test, the
    [flock_translate_cmd] of [cmd & ~LOCK_NB], the descriptor lookup
    and its [fd_empty] test, the [f_mode] test, the LSM hook, and only
    then the lock itself.  So

      flock(-1, LOCK_MAND)  is 0        — no fd is consulted
      flock(-1, 0)          is -EINVAL  — the operation loses to no fd
      flock(-1, LOCK_EX)    is -EBADF

    and a model that resolved the descriptor first would answer -EBADF
    to all three.

    WHAT IS ANSWERED, AND WHY EACH ANSWER IS CERTAIN.

    - LOCK_MAND (any word with bit 0x20 set): 0.  Unconditional; see
      [flock_mand_b].

    - an operation [flock_translate_cmd] does not recognize: -EINVAL.
      Unconditional, and decided before the fd.

    - a descriptor that is not open: -EBADF.  [fd_empty(f)] is the only
      thing between the operation check and the lock.

    - LOCK_UN on any open descriptor: 0.  UNCONDITIONAL, and this is
      the one arm that needs no premise about who else holds a lock.
      Walk it: [flock_translate_cmd] gives F_UNLCK, so the [f_mode]
      test — [type != F_UNLCK && !(f_mode & (FMODE_READ|FMODE_WRITE))]
      — is skipped, and [locks_lock_file_wait] reaches
      [flock_lock_inode] (fs/locks.c).  There [locks_get_lock_context]
      returning NULL is [return (flc_flags & FL_EXISTS) ? -ENOENT : 0]
      for an unlock, and FL_EXISTS is a fcntl-side flag that
      [flock_make_lock] never sets; with a context, the first loop
      drops whatever this [struct file] held and [lock_is_unlock] then
      takes [goto out] with [error] still 0.  Neither branch reads the
      list of locks OTHER files hold, so an unlock cannot -EAGAIN and
      cannot block.  Releasing a lock that was never taken is 0 too.

    - LOCK_SH or LOCK_EX (with or without LOCK_NB) on an [FdFile] or
      [FdFileW] whose path NO OTHER DESCRIPTOR NAMES: 0.  This is the
      arm the premise below is spent on.

    WHY THE SOLE-OPENER GATE IS THE RIGHT ONE, and not a conservative
    flourish.  An FLOCK lock's owner is the [struct file], not the
    process: [flock_make_lock] sets [flc_owner = filp], and
    [flock_locks_conflict] returns false outright when
    [caller_flc->flc_file == sys_flc->flc_file].  So one open file
    description can lock, relock, upgrade and downgrade freely and
    never conflict with itself, and a SECOND [openat] of the same name
    in the SAME PROCESS produces a second [struct file] that DOES
    conflict.  That is not a corner: it is the ordinary way a program
    deadlocks against itself, and it is reachable here with two modeled
    syscalls.

      fd1 = openat(AT_FDCWD, "f", ...);  flock(fd1, LOCK_EX);      /* 0 */
      fd2 = openat(AT_FDCWD, "f", ...);  flock(fd2, LOCK_EX|LOCK_NB);
                                                        /* -EAGAIN */

    A model that answered 0 to the second call would be wrong in
    the sense of design priority 1 (README.md), and the state that would let it
    answer -EAGAIN instead is a per-open-file-description lock table
    the model does not have — and could not key correctly if it did,
    since [File.dup_spec] copies an [FdEntry] and the copy is the SAME
    [struct file], which does not conflict, while a reopen is a
    different one, which does.  Two identical [FdFile p off] entries do
    not say which happened.  So the second call DECLINES, and the first
    is answered only while it is provably alone.  The gate costs the
    duplicated-descriptor case (a [dup] of the locked fd declines even
    though Linux would answer 0); that is coverage, not soundness.

    WHY THE OTHER FOUR FD KINDS DECLINE, each for its own reason rather
    than by a shared shrug:

    - [FdPipe]: BOTH ENDS OF ONE PIPE SHARE AN INODE and are two
      [struct file]s, so [pipe2] alone builds the conflicting pair the
      gate above exists to refuse — and [State.FdPipe]'s id would make
      the gate expressible, so this decline is a coverage choice with a
      known shape rather than a missing fact.
    - [FdChannel]: the object is not in the model.  The model already
      assumes a channel is a PIPE ([Sync.fsync_spec]'s -EINVAL and
      [ReadWrite.lseek_spec]'s -ESPIPE both spend that assumption), and
      that assumption does not say whether two channels are two ends of
      one pipe or two different pipes — which is exactly the question
      an inode-scoped lock asks.
    - [FdDir]: "." and ".." are both [FdDir] and the constructor
      carries nothing, so two directory references cannot be told
      apart; two [openat(".")] descriptors are two [struct file]s on
      one inode.
    - [FdSocket]: sockfs gives every socket its own inode, so the
      conflicting pair is not constructible — but the answer would then
      be 0 by an argument about [sock_alloc] rather than about
      fs/locks.c, and no caller wants it.  Declined for want of a
      reason to admit it, not for want of one to refuse it.

    WHY A PATH IS THE RIGHT KEY FOR THE FILE KINDS.  Conflicts are
    per-INODE, and [Fs.Fs] is a flat path-to-bytes map with no inode
    notion, so the two coincide only under assumptions the model
    already makes everywhere: distinct keys are distinct files (a hard
    link would break it, and no modeled syscall makes one — [linkat]
    has no arm), and a key is a regular file in the working directory
    ([Open.openat_spec]'s separator gate is what keeps every key a plain
    name).  The constructors [path_openers] skips — [FdChannel], [FdDir],
    [FdSocket] and [FdPipe] — rest on the same map: a pipefs, sockfs or
    directory inode is not a key of [Fs.Fs], so no descriptor of those
    kinds can share an inode with an [FdFile].

    WHAT THE GRANT ASSUMES ABOUT THE WORLD, stated as an assumption
    rather than derived: no process outside the model holds a
    conflicting flock on the inode.  This is the premise
    [Sys/Uapi.v]'s O_NONBLOCK note already asserts for leases — "the
    model runs ONE process, so nothing else can hold one either" — and
    it is load-bearing here in a way it is not there, because a lease
    also needs an fcntl the model declines while a flock needs only
    another process that opened the same name.  Modeling [clone]
    parent-side widens the population it quantifies over: a child this
    model never steps inherits the fd table, and locks taken through an
    INHERITED descriptor are the same [struct file] and still do not
    conflict, but a child that opens the name again is a second one
    that does.

    THE FILESYSTEM BOUND, which is real and is the same one
    [Sync.fsync_spec] names for [.fsync].  Everything above assumes
    [f_op->flock] is NULL, so that [locks_lock_file_wait] — the local,
    inode-scoped path — is what runs.  It holds for the filesystems a
    run can plausibly sit on: neither [ext4_file_operations]
    (fs/ext4/file.c) nor [shmem_file_operations] (mm/shmem.c) nor
    [ext4_dir_operations] (fs/ext4/dir.c) nor [simple_dir_operations]
    (fs/libfs.c) declares one, and neither do [pipeanon_fops]
    (fs/pipe.c), [socket_file_ops] (net/socket.c), [tty_fops]
    (drivers/tty/tty_io.c) or [null_fops] (drivers/char/mem.c).  A
    network filesystem that DOES declare one — NFS is the standing
    example — answers from its own lock manager, and a run whose
    working directory sits on such a mount is outside this spec.  Same
    shape as fsync's procfs/sysfs bound: named, not fixed.

    OUT OF SCOPE, and unreachable rather than approximated:

    - -ENOMEM from [locks_alloc_lock] or [locks_get_lock_context].  The
      model has no allocation-failure state, so no execution reaches
      it.  This spec commits to its answers absolutely rather than
      offering an [Syscall.errno_from] alternative, which is the
      position [Fcntl.fcntl_spec] and [Ioctl.ioctl_spec] take for the
      same class.
    - the LSM hook [security_file_lock], which runs after the [f_mode]
      test and can fail the call under an enforcing module.  Same
      position again, and for the same reason: the model describes a
      kernel with no LSM registering these hooks.
    - the -EBADF an O_PATH descriptor gets: [SYSCALL_DEFINE2(flock)]'s
      [CLASS(fd, f)] is [fdget], which refuses an FMODE_PATH file before
      the command is read (fs/locks.c and fs/file.c, read at v6.18.44;
      identical at v6.18.46), and that is -EBADF for LOCK_UN too.  The
      model's O_PATH kind ([State.OProcPath]) is declined, with the
      other two opaque objects, ahead of the unlock arm.
    - blocking.  A LOCK_SH or LOCK_EX without LOCK_NB that conflicts
      sleeps in [wait_event_interruptible] (fs/locks.c,
      [flock_lock_inode_wait]) until the holder releases or a signal
      arrives.  Every shape that can conflict declines above, so the
      model never has to represent a syscall that does not return, and
      the -EINTR that path can produce is unreachable with it. *)
Definition flock_spec (fd cmd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if flock_mand_b cmd then ret_only (Z_to_bv 64 0)
    (* the removed mandatory-lock request: a no-op that succeeds,
       decided before the fd is looked at *)
  else if negb (flock_cmd_ok_b cmd) then err_ret EINVAL
    (* [flock_translate_cmd] fell off its switch — still before the fd *)
  else
    match fd_lookup (m_fds m) fd with
    | None => err_ret EBADF                        (* fd not open *)
    | Some e =>
        if fd_is_opaque e then unmodeled
          (* FAIL-CLOSED, ahead of the kind-blind unlock below: an O_PATH
             file is -EBADF on every command (see above), and an eventfd
             or a /proc/sys file is a [struct file] on an inode whose
             other openers this model does not count *)
        else if flock_unlock_b cmd then ret_only (Z_to_bv 64 0)
          (* an unlock reads no other file's locks: unconditionally 0 *)
        else
          match e with
          | FdFile p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_only (Z_to_bv 64 0)         (* provably uncontended *)
              else unmodeled                       (* a second opener could hold it *)
          | FdFileW p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_only (Z_to_bv 64 0)
              else unmodeled
          | FdFileA p _ =>
              (* the same regular file opened in append mode.  O_APPEND is
                 a property of the open file description that decides where
                 a WRITE lands; [flock] locks the inode and reads no
                 [f_flags] at all, so the sole-opener argument transfers
                 unchanged *)
              if flock_sole_opener (m_fds m) p
              then ret_only (Z_to_bv 64 0)
              else unmodeled
          | FdFileRW p _ =>
              (* the same regular file opened O_RDWR.  [sys_flock] resolves
                 its descriptor through [fdget] and reads no [f_mode] and
                 no [f_flags] on any path to [flock_lock_inode_wait]: the
                 lock is on the INODE, and which directions the
                 description may transfer is not one of its inputs
                 (fs/locks.c, Linux v6.18.46).  So the access mode cannot
                 change the count, and the sole-opener argument transfers
                 unchanged from the three arms above.

                 COUNTING IT IS THE SOUNDNESS-RELEVANT HALF: skipping it
                 in [path_openers] would leave [flock_sole_opener] true
                 while a SECOND read-write descriptor held the same path,
                 and the model would answer 0 for a lock the kernel makes
                 conflict — an unsound accept rather than a gap. *)
              if flock_sole_opener (m_fds m) p
              then ret_only (Z_to_bv 64 0)
              else unmodeled
          | FdChannel _ => unmodeled               (* the object is not in the model *)
          | FdDir       => unmodeled               (* two dirrefs are indistinguishable *)
          | FdSocket _  => unmodeled               (* no caller, and a different argument *)
          | FdPipe _ _  => unmodeled               (* both ends share one inode *)
          | FdDevNull _ _ => unmodeled
              (* FAIL-CLOSED: every open of /dev/null is a [struct file]
                 on ONE inode, so two descriptors of this kind conflict
                 exactly as two [FdFile]s on one path do, and the
                 sole-opener gate would need an [FdDevNull] count the way
                 [path_openers] counts a path.  Derivable, not written. *)
          | FdUrandom => unmodeled
              (* FAIL-CLOSED, for the /dev/null reason: one inode, so
                 an [FdUrandom] count would be needed.  Not written. *)
          | FdOpaque _ => unmodeled
              (* unreachable: [fd_is_opaque] declined this kind above *)
          end
    end.
