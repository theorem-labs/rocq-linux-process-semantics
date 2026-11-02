(** * LinuxProcessSem.Specs — per-syscall relational specs and the dispatcher

    TRUST BOUNDARY: this file is part of the trusted specification.

    SYSCALL MODELING PRIORITY: a spec should admit exactly the results and
    effects Linux permits.  Soundness comes first: until a case meets that
    standard, it must fail closed rather than admit an approximation.
    Existing over-approximations are gaps against this priority, not permitted
    interpretations of it.  Completeness then expands the covered cases.  When
    Linux permits a constrained set rather than one result, the spec should
    encode that set and its constraints without selecting a particular member.
    The constraints are then provable from the spec, but no particular
    permitted member is pinned down without additional environment facts or
    assumptions selecting it.

    REPRESENTATION: syscall arguments and returns are [word = bv 64],
    buffer bytes are [byte = bv 8], errnos and flag masks are [Z]
    (bridged with [errno_ret] / [bv_unsigned]).  Length and bound
    comparisons happen in [Z] over unsigned values, keeping the
    unbounded-integer meaning.  [Forall (fun b => b < 256)] clauses on
    chosen byte lists are unnecessary — [bv 8] enforces them by type.

    Each syscall is a [Sys SyscallEffect] program: given the decoded
    arguments (and, through the monad, the pre-syscall memory and model
    state), it describes the set of admissible effects — the return value
    and the ordinary/symbolic user-memory effects — together with the model
    update and the observable events.  Non-determinism ([choose]/[alt]) is the
    environment's: how many bytes a stdin read delivers (short reads),
    where mmap/mremap places a mapping, which fd number the kernel hands out.
    WHICH bytes stdin delivers, and where the input ends, are NOT
    nondeterministic: they come from the run's input stream
    ([State.InputStream], threaded through the model's [m_stdin]).

    FAIL CLOSED: each modeled syscall yields [unmodeled] on argument shapes it does
    not cover (unreadable source buffers, unwritable output buffers,
    unmodeled open flags, non-AT_FDCWD dirfd), and the dispatcher
    yields [unmodeled] on any syscall NUMBER outside [modeled_sysnos].  A target
    binary therefore cannot smuggle behavior through anything the model
    does not cover.  (A SOURCE binary is unconstrained only when EVERY
    execution errors; one unmodeled resolution does not excuse it when
    another resolution survives.  Keeping source binaries inside the
    modeled surface remains a task-construction-time responsibility.)
    Distinguish [unmodeled] from modeled FAILURE: read/write/close
    on a nonexistent fd return -EBADF (a real kernel behavior, not a
    hole in the model), and open of a missing file returns -ENOENT.

    Syscall numbers are the Linux asm-generic / riscv64 ABI.

    WHERE A SPEC LIVES.  The specs are under [Sys/], laid out the way
    Linux lays out its own source: one file per kernel source file,
    holding the syscalls Linux defines there and only those.  So which
    file a spec belongs in is not a judgement call — look up where the
    kernel defines the syscall, and that is the answer.

      Sys/Fs/ReadWrite.v         fs/read_write.c   read write readv writev lseek
                                                   pread64 pwrite64
      Sys/Fs/Open.v              fs/open.c         openat close ftruncate faccessat faccessat2
      Sys/Fs/Sync.v              fs/sync.c         fsync fdatasync
      Sys/Fs/Stat.v              fs/stat.c         readlinkat newfstatat fstat
      Sys/Fs/Select.v            fs/select.c       pselect6 ppoll
      Sys/Fs/Namei.v             fs/namei.c        unlinkat
      Sys/Fs/Readdir.v           fs/readdir.c      getdents64
      Sys/Fs/DPath.v             fs/d_path.c       getcwd
      Sys/Fs/Ioctl.v             fs/ioctl.c        ioctl
      Sys/Fs/Fcntl.v             fs/fcntl.c        fcntl
      Sys/Fs/Locks.v             fs/locks.c        flock
      Sys/Fs/Pipe.v              fs/pipe.c         pipe2
      Sys/Fs/File.v              fs/file.c         dup dup3, and which descriptor an open gets
      Sys/Fs/Timerfd.v           fs/timerfd.c      timerfd_create
      Sys/Fs/EventPoll.v         fs/eventpoll.c    epoll_create1 epoll_ctl epoll_pwait
      Sys/Fs/EventFd.v           fs/eventfd.c      eventfd2
      Sys/Mm/Mmap.v              mm/mmap.c         brk mmap munmap
      Sys/Mm/Mremap.v            mm/mremap.c       mremap
      Sys/Mm/Mprotect.v          mm/mprotect.c     mprotect
      Sys/Mm/Madvise.v           mm/madvise.c      madvise
      Sys/Kernel/Exit.v          kernel/exit.c     exit exit_group wait4
      Sys/Kernel/Fork.v          kernel/fork.c     set_tid_address clone clone3
      Sys/Kernel/Futex/Syscalls.v  kernel/futex/syscalls.c  futex set_robust_list
      Sys/Kernel/Signal.v        kernel/signal.c   sigaltstack rt_sigaction
                                                   rt_sigprocmask
      Sys/Kernel/Groups.v        kernel/groups.c   getgroups setgroups
      Sys/Kernel/Sched/Syscalls.v  kernel/sched/syscalls.c  sched_getaffinity
                                                   sched_setscheduler
                                                   sched_yield
      Sys/Kernel/Sys.v           kernel/sys.c      getpid gettid setsid uname
                                                   prlimit64 getuid geteuid
                                                   getgid getegid setuid setgid
                                                   setresuid setresgid
                                                   prctl (whose PR_CAPBSET_READ
                                                   arm answers to
                                                   security/commoncap.c's
                                                   cap_task_prctl, reached
                                                   through kernel/sys.c's
                                                   security_task_prctl)
      Sys/Kernel/Time/Hrtimer.v  kernel/time/hrtimer.c       nanosleep
      Sys/Kernel/Time/PosixTimers.v
                                 kernel/time/posix-timers.c  clock_gettime clock_getres
      Sys/Kernel/Time/Time.v     kernel/time/time.c          gettimeofday
      Sys/Net/Socket.v           net/socket.c      socket bind listen accept connect accept4
      Sys/Drivers/Char/Random.v  drivers/char/random.c  getrandom

    Three files carry what the kernel keeps in headers rather than in
    any one syscall's source: [Sys/Uapi.v] the ABI constants,
    [Sys/Syscall.v] the calling convention (how a spec returns, how the
    ABI narrows an argument), and [Sys/Uaccess.v] the user-buffer
    boundary (checking a range, bounding a transfer, delivering bytes).

    This file re-exports all of them, so a consumer that
    [Require Import ... Specs] sees every name unqualified, as before. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Dispatch SyscallTable
  Syscall Uapi Uaccess
  Fs.DPath Fs.File Fs.ReadWrite Fs.Open Fs.Sync Fs.Stat Fs.Select Fs.Ioctl Fs.Fcntl Fs.Namei
  Fs.Readdir Fs.Locks Fs.Timerfd Fs.Pipe Fs.EventPoll Fs.EventFd
  Mm.Mmap Mm.Mremap Mm.Mprotect Mm.Madvise
  Kernel.Exit Kernel.Fork Kernel.Futex.Syscalls Kernel.Groups Kernel.Sched.Syscalls
  Kernel.Signal Kernel.Sys
  Kernel.Time.Hrtimer Kernel.Time.PosixTimers Kernel.Time.Time
  Net.Socket
  Drivers.Char.Random.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   Dispatcher — FAIL CLOSED
   ========================================================================= *)

(** The syscall numbers this model covers, as unsigned values.  The
    trace semantics does not consult this list — an ecall whose number
    is not in it simply falls through the dispatcher to [unmodeled] (fail
    closed).  The list documents the modeled surface (a SOURCE binary
    issuing a syscall outside it can [unmodeled], but its task is vacuous
    only if all executions do so — see [Equivalence.equiv] — so task
    construction must keep source binaries inside it).  It cannot drift
    from the dispatcher — both are read off [Sys.SyscallTable.spec_table]
    — and [Checks/DispatchSurface.v] proves the two facts that identity
    does NOT give: every listed number is answered on some input, so a
    dead arm fails the build, and no number is listed twice, which
    [Sys.Dispatch.lookup_arm] would otherwise resolve first-match-wins.

    TODO(syscall coverage): support every syscall a musl-linked source
    binary can issue, so real source binaries provably stay inside the
    modeled surface on all resolutions.

    THERE IS NO LIST OF WHAT IS MISSING HERE, AND THAT IS DELIBERATE.
    A list kept by hand goes stale on the next arm, nothing compares it
    against anything, and its real effect is to make the gap look small.

    The set of ABI numbers with no arm has several hundred members.
    No count is written here on purpose — one would go stale on the next
    arm — so compute it, remembering that the lexical sort matters because [comm]
    is not numeric.  unistd.h is include/uapi/asm-generic/unistd.h at
    v6.18.46, commit 1f99e9ab748f, and is not vendored here:

      grep -E '^#define __NR(3264)?_[a-z_0-9]+ +[0-9]+$' unistd.h \
        | grep -v __NR_syscalls | awk '{print $3}' | sort -u > abi
      grep -oE 'mkSpecArm +[0-9]+' Sys/SyscallTable.v \
        | grep -oE '[0-9]+' | sort -u > modeled
      comm -23 abi modeled | wc -l     # defined by the ABI, no arm
      comm -13 abi modeled | wc -l     # must be 0, or the greps are wrong

    No measurement of the musl surface is in this repository.  Measure
    it before relying on any claim about it.

    WHAT WOULD EARN A LIST ITS PLACE is a check rather than a
    sentence — one that fails the build when it stops being true.  That
    is a DIFFERENT set
    comparison from the one above: the ABI residue is computable from
    two files and is only a ceiling, while the set this TODO is about is
    the far smaller one a musl-linked binary can actually issue.  That
    one needs a corpus of musl-linked binaries, which this repository
    does not have.

    Futex (98) HAS an arm, but what resists
    modeling is an answer that depends on a WAITER EXISTING, and
    [Sys.Kernel.Futex.Syscalls.futex_spec] admits only the two private
    op words whose answer does not.  Every other op declines from inside
    that spec, the way [Fs.Ioctl.ioctl_spec] declines every request but
    its own. *)

Definition modeled_sysnos : list Z := arm_numbers spec_table.

(** Dispatch on the unsigned syscall number.  The final [unmodeled] arm is
    the fail-closed fallback for every number outside [modeled_sysnos]. *)
Definition syscall_spec : Sys SyscallEffect := dispatch spec_table.
