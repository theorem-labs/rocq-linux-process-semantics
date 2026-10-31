(** * LinuxProcessSem.Sys.Kernel.Fork — set_tid_address (96), clone (220), clone3 (435)

    This file answers to Linux [kernel/fork.c]: it holds what the kernel
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
  Syscall.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** [PID_MAX_ENVELOPE]: the upper bound on the tid the environment may
    choose, exclusive.

    Why the envelope is [1 <= tid < 2^22].  Citations are torvalds/linux read at
    v6.16; the version range over which they hold is stated at the end.

    - POSITIVE.  [set_tid_address] returns [task_pid_vnr(current)]
      ([kernel/fork.c], [SYSCALL_DEFINE1(set_tid_address, int __user *,
      tidptr)]) — a body of two statements, with no validation of [tidptr]
      and no error path at all, which is also why the spec below accepts
      and ignores the argument.  Pids come from [idr_alloc_cyclic(&tmp->idr,
      NULL, pid_min, pid_max, GFP_ATOMIC)] in [alloc_pid] ([kernel/pid.c]),
      where [pid_min] is initialised to [1] and only ever raised to
      [RESERVED_PIDS], so a live task never holds tid 0.  The kernel's own
      predicate for a valid tid, on the requested-tid path of that same
      function, is [if (tid < 1 || tid >= pid_max)] yielding [-EINVAL].

    - BELOW [2^22].  [idr_alloc_cyclic]'s [end] argument is EXCLUSIVE
      ([lib/idr.c]), so [pid_max] itself is never allocated, and
      [pid_max <= pid_max_max = PID_MAX_LIMIT]: [pid_max_max] is
      initialised to [PID_MAX_LIMIT] in [kernel/pid.c], and every write to
      [pid_max] is clamped to it — by the [pid_max] sysctl's [extra2]
      bound, and by the [min] in [pid_idr_init] and in
      [register_pidns_sysctls].  [PID_MAX_LIMIT]
      ([include/linux/threads.h]) is
      [IS_ENABLED(CONFIG_BASE_SMALL) ? PAGE_SIZE * 8]
      [: (sizeof(long) > 4 ? 4 * 1024 * 1024 : PID_MAX_DEFAULT)].
      That is TWO arms, and [2^22] is the ceiling of both on a 64-bit
      kernel rather than the value of one: the second arm is exactly
      [4 * 1024 * 1024 = 2^22], and the [CONFIG_BASE_SMALL] arm is
      [PAGE_SIZE * 8], which on riscv64 is [32768] — [arch/riscv/Kconfig]
      selects [HAVE_PAGE_SIZE_4KB] unconditionally, so [PAGE_SIZE] is
      [4096].  A [CONFIG_BASE_SMALL=y] kernel, or any smaller runtime
      [pid_max], therefore stays strictly inside this envelope.  The model
      over-approximates in the safe direction and deliberately abstracts
      the environment's choice rather than pinning one kernel's answer.

    - VERSION RANGE.  The SHAPE of [pid_max] moved inside the plausible
      window: a single global [int pid_max] through v6.13, and from v6.14
      a per-namespace field ([include/linux/pid_namespace.h]) read as
      [READ_ONCE(tmp->pid_max)].  The BOUND survives that refactor —
      [pid_max <= pid_max_max = PID_MAX_LIMIT] holds in both shapes, and
      the [pid_min] computation is untouched by it — across v6.12..v6.16.
      That is what makes [2^22] safe to state here as a constant rather
      than as one kernel's answer.

    Admitting 0 is not a harmless over-approximation: musl 1.2.6
    ([src/exit/exit.c], [exit]) does
    [int prev = a_cas(exit_lock, 0, tid); if (prev == tid) a_crash();], so
    a tid of 0 makes the first ORDINARY [exit] call indistinguishable from
    a recursive one and crash before [exit_group]. *)
Definition PID_MAX_ENVELOPE : Z := (2 ^ 22)%Z.

(** [set_tid_address tidptr]: returns the caller's tid — a value the
    model cannot predict, so its VALUE is the environment's choice
    (like getrandom's bytes), but the process's tid never changes, so
    the choice is made ONCE: the first call picks a positive tid below
    the model's [PID_MAX_ENVELOPE] of [2^22] and
    records it in [m_tid]; every later call returns the recorded value,
    as the real kernel does.  NO MEMORY EFFECT, and the reason is not
    the one a reader expects.

    [set_tid_address] records [tidptr] in the CALLER's
    [current->clear_child_tid].  [copy_process] sets a DIFFERENT task's
    [p->clear_child_tid] under [CLONE_CHILD_CLEARTID], and the two
    share only a field name — one is [current->], the other [p->].  So
    the flag word is the wrong thing to reason about here: ruling out
    [CLONE_CHILD_CLEARTID] rules out the second writer and says nothing
    about the first.

    The write through the CALLER's pointer happens in [mm_release]
    (kernel/fork.c), which is [static] and reached only from
    [exit_mm_release] and [exec_mm_release], both passing the task
    itself — so it fires when THIS task exits or execs, not when any
    child does.  It is guarded on [atomic_read(&mm->mm_users) > 1].

    THIS MODEL ADMITS NO SECOND HOLDER OF AN mm, so [mm_users] is 1 and
    the write cannot fire.  That is a closed-world statement about the
    ENVIRONMENT and it is deliberately broader than any flag test:
    [mmget] is a bare [atomic_inc(&mm->mm_users)] and [get_task_mm]
    calls it for any non-kthread task, so [CLONE_VM] is only one of the
    routes to a second holder — [/proc] (fs/proc/array.c,
    fs/proc/base.c, fs/proc/task_mmu.c), [ptrace] (kernel/ptrace.c), a
    BPF task iterator (kernel/bpf/task_iter.c) and [kernel/sys.c] each
    raise it without any clone at all.  Naming [CLONE_VM] would give a
    false all-clear to four of them.

    THIS DOES NOT REST ON 220 BEING DECLINED.  It rests on nothing else
    holding a reference to this mm; anything that makes a second holder
    possible re-opens it, and [Exit.exit_spec] has no way to express an
    exit-time write today.  ([Run.sstep] producing exactly one
    configuration is a true backstop, but it is not the argument: the
    write in question is the caller's own, so no child need exist for
    it to fire.)

    One detail a description of the write alone would hide:
    [tsk->clear_child_tid = NULL] runs REGARDLESS of the [mm_users]
    test, so the field is cleared even when nothing is written — which
    matters to anyone reasoning about a second exit.

    Byte-identical in kernel/fork.c across v6.10..v6.15.  musl calls
    this unconditionally from [__init_tp]. *)
Definition set_tid_address_spec : Sys SyscallEffect :=
  m <- get_model ;;
  match m_tid m with
  | Some tid => ret_only tid
  | None =>
      tid <- choose (fun tid => (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z) ;;
      set_tid tid ;;
      ret_only tid
  end.


(* =========================================================================
   Process creation — the CALLER's resolution, and nothing else
   ========================================================================= *)

(** [clone] (220) and [clone3] (435), modeled ONLY in the answer the
    CALLING process receives: a child pid, or a failure.  No second
    process is created.  [Run.config] holds one [machine_state] and one
    [Model], and nothing here adds a second of either; the child is never
    a configuration this development can be in.

    WHY THE CHILD IS OUT OF SCOPE.  The measurement this model exists to
    support is a property of the process that issues the call, and every
    fork on the dropbear server's CONNECTION PATH is meant to end in an
    exec.  There are three, out of four in the server.  The
    per-connection fork (src/svr-main.c) has
    its child re-exec the dropbear binary through [fexecve], the default
    on Linux since 2022.82; the session forks — [ptycommand]
    (src/svr-chansession.c) and, without a pty, [spawn_command]
    (src/dbutil.c) — have theirs [execv] the login shell ([run_command],
    src/dbutil.c).  What the child does after the exec is not something
    a statement about THIS process should try to say.

    THREE QUALIFICATIONS, none of which changes the scope decision.  The
    daemonizing fork ([daemon], src/svr-main.c) execs nothing, and is
    skipped under [-F].  And the re-exec is conditional: it is
    compile-gated, and it has two failure paths that fall through to
    [svr_session] in the FORKED image.  Only ONE of them is visible in a
    release build — the failed [fexecve], which logs "fexecve failed,
    disabling re-exec".  The other, the binary not opening, is reported
    through [TRACE] and so compiles out without DEBUG_TRACE.  So "the
    child always execs" is not something to lean on, and the case where
    it does not is partly silent.  And what a child runs BEFORE its
    exec is covered by nothing here.  All three are known gaps.

    WHY IGNORING IT IS NOT AUTOMATICALLY SAFE.  A child that this model
    never steps can still change what the parent observes, or what a
    run of the parent OBSERVABLY DOES.  The channels, closed here or
    named — CLOSED FIRST, then the five that are not:

    - THE ADDRESS SPACE.  A child sharing the parent's [mm] could write
      the parent's memory between two of the parent's own instructions,
      and every claim about the parent's memory would be void.  Closed by
      [clone_fork_flags_b] below: the one flag word this model answers
      has neither [CLONE_VM] nor [CLONE_VFORK], so [copy_process] takes
      [dup_mm] and the two address spaces are separate from the call
      onwards.
    - THE DESCRIPTOR TABLE AND THE FILE OFFSET.  [CLONE_FILES] shares the
      table itself and [CLONE_FS] shares [fs_struct] (so a child [chdir]
      moves the parent's [AT_FDCWD], the only dirfd [Open.openat_spec]
      accepts); [CLONE_PIDFD] installs a NEW descriptor in the PARENT's
      table.  All three are outside the modeled flag word.  What survives
      even a plain fork is the FILE OFFSET: [copy_files] duplicates the
      table while both tables point at the same [struct file], so a
      child's [read] advances the offset the parent will read from next.
      [State.FdEntry] inlines that offset into the descriptor
      ([FdFile p off]) and [ReadWrite.read_spec] advances it privately, so the
      model cannot express the sharing.  Closed by declining the call
      outright while any such descriptor is open —
      [clone_no_shared_file_b], stated as
      [Checks.ProcessCreation.clone_open_file_unmodeled].
    - PARENT MEMORY WRITTEN BY THE CALL ITSELF.  [CLONE_PARENT_SETTID]
      writes the child tid through [parent_tidptr] and [CLONE_PIDFD]
      writes an int through the same pointer.  Both are outside the
      modeled flag word, so the call writes no byte of user memory and
      the effect below carries no write entry.

    FIVE CHANNELS ARE NOT CLOSED, and none of them is closeable by a
    flag test.  Each is a known gap, stated here rather than pretended
    away.

    - A TRACER.  A child that survives could [ptrace] the parent and
      write its memory ([PTRACE_POKEDATA]) or its registers
      ([PTRACE_SETREGS]) with [CLONE_VM] clear.  That is an assumption
      about the ENVIRONMENT (Yama's [ptrace_scope], uid separation);
      declining 220 would not discharge it, since an independently
      started tracer needs no [clone] at all.
    - A SIGNAL.  A child needs no [ptrace] at all to [kill] its parent:
      a matching uid is enough, with no [ptrace_may_access] and no Yama
      gate, so this is strictly EASIER than the tracer route above.  The
      model has no signal machinery — [Run.sstep] has no rule for death
      by signal — so a real run would truncate with no [ExitEv] where
      this model runs on.  The same environment assumption is what rules
      it out, and it is a weaker assumption than the tracer one needs.
    - THE PARENT'S RESOURCE LIMITS.  [prlimit64] (261) IS modeled, and
      [State.m_rlimit_core] pins the pair at the first read.  A child
      aiming [prlimit64(getppid(), RLIMIT_CORE, ...)] at its parent
      moves that pair between two of the parent's own reads.  Gated by
      the same [ptrace_may_access] the tracer bullet assumes away, on a
      different field.
    - THE FILE SYSTEM, which is OBSERVABLE.  [State.event]'s [ExitEv]
      carries the final [Fs.Fs], so what a run's file system ends up
      holding is part of the trace [Equivalence] compares.  A child
      forked with [SIGCHLD] gets a COPY of [fs_struct] pointing at the
      same directory, so it can [openat], [write] and [unlinkat] after
      the fork, and the [ExitEv] this model emits carries only what the
      PARENT did.  And the trace half is the MILDER one: a later parent
      [openat] or [read] resolves against [m_fs], which the
      child has diverged, so a SYSCALL ANSWER is wrong and not merely
      the final snapshot.  Neither is a decline: the model gives a
      definite answer where a real run has another.  dropbear's child
      really does this — the PTY path's login record, written in the
      child BETWEEN the [dup2]s (after stdin and stdout, before stderr,
      and dropbear's own comment there says the position matters),
      opens a regular file.  On this
      repository's musl target it is the LASTLOG write specifically, and
      it is ENABLED: musl points [_PATH_UTMP] and [_PATH_WTMP] at
      /dev/null/utmp and /dev/null/wtmp, so those two can only fail
      -ENOTDIR, but [_PATH_LASTLOG] is /var/log/lastlog, a real path,
      and dropbear's src/loginrec.h derives [LASTLOG_FILE] from it and
      defines [USE_LASTLOG].  So the file-system channel fires on the
      very toolchain this model targets.
    - THE STANDARD DESCRIPTORS, in both directions.  See
      [clone_no_shared_file_b] below for the read side; the write side
      is that a child's writes to fds 1 and 2 are events from a process
      this model never steps, so no widening of THIS process's syscalls
      can put them in the trace.

    ONE THING THE FLAG WORD REQUESTS IS HARMLESS, and the derivation is
    worth writing out because it is an argument from two absences and
    one inherited fact.  [SIGCHLD] is the exit signal, so the child's
    exit sends SIGCHLD to this process.  Nothing comes of it either way:

    The chain, outermost first, is [__send_signal_locked] (named
      [__send_signal] up to v5.18 and renamed IN v5.19 by commit
      157cc18122b4, whose subject names [send_signal] and whose body
      does this one too) -> [prepare_signal]
      -> [sig_ignored] -> [sig_task_ignored] -> [sig_handler_ignored].

    - UNBLOCKED, it is discarded.  [sig_handler_ignored] (kernel/signal.c)
      is true for a [SIG_DFL] handler on a signal in
      [SIG_KERNEL_IGNORE_MASK] (include/linux/signal.h), which SIGCHLD
      is; [sig_ignored] returns true through it and
      [__send_signal_locked] skips the queue.
    - BLOCKED BY THE RECEIVING TASK, it is QUEUED, not discarded —
      [sig_ignored] opens "Blocked signals are never ignored" and
      returns false when the signal is in that task's [blocked] or
      [real_blocked].  The precondition is about the task the signal is
      delivered to, which for SIGCHLD-on-exit is this process.  A
      queued-but-blocked signal sets no [TIF_SIGPENDING], so it cannot
      interrupt a modeled syscall or reach [get_signal]; it is inert
      until unblocked, and nothing here can unblock it.
    - UNDER A TRACER it is queued whatever the disposition:
      [sig_ignored] returns false early on [t->ptrace && sig != SIGKILL].
      That is not a further gap — a tracer is already one of the five
      open channels above, and the same environment assumption rules
      this out.

    Both halves would need the process unable to change its
    disposition or its mask, and it can change the mask.  That does
    not reopen either: [rt_sigprocmask] (135) is modeled, but unblocking
    a queued SIGCHLD is what makes it DELIVERABLE, and delivery re-reads
    the disposition in [get_signal] (kernel/signal.c), where [SIG_DFL]
    plus [sig_kernel_ignore] discards it.  So the blocked case funnels
    into the unblocked one and both halves rest on the disposition.
    The DISPOSITION: [rt_sigaction] (134) IS modeled, so
    what carries this
    half is [Signal.sigaction_accepted] — its accepted set is {SIGINT,
    SIGTERM}, so an install FOR SIGCHLD fails closed at the signal and
    the disposition SIGCHLD is delivered against stays the inherited
    one.  [Checks.Cases.Kernel.Signal.rt_sigaction_sigchld_unmodeled]
    pins that, and the note above [Signal.sigaction_accepted] records
    the obligation this arm puts on it.  The
    STARTING disposition and mask are inherited across [execve] —
    [flush_signal_handlers] resets handlers to [SIG_DFL] but PRESERVES
    [SIG_IGN], and fs/exec.c writes no [->blocked] at all — so both are
    a property of how the process was started, the same shape as
    [State.access_okb]'s post-[execve] [pmlen = 0].

    ALLOWLIST, NOT BLOCKLIST.  The gate admits exactly one flag word,
    [SIGCHLD], and declines every other.  Naming the dangerous bits
    instead would be a blocklist over a 32-bit space in which new bits
    keep being defined, and each of the bits above is a separate thing
    somebody had to think of first.

    OUT-OF-TREE MEASUREMENT (not a checked fact; nothing in this
    repository re-derives it).  Subject: a dropbear server run as a [-F]
    DAEMON, not the [-i] inetd invocation, driven by a real OpenSSH
    client through public-key authentication, far enough that the remote
    shell ran a command and echoed a marker.
    Toolchain: riscv64, musl — this repository's target.  Date and
    dropbear version: NOT RECORDED, which is a defect of the
    measurement rather than of the result; re-run it before relying on
    it.  Scope: the syscalls of the traced process itself, not of any
    child it left behind.  Result: exactly one clone, flag word 0x11 —
    the per-connection fork.  The session fork happens in the child, and
    the trace does not follow children.

    0x11 is [SIGCHLD] with no other bit set, and that is what musl
    issues: riscv64 has no [SYS_fork], so [_Fork] passes the literal
    [SIGCHLD].  It is NOT what glibc issues — [arch_fork] passes
    [CLONE_CHILD_SETTID | CLONE_CHILD_CLEARTID | SIGCHLD], 0x01200011 —
    so the measurement corroborates this flag word for a musl build
    only, and a glibc-linked program fails closed here rather than being
    answered.  One of those two bits is [CLONE_CHILD_CLEARTID], which is
    exactly what [set_tid_address_spec]'s ignored [tidptr] rests on
    being absent, so glibc is excluded for a reason this model states
    elsewhere rather than by accident.

    THE TRACE COVERS THE FLAG WORD AND NOTHING ELSE, and the rest of the
    gate is what keeps dropbear out.  ONE thing stops it:
    [clone_no_shared_file_b] below declines a call made with a regular
    file open, and dropbear's per-connection fork is made with one open
    ON PURPOSE: [execfd], opened [O_CLOEXEC | O_RDONLY] in
    src/svr-main.c and held across the fork because the child needs it
    for [fexecve] — [O_CLOEXEC] closes on exec, not on fork.

    musl's
    [_Fork] brackets the clone with [__block_all_sigs] /
    [__restore_sigs], and [__block_all_sigs(set)] is
    [rt_sigprocmask(SIG_BLOCK, &all_mask, set, 8)] (musl
    src/signal/block.c), whose [oldset] is NON-NULL.
    [Kernel.Signal.rt_sigprocmask_spec]
    answers that shape, so the bracket conforms and
    [clone_no_shared_file_b] is the only modeled decline between
    musl's [fork] and this arm.  A source binary that calls [fork] with
    no regular file open reaches it.

    So the arm this section adds is reached by a RAW [clone] and not by
    the program the flag word was measured on.  That is worth saying
    plainly rather than leaving the header's dropbear framing to imply
    otherwise: what the measurement licenses is the SHAPE of the
    admitted word, not a claim that the modeled surface covers a
    dropbear run.

    Widening this test is a change to the modeled surface and belongs in
    a change of its own; the refusals it currently implies are pinned by
    name in [Checks.ProcessCreation].

    THE ANSWER IS NEVER ZERO, AND THAT IS A DECISION.  Zero is the
    CHILD's return from [clone].  Admitting it would make the model
    follow the child's branch through the caller's own code, which for
    dropbear runs on to [execv] and would fail closed there — but for the
    wrong reason, and looking like coverage of a path this design
    deliberately does not cover.  So the resolution is bounded strictly
    below by 1, [Checks.ProcessCreation.clone_never_returns_zero] and
    [Checks.ProcessCreation.clone3_never_returns_zero] state it against
    the two specs themselves — separately, because routing 435 somewhere
    other than [clone_resolve] would break one and not the other — and a
    checker that accepted a forged 0 would break those proofs rather
    than quietly widening the model.

    KERNEL SIDE, mainline v6.6..v7.2 and stable linux-6.6.y,
    linux-6.12.y, linux-6.17.y.  riscv64 selects
    [CONFIG_CLONE_BACKWARDS] (arch/riscv/Kconfig), so
    [SYSCALL_DEFINE5(clone)] (kernel/fork.c) reads
    (flags, newsp, parent_tidptr, tls, child_tidptr).  With
    [flags = SIGCHLD] the tid pointers and [tls] are never dereferenced —
    the uses are gated on [CLONE_PARENT_SETTID] (a [put_user] into the
    caller's memory, not a read), [CLONE_CHILD_SETTID] and
    [CLONE_SETTLS] — so this spec does not fetch them, exactly as
    [Ioctl.ioctl_spec] does not take its third argument.  On success
    [kernel_clone] returns [pid_vnr(pid)] to the caller, a live pid and
    therefore strictly positive and different from the caller's own.  The
    failures reachable for this flag word are the resource ones, and they
    are a function of state the model does not carry (RLIMIT_NPROC and
    the global thread ceiling through [copy_process]'s [-EAGAIN], and
    allocation failure through [-ENOMEM]), so they are offered as an
    [errno_from] alternative in the way every other untracked environment
    failure in these specs is. *)
Definition SIGCHLD : Z := 17.

(** The clone failures this model admits, for the ONE flag word it
    answers.  Enumerated by walking every error return in [kernel_clone]
    and [copy_process] (kernel/fork.c) in source order and asking which
    survives [flags = SIGCHLD].  Mainline v6.6..v7.2 and stable
    linux-6.6.y / linux-6.12.y / linux-6.17.y.  [kernel_clone] changed
    four times in that window, established by extracting it at every
    release and diffing consecutive pairs rather than by comparing the
    endpoints — which is what it takes, because one of the four is
    invisible at the endpoints.  None reaches an error return this flag
    word can take.  A [CONFIG_LRU_GEN] guard became
    [CONFIG_LRU_GEN_WALKS_MMU] at v6.8.  At v6.9 the legacy-clone check
    began reading [clone_flags] rather than [args->flags] (commit
    b639585e71e6, "fork: Using clone_flags for legacy clone check"), a
    no-op then and load-bearing from v7.1, when [CLONE_EMPTY_MNTNS]
    handling began mutating [clone_flags] ahead of that check and
    writing it back.  And v7.1 added a
    [valid_signal(args->exit_signal)] gate (commit 09e7827e7857,
    "kernel/fork: validate exit_signal in kernel_clone()"), which
    SIGCHLD passes, and [CLONE_EMPTY_MNTNS] handling, which this flag
    word does not request.

    - EAGAIN.  [is_rlimit_overlimit(..., RLIMIT_NPROC, ...)], the
      [nr_threads >= max_threads] ceiling, [alloc_pid] (which has two
      [-ENOSPC] remappings: to -EEXIST on the [set_tid] path, which
      needs [set_tid_size > 0] and so is clone3-only, and to -EAGAIN on
      the path a plain fork takes — so -ENOSPC never escapes either
      way),
      [sched_fork]'s refusal to fork a SCHED_DEADLINE task, and
      [pids_can_fork] in the pids cgroup controller.
    - ENOMEM.  Every allocation on the path: [dup_task_struct],
      [prepare_creds], [mpol_dup], [audit_alloc], [lsm_task_alloc],
      [copy_files], [copy_fs_struct], [copy_sighand], [copy_signal],
      [copy_mm], [copy_namespaces], [__copy_io], and a dying pid
      namespace.  [dup_mm] FLATTENS [dup_mmap]'s -EINTR into a NULL
      return that [copy_mm] reports as -ENOMEM, so that -EINTR is not
      separately reachable.
    - EMFILE.  [dup_fd] (fs/file.c) when the parent holds more open
      descriptors than the CURRENT [fs.nr_open] — reachable whenever the
      sysctl was lowered after the descriptors were opened.  The test is
      inline in [dup_fd] in mainline up to v6.12 and inside
      [alloc_fdtable] from v6.13 (commit 1d3b4bec3ce5, "alloc_fdtable():
      change calling conventions"); both spellings return -EMFILE.  The
      STABLE branches named above are not split the same way — the
      refactor was backported, so linux-6.6.y and linux-6.12.y carry the
      [alloc_fdtable] form while their mainline tags carry the inline
      one.  What the split changes is the THRESHOLD, not the answer: v6.12 rounds
      [sysctl_nr_open] up to a [BITS_PER_LONG] boundary and v6.13 rounds
      it down, so the two differ unless it is already a multiple of 64.
      From v6.17 [alloc_fdtable] carries a second -EMFILE as well, for a
      count past INT_MAX divided by the size of a [struct file] pointer
      (commit 04a2c4b4511d).  THE TWO BACKPORTS ARE SEPARATE:
      linux-6.6.y took both in 6.6.103 (absent at .102), while
      linux-6.12.y took the INT_MAX site at 6.12.43 and the refactor
      only at 6.12.44 — so a 6.12.43 reader has one site and not the
      other.  Every one of these sites answers -EMFILE, which is all
      this list records.
    - EACCES.  [security_task_alloc] → [selinux_task_alloc]
      (security/selinux/hooks.c), which is [avc_has_perm(..., PROCESS__FORK,
      ...)] and answers -EACCES on denial.  AppArmor's and TOMOYO's
      [task_alloc] both return 0 unconditionally, so SELinux is the only
      in-tree source.  What [selinux_task_alloc] RETURNS is unchanged in
      mainline v6.6..v7.2 and in stable linux-6.6.y, linux-6.12.y and
      linux-6.17.y: [avc_has_perm]'s verdict.  Its body is not — from
      v6.18 it also copies the task's security blob first (commit
      dde3a5d0f4dc, "selinux: move avdcache to per-task security
      struct"), which changes what it does and not what it answers.
      That commit carries [Cc: stable] and was backported as
      21879b76831f, so linux-6.17.y carries the changed body too, from
      6.17.10.

    ONE -EAGAIN IN THIS FUNCTION IS NOT ON THE LIST AND SHOULD NOT BE.
    v7.x has one inside [#ifdef CONFIG_IO_URING] that is a REDUNDANT
    RESTORE — it re-sets [retval] to the value the [nr_threads] check
    already left live, on a path gated by [args->kthread].  A list built
    by grepping the file would count it as a distinct source; this one
    was built by asking which returns survive [flags = SIGCHLD] from a
    user process, and it is neither distinct nor reachable.

    NOT ADMITTED, and why each is unreachable rather than absorbed:
    -EINVAL, -EPERM and -EBUSY are all gated on flag bits this word does
    not set ([cpuset_can_fork] short-circuits on [same_cs], leaving
    [pids_can_fork]'s -EAGAIN as the only cgroup answer); -EFAULT cannot
    arise because legacy [clone] dereferences no user pointer for this
    word; -ENOSPC is remapped by [alloc_pid]; and -ERESTARTNOINTR and
    -EINTR are reachable inside [copy_process] but never reach a
    register the program can read — riscv64's [arch_do_signal_or_restart]
    (arch/riscv/kernel/signal.c) restarts -ERESTARTNOINTR
    unconditionally, its "revert the decision to restart" branch
    covering only -ERESTARTNOHAND, -ERESTART_RESTARTBLOCK and a
    non-SA_RESTART -ERESTARTSYS, and the -EINTR arm is reached only with
    SIGKILL pending, which group-exits the task before it returns to
    userspace.  This is the argument [Mremap.mremap_errnos] makes for its own
    killable lock.

    THREE ENVIRONMENT RESTRICTIONS, stated rather than modeled, in the
    shape [Kernel.Sys.getpid_spec] uses for the same problem.  Each can make a real
    kernel answer something outside this list, and none is visible to
    the model:
    - a parent holding INHERITABLE PERF EVENTS reaches
      [perf_event_init_task], whose [inherit_group] has an -EINVAL of
      its own plus whatever a PMU's [event_init] returns.
      [perf_event_init_context] returns 0 immediately when the parent
      has no [perf_event_ctxp], and [perf_event_open] (241) is outside
      [Specs.modeled_sysnos], so a modeled run creates none — but it could
      have INHERITED one from its own parent.  The model describes a
      process that holds none.
    - a BPF LSM program attached to [task_alloc] may return any errno.
    - with CONFIG_SCHED_CLASS_EXT and a BPF scheduler attached,
      [sched_cgroup_fork] (int-returning from v6.12) forwards the
      scheduler's own task init — [scx_ops_init_task] at v6.12,
      [scx_init_task] from v6.16, [__scx_init_task] from v7.1, and the
      file moving from kernel/sched/ext.c to kernel/sched/ext/ext.c at
      v7.2, which is a SEPARATE change from any of the renames —
      through
      [ops_sanitize_err], which passes any value in [-MAX_ERRNO, -1]. *)
Definition clone_errnos : list Z := [EAGAIN; ENOMEM; EMFILE; EACCES].

(** The one flag word this model answers: a child that shares nothing,
    reporting [SIGCHLD] on exit.  This is what [fork] is.

    THE TEST IS ON THE WHOLE 64-BIT REGISTER, which is STRICTER than the
    kernel's own reading and deliberately so.  [SYSCALL_DEFINE5(clone)]
    splits [lower_32_bits(clone_flags)] into two disjoint halves —
    [.flags] gets it masked with [~CSIGNAL] and [.exit_signal] gets it
    masked with [CSIGNAL] — and reads nothing above bit 31, so a
    register of 0x1_00000011 is a plain fork to
    Linux and is DECLINED here.  Declining is the fail-closed direction:
    the model refuses a call it could have answered, rather than
    answering one it should not.  Nothing musl issues sets those bits —
    [_Fork] passes the literal [SIGCHLD] — so the strictness costs
    nothing that has been observed.  What it costs the CLAIM is that
    this model's admitted set is the singleton {17} where the kernel's
    is every word congruent to 17 modulo 2^32.

    [clone3] does NOT truncate: [copy_clone_args_from_user] assigns the
    struct's [flags] field to [kernel_clone_args.flags] whole, and
    [CLONE_CLEAR_SIGHAND] really is bit 32.  So the 64-bit test
    [clone3_fork_args_b] makes on that field is EXACT rather than
    strict, and the asymmetry between the two entry points is the
    kernel's rather than this model's.

    THE THREAD-CREATING WORDS ARE DECLINED, AND -EAGAIN IS NOT AN
    ALTERNATIVE.  A [pthread_create] issues
    [CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND | CLONE_THREAD |
    CLONE_SYSVSEM | CLONE_SETTLS | CLONE_PARENT_SETTID |
    CLONE_CHILD_CLEARTID] — musl 1.2.6 adds [CLONE_DETACHED], glibc does
    not — and Linux ACCEPTS it and returns a tid.  This model cannot
    represent the result: a second task sharing the address space is not
    a configuration the development has.

    The tempting repair is to answer an errno instead.  -EAGAIN is real
    for this word: [copy_process] keeps its [RLIMIT_NPROC] and
    [nr_threads >= max_threads] ceilings whatever the flags are, and
    [copy_files] under [CLONE_FILES] and [copy_mm] under [CLONE_VM]
    merely take references, so the -EMFILE and the -ENOMEM a plain fork
    can raise fall away and -EAGAIN is what is left.  Answering it would
    make [pthread_create] fail deterministically and keep termination
    decidable, which is what an unmodeled arm costs today.

    It would also be wrong, in the direction this file cares about most.
    The admitted set would no longer be a SUBSET of Linux's answers in
    the sense that matters at the checker: with the success arm absent,
    a run in which the kernel really created the thread is not merely
    uncovered, it is REJECTED — the model asserting that Linux could not
    have done what it did.  That is a false claim about Linux rather
    than an honest gap, and [Specs.v]'s own rule ("must fail closed
    rather than admit an approximation") names the shape.  The gate
    therefore stays an
    allowlist of one word. *)
Definition clone_fork_flags_b (flags : word) : bool :=
  bv_eqb flags (Z_to_bv 64 SIGCHLD).

(** No descriptor this model would give the child a PRIVATE offset for.

    [FdFile] and [FdFileW] inline the offset into the descriptor, so a
    copied [m_fds] would hand the child an offset of its own where
    [copy_files] gave it a shared one — a wrong answer rather than a
    declined one.

    [FdDir] shares an [f_pos] on a real kernel exactly as a regular file
    does, and the reason it does not close this gate is NOT that the
    model has no position for it — that would be the same defect one
    line up, read backwards.  It is that no modeled syscall can OBSERVE
    a directory position: [ReadWrite.lseek_spec] declines [FdDir], and
    [Readdir.getdents64_spec] declines every listing while its one
    directory answer — [filldir64]'s -EINVAL for a buffer with no room
    for an entry — is the arm on which the kernel leaves [f_pos]
    untouched.  So there is no answer for the sharing to make wrong.
    Give either a position-moving arm and [FdDir] joins the gate.

    [FdChannel] is the honest hole, and it is a hole in the MODEL rather
    than in this test.  A channel's position is not in the descriptor at
    all: it is the run's [InputStream] in [m_stdin], or a write side
    with no position.  The [Ioctl.ioctl_spec] ASSUMPTION block says how
    the three standard descriptors earn their far-end agnosticism — by
    WIDENING, [ReadWrite.write_spec] admitting a short return and [ReadWrite.read_spec] a
    short read or end-of-input — and that widening is over HOW MANY
    bytes arrive.  A child that READ from an inherited fd 0 moves the
    shared offset, so the parent's next read would deliver a later
    SUFFIX, and which bytes arrive is not what either widening ranges
    over.  Declining on channels as well would not close the hole and
    would nearly cost the arm.  It would not close it because the FILE
    SYSTEM channel above survives a child holding no descriptor at all.
    And it would nearly cost it because [State.init_model] seeds three
    channels and [Open.close_spec] is the only thing that removes one, so the
    programs left able to clone would be those that had closed all three
    standard descriptors first.  The gate closes on what it can name;
    the channel case is a known gap.

    [FdSocket] is declined for the [FdFile] reason with a different
    payload.  The descriptor inlines the connection's remaining receive
    script, and reading it rewrites the entry in place —
    [ReadWrite.read_spec] advances the script past the bytes it
    delivered, and the -ECONNRESET and -ETIMEDOUT arms move the entry to
    [SkReset] once the error has been reported.  A copied [m_fds] would
    give the child its own copy of that state, so the peer's reset would
    be reported once to each where Linux reports it once for the
    connection, and bytes the child consumed would still be waiting for
    the parent.  That is a wrong answer, not a declined one, so this
    gate names it. *)
Definition clone_no_shared_file_b (fds : list (word * FdEntry)) : bool :=
  forallb (fun e => match snd e with
                    | FdFile _ _ | FdFileW _ _ | FdFileA _ _
                    | FdFileRW _ _ | FdSocket _ => false
                    | FdChannel _ | FdDir => true
                    (* A PIPE END JOINS THE GATE, fail-closed, and it is
                       the one entry here whose shared object is the
                       POINT of the descriptor rather than a payload it
                       happens to carry.  [copy_files] hands the child a
                       second reference to the same [struct file]
                       (kernel/fork.c, v6.18.46), and both references
                       name one [pipe_inode_info] -- one ring, one
                       [pipe->readers]/[pipe->writers] count.  So a
                       child that reads drains bytes the parent then
                       cannot read, and a child that CLOSES its copy
                       does not drop the writer count, which is what
                       decides whether the peer sees EOF or blocks
                       ([pipe_release], fs/pipe.c:730-733, and
                       [anon_pipe_read]'s [!pipe->writers] test at
                       :370-371, v6.18.46).  Deriving the real answer
                       needs both the queue and a reference count this
                       model does not have -- an [FdEntry] carries no
                       per-description state and nothing counts ends --
                       so [clone] with a pipe end open declines. *)
                    | FdPipe _ _ => false
                    (* /dev/null PASSES, for the [FdDir] reason: the
                       child's second reference to the [struct file]
                       ([copy_files] -> [dup_fd]'s [get_file],
                       kernel/fork.c and fs/file.c, v6.18.46) shares an
                       [f_pos] that [null_lseek] pins at 0 and that
                       [read_null]/[write_null] never move
                       (drivers/char/mem.c), and no modeled arm on this
                       kind reads [f_flags].  A close in either process
                       drops nothing the other can observe: the node
                       has no reader or writer count.  So there is no
                       shared state for the sharing to make wrong. *)
                    | FdDevNull _ _ => true
                    (* /dev/urandom PASSES for the same reason: the shared
                       [struct file]'s [f_pos] is pinned at 0 and its
                       [f_flags] read by nothing modeled, and the bytes a
                       read hands out come from the run's declared stream
                       ([State.m_urandom]) rather than from the file.  The
                       child is not executed by this model ([clone] describes
                       the parent), so nothing it might read off the device
                       is a consumption the declaration has to account for:
                       the stream is what the device hands THIS process. *)
                    | FdUrandom => true
                    (* THE THREE OPAQUE OBJECTS PASS, each for its own
                       reason, and the reason is in every case that no
                       modeled arm reads the state the child's second
                       reference shares ([copy_files] -> [dup_fd]'s
                       [get_file], kernel/fork.c and fs/file.c, read at
                       v6.18.44; identical at v6.18.46):
                       - an O_PATH descriptor ([OProcPath]) has
                         [empty_fops] ([do_dentry_open], fs/open.c) and
                         does no I/O at all; the model reads only its
                         path, as a directory for [openat] and
                         [newfstatat], and neither process can change
                         that path.  A close in either drops nothing the
                         other can see: the file has no reader or writer
                         count.
                       - a /proc/sys file ([OProcFile]) shares an
                         [f_pos] that a child's read moves, and the
                         parent's next read is answered with bytes of
                         the environment's choice whatever the offset
                         ([ReadWrite.read_proc_spec]), so no answer the
                         model gives depends on it.
                       - an eventfd ([OEventFd]) shares one counter, and
                         every arm that would read or move it (read,
                         write, poll, epoll) declines on this kind. *)
                    | FdOpaque _ => true
                    end) fds.

(** The pids a successful [clone] may report.  Strictly positive, which
    is the never-zero decision above; below [PID_MAX_ENVELOPE], the same
    envelope [set_tid_address_spec] picks the caller's own tid in — so
    the intersection of the two windows applies, and
    [PID_MAX_ENVELOPE]'s own argument runs v6.12..v6.16, narrower than
    this section's; and different from that tid, because [alloc_pid]
    hands out a FREE pid and the caller's own is in use.

    THE LAST CONJUNCT IS VACUOUS UNTIL THE TID IS OBSERVED.  [m_tid]
    starts [None] ([State.init_model]) and nothing forces a [getpid] or
    a [set_tid_address] first, so a clone made before either admits the
    caller's own pid, which [alloc_pid] could not hand out.  A widening,
    not an unsound acceptance, and it sits beside a second one: this
    model retires no pid either.  Written as a boolean so the spec
    and the acceptor make one test rather than two that could drift. *)
Definition clone_pid_ok_b (m : Model) (r : word) : bool :=
  (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z &&
  (match m_tid m with None => true | Some t0 => negb (bv_eqb r t0) end).

(** The resolution both entry points share, once the arguments are known
    to describe a plain fork.  The caller's identity, descriptors, file
    system and clock are all untouched by its own [clone], and the child
    is not a thing this model holds — but the FACT that a child now
    exists is, because [Kernel.Exit.wait4_spec] answers -ECHILD only
    while no child has been created.  So the success branch, and only
    the success branch, records it with [State.with_children]: the
    errno alternative created nothing, and the [clone_no_shared_file_b]
    decline never reaches a resolution at all.

    Without this call the pair is unsound in a way neither side's proofs
    can see — [wait4] would answer -ECHILD for a caller that has a
    child, with the gate proved and the creating arm proved. See
    [State.with_children]'s own note, and
    [Checks.ProcessCreation.clone_checker_admits_a_pid], which pins the
    post-model and stops compiling if this line is removed. *)
Definition clone_resolve : Sys SyscallEffect :=
  m <- get_model ;;
  if negb (clone_no_shared_file_b (m_fds m)) then unmodeled
  else
    alt (e <- errno_from clone_errnos ;; err_ret e)
        (pid <- choose (fun p => clone_pid_ok_b m p = true) ;;
         modify with_children ;;
         ret_only pid).

Definition clone_spec (flags : word) : Sys SyscallEffect :=
  if clone_fork_flags_b flags then clone_resolve else unmodeled.

(** [clone3] reaches the same [kernel_clone] through a struct in user
    memory rather than through registers.  [struct clone_args]
    (include/uapi/linux/sched.h) is eleven [__aligned_u64] fields —
    flags, pidfd, child_tid, parent_tid, exit_signal, stack, stack_size,
    tls, set_tid, set_tid_size, cgroup — and [copy_clone_args_from_user]
    accepts a [size] in [CLONE_ARGS_SIZE_VER0, PAGE_SIZE] and rejects
    outside it, in that order: [usize > PAGE_SIZE] is -E2BIG first, then
    [usize < CLONE_ARGS_SIZE_VER0] is -EINVAL.  Inside that range and
    below the struct's own size it zero-fills what the caller did not
    supply; above the struct's own size it requires the excess to be
    zero and answers -E2BIG otherwise.  One further size gate does not
    reach the admitted image but is part of the same function:
    [CLONE_INTO_CGROUP] additionally demands
    [usize >= CLONE_ARGS_SIZE_VER2].

    This model answers ONE size, the full struct, and declines the
    short forms.  A short [size] is a different kernel path — the
    zero-fill in [copy_struct_from_user] — and reproducing it would mean
    modeling how many fields the caller's headers had.  Declining is
    fail-closed in the ordinary way, and it costs nothing observed: NO
    LIBC EMITS A FORK-SHAPED CLONE3.  glibc's [fork] goes through
    [arch_fork] to a raw legacy [clone].  Its clone3 callers are three,
    none of them on a [fork] path.  [__clone_internal] is reached from
    [pthread_create], which passes
    [CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SYSVSEM | CLONE_SIGHAND |
    CLONE_THREAD | CLONE_SETTLS | CLONE_PARENT_SETTID |
    CLONE_CHILD_CLEARTID] — the opposite of the admitted image, and
    refused by the flags
    field before the size is reached.  [posix_spawn] is the third, and
    it reaches [__clone3] DIRECTLY (sysdeps/unix/sysv/linux/spawni.c) —
    that one does pass this struct's size with
    [exit_signal = SIGCHLD], but with
    [CLONE_CLEAR_SIGHAND | CLONE_VM | CLONE_VFORK] in its BASE flag word
    — a spawn asking for a cgroup or a pidfd sets more — so it is
    refused on the flags field whichever it is.  riscv64 has the [clone3] wrapper, so it
    really executes here.  musl issues no clone3 at all.  So this arm, like the legacy one, is
    reached by a RAW syscall.

    The admitted image is the whole struct zero except [exit_signal], at
    offset 32, equal to [SIGCHLD] — which is [clone(SIGCHLD, 0)] told a
    different way, and reaches [kernel_clone] with the same arguments.

    ONE ASYMMETRY BETWEEN THE TWO ENTRY POINTS IS THIS MODEL'S OWN, and
    unlike the 32-bit truncation above it is not the kernel's.  The
    legacy arm fetches [arg 0] and nothing else, so it answers
    [clone(SIGCHLD, newsp)] for ANY [newsp]; this image requires [stack]
    and [stack_size] to be zero, so the same request through 435 is
    declined.  Both directions are sound — the caller's return is the
    same whatever [newsp] is, since [copy_thread] only seats it in the
    CHILD's registers — and the legacy arm is the more permissive of the
    two.  Narrowing 220 to match would be a change to the modeled
    surface for no gain, and widening 435 to match would mean admitting
    a [stack]/[stack_size] pair whose only effect is on a child this
    model does not step.  Left as it is, and written down because the
    sentence above would otherwise read as if the two were identical.

    In particular [flags] must be zero, so the sharing bits the header
    paragraph names are excluded here by the same allowlist.

    [sizeof (struct clone_args)] is 88 and its field order is unchanged
    in mainline v5.10..v7.2 and in stable linux-6.6.y, linux-6.12.y and
    linux-6.17.y — and that is LOG-EXHAUSTIVE rather than sampled: the
    last commit to touch the struct's fields is ef2c41cf38a7, released
    at v5.7, so nothing in the window could have changed it.  The header
    gained six DEFINES at v7.1 — four of them clone3 flags — and v7.2's
    copy is byte-identical to v7.1's, while the struct itself gained
    nothing, so there is no VER3 in the window — which
    [copy_clone_args_from_user]'s own
    [BUILD_BUG_ON(sizeof(struct clone_args) != CLONE_ARGS_SIZE_VER2)]
    would catch first anyway.  A future
    one would change this number, which is why it is a constant rather
    than a literal. *)
Definition CLONE_ARGS_SIZE : Z := 88.

(** Field [k] of a [struct clone_args] image, little-endian. *)
Definition clone_args_field (bs : list byte) (k : nat) : word :=
  le_bytes_to_word (firstn 8 (skipn (8 * k) bs)).

Definition clone3_fork_args_b (bs : list byte) : bool :=
  w_is0 (clone_args_field bs 0)                          (* flags        *)
  && w_is0 (clone_args_field bs 1)                       (* pidfd        *)
  && w_is0 (clone_args_field bs 2)                       (* child_tid    *)
  && w_is0 (clone_args_field bs 3)                       (* parent_tid   *)
  && bv_eqb (clone_args_field bs 4) (Z_to_bv 64 SIGCHLD) (* exit_signal  *)
  && w_is0 (clone_args_field bs 5)                       (* stack        *)
  && w_is0 (clone_args_field bs 6)                       (* stack_size   *)
  && w_is0 (clone_args_field bs 7)                       (* tls          *)
  && w_is0 (clone_args_field bs 8)                       (* set_tid      *)
  && w_is0 (clone_args_field bs 9)                       (* set_tid_size *)
  && w_is0 (clone_args_field bs 10).                     (* cgroup       *)

(** [CLONE_ARGS_SIZE] as a [nat], for the copy-in ledger.  The mirror is
    a theorem rather than a second literal, so the two cannot drift. *)
Definition CLONE_ARGS_SIZE_nat : nat := 88.

Lemma clone_args_size_nat_ok : Z.of_nat CLONE_ARGS_SIZE_nat = CLONE_ARGS_SIZE.
Proof. reflexivity. Qed.

(** THE STRUCT IS READ, AND THE LEDGER SAYS SO.  [clone3] differs from
    legacy [clone] in exactly one observable way before the resolution:
    it copies [struct clone_args] out of user memory, and
    [copy_struct_from_user] faults every page of it in.  Recording that
    range is what stops the model admitting an allocation the kernel
    refuses -- [eff_copyins] feeds [syscall_effect_accesses] and so
    [Run.materialize_model_accesses], which is where a straddling
    struct in a [MAP_NORESERVE] region charges its second page.

    The ledger goes on the paths PAST a successful read and nowhere
    else.  A [size] the model declines never reaches the copy; an
    unreadable struct is a copy that FAILED, and Linux charges nothing
    for it either.  Both of those are [unmodeled] here, which carries no
    effect at all, so the boundary is exactly "the read succeeded". *)
Definition clone3_resolve (uargs : word) : Sys SyscallEffect :=
  record_copyins [(uargs, CLONE_ARGS_SIZE_nat)] clone_resolve.

(** The ledger is the ONLY thing [clone3_resolve] adds: strip it and what
    is left is the very outcome [clone_resolve] admits, with the same
    return, model and events.  Everything proved about the shared
    resolution therefore carries over to [clone3] unchanged. *)
Lemma clone3_resolve_inv : forall uargs i m eff m' evs,
  clone3_resolve uargs i m (Ok eff m' evs) ->
  exists e0, clone_resolve i m (Ok e0 m' evs) /\ eff_ret eff = eff_ret e0.
Proof.
  intros uargs i m eff m' evs H.
  unfold clone3_resolve, record_copyins in H.
  destruct H as (e0 & m0 & evs0 & evs2 & H0 & Hp & Hevs).
  unfold pure in Hp. inversion Hp; clear Hp; subst.
  exists e0. rewrite app_nil_r in *. split; [exact H0 | reflexivity].
Qed.

Definition clone3_spec (uargs size : word) : Sys SyscallEffect :=
  if negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)) then unmodeled
  else
    i <- input ;;
    match read_bytes_map (in_mem i) uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
    | None => unmodeled       (* the struct is not wholly readable *)
    | Some bs =>
        if clone3_fork_args_b bs then clone3_resolve uargs else unmodeled
    end.
