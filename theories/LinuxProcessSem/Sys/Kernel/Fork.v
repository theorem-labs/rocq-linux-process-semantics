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
  Syscall Uapi.
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
      [clone_fork_flags_b], [clone_ns_flags_b] and [clone_class] below: no
      flag word that gets a child has [CLONE_VM] or [CLONE_VFORK], so
      [copy_process] takes [dup_mm] and the two address spaces are
      separate from the call onwards.
    - THE DESCRIPTOR TABLE AND THE FILE OFFSET.  [CLONE_FILES] shares the
      table itself and [CLONE_FS] shares [fs_struct] (so a child [chdir]
      moves the parent's [AT_FDCWD], the only dirfd [Open.openat_spec]
      accepts); [CLONE_PIDFD] installs a NEW descriptor in the PARENT's
      table.  No word that gets a child holds any of the three.  What survives
      even a plain fork is the FILE OFFSET: [copy_files] duplicates the
      table while both tables point at the same [struct file], so a
      child's [read] advances the offset the parent will read from next.
      [State.FdEntry] inlines that offset into the descriptor
      ([FdFile p off]) and [ReadWrite.read_spec] advances it privately, so the
      model cannot express the sharing.  Closed by declining the call
      outright while any such descriptor is open —
      [clone_no_shared_file_b], stated as
      [Checks.ProcessCreation.clone_open_file_unmodeled] — except a
      [clone3] whose size tests or struct copy fail ([clone3_copy]:
      -E2BIG, -EINVAL or -EFAULT) or whose struct [clone3_einval_sz]
      refuses (-EINVAL); these answer whatever the table holds and
      create no child.  An inherited
      file's offset ([State.OInherited]) is handed to the child instead:
      the caller keeps the descriptor without it ([forfeit_inherited]).
    - PARENT MEMORY WRITTEN BY THE CALL ITSELF.  [CLONE_PARENT_SETTID]
      writes the child tid through [parent_tidptr] and [CLONE_PIDFD]
      writes an int through the same pointer.  No word that gets a child
      holds [CLONE_PIDFD], and an -EINVAL writes nothing.  A word that
      gets a child with [CLONE_PARENT_SETTID] carries that write in its
      effect ([clone_with_stores], [tid_store_case]), and declines where
      the memory backs the four bytes only in part; every other answer
      writes no byte of user memory and its effect carries no write
      entry.

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
    half is its signal gate — [Signal.sigaction_accepted], whose
    accepted set is {SIGINT, SIGTERM}, and [Signal.sigchld_dfl_install],
    which answers a SIGCHLD install only when its handler word is
    [SIG_DFL].  So the disposition SIGCHLD is delivered against is the
    inherited one or [SIG_DFL], both of which discard it, and every
    install that would change that fails closed at the signal.
    [Checks.Cases.Kernel.Signal.rt_sigaction_sigchld_unmodeled]
    pins that, and the note above [Signal.sigaction_accepted] records
    the obligation this arm puts on it.  The
    STARTING disposition and mask are inherited across [execve] —
    [flush_signal_handlers] resets handlers to [SIG_DFL] but PRESERVES
    [SIG_IGN], and fs/exec.c writes no [->blocked] at all — so both are
    a property of how the process was started, the same shape as
    [State.access_okb]'s post-[execve] [pmlen = 0].

    ALLOWLIST, NOT BLOCKLIST.  The gates admit the one flag word
    [SIGCHLD] ([clone_fork_flags_b]), [SIGCHLD] plus namespace bits
    and nothing else ([clone_ns_flags_b]), and either of those two with
    bits of [clone_extra_bits] ([clone_class]: [CLONE_SYSVSEM] and the
    four tid bits), and give no child for any other.  Another word answers
    -EINVAL when its decoded record exists
    and Linux's argument-only checks refuse it ([clone_arg_checks]: a
    refusal that creates no child and reads only the arguments), for
    [clone] only behind the descriptor gate ([clone_einval]), or, for
    [clone3], when its own tests refuse the struct ([clone3_pre]); and
    declines otherwise.
    Naming the dangerous bits
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
    only.  glibc's word is admitted through [clone_class]: its child
    stores its own pid at a4 in its own copy of the memory, and its
    [CLONE_CHILD_CLEARTID] store at exit is made only while another
    holder pins the child's mm, which without [CLONE_VM] nothing modeled
    does ([clone_tid_bits]).  That is a different writer
    from the one [set_tid_address_spec]'s ignored [tidptr] rests on
    being unable to fire: that one is the CALLER's own
    [clear_child_tid], and no admitted word makes a second holder of the
    caller's mm.

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
    name in [Checks.ProcessCreation].  The namespace word is such a
    change, and it has its own gate and resolution
    ([clone_ns_flags_b], [clone_ns_resolve]) rather than a wider test
    here.

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
    (flags, newsp, parent_tidptr, tls, child_tidptr).  The tid pointers
    and [tls] are used only under [CLONE_PARENT_SETTID] (a [put_user]
    into the caller's memory, not a read), [CLONE_CHILD_SETTID] (a
    store into the child's memory) and [CLONE_SETTLS] (the child's tp).
    This spec reads the parent-tid pointer for the caller's store
    ([clone_with_stores]) and the child-tid pointer to decide that the
    child's store is one the core can make ([child_tid_ok]); [newsp] and
    [tls] reach only the child's registers ([Procs.child_ms]).  The two
    words [clone_fork_flags_b] and [clone_ns_flags_b] admit read none of
    them, exactly as
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

(** The clone failures this model admits for the FORK word (the
    namespace word admits every errno but -EINTR: see [clone_ns_resolve]).
    Enumerated by walking every error return in [kernel_clone]
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

    THREE HOST REFUSERS, named as launch values rather than stated as
    restrictions ([State.CloneRefusers], read through
    [State.m_clone_refusers]).  Each can make a real kernel answer
    something outside this list, and none is visible to the model:
    - a parent holding INHERITABLE PERF EVENTS reaches
      [perf_event_init_task], whose [inherit_group] has an -EINVAL of
      its own plus whatever a PMU's [event_init] returns.
      [perf_event_init_context] returns 0 immediately when the parent
      has no [perf_event_ctxp], and [perf_event_open] (241) is outside
      [Specs.modeled_sysnos], so a modeled run creates none — but it could
      have INHERITED one from its own parent, and a process outside the
      model can attach one to it during the run ([State.cr_perf_inherit]).
    - a BPF LSM program attached to [task_alloc] may return any errno
      ([State.cr_bpf_task_alloc]).
    - with CONFIG_SCHED_CLASS_EXT and a BPF scheduler attached,
      [sched_cgroup_fork] (int-returning from v6.12) forwards the
      scheduler's own task init — [scx_ops_init_task] at v6.12,
      [scx_init_task] from v6.16, [__scx_init_task] from v7.1, and the
      file moving from kernel/sched/ext.c to kernel/sched/ext/ext.c at
      v7.2, which is a SEPARATE change from any of the renames —
      through
      [ops_sanitize_err], which passes any value in [-MAX_ERRNO, -1]
      ([State.cr_sched_ext]; the host can attach one during the run).
    This list is the answer at the default, [State.no_clone_refusers],
    which [Run.valid_input] and its sibling launch predicates pin.  With
    any refuser present, [clone_spec] and [clone3_spec] admit every
    errno from 1 to 4095 beside it ([clone_refusable]). *)
Definition clone_errnos : list Z := [EAGAIN; ENOMEM; EMFILE; EACCES].

(** The fork word: a child that shares nothing, reporting [SIGCHLD] on
    exit.  This is what [fork] is.  (The other word that gets a child,
    [SIGCHLD] plus namespace bits, has its own gate, [clone_ns_flags_b].)

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
    rather than admit an approximation") names the shape.  This gate
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
    [Readdir.getdents64_spec] declines every [FdDir] listing while its one
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
                    (* FIVE OPAQUE OBJECTS PASS, each for its own
                       reason, and the reason is in every case that no
                       answer the model gives depends on the state the
                       child's second reference shares ([copy_files] ->
                       [dup_fd]'s [get_file], kernel/fork.c and
                       fs/file.c, read at v6.18.44; identical at
                       v6.18.46):
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
                       - an eventfd an earlier clone shared ([OEventFd],
                         made by [share_eventfds] below) shares one
                         counter, and the model already holds that
                         counter as the environment's: a read answers any
                         nonzero value or -EAGAIN, and a write 8 or
                         -EAGAIN, whatever another writer has done
                         ([ReadWrite.read_eventfd_spec],
                         [ReadWrite.write_eventfd_spec]); select, poll
                         and epoll decline on it.  The child is one more
                         such writer.  It also shares [f_flags], whose
                         O_NONBLOCK those two arms read
                         ([ReadWrite.efd_nonblock_b]); SCOPE.md assumes
                         no other holder changes it.
                       - a namespace and mount model file ([ONsFile]) shares an [f_pos]
                         and [f_flags], and nothing modeled reads either:
                         every arm but close, close_range and fcntl's
                         F_SETFD/F_GETFD declines on this kind.
                       - an inherited file whose offset the model no
                         longer holds ([OInherited None]; see
                         [forfeit_inherited] below) shares an [f_pos]
                         and [f_flags] that nothing modeled reads on it:
                         close, close_range and fcntl's F_SETFD/F_GETFD
                         answer on it, as on [ONsFile]; [write] (-EBADF)
                         and [setns] (-EINVAL) also answer on it, from
                         the description's access mode and file type,
                         which no holder changes, and neither answer
                         depends on [f_pos] or [f_flags]; every other
                         arm declines on it.
                       THREE DECLINE, fail-closed:
                       - the /proc/self/fd directory ([OProcFdDir])
                         shares the [f_pos] that [getdents64] reads and
                         moves, and the model holds that position in the
                         parent's entry ([Readdir.procfd_getdents_spec]),
                         so a child's listing would leave it wrong.
                       - a signalfd ([OSignalFd]) shares its mask, which
                         [signalfd4] on the same descriptor may change in
                         either process (fs/signalfd.c [do_signalfd4],
                         read at v6.18.44; identical at v6.18.46).
                       - a live inherited file ([OInherited (Some _)])
                         shares the [f_pos] that [read] moves, and the
                         model holds that offset in the entry
                         ([ReadWrite.read_spec]), for the [FdFile] reason
                         above. Both words ask this gate of the
                         table [forfeit_inherited] leaves the
                         caller, which holds no live one
                         ([clone_resolve], [clone_ns_resolve]).
                       - an alias ([OAlias], left by [Fs.File.dup3_spec]'s
                         move) names a regular file's description whose
                         [f_pos] its partner's entry carries; the child
                         would hold a third descriptor of it, and the
                         one-descriptor argument the alias rests on
                         ([State.OAlias]) would not hold. In a run its
                         partner holds that regular file, which declines
                         above as well; the alias declines on its own so
                         that the gate says so. *)
                    | FdOpaque (OProcPath _ | OProcFile _ | OEventFd _ | ONsFile _
                                | OInherited None) => true
                    | FdOpaque (OProcFdDir _ _ | OSignalFd _ _ | OInherited (Some _)
                                | OAlias _) => false
                    (* AN AF_UNIX SEQPACKET END DECLINES, for the pipe
                       reason: the child's second reference names the
                       same socket, whose peer and queue both copies
                       share, and a close in one process does not release
                       it (the socket's [sock_close], net/socket.c:1454-1458,
                       runs only when the last reference goes: [fput],
                       fs/file_table.c:579-583, v6.18.46), so the
                       peer's end of file would depend on a reference
                       count the model does not hold.  It is also what
                       keeps [State.seq_peer] exact: each end has one
                       descriptor, in this process. *)
                    | FdSeqpacket _ _ _ => false
                    (* A STREAM-PAIR END JOINS THE GATE, fail-closed, for
                       the pipe's reason: the child's copy names the same
                       socket, so a child that reads drains the parent's
                       queue and a child that closes its copy does not run
                       [unix_release_sock], which happens at the last
                       [fput] -- and [State.stream_peer] reads ends off
                       the fd table, which a copied table would double. *)
                    | FdStream _ _ _ => false
                    (* AN EVENTFD PASSES, AND THE CLONE MAKES IT THE
                       SHARED KIND.  The child's copy names the same
                       [eventfd_ctx], so after the clone a child that
                       reads or writes moves the counter [State.FdEventfd]
                       keeps in this one entry.  The success branch
                       therefore replaces the entry with
                       [FdOpaque (OEventFd w)] ([share_eventfds] below),
                       on which no arm reads a counter the model stores:
                       after a clone the description is shared by two
                       tasks, so read and write answer from the
                       environment's counter
                       ([ReadWrite.read_eventfd_spec],
                       [ReadWrite.write_eventfd_spec]) and select, poll
                       and epoll decline.  Before the clone, and after a
                       clone that failed, the entry stays [FdEventfd] and
                       the counter stays modeled. *)
                    | FdEventfd _ => true
                    (* A DATAGRAM SOCKET takes the [FdSocket] answer, for
                       [Fs.File.dup_modeled_entry]'s reason: one rule for
                       every socket kind. *)
                    | FdDgram _ => false
                    (* AN UNNAMED FILE JOINS THE GATE: the child's copy
                       would share the one [struct file] -- its [f_pos]
                       -- and the inode, so a child's write would move
                       contents that [State.FdAnon] keeps in this
                       process's entries alone.  SCOPE.md states that an
                       unnamed file is this process's only. *)
                    | FdAnon _ _ => false
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

(** THE PARENT GIVES UP THE OFFSET OF EACH INHERITED DESCRIPTOR at a
    clone of either word.

    Linux: the clone has no CLONE_FILES, so [copy_files] copies the
    table with [dup_fd], and each copied slot takes one more reference
    on the SAME [struct file] (kernel/fork.c [copy_files]; fs/file.c
    [dup_fd]; v6.18.46).  The offset is that file's [f_pos], and a
    [read] through either table moves it ([ksys_read],
    fs/read_write.c).  The model holds the offset of an inherited file
    inside the descriptor's entry ([State.OInherited]), so two tables
    that both held it live would hold two offsets for one.

    So the caller keeps each such descriptor as [OInherited None], which
    holds no offset: [close], [close_range] and [fcntl]'s [F_GETFD] and
    [F_SETFD] answer on it, and every call that reads or moves the offset
    declines.  The child is built from the caller's table BEFORE the call
    (the multi-process core's [Procs.child_entry]), so it keeps the live
    entry, and after the clone the child is the only process of the
    configuration that holds the offset.  In a one-process run the child
    is not modeled, and the caller holds no offset an unseen child could
    move.  Nothing else makes a second live entry for one description:
    [File.dup_modeled_entry] declines every opaque kind for [dup] and
    [dup3], and [fcntl]'s [F_DUPFD] is not modeled.  So at most one
    descriptor entry of a configuration holds each inherited offset. *)
Definition inherited_live_b (e : FdEntry) : bool :=
  match e with
  | FdOpaque (OInherited (Some _)) => true
  | _ => false
  end.

(** THE FUTURE-CONSTRUCTOR OBLIGATION, stated here and beside
    [eventfd_shared_entry].  A successful clone applies this function
    and [eventfd_shared_entry] to the caller's table, and no kind that
    exists today is changed by both ([forfeit_share_entry_comm] checks
    every one).  Both functions end in a wildcard arm, so a new
    [FdEntry] or [OpaqueFd] constructor does not stop the build here.
    Whoever adds one that both Linux effects reach (a description
    whose offset the model holds AND whose state two tasks would
    share) gives it both effects in both functions, or makes the clone
    gate [clone_no_shared_file_b] decline it.  This is a duty of the
    author who adds the constructor, not a premise on any input. *)
Definition forfeit_entry (e : FdEntry) : FdEntry :=
  match e with
  | FdOpaque (OInherited (Some _)) => FdOpaque (OInherited None)
  | _ => e
  end.

Definition forfeit_inherited (fds : list (word * FdEntry)) : list (word * FdEntry) :=
  map (fun kv => (fst kv, forfeit_entry (snd kv))) fds.

(** The caller's model after a successful clone of either word with
    only the forfeit applied: the table [clone_child_made] starts from
    before it shares the eventfds. *)
Definition forfeit_model (m : Model) : Model :=
  with_fds (forfeit_inherited (m_fds m)) m.

Lemma forfeit_entry_not_live : forall e, inherited_live_b (forfeit_entry e) = false.
Proof.
  intros [ch|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd0 st0|c|fam|aid af|o|i0 sd st];
    try reflexivity.
  destruct o as [q|q|fl|h|fl pos|mk fl|[[data off]|]|pt]; reflexivity.
Qed.

Lemma forfeit_entry_id : forall e, inherited_live_b e = false -> forfeit_entry e = e.
Proof.
  intros [ch|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd0 st0|c|fam|aid af|o|i0 sd st] H;
    try reflexivity.
  destruct o as [q|q|fl|h|fl pos|mk fl|[[data off]|]|pt]; try reflexivity.
  discriminate H.
Qed.

(** No entry the caller keeps holds a live offset... *)
Lemma forfeit_inherited_no_live : forall fds,
  forallb (fun kv => negb (inherited_live_b (snd kv))) (forfeit_inherited fds) = true.
Proof.
  intros fds. unfold forfeit_inherited. apply forallb_forall.
  intros kv Hin. apply in_map_iff in Hin as (kv0 & <- & _). cbn [snd].
  rewrite forfeit_entry_not_live. reflexivity.
Qed.

(** ...the caller keeps every descriptor number it had... *)
Lemma forfeit_inherited_keys : forall fds, map fst (forfeit_inherited fds) = map fst fds.
Proof.
  intros fds. unfold forfeit_inherited. rewrite map_map. reflexivity.
Qed.

Lemma fd_lookup_forfeit_inherited : forall fds k,
  fd_lookup (forfeit_inherited fds) k = option_map forfeit_entry (fd_lookup fds k).
Proof.
  induction fds as [|[k0 e] r IH]; intros k; [reflexivity|].
  cbn [forfeit_inherited map fst snd fd_lookup].
  destruct (bv_eqb k0 k); [reflexivity|]. exact (IH k).
Qed.

(** ...and a table without a live inherited entry is left as it was, so
    every table the gate passed before this change it passes unchanged. *)
Lemma forfeit_inherited_id : forall fds,
  forallb (fun kv => negb (inherited_live_b (snd kv))) fds = true ->
  forfeit_inherited fds = fds.
Proof.
  induction fds as [|[k e] r IH]; intros H; [reflexivity|].
  cbn [forallb snd] in H. apply andb_true_iff in H as [He Hr].
  apply negb_true_iff in He.
  cbn [forfeit_inherited map fst snd].
  rewrite (forfeit_entry_id e He). f_equal. exact (IH Hr).
Qed.

Lemma clone_no_shared_file_b_no_live : forall fds,
  clone_no_shared_file_b fds = true ->
  forallb (fun kv => negb (inherited_live_b (snd kv))) fds = true.
Proof.
  intros fds H. unfold clone_no_shared_file_b in H.
  rewrite forallb_forall in H. apply forallb_forall.
  intros kv Hin. specialize (H kv Hin). cbv beta in H |- *.
  destruct (snd kv) as [ch|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd0 st0|c|fam|aid af|o|i0 sd st];
    try reflexivity.
  destruct o as [q|q|fl|h|fl pos|mk fl|[[data off]|]|pt]; try reflexivity.
  cbn in H. discriminate H.
Qed.

Lemma forfeit_inherited_gate : forall fds,
  clone_no_shared_file_b fds = true -> forfeit_inherited fds = fds.
Proof.
  intros fds H. exact (forfeit_inherited_id fds (clone_no_shared_file_b_no_live fds H)).
Qed.

(** ...and a model whose table the gate passes is its own
    [forfeit_model]: on every table that holds no live inherited
    descriptor, the forfeit leaves the model as it was. *)
Lemma forfeit_model_gate : forall m,
  clone_no_shared_file_b (m_fds m) = true -> forfeit_model m = m.
Proof.
  intros m Hg. unfold forfeit_model. rewrite (forfeit_inherited_gate _ Hg).
  destruct m as [[t p] vm io fs pr lim tm]. reflexivity.
Qed.

(** THE EVENTFDS A SUCCESSFUL CLONE SHARES.

    [copy_files] gives the child a second reference to every open
    [struct file] (kernel/fork.c [copy_process], [dup_fd] in fs/file.c,
    Linux v6.18.46), so an eventfd open at the clone has one
    [eventfd_ctx] that two tasks can read and write.  So the success
    branch of each clone resolution turns every [State.FdEventfd] in the
    caller's table into [State.FdOpaque (State.OEventFd w)], on which no
    arm reads a counter the model stores: read and write answer from the
    environment's counter ([ReadWrite.read_eventfd_spec],
    [ReadWrite.write_eventfd_spec], which read [w]'s two bits), and
    select, poll and epoll decline.  The child's table, built by the multi-process
    core's [Procs.child_entry] from the caller's table before the call,
    gets the same conversion and nothing else: it shares the counter
    too, and it keeps each live inherited offset ([forfeit_inherited]
    applies to the caller alone).

    [w] is the part of the file's flag word the model keeps, rebuilt
    from the context: [EFD_SEMAPHORE] when [ef_semaphore], and
    O_NONBLOCK (= EFD_NONBLOCK) when [ef_nonblock].  [Fcntl.fcntl_spec]
    answers F_GETFL and F_SETFL on the shared kind exactly from [w].
    EFD_CLOEXEC is not in [w]: it is a bit of the descriptor table, not
    of the file, and [eventfd2] records none in [State.m_cloexec], so
    after the clone it is unknown unless an [F_SETFD] recorded it, and
    [Fcntl.fcntl_spec]'s F_GETFD declines on the shared kind where it is
    unknown ([Fcntl.getfd_declines]).  The rewrite keeps every entry at
    its number, so every close-on-exec key still names an open
    descriptor. *)
Definition eventfd_shared_flags (c : EventfdCtx) : word :=
  Z_to_bv 64 (Z.lor (if ef_semaphore c then EFD_SEMAPHORE else 0%Z)
                    (if ef_nonblock c then O_NONBLOCK else 0%Z)).

(** THE FUTURE-CONSTRUCTOR OBLIGATION, stated here and beside
    [forfeit_entry].  A successful clone applies this function and
    [forfeit_entry] to the caller's table, and no kind that exists
    today is changed by both ([forfeit_share_entry_comm] checks every
    one).  Both functions end in a wildcard arm, so a new [FdEntry] or
    [OpaqueFd] constructor does not stop the build here.  Whoever adds
    one that both Linux effects reach (state two tasks would share AND
    an offset the model holds) gives it both effects in both functions,
    or makes the clone gate [clone_no_shared_file_b] decline it.  This
    is a duty of the author who adds the constructor, not a premise on
    any input. *)
Definition eventfd_shared_entry (e : FdEntry) : FdEntry :=
  match e with
  | FdEventfd c => FdOpaque (OEventFd (eventfd_shared_flags c))
  | _ => e
  end.

Fixpoint share_eventfds (fds : list (word * FdEntry)) : list (word * FdEntry) :=
  match fds with
  | [] => []
  | (k, e) :: r => (k, eventfd_shared_entry e) :: share_eventfds r
  end.

(** The caller's model after a successful clone that returned [pid]:
    each live inherited offset forfeited ([forfeit_inherited]), every
    eventfd shared ([share_eventfds]), and the child recorded, its bit
    and its pid ([State.with_child]).  The child's own table is the
    caller's table BEFORE the call with only [share_eventfds] applied
    ([Procs.child_entry]), never this one: it keeps each live inherited
    offset. *)
Definition clone_child_made (pid : word) (m : Model) : Model :=
  with_child pid
    (with_fds (share_eventfds (forfeit_inherited (m_fds m))) m).

(** NO [FdEventfd] IS LEFT after the conversion, under any descriptor
    number: the post-clone table holds the counter nowhere. *)
Lemma share_eventfds_no_eventfd : forall fds fd c,
  fd_lookup (share_eventfds fds) fd <> Some (FdEventfd c).
Proof.
  induction fds as [|[k e] r IH]; intros fd c; cbn [share_eventfds fd_lookup].
  - discriminate.
  - destruct (bv_eqb k fd).
    + destruct e; cbn [eventfd_shared_entry]; discriminate.
    + apply IH.
Qed.

Lemma share_eventfds_no_eventfd_in : forall fds k c,
  ~ In (k, FdEventfd c) (share_eventfds fds).
Proof.
  induction fds as [|[k0 e] r IH]; intros k c; cbn [share_eventfds In].
  - tauto.
  - intros [Heq|Hin].
    + destruct e; cbn [eventfd_shared_entry] in Heq; inversion Heq.
    + exact (IH k c Hin).
Qed.

Lemma clone_child_made_no_eventfd : forall pid m fd c,
  fd_lookup (m_fds (clone_child_made pid m)) fd <> Some (FdEventfd c).
Proof.
  intros pid m fd c.
  exact (share_eventfds_no_eventfd (forfeit_inherited (m_fds m)) fd c).
Qed.

(** NEITHER CONVERSION OVERRIDES THE OTHER, entry by entry.  An eventfd
    is not a live inherited file and a shared eventfd is not one either,
    so [forfeit_entry] fixes both; a live inherited file is not an
    eventfd and its forfeited form is not one either, so
    [eventfd_shared_entry] fixes both; every other entry is fixed by
    each.  The case split below runs over every constructor of [FdEntry]
    and [OpaqueFd]; see the future-constructor obligation above
    [forfeit_entry] for why that is not automatic. *)
Lemma forfeit_share_entry_comm : forall e,
  eventfd_shared_entry (forfeit_entry e) = forfeit_entry (eventfd_shared_entry e).
Proof.
  intros [ch|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd0 st0|c|fam|aid af|o|i0 sd st];
    try reflexivity.
  destruct o as [q|q|fl|h|fl pos|mk fl|[[data off]|]|pt]; reflexivity.
Qed.

Lemma share_eventfds_map : forall fds,
  share_eventfds fds = map (fun kv => (fst kv, eventfd_shared_entry (snd kv))) fds.
Proof.
  induction fds as [|[k e] r IH]; [reflexivity|].
  cbn [share_eventfds map fst snd]. rewrite IH. reflexivity.
Qed.

(** The table equation: on every raw table, duplicate numbers included,
    sharing after the forfeit is the forfeit after sharing. *)
Lemma share_forfeit_comm : forall fds,
  share_eventfds (forfeit_inherited fds) = forfeit_inherited (share_eventfds fds).
Proof.
  intros fds. rewrite !share_eventfds_map. unfold forfeit_inherited.
  rewrite !map_map. apply map_ext. intros [k e]. cbn [fst snd].
  rewrite forfeit_share_entry_comm. reflexivity.
Qed.

(** Sharing keeps every descriptor number, in its place. *)
Lemma share_eventfds_keys : forall fds, map fst (share_eventfds fds) = map fst fds.
Proof.
  intros fds. rewrite share_eventfds_map, map_map. reflexivity.
Qed.

Lemma share_eventfds_length : forall fds, length (share_eventfds fds) = length fds.
Proof.
  intros fds. rewrite share_eventfds_map. apply length_map.
Qed.

Lemma fd_lookup_share_eventfds : forall fds k,
  fd_lookup (share_eventfds fds) k = option_map eventfd_shared_entry (fd_lookup fds k).
Proof.
  induction fds as [|[k0 e] r IH]; intros k; [reflexivity|].
  cbn [share_eventfds fd_lookup].
  destruct (bv_eqb k0 k); [reflexivity|]. exact (IH k).
Qed.

(** THE CALLER'S TABLE AFTER A SUCCESSFUL CLONE, descriptor by
    descriptor, under [fd_lookup]'s first match. *)
Lemma fd_lookup_clone_parent : forall fds k,
  fd_lookup (share_eventfds (forfeit_inherited fds)) k
  = option_map (fun e => eventfd_shared_entry (forfeit_entry e)) (fd_lookup fds k).
Proof.
  intros fds k. rewrite fd_lookup_share_eventfds, fd_lookup_forfeit_inherited.
  destruct (fd_lookup fds k); reflexivity.
Qed.

(** An absent descriptor stays absent. *)
Lemma fd_lookup_clone_parent_none : forall fds k,
  fd_lookup fds k = None ->
  fd_lookup (share_eventfds (forfeit_inherited fds)) k = None.
Proof.
  intros fds k H. rewrite fd_lookup_clone_parent, H. reflexivity.
Qed.

(** Where the forfeit changes nothing, the caller's entry is the one the
    eventfd conversion alone gives... *)
Lemma clone_parent_agrees_share : forall fds k e,
  fd_lookup fds k = Some e -> forfeit_entry e = e ->
  fd_lookup (share_eventfds (forfeit_inherited fds)) k = fd_lookup (share_eventfds fds) k.
Proof.
  intros fds k e Hl Hf.
  rewrite fd_lookup_clone_parent, fd_lookup_share_eventfds, Hl.
  cbn [option_map]. rewrite Hf. reflexivity.
Qed.

(** ...and where the eventfd conversion changes nothing, it is the one
    the forfeit alone gives. *)
Lemma clone_parent_agrees_forfeit : forall fds k e,
  fd_lookup fds k = Some e -> eventfd_shared_entry e = e ->
  fd_lookup (share_eventfds (forfeit_inherited fds)) k = fd_lookup (forfeit_inherited fds) k.
Proof.
  intros fds k e Hl Hs.
  rewrite fd_lookup_clone_parent, fd_lookup_forfeit_inherited, Hl.
  cbn [option_map]. rewrite forfeit_share_entry_comm, Hs. reflexivity.
Qed.

(** The caller keeps no live inherited offset after either conversion
    order. *)
Lemma clone_parent_no_live : forall fds,
  forallb (fun kv => negb (inherited_live_b (snd kv)))
          (share_eventfds (forfeit_inherited fds)) = true.
Proof.
  intros fds. rewrite share_forfeit_comm. apply forfeit_inherited_no_live.
Qed.

(** The child's table keeps each live inherited entry exactly, bytes and
    offset. *)
Lemma clone_child_keeps_inherited : forall fds k live,
  fd_lookup fds k = Some (FdOpaque (OInherited (Some live))) ->
  fd_lookup (share_eventfds fds) k = Some (FdOpaque (OInherited (Some live))).
Proof.
  intros fds k live H. rewrite fd_lookup_share_eventfds, H. reflexivity.
Qed.

(** THE GATE IS BLIND TO THE SHARING: a concrete eventfd and its shared
    form both pass, and every other entry is unchanged.  So no admission
    condition is added or removed by [share_eventfds]. *)
Lemma share_eventfds_gate : forall fds,
  clone_no_shared_file_b (share_eventfds fds) = clone_no_shared_file_b fds.
Proof.
  intros fds. rewrite share_eventfds_map. unfold clone_no_shared_file_b.
  induction fds as [|[k e] r IH]; [reflexivity|].
  cbn [map forallb fst snd]. rewrite IH. f_equal.
  destruct e as [ch|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd0 st0|c|fam|aid af|o|i0 sd st];
    reflexivity.
Qed.

(** On a table the gate passes, the caller's new table is the sharing
    alone: the forfeit has nothing left to change. *)
Lemma clone_child_made_gate : forall pid m,
  clone_no_shared_file_b (m_fds m) = true ->
  clone_child_made pid m = with_child pid (with_fds (share_eventfds (m_fds m)) m).
Proof.
  intros pid m Hg. unfold clone_child_made. rewrite (forfeit_inherited_gate _ Hg).
  reflexivity.
Qed.

(** The conversion changes the table and the child record and nothing
    else: [clone_child_made] is [State.with_child] over the caller's
    [forfeit_model] with its eventfds shared. *)
Lemma clone_child_made_forfeit_model : forall pid m,
  clone_child_made pid m
  = with_child pid (with_fds (share_eventfds (m_fds (forfeit_model m))) (forfeit_model m)).
Proof. reflexivity. Qed.
(** The resolution both entry points share, once the arguments are known
    to describe a plain fork.  The caller's identity, file system and
    clock are all untouched in Linux by its own [clone], and the child
    is not a thing this model holds — but the FACT that a child now
    exists is, because [Kernel.Exit.wait4_spec] answers -ECHILD only
    while no child has been created, and so is the model's copy of the
    caller's table: each live inherited descriptor is forfeited
    ([forfeit_inherited]) and every open eventfd is shared
    ([share_eventfds]).  So the success branch, and only the success
    branch, applies [clone_child_made], which does both to the table
    and records the child with [State.with_child]: the child bit
    [State.with_children] sets, and the returned pid appended to
    [State.procst_child_pids], the list a reap reads and removes from.
    The errno alternative created nothing and converts nothing, so a
    failed clone leaves every inherited offset and every eventfd
    counter where it was, and the [clone_no_shared_file_b] decline
    never reaches a resolution at all.  That gate is asked of the table
    the caller KEEPS ([forfeit_inherited]), as the namespace word's is;
    [share_eventfds] leaves its answer unchanged
    ([share_eventfds_gate]).

    Without this call the pair is unsound in a way neither side's proofs
    can see — [wait4] would answer -ECHILD for a caller that has a
    child, with the gate proved and the creating arm proved. See
    [State.with_children]'s own note, and
    [Checks.ProcessCreation.clone_checker_admits_a_pid], which pins the
    post-model and stops compiling if this line is removed. *)
Definition clone_resolve : Sys SyscallEffect :=
  m <- get_model ;;
  if negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))) then unmodeled
  else
    alt (e <- errno_from clone_errnos ;; err_ret e)
        (pid <- choose (fun p => clone_pid_ok_b m p = true) ;;
         modify (clone_child_made pid) ;;
         ret_only pid).

(* =========================================================================
   clone with namespace flags — the PARENT'S VIEW, and nothing else
   ========================================================================= *)

(** The seven namespace bits [clone_ns_flags_b] admits, as one mask.
    [copy_namespaces] (kernel/nsproxy.c) tests six of them and
    [CLONE_NEWTIME]; [copy_creds] (kernel/cred.c) tests the seventh,
    [CLONE_NEWUSER].  [CLONE_NEWTIME] is not here because legacy [clone]
    cannot carry it: see [Uapi.CLONE_NEWNS]. *)
Definition clone_ns_mask : Z :=
  Z.lor CLONE_NEWNS (Z.lor CLONE_NEWCGROUP (Z.lor CLONE_NEWUTS
    (Z.lor CLONE_NEWIPC (Z.lor CLONE_NEWUSER (Z.lor CLONE_NEWPID
      CLONE_NEWNET))))).

(** THE NAMESPACE WORD: [SIGCHLD] together with a NON-EMPTY set of the
    seven bits of [clone_ns_mask], and nothing else.  This is the call
    bubblewrap 0.13.1's parent makes ([raw_clone], utils.c, called from
    [main]) with the flag word
    [SIGCHLD | CLONE_NEWNS | CLONE_NEWUSER | CLONE_NEWPID | CLONE_NEWNET
    | CLONE_NEWIPC | CLONE_NEWUTS] and a NULL stack.

    THE TEST IS ON THE WHOLE 64-BIT REGISTER, strict in the same way
    [clone_fork_flags_b] is and for the same reason:
    [SYSCALL_DEFINE5(clone)] reads [lower_32_bits(clone_flags)] only, so
    a register with a bit above 31 set is the same call to Linux and is
    declined here.  Clearing the seven namespace bits must leave exactly
    [SIGCHLD], so the exit signal is SIGCHLD and every other flag bit is
    clear: each bit [Checks.ProcessCreation.clone_sharing_bits] names,
    and [CLONE_PTRACE], [CLONE_PARENT], [CLONE_DETACHED],
    [CLONE_UNTRACED] as well.  So every word this test admits passes
    each argument check at the head of [copy_process] (none of them
    reads a namespace bit without [CLONE_FS], [CLONE_THREAD] or
    [CLONE_SYSVSEM] beside it), and the tid pointers, [tls] and [newsp]
    are read by no code this word reaches in the PARENT, exactly as for
    the fork word.

    THE TWO TESTS ARE DISJOINT: the fork word holds no namespace bit and
    this test requires one.  [clone_spec] asks [clone_fork_flags_b]
    first, so the fork word keeps [clone_resolve] and its four errnos. *)
Definition clone_ns_flags_b (flags : word) : bool :=
  Z.eqb (Z.land (bv_unsigned flags) (Z.lnot clone_ns_mask)) SIGCHLD
  && negb (Z.eqb (Z.land (bv_unsigned flags) clone_ns_mask) 0).

(** The resolution of the namespace word.

    THE PARENT'S VIEW OF THIS CALL DELIBERATELY MODELS NO CHILD.  The
    child runs in the new namespaces, and what it does there is the
    subject of a separate child model (namespaces and mounts), not of this file.  The
    boundary is chosen, not a gap found later: this arm says what the
    CALLING process receives — a child pid or an errno — and that the
    process now has a child, and nothing about the child.  Everything
    [clone_spec]'s header says about the plain fork applies unchanged:
    no second configuration exists, the five channels named there stay
    open (the file system among them: a new mount namespace is a copy of
    the parent's mounts over the same superblocks, so a child can still
    write what the parent later reads), and the SIGCHLD the child's
    exit sends comes to nothing by the argument given there.

    WHAT THE PARENT SEES, from the kernel (each function read at
    v6.18.44):
    kernel/fork.c [SYSCALL_DEFINE5(clone)] read at v6.18.44; identical at v6.18.46.
    kernel/fork.c [kernel_clone] read at v6.18.44; identical at v6.18.46.
    kernel/fork.c [copy_process] read at v6.18.44; identical at v6.18.46.
    kernel/cred.c [copy_creds] read at v6.18.44; identical at v6.18.46.
    kernel/user_namespace.c [create_user_ns] read at v6.18.44; identical at v6.18.46.
    kernel/nsproxy.c [copy_namespaces] read at v6.18.44; identical at v6.18.46.
    kernel/nsproxy.c [create_new_namespaces] read at v6.18.44; identical at v6.18.46.

    - SUCCESS.  [kernel_clone] returns [pid_vnr(pid)], the child's pid in
      the CALLER's pid namespace — with [CLONE_NEWPID] the child is pid 1
      in its own namespace, and the caller still sees an ordinary pid of
      its own namespace.  So the admitted pids are exactly
      [clone_resolve]'s: [clone_pid_ok_b], never 0.  And the caller now
      has a child, so the success branch applies [clone_child_made]: it
      records the child with [State.with_child] (the child bit and the
      pid), which [Kernel.Exit.wait4_spec]'s -ECHILD reads
      ([Checks.ProcessCreation.clone_ns_resolve_declines_or_sets_children]),
      and it turns each open eventfd into the shared kind
      ([share_eventfds]), for [clone_resolve]'s reason.
      No byte of the caller's memory moves: [CLONE_PARENT_SETTID] and
      [CLONE_PIDFD] are clear.  The caller's own credentials, namespaces
      and [fs_struct] are not touched: [copy_creds], [copy_namespaces]
      and [copy_fs] act on the new task [p].  Its descriptor table is
      not touched in Linux either, but the model's copy of it is: each
      live inherited descriptor becomes [OInherited None]
      ([forfeit_inherited], above), because the description it names was
      made before the clone and its offset now lives in the child's
      entry alone; and each open eventfd becomes the shared kind
      ([share_eventfds], above).
    - FAILURE: EVERY ERRNO FROM 1 TO 4095 BUT -EINTR ([Syscall.errno_any]).  The
      failures of this word run through everything a plain fork's do
      ([clone_errnos]) and then through [create_user_ns] (-ENOSPC past 32
      levels or past [max_user_namespaces], -EPERM in a chroot or for an
      unmapped creator, whatever [security_create_user_ns] answers),
      [copy_namespaces]'s [ns_capable(CAP_SYS_ADMIN)] (-EPERM), and each
      of [copy_mnt_ns], [copy_utsname], [copy_ipcs], [copy_pid_ns],
      [copy_cgroup_ns] and [copy_net_ns] — the last runs every
      registered pernet init function, each of which can return its own
      errno.  That set cannot be enumerated with confidence, so the arm
      admits every errno but -EINTR rather than a list a missing member
      of which would make the model reject a real kernel's answer.
      -EINTR is left out for the reason argued at [clone_errnos] above:
      [copy_process]'s own -EINTR (kernel/fork.c, [fatal_signal_pending])
      reaches userspace only after SIGKILL has ended the task; and the
      namespace inits' interruptible waits can answer -EINTR only with a
      signal pending, which SCOPE.md's "Nothing outside the process makes
      a signal pending for it" assumption excludes.  The cost is
      the usual one of a wide set: the model also admits errnos no
      kernel returns here.  [Run.injected_table] keeps [clone_errnos]
      for 220, so under a forced-only [Run.SpuriousCfg] the four
      resource errnos (-EAGAIN, -ENOMEM, -EMFILE, -EACCES) are filtered
      where a pid is admissible and every other errno stays admitted —
      -ENOSPC from [max_user_namespaces], a resource limit too, among
      them.  A statement that reads "forced-only" as "no resource
      failure" for the namespace word must exclude those itself.

    The [clone_no_shared_file_b] gate is the one [clone_resolve] has, for
    the same reason: a child given a copy of the descriptor table shares
    every [struct file] with the caller whatever namespaces it runs in.
    It is asked of the table the caller KEEPS ([forfeit_inherited]), as
    the fork word's is. *)
Definition clone_ns_resolve : Sys SyscallEffect :=
  m <- get_model ;;
  if negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))) then unmodeled
  else
    alt (e <- errno_any ;; err_ret e)
        (pid <- choose (fun p => clone_pid_ok_b m p = true) ;;
         modify (clone_child_made pid) ;;
         ret_only pid).

(* =========================================================================
   The decoded argument record and the argument-only -EINVAL checks
   ========================================================================= *)

(** THE DECODED ARGUMENT RECORD.  [clone] and [clone3] both fill one
    [struct kernel_clone_args] (kernel/fork.c, Linux v6.18.46), and the
    model keeps one record of the part of it a clone reads: the flags,
    the exit signal, the pidfd, child-tid and parent-tid pointers, the
    stack and the tls.  [clone] fills it from its registers
    ([clone_args_of_clone], below) and [clone3] from its struct
    ([clone3_pre], after [clone_args_field]).  The argument checks
    ([clone_arg_checks]) read the record, not the registers.

    The flags and the exit signal are two fields, as in Linux: legacy
    [clone] splits [lower_32_bits(clone_flags)] into [.flags] without
    [CSIGNAL] and [.exit_signal] with only [CSIGNAL] (fork.c:2742-2750),
    and [clone3] copies the two struct fields (fork.c:2802-2813).  No
    record of this model has a flag bit in the signal byte, but for
    [clone3] that takes more than the copy: Linux lets CLONE_NEWTIME
    (0x80), which lies inside the signal byte, through
    [clone3_args_valid] (fork.c:2864-2865), and [clone3_pre] refuses
    every other signal-byte flag and declines that one
    ([clone3_pre_split]). *)
Record CloneArgs := mkCloneArgs {
  cla_flags : Z;
  cla_exit_signal : Z;
  cla_pidfd : word;
  cla_child_tid : word;
  cla_parent_tid : word;
  cla_stack : word;
  cla_tls : word
}.

(** What the core hands the namespace extension about a pending clone's
    arguments: the decoded record of the call, or nothing.  A record is
    not a promise that the core answers the call, nor that any rule
    reads the record — a [clone] (220) word the core declines still has
    one, and the admitted words are still gated on the raw register.
    [Procs.clone_in_of] says exactly which calls have one. *)
Inductive CloneIn := CiArgs (r : CloneArgs) | CiNoArgs.

(** [clone]'s registers under [CONFIG_CLONE_BACKWARDS], which
    arch/riscv/Kconfig selects: a0 the flag word, a1 the new stack, a2
    the parent-tid pointer and also the pidfd pointer, a3 the tls, a4 the
    child-tid pointer (fork.c:2720-2753).

    THE RAW-INPUT GUARD.  Linux reads only the low 32 bits of a0
    (fork.c:2743, 2747).  The record would hide the high 32, so a word
    with any of them set has no record, and the call declines: the
    whole-register strictness [clone_fork_flags_b] and
    [clone_ns_flags_b] already have. *)
Definition clone_args_of_clone (a0 a1 a2 a3 a4 : word) : option CloneArgs :=
  if (bv_unsigned a0 <? 2 ^ 32)%Z
  then Some (mkCloneArgs
               (Z.land (bv_unsigned a0) (Z.land CLONE_LEGACY_FLAGS (Z.lnot CSIGNAL)))
               (Z.land (bv_unsigned a0) CSIGNAL)
               a2 a4 a2 a1 a3)
  else None.

(** A flag word holds a bit of [b]. *)
Definition clone_has (f b : Z) : bool := negb (Z.land f b =? 0)%Z.

(** THE ARGUMENT-ONLY -EINVAL CHECKS of [kernel_clone] and
    [copy_process] (kernel/fork.c, Linux v6.18.46), in kernel order.
    Each answers -EINVAL before any other step of [kernel_clone] and
    [copy_process] and changes no state, so the answer is -EINVAL when any of them fires, whichever
    fires first:
    - K0 ([kernel_clone], 2588-2591): CLONE_PIDFD and CLONE_PARENT_SETTID
      with the pidfd pointer equal to the parent-tid pointer.  Legacy
      [clone] passes a2 as both (2744, 2746), so there the two bits
      together always fire;
    - C1 (1951-1952): CLONE_NEWNS with CLONE_FS;
    - C2 (1954-1955): CLONE_NEWUSER with CLONE_FS;
    - C3 (1961-1962): CLONE_THREAD without CLONE_SIGHAND;
    - C4 (1969-1970): CLONE_SIGHAND without CLONE_VM;
    - C6a (1986-1987): CLONE_THREAD with CLONE_NEWUSER or CLONE_NEWPID;
    - C7 (1992-1999): CLONE_PIDFD with CLONE_DETACHED.
    Two rows of the same block read state rather than the record and are
    not here.  C5 (1978-1980) refuses CLONE_PARENT from a group with
    SIGNAL_UNKILLABLE; every word with CLONE_PARENT that no row here
    refuses declines, so C5 never has to be decided.  C6b (1986-1989)
    refuses CLONE_THREAD while the active pid namespace is not
    [pid_ns_for_children], which only the namespace extension holds.

    ONE definition, which the namespace extension reads too
    ([Ns.Clone.clone_ns_exact], over the record [Procs.clone_in_of]
    gives), so that the core and the extension cannot disagree on which
    records these rows refuse. *)
Definition clone_arg_checks (r : CloneArgs) : bool :=
  let f := cla_flags r in
  (clone_has f CLONE_PIDFD && clone_has f CLONE_PARENT_SETTID
     && bv_eqb (cla_pidfd r) (cla_parent_tid r))
  || (clone_has f CLONE_NEWNS && clone_has f CLONE_FS)
  || (clone_has f CLONE_NEWUSER && clone_has f CLONE_FS)
  || (clone_has f CLONE_THREAD && negb (clone_has f CLONE_SIGHAND))
  || (clone_has f CLONE_SIGHAND && negb (clone_has f CLONE_VM))
  || (clone_has f CLONE_THREAD
        && (clone_has f CLONE_NEWUSER || clone_has f CLONE_NEWPID))
  || (clone_has f CLONE_PIDFD && clone_has f CLONE_DETACHED).

(** Every row reads one of four bits: a record whose flags hold none of
    them passes every check. *)
Definition clone_check_bits : Z :=
  Z.lor CLONE_FS (Z.lor CLONE_SIGHAND (Z.lor CLONE_THREAD CLONE_PIDFD)).

Lemma clone_arg_checks_bits : forall r,
  clone_arg_checks r = true -> Z.land (cla_flags r) clone_check_bits <> 0%Z.
Proof.
  intros r H Hz.
  assert (Hb : forall b, Z.land b clone_check_bits = b ->
             clone_has (cla_flags r) b = false).
  { intros b Hbm. unfold clone_has.
    rewrite <- Hbm, (Z.land_comm b), Z.land_assoc, Hz, Z.land_0_l.
    reflexivity. }
  unfold clone_arg_checks in H. cbv zeta in H.
  rewrite (Hb CLONE_FS), (Hb CLONE_SIGHAND), (Hb CLONE_THREAD), (Hb CLONE_PIDFD)
    in H by (vm_compute; reflexivity).
  rewrite ?andb_false_r in H. cbn in H. discriminate H.
Qed.

(** Every word the namespace gate admits is [SIGCHLD] plus bits of
    [clone_ns_mask], so it shares no bit with any [b] that is disjoint
    from both ([Checks.Sys.Kernel.Fork.clone_ns_flags_disjoint] states
    the same for the checker's readers). *)
Local Lemma clone_ns_word_disjoint : forall flags b,
  clone_ns_flags_b flags = true ->
  Z.land clone_ns_mask b = 0%Z -> Z.land SIGCHLD b = 0%Z ->
  Z.land (bv_unsigned flags) b = 0%Z.
Proof.
  intros flags b H Hm Hs. unfold clone_ns_flags_b in H.
  apply andb_true_iff in H as [H _]. apply Z.eqb_eq in H.
  rewrite <- (Z.land_m1_r (bv_unsigned flags)),
    <- (Z.lor_lnot_diag clone_ns_mask), Z.land_lor_distr_r, H,
    Z.land_lor_distr_l, <- Z.land_assoc, Hm, Hs, Z.land_0_r.
  reflexivity.
Qed.

(** NO CHECK REFUSES AN ADMITTED WORD: the fork word and every namespace
    word hold none of [clone_check_bits].  So [clone_spec] may ask the
    two admitted-word tests before the checks, where Linux runs the
    checks first, and give the same answer. *)
Lemma clone_admitted_no_arg_check : forall flags a1 a2 a3 a4 r,
  clone_fork_flags_b flags = true \/ clone_ns_flags_b flags = true ->
  clone_args_of_clone flags a1 a2 a3 a4 = Some r ->
  clone_arg_checks r = false.
Proof.
  intros flags a1 a2 a3 a4 r Hw Hr.
  destruct (clone_arg_checks r) eqn:Hc; [|reflexivity]. exfalso.
  apply clone_arg_checks_bits in Hc. apply Hc.
  unfold clone_args_of_clone in Hr.
  destruct (bv_unsigned flags <? 2 ^ 32)%Z; [|discriminate Hr].
  injection Hr as <-. cbn [cla_flags].
  rewrite <- Z.land_assoc.
  destruct Hw as [Hw|Hw].
  - unfold clone_fork_flags_b in Hw. apply bv_eqb_eq in Hw. subst flags.
    vm_compute. reflexivity.
  - apply (clone_ns_word_disjoint flags); [exact Hw| |]; vm_compute; reflexivity.
Qed.

(** AND EVERY ADMITTED WORD HAS ONE: both admitted words lie in the low
    32 bits, so the raw-input guard of [clone_args_of_clone] passes and
    the word has a record, which no check refuses.  This is what makes a
    [clone] (220) that creates a child a call with a record
    ([clone_spec_success_record], [Procs.clone_success_has_record]). *)
Lemma clone_admitted_word_record : forall flags a1 a2 a3 a4,
  clone_fork_flags_b flags = true \/ clone_ns_flags_b flags = true ->
  exists r, clone_args_of_clone flags a1 a2 a3 a4 = Some r
            /\ clone_arg_checks r = false.
Proof.
  intros flags a1 a2 a3 a4 Hw.
  assert (Hlt : (bv_unsigned flags <? 2 ^ 32)%Z = true).
  { destruct Hw as [Hw|Hw].
    - unfold clone_fork_flags_b in Hw. apply bv_eqb_eq in Hw. subst flags.
      vm_compute. reflexivity.
    - assert (Hd : Z.land (bv_unsigned flags) (Z.lnot (Z.ones 32)) = 0%Z)
        by (apply (clone_ns_word_disjoint flags);
            [exact Hw | vm_compute; reflexivity | vm_compute; reflexivity]).
      assert (H32 : (0 < 2 ^ 32)%Z) by reflexivity.
      apply Z.ltb_lt.
      rewrite <- (Z.land_m1_r (bv_unsigned flags)), <- (Z.lor_lnot_diag (Z.ones 32)),
        Z.land_lor_distr_r, Hd, Z.lor_0_r, Z.land_ones by lia.
      destruct (Z.mod_pos_bound (bv_unsigned flags) (2 ^ 32) H32) as [_ Hm]. exact Hm. }
  assert (Hr : clone_args_of_clone flags a1 a2 a3 a4
               = Some (mkCloneArgs
                         (Z.land (bv_unsigned flags)
                            (Z.land CLONE_LEGACY_FLAGS (Z.lnot CSIGNAL)))
                         (Z.land (bv_unsigned flags) CSIGNAL) a2 a4 a2 a1 a3))
    by (unfold clone_args_of_clone; rewrite Hlt; reflexivity).
  eexists. split; [exact Hr|].
  exact (clone_admitted_no_arg_check flags a1 a2 a3 a4 _ Hw Hr).
Qed.

(** [clone]'s checks are a function of a0 alone: the two pointers K0
    compares are both a2, so K0 reduces to its two bits, and no other row
    reads a pointer.  The namespace model asks this
    ([Ns.Clone.clone_ns_exact_core_gate_word]); [clone_legacy_einval_b_spec]
    states that it is the record's answer whatever a1 to a4 hold. *)
Definition clone_legacy_einval_b (a0 : word) : bool :=
  match clone_args_of_clone a0 a0 a0 a0 a0 with
  | Some r => clone_arg_checks r
  | None => false
  end.

Lemma clone_legacy_einval_b_spec : forall a0 a1 a2 a3 a4,
  clone_legacy_einval_b a0 =
  match clone_args_of_clone a0 a1 a2 a3 a4 with
  | Some r => clone_arg_checks r
  | None => false
  end.
Proof.
  intros. unfold clone_legacy_einval_b, clone_args_of_clone.
  destruct (bv_unsigned a0 <? 2 ^ 32)%Z; [|reflexivity].
  unfold clone_arg_checks. cbn [cla_flags cla_pidfd cla_parent_tid].
  unfold bv_eqb. rewrite !Z.eqb_refl. reflexivity.
Qed.

(** [clone]'s -EINVAL for a word the argument checks refuse.

    A DELIBERATE NARROWING AGAINST LINUX.  Linux answers -EINVAL here
    whatever the caller's descriptor table holds: the checks come before
    [copy_files] (kernel/fork.c:1944-1999).  This arm answers it only
    when [clone_no_shared_file_b] passes the table the caller keeps, the
    gate both admitted words have, and declines otherwise.  The reason is
    a published statement: [Checks.ProcessCreation.clone_open_file_unmodeled]
    says that a [clone] made with such a descriptor open declines, for
    EVERY flag word.  A decline is never a wrong answer.  Lifting the
    gate means restating that lemma.  [clone3] has no such statement, and
    [clone3_einval] answers -EINVAL whatever the table holds, as Linux
    does. *)
Definition clone_einval : Sys SyscallEffect :=
  m <- get_model ;;
  if clone_no_shared_file_b (forfeit_inherited (m_fds m)) then err_ret EINVAL
  else unmodeled.

(* =========================================================================
   CLONE_SYSVSEM and the four tid bits, without CLONE_VM
   ========================================================================= *)

(** The four bits that make a clone store a thread id or seat a tls,
    and with [CLONE_SYSVSEM] the bits the admitted words may add to the
    fork word and to the namespace word (include/uapi/linux/sched.h,
    Linux v6.18.46).  What Linux does with each, without [CLONE_VM]:
    - [CLONE_SYSVSEM]: [copy_semundo] (ipc/sem.c:2306-2321) shares the
      caller's SysV undo list, allocating one first when the caller has
      none: -ENOMEM (1855-1858), which [clone_errnos] already holds.  No
      answer of this model reads an undo list: it has no SysV semaphore
      call, and [exit_sem] has nothing to undo.  With [CLONE_NEWIPC]
      [copy_namespaces] refuses the word (kernel/nsproxy.c:161-162, 171-173),
      so that pair gets no child ([clone_ns_refused]).
    - [CLONE_PARENT_SETTID]: [kernel_clone] stores the return value at
      the parent-tid pointer in the caller's memory (fork.c:2626-2627)
      and ignores the result: [tid_store_case].
    - [CLONE_CHILD_SETTID]: the child stores its own pid at the child-tid
      pointer at its first run (kernel/sched/core.c:5272-5273), into its
      own copy of the memory, before its first instruction; the
      multi-process core makes that store when it creates the child
      ([Procs.child_tid_store]), and the released step admits the word
      only where that store is Linux's ([child_tid_ok]).
    - [CLONE_CHILD_CLEARTID]: the child's exit or exec stores 0 there
      only while another holder pins its mm ([mm_users > 1],
      fork.c:1436-1446).  Without [CLONE_VM] nothing modeled does, so
      nothing is stored, and no other task reads that memory: no
      observable effect.
    - [CLONE_SETTLS]: [copy_thread] seats the tls in the child's tp
      (arch/riscv/kernel/process.c:253-254): [Procs.child_ms]. *)
Definition clone_tid_bits : Z :=
  Z.lor CLONE_PARENT_SETTID
    (Z.lor CLONE_CHILD_SETTID (Z.lor CLONE_CHILD_CLEARTID CLONE_SETTLS)).

Definition clone_extra_bits : Z := Z.lor CLONE_SYSVSEM clone_tid_bits.

(** The two words the gates admitted before these bits hold none of them,
    so their records make no store and seat no tls
    ([Procs.clone_no_extra_bits_unchanged]). *)
Lemma clone_admitted_no_extra_bits : forall flags a1 a2 a3 a4 r,
  clone_fork_flags_b flags = true \/ clone_ns_flags_b flags = true ->
  clone_args_of_clone flags a1 a2 a3 a4 = Some r ->
  Z.land (cla_flags r) clone_extra_bits = 0%Z.
Proof.
  intros flags a1 a2 a3 a4 r Hw Hr.
  unfold clone_args_of_clone in Hr.
  destruct (bv_unsigned flags <? 2 ^ 32)%Z; [|discriminate Hr].
  injection Hr as <-. cbn [cla_flags].
  rewrite <- Z.land_assoc.
  destruct Hw as [Hw|Hw].
  - unfold clone_fork_flags_b in Hw. apply bv_eqb_eq in Hw. subst flags.
    vm_compute. reflexivity.
  - apply (clone_ns_word_disjoint flags); [exact Hw| |]; vm_compute; reflexivity.
Qed.

(** What the core answers for a decoded record the argument checks pass:
    - [CcFork]: the fork word with bits of [clone_extra_bits];
    - [CcNs]: the namespace word with bits of [clone_extra_bits], but not
      [CLONE_NEWIPC] with [CLONE_SYSVSEM];
    - [CcNsRefused]: [CLONE_NEWIPC] with [CLONE_SYSVSEM], which
      [copy_namespaces] refuses, -EPERM or -EINVAL by the caller's
      capability (kernel/nsproxy.c:161-162, 171-173), after every
      failure of the steps before it;
    - [CcNone]: any other record, which declines.
    The exit signal is [SIGCHLD], as the two admitted words have it: no
    other exit signal is modeled. *)
Inductive CloneClass := CcFork | CcNs | CcNsRefused | CcNone.

Definition clone_class (r : CloneArgs) : CloneClass :=
  let f := cla_flags r in
  if negb (cla_exit_signal r =? SIGCHLD)%Z then CcNone
  else if clone_has f (Z.lnot (Z.lor clone_extra_bits clone_ns_mask)) then CcNone
  else if negb (clone_has f clone_ns_mask) then CcFork
  else if clone_has f CLONE_NEWIPC && clone_has f CLONE_SYSVSEM then CcNsRefused
  else CcNs.

(** The class [clone3_spec] answers with a child besides the fork image
    ([clone3_with_stores]); a record of it has no namespace bit. *)
Definition clone_class_fork_b (r : CloneArgs) : bool :=
  match clone_class r with CcFork => true | _ => false end.

Lemma clone_class_fork_b_ns : forall r,
  clone_class_fork_b r = true -> clone_has (cla_flags r) clone_ns_mask = false.
Proof.
  intros r H. unfold clone_class_fork_b, clone_class in H. cbv zeta in H. revert H.
  destruct (clone_has (cla_flags r) clone_ns_mask) eqn:Hm; [|intros _; reflexivity].
  destruct (negb (cla_exit_signal r =? SIGCHLD)%Z); [intros Hx; discriminate Hx|].
  destruct (clone_has (cla_flags r) (Z.lnot (Z.lor clone_extra_bits clone_ns_mask)));
    [intros Hx; discriminate Hx|].
  destruct (clone_has (cla_flags r) CLONE_NEWIPC && clone_has (cla_flags r) CLONE_SYSVSEM);
    intros Hx; discriminate Hx.
Qed.

(** THE CASES OF A 4-BYTE [put_user] OF A THREAD ID at [p], over the
    writable view [w] ([State.in_wmem]), for the [CLONE_PARENT_SETTID]
    store and the child's [CLONE_CHILD_SETTID] store (fork.c:2626-2627;
    kernel/sched/core.c:5272-5273; both ignore the result):
    - [access_ok] refuses the range: nothing is written
      (arch/riscv/include/asm/uaccess.h:408-414);
    - the memory backs all four bytes writably: all four are written;
    - it backs none of them writably (unmapped, or mapped read-only):
      nothing is written, since an aligned store faults whole and the byte
      copy of a misaligned one faults at its first byte
      (arch/riscv/lib/uaccess.S:193-207);
    - it backs some of them writably: the byte copy of a misaligned
      pointer can write a prefix (uaccess.h:322-326, uaccess.S:203-207),
      which this model does not state, so the call declines.
    [TsSkip] is the two cases that write nothing. *)
Inductive TidStore := TsSkip | TsWrite | TsPartial.

(** The four bytes of a 4-byte slot at [p] in a view of the memory. *)
Definition tid_bytes (v : word -> option byte) (p : word) : list (option byte) :=
  map (fun k => v (p + Z_to_bv 64 k)) [0; 1; 2; 3]%Z.

Definition all_backed (bs : list (option byte)) : bool :=
  forallb (fun b => match b with Some _ => true | None => false end) bs.

Definition none_backed (bs : list (option byte)) : bool :=
  forallb (fun b => match b with Some _ => false | None => true end) bs.

Definition tid_store_case (w : word -> option byte) (p : word) : TidStore :=
  if negb (access_okb p 4) then TsSkip
  else if all_backed (tid_bytes w p) then TsWrite
  else if none_backed (tid_bytes w p) then TsSkip
  else TsPartial.

(** The record's two store pointers, when its flags ask for the store. *)
Definition clone_parent_tid (r : CloneArgs) : option word :=
  if clone_has (cla_flags r) CLONE_PARENT_SETTID then Some (cla_parent_tid r) else None.

Definition clone_child_tid (r : CloneArgs) : option word :=
  if clone_has (cla_flags r) CLONE_CHILD_SETTID then Some (cla_child_tid r) else None.

(** The bytes a store of [v] at [pt] writes: [v]'s low four bytes,
    little-endian, when the memory backs them all writably. *)
Definition tid_writes (w : word -> option byte) (pt : option word) (v : word)
    : list (word * list byte) :=
  match pt with
  | Some p => match tid_store_case w p with
              | TsWrite => [(p, le32_bytes v)]
              | _ => []
              end
  | None => []
  end.

Definition tid_store_partial (w : word -> option byte) (pt : option word) : bool :=
  match pt with
  | Some p => match tid_store_case w p with TsPartial => true | _ => false end
  | None => false
  end.

(** THE CHILD'S [CLONE_CHILD_SETTID] STORE IS ONE THE CORE MAKES AS LINUX
    DOES.  The child's memory is a copy of the caller's as it was when
    the call began ([copy_mm], fork.c:1547-1549, before every store into
    the caller's memory), so the caller's views of its memory are the
    child's, and the caller's model [m] holds the accounting the child's
    copy starts from.  The core makes the store from the caller's memory
    alone ([Procs.child_tid_store]): it writes when [access_ok] admits
    the slot and the memory backs all four bytes readably.  So the word
    declines where that rule and Linux's cases ([tid_store_case] over the
    writable view [in_wmem i]) could part, or where the store is not one
    the model states:
    - it also holds [CLONE_NEWPID]: the child's pid in its own pid
      namespace is 1 there, a value only the namespace extension knows;
    - the slot is backed writably in part ([TsPartial]);
    - the slot is backed writably and not readably, or backed readably
      and not writably (a read-only mapping): the two views disagree;
    - the store needs a page the model cannot account in the child's copy
      ([State.materialize_model_accesses], the test the released step
      makes of every store it makes). *)
Definition child_tid_ok (i : SyscallInput) (m : Model) (r : CloneArgs) : bool :=
  match clone_child_tid r with
  | None => true
  | Some p =>
      negb (clone_has (cla_flags r) CLONE_NEWPID)
      && (negb (access_okb p 4)
          || match tid_store_case (in_wmem i) p with
             | TsWrite =>
                 all_backed (tid_bytes (in_mem i) p)
                 && match materialize_model_accesses m [(p, 4%nat)] with
                    | Some _ => true
                    | None => false
                    end
             | TsSkip => none_backed (tid_bytes (in_mem i) p)
             | TsPartial => false
             end)
  end.

(** Both stores of a record are ones the model states. *)
Definition clone_stores_ok (i : SyscallInput) (m : Model) (r : CloneArgs) : bool :=
  negb (tid_store_partial (in_wmem i) (clone_parent_tid r)) && child_tid_ok i m r.

(** A successful answer, with the [CLONE_PARENT_SETTID] store of the pid
    it returns; a failure stores nothing (fork.c:2611-2615 return before
    2626). *)
Definition tid_store_effect (w : word -> option byte) (pt : option word)
    (eff : SyscallEffect) : SyscallEffect :=
  if addr_is_error_b (eff_ret eff) then eff
  else mkEffectU (eff_ret eff) (eff_writes eff ++ tid_writes w pt (eff_ret eff))
         (eff_zeros eff) (eff_unmaps eff) (eff_copies eff) (eff_copyins eff).

(** A word with bits of [clone_extra_bits]: the resolution [body] of the
    word without them, and the caller's [CLONE_PARENT_SETTID] store of the
    pid it returns, when the stores of the record are ones the model
    states ([clone_stores_ok]); a decline otherwise.  The PARENT MEMORY
    WRITTEN BY THE CALL ITSELF is in the effect, so the single-process
    step and the multi-process core give the caller the same memory; the
    core rewrites the four bytes when the namespace extension gives the
    call a return value of its own ([Procs.clone_parent_rewrite]). *)
Definition clone_with_stores (r : CloneArgs) (body : Sys SyscallEffect)
    : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if clone_stores_ok i m r
  then eff <- body ;; pure (tid_store_effect (in_wmem i) (clone_parent_tid r) eff)
  else unmodeled.

(** [CLONE_NEWIPC] with [CLONE_SYSVSEM] gets no child: [copy_namespaces]
    refuses it (kernel/nsproxy.c:161-162, 171-173) after every step
    before it, so every errno the namespace word admits and no pid.
    Which of -EPERM and -EINVAL is the namespace tables' to decide. *)
Definition clone_ns_refused : Sys SyscallEffect :=
  m <- get_model ;;
  if negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))) then unmodeled
  else e <- errno_any ;; err_ret e.

(** A body followed by a pure map of its effect. *)
Lemma bind_pure_map_iff : forall (body : Sys SyscallEffect)
    (f : SyscallEffect -> SyscallEffect) i m o,
  (eff <- body ;; pure (f eff)) i m o <->
  match o with
  | Ok y m' evs => exists e0, body i m (Ok e0 m' evs) /\ y = f e0
  | Unmodeled => body i m Unmodeled
  end.
Proof.
  intros body f i m o. unfold bind, pure. destruct o as [y m2 evs|]; cbv beta iota; split.
  - intros (x & m1 & evs1 & evs2 & Hb & Hp & He).
    injection Hp as Hy Hm Hev. subst. exists x. rewrite app_nil_r.
    split; [exact Hb | reflexivity].
  - intros (e0 & Hb & ->). exists e0, m2, evs, []. split; [exact Hb|].
    split; [reflexivity | rewrite app_nil_r; reflexivity].
  - intros [H | (x & m1 & evs1 & Hb & Hp)]; [exact H | discriminate Hp].
  - intros H. left. exact H.
Qed.

(** [clone_with_stores], outcome by outcome. *)
Lemma clone_with_stores_iff : forall r body i m o,
  clone_with_stores r body i m o <->
  (clone_stores_ok i m r = true /\
     match o with
     | Ok eff m' evs => exists e0, body i m (Ok e0 m' evs)
                          /\ eff = tid_store_effect (in_wmem i) (clone_parent_tid r) e0
     | Unmodeled => body i m Unmodeled
     end)
  \/ (clone_stores_ok i m r = false /\ o = Unmodeled).
Proof.
  intros r body i m o. unfold clone_with_stores.
  rewrite bind_input_iff. cbv beta. rewrite bind_get_model. cbv beta.
  destruct (clone_stores_ok i m r) eqn:Hok; cbv iota.
  - rewrite bind_pure_map_iff. split.
    + intros H. left. split; [reflexivity | exact H].
    + intros [[_ H] | [Hf _]]; [exact H | discriminate Hf].
  - unfold unmodeled. split.
    + intros H. right. split; [reflexivity | exact H].
    + intros [[Ht _] | [_ H]]; [discriminate Ht | exact H].
Qed.

(* =========================================================================
   The host's clone refusers
   ========================================================================= *)

(** WHAT A REFUSER ANSWERS: any errno from 1 to 4095, -EINTR included,
    with the caller's model unchanged.  A BPF LSM program on [task_alloc]
    and a sched_ext scheduler's task init may return any value in
    [-MAX_ERRNO, -1] ([State.cr_bpf_task_alloc], [State.cr_sched_ext]);
    [perf_event_init_task] returns its own -EINVAL or what a PMU's
    [event_init] returns ([State.cr_perf_inherit]).  An -EINTR a refuser
    returns reaches the program as it is: the restart and the SIGKILL
    arguments at [clone_errnos] are about [copy_process]'s own -EINTR,
    which needs a fatal signal pending.  The failure created nothing, so
    the model is the caller's at each of the three refusers' steps
    ([State.CloneRefusers]).  The shared namespace state is the namespace
    side's: [Ns.Clone.clone_ns] admits, for every errno, both the state as
    it was (a refusal before [alloc_pid]) and [Ns.Clone.pid_advanced] (one
    after it), an over-approximation that covers either step. *)
Definition clone_refused_fail : Sys SyscallEffect :=
  e <- choose (fun e => (1 <= e <= 4095)%Z) ;; err_ret e.

(** THE REFUSERS AT EACH ANSWERED WORD.  [answered] says whether the call
    reaches [copy_process] in a word class the model answers: for such a
    call, with a refuser present in the model ([State.m_clone_refusers]),
    the call admits [fail] beside [k], its answer from the model's lists.
    Everywhere else the answer is [k] alone: at the default, for a word
    the model declines, and where the descriptor gate declines
    ([clone_no_shared_file_b] over the table the caller keeps), because a
    decline admits no answer at all. *)
Definition clone_refusable (answered : SyscallInput -> bool)
    (fail k : Sys SyscallEffect) : Sys SyscallEffect :=
  fun i m o =>
    if answered i && clone_refused_b (m_clone_refusers m)
       && clone_no_shared_file_b (forfeit_inherited (m_fds m))
    then alt fail k i m o
    else k i m o.

(** THE REFUSERS INSIDE AN ARM.  The arms [clone_class] admits beyond
    the two words, and [clone3]'s records beyond the fork image, reach
    [copy_process] too, so with a refuser present each admits the
    refusal's errnos as well.  [clone_spec]'s and [clone3_spec]'s tests
    cannot count them as answered: those tests read the input alone, and
    these arms can still decline on the model ([child_tid_ok] reads its
    accounting), while a call the wrapper both refuses and declines would
    have no checker.  So the refusal sits inside the arm, under its stores
    gate: [clone_with_stores] declines first, and a refusal's
    error-encoded effect gets no store ([tid_store_effect]), as Linux
    makes the [CLONE_PARENT_SETTID] store only after [copy_process]
    succeeded (fork.c:2611-2615, 2626-2627). *)
Definition clone_refusable_arm (body : Sys SyscallEffect) : Sys SyscallEffect :=
  clone_refusable (fun _ => true) clone_refused_fail body.

(** The fork word goes to [clone_resolve] and the namespace word to
    [clone_ns_resolve].  Every other word is decoded into its argument
    record ([clone_args_of_clone]): -EINVAL when the argument checks
    refuse the record ([clone_arg_checks], through [clone_einval]); the
    fork or namespace resolution with the stores of [clone_extra_bits]
    when [clone_class] admits it; and a decline otherwise, a word without
    a record included.

    Linux runs the checks before every other step; here they come after
    the two admitted-word tests, which changes no answer
    ([clone_admitted_no_arg_check]).

    This is the answer from the model's own lists, the whole answer of a
    run whose host has no clone refuser ([State.no_clone_refusers]);
    [clone_spec] below adds the refusers' errnos to it for the two words
    ([clone_spec_default_iff]), and each arm of a decoded record adds them
    itself ([clone_refusable_arm]). *)
Definition clone_spec_lists (flags : word) : Sys SyscallEffect :=
  if clone_fork_flags_b flags then clone_resolve
  else if clone_ns_flags_b flags then clone_ns_resolve
  else
    i <- input ;;
    match clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) with
    | Some r =>
        if clone_arg_checks r then clone_einval
        else match clone_class r with
             | CcFork => clone_with_stores r (clone_refusable_arm clone_resolve)
             | CcNs => clone_with_stores r (clone_refusable_arm clone_ns_resolve)
             | CcNsRefused => clone_refusable_arm clone_ns_refused
             | CcNone => unmodeled
             end
    | None => unmodeled
    end.

(** [clone]: the answer from the lists, and with a refuser present every
    errno from 1 to 4095 for both words the lists answer. *)
Definition clone_spec (flags : word) : Sys SyscallEffect :=
  clone_refusable (fun _ => clone_fork_flags_b flags || clone_ns_flags_b flags)
    clone_refused_fail (clone_spec_lists flags).

(** With no refuser present the wrapper is its argument. *)
Lemma clone_refusable_absent : forall answered fail k i m o,
  clone_refused_b (m_clone_refusers m) = false ->
  (clone_refusable answered fail k i m o <-> k i m o).
Proof.
  intros answered fail k i m o H. unfold clone_refusable.
  rewrite H, Bool.andb_false_r. cbn [andb].
  split; intro X; exact X.
Qed.

(** At a call the wrapper does not count as answered — the default arm,
    and every word the lists answer with -EINVAL or a decline — the
    wrapper is its argument whatever the host holds. *)
Lemma clone_refusable_unanswered : forall answered fail k i m o,
  answered i = false ->
  (clone_refusable answered fail k i m o <-> k i m o).
Proof.
  intros answered fail k i m o H. unfold clone_refusable.
  rewrite H. cbn [andb].
  split; intro X; exact X.
Qed.

(** Every outcome of the wrapper is the refusal's or the lists'. *)
Lemma clone_refusable_cases : forall answered fail k i m o,
  clone_refusable answered fail k i m o -> fail i m o \/ k i m o.
Proof.
  intros answered fail k i m o H. unfold clone_refusable in H.
  destruct (answered i && clone_refused_b (m_clone_refusers m)
            && clone_no_shared_file_b (forfeit_inherited (m_fds m))).
  - exact H.
  - right. exact H.
Qed.

(** Every outcome of the lists stays admitted. *)
Lemma clone_refusable_lists : forall answered fail k i m o,
  k i m o -> clone_refusable answered fail k i m o.
Proof.
  intros answered fail k i m o H. unfold clone_refusable.
  destruct (answered i && clone_refused_b (m_clone_refusers m)
            && clone_no_shared_file_b (forfeit_inherited (m_fds m))).
  - apply alt_r. exact H.
  - exact H.
Qed.

(** And the refusal is admitted at an answered call with a refuser
    present and the gate open. *)
Lemma clone_refusable_refused : forall answered fail k i m o,
  answered i = true ->
  clone_refused_b (m_clone_refusers m) = true ->
  clone_no_shared_file_b (forfeit_inherited (m_fds m)) = true ->
  fail i m o -> clone_refusable answered fail k i m o.
Proof.
  intros answered fail k i m o Ha Hr Hg Hf. unfold clone_refusable.
  rewrite Ha, Hr, Hg. change (alt fail k i m o). apply alt_l. exact Hf.
Qed.

(** A refusal returns an errno from 1 to 4095 and leaves the model and
    the events alone. *)
Lemma clone_refused_fail_inv : forall i m o,
  clone_refused_fail i m o ->
  exists e, (1 <= e <= 4095)%Z /\ o = Ok (mkEffect (errno_ret e) [] []) m [].
Proof.
  intros i m o H. unfold clone_refused_fail, bind in H.
  destruct o as [eff m' evs|]; cbv beta iota in H.
  - destruct H as (e & m1 & evs1 & evs2 & He & Hr & Hevs).
    unfold choose in He.
    destruct He as (e0 & Hrange & He0). injection He0 as -> -> ->.
    unfold err_ret, ret_only, pure in Hr. injection Hr as -> -> ->.
    exists e0. split; [exact Hrange|]. cbn in Hevs. subst evs. reflexivity.
  - destruct H as [H | (e & m1 & evs1 & He & Hr)].
    + unfold choose in H. destruct H as (x & _ & Hx). discriminate Hx.
    + unfold err_ret, ret_only, pure in Hr. discriminate Hr.
Qed.

Lemma clone_refused_fail_ok : forall e i m,
  (1 <= e <= 4095)%Z ->
  clone_refused_fail i m (Ok (mkEffect (errno_ret e) [] []) m []).
Proof.
  intros e i m He. unfold clone_refused_fail, bind. cbv beta iota.
  exists e, m, [], []. split; [apply choose_ok; exact He|].
  split; reflexivity.
Qed.

(** THE DEFAULT IS TODAY'S ANSWER.  In a model whose host has no clone
    refuser, [clone] admits exactly what the model's lists admit, the
    answer [clone_spec] gave before the refusers were named. *)
Theorem clone_spec_default_iff : forall flags i m o,
  m_clone_refusers m = no_clone_refusers ->
  (clone_spec flags i m o <-> clone_spec_lists flags i m o).
Proof.
  intros flags i m o H. unfold clone_spec. apply clone_refusable_absent.
  rewrite H. reflexivity.
Qed.

(** An errno in [1,4095] reads as an error-encoded return.
    [Checks.Sys.Prelude.errno_ret_error_b] is the same fact, stated where
    the checker layer can cite it; this file is below that layer, and the
    two lemmas below need it here. *)
Local Lemma errno_ret_is_error : forall e,
  (1 <= e <= 4095)%Z -> addr_is_error_b (errno_ret e) = true.
Proof.
  intros e He. unfold addr_is_error_b, errno_ret, two_pow_64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64%Z.
  replace (- e)%Z with (2 ^ 64 - e + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia.
  apply Z.ltb_lt. lia.
Qed.

(** A [clone] (220) THAT CREATES A CHILD HAS A RECORD THE CHECKS PASS.
    An answer that is not error-encoded ([State.addr_is_error_b], the
    test [Procs.clone_success_b] reads) comes from neither a host
    refuser nor the argument checks' -EINVAL, so it comes from one of the
    two admitted words, which have a record no check refuses
    ([clone_admitted_word_record]), or from an arm of a decoded record
    the checks pass ([clone_class]'s [CcFork] and [CcNs]).  This is the
    guard for a call with no record: the core resolves none successfully
    ([Procs.clone_success_has_record],
    [Ns.Clone.clone_ns_exact_core_gate]). *)
Lemma clone_spec_success_record : forall flags i m eff m' evs,
  clone_spec flags i m (Ok eff m' evs) ->
  addr_is_error_b (eff_ret eff) = false ->
  exists r, clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
              = Some r
            /\ clone_arg_checks r = false.
Proof.
  intros flags i m eff m' evs H Herr. unfold clone_spec in H.
  apply clone_refusable_cases in H as [H | H].
  { exfalso. apply clone_refused_fail_inv in H as (e & He & Heq).
    injection Heq as -> _ _. cbn [eff_ret] in Herr.
    rewrite (errno_ret_is_error e He) in Herr. discriminate Herr. }
  destruct (clone_fork_flags_b flags) eqn:Hf;
    [apply (clone_admitted_word_record flags _ _ _ _ (or_introl Hf))|].
  destruct (clone_ns_flags_b flags) eqn:Hns;
    [apply (clone_admitted_word_record flags _ _ _ _ (or_intror Hns))|].
  unfold clone_spec_lists in H. rewrite Hf, Hns in H. cbv iota in H.
  apply bind_input_iff in H. cbv beta in H.
  destruct (clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4))
    as [r|]; cbv iota in H; [|exfalso; unfold unmodeled in H; discriminate H].
  destruct (clone_arg_checks r) eqn:Hc; cbv iota in H;
    [|exists r; split; [reflexivity | exact Hc]].
  exfalso. unfold clone_einval in H. apply bind_get_model in H. cbv beta in H.
  destruct (clone_no_shared_file_b (forfeit_inherited (m_fds m)));
    cbv iota in H; [|unfold unmodeled in H; discriminate H].
  unfold err_ret, ret_only, pure in H. injection H as -> _ _.
  cbn [eff_ret] in Herr. vm_compute in Herr. discriminate Herr.
Qed.

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

    This model answers those size tests and that copy in the kernel's
    order ([clone3_copy], below), so every [size] reaches an answer or a
    decline that [clone3_copy]'s note names.  Who reaches the arm at
    all: NO
    LIBC EMITS A FORK-SHAPED CLONE3.  glibc's [fork] goes through
    [arch_fork] to a raw legacy [clone].  Its clone3 callers are three,
    none of them on a [fork] path.  [__clone_internal] is reached from
    [pthread_create], which passes
    [CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SYSVSEM | CLONE_SIGHAND |
    CLONE_THREAD | CLONE_SETTLS | CLONE_PARENT_SETTID |
    CLONE_CHILD_CLEARTID] — the opposite of the admitted image, and
    declined on the flags field when its size and stack range are valid
    (-EINVAL when [access_ok] refuses the stack
    range).  [posix_spawn] is the third, and
    it reaches [__clone3] DIRECTLY (sysdeps/unix/sysv/linux/spawni.c) —
    that one does pass this struct's size with
    [exit_signal = SIGCHLD], but with
    [CLONE_CLEAR_SIGHAND | CLONE_VM | CLONE_VFORK] in its BASE flag word
    — a spawn asking for a cgroup or a pidfd sets more — so it is
    declined on the flags field whichever it is when its stack range
    and its cgroup field are valid (-EINVAL when [access_ok] refuses
    the stack range, or when it asks for a cgroup above INT_MAX).
    riscv64 has the [clone3] wrapper, so it
    really executes here.  musl issues no clone3 at all.  So this arm, like the legacy one, is
    reached by a RAW syscall.

    The admitted image is the whole struct zero except [exit_signal], at
    offset 32, equal to [SIGCHLD] — which is [clone(SIGCHLD, 0)] told a
    different way, and reaches [kernel_clone] with the same arguments.

    THE STACK.  The image above requires [stack] and [stack_size] to be
    zero.  A struct with a stack, or with bits of [clone_extra_bits], is
    answered by [clone3_with_stores] instead when [clone_class] admits
    its record: [clone3_pre] has replaced the stack by [stack +
    stack_size] (fork.c:2845-2847), which the child's sp takes
    ([Procs.child_ms]); the caller's answer reads neither.  So a stack
    reaches the child's registers through either entry point.

    Every other flag bit is excluded here by the same allowlist.

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

(** [CLONE_ARGS_SIZE_VER0] (include/uapi/linux/sched.h): the smallest
    [size] [copy_clone_args_from_user] takes, the struct up to [tls]. *)
Definition CLONE_ARGS_SIZE_VER0 : Z := 64.

(** THE TAIL TEST, [check_zeroed_user] (lib/usercopy.c:45-81, Linux
    v6.18.46), over the bytes of the caller's struct past the kernel's
    88.  Linux reads the tail in aligned 8-byte words, in address order:
    the first word with the bytes below the tail masked off (59-61), the
    last with the bytes past it (73-74).  It stops at the first word it
    cannot read (-EFAULT, 79-81) or the first word with a non-zero tail
    byte (-E2BIG, and no later word is read: 63-65, 76-78).  So within one
    word the fault comes first: a word is read, or faults, as a whole.

    [clone3_tail_words] groups the tail bytes ([State.in_mem] at each
    address) by the aligned word that holds them: the first group runs to
    the first 8-byte boundary, each later one is a whole word, the last
    stops at the tail's end.  [clone3_tail_scan] walks the groups.  A
    group is unreadable when one of its bytes is: the model's memory is
    byte-addressed, and an aligned word never straddles a page, so on a
    memory whose readability is a property of the page (every memory a
    process has) a word Linux can read is exactly a group whose bytes are
    all readable.  The bytes of a word outside the tail are never
    consulted: they share the word's page, so they add no fault, and
    their values are masked off.
    - [TsZero]: every tail byte reads as 0.
    - [TsNonzero n]: a group with a non-zero byte, all earlier groups
      zero; [n] tail bytes are covered by the words read, that one
      included.
    - [TsFault n]: an unreadable group, all earlier groups zero; [n]
      tail bytes are covered by the words read before it. *)
Inductive Clone3TailScan := TsZero | TsNonzero (n : nat) | TsFault (n : nat).

(** The groups after the first: whole words, [fuel] bounding the walk (a
    group takes at least one byte, so the list's length is enough). *)
Fixpoint clone3_word_groups (fuel : nat) (l : list (option byte))
    : list (list (option byte)) :=
  match fuel with
  | O => []
  | S f => match l with
           | [] => []
           | _ => firstn 8 l :: clone3_word_groups f (skipn 8 l)
           end
  end.

Definition clone3_tail_words (mem : word -> option byte) (tail : word) (rest : nat)
    : list (list (option byte)) :=
  let tb := map (fun j => mem (Z_to_bv 64 (bv_unsigned tail + Z.of_nat j))) (seq 0 rest) in
  let c0 := (8 - Z.to_nat (bv_unsigned tail mod 8))%nat in
  firstn c0 tb :: clone3_word_groups rest (skipn c0 tb).

Fixpoint clone3_tail_scan (ws : list (list (option byte))) (acc : nat) : Clone3TailScan :=
  match ws with
  | [] => TsZero
  | w :: ws' =>
      if existsb (fun o => match o with None => true | Some _ => false end) w
      then TsFault acc
      else if existsb (fun o => match o with
                                | Some b => negb (bv_eqb b (Z_to_bv 8 0))
                                | None => false
                                end) w
      then TsNonzero (acc + length w)
      else clone3_tail_scan ws' (acc + length w)
  end.

(** The tail bytes the words read cover, as a ledger: none when no word
    was read. *)
Definition clone3_tail_reads (tail : word) (n : nat) : list (word * nat) :=
  match n with O => [] | _ => [(tail, n)] end.

(** WHAT THE COPY GIVES.  [C3Err reads en]: the call fails with [en]
    having read [reads].  [C3Decline]: the model declines.
    [C3Struct reads short bs]: the 88-byte struct [bs] the kernel's
    [struct clone_args] holds after the copy, having read [reads];
    [short] says the caller's [size] was below [CLONE_ARGS_SIZE], which
    one later test reads ([clone3_pre_sz]). *)
Inductive Clone3Copy :=
| C3Err (reads : list (word * nat)) (en : Z)
| C3Decline
| C3Struct (reads : list (word * nat)) (short : bool) (bs : list byte).

(** [copy_from_user] of the whole struct, the step the 88-byte call
    takes alone and a longer call takes after its tail test.  The range
    test comes before the walk ([State.copy_bytes_map]): a range
    [access_ok] refuses is -EFAULT having read nothing.

    A KNOWN GAP: a range [access_ok] admits that the memory does not
    wholly back declines, where Linux answers -EFAULT.  It is answerable
    on a memory mapped in whole pages, the premise the tail walk below
    uses: riscv64's scalar copy ([__asm_copy_from_user],
    arch/riscv/lib/uaccess.S) reads upward, so the readable prefix,
    [(uargs, k)], charges exactly the pages Linux touched.  The 88-byte
    call has always declined it, and answering it changes the 88-byte
    relation, which this model's size work left unchanged
    ([Checks.ProcessCreation.clone3_spec_88_unchanged]); so every size
    declines it alike, and answering it at every size is a separate
    change. *)
Definition clone3_copy_full (mem : word -> option byte) (uargs : word) : Clone3Copy :=
  match copy_bytes_map mem uargs CLONE_ARGS_SIZE with
  | Some bs => C3Struct [(uargs, CLONE_ARGS_SIZE_nat)] false bs
  | None =>
      if negb (access_okb uargs CLONE_ARGS_SIZE) then C3Err [] EFAULT
      else C3Decline
  end.

Definition clone3_tail (uargs : word) : word :=
  Z_to_bv 64 (bv_unsigned uargs + CLONE_ARGS_SIZE).

Definition clone3_rest (usize : Z) : nat := Z.to_nat (usize - CLONE_ARGS_SIZE).

(** [check_zeroed_user]'s range test, over the tail widened down to its
    word. *)
Definition clone3_tail_ok (uargs : word) (usize : Z) : bool :=
  let align := (bv_unsigned (clone3_tail uargs) mod 8)%Z in
  access_okb (Z_to_bv 64 (bv_unsigned (clone3_tail uargs) - align))
    (Z.of_nat (clone3_rest usize) + align).

(** [check_zeroed_user]'s word walk. *)
Definition clone3_tail_test (mem : word -> option byte) (uargs : word) (usize : Z)
    : Clone3TailScan :=
  clone3_tail_scan (clone3_tail_words mem (clone3_tail uargs) (clone3_rest usize)) 0.

(** THE SIZE TESTS AND THE COPY, in the kernel's order:
    [copy_clone_args_from_user] (kernel/fork.c:2772-2779, Linux
    v6.18.46) and [copy_struct_from_user]
    (include/linux/uaccess.h:400-411), on riscv64, where [PAGE_SIZE] is
    4096 ([State.page_size]).
    1. [usize > PAGE_SIZE]: -E2BIG; [usize < CLONE_ARGS_SIZE_VER0]:
       -EINVAL (2772-2775).  Nothing is read.
    2. [usize < CLONE_ARGS_SIZE]: the kernel's bytes past [usize] are
       zeroed (uaccess.h:400-401), then [copy_from_user] of [usize] bytes
       (408-409): a range [access_ok] refuses is -EFAULT having read
       nothing, one it admits that the memory does not wholly back
       declines, as for 88 ([clone3_copy_full]).  The struct is the
       caller's [usize] bytes and zeros.
    3. [usize = CLONE_ARGS_SIZE]: [clone3_copy_full].
    4. [usize > CLONE_ARGS_SIZE]: the tail test runs FIRST (402-405).
       [check_zeroed_user] widens the tail down to its word
       ([from -= align; size += align], usercopy.c:53-54) and asks
       [access_ok] of that range before it reads a word
       ([user_read_access_begin], 56-57, riscv64's
       [user_access_begin]): refused, -EFAULT having read nothing.
       Then the word walk ([clone3_tail_scan]): a non-zero tail byte is
       -E2BIG and an unreadable word -EFAULT, each having read the words
       before it (and, for -E2BIG, that word).  Only a tail of zeros
       reaches [copy_from_user] of the head, the 88 bytes, which is
       [clone3_copy_full] after the tail's reads.  The tail starts at
       [uargs + 88] taken modulo 2^64, as the kernel's pointer sum is;
       a [uargs] that close to the top fails the head's own
       [access_ok]. *)
Definition clone3_copy (mem : word -> option byte) (uargs : word) (usize : Z)
    : Clone3Copy :=
  if (page_size <? usize)%Z then C3Err [] E2BIG
  else if (usize <? CLONE_ARGS_SIZE_VER0)%Z then C3Err [] EINVAL
  else if (usize <? CLONE_ARGS_SIZE)%Z then
    match copy_bytes_map mem uargs usize with
    | Some bs =>
        C3Struct [(uargs, Z.to_nat usize)] true
          (bs ++ repeat (Z_to_bv 8 0) (Z.to_nat (CLONE_ARGS_SIZE - usize)))
    | None => if negb (access_okb uargs usize) then C3Err [] EFAULT else C3Decline
    end
  else if (CLONE_ARGS_SIZE <? usize)%Z then
    if negb (clone3_tail_ok uargs usize) then C3Err [] EFAULT
    else match clone3_tail_test mem uargs usize with
         | TsNonzero n => C3Err (clone3_tail_reads (clone3_tail uargs) n) E2BIG
         | TsFault n => C3Err (clone3_tail_reads (clone3_tail uargs) n) EFAULT
         | TsZero =>
             match clone3_copy_full mem uargs with
             | C3Struct reads short bs =>
                 C3Struct ((clone3_tail uargs, clone3_rest usize) :: reads) short bs
             | C3Err reads en => C3Err ((clone3_tail uargs, clone3_rest usize) :: reads) en
             | C3Decline => C3Decline
             end
         end
  else clone3_copy_full mem uargs.

(** At 88 the copy is [clone3_copy_full]: no size test fires and there
    is no tail. *)
Lemma clone3_copy_88 : forall mem uargs,
  clone3_copy mem uargs CLONE_ARGS_SIZE = clone3_copy_full mem uargs.
Proof. reflexivity. Qed.

Lemma clone3_size_88_unsigned :
  bv_unsigned (Z_to_bv 64 CLONE_ARGS_SIZE) = CLONE_ARGS_SIZE.
Proof. reflexivity. Qed.

(** [clone3_copy] in each size class. *)
Lemma clone3_copy_above_page : forall mem uargs usize,
  (page_size < usize)%Z -> clone3_copy mem uargs usize = C3Err [] E2BIG.
Proof.
  intros mem uargs usize H. unfold clone3_copy.
  replace (page_size <? usize)%Z with true by (symmetry; apply Z.ltb_lt; exact H).
  reflexivity.
Qed.

Lemma clone3_copy_below_ver0 : forall mem uargs usize,
  (usize < CLONE_ARGS_SIZE_VER0)%Z -> clone3_copy mem uargs usize = C3Err [] EINVAL.
Proof.
  intros mem uargs usize H. unfold clone3_copy.
  replace (page_size <? usize)%Z with false
    by (symmetry; apply Z.ltb_ge; unfold page_size, CLONE_ARGS_SIZE_VER0 in *; lia).
  replace (usize <? CLONE_ARGS_SIZE_VER0)%Z with true by (symmetry; apply Z.ltb_lt; exact H).
  reflexivity.
Qed.

Lemma clone3_copy_short : forall mem uargs usize,
  (CLONE_ARGS_SIZE_VER0 <= usize < CLONE_ARGS_SIZE)%Z ->
  clone3_copy mem uargs usize =
  match copy_bytes_map mem uargs usize with
  | Some bs =>
      C3Struct [(uargs, Z.to_nat usize)] true
        (bs ++ repeat (Z_to_bv 8 0) (Z.to_nat (CLONE_ARGS_SIZE - usize)))
  | None => if negb (access_okb uargs usize) then C3Err [] EFAULT else C3Decline
  end.
Proof.
  intros mem uargs usize H. unfold clone3_copy.
  replace (page_size <? usize)%Z with false
    by (symmetry; apply Z.ltb_ge; unfold page_size, CLONE_ARGS_SIZE in *; lia).
  replace (usize <? CLONE_ARGS_SIZE_VER0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  replace (usize <? CLONE_ARGS_SIZE)%Z with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma clone3_copy_long : forall mem uargs usize,
  (CLONE_ARGS_SIZE < usize <= page_size)%Z ->
  clone3_copy mem uargs usize =
  if negb (clone3_tail_ok uargs usize) then C3Err [] EFAULT
  else match clone3_tail_test mem uargs usize with
       | TsNonzero n => C3Err (clone3_tail_reads (clone3_tail uargs) n) E2BIG
       | TsFault n => C3Err (clone3_tail_reads (clone3_tail uargs) n) EFAULT
       | TsZero =>
           match clone3_copy_full mem uargs with
           | C3Struct reads short bs =>
               C3Struct ((clone3_tail uargs, clone3_rest usize) :: reads) short bs
           | C3Err reads en => C3Err ((clone3_tail uargs, clone3_rest usize) :: reads) en
           | C3Decline => C3Decline
           end
       end.
Proof.
  intros mem uargs usize H. unfold clone3_copy.
  replace (page_size <? usize)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  replace (usize <? CLONE_ARGS_SIZE_VER0)%Z with false
    by (symmetry; apply Z.ltb_ge; unfold CLONE_ARGS_SIZE, CLONE_ARGS_SIZE_VER0 in *; lia).
  replace (usize <? CLONE_ARGS_SIZE)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  replace (CLONE_ARGS_SIZE <? usize)%Z with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(** The copy fails with one of three errnos. *)
Lemma clone3_copy_errno : forall mem uargs usize reads en,
  clone3_copy mem uargs usize = C3Err reads en ->
  en = E2BIG \/ en = EINVAL \/ en = EFAULT.
Proof.
  intros mem uargs usize reads en H.
  unfold clone3_copy, clone3_copy_full in H. cbv zeta in H.
  repeat first
    [ match type of H with
      | context [if ?b then _ else _] =>
          lazymatch b with
          | true => fail
          | false => fail
          | _ => destruct b; cbv iota in H
          end
      end
    | match type of H with
      | context [match copy_bytes_map ?a ?b ?c with _ => _ end] =>
          destruct (copy_bytes_map a b c); cbv iota in H
      end
    | match type of H with
      | context [match clone3_tail_test ?a ?b ?c with _ => _ end] =>
          destruct (clone3_tail_test a b c); cbv iota in H
      end ];
    try discriminate H; injection H as _ <-; auto.
Qed.

(** THE STRUCT IS READ, AND THE LEDGER SAYS SO.  [clone3] differs from
    legacy [clone] in exactly one observable way before the resolution:
    it copies [struct clone_args] out of user memory, and
    [copy_struct_from_user] faults every page it reads in.  Recording
    the ranges read ([clone3_copy]'s [reads]) is what stops the model
    admitting an allocation the kernel refuses -- [eff_copyins] feeds
    [syscall_effect_accesses] and so [Run.materialize_model_accesses],
    which is where a straddling struct in a [MAP_NORESERVE] region
    charges its second page.

    The ledger names the bytes of the caller's struct that the kernel's
    reads covered: the head, [min size 88] bytes at [uargs], and for a
    longer struct the tail bytes its words covered, before the head.  A
    word of the tail walk also covers bytes outside the struct, but those
    lie on the word's page, which the ledger already names, so the pages
    charged are the same.  A range [access_ok] refuses is -EFAULT with no
    effect beyond the return and the reads before it, and a copy the
    memory does not wholly back is [unmodeled], which carries no effect
    at all. *)
Definition clone3_resolve (reads : list (word * nat)) : Sys SyscallEffect :=
  record_copyins reads clone_resolve.

(** The ledger is the ONLY thing [clone3_resolve] adds: strip it and what
    is left is the very outcome [clone_resolve] admits, with the same
    return, model and events.  Everything proved about the shared
    resolution therefore carries over to [clone3] unchanged. *)
Lemma clone3_resolve_inv : forall reads i m eff m' evs,
  clone3_resolve reads i m (Ok eff m' evs) ->
  exists e0, clone_resolve i m (Ok e0 m' evs) /\ eff_ret eff = eff_ret e0.
Proof.
  intros reads i m eff m' evs H.
  unfold clone3_resolve, record_copyins in H.
  destruct H as (e0 & m0 & evs0 & evs2 & H0 & Hp & Hevs).
  unfold pure in Hp. inversion Hp; clear Hp; subst.
  exists e0. rewrite app_nil_r in *. split; [exact H0 | reflexivity].
Qed.

(** [clone3]'s steps before [kernel_clone], read off the copied struct
    [bs] in kernel order ([copy_clone_args_from_user] and
    [clone3_args_valid], kernel/fork.c, Linux v6.18.46), for a [size] of
    at least [CLONE_ARGS_SIZE] (88, which is [CLONE_ARGS_SIZE_VER2]): the
    size tests (2772-2775) and the copy ([clone3_copy]) have passed, so
    the first test here is the one after the copy.  A shorter struct is
    [clone3_pre_short]'s.
    - [CdErr]: -EINVAL, from a test that reads the struct alone;
    - [CdDecline]: the call declines;
    - [CdArgs r]: every test passed, and [r] is the decoded record.
    The steps:
    1. set_tid_size above 32 ([MAX_PID_NS_LEVEL]), or set_tid and
       set_tid_size not both zero or both non-zero: -EINVAL (2781-2788).
    2. A non-zero set_tid: DECLINE.  The set_tid array is outside the
       model; its copy (2815-2818) comes after steps 3 and 4.
    3. exit_signal with a bit above [CSIGNAL], or above 64 ([_NSIG],
       [valid_signal]): -EINVAL (2794-2796).
    4. CLONE_INTO_CGROUP with cgroup above INT_MAX: -EINVAL (2798-2800;
       the size half of that test never fires at 88 or above).
    5. [clone3_args_valid] (2853-2879): a flag outside
       CLONE_LEGACY_FLAGS, CLONE_CLEAR_SIGHAND and CLONE_INTO_CGROUP;
       CLONE_DETACHED, or a [CSIGNAL] bit other than CLONE_NEWTIME;
       CLONE_SIGHAND with CLONE_CLEAR_SIGHAND; CLONE_THREAD or
       CLONE_PARENT with a non-zero exit signal; a stack of 0 with a
       non-zero size, a non-zero stack with size 0, or a stack range
       [access_ok] refuses ([clone3_stack_valid], 2833-2844): -EINVAL.
    6. CLONE_INTO_CGROUP or CLONE_NEWTIME: DECLINE.  The record has no
       cgroup field; CLONE_NEWTIME (0x80) lies inside the legacy signal
       byte, so it declines before any reader could merge the flags and
       the exit signal into one word, and the time namespace is outside
       the model.  Steps 2 and 6 are [clone3]'s raw-input guard.
    7. Otherwise the record, with [stack] replaced by [stack +
       stack_size] when it is not 0: the riscv stack grows down
       (2845-2847). *)
Inductive Clone3Pre := CdErr | CdDecline | CdArgs (r : CloneArgs).

Definition clone3_pre (bs : list byte) : Clone3Pre :=
  let flags := bv_unsigned (clone_args_field bs 0) in
  let pidfd := clone_args_field bs 1 in
  let child_tid := clone_args_field bs 2 in
  let parent_tid := clone_args_field bs 3 in
  let es := bv_unsigned (clone_args_field bs 4) in
  let stack := clone_args_field bs 5 in
  let ssize := clone_args_field bs 6 in
  let tls := clone_args_field bs 7 in
  let set_tid := clone_args_field bs 8 in
  let set_tid_size := bv_unsigned (clone_args_field bs 9) in
  let cgroup := bv_unsigned (clone_args_field bs 10) in
  if (32 <? set_tid_size)%Z
     || (w_is0 set_tid && negb (set_tid_size =? 0)%Z)
     || (negb (w_is0 set_tid) && (set_tid_size =? 0)%Z)
  then CdErr
  else if negb (w_is0 set_tid) then CdDecline
  else if negb (Z.land es (Z.lnot CSIGNAL) =? 0)%Z || (64 <? es)%Z then CdErr
  else if clone_has flags CLONE_INTO_CGROUP && (2147483647 <? cgroup)%Z then CdErr
  else if clone_has flags
            (Z.lnot (Z.lor CLONE_LEGACY_FLAGS
                       (Z.lor CLONE_CLEAR_SIGHAND CLONE_INTO_CGROUP)))
          || clone_has flags
               (Z.lor CLONE_DETACHED (Z.land CSIGNAL (Z.lnot CLONE_NEWTIME)))
          || (clone_has flags CLONE_SIGHAND && clone_has flags CLONE_CLEAR_SIGHAND)
          || ((clone_has flags CLONE_THREAD || clone_has flags CLONE_PARENT)
                && negb (es =? 0)%Z)
          || (w_is0 stack && negb (w_is0 ssize))
          || (negb (w_is0 stack)
                && (w_is0 ssize || negb (access_okb stack (bv_unsigned ssize))))
  then CdErr
  else if clone_has flags CLONE_INTO_CGROUP || clone_has flags CLONE_NEWTIME
  then CdDecline
  else CdArgs (mkCloneArgs flags es pidfd child_tid parent_tid
                 (if w_is0 stack then stack else stack + ssize) tls).

(** -EINVAL from [clone3]'s own tests or, on the record they pass, from
    [clone_arg_checks] in [kernel_clone] and [copy_process]. *)
Definition clone3_einval_b (bs : list byte) : bool :=
  match clone3_pre bs with
  | CdErr => true
  | CdDecline => false
  | CdArgs r => clone_arg_checks r
  end.

(** A struct shorter than [CLONE_ARGS_SIZE] (64 to 87 bytes), zero-filled
    to 88 by the copy ([clone3_copy]), goes through the same steps, and
    one of them reads the size: step 4 refuses CLONE_INTO_CGROUP when
    [usize < CLONE_ARGS_SIZE_VER2] (fork.c:2798-2800), whatever the
    cgroup field holds.  Steps 1, 3 and 4 are all -EINVAL and all come
    before the set_tid copy and [clone3_args_valid], so on a short struct
    with CLONE_INTO_CGROUP every struct step 1 passes is -EINVAL.  Where
    [clone3_pre] gives -EINVAL or a record, the short struct gives the
    same (a record never has CLONE_INTO_CGROUP: step 6); where it
    declines, at step 2 (a non-zero set_tid) or step 6, the short struct
    is -EINVAL if it has CLONE_INTO_CGROUP, and declines otherwise. *)
Definition clone3_pre_short (bs : list byte) : Clone3Pre :=
  match clone3_pre bs with
  | CdDecline =>
      if clone_has (bv_unsigned (clone_args_field bs 0)) CLONE_INTO_CGROUP
      then CdErr else CdDecline
  | d => d
  end.

(** The steps for the struct [clone3_copy] gives, [short] as it says. *)
Definition clone3_pre_sz (short : bool) (bs : list byte) : Clone3Pre :=
  if short then clone3_pre_short bs else clone3_pre bs.

Definition clone3_einval_sz (short : bool) (bs : list byte) : bool :=
  match clone3_pre_sz short bs with
  | CdErr => true
  | CdDecline => false
  | CdArgs r => clone_arg_checks r
  end.

Lemma clone3_einval_sz_full : forall bs, clone3_einval_sz false bs = clone3_einval_b bs.
Proof. reflexivity. Qed.

(** A struct shorter than 88 without CLONE_INTO_CGROUP goes through the
    steps exactly as the 88-byte struct with the same bytes does. *)
Lemma clone3_pre_short_no_cgroup : forall bs,
  clone_has (bv_unsigned (clone_args_field bs 0)) CLONE_INTO_CGROUP = false ->
  clone3_pre_short bs = clone3_pre bs.
Proof.
  intros bs H. unfold clone3_pre_short. rewrite H.
  destruct (clone3_pre bs); reflexivity.
Qed.

(** A record of the sized steps is [clone3_pre]'s record. *)
Lemma clone3_pre_sz_args : forall short bs r,
  clone3_pre_sz short bs = CdArgs r -> clone3_pre bs = CdArgs r.
Proof.
  intros [|] bs r H; cbn [clone3_pre_sz] in H; [|exact H].
  unfold clone3_pre_short in H. revert H.
  destruct (clone3_pre bs); intros H; [discriminate H| |exact H].
  destruct (clone_has _ _); discriminate H.
Qed.

(** The fork image passes every test and every check, so the order of
    the image test and [clone3_einval_sz] in [clone3_on_struct] changes
    no answer ([clone3_fork_args_no_einval_sz] at every size). *)
Lemma clone3_fork_args_no_einval : forall bs,
  clone3_fork_args_b bs = true -> clone3_einval_b bs = false.
Proof.
  intros bs H. unfold clone3_fork_args_b, w_is0 in H.
  repeat (apply andb_true_iff in H as [H ?]).
  repeat match goal with Hb : bv_eqb _ _ = true |- _ => apply bv_eqb_eq in Hb end.
  unfold clone3_einval_b, clone3_pre. cbv zeta.
  repeat match goal with Hb : clone_args_field bs _ = _ |- _ => rewrite Hb; clear Hb end.
  vm_compute. reflexivity.
Qed.

(** ...and gives a record. *)
Lemma clone3_fork_args_pre_args : forall bs,
  clone3_fork_args_b bs = true ->
  match clone3_pre bs with CdArgs _ => True | _ => False end.
Proof.
  intros bs H. unfold clone3_fork_args_b, w_is0 in H.
  repeat (apply andb_true_iff in H as [H ?]).
  repeat match goal with Hb : bv_eqb _ _ = true |- _ => apply bv_eqb_eq in Hb end.
  unfold clone3_pre. cbv zeta.
  repeat match goal with Hb : clone_args_field bs _ = _ |- _ => rewrite Hb; clear Hb end.
  vm_compute. exact I.
Qed.

(** The record's flags are the struct's flags field. *)
Lemma clone3_pre_flags : forall bs r,
  clone3_pre bs = CdArgs r -> cla_flags r = bv_unsigned (clone_args_field bs 0).
Proof.
  intros bs r H. unfold clone3_pre in H. cbv zeta in H.
  repeat match type of H with
         | context [if ?b then _ else _] => destruct b; cbv iota in H
         end;
    try discriminate H; injection H as <-; reflexivity.
Qed.

(** The fork image at any size: no -EINVAL, and a record. *)
Lemma clone3_fork_args_no_einval_sz : forall short bs,
  clone3_fork_args_b bs = true -> clone3_einval_sz short bs = false.
Proof.
  intros short bs H. pose proof (clone3_fork_args_no_einval bs H) as He.
  pose proof (clone3_fork_args_pre_args bs H) as Ha.
  unfold clone3_einval_b in He. revert He Ha.
  unfold clone3_einval_sz, clone3_pre_sz.
  destruct short; [unfold clone3_pre_short|];
    destruct (clone3_pre bs); intros He Ha; try contradiction Ha; exact He.
Qed.

Lemma clone3_fork_args_pre_args_sz : forall short bs,
  clone3_fork_args_b bs = true ->
  match clone3_pre_sz short bs with CdArgs _ => True | _ => False end.
Proof.
  intros short bs H. pose proof (clone3_fork_args_pre_args bs H) as Ha. revert Ha.
  unfold clone3_pre_sz. destruct short; [unfold clone3_pre_short|];
    destruct (clone3_pre bs); intros Ha; try contradiction Ha; exact I.
Qed.

Lemma clone3_pre_sz_flags : forall short bs r,
  clone3_pre_sz short bs = CdArgs r -> cla_flags r = bv_unsigned (clone_args_field bs 0).
Proof.
  intros short bs r H. exact (clone3_pre_flags bs r (clone3_pre_sz_args short bs r H)).
Qed.

(** THE TWO FIELDS STAY APART: no flag bit in the exit-signal byte, no
    signal bit above it.  So the one word a reader builds from a record,
    [Z.lor flags exit_signal], gives both fields back
    ([flags_signal_split]), and no flag bit is read as part of the exit
    signal.  Both decoders give such records
    ([clone_args_of_clone_split], [clone3_pre_split]). *)
Definition clone_args_split (r : CloneArgs) : Prop :=
  Z.land (cla_flags r) CSIGNAL = 0%Z
  /\ Z.land (cla_exit_signal r) (Z.lnot CSIGNAL) = 0%Z.

Lemma flags_signal_split : forall f e : Z,
  Z.land f CSIGNAL = 0%Z -> Z.land e (Z.lnot CSIGNAL) = 0%Z ->
  Z.land (Z.lor f e) (Z.lnot CSIGNAL) = f /\ Z.land (Z.lor f e) CSIGNAL = e.
Proof.
  intros f e Hf He.
  assert (Hf' : Z.land f (Z.lnot CSIGNAL) = f).
  { transitivity (Z.land f (Z.lor CSIGNAL (Z.lnot CSIGNAL))).
    - now rewrite Z.land_lor_distr_r, Hf, Z.lor_0_l.
    - now rewrite Z.lor_lnot_diag, Z.land_m1_r. }
  assert (He' : Z.land e CSIGNAL = e).
  { transitivity (Z.land e (Z.lor CSIGNAL (Z.lnot CSIGNAL))).
    - now rewrite Z.land_lor_distr_r, He, Z.lor_0_r.
    - now rewrite Z.lor_lnot_diag, Z.land_m1_r. }
  split.
  - now rewrite Z.land_lor_distr_l, He, Z.lor_0_r, Hf'.
  - now rewrite Z.land_lor_distr_l, Hf, Z.lor_0_l, He'.
Qed.

(** With the fields apart, the word is [SIGCHLD] exactly when the record
    is a plain fork's: no flag, exit signal [SIGCHLD]. *)
Lemma clone_args_word_sigchld : forall r, clone_args_split r ->
  (Z.lor (cla_flags r) (cla_exit_signal r) = SIGCHLD
   <-> cla_flags r = 0%Z /\ cla_exit_signal r = SIGCHLD).
Proof.
  intros r [Hf He]. split.
  - intros H. destruct (flags_signal_split _ _ Hf He) as [H1 H2].
    rewrite H in H1, H2.
    change (Z.land SIGCHLD (Z.lnot CSIGNAL)) with 0%Z in H1.
    change (Z.land SIGCHLD CSIGNAL) with SIGCHLD in H2.
    split; symmetry; assumption.
  - intros [-> ->]. reflexivity.
Qed.

Lemma clone_args_of_clone_split : forall a0 a1 a2 a3 a4 r,
  clone_args_of_clone a0 a1 a2 a3 a4 = Some r -> clone_args_split r.
Proof.
  intros a0 a1 a2 a3 a4 r H. unfold clone_args_of_clone in H.
  destruct (bv_unsigned a0 <? 2 ^ 32)%Z; [|discriminate H].
  injection H as <-. unfold clone_args_split. cbn [cla_flags cla_exit_signal].
  split.
  - rewrite <- Z.land_assoc.
    replace (Z.land (Z.land CLONE_LEGACY_FLAGS (Z.lnot CSIGNAL)) CSIGNAL) with 0%Z
      by (vm_compute; reflexivity).
    apply Z.land_0_r.
  - rewrite <- Z.land_assoc.
    replace (Z.land CSIGNAL (Z.lnot CSIGNAL)) with 0%Z by (vm_compute; reflexivity).
    apply Z.land_0_r.
Qed.

(** For [clone] the record's word is a0 itself: a record exists only for
    an a0 below 2^32. *)
Lemma clone_args_of_clone_word : forall a0 a1 a2 a3 a4 r,
  clone_args_of_clone a0 a1 a2 a3 a4 = Some r ->
  Z.lor (cla_flags r) (cla_exit_signal r) = bv_unsigned a0.
Proof.
  intros a0 a1 a2 a3 a4 r H. unfold clone_args_of_clone in H.
  destruct (bv_unsigned a0 <? 2 ^ 32)%Z eqn:Hlt; [|discriminate H].
  injection H as <-. cbn [cla_flags cla_exit_signal].
  rewrite <- Z.land_lor_distr_r.
  replace (Z.lor (Z.land CLONE_LEGACY_FLAGS (Z.lnot CSIGNAL)) CSIGNAL) with (Z.ones 32)
    by (vm_compute; reflexivity).
  rewrite Z.land_ones by lia.
  apply Z.mod_small. apply Z.ltb_lt in Hlt.
  destruct (bv_unsigned_in_range 64 a0) as [H0 _].
  split; [exact H0 | exact Hlt].
Qed.

Lemma clone3_pre_split : forall bs r, clone3_pre bs = CdArgs r -> clone_args_split r.
Proof.
  intros bs r H. unfold clone3_pre in H. cbv zeta in H.
  repeat match type of H with
         | context [if ?b then _ else _] =>
             let E := fresh "E" in destruct b eqn:E; cbv iota in H
         end.
  all: try discriminate H.
  all: injection H as <-; unfold clone_args_split; cbn [cla_flags cla_exit_signal].
  all: repeat match goal with
              | Hb : (_ || _) = false |- _ =>
                  let H1 := fresh "Ho" in let H2 := fresh "Ho" in
                  apply orb_false_iff in Hb as [H1 H2]
              end.
  all: match goal with
       | HD : clone_has ?f (Z.lor CLONE_DETACHED _) = false,
         HT : clone_has ?f CLONE_NEWTIME = false,
         HE : negb (Z.eqb (Z.land ?e (Z.lnot CSIGNAL)) 0%Z) = false |- _ =>
           unfold clone_has in HD, HT;
           apply negb_false_iff in HD; apply Z.eqb_eq in HD;
           apply negb_false_iff in HT; apply Z.eqb_eq in HT;
           apply negb_false_iff in HE; apply Z.eqb_eq in HE;
           split; [|exact HE];
           assert (HC : CSIGNAL = Z.lor (Z.land (Z.lor CLONE_DETACHED
                          (Z.land CSIGNAL (Z.lnot CLONE_NEWTIME))) CSIGNAL) CLONE_NEWTIME)
             by (vm_compute; reflexivity);
           rewrite HC at 1;
           now rewrite Z.land_lor_distr_r, Z.land_assoc, HD, Z.land_0_l, HT, Z.lor_0_l
       end.
Qed.

Lemma clone3_pre_sz_split : forall short bs r,
  clone3_pre_sz short bs = CdArgs r -> clone_args_split r.
Proof.
  intros short bs r H. exact (clone3_pre_split bs r (clone3_pre_sz_args short bs r H)).
Qed.

(** A failure after [reads]: the copy's -E2BIG, -EINVAL or -EFAULT
    ([clone3_copy]). *)
Definition clone3_fail (reads : list (word * nat)) (en : Z) : Sys SyscallEffect :=
  record_copyins reads (err_ret en).

(** [clone3]'s -EINVAL from a test that reads the copied struct, with
    the copy's [reads] in the ledger. *)
Definition clone3_einval (reads : list (word * nat)) : Sys SyscallEffect :=
  record_copyins reads (err_ret EINVAL).

(** A [clone3] record [clone_class] gives [CcFork], other than the fork
    image: the fork resolution with the host refusers' errnos
    ([clone_refusable_arm]) and the record's stores ([clone_with_stores]),
    the copy's [reads] in the ledger, so a refusal carries the ledger
    [clone3_refused_fail] gives the fork image.  The record's stack is
    [stack + stack_size] (fork.c:2845-2847) and its tls the struct's; the
    caller's answer reads neither, the child's registers do
    ([Procs.child_ms]).  A [clone3] record with a namespace bit declines:
    [clone3_spec_lists] answers no other class. *)
Definition clone3_with_stores (reads : list (word * nat)) (r : CloneArgs)
    : Sys SyscallEffect :=
  record_copyins reads (clone_with_stores r (clone_refusable_arm clone_resolve)).

(** What [clone3] does with the struct [clone3_copy] gives: the fork
    image, -EINVAL from its own tests or the argument checks, or a record
    [clone_class] puts in the fork class; everything else declines. *)
Definition clone3_on_struct (reads : list (word * nat)) (short : bool) (bs : list byte)
    : Sys SyscallEffect :=
  if clone3_fork_args_b bs then clone3_resolve reads
  else if clone3_einval_sz short bs then clone3_einval reads
  else match clone3_pre_sz short bs with
       | CdArgs r =>
           match clone_class r with
           | CcFork => clone3_with_stores reads r
           | _ => unmodeled
           end
       | _ => unmodeled
       end.

(** THE SIZE TESTS AND THE COPY COME FIRST ([clone3_copy]): the call
    fails, declines, or goes on with the struct.  The copy asks
    [access_ok] before it walks, through [State.copy_bytes_map] and, for
    the tail, before its first word: [copy_clone_args_from_user]
    (kernel/fork.c, Linux v6.18.46) reads the struct with
    [copy_struct_from_user] (include/linux/uaccess.h), whose
    [copy_from_user] asks [access_ok] in [_inline_copy_from_user], which
    riscv64 reaches through [_copy_from_user] (lib/usercopy.c) because it
    defines no [masked_user_access_begin].  So a [uargs] whose range
    wraps past 2^64 and reads back from 0 is -EFAULT before the fields
    are judged — the bare walk read a fork-shaped struct there and the
    arm resolved the call.  [Checks.Cases.Kernel.Fork]'s [clone3_wrap_]
    group pins it, beside a neighbour at the top of what [access_ok]
    accepts; its [clone3_size_] group pins the size tests and the tail
    test.

    This is the answer from the model's lists; [clone3_spec] below adds
    the host refusers' errnos to it ([clone3_spec_default_iff]). *)
Definition clone3_spec_lists (uargs size : word) : Sys SyscallEffect :=
  i <- input ;;
  match clone3_copy (in_mem i) uargs (bv_unsigned size) with
  | C3Err reads en => clone3_fail reads en
  | C3Decline => unmodeled
  | C3Struct reads short bs => clone3_on_struct reads short bs
  end.

(** The calls of 435 that reach [copy_process] in a class the model
    answers: a size and a copy that give a struct ([clone3_copy]), and
    the fork image.  At [CLONE_ARGS_SIZE] that is a struct the copy read
    whole ([clone3_answered_b_88]); a short struct and a long one with a
    zero tail reach [copy_process] the same way ([clone3_copy]). *)
Definition clone3_answered_b (uargs size : word) (i : SyscallInput) : bool :=
  match clone3_copy (in_mem i) uargs (bv_unsigned size) with
  | C3Struct _ _ bs => clone3_fork_args_b bs
  | _ => false
  end.

(** The ranges the copy read, whatever it gave. *)
Definition clone3_copy_reads (c : Clone3Copy) : list (word * nat) :=
  match c with
  | C3Err reads _ => reads
  | C3Decline => []
  | C3Struct reads _ _ => reads
  end.

(** ...at the call's own input. *)
Definition clone3_input_reads (uargs size : word) (i : SyscallInput) : list (word * nat) :=
  clone3_copy_reads (clone3_copy (in_mem i) uargs (bv_unsigned size)).

(** A refusal of 435 comes after the struct was read, so it carries the
    copy-in ledger [clone3_resolve] carries: the copy's [reads]. *)
Definition clone3_refused_fail (reads : list (word * nat)) : Sys SyscallEffect :=
  record_copyins reads clone_refused_fail.

(** [clone3]: the answer from the lists, and with a refuser present every
    errno from 1 to 4095 for the fork image, at every size the copy
    takes. *)
Definition clone3_spec (uargs size : word) : Sys SyscallEffect :=
  fun i => clone_refusable (clone3_answered_b uargs size)
             (clone3_refused_fail (clone3_input_reads uargs size i))
             (clone3_spec_lists uargs size) i.

(** At [CLONE_ARGS_SIZE] the test and the ledger are the 88-byte ones:
    the struct the copy read whole, and its one range. *)
Lemma clone3_answered_b_88 : forall uargs i,
  clone3_answered_b uargs (Z_to_bv 64 CLONE_ARGS_SIZE) i
  = match copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE with
    | Some bs => clone3_fork_args_b bs
    | None => false
    end.
Proof.
  intros uargs i. unfold clone3_answered_b.
  rewrite clone3_size_88_unsigned, clone3_copy_88. unfold clone3_copy_full.
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE); [reflexivity|].
  destruct (negb (access_okb uargs CLONE_ARGS_SIZE)); reflexivity.
Qed.

Lemma clone3_input_reads_struct : forall uargs size i reads short bs,
  clone3_copy (in_mem i) uargs (bv_unsigned size) = C3Struct reads short bs ->
  clone3_input_reads uargs size i = reads.
Proof.
  intros uargs size i reads short bs H. unfold clone3_input_reads. rewrite H.
  reflexivity.
Qed.

Lemma clone3_refused_fail_inv : forall reads i m o,
  clone3_refused_fail reads i m o ->
  exists e, (1 <= e <= 4095)%Z
            /\ o = Ok (mkEffectU (errno_ret e) [] [] [] [] reads) m [].
Proof.
  intros reads i m o H. unfold clone3_refused_fail, record_copyins, bind in H.
  destruct o as [eff m' evs|]; cbv beta iota in H.
  - destruct H as (e0 & m1 & evs1 & evs2 & H0 & Hp & Hevs).
    apply clone_refused_fail_inv in H0 as (e & He & Heq).
    injection Heq as -> -> ->.
    unfold pure in Hp. injection Hp as -> -> ->.
    exists e. split; [exact He|]. cbn in Hevs. subst evs.
    rewrite app_nil_r. reflexivity.
  - destruct H as [H | (e0 & m1 & evs1 & H0 & Hp)].
    + apply clone_refused_fail_inv in H as (e & _ & Heq). discriminate Heq.
    + unfold pure in Hp. discriminate Hp.
Qed.

Lemma clone3_refused_fail_ok : forall reads e i m,
  (1 <= e <= 4095)%Z ->
  clone3_refused_fail reads i m
    (Ok (mkEffectU (errno_ret e) [] [] [] [] reads) m []).
Proof.
  intros reads e i m He. unfold clone3_refused_fail.
  apply (record_copyins_ok_empty _ _ _ _ (mkEffect (errno_ret e) [] []));
    [reflexivity|].
  apply clone_refused_fail_ok. exact He.
Qed.

(** THE DEFAULT IS TODAY'S ANSWER for [clone3] too. *)
Theorem clone3_spec_default_iff : forall uargs size i m o,
  m_clone_refusers m = no_clone_refusers ->
  (clone3_spec uargs size i m o <-> clone3_spec_lists uargs size i m o).
Proof.
  intros uargs size i m o H. unfold clone3_spec. cbv beta. apply clone_refusable_absent.
  rewrite H. reflexivity.
Qed.

(** THE WORDS ANSWERED BEFORE THE ARGUMENT CHECKS ANSWER AS BEFORE: in
    the model's own lists, the fork word, every namespace word and
    [clone3]'s fork image keep the resolution each had, outcome for
    outcome.  The host refusers' layer above the lists ([clone_spec],
    [clone3_spec]) is the pin's and is untouched by the argument
    checks. *)
Lemma clone_admitted_words_unchanged :
  (forall flags i m o, clone_fork_flags_b flags = true ->
     (clone_spec_lists flags i m o <-> clone_resolve i m o))
  /\ (forall flags i m o, clone_ns_flags_b flags = true ->
     (clone_spec_lists flags i m o <-> clone_ns_resolve i m o))
  /\ (forall uargs i m o bs,
     copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE = Some bs ->
     clone3_fork_args_b bs = true ->
     (clone3_spec_lists uargs (Z_to_bv 64 CLONE_ARGS_SIZE) i m o
      <-> clone3_resolve [(uargs, CLONE_ARGS_SIZE_nat)] i m o)).
Proof.
  split; [|split].
  - intros flags i m o Hf. unfold clone_spec_lists. rewrite Hf. cbv iota.
    apply iff_refl.
  - intros flags i m o Hns. unfold clone_spec_lists. rewrite Hns.
    destruct (clone_fork_flags_b flags) eqn:Hf; [|cbv iota; apply iff_refl].
    exfalso. unfold clone_fork_flags_b in Hf. apply bv_eqb_eq in Hf. subst flags.
    vm_compute in Hns. discriminate Hns.
  - intros uargs i m o bs Hbs Ha. unfold clone3_spec_lists.
    rewrite clone3_size_88_unsigned.
    split; intros H.
    + apply bind_input_iff in H. cbv beta in H.
      rewrite clone3_copy_88 in H. unfold clone3_copy_full in H. rewrite Hbs in H.
      cbv iota in H. unfold clone3_on_struct in H. rewrite Ha in H. exact H.
    + apply bind_input_iff. cbv beta.
      rewrite clone3_copy_88. unfold clone3_copy_full. rewrite Hbs.
      cbv iota. unfold clone3_on_struct. rewrite Ha. exact H.
Qed.

(** A [clone3] (435) THAT CREATES A CHILD HAS A RECORD THE CHECKS PASS,
    for the reason [clone_spec_success_record] gives: an answer that is
    not error-encoded comes from neither a host refuser, nor a failure
    of the size tests or the copy ([clone3_copy]: -E2BIG, -EINVAL,
    -EFAULT), nor the -EINVAL of the struct's own tests or the argument
    checks, so the copy gave a struct, at whatever size, and the struct
    is the fork image, which decodes ([clone3_fork_args_pre_args_sz])
    into a record no check refuses ([clone3_fork_args_no_einval_sz]), or
    a struct whose record the checks pass and [clone_class] puts in the
    fork class ([clone3_with_stores]).  At [CLONE_ARGS_SIZE] the struct
    is the 88 bytes the copy read whole
    ([clone3_spec_success_record_88]). *)
Lemma clone3_spec_success_record : forall uargs size i m eff m' evs,
  clone3_spec uargs size i m (Ok eff m' evs) ->
  addr_is_error_b (eff_ret eff) = false ->
  exists reads short bs r,
    clone3_copy (in_mem i) uargs (bv_unsigned size) = C3Struct reads short bs
    /\ (clone3_fork_args_b bs = true \/ clone_class_fork_b r = true)
    /\ clone3_pre_sz short bs = CdArgs r
    /\ clone_arg_checks r = false.
Proof.
  intros uargs size i m eff m' evs H Herr. unfold clone3_spec in H. cbv beta in H.
  apply clone_refusable_cases in H as [H | H].
  { exfalso. apply clone3_refused_fail_inv in H as (e & He & Heq).
    injection Heq as -> _ _. cbn [eff_ret] in Herr.
    rewrite (errno_ret_is_error e He) in Herr. discriminate Herr. }
  unfold clone3_spec_lists in H.
  apply bind_input_iff in H. cbv beta in H.
  destruct (clone3_copy (in_mem i) uargs (bv_unsigned size))
    as [reads en| |reads short bs] eqn:Hc; cbv iota in H.
  { exfalso. pose proof (clone3_copy_errno _ _ _ _ _ Hc) as Hen.
    unfold clone3_fail, record_copyins, bind in H. cbv beta iota in H.
    destruct H as (core & m1 & evs1 & evs2 & H0 & Hp & _).
    unfold err_ret, ret_only, pure in H0. injection H0 as -> -> ->.
    unfold pure in Hp. injection Hp as -> _ _.
    cbn [eff_ret with_copyins] in Herr.
    destruct Hen as [-> | [-> | ->]]; vm_compute in Herr; discriminate Herr. }
  { exfalso. unfold unmodeled in H. discriminate H. }
  exists reads, short, bs. unfold clone3_on_struct in H.
  destruct (clone3_fork_args_b bs) eqn:Ha; cbv iota in H.
  2: { destruct (clone3_einval_sz short bs) eqn:Hne; cbv iota in H.
       { exfalso.
         unfold clone3_einval, record_copyins, bind in H. cbv beta iota in H.
         destruct H as (core & m1 & evs1 & evs2 & H0 & Hp & _).
         unfold err_ret, ret_only, pure in H0. injection H0 as -> -> ->.
         unfold pure in Hp. injection Hp as -> _ _.
         cbn [eff_ret with_copyins] in Herr. vm_compute in Herr. discriminate Herr. }
       unfold clone3_einval_sz in Hne.
       destruct (clone3_pre_sz short bs) as [| |r] eqn:Hp; cbv iota in H, Hne;
         [ exfalso; unfold unmodeled in H; discriminate H
         | exfalso; unfold unmodeled in H; discriminate H
         | ].
       destruct (clone_class r) eqn:Hcl; cbv iota in H;
         [ | exfalso; unfold unmodeled in H; discriminate H
           | exfalso; unfold unmodeled in H; discriminate H
           | exfalso; unfold unmodeled in H; discriminate H ].
       exists r. split; [first [reflexivity | exact Hc]|].
       split; [right; unfold clone_class_fork_b; rewrite Hcl; reflexivity|].
       split; [first [reflexivity | exact Hp] | exact Hne]. }
  pose proof (clone3_fork_args_pre_args_sz short bs Ha) as Hpre.
  destruct (clone3_pre_sz short bs) as [| |r] eqn:Hp;
    [ exfalso; try rewrite Hp in Hpre; cbv beta iota in Hpre; exact Hpre
    | exfalso; try rewrite Hp in Hpre; cbv beta iota in Hpre; exact Hpre
    | ].
  pose proof (clone3_fork_args_no_einval_sz short bs Ha) as Hne.
  unfold clone3_einval_sz in Hne. rewrite Hp in Hne.
  exists r. split; [first [reflexivity | exact Hc]|].
  split; [left; first [reflexivity | exact Ha]|].
  split; [first [reflexivity | exact Hp] | exact Hne].
Qed.

(** At [CLONE_ARGS_SIZE], the struct of a call that creates a child is
    the 88 bytes the copy read whole, and its record is [clone3_pre]'s. *)
Lemma clone3_spec_success_record_88 : forall uargs i m eff m' evs,
  clone3_spec uargs (Z_to_bv 64 CLONE_ARGS_SIZE) i m (Ok eff m' evs) ->
  addr_is_error_b (eff_ret eff) = false ->
  exists bs r,
    copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE = Some bs
    /\ (clone3_fork_args_b bs = true \/ clone_class_fork_b r = true)
    /\ clone3_pre bs = CdArgs r
    /\ clone_arg_checks r = false.
Proof.
  intros uargs i m eff m' evs H Herr.
  destruct (clone3_spec_success_record _ _ _ _ _ _ _ H Herr)
    as (reads & short & bs & r & Hc & Ha & Hp & Hk).
  rewrite clone3_size_88_unsigned, clone3_copy_88 in Hc. unfold clone3_copy_full in Hc.
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE) as [bs0|] eqn:Hbs.
  - injection Hc as _ Hs Hb. subst short bs0. cbn [clone3_pre_sz] in Hp.
    exists bs, r. split; [first [exact Hbs | reflexivity]|]. split; [exact Ha|].
    split; assumption.
  - destruct (negb (access_okb uargs CLONE_ARGS_SIZE)); discriminate Hc.
Qed.
