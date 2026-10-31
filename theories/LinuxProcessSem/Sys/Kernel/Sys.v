(** * LinuxProcessSem.Sys.Kernel.Sys — getpid (172), getppid (173), gettid (178), setsid (157), uname (160), prctl (167), prlimit64 (261)

    This file answers to Linux [kernel/sys.c]: it holds what the kernel
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
  Syscall Uapi Uaccess Kernel.Fork.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** [getpid]: returns the caller's thread-group id.  It takes no
    arguments and has no failure path — the kernel reads the value out
    of [current] and returns it
    (Linux v6.10-v6.16, kernel/sys.c, [SYSCALL_DEFINE0(getpid)], whose
    body is byte-identical across that range).  riscv OVERRIDES the
    generic [SYSCALL_DEFINE0] with one whose [pt_regs] parameter is
    named [__unused].  The macro that unpacks registers,
    [SC_RISCV_REGS_TO_ARGS], reads [orig_a0] and [a1]..[a6] — seven, not
    six — and has exactly two use sites, [__SYSCALL_DEFINEx] and
    [COMPAT_SYSCALL_DEFINEx]
    (Linux v6.10-v6.16, arch/riscv/include/asm/syscall_wrapper.h,
    [SYSCALL_DEFINE0], [COMPAT_SYSCALL_DEFINE0],
    [SC_RISCV_REGS_TO_ARGS]).  [getpid] goes through NEITHER: the
    zero-argument forms expand without it, and [getpid] has no compat
    variant to reach the second.  So no argument register is read on
    this path, and the model is right to ignore all of them.

    Sharing the relation means sharing its bound: the value this answers
    is inside [PID_MAX_ENVELOPE], whose own argument runs across
    v6.12..v6.16 (see there).  The JOINT claim — that [getpid] answers a
    value in that envelope — therefore holds on v6.12..v6.16, the
    intersection, even though [getpid]'s own body is unchanged over the
    wider range quoted above.

    IT IS THE SAME NUMBER [set_tid_address] RETURNS, and the model
    shares the relation rather than restating it, so the two can never
    drift apart.  The argument is Linux's:

    - [getpid] answers [task_tgid_vnr(current)] and [set_tid_address]
      answers [task_pid_vnr(current)] — the same expression [gettid]
      returns, though the two functions are not identical line for line
      ([set_tid_address] first records [tidptr] in
      [current->clear_child_tid]); it is the RETURN statements that
      match byte for byte
      (Linux v6.10-v6.16, kernel/sys.c, [SYSCALL_DEFINE0(gettid)])
      (Linux v6.10-v6.16, kernel/sys.c, [SYSCALL_DEFINE0(getpid)]; and
      kernel/fork.c, [SYSCALL_DEFINE1(set_tid_address)]).
    - Both are the [_vnr] form, so both pass [ns = NULL] to
      [__task_pid_nr_ns] and resolve it to
      [task_active_pid_ns(current)] — the same namespace object in the
      same call.  No pid namespace can separate them
      (Linux v6.10-v6.16, include/linux/pid.h, [task_pid_vnr] and
      [task_tgid_vnr]; kernel/pid.c, [__task_pid_nr_ns]).
    - They then differ only in which [struct pid] they read:
      [PIDTYPE_PID] takes [current->thread_pid], [PIDTYPE_TGID] takes
      [current->signal->pids[PIDTYPE_TGID]]
      (Linux v6.10-v6.16, kernel/pid.c, [task_pid_ptr]).  A task
      created WITHOUT [CLONE_THREAD] has the very same [struct pid]
      installed as both, so the two are one object and the calls agree
      (Linux v6.10-v6.16, kernel/fork.c, [copy_process]).

    THE PRECONDITION IS "the task is its own thread-group leader", not
    "the task is single-threaded" — the two are different predicates
    and the gap is real.  A process that once called [clone] with
    [CLONE_THREAD] and whose group leader then exited has ONE runnable
    thread, yet its [PIDTYPE_TGID] pid is still the dead leader's while
    its [thread_pid] is its own, so [getpid] and [gettid] disagree
    there.  The model admits no such process.  It DOES have [clone]
    (220) and [clone3] (435), but only for a flag word that shares
    nothing -- [Fork.clone_fork_flags_b] admits [SIGCHLD] alone, and
    [Checks.ProcessCreation.clone_sharing_flags_unmodeled] proves any
    bit of [clone_sharing_bits] forces [Unmodeled], [CLONE_THREAD] and
    [CLONE_SIGHAND] among them.  So no task this model describes was
    ever created with [CLONE_THREAD], and
    [current == current->group_leader] holds throughout.  The premise
    rests on the flag word, not on the syscall NUMBER,
    and widening [clone_fork_flags_b] breaks that proof rather than
    this comment.  ([execve] by
    a non-leader thread re-establishes the equality rather than
    breaking it — [de_thread] swaps the pids so the survivor holds one
    [struct pid] in both slots (Linux v6.10-v6.16, fs/exec.c,
    [de_thread]; kernel/pid.c, [exchange_tids]) — but the model has no
    [execve] mid-process either.)

    Which of the two calls happens first is therefore not observable:
    whichever runs first pins the identity, and the other returns it.
    The tid was already the environment's choice, made once (see
    [Fork.set_tid_address_spec] above); [getpid] only gives a second way to
    observe it.

    Residual infidelity, stated rather than modeled: [SYSCALL_DEFINE0]
    emits [ALLOW_ERROR_INJECTION(..., ERRNO)] — the generic one and
    riscv's alike, as [__SYSCALL_DEFINEx] does for every other number
    here (Linux v6.10-v6.16, include/linux/syscalls.h,
    [SYSCALL_DEFINE0]).  So on a kernel built with
    [CONFIG_FUNCTION_ERROR_INJECTION] and running a BPF program that
    calls [bpf_override_return], any of these calls can be made to
    return an errno.  It bites hardest on the relation shared with
    [set_tid_address], whose spec admits no errno at all, so an injected
    one would make the model REJECT a real kernel's answer.  The model
    describes a kernel with no such override attached. *)
Definition getpid_spec : Sys SyscallEffect := set_tid_address_spec.

(** [gettid]: returns the caller's THREAD id.  Like [getpid] it takes no
    arguments, has no failure path, and reads the value out of [current]
    (kernel/sys.c, [SYSCALL_DEFINE0(gettid)], Linux v6.18.46, commit
    1f99e9ab748f) — the same line the paragraph above quotes, pinned
    here to the version this tree cites rather than carried over from
    the range that paragraph names.  riscv's [SYSCALL_DEFINE0] override
    does not reach it either, for the reason given there: the
    zero-argument form takes [const struct pt_regs *__unused] and
    expands without [SC_RISCV_REGS_TO_ARGS], and [gettid] has no compat
    variant, so no argument register is read on this path and the model
    is right to ignore all of them
    (arch/riscv/include/asm/syscall_wrapper.h, [SYSCALL_DEFINE0], same
    commit).

    IT IS THE SAME NUMBER [set_tid_address] RETURNS, and the model
    shares the relation rather than restating it, exactly as [getpid]
    does.  THE ARGUMENT IS SHORTER THAN [getpid]'S AND RESTS ON LESS,
    which is the one thing worth reading twice here:

    - [gettid] answers [task_pid_vnr(current)] and [set_tid_address]
      answers [task_pid_vnr(current)]
      (kernel/sys.c, [SYSCALL_DEFINE0(gettid)]; and kernel/fork.c,
      [SYSCALL_DEFINE1(set_tid_address)]; both Linux v6.18.46, commit
      1f99e9ab748f).  That is ONE
      EXPRESSION EVALUATED TWICE IN THE SAME TASK, not two expressions
      that agree under a side condition.  No namespace argument and no
      [task_pid_ptr] case split is needed to join them, because there is
      nothing to join.
    - [getpid]'s [task_tgid_vnr] is the one that needs work: it reads
      [PIDTYPE_TGID] where these two read [PIDTYPE_PID], so the
      paragraph above has to establish that the caller is its own
      thread-group leader before the two name one [struct pid].  THAT
      PREMISE IS NOT LOAD-BEARING HERE.  Widening
      [Fork.clone_fork_flags_b] to admit [CLONE_THREAD] would break
      [getpid]'s claim and leave this one standing.

    WHAT IT DOES REST ON is the premise every one of the three shares
    and none of them argues separately, because the STATE carries it:
    [State.m_tid] is ONE slot, so the model describes a process with one
    task.  A second task would need a tid of its own, and [gettid] is
    the syscall that would report it — [getpid] would not, answering the
    shared tgid.  So the fail-closed obligation that keeps this arm
    honest is the clone one: [Checks.ProcessCreation.clone_sharing_flags_unmodeled]
    proves any bit of [clone_sharing_bits] forces [Unmodeled],
    [CLONE_THREAD] among them, so no run this model describes ever has a
    second task to ask.  A change that gave the model threads owes
    [gettid] a per-task tid before it owes [getpid] anything.

    Which of the three calls happens first is not observable, for the
    reason given above: whichever runs first pins the identity and the
    others return it.

    The residual infidelity stated for [getpid] — [SYSCALL_DEFINE0]'s
    [ALLOW_ERROR_INJECTION(..., ERRNO)]
    (include/linux/syscalls.h, [SYSCALL_DEFINE0], Linux v6.18.46,
    commit 1f99e9ab748f) —
    covers this number too, and on the same shared relation, which
    admits no errno at all.  The model describes a kernel with no such
    override attached. *)
Definition gettid_spec : Sys SyscallEffect := set_tid_address_spec.

(** [setsid()]: makes the caller a session leader, or fails -EPERM.

    [ksys_setsid] (kernel/sys.c) seeds [err = -EPERM] and returns it
    unless BOTH tests pass: the caller must not already carry
    [group_leader->signal->leader], and [pid_task(sid, PIDTYPE_PGID)]
    must find no LIVE TASK whose process-group id is the caller's own
    pid.  On success it sets that leader bit, calls [set_special_pids(
    sid)] — which makes the caller lead a process group named by its own
    pid — and returns [pid_vnr(task_pid(group_leader))], the caller's
    tgid: the value [getpid] returns, and the value this model keeps in
    [State.m_tid].

    VERSION WINDOW.  The two tests, their order and the returned session
    id are unchanged in mainline v4.17..v7.2 and in stable
    linux-4.19.y..linux-7.1.y; [ksys_setsid] is byte-identical from
    v4.17 through v6.14, and again from v6.15 through v7.2.  THE SAMPLE
    IS THE INTERIOR, NOT THE ENDPOINTS: the whole body hashed at 22
    mainline tags spanning v4.17..v7.2 — 17 of them inside the lower
    range — and on all ten stable branches in linux-4.19.y..linux-7.1.y
    gives exactly those two forms and no third.  The one edit in that
    window is commit 7903f907a226 ("pid: perform free_pid() calls
    outside of tasklist_lock", first released in v6.15 and backported to
    no older stable branch: every stable branch through linux-6.12.y
    carries the pre-6.15 form, and only linux-6.17.y and later carry the
    other), which threads a [struct pid *pids[PIDTYPE_MAX]] through
    [set_special_pids] and frees the dropped references after
    [write_unlock_irq(&tasklist_lock)]; it changes when references are
    freed, not what the call computes.  [SYSCALL_DEFINE0(setsid)] is
    [return ksys_setsid();] at every one of those tags and branches, so
    the wrapper adds nothing anywhere in the window; setsid is 157 on
    riscv64 (scripts/syscall.tbl, which generates asm/unistd_64.h since
    v6.11 and matched include/uapi/asm-generic/unistd.h before it — the
    generic header keeps the entry either way, so what moved is which
    mechanism riscv reads it through, not where the number lives).

    WHY EVERY CALL BUT THE FIRST SUCCESS ADMITS BOTH ANSWERS.  Whether
    either test fires is a fact about the launching environment and
    about OTHER PROCESSES, and [State.ProcInput] carries neither — it
    carries argv, envp, the file system and stdin, and [Run.ExecEntry]
    carries the stack pointer and the break.  A job-control shell puts
    each job in its own process group, so setsid is -EPERM for the job's
    LEADER; the second and later members of a pipeline are not leaders
    and their setsid succeeds, as does that of a process started without
    job control, which inherits its parent's group.  The model does not
    know which it is, and says so the way it says so everywhere else an
    environment condition is untracked: with an [alt], exactly as
    [Open.openat_spec] offers [openat_errnos] beside its tracked answer.
    Admitting only success would be WRONG rather than conservative.
    What it costs: a program that BRANCHES on the answer has two
    behaviours under this model.

    WHY ONLY SUCCESS IS RECORDED.  A -EPERM is not always sticky.  When
    it comes from the process-group test it USUALLY is: [sid] there is
    the caller's OWN pid, so in the ordinary case the task the test
    finds is the caller itself, which cannot exit while it is running.
    But it need not be the caller.  An environment that created group P
    (= the pid this process was later given), left a descendant in it,
    and then moved this process out with [setpgid] leaves the test
    firing on a task that CAN exit, and once the last such task does,
    the next setsid succeeds.  That state is reachable, so recording a
    failure would forbid a run Linux allows — and the model has no way
    to tell the two shapes apart, since neither the group nor its
    membership is anything it carries.  A SUCCESS is sticky, and
    permanently:
    [ksys_setsid] is the only writer of [signal->leader] in the tree, it
    never clears it, it tests it first, and [SYSCALL_DEFINE2(setpgid)]
    refuses to move a session leader out of its group.  So one bit —
    [State.m_setsid_succeeded] — is exactly what has to be carried; a
    session id, a process-group id and a leader bit would be needed
    only to tell apart states this model cannot observe apart.  What it
    costs: the model cannot say a second call fails after a first one
    did.

    THE SESSION ID is the caller's tgid, and equals the tid
    [Fork.set_tid_address_spec] reports only because this model has one
    thread — see [State.m_tid]'s note — so it is [State.m_tid], picked
    in the same envelope [Fork.set_tid_address_spec] picks it in and
    equal to any value already observed.  The consistency is written
    into the [choose] rather than read out of [State.m_tid] by a match,
    which is what keeps the two arms of the [alt] disjoint for EVERY
    [Model] and not merely every reachable one: a return of
    [errno_ret EPERM] can never satisfy the range, so it belongs to the
    first arm alone.  No memory effect — setsid takes no arguments and
    writes nothing.

    WHAT SUCCESS ALSO DOES, AND WHY IT DOES NOT SHOW.
    [sched_autogroup_create_attach] changes scheduling weight and
    [proc_sid_connector] emits a netlink message to whoever subscribed;
    neither is a syscall answer to this process, and both — like
    [proc_clear_tty] — are empty inlines without their config option.
    [proc_clear_tty(group_leader)] is the one that is NOT free in
    general: it clears [signal->tty], after which [__tty_check_change]
    stops matching and the caller no longer takes SIGTTIN when it READS
    an inherited terminal from a background process group (the SIGTTOU a
    background WRITE would raise is additionally gated on [L_TOSTOP],
    off by default, so that half is usually moot anyway).  It is
    invisible HERE because of two commitments of this model
    — its channels are never terminals
    ([Ioctl.ioctl_spec] answers TIOCGWINSZ -ENOTTY on every open fd) and
    it delivers no signals at all — so there is no controlling terminal
    to clear and no SIGTTIN to withhold.  Revisit this if either
    commitment is relaxed. *)
Definition setsid_spec : Sys SyscallEffect :=
  m <- get_model ;;
  if m_setsid_succeeded m then err_ret EPERM
  else
    alt (err_ret EPERM)                       (* an untracked environment condition *)
        (tid <- choose (fun t =>
                  (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\
                  match m_tid m with None => True | Some t0 => t = t0 end) ;;
         set_tid tid ;;
         set_setsid_succeeded ;;
         ret_only tid).

(** [getppid] (173): the thread-group id of the caller's PARENT, as the
    caller's own pid namespace numbers it.  No argument and no failure
    path:

        rcu_read_lock();
        pid = task_tgid_vnr(rcu_dereference(current->real_parent));
        rcu_read_unlock();
        return pid;

    kernel/sys.c [SYSCALL_DEFINE0(getppid)], read at v6.18.44; identical at v6.18.46.
    include/linux/pid.h [task_tgid_vnr], read at v6.18.44; identical at v6.18.46.
    kernel/pid.c [__task_pid_nr_ns], [pid_nr_ns], read at v6.18.44; identical at v6.18.46.
    kernel/exit.c [forget_original_parent], read at v6.18.44; identical at v6.18.46.

    THE RANGE IS [[0, Fork.PID_MAX_ENVELOPE)], the tid's envelope with 0
    admitted.  [task_tgid_vnr] is [__task_pid_nr_ns(parent, PIDTYPE_TGID,
    NULL)], which takes the namespace of the CALLER
    ([task_active_pid_ns(current)]) and asks [pid_nr_ns] for the
    parent's number in it.  [pid_nr_ns] answers 0 when the parent's
    [struct pid] has no number at that level -- the parent lives in an
    ancestor namespace, which is exactly the first process of a
    [clone(CLONE_NEWPID)] asking about the process that made it -- and
    otherwise a pid of the caller's namespace, which is below [pid_max]
    and so below [PID_MAX_ENVELOPE] (the argument is at that
    definition).  0 is a real answer here where it is not for the
    caller's own tid: a task always has a number in its own active
    namespace, its parent need not.

    A FRESH CHOICE ON EVERY CALL, AND NO PIN.  The parent is the one
    process fact this model cannot hold still.  When the parent exits,
    [forget_original_parent] rewrites the caller's [real_parent] to a
    subreaper or to the namespace's init, at a moment no input of this
    model names, so two calls can answer two different values.  A
    choice recorded once, the way [Fork.set_tid_address_spec] records
    the tid, would forbid that run; an unconstrained choice per call
    admits it, and that is the honest model.

    A PROGRAM CAN TOLERATE IT.  What a fresh choice costs is that the
    model never says WHICH parent: a statement that needs [getppid] to
    name a particular process has to take that as a premise about the
    environment.  What it does not cost is the program that CHECKS:
    BET-467's launcher is handed the pid of the process that started it,
    compares [getppid]'s answer with it, and stops if they differ.  A
    proof about that program quantifies over the answer, reads it from
    the call log ([Run.star_calls]: [sc_no = 173], [sc_ret]) and covers
    both branches, which is exactly what a per-call choice supports.

    No argument register is read and no model state is read or written:
    the riscv [SYSCALL_DEFINE0] wrapper argument given at [getpid_spec]
    covers this number too, as does its residual error-injection
    infidelity.  The four credential READERS -- [getuid] (174),
    [geteuid] (175), [getgid] (176), [getegid] (177) -- and five setters
    are in the credentials section below. *)
Definition getppid_spec : Sys SyscallEffect :=
  ppid <- choose (fun p : word => (bv_unsigned p < PID_MAX_ENVELOPE)%Z) ;;
  ret_only ppid.

(* ------------------------------------------------------------- prlimit64 *)

(** A [struct rlimit64] as the 16 bytes Linux moves through
    [copy_to_user]: [__u64 rlim_cur] then [__u64 rlim_max], little-endian,
    8-byte aligned, no padding (Linux v6.10-v6.15,
    include/uapi/linux/resource.h, [struct rlimit64]; byte-identical at
    all six tags).

    The kernel stores a [struct rlimit] of [__kernel_ulong_t] and converts
    with [rlim_to_rlim64]/[rlim64_to_rlim], but on riscv64 both are the
    IDENTITY: [BITS_PER_LONG] is 64, so [RLIM_INFINITY] = [~0UL] =
    [~0ULL] = [RLIM64_INFINITY] and [rlim64_is_infinity] collapses
    nothing.  Every 64-bit pattern round-trips unchanged, which is why
    this model stores the user's words verbatim.  (On a 32-bit
    architecture the conversion clamps a whole range to infinity; that
    architecture is not modeled.)

    The model holds the 16 BYTES and only ever projects out of them; it
    never builds them from a decoded pair.  That is deliberate: an
    encode/decode round trip would have to be proved to make the spec and
    the executable checker agree, and nothing here needs one when both
    sides read the same bytes the same way. *)
Definition rlim64_soft (bs : list byte) : word := le_bytes_to_word (firstn 8 bs).
Definition rlim64_hard (bs : list byte) : word := le_bytes_to_word (skipn 8 bs).

(** The kernel's standing invariant on a limit pair: 16 bytes wide, and
    soft <= hard.  [do_prlimit] refuses to store a pair violating it
    (-EINVAL), and no other path can create one, so no [prlimit64] read
    reports soft > hard anywhere in the cited window (Linux v6.10-v6.15,
    kernel/sys.c, [do_prlimit]; byte-identical at all six tags). *)
Definition rlim64_wf (bs : list byte) : bool :=
  (Nat.eqb (length bs) 16
   && (bv_unsigned (rlim64_soft bs) <=? bv_unsigned (rlim64_hard bs))%Z)%bool.

(** [prlimit64(pid, resource, new_rlim, old_rlim)] — syscall 261.

    WHY THIS NUMBER.  riscv64 carries all three of [getrlimit] (163),
    [setrlimit] (164) and [prlimit64] (261) at every tag in the cited
    window, but the first two arrive by TWO DIFFERENT MECHANISMS across
    it, so one path-and-range pairing would be wrong at one end.  Through
    v6.10 the numbers come from [__ARCH_WANT_SET_GET_RLIMIT], defined for
    [__LP64__] in arch/riscv/include/uapi/asm/unistd.h — the uapi header,
    not the one beside it.  From v6.11 riscv generates its table instead,
    and the selection is [syscall_abis_64 += riscv rlimit] in
    arch/riscv/kernel/Makefile.syscalls; the older define survives but no
    longer decides anything.  163 and 164 are NOT
    modeled and fall through the dispatcher to [unmodeled], which is
    correct rather than merely convenient: they enter [do_prlimit]
    DIRECTLY, skipping [check_prlimit_permission] and the
    [security_task_prlimit] LSM hook, so they are a different call and
    would need their own argument.  musl reaches the limits through
    [prlimit64] regardless — its [getrlimit]/[setrlimit] try
    [SYS_prlimit64] first and only fall back on -ENOSYS.

    ONLY [RLIMIT_CORE] IS MODELED.  Every other resource id is
    [unmodeled] (fail closed).  This is not caution about ids nobody
    uses; five of them would CONTRADICT the rest of this model if an
    arm answered them, three by disagreeing with state the model keeps
    and two by promising an errno it never raises:

    - [RLIMIT_STACK] is ALREADY modeled, as [State.stack_max_size] = 8
      MiB.  It is observable — [Run.init_machine_state] zero-maps exactly
      [[Run.stack_window_lo], init_sp)], whose floor is the higher of
      [stack_max_size] below the stack VMA's end [StackLayout.ed_top]
      and the guard gap above the mmap base, so under a launch
      [Run.entry_launch_ok_va] admits it is what is left below
      [init_sp] of the [stack_max_size] bytes under that end, and a
      store outside that
      window is a [RiscvSemantics.MachineFault] — and it also fixes
      [State.alloc_top] relative to the run's stack pointer.  It is a
      CONSTANT, so a [setrlimit] that
      claimed to change it would be a lie, and a [getrlimit] arm would
      have to answer the 8 MiB soft limit while claiming a hard limit the
      model does not represent.
    - [RLIMIT_AS] and [RLIMIT_DATA] are the real kernel checks
      ([may_expand_vm]) that this file already names, at the mremap and
      mprotect notes above, as the reason -ENOMEM stays INJECTABLE rather
      than tracked.  The nearby [VmMaps.vm_limit] is not either of them —
      it meters only [vm_maps], never the image or the stack — and it is
      a PARAMETER OF THE RUN pinned per role by
      [Equivalence.strong_equiv] to [State.source_alloc_limit] (16 GiB)
      or [State.target_alloc_limit] (512 GiB).  An arm answering
      [getrlimit(RLIMIT_AS)] with [vm_limit] would therefore let a
      program read WHICH SIDE OF THE EQUIVALENCE IT IS, and answering
      [RLIM_INFINITY] instead would deny an allocation failure the model
      really does force.

    - [RLIMIT_FSIZE] caps a write, and this model has no -EFBIG: the
      transfer bound the write/writev specs enforce is [Uaccess.rw_bytes_max],
      Linux's own [MAX_RW_COUNT], which is a different limit with a
      different failure.  An arm reporting a file-size limit would
      promise an enforcement no spec in this file performs.
    - [RLIMIT_NOFILE] is the one the model HOLDS —
      [State.limst_nofile], the SOFT limit, an input of the run seeded by
      [State.init_model] and read by [Fs.File.dup3_spec] — and it is
      declined here, for two reasons.
      Answering a READ would have to fill in a whole [struct rlimit64],
      and the HARD limit is not carried: nothing reads it, so nothing
      obliged the record to hold it.  Answering the soft one alone would
      also hand a program a bound the fd allocator does not honour —
      [File.lowest_fd] ignores it.  And answering a SET
      would make the field MUTABLE, which [Fs.File.dup3_spec]'s gate is
      built on it not being: that spec tests one number for the whole
      run.  Widening this arm to RLIMIT_NOFILE therefore has three
      obligations, not one.

    [RLIMIT_CORE] is safe for the opposite reason: this model has no
    signals, no [MachineFault]-to-core-dump path, and the only channel
    by which a file appears in an observable [Fs] is [openat]/[write]/
    [writev].  Nothing can dump core, so the limit on a core dump's size
    constrains nothing the semantics can see.  It is modeled anyway
    because it is what a real program sets: it is the first
    dropbear-attributable syscall in a trace, from [disallow_core].

    WHAT THE ARMS ARE.  The enumeration below is THIS SPEC'S OWN MATCH
    ORDER — pid, then resource, then the pointer pairing, then read
    against write — and IT IS NOT LINUX'S CHECK ORDER.  Linux's, from
    kernel/sys.c's [SYSCALL_DEFINE4(prlimit64)] and [do_prlimit], is:

        [new_rlim]'s [copy_from_user]               -EFAULT
        [pid] / [find_task_by_vpid]                 -ESRCH
        [check_prlimit_permission]                  -EPERM (and its LSM)
        [do_prlimit]: [resource >= RLIM_NLIMITS]    -EINVAL
        [do_prlimit]: [rlim_cur > rlim_max]         -EINVAL
        [do_prlimit]: [capable]/[security_task_setrlimit]  -EPERM
        [old_rlim]'s [copy_to_user]                 -EFAULT

    The pointer read is FIRST on the kernel and does not appear in the
    enumeration at all; (3) below is where that gap is stated and
    costed.  Nothing depends on the two orders agreeing: every arm on
    which they differ is [unmodeled], and an [unmodeled] arm admits
    nothing, so it cannot contradict the kernel the way a mis-ordered
    answer would.  An enumeration of what a call refuses is not a claim
    about what it checks first.

    THE CITED WINDOW, AND WHERE IT DOES NOT REACH.
    [SYSCALL_DEFINE4(prlimit64)] is byte-identical across MAINLINE
    v6.10-v6.15 — in fact across v6.9-v6.17 — but that is a claim about
    mainline only.  linux-6.12.y carries the later [need_tasklist] /
    [pid_alive] form — mainline's own text only after v6.17, backported
    to that LTS branch — which inserts a SECOND -ESRCH between
    [check_prlimit_permission] and [do_prlimit].  It is gated on
    [!same_thread_group(tsk, current)], and at [pid] 0 — the only pid
    this spec answers — [tsk] IS [current], so the gate is false and the
    arm is unreachable.  Nothing below changes; the byte-identity claim
    is what needed scoping.  [do_prlimit] itself is identical on
    linux-6.12.y as well.

    (1) [pid] must be 0.  [tsk = pid ? find_task_by_vpid(pid) : current],
        so 0 means [current] and takes no lookup.  A nonzero pid is
        [unmodeled]: this model steps a single process and has no
        other pid to compare against, so it can decide neither the
        -ESRCH of a pid that names nothing nor the credential match in
        [check_prlimit_permission].  ([clone] can RETURN a child
        pid, but the child is never a task this model steps, so there
        is nothing for a nonzero [pid] to name.)  Note the kernel's own fast path is
        [if (current == task) return 0], so a nonzero pid naming this
        very process would behave identically — the model simply cannot
        tell which pid that is.
    (2) [resource] must be [RLIMIT_CORE] (see above).
    (3) THE MODEL DECLINES EARLIER THAN LINUX ANSWERS, deliberately, and
        the gap is worth naming because order is behavior.  Linux does
        the [new_rlim] [copy_from_user] in [SYSCALL_DEFINE4(prlimit64)]
        itself, BEFORE the pid lookup and before [do_prlimit]'s
        [resource >= RLIM_NLIMITS] test — so
        [prlimit64(0, 9999, bad_ptr, NULL)] is -EFAULT on a real kernel,
        and [prlimit64(999, 9999, bad_ptr, NULL)] is too.  This spec
        tests pid and resource first and yields [unmodeled] for both,
        which is the difference the header above names between this
        enumeration's order and Linux's.
        That is a DECLINE, not a wrong answer: an [unmodeled] arm admits
        nothing, so it cannot contradict the kernel the way a
        mis-ordered -EINVAL would.  What it costs is coverage — those
        two calls leave the modeled surface instead of being answered —
        and nothing needs them, since a program that faults its own
        rlimit pointer has already lost.  The same bound applies to a
        set made before any read: (6) declines on the missing record
        before it looks at the pointer, so its -EFAULT is out of reach
        too.
    (4) Exactly one of [new_rlim]/[old_rlim] is non-NULL.  Both NULL is a
        no-op nothing issues.  Both non-NULL is the read-modify-write
        [prlimit64] alone can express, and it is [unmodeled] for a
        specific reason: when its [copy_to_user] of [old_rlim] faults,
        the kernel returns -EFAULT with the new limit ALREADY COMMITTED
        and does not roll back at any of the six cited tags.  Modeling
        a failed call that mutates state is a real obligation, and
        nothing needs it — glibc's and musl's [getrlimit]/[setrlimit]
        each pass NULL for the other pointer.
    (5) THE READ ([new_rlim] NULL).  The pair is written to [old_rlim]
        and 0 returned.  On the first read the environment CHOOSES it,
        subject only to the kernel's invariant soft <= hard, and the
        model records it in [m_rlimit_core]; every later read returns
        what was recorded.  This is [set_tid_address]'s pin exactly: the
        limits are inherited at exec and the model does not know them,
        but they do not change under it.  A successful set REPLACES the
        record, so a read after a set reports what was set rather than
        what was inherited.  (Linux's own boot default is
        [RLIMIT_CORE] = [{0, RLIM_INFINITY}], per [INIT_RLIMITS] in
        include/asm-generic/resource.h, but a parent may have set
        anything, so pinning that constant would be a narrower claim than
        the truth.)
    (6) THE WRITE ([old_rlim] NULL).  The 16 bytes are read as
        [(cur, max)].
        An [access_ok] rejection happens before [copy_from_user] issues a
        load, so that -EFAULT arm records no copy-in.  Once the range passes
        that gate and the struct is readable, all 16 bytes are recorded —
        including when the decoded pair is later refused with -EINVAL.
        - [cur > max] is -EINVAL, which the kernel tests before any
          capability or LSM question.
        - Otherwise the new HARD limit must EQUAL the recorded one.
          RAISING is the case the model genuinely cannot decide:
          [do_prlimit] consults [capable(CAP_SYS_RESOURCE)] exactly when
          [new_rlim->rlim_max > rlim->rlim_max], and this model carries no
          credentials, the same gap the [rw_verify_area] note above names
          for its LSM denial and the [mmap] note for [security_mmap_addr]'s
          -EPERM.
          LOWERING IS A DELIBERATE BOUND, NOT A NECESSITY, and it is worth
          saying which it is.  [security_task_setrlimit] runs on every set,
          but its SELinux implementation ([selinux_task_setrlimit]) consults
          the AVC only when [rlim_max] CHANGES, so an unchanged hard limit is
          unconditionally 0 there — this arm is better founded than "the hook
          might refuse".  AppArmor is the real counterexample:
          [apparmor_task_setrlimit] can deny a set that leaves [rlim_max]
          alone, and what covers that is this model's standing position that
          it has no LSM at all, not anything special about the arm.  Under
          that position a lowering set is exactly as decidable as an
          unchanged one.  It is declined because nothing
          needs it — dropbear writes the hard limit back untouched — and
          because the narrower arm is the one that stays true if this model
          ever acquires an LSM, whereas an arm admitting lowering would
          have to be withdrawn.  [tests/prlimit64_spec.c]'s [set-lower]
          mode pins the kernel's own answer on the outside of that bound.
        - A write before any read is [unmodeled]: with [m_rlimit_core]
          still [None] the recorded hard limit does not exist, so the
          comparison above cannot be made.  [disallow_core] does its
          [getrlimit] first, which is what makes its [setrlimit] land
          inside the modeled surface.

    A pointer that is not fully readable/writable is -EFAULT only when
    [access_ok] refuses the range ([State.access_okb], the test the
    zero-length transfers already use); a range [access_ok] admits that
    is not wholly mapped is [unmodeled], as every other buffer in this
    file.  For [old_rlim] that is because Linux's copy-out there may be
    PARTIAL and the model cannot say how much of it landed; for
    [new_rlim] the copy-in goes to a kernel local and a fault is a plain
    -EFAULT, but which bytes of the mask the kernel read is not something
    the ledger can state, so it declines the same way.

    WHAT THE DECLINES COST THE EQUIVALENCE THEOREM.  Not an escape — a
    REFUSAL TO CERTIFY.  [Equivalence.strong_equiv] is [modeled] of the
    SOURCE conjoined with [equiv], and [modeled] is an obligation to
    PROVE, not one the source is let off: it exists precisely so that a
    binary using an unmodeled syscall cannot satisfy the theorem
    trivially.  So a source reaching one of the arms above is NOT
    vacuously equivalent to anything; [strong_equiv] becomes unprovable
    for it, and per [Equivalence.strong_equiv]'s own note a source that
    leaves the modeled surface on ONE input fails the theorem even where
    it is well covered on every other.  (The [bh_all_errors] escape is a
    different mechanism, internal to [equiv], and it is all-executions
    rather than per-resolution; it does not fire here.)

    The arms
    named above — a nonzero pid, a resource other than RLIMIT_CORE, both
    pointers, a set before a read or one changing the hard limit — are
    where the refusal begins, and keeping source binaries
    away from them is the job of whoever chooses the source. *)
Definition prlimit64_spec (pid resource new_rlim old_rlim : word)
    : Sys SyscallEffect :=
  if negb (w_is0 pid) then unmodeled            (* (1) no other task exists *)
  else if negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE) then unmodeled  (* (2) *)
  else if w_is0 new_rlim && w_is0 old_rlim then unmodeled                 (* (4) *)
  else if negb (w_is0 new_rlim) && negb (w_is0 old_rlim) then unmodeled   (* (4) *)
  else
  i <- input ;;
  m <- get_model ;;
  if w_is0 new_rlim then
    (* (5) the READ *)
    match read_bytes_map (in_wmem i) old_rlim (Z_to_bv 64 16) with
    | None =>
        if negb (access_okb old_rlim 16) then err_ret EFAULT
        else unmodeled
    | Some _ =>
        match m_rlimit_core m with
        | Some bs => pure (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] [])
        | None =>
            bs <- choose (fun bs : list byte => rlim64_wf bs = true) ;;
            set_rlimit_core bs ;;
            pure (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] [])
        end
    end
  else
    (* (6) the WRITE *)
    match m_rlimit_core m with
    | None => unmodeled          (* no recorded hard limit to compare against *)
    | Some bs0 =>
        match read_bytes_map (in_mem i) new_rlim (Z_to_bv 64 16) with
        | None =>
            if negb (access_okb new_rlim 16) then err_ret EFAULT
            else unmodeled
        | Some nb =>
            record_copyins [(new_rlim, 16%nat)]
            (
            if (bv_unsigned (rlim64_hard nb) <? bv_unsigned (rlim64_soft nb))%Z
            then err_ret EINVAL
            else if negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0)) then unmodeled
            else set_rlimit_core nb ;; ret_only (Z_to_bv 64 0))
        end
    end.

(* =========================================================================
   Credentials — who the process is
   =========================================================================

   These calls NEED CREDENTIAL STATE.  Without it the only answer available
   would be the constant 0 the auxv reports, and a spec answering 0 would make
   [Checks.ExecutableSpecs.check_syscall] return [CheckReject] on the
   truthful answer of any kernel not running the process as root — the
   model accusing the kernel of a violation it did not commit.
   [State.ProcInput]
   carries the launching ids, so the readers answer what the environment
   chose instead of what the model guessed.  The auxv reports the SAME
   answer rather than a second one: [StackLayout.auxv_entries] takes the
   uid as an argument and [Run.init_machine_state] fills it from
   [State.in_uid], the field [State.init_model] copies into the
   credentials read here, so AT_UID and [getuid] cannot disagree — which
   is what Linux guarantees by munging one [struct cred] field in both
   [create_elf_tables] and [SYSCALL_DEFINE0(getuid)].

   The kernel keeps eight ids in [struct cred] ([include/linux/cred.h]):
   [uid]/[gid], [euid]/[egid], [suid]/[sgid], [fsuid]/[fsgid].  The model
   keeps six ([State.Creds]) and reads the other two off them;
   [State.Creds]'s comment says which are dropped and why.  Everything
   below is read off stable Linux v6.18.46 (commit 1f99e9ab748f),
   kernel/sys.c.  The four setter entry points this file models --
   [__sys_setuid], [__sys_setgid], [__sys_setresuid] and [__sys_setresgid],
   together with the [set_user] and [flag_nproc_exceeded] helpers the uid
   half of them calls -- are BYTE-IDENTICAL there and at every mainline
   release tag from v6.10 through v6.18, so no line here is one release's
   answer.

   TWO STANDING ASSUMPTIONS about the environment, both needed and both
   stated once here rather than repeated per syscall:

   - THE INIT USER NAMESPACE.  [make_kuid]/[make_kgid] are then the
     identity on the value, and every "is this id valid" test reduces to
     "is it different from [(uid_t)-1]" (Linux v6.18.46,
     kernel/user_namespace.c, [make_kuid]; include/linux/uidgid.h,
     [INVALID_UID]).  This is what makes [setresuid]'s and [setresgid]'s
     -EINVAL UNREACHABLE, below.
   - A CAPABILITY-ONLY LSM.  [security_task_fix_setuid] is then
     [cap_task_fix_setuid], which returns 0 for every flag these calls
     pass, and [security_task_fix_setgid] has no capability-LSM hook at
     all and takes its default of 0 (Linux v6.18.46,
     security/commoncap.c, [cap_task_fix_setuid];
     include/linux/lsm_hook_defs.h).  A kernel running SELinux, AppArmor
     or Smack can deny where this model permits, and is outside the
     window.

   [State.creds_privileged] carries the third and largest assumption, the
   one that lets an effective uid stand in for a capability set.
   ========================================================================= *)

(** Every id these syscalls can INSTALL is one a real process could hold
    — [Run.valid_id]'s bound, kept for the whole RUN and not only at
    launch.  Two steps, both visible in the specs below: [Syscall.uid32]
    puts every argument below 2^32, and the single 32-bit value no
    process can hold is never written, because [setid_spec] rejects it
    with -EINVAL before it reaches [set_creds] and [setresid_spec] reads
    it as "leave this id alone" rather than as a value.  So no run
    reaches a credential state that [Run.valid_creds] would have refused
    as a starting point. *)

(** The three user ids, or the three group ids, of one [State.Creds] —
    real, effective, saved.  [setuid]/[setgid] and
    [setresuid]/[setresgid] are pairs of syscalls whose rules are
    identical once you say which triple they act on, so the specs below
    are written once over this view and applied twice.  What genuinely
    differs between the pair is one thing, and it is an argument:
    the user setters can fail with -EAGAIN and the group setters cannot
    (see [setid_errnos]). *)
Record IdTriple := mkIdTriple {
  id_real  : word;
  id_eff   : word;
  id_saved : word;
}.

Definition cred_uids (c : Creds) : IdTriple :=
  mkIdTriple (cr_uid c) (cr_euid c) (cr_suid c).
Definition cred_gids (c : Creds) : IdTriple :=
  mkIdTriple (cr_gid c) (cr_egid c) (cr_sgid c).

(** Both setters CARRY THE SUPPLEMENTARY GROUP LIST OVER UNCHANGED, and
    that is a kernel fact rather than a convenience: [__sys_setuid],
    [__sys_setgid], [__sys_setresuid] and [__sys_setresgid] (kernel/sys.c)
    each build the new credentials with [prepare_creds], which [memcpy]s
    the old [struct cred] and takes another reference on the SAME
    [group_info] (kernel/cred.c), and then write only the id fields.
    Nothing on those four paths calls [set_groups].  A setter that
    dropped the list here would make a later [getgroups] (158) report 0
    where Linux reports the inherited count. *)
Definition set_cred_uids (t : IdTriple) (c : Creds) : Creds :=
  mkCreds (id_real t) (id_eff t) (id_saved t) (cr_gid c) (cr_egid c)
          (cr_sgid c) (cr_groups c).
Definition set_cred_gids (t : IdTriple) (c : Creds) : Creds :=
  mkCreds (cr_uid c) (cr_euid c) (cr_suid c) (id_real t) (id_eff t)
          (id_saved t) (cr_groups c).

(** [getuid] (174), [geteuid] (175), [getgid] (176), [getegid] (177):
    return one id.  TOTAL — no argument is read, no allocation happens,
    no check can fail, and the value is a value even when it is large:
    [from_kuid_munged] answers an unmappable id with [overflowuid]
    (65534), never with an errno (Linux v6.18.46, kernel/sys.c,
    [SYSCALL_DEFINE0(getuid)] and its three siblings;
    kernel/user_namespace.c, [from_kuid_munged] / [from_kgid_munged]).
    In the init user namespace the mapping is the identity, so the model
    returns the stored id unchanged, and [Run.valid_id]'s 32-bit bound
    keeps it clear of the [State.addr_is_error_b] error band.

    The ANSWER is the run's, not a constant: [State.ProcInput] carries
    the launching uid and gid, so a program is analysed under every user
    it could have been launched as rather than under one the model
    invented.  A constant would have been worse than no model at all —
    it would REJECT the truthful answer of any kernel not running the
    process as root.

    [getppid] (173) is NOT one of these readers, although it sits beside
    them in kernel/sys.c.  The parent's pid is a function of no input and
    of no model state, and it CHANGES under the kernel -- when the parent
    exits, [find_new_reaper] reparents the process to a subreaper or to
    the namespace's init -- at a moment the model cannot predict.  So the
    treatment [Kernel.Fork.set_tid_address_spec] gives the tid, one
    choice recorded once, does not transfer.  [getppid_spec] above makes
    a fresh choice on every call instead, and says why a program can be
    proved to tolerate that. *)
Definition getid_spec (sel : Creds -> word) : Sys SyscallEffect :=
  m <- get_model ;;
  ret_only (sel (m_creds m)).

(** The environment failures the id setters can suffer, as opposed to
    the answers their arguments and credentials determine.

    -ENOMEM: [prepare_creds] allocates the new credential record and can
    fail.  Every one of the four id setters reaches it.

    -EAGAIN: [set_user] swaps in the per-uid [struct user_struct] and
    [set_cred_ucounts] the per-uid [struct ucounts].  [set_user] is
    CALLED only when the call changes the real uid; [set_cred_ucounts]
    is called unconditionally but returns 0 through a fast path unless
    [new->uid] differs from the ucounts already held, so it too can
    ALLOCATE, and therefore fail, only then.  Neither exists on the
    group side.  So the flag: [-EAGAIN] is admissible exactly on a
    user-id setter that moves the real uid, and admitting it more widely
    would let a target answer -EAGAIN to a call no kernel can fail
    (Linux v6.18.46, kernel/sys.c, [set_user]; kernel/cred.c,
    [set_cred_ucounts]).

    NOT an -EAGAIN source, contrary to the pre-v5.17 shape: RLIMIT_NPROC.
    The check left [set_user] in v5.17 for [flag_nproc_exceeded], which
    returns [void] and defers enforcement to the next [execve], so the
    limit is invisible to every syscall modeled here. *)
Definition setid_errnos (real_uid_changes : bool) : list Z :=
  if real_uid_changes then [ENOMEM; EAGAIN] else [ENOMEM].

(** [setuid uid] (146) and [setgid gid] (144), one spec over
    [IdTriple]; [user] says which of the two, and reaches only
    [setid_errnos].  (Linux v6.18.46, kernel/sys.c,
    [SYSCALL_DEFINE1(setuid)] / [__sys_setuid] and
    [SYSCALL_DEFINE1(setgid)] / [__sys_setgid], byte-identical across the
    range above.)

    In kernel order:

    - [(uid_t)-1] is rejected -EINVAL before anything is allocated, so
      that call can never answer -ENOMEM.
    - [prepare_creds] runs NEXT, before the capability test — so a call
      that would be refused -EPERM may instead answer -ENOMEM.  That
      ordering is the opposite of [setresuid]'s, which tests permission
      first; it is not a detail, it is observable.
    - PRIVILEGED: real, effective and saved all become the argument.
      This is the transition that drops root for good — it takes all
      three ids away from 0, so [cap_emulate_setxuid] clears
      [cap_permitted], and no later call can come back.  It is also why a
      privilege-drop sequence must set the GROUP ids first: after this
      call [State.creds_privileged] is false, and [setgid] to a fresh gid
      would be refused.
    - UNPRIVILEGED: the argument must already be the real or the saved
      id, and only the effective id moves.  Anything else is -EPERM.

    The kernel also assigns [fsuid]/[fsgid] alongside the effective id on
    every branch.  The model does not carry them: they differ from the
    effective ids only through [setfsuid]/[setfsgid], which are
    unmodeled, and nothing the model can observe consults them
    ([State.Creds]).

    The state change is ATOMIC, as the kernel's is: it builds a whole new
    [struct cred] and either commits it or aborts it, so no failing call
    leaves half its effect behind.  Here every failing branch returns
    without reaching [set_creds]. *)
Definition setid_spec (get : Creds -> IdTriple) (put : IdTriple -> Creds -> Creds)
    (user : bool) (v : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let c := m_creds m in
  let t := get c in
  if bv_eqb v ID_MINUS_ONE then err_ret EINVAL
  else if creds_privileged c then
    alt (e <- errno_from (setid_errnos (andb user (negb (bv_eqb v (id_real t))))) ;; err_ret e)
        (set_creds (put (mkIdTriple v v v) c) ;; ret_only (Z_to_bv 64 0))
  else if orb (bv_eqb v (id_real t)) (bv_eqb v (id_saved t)) then
    alt (e <- errno_from (setid_errnos false) ;; err_ret e)
        (set_creds (put (mkIdTriple (id_real t) v (id_saved t)) c) ;; ret_only (Z_to_bv 64 0))
  else
    alt (e <- errno_from (setid_errnos false) ;; err_ret e) (err_ret EPERM).

(** [setresuid ruid euid suid] (147) and [setresgid] (149), again one
    spec over [IdTriple].  (Linux v6.18.46, kernel/sys.c,
    [SYSCALL_DEFINE3(setresuid)] / [__sys_setresuid] and
    [SYSCALL_DEFINE3(setresgid)] / [__sys_setresgid], byte-identical
    across the range above.  There is no [flags] parameter on either,
    there or on current mainline.)

    -EINVAL IS UNREACHABLE.  The kernel tests
    [(ruid != (uid_t)-1) && !uid_valid(make_kuid(ns, ruid))], and in the
    init user namespace the second conjunct is exactly
    [ruid == (uid_t)-1] — the negation of the first.  So the model omits
    the arm rather than writing an arm nothing can reach.

    The rest, in kernel order:

    - [(uid_t)-1] in any position means LEAVE THAT ID ALONE.  It is read
      as the raw argument, before and independently of any validity
      question, which is why the same bit pattern is a rejected VALUE for
      [setuid] and a no-op REQUEST here.
    - The NO-OP fast path returns 0 before [prepare_creds], so a call
      that asks for nothing is total: it can answer neither -ENOMEM nor
      -EAGAIN.  The kernel's condition on the effective id is
      [keuid == old->euid && keuid == old->fsuid]; the model's [fsuid]
      always equals its [euid] ([setid_spec]'s note), so the second
      conjunct is implied and the model tests the first.
    - PERMISSION: each id the call would install must ALREADY be one of
      the three current ids — real, effective or saved — in any position.
      If any is new, the caller must be privileged, else -EPERM.  This
      test runs BEFORE [prepare_creds], so unlike [setuid] a refused call
      here never answers -ENOMEM.  That ordering is why the two specs
      differ: commit 659c0ce1cb9e ("kernel/sys.c: fix and improve control
      flow in __sys_setres[ug]id()", v6.3) hoisted the capability check
      above [prepare_creds] here, and left [__sys_setuid] alone.
    - Otherwise every named id is installed.  Unlike [setuid], the saved
      id is NEVER touched implicitly: it changes if and only if the third
      argument names it.  That is what makes
      [setresgid(-1, -1, g)] — dropbear's way of parking the utmp group
      in the saved gid, to be picked up later with [setegid] — do exactly
      that and nothing else.
    - [seteuid]/[setegid] are not syscalls: musl compiles them to
      [setresuid(-1, e, -1)] and [setresgid(-1, e, -1)]
      (musl 1.2.5, src/unistd/seteuid.c, src/unistd/setegid.c), so they
      are modeled here and nowhere else. *)
Definition setresid_spec (get : Creds -> IdTriple) (put : IdTriple -> Creds -> Creds)
    (user : bool) (r e s : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let c := m_creds m in
  let t := get c in
  let pick (a : word) (cur : word) :=
    if bv_eqb a ID_MINUS_ONE then cur else a in
  let nr := pick r (id_real t) in
  let ne := pick e (id_eff t) in
  let ns := pick s (id_saved t) in
  if andb (andb (bv_eqb nr (id_real t)) (bv_eqb ne (id_eff t)))
          (bv_eqb ns (id_saved t)) then
    ret_only (Z_to_bv 64 0)                    (* no-op: 0, before any allocation *)
  else
    let is_old (x : word) :=
      orb (orb (bv_eqb x (id_real t)) (bv_eqb x (id_eff t))) (bv_eqb x (id_saved t)) in
    if andb (negb (andb (andb (is_old nr) (is_old ne)) (is_old ns)))
            (negb (creds_privileged c)) then
      err_ret EPERM                            (* before [prepare_creds] since 659c0ce1cb9e: no -ENOMEM here *)
    else
      alt (en <- errno_from (setid_errnos (andb user (negb (bv_eqb nr (id_real t))))) ;; err_ret en)
          (set_creds (put (mkIdTriple nr ne ns) c) ;; ret_only (Z_to_bv 64 0)).

(* ---- uname (160) -------------------------------------------------------- *)

(** The six members of [struct new_utsname], as byte ranges of the 390
    bytes the syscall copies out.  [uts_field k bs] is member [k], 65
    bytes wide, in declaration order: 0 [sysname], 1 [nodename],
    2 [release], 3 [version], 4 [machine], 5 [domainname]
    (include/uapi/linux/utsname.h, [struct new_utsname], Linux v6.18.46,
    commit 1f99e9ab748f). *)
Definition uts_field (k : nat) (bs : list byte) : list byte :=
  firstn 65 (skipn (k * 65) bs).

Definition uts_nul : byte := Z_to_bv 8 0.

(** A member built from its C string literal: the characters, then NUL
    to the full 65 bytes.  That is what a [char field[65]] initialized
    from a string literal holds -- C zero-fills the remainder -- and it
    is how [init_uts_ns] sets all six (init/version-timestamp.c,
    [init_uts_ns], Linux v6.18.46, commit 1f99e9ab748f). *)
Definition uts_literal (cs : list Z) : list byte :=
  map (Z_to_bv 8) cs ++ repeat uts_nul (65 - length cs).

Definition uts_eqb (l1 l2 : list byte) : bool :=
  (Nat.eqb (length l1) (length l2)
   && forallb (fun p => bv_eqb (fst p) (snd p)) (combine l1 l2))%bool.

(** [UTS_SYSNAME], "Linux" (include/linux/uts.h,
    [#define UTS_SYSNAME "Linux"], Linux v6.18.46, commit 1f99e9ab748f).
    The definition is guarded by [#ifndef] and no riscv header overrides
    it, so a riscv64 build has this string; nothing writes [sysname]
    afterwards -- [sethostname] (161) writes [nodename] and
    [setdomainname] (162) writes [domainname], and kernel/sys.c defines
    no setter for any other member. *)
Definition uts_sysname_chars : list Z := [76; 105; 110; 117; 120]%Z.

(** [UTS_MACHINE], "riscv64" (arch/riscv/Makefile,
    [UTS_MACHINE := riscv64] on the 64-bit branch of its
    [ifeq ($(CONFIG_ARCH_RV64I),y)], Linux v6.18.46, commit
    1f99e9ab748f).

    [override_architecture] IS COMPILED IN ON THIS ARCHITECTURE and does
    not fire for the process this model describes.  riscv defines
    [COMPAT_UTS_MACHINE "riscv32\0\0"] (arch/riscv/include/asm/compat.h),
    so kernel/sys.c takes the [#ifdef COMPAT_UTS_MACHINE] arm and
    [SYSCALL_DEFINE1(newuname)] rewrites [machine] whenever
    [personality(current->personality) == PER_LINUX32].  This model runs
    an rv64 ELF started by an ordinary [execve], which
    [SET_PERSONALITY] leaves at [PER_LINUX]; the personality a parent may
    have set with [personality(2)] (135 is not that call, and 92 has no
    arm) is outside the modeled surface, and the [PER_LINUX32] value
    would in any case belong to a 32-bit image this model does not
    load. *)
Definition uts_machine_chars : list Z := [114; 105; 115; 99; 118; 54; 52]%Z.

(** THE ENVELOPE OF UTS NAMES v6.18.46 CAN COPY OUT, as a predicate on
    the 390 bytes.  Everything the KERNEL SOURCE settles is pinned;
    everything the BUILD or the boot settles is left free, and the free
    members carry the one invariant the kernel does maintain.

    PINNED: [sysname] and [machine], each exactly its literal zero-filled
    to 65 bytes, for the reasons given above their character lists.

    FREE, with a terminator: [nodename], [release], [version] and
    [domainname].  Their values are not in the kernel tree —
    [UTS_RELEASE] and [UTS_VERSION] come from include/generated/, and
    [UTS_NODENAME] is [CONFIG_DEFAULT_HOSTNAME] which the [hostname=]
    boot parameter and [sethostname] (161) then overwrite — so pinning
    any of them would be a claim about a build rather than about Linux.
    What IS true of all four at v6.18.46 is that BYTE 64 OF EACH IS NUL,
    which is what makes each member a C string of at most 64 characters:

    - the four are zero-filled by [init_uts_ns]'s initializer;
    - [early_hostname] uses [strscpy] into the 65-byte buffer, which
      terminates (init/version.c);
    - [sethostname] and [setdomainname] refuse a [len] above
      [Uapi.NEW_UTS_LEN] and then
      [memset(u->field + len, 0, sizeof(u->field) - len)], so at least
      the last byte is cleared (kernel/sys.c);
    - [override_release], the [UNAME26] personality rewrite, writes
      [copy + 1 <= 65] bytes out of a [char buf[65] = { 0 }] filled by
      [scnprintf], which never writes past index 64 (kernel/sys.c).

    NOTHING STRONGER IS CLAIMED ABOUT THE FREE MEMBERS, and both weakenings
    are real rather than defensive:

    - [sethostname] copies [len] bytes VERBATIM, embedded NULs included,
      so a member may hold bytes after its terminator that a
      zero-filled member would not.
    - [override_release] writes only a PREFIX over an existing
      [release], so under the [UNAME26] personality the tail of the
      previous release survives past the new terminator.  A
      "NUL-padded" predicate would reject a real kernel's answer on
      that path, which is the mistake this one is written to avoid. *)
Definition utsname_wf (bs : list byte) : bool :=
  (Nat.eqb (length bs) 390
   && uts_eqb (uts_field 0 bs) (uts_literal uts_sysname_chars)
   && uts_eqb (uts_field 4 bs) (uts_literal uts_machine_chars)
   && bv_eqb (nth 64 (uts_field 1 bs) uts_nul) uts_nul
   && bv_eqb (nth 64 (uts_field 2 bs) uts_nul) uts_nul
   && bv_eqb (nth 64 (uts_field 3 bs) uts_nul) uts_nul
   && bv_eqb (nth 64 (uts_field 5 bs) uts_nul) uts_nul)%bool.

(** [uname name] — syscall 160, which riscv64 routes to [sys_newuname]
    (include/uapi/asm-generic/unistd.h, [__NR_uname 160],
    [__SYSCALL(__NR_uname, sys_newuname)], Linux v6.18.46, commit
    1f99e9ab748f).  The other two [uname] flavours are not reachable
    here: [SYSCALL_DEFINE1(uname, ...)] over a [struct old_utsname] and
    [SYSCALL_DEFINE1(olduname, ...)] are behind
    [__ARCH_WANT_SYS_OLD_UNAME] / [__ARCH_WANT_SYS_OLDUMOUNT] in
    kernel/sys.c, and asm-generic's unistd.h — the table riscv uses —
    defines neither.

    THE WHOLE KERNEL FUNCTION, in its own order (Linux v6.18.46, commit
    1f99e9ab748f, kernel/sys.c, [SYSCALL_DEFINE1(newuname)]):

      down_read(&uts_sem);
      memcpy(&tmp, utsname(), sizeof(tmp));
      up_read(&uts_sem);
      if (copy_to_user(name, &tmp, sizeof(tmp)))       return -EFAULT;
      if (override_release(name->release, sizeof(name->release)))
                                                       return -EFAULT;
      if (override_architecture(name))                 return -EFAULT;
      return 0;

    There is no argument to validate, no flag word, and no errno but
    -EFAULT: the syscall takes one pointer and either fills it or does
    not.  So the envelope is a question about that pointer and about
    WHICH utsname, and nothing else.

    THE POINTER, in the three bands every buffer in this file is judged
    in:

    - [access_ok] REFUSES the 390-byte range: -EFAULT.  That is
      [copy_to_user]'s own gate ([_copy_to_user], include/linux/uaccess.h,
      which returns the untouched byte count when [access_ok] fails), and
      it fires before a single byte moves, so the answer is exact.

      IT IS ASKED FIRST, BEFORE THE WALK, and that order is load-bearing
      rather than cosmetic: [State.read_bytes_map] advances with WRAPPING
      word arithmetic while [State.access_okb] subtracts in [Z], so a
      [name] near 2^64 whose 390 bytes wrap round onto mapped low
      addresses reads as "wholly writable" to the walk and is refused by
      Linux.  Asking the walk first is a known defect, and both
      [prlimit64_spec] arms have it; this arm is written the way
      [Net.Socket.socketpair_spec] and [Fs.Pipe.pipe2_spec] are,
      and [Checks.Cases.Kernel.Sys]'s [uname_wrap_] group pins both
      directions.
    - [access_ok] admits the range and it is WHOLLY WRITABLE: the modeled
      path.  390 bytes land at [name] and the call returns 0.
    - [access_ok] admits it and it is NOT wholly writable: [unmodeled].
      [copy_to_user] copies until it faults, so a struct straddling into
      an unmapped page COMMITS a prefix and then answers -EFAULT — the
      half-written shape [Time.gettimeofday_spec] declines
      for the same reason, and this one is worse, because the prefix may
      end anywhere in 390 bytes rather than at one of two fields.

    WHICH UTSNAME: the environment's, recorded once.  On the first
    [uname] of a run the model CHOOSES any buffer [utsname_wf] admits and
    pins it in [State.procst_utsname]; every later [uname] must deliver
    exactly those bytes.  That pin is the whole reason this spec is not a
    per-call [choose]: two calls that disagreed about the running kernel
    would be a trace no Linux machine produces.  [State.procst_utsname]
    argues the mechanism and the note above [State.Model] compares it
    against the two alternatives.

    WHAT IS NOT MODELED, and it is one thing rather than a list: a
    program that DEPENDS ON THE CONTENT of [nodename], [release],
    [version] or [domainname] is answered, but answered
    nondeterministically — the model will not tell it which kernel it is
    on, because the kernel source does not say.  A binary that branches
    on the release string therefore has more than one admissible
    execution and its equivalence has to hold for all of them; a binary
    that copies the release into a diagnostic buffer, which is what the
    callers this arm exists for do, does not care. *)
Definition uname_spec (name : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (access_okb name NEW_UTSNAME_SIZE) then err_ret EFAULT
  else
    match read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE) with
    | None => unmodeled       (* a partial [copy_to_user] then -EFAULT *)
    | Some _ =>
        match m_utsname m with
        | Some bs => pure (mkEffect (Z_to_bv 64 0) [(name, bs)] [])
        | None =>
            bs <- choose (fun bs : list byte => utsname_wf bs = true) ;;
            set_utsname bs ;;
            pure (mkEffect (Z_to_bv 64 0) [(name, bs)] [])
        end
    end.

(* ================================================================ prctl *)

(** THE OPTIONS THIS MODEL ANSWERS, as a closed list rather than as the
    shape of a [match].  [prctl] is a multiplexer, so "the modeled
    surface" stops being a set of syscall NUMBERS at the moment it gains
    an arm: what is modeled is a set of (number, option) pairs, and
    nothing in [Specs.modeled_sysnos] can say which.  This list is where
    that set is written down, [prctl_spec]'s first test is membership
    in it, and [Checks.ProcessCreation.prctl_modeled_options_are] pins
    it exactly, so widening the multiplexer is a change a proof reports
    rather than one a reader has to notice.  The obligation that pin
    carries is named there and is not restated here. *)
Definition prctl_modeled_options : list Z :=
  [PR_CAPBSET_READ; PR_SET_PDEATHSIG; PR_SET_DUMPABLE; PR_SET_NO_NEW_PRIVS].

(** [prctl(option, arg2, arg3, arg4, arg5)] — syscall 167, answered for
    the four options of [prctl_modeled_options] and for nothing else.
    [PR_CAPBSET_READ] is answered by the capability LSM hook; the other
    three by kernel/sys.c's own [switch].  The paragraphs below take
    them in that order.

    security/commoncap.c [cap_task_prctl], read at v6.18.44; identical at v6.18.46.
    security/security.c [security_task_prctl], read at v6.18.44; identical at v6.18.46.
    kernel/sys.c [SYSCALL_DEFINE5(prctl)], read at v6.18.44; identical at v6.18.46.
    include/linux/signal.h [valid_signal], read at v6.18.44; identical at v6.18.46.
    include/linux/sched/coredump.h [SUID_DUMP_DISABLE], [SUID_DUMP_USER], read at v6.18.44; identical at v6.18.46.
    kernel/cred.c [commit_creds], read at v6.18.44; identical at v6.18.46.

    PR_CAPBSET_READ: WHERE THE ANSWER COMES FROM, AND WHY IT IS NOT
    kernel/sys.c.
    [SYSCALL_DEFINE5(prctl)] opens with

        error = security_task_prctl(option, arg2, arg3, arg4, arg5);
        if (error != -ENOSYS)
                return error;

    so the LSM hook runs BEFORE the syscall's own [switch] and can
    answer outright (Linux v6.18.46, commit 1f99e9ab748f, kernel/sys.c,
    [SYSCALL_DEFINE5(prctl)]).  [PR_CAPBSET_READ] is answered there:
    capability's hook is [cap_task_prctl] (security/commoncap.c), whose
    first arm is

        case PR_CAPBSET_READ:
                if (!cap_valid(arg2))
                        return -EINVAL;
                return !!cap_raised(old->cap_bset, arg2);

    with [old = current_cred()].  So this option never reaches
    kernel/sys.c's [switch] at all, and the file this spec answers to is
    security/commoncap.c as much as kernel/sys.c.  It lives here
    anyway, beside the other 167 arms it shares a dispatcher entry with;
    [Specs.v]'s map is what says where a spec lives, and splitting one
    syscall's options across two files would make that map lie about
    which file a number is answered in.

    WHICH HOOK ANSWERS IS A PRECONDITION, and it is this model's
    standing one rather than a new assumption.  [security_task_prctl]
    walks EVERY registered [task_prctl] hook and keeps the first
    non-[-ENOSYS] answer, breaking out as soon as one is nonzero
    (security/security.c).  Capability's is registered by
    [capability_init] and is not optional -- commoncap is the
    implementation of capabilities, not an LSM a build may leave out --
    so the arm above always runs, and its 1 or its -EINVAL is nonzero
    and ends the walk.  What a SECOND hook would do is what this model
    already declines to describe anywhere: [prlimit64]'s note names the
    same position for [security_task_setrlimit], and [Mm.Mmap]'s for
    [security_mmap_addr].  A kernel running an LSM that also claims this
    option is outside the model, exactly as one whose AppArmor refuses
    an unchanged rlimit is.

    ORDER IS BEHAVIOR, and this one has exactly two steps.
    [cap_task_prctl] tests [cap_valid(arg2)] and nothing else before
    reading the bounding set; [arg3], [arg4] and [arg5] are not read on
    this arm at all — unlike [PR_MCE_KILL_GET], which rejects a nonzero
    one — so a caller that leaves garbage in a2..a4 gets the same
    answer, and this arm reads only the two registers the kernel reads.

    [cap_valid] IS AN UNSIGNED TEST ON THE FULL REGISTER.  It is
    [((x) >= 0 && (x) <= CAP_LAST_CAP)] (include/uapi/linux/capability.h)
    and [cap_task_prctl] applies it to an [unsigned long arg2], so the
    left half is vacuous and the right is a 64-bit unsigned comparison:
    no truncation, no sign extension, and [prctl(PR_CAPBSET_READ, 2^32)]
    is -EINVAL rather than the answer for capability 0.  That is the
    OPPOSITE of the [option] beside it, which is an [int] in the
    [SYSCALL_DEFINE5] prototype and therefore reaches the kernel already
    narrowed: riscv's own [__SYSCALL_DEFINEx] applies
    [__MAP(x,__SC_CAST,__VA_ARGS__)] to the registers
    [SC_RISCV_REGS_TO_ARGS] unpacked
    (arch/riscv/include/asm/syscall_wrapper.h), and [__SC_CAST] is
    [(__force t) a] (include/linux/syscalls.h).  [Sys.SyscallTable]
    applies [Syscall.int32] to it in the arm, exactly as it does for
    [setsockopt]'s [level].  The asymmetry is real:
    [prctl(2^32 | PR_CAPBSET_READ, 0)] answers 1 while
    [prctl(PR_CAPBSET_READ, 2^32)] answers -EINVAL.

    WHY THE ANSWER IS 1 RATHER THAN A CHOICE.  [cap_raised(old->cap_bset,
    arg2)] reads a bit of the caller's capability bounding set, which is
    inherited across fork and exec and which this model does not carry.
    It does not have to: this model already ASSUMES an UNNARROWED
    bounding set.  The
    assumption is [State.creds_privileged]'s — the note above that
    definition lists "an UNNARROWED capability bounding set" among the
    conditions under which answering [ns_capable_setid(CAP_SETUID)] with
    the effective uid is EXACT, and says why that one is easy to miss:
    [handle_privileged_root] grants legacy root
    [cap_combine(old->cap_bset, old->cap_inheritable)]
    (security/commoncap.c), so an ancestor's
    [prctl(PR_CAPBSET_DROP, CAP_SETUID)] leaves a euid-0 process with no
    CAP_SETUID and breaks the biconditional [setuid] rests on.  Under
    that standing assumption [cap_bset] is [CAP_FULL_SET], every valid
    capability is raised in it, and 1 is not one admissible answer among
    several — it is the answer.

    A NONDETERMINISTIC BOUNDING SET WOULD CONTRADICT THE REST OF THE
    MODEL, which is the argument for the constant rather than
    convenience.  Had this arm chosen its answer — an [alt], or a
    [choose] pinned at first observation the way [m_rlimit_core] is —
    the model would admit a run in which
    [prctl(PR_CAPBSET_READ, CAP_SETUID)] answers 0 while [setuid_spec]
    is still deciding privilege by [creds_privileged], i.e. still
    asserting that a euid-0 caller HAS CAP_SETUID.  Two arms of one
    model would then disagree about one kernel fact.  Answering 1 is
    what keeps them consistent, and it does more than that: it makes the
    assumption OBSERVABLE.  In a narrowed-bounds environment (a
    container's default capability set, say)
    [Checks.ExecutableSpecs.check_syscall] REFUSES such a kernel's
    truthful 0, so the environment shows up as a rejection rather than
    as a silently wrong [setuid].

    -EINVAL IS A VERSION CLAIM, and the only one here.  [CAP_LAST_CAP]
    is 40 at the cited commit and has been since v5.9; a kernel that
    defines a 41st capability answers 1 where this spec answers -EINVAL.
    See [Uapi.CAP_LAST_CAP].  The boundary is worth pinning rather than
    declining because it is what programs READ: libcap's [cap_max_bits]
    binary-searches it from a constructor.

    THE THREE OPTIONS kernel/sys.c ANSWERS: [PR_SET_PDEATHSIG],
    [PR_SET_DUMPABLE], [PR_SET_NO_NEW_PRIVS].  [cap_task_prctl] has no
    case for any of them and returns -ENOSYS from its [default:], which
    is [LSM_RET_DEFAULT(task_prctl)], so [security_task_prctl] keeps
    -ENOSYS and [SYSCALL_DEFINE5(prctl)] goes on to its own [switch].
    That is the capability-only LSM the credentials section above names
    as a standing assumption; a second LSM that claims one of these
    options is outside the model, as for [PR_CAPBSET_READ] above.  The
    three cases, quoted:

        case PR_SET_PDEATHSIG:
                if (!valid_signal(arg2)) { error = -EINVAL; break; }
                ... me->pdeath_signal = arg2; ...
                break;
        case PR_SET_DUMPABLE:
                if (arg2 != SUID_DUMP_DISABLE && arg2 != SUID_DUMP_USER) {
                        error = -EINVAL; break; }
                set_dumpable(me->mm, arg2);
                break;
        case PR_SET_NO_NEW_PRIVS:
                if (arg2 != 1 || arg3 || arg4 || arg5)
                        return -EINVAL;
                task_set_no_new_privs(current);
                break;

    and the function ends [return error;] with [error = 0] set before
    the [switch].  So each answers 0 or -EINVAL, decided by its arguments
    alone, and has no other failure: none allocates, and none can be
    refused by privilege.

    - [valid_signal(arg2)] is [arg2 <= _NSIG] on an [unsigned long],
      [_NSIG] being 64 on riscv64: 0 to 64 is 0 (0 clears the parent-death
      signal), anything above, including every value with a high bit
      set, is -EINVAL.  The full register, as for [cap_valid].
    - [SUID_DUMP_DISABLE] is 0 and [SUID_DUMP_USER] is 1, so the
      dumpable flag answers 0 for [arg2] in {0, 1} and -EINVAL for any
      other value, again over the full register.  2
      ([SUID_DUMP_ROOT]) is refused here; only [suid_dumpable] sets it.
    - [PR_SET_NO_NEW_PRIVS] is the one option that reads [arg3], [arg4]
      and [arg5] -- a2, a3 and a4 -- and it reads them as whole
      registers: 0 for [arg2 = 1] with the other three 0, -EINVAL for
      anything else.  That is why this spec reads the input, and only
      on that branch; its signature still takes [arg2] alone, as the
      dispatcher has always passed it.

    THE MODEL STORES NOTHING FOR THEM, and that is sound because no
    modeled call reads the bit, the signal or the flag.
    - The no-new-privs bit is read by [PR_GET_NO_NEW_PRIVS] (39), by
      seccomp ([PR_SET_SECCOMP] (22) and [seccomp] (277)) and by
      [execve] (fs/exec.c): 39 and 22 are outside
      [prctl_modeled_options], and 277 and 221 have no arm.
    - The parent-death signal is read by [PR_GET_PDEATHSIG] (2), which
      is declined, and is SENT by [forget_original_parent] when the
      parent exits.  That is a signal from outside the process, which
      the environment this model quantifies over does not deliver (the
      premise [Signal.rt_sigaction_spec]'s header states; SCOPE.md
      lists it among the assumptions the model does not check).
    - The dumpable flag is read by [PR_GET_DUMPABLE] (3), declined; by
      core dumps, which this model has none of ([prlimit64_spec]'s
      RLIMIT_CORE note); by ptrace access checks, and the model admits
      no tracer; and by procfs ownership ([task_dump_owner],
      fs/proc/base.c), to which no modeled answer is pinned.
    A statement that needs one of them SET reads it from the call log
    ([Run.star_calls]: [sc_no = 167], [sc_args], [sc_ret = 0]); what the
    kernel then does with it is a kernel-side obligation.  Such a
    statement must take the LAST such call that follows the last
    credential change: [commit_creds] (kernel/cred.c) clears
    [pdeath_signal] and resets the dumpable flag to [suid_dumpable]
    whenever a call moves the effective or filesystem ids or narrows
    the capability sets, so a [setuid] after [prctl(PR_SET_DUMPABLE, 1)]
    undoes it.  The no-new-privs bit has no such reset: nothing clears
    it.

    EVERY OTHER OPTION IS [unmodeled], and one of them is load-bearing.
    [PR_SET_TAGGED_ADDR_CTRL] (55) is one of the two callers of riscv's
    [set_tagged_addr_ctrl] (arch/riscv/kernel/process.c), and declining
    it is half of why [State.access_okb] is exact — the other half being
    [ptrace] (117), which has no arm at all.  None of the four answered
    options reaches [set_tagged_addr_ctrl]: its only callers are that
    option's [SET_TAGGED_ADDR_CTRL] and riscv's ptrace regset (read at
    v6.18.44).  That argument rests
    on [prctl_modeled_options] being a closed list, not on the NUMBER
    167, which is why that list is a definition with a pin on it and
    not a [match] a reader has to read.  See
    [Checks.ProcessCreation.prctl_tagged_addr_ctrl_unmodeled].

    WHAT THE DECLINE COSTS is [prlimit64]'s cost, in the same currency:
    a source that calls [prctl] with any other option cannot be
    certified by [Equivalence.strong_equiv], because [modeled] is an
    obligation to prove rather than one the source is let off. *)
Definition prctl_spec (option_ arg2 : word) : Sys SyscallEffect :=
  if negb (existsb (Z.eqb (bv_unsigned option_)) prctl_modeled_options)
  then unmodeled
  else if Z.eqb (bv_unsigned option_) PR_CAPBSET_READ then
    (if (CAP_LAST_CAP <? bv_unsigned arg2)%Z then err_ret EINVAL
     else ret_only (Z_to_bv 64 1))
  else if Z.eqb (bv_unsigned option_) PR_SET_PDEATHSIG then
    (if (64 <? bv_unsigned arg2)%Z then err_ret EINVAL   (* !valid_signal *)
     else ret_only (Z_to_bv 64 0))
  else if Z.eqb (bv_unsigned option_) PR_SET_DUMPABLE then
    (if (1 <? bv_unsigned arg2)%Z then err_ret EINVAL    (* not 0 or 1 *)
     else ret_only (Z_to_bv 64 0))
  else if Z.eqb (bv_unsigned option_) PR_SET_NO_NEW_PRIVS then
    i <- input ;;
    (if (bv_eqb arg2 (Z_to_bv 64 1) && w_is0 (in_arg i 2)
         && w_is0 (in_arg i 3) && w_is0 (in_arg i 4))%bool
     then ret_only (Z_to_bv 64 0) else err_ret EINVAL)
  else unmodeled.     (* unreachable: the list has no fifth member *)
