(** * LinuxProcessSem.Sys.Kernel.Exit — exit (93), exit_group (94), wait4 (260)

    This file answers to Linux [kernel/exit.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export Syscall Uapi.
Open Scope bv_scope.
Open Scope sys_scope.

(** Halt the run.  The observed exit code is the low byte of the status,
    as a waiting parent sees it.  The returned effect is never applied
    (Run.v ends the trace with an [ExitEv] instead). *)
Definition exit_spec (code : word) : Sys SyscallEffect :=
  set_halted (bv_and code (Z_to_bv 64 255)) ;; ret_only (Z_to_bv 64 0).


(* =========================================================================
   Process reaping: wait4 (260) — A CALLER WITH NO CHILDREN
   ========================================================================= *)

(** [upid = -1] after the [int] truncation [Syscall.pid32] applies:
    "reap any child".  It is the ONLY selector modeled — see
    [wait4_spec]. *)
Definition WAIT_ANY32 : Z := (2 ^ 32 - 1)%Z.

(** [wait4 upid stat_addr options rusage] (260) — the whole call, for
    the only caller it ANSWERS: one with no children.  Not the only
    caller the model can have — [clone] creates one — the other is
    declined, at the [State.m_has_children] gate in the body below.

    Kernel side read at v6.12.  [kernel_wait4] and
    [SYSCALL_DEFINE4(wait4, ...)] (kernel/exit.c) are byte-identical IN
    MAINLINE from v4.13 — where Al Viro's 359566faefa8,
    "kernel_wait4()/kernel_waitid(): delay copying status to userland",
    turned [wo_stat] from an [int __user *] into an [int] and put the
    copy-out behind the [ret > 0] guard this spec rests on, so there is
    no earlier tag for the claim to reach — through v7.2, the newest
    release.  Spot-checked against the HEADS of linux-6.6.y and
    linux-6.12.y, which do not diverge; that is a claim about those two
    heads and not about every point release along them.  Every claim
    below about those two functions holds over that window.

    ** THE ANSWER IS -ECHILD, AND IT IS THE ONLY ANSWER

    The model is single-process, and STRUCTURALLY so: [Run.config]
    holds one [machine_state] and one [Model], and no [Run.sstep] rule
    produces a second of either.  THAT IS NOT THE SAME AS THE CALLER
    HAVING NO CHILD.  [clone] (220) and [clone3] (435) are modeled, and
    the success branches of [Kernel.Fork.clone_resolve] and
    [Kernel.Fork.clone_ns_resolve] are exactly the
    operation that creates one: the child is never a configuration, but
    the FACT that the caller has one is, in [State.m_has_children].  So
    -ECHILD is carried by two things rather than by an absence.

    - THE CREATING ARMS RECORD THE CHILD.  [clone_resolve] and
      [clone_ns_resolve] end their pid branch with
      [modify with_children], and
      [Checks.ProcessCreation.clone_resolve_declines_or_sets_children]
      and [Checks.ProcessCreation.clone_ns_resolve_declines_or_sets_children]
      are the universal statements of it, over every model, every
      argument shape and every admissible resolution: an errno answer
      leaves the model untouched, and any other answer leaves
      [m_has_children] set.
    - THIS SPEC READS WHAT THAT ARM WROTE.  The gate in the body below
      answers -ECHILD only while the field is clear, and yields
      [unmodeled] otherwise.  A caller with a child gets no answer here
      rather than a wrong one.

    WHAT A NEW CHILD-CREATING ARM OWES is [State.with_children] on its
    post-state.  Nothing enforces that: an arm that creates a child and
    never applies the setter leaves this spec answering -ECHILD for a
    caller that has one, with the gate proved and the creating arm
    proved and no proof in the tree disturbed.  See
    [State.with_children]'s own note, which records the same obligation
    beside the setter.

    THE TRACEE LIST IS STILL CLOSED BY A DECLINE.  [ptrace] (117) is
    the only route to the caller's [current->ptraced] a modeled syscall
    could take, and it is outside the modeled surface —
    [Checks.ProcessCreation.ptrace_unmodeled] pins that against
    [Specs.syscall_spec] itself, as [execve_unmodeled] and
    [execveat_unmodeled] do for 221 and 281 — which are declined for
    reasons of their own rather than for this one, since Linux's
    [execve] adds to neither list.

    THAT IS ONLY HALF OF IT, AND THE OTHER HALF IS ASSUMED.  For the
    lists to be empty they must also have STARTED empty, and that is a
    property of how the process was launched rather than anything this
    model can see.  It is not a property of [execve]: at v6.18.46
    (commit 1f99e9ab748f) [fs/exec.c] never reads or writes
    [current->children] at all — [begin_new_exec] and [de_thread] kill
    sibling THREADS ([zap_other_threads], kernel/signal.c) and reap no
    child — and [exit_ptrace] (kernel/ptrace.c) is reached only through
    [forget_original_parent] from [exit_notify] on the EXIT path.  A
    launcher that forks a grandchild, or attaches
    a tracee, before exec'ing this image hands the caller something to
    wait for, and Linux then answers 0 or a pid where this spec
    answers -ECHILD.  That is a FALSE REJECTION, the expensive
    direction named below.  Nothing here binds the launcher: this is a
    premise of the run, and a known gap.  The argument
    for answering rather than declining: the only alternative is
    admitting all three resolutions on every call, which is a trace
    Linux cannot produce
    under EVERY launcher rather than an unusual one.  The ordinary
    [fork]-then-[execve] launch satisfies the assumption, but for a
    reason that is not exec: [copy_process] (kernel/fork.c) and
    [ptrace_init_task] (include/linux/ptrace.h) give a FRESH task
    empty lists, and a task that forks nothing before exec'ing keeps
    them.

    An empty pair of lists is exactly the state [do_wait] answers
    -ECHILD to.  [__do_wait]
    (kernel/exit.c, v6.7 and later; the same body is inline in [do_wait]
    before that — Jens Axboe's 06a101ca45b2, "exit: move core of
    do_wait() into helper", is a pure refactor) seeds
    [wo->notask_error] with -ECHILD.  With [upid = -1] the type is
    [PIDTYPE_MAX], so the [wo_type < PIDTYPE_MAX] early exit is NOT
    taken and the tasklist walk runs; [do_wait_thread] and
    [ptrace_do_wait] are list walks that return 0 on an empty list, so
    [wait_consider_task] — and with it [wait_task_zombie], the only
    thing that clears [notask_error] or fills [wo_stat] — never runs.
    Control reaches [notask:] with [notask_error] still -ECHILD, and
    the -ERESTARTSYS assignment there is guarded on [!retval], which
    -ECHILD fails; the WNOHANG conjunct beside it never has to be
    consulted.  [do_wait] then returns that value unchanged: its loop
    breaks on anything but -ERESTARTSYS, before [signal_pending] or
    [schedule] is reached, so there is no sleep and no interruption
    point.  WNOHANG's bare 0 is NOT admissible here — it is what
    [notask_error] cleared to 0 returns, and only a child that exists
    but has nothing to report clears it.

    So this is not an over-approximation.  It is the one answer Linux
    gives, and admitting any other — a pid, a bare 0 — would put a
    trace in the model that Linux cannot produce.

    ** [stat_addr] IS NOT READ, AND THAT IS BEHAVIOR

    No arm here looks at [stat_addr], not even to check that it is
    writable, and the spec takes it as an argument to say so.
    [kernel_wait4]'s copy-out is

      if (ret > 0 && stat_addr && put_user(wo.wo_stat, stat_addr))

    and C short-circuits: at [ret = -ECHILD] the pointer is never
    dereferenced.  An unmapped [stat_addr], one past
    [State.TASK_SIZE], one the model cannot see as writable — every
    one of them answers -ECHILD and faults on nothing.  A spec that
    judged the pointer would REJECT calls Linux answers, which costs
    the equivalence theorem rather than merely costing coverage.  The
    [rusage] copy in [SYSCALL_DEFINE4(wait4, ...)] is guarded the same
    way, on [err > 0], and is likewise never reached.

    ** The argument surface, which is narrow on purpose

    Every argument shape not named above declines and fails closed.
    Each of the three guards below is a call a real kernel ANSWERS, so
    declining is a choice rather than a consequence.

    - [upid] must be -1, "any child" ([type = PIDTYPE_MAX]).  It is
      also the only selector dropbear issues: both call sites are
      [waitpid(-1, ...)] (svr-chansession.c, svr-main.c), and musl's
      [waitpid] is [sys_wait4_cp(pid, status, options, 0)]
      (src/process/waitpid.c, v1.2.5 and v1.2.6).  The other shapes are
      not interchangeable with it.  THREE are different eligible-child
      rules — [upid > 0] one child, [upid == 0] the caller's process
      group, [upid < 0] the group [-upid] — and each takes the
      [wo_type < PIDTYPE_MAX] early exit whose verdict depends on
      whether the named pid or group EXISTS, which is state outside
      this model: a live process group with no children answers
      -ECHILD too, but through [pid_has_task], and a group that does
      not exist answers it through a NULL [wo_pid].  Answering them
      here would be right by coincidence rather than by argument.
      [upid == INT_MIN] is NOT a fourth rule: it returns -ESRCH before
      the selector chain is entered at all, because negating it would
      overflow.  That guard is not FIRST, though — the option mask is
      validated ahead of it, so [wait4(INT_MIN, _, <an unknown option
      bit>, _)] is -EINVAL rather than -ESRCH.  Both shapes decline
      here either way, but the reason differs, and a reader who took
      "before any selector" for "before anything" would have the wrong
      one.

    - [options] must be exactly [Uapi.WNOHANG].  Two separate reasons,
      and the first is the load-bearing one: WITHOUT WNOHANG THE CALL
      BLOCKS ONCE A CHILD EXISTS, and blocking is a wait-queue sleep
      this model has no vocabulary for.  [__do_wait] returns
      -ERESTARTSYS when a child exists but nothing is ready, and
      [do_wait] then sleeps until a signal or a child wakes it — so a
      blocking [wait4] can also come back -EINTR, an answer no arm
      here produces.  A childless caller would get -ECHILD from a
      blocking call as well, since the -ERESTARTSYS assignment is
      guarded on [!retval]; declining anyway keeps the guard on the
      ARGUMENT rather than on a coincidence of the state, so the spec
      does not have to be re-argued the day a child becomes
      expressible.

      NOTE WHICH FAILURE THE OTHER CHOICE WOULD BE.  Admitting the
      blocking call without admitting -EINTR would not leave a program
      unprovable, the way declining does; it would make the model
      REFUSE AN ANSWER LINUX REALLY GIVES, which makes
      [Equivalence.strong_equiv] FALSE for every binary that issues one
      rather than merely out of reach.  Declining costs coverage.  A
      false rejection costs the theorem.

      THE SECOND REASON, which would not have been enough on its own:
      an unknown option bit is -EINVAL, tested before anything else
      ([options & ~(WNOHANG|WUNTRACED|WCONTINUED|__WNOTHREAD|__WCLONE|
      __WALL)]), and the reportable-state bits WUNTRACED and WCONTINUED
      ask about a child's stop and continue.  Both dropbear call sites
      pass WNOHANG, so nothing is lost.

    - [rusage] must be NULL.  It is the literal 0 musl passes.  A
      non-NULL one is never written at -ECHILD, so answering it would
      be sound — but it asks for a [struct rusage] of accounting the
      model does not carry, and the day a reap becomes expressible the
      arm would have to be rewritten rather than extended.

    ** WHAT THIS COSTS, AND WHAT HAS TO CHANGE IF A CHILD APPEARS

    Nothing in the equivalence theorem is narrowed by answering
    -ECHILD: a spec that admits fewer resolutions admits fewer traces,
    and every trace it does admit is one Linux produces.  What the
    narrowness buys is priority 2 — the model contains no
    successful reap, which is a trace this process cannot have.

    The whole of this spec is CONDITIONAL ON THERE BEING NO CHILD.
    Half of that condition is discharged by the [State.m_has_children]
    gate in the body below — a caller the model gave a child is
    declined rather than answered — and half is a premise about the
    launcher, the lists having to have STARTED empty, as the second
    section above says, and nothing here binds the launcher.
    If a child ever becomes a configuration in this model,
    this spec is wrong rather than incomplete, and it is the first
    thing that has to change: the reap, WNOHANG's bare 0, the
    [put_user] and the -EFAULT it can answer, and the fact that Linux's
    -EFAULT is LOSSY — [kernel_wait4] reaps the child and drops the pid
    reference BEFORE the copy-out, so a failed copy destroys a zombie
    and an exit status nothing can recover — all arrive together. *)
Definition wait4_spec (upid stat_addr options rusage : word)
    : Sys SyscallEffect :=
  if negb (Z.eqb (bv_unsigned upid) WAIT_ANY32) then unmodeled
  else if negb (Z.eqb (bv_unsigned options) WNOHANG) then unmodeled
  else if negb (w_is0 rusage) then unmodeled
  else
    m <- get_model ;;
    if State.m_has_children m then unmodeled
    else err_ret ECHILD.
