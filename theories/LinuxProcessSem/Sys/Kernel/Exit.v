(** * LinuxProcessSem.Sys.Kernel.Exit — exit (93), exit_group (94), wait4 (260)

    This file answers to Linux [kernel/exit.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** Halt the run.  The observed exit code is the low byte of the status,
    as a waiting parent sees it.  The returned effect is never applied
    (Run.v ends the trace with an [ExitEv] instead). *)
Definition exit_spec (code : word) : Sys SyscallEffect :=
  set_halted (bv_and code (Z_to_bv 64 255)) ;; ret_only (Z_to_bv 64 0).


(* =========================================================================
   Process reaping: wait4 (260)
   ========================================================================= *)

(** [upid = -1] after the [int] truncation [Syscall.pid32] applies:
    "reap any child".  It is the ONLY selector modeled — see
    [wait4_spec]. *)
Definition WAIT_ANY32 : Z := (2 ^ 32 - 1)%Z.

(** THE STATUS WORDS A REAP CAN REPORT for a child that exited or was
    killed.  [wait_task_zombie] (kernel/exit.c) hands back
    [SIGNAL_GROUP_EXIT ? group_exit_code : exit_code], and that word has
    one of two shapes:

    - AN EXIT: [(code & 0xff) << 8], what [SYSCALL_DEFINE1(exit)] and
      [SYSCALL_DEFINE1(exit_group)] pass to [do_exit] and
      [do_group_exit].  The low byte is 0 and the word is below 0x10000.
    - A DEATH BY A SIGNAL: the signal number, which [get_signal]
      (kernel/signal.c) passes to [do_group_exit] and [complete_signal]
      stores as [group_exit_code], with 0x80 added by [coredump_finish]
      (fs/coredump.c) when a core was written.  Bits 0..6 hold a signal
      1..64 and the word is below 0x100.

    A stopped report (0x7f in the low byte) or a continued one (0xffff)
    needs WUNTRACED or WCONTINUED, which [wait4_spec] declines, so
    neither is here.

    THIS ADMITS MORE THAN LINUX GIVES.  Every signal 1..64, with or
    without the core bit, counts as a death, where Linux kills only by a
    signal whose action is fatal (SIGSTOP stops, and SIGCHLD and SIGCONT
    are ignored, under their default actions) and sets the core bit only
    for a signal whose default action dumps core.  SCOPE.md lists this
    under "Known gaps in precision".

    Over [Z] rather than [word] so that a checker can decode the four
    stored bytes with [BvBase.bytes_le_to_Z] and test the value it
    reads.  Kernel citations read at v6.18.44; identical at v6.18.46. *)
Definition wait_status_okz (s : Z) : bool :=
  (0 <=? s)%Z
  && (((Z.land s 255 =? 0)%Z && (s <? 65536)%Z)
      || ((1 <=? Z.land s 127)%Z && (Z.land s 127 <=? 64)%Z && (s <? 256)%Z)).

(** [q] is one of the recorded children [l]: [In q l], as a boolean
    test. *)
Definition pid_recorded_b (q : word) (l : list word) : bool :=
  existsb (bv_eqb q) l.

(** [l] without the FIRST occurrence of [q], the rest in their order:
    what [release_task] (kernel/exit.c) leaves of the parent's
    [children] list when it unlinks the reaped task
    ([__unhash_process]'s [list_del_init(&p->sibling)]).  Read at
    v6.18.44; identical at v6.18.46. *)
Fixpoint remove_pid (q : word) (l : list word) : list word :=
  match l with
  | [] => []
  | p :: l' => if bv_eqb q p then l' else p :: remove_pid q l'
  end.

(** The status pointer a reap can store through: NULL, which asks for no
    store, or four bytes that [State.copy_bytes_map] admits ([access_ok]
    over the range, then the walk over [wmem]). *)
Definition wait4_stat_ok_b (wmem : word -> option byte) (stat_addr : word)
    : bool :=
  w_is0 stat_addr
  || match copy_bytes_map wmem stat_addr 4 with
     | Some _ => true
     | None => false
     end.

(** The store a reap makes: [put_user] of the [int] status to
    [stat_addr], four bytes little-endian, and nothing when [stat_addr]
    is NULL. *)
Definition wait4_stat_store (stat_addr : word) (s : Z)
    : list (word * list byte) :=
  if w_is0 stat_addr then [] else [(stat_addr, Z_to_le_bytes 4 s)].

(** [wait4 upid stat_addr options rusage] (260) — the whole call, for
    the one argument shape it answers: [wait4(-1, stat_addr, WNOHANG,
    NULL)].  It is the call bubblewrap 0.13.1's [monitor_child] loop
    makes through [waitpid(-1, &died_status, WNOHANG)] (bubblewrap.c),
    and musl's [waitpid] is [sys_wait4_cp(pid, status, options, 0)]
    (src/process/waitpid.c, v1.2.5 and v1.2.6).

    Kernel side read at v6.18.44; identical at v6.18.46: kernel/exit.c
    [SYSCALL_DEFINE4(wait4)], [kernel_wait4], [do_wait], [__do_wait],
    [do_wait_thread], [wait_consider_task], [eligible_child],
    [wait_task_zombie] and [release_task].  [kernel_wait4] and
    [SYSCALL_DEFINE4(wait4, ...)] are byte-identical IN MAINLINE from
    v4.13 — where Al Viro's 359566faefa8,
    "kernel_wait4()/kernel_waitid(): delay copying status to userland",
    turned [wo_stat] from an [int __user *] into an [int] and put the
    copy-out behind the [ret > 0] guard this spec rests on — through
    v7.2.

    ** WHAT THE MODEL HOLDS OF A CHILD

    The model has one process: [Run.config] holds one [machine_state]
    and one [Model], and no [Run.sstep] rule produces a second of
    either.  The child a [clone] (220) or [clone3] (435) creates is
    never a configuration here.  What the model holds of it is the FACT
    that it exists ([State.m_has_children]) and the pid the clone
    returned ([State.m_child_pids], oldest first).  The success branches
    of [Kernel.Fork.clone_resolve] and [Kernel.Fork.clone_ns_resolve]
    record both through [State.with_child], and
    [Checks.ProcessCreation.clone_resolve_declines_or_sets_children],
    [Checks.ProcessCreation.clone_ns_resolve_declines_or_sets_children]
    and [Checks.ProcessCreation.clone_success_records_pid] are the
    universal statements of it.  WHAT A NEW CHILD-CREATING ARM OWES is
    [State.with_child] on its post-state: an arm that creates a child
    and never applies it leaves this spec answering -ECHILD for a caller
    that has one, with every proof in the tree still closing.

    ** THREE CALLERS, THREE ANSWERS

    - NO CHILD ([State.m_has_children] clear): -ECHILD, and nothing
      else.
    - A RECORDED CHILD (the bit set and [State.m_child_pids] not empty),
      in a process whose held SIGCHLD bit is set ([State.m_sigchld_dfl]:
      a SIG_DFL launch or its own SIG_DFL install; see THE SIGCHLD
      DISPOSITION below):
      the environment's choice of 0, with nothing stored and the model
      unchanged, or of a reap: the pid [q] of a recorded child, never 0,
      with a status word [s] that [wait_status_okz] admits, [s] stored at
      [stat_addr] unless it is NULL ([wait4_stat_store]), and the FIRST
      [q] removed from the list ([remove_pid]).  The child bit stays set.
    - A CHILD THE MODEL DID NOT RECORD (the bit set and the list empty):
      [unmodeled].  Every recorded child has been reaped by an earlier
      call, and the bit is never cleared ([State.with_children] says
      why), so the model does not know whether a child remains.
    - A RECORDED CHILD IN A PROCESS WHOSE SIGCHLD BIT IS CLEAR (a SIG_IGN
      launch and no SIG_DFL install): [unmodeled], whatever the list holds.

    Before this, every caller with a child was declined, and the model
    contained no reap.

    ** THE SIGCHLD DISPOSITION

    Linux leaves an exiting child a zombie for [wait4] only when its
    parent's SIGCHLD is not SIG_IGN and SA_NOCLDWAIT is clear: otherwise
    [do_notify_parent] (kernel/signal.c) sets [autoreap], the child is
    reaped at its exit, and [wait4] answers 0 and then -ECHILD, never
    its pid.  The disposition a process starts with is its launcher's:
    [begin_new_exec] (fs/exec.c) calls [flush_signal_handlers(me, 0)],
    which keeps a SIG_IGN, writes SIG_DFL over every other handler and
    clears [sa_flags], SA_NOCLDWAIT included.  So the model answers a
    caller with a recorded child only while the held bit
    [State.procst_sigchld_dfl] is set: [State.init_model] seeds it from
    the launch's declared disposition ([State.ProcInput.in_sigchld_default],
    [true] at SIG_DFL, which [Run.valid_input] and its siblings pin), and
    the one SIGCHLD install [Kernel.Signal.rt_sigaction_spec] answers,
    SIG_DFL with SA_NOCLDWAIT clear ([Kernel.Signal.sigchld_dfl_install]),
    sets it; every other SIGCHLD install declines, so once set the
    disposition stays SIG_DFL.  A child the
    process cloned copies the bit, as [copy_sighand] (kernel/fork.c)
    copies the actions.  bubblewrap 0.13.1 makes the install first
    thing in [main] (bubblewrap.c:2910-2914), before any clone.  The
    childless -ECHILD does not read the bit: with no child there is
    nothing to reap, whatever the disposition.

    ** A CALLER WITH NO CHILD: -ECHILD IS THE ONE ANSWER LINUX GIVES

    An empty pair of lists ([current->children] and [current->ptraced])
    is exactly the state [do_wait] answers -ECHILD to.  [__do_wait]
    (kernel/exit.c, v6.7 and later; the same body is inline in
    [do_wait] before that — Jens Axboe's 06a101ca45b2, "exit: move core
    of do_wait() into helper", is a pure refactor) seeds
    [wo->notask_error] with -ECHILD.  With [upid = -1] the type is
    [PIDTYPE_MAX], so the [wo_type < PIDTYPE_MAX] early exit is NOT
    taken and the tasklist walk runs; [do_wait_thread] and
    [ptrace_do_wait] are list walks that return 0 on an empty list, so
    [wait_consider_task] — and with it [wait_task_zombie], the only
    thing that clears [notask_error] or fills [wo_stat] — never runs.
    Control reaches [notask:] with [notask_error] still -ECHILD, and
    the -ERESTARTSYS assignment there is guarded on [!retval], which
    -ECHILD fails.  [do_wait] then returns that value unchanged: its
    loop breaks on anything but -ERESTARTSYS, before [signal_pending]
    or [schedule] is reached, so there is no sleep and no interruption
    point.  WNOHANG's bare 0 is NOT admissible here — it is what
    [notask_error] cleared to 0 returns, and only a child that exists
    clears it.

    ** A CALLER WITH A RECORDED CHILD: 0 OR A REAP

    EVERY RECORDED CHILD IS ELIGIBLE.  [eligible_child] takes a child
    whose [exit_signal] is SIGCHLD when __WCLONE and __WALL are clear,
    and every recorded child was created by a clone whose exit signal is
    SIGCHLD ([Kernel.Fork.clone_fork_flags_b],
    [Kernel.Fork.clone_ns_flags_b], [Kernel.Fork.clone3_fork_args_b]).
    So [wait_consider_task] reaches each one.  A live child clears
    [notask_error] to 0 and reports nothing (a stop or a continue is
    reported only under WUNTRACED or WCONTINUED), and [__do_wait] then
    returns 0 under WNOHANG.  A zombie child goes to
    [wait_task_zombie], which reaps it ([release_task]) and returns its
    pid with the status word in [wo_stat].

    WHICH ANSWER IS THE ENVIRONMENT'S.  The child runs outside this
    model, so whether it has exited by this call, and with which status,
    is not a thing the model can know.  [do_wait_thread] walks
    [current->children] oldest first and reaps the first zombie it
    finds; the model lets the environment name ANY recorded child, which
    is the first zombie for some timing of the children's exits.  Each
    admitted answer is one Linux gives for some such timing.  The pid
    is never 0 because [task_pid_vnr] of a live task is not, and
    because a recorded 0 reaped through a NULL [stat_addr] would give
    the same effect as the bare 0 with a different model, which no
    checker could tell apart.

    ** [stat_addr]

    [kernel_wait4]'s copy-out is

      if (ret > 0 && stat_addr && put_user(wo.wo_stat, stat_addr))
          ret = -EFAULT;

    and C short-circuits: at -ECHILD and at 0 the pointer is never
    dereferenced.  So the childless caller's -ECHILD does not read
    [stat_addr] at all: an unmapped pointer, one past
    [State.TASK_SIZE], one the model cannot see as writable — every one
    of them answers -ECHILD and faults on nothing.  A spec that judged
    the pointer there would REJECT calls Linux answers.

    At a caller with a recorded child the pointer IS judged, before any
    choice: a non-NULL [stat_addr] that is not four writable bytes
    ([wait4_stat_ok_b]) declines THE WHOLE CALL, so a caller never sees
    [Unmodeled] beside an [Ok].  Linux's answer there is LOSSY:
    [wait_task_zombie] has already run [release_task] when [put_user]
    fails, so the call answers -EFAULT and the zombie and its status are
    gone.  The model does not carry that answer, and the multi-process
    core ([Procs]) declines the same path.  Deciding the decline first
    also declines the bare 0, which Linux would give without touching
    the pointer: coverage lost, not soundness.

    ** WHAT THE LAUNCH IS ASSUMED TO GIVE (in SCOPE.md)

    - NO CHILDREN AND NO TRACEES AT LAUNCH.  For the lists to match what
      the model recorded they must have STARTED empty, and that is a
      property of how the process was launched rather than anything this
      model can see.  It is not a property of [execve]: at v6.18.46
      (commit 1f99e9ab748f) [fs/exec.c] never reads or writes
      [current->children] at all — [begin_new_exec] and [de_thread] kill
      sibling THREADS ([zap_other_threads], kernel/signal.c) and reap no
      child — and [exit_ptrace] (kernel/ptrace.c) is reached only
      through [forget_original_parent] from [exit_notify] on the EXIT
      path.  A launcher that forks a grandchild, or attaches a tracee,
      before exec'ing this image hands the caller something to wait for,
      and Linux then answers 0 or a pid where this spec answers -ECHILD.
      That is a FALSE REJECTION.  The ordinary [fork]-then-[execve]
      launch satisfies the assumption: [copy_process] (kernel/fork.c)
      and [ptrace_init_task] (include/linux/ptrace.h) give a FRESH task
      empty lists, and a task that forks nothing before exec'ing keeps
      them.

    This spec does NOT assume the launch's SIGCHLD disposition: the
    recorded-child answers wait for the process's own SIG_DFL install
    (THE SIGCHLD DISPOSITION above), so a launcher's SIG_IGN can only
    turn an answer into a decline.  [flush_signal_handlers] clears
    [sa_flags] at [execve], so a launcher's SA_NOCLDWAIT does not
    survive either.  SCOPE.md still lists "At launch SIGCHLD is not at
    SIG_IGN" for the multi-process core's own [wait4] arms in [Procs],
    which do not read the bit yet; it is retired when they do.

    THE TRACEE LIST IS CLOSED BY A DECLINE.  [ptrace] (117) is the only
    route to the caller's [current->ptraced] a modeled syscall could
    take, and it is outside the modeled surface —
    [Checks.ProcessCreation.ptrace_unmodeled] pins that against
    [Specs.syscall_spec] itself, as [execve_unmodeled] and
    [execveat_unmodeled] do for 221 and 281.

    ** The argument surface, which is narrow on purpose

    Every argument shape not named above declines and fails closed.
    Each of the three guards below is a call a real kernel ANSWERS, so
    declining is a choice rather than a consequence.

    - [upid] must be -1, "any child" ([type = PIDTYPE_MAX]).  It is
      also the only selector dropbear issues: both call sites are
      [waitpid(-1, ...)] (svr-chansession.c, svr-main.c).  The other
      shapes are not interchangeable with it.  THREE are different
      eligible-child rules — [upid > 0] one child, [upid == 0] the
      caller's process group, [upid < 0] the group [-upid] — and each
      takes the [wo_type < PIDTYPE_MAX] early exit whose verdict depends
      on whether the named pid or group EXISTS, which is state outside
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
      BLOCKS WHILE A CHILD LIVES, and blocking is a wait-queue sleep
      this model has no vocabulary for.  [__do_wait] returns
      -ERESTARTSYS when a child exists but nothing is ready, and
      [do_wait] then sleeps until a signal or a child wakes it — so a
      blocking [wait4] can also come back -EINTR, an answer no arm
      here produces.  A childless caller would get -ECHILD from a
      blocking call as well, since the -ERESTARTSYS assignment is
      guarded on [!retval]; declining anyway keeps the guard on the
      ARGUMENT rather than on a coincidence of the state.  The
      multi-process core answers the blocking reap ([Procs]).

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
      ask about a child's stop and continue, which the model does not
      hold.  bubblewrap's and dropbear's call sites pass WNOHANG alone.

    - [rusage] must be NULL.  It is the literal 0 musl passes.  A
      non-NULL one asks, at a reap, for a [struct rusage] of accounting
      the model does not carry ([SYSCALL_DEFINE4(wait4)] copies it out
      on [err > 0]). *)
Definition wait4_spec (upid stat_addr options rusage : word)
    : Sys SyscallEffect :=
  if negb (Z.eqb (bv_unsigned upid) WAIT_ANY32) then unmodeled
  else if negb (Z.eqb (bv_unsigned options) WNOHANG) then unmodeled
  else if negb (w_is0 rusage) then unmodeled
  else
    m <- get_model ;;
    if State.m_has_children m then
      match State.m_child_pids m with
      | [] => unmodeled
      | _ :: _ =>
          if negb (State.m_sigchld_dfl m) then unmodeled
          else
          i <- input ;;
          if negb (wait4_stat_ok_b (in_wmem i) stat_addr) then unmodeled
          else
            alt (ret_only (Z_to_bv 64 0))
                (q <- choose (fun q =>
                        (pid_recorded_b q (State.m_child_pids m)
                         && clone_pid_ok_b m q) = true) ;;
                 s <- choose (fun s => wait_status_okz s = true) ;;
                 modify (with_child_pids
                           (remove_pid q (State.m_child_pids m))) ;;
                 pure (mkEffect q (wait4_stat_store stat_addr s) []))
      end
    else err_ret ECHILD.
