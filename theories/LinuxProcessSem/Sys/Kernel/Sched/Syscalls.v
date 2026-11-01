(** * LinuxProcessSem.Sys.Kernel.Sched.Syscalls — sched_getaffinity (123), sched_setscheduler (119), sched_yield (124)

    This file answers to Linux [kernel/sched/syscalls.c]: it holds what
    the kernel defines there, and nothing else.  Which file a spec
    belongs in is therefore not a judgement call — look up where the
    kernel defines the syscall.  [Specs.v] carries the whole map.  The
    scheduler syscalls moved out of [kernel/sched/core.c] into
    [kernel/sched/syscalls.c] at v6.11.  That the MOVE was behaviourally
    empty is checked for [sched_getaffinity]'s two functions and claimed
    for no others: both are byte-identical either side of it.  The
    [sched_setscheduler] arm below makes no cross-version claim at all
    and is read at v6.18.46 alone.  [sched_yield] moved with them and
    is read at v6.12.1.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* ---- sched_getaffinity (123) -------------------------------------------- *)

(** [sched_getaffinity pid len user_mask_ptr] (123).

    Every kernel citation below is at v6.18.46, commit 1f99e9ab748f,
    unless it names a version window of its own.

    NUMBER 123 HAS TWO ENTRY POINTS and this spec models one of them.
    include/uapi/asm-generic/unistd.h wires it with [__SC_COMP], which
    names sys_sched_getaffinity in the native table and
    compat_sys_sched_getaffinity in the compat one; the second is
    defined by kernel/compat.c's
    [COMPAT_SYSCALL_DEFINE3(sched_getaffinity)].  Neither generated
    symbol is written in brackets here on purpose: the name a reader
    can retrace is the macro, not what it expands to.
    Which table an ecall indexes is decided by [syscall_handler]
    (arch/riscv/include/asm/syscall.h): [compat_sys_call_table] when
    [(regs->status & SR_UXL) == SR_UXL_32], the native one otherwise.
    Every process this model can load is LP64 — elf-snapshot refuses any
    image whose [EI_CLASS] is not [ELFCLASS64], and the ISA model is RV64
    — so the native arm is the only one reachable here.  That is worth
    naming because it is NOT a property of the architecture: riscv64
    defaults [CONFIG_COMPAT] on (arch/riscv/Kconfig, [config COMPAT],
    [default 64BIT]), and the two bodies gate differently.  The compat
    one is [len & (sizeof(compat_ulong_t) - 1)], which is [& 3] where the
    native gate is [& 7], so a 32-bit task SUCCEEDS at a [len] of 4 where
    an LP64 task is refused.  A 32-bit caller does not see a different 8;
    it lands in a different function.  This spec stops being right about
    a [len] of 4 the day something teaches the loader to accept an
    ELFCLASS32 image.

    THE NATIVE FUNCTION, in its own order (kernel/sched/syscalls.c,
    [SYSCALL_DEFINE3(sched_getaffinity)] and the [sched_getaffinity]
    helper it calls):

      if ((len * BITS_PER_BYTE) < nr_cpu_ids)  return -EINVAL;
      if (len & (sizeof(unsigned long)-1))     return -EINVAL;
      if (!zalloc_cpumask_var(&mask, GFP_KERNEL)) return -ENOMEM;
      ret = sched_getaffinity(pid, mask);      /* -ESRCH, or an LSM's
                                                  errno, or 0 with
                                                  mask = p->cpus_mask
                                                       & cpu_active_mask */
      if (ret == 0) {
        unsigned int retlen = min(len, cpumask_size());
        if (copy_to_user(user_mask_ptr, cpumask_bits(mask), retlen))
             ret = -EFAULT;
        else ret = retlen;
      }
      return ret;

    The outer body is byte-identical from v6.3 through v6.18.46; before
    v6.3 it differs only in [alloc_cpumask_var] versus [zalloc_] and in
    passing [mask] rather than [cpumask_bits(mask)] to [copy_to_user],
    neither of which touches the two gates.  The helper is
    byte-identical from v6.7 through v6.18.46.  v6.1 through v6.6 are a
    different TEXT — explicit [rcu_read_lock] and [raw_spin_lock_irqsave]
    where v6.7+ uses [guard], a [goto out_unlock] single exit where v6.7+
    returns early — and the same BEHAVIOUR: same errno set, same
    [security_task_getscheduler] position, same [cpumask_and(mask,
    &p->cpus_mask, cpu_active_mask)].  Nothing this spec models is inside
    the helper at all.  Both claims are over the whole interval rather
    than its endpoints: the two bodies were extracted and compared at
    every release tag in the range, the v6.10/v6.11 move of the file
    included.

    WHAT IS MODELED IS THE MACHINE-INDEPENDENT HALF, and that is the
    whole argument for this arm.  Both gates return the SAME errno, so
    which of them fires is not observable — only whether one of them
    does.  That lets the spec answer for a length either gate refuses
    without knowing [nr_cpu_ids], the runtime CPU count this model has
    no representation of at all:

    - A LENGTH THAT IS NOT A MULTIPLE OF 8 is -EINVAL whatever
      [nr_cpu_ids] is.  If the size gate fires first the answer is
      -EINVAL; if it does not, the alignment gate fires and the answer
      is -EINVAL.
    - A LENGTH WHOSE BIT COUNT WRAPS TO ZERO is -EINVAL because
      [nr_cpu_ids >= 1].  [len] is an [unsigned int] and [BITS_PER_BYTE]
      is the plain [8] (include/linux/bits.h — the constant this arm
      rests on, since an [8UL] there would widen the product to 64 bits
      and leave no wrap to model), so [len * BITS_PER_BYTE] is computed
      in [unsigned int] and WRAPS modulo 2^32.  The product is zero
      exactly on the multiples of 2^29, which a model doing the
      multiplication over the integers would call successes.
      [nr_cpu_ids >= 1] is what turns "the product is 0" into "-EINVAL".
      IT IS A CLAIM ABOUT RISCV64 AND IS STATED THAT WAY ON PURPOSE:
      the general form is false, because arch/x86/xen/smp_pv.c's
      [xen_smp_count_cpus] calls [set_nr_cpu_ids(cpus)] with an
      unguarded [cpus] that is 0 when the very first [VCPUOP_is_up]
      hypercall fails.  On riscv64 it holds by two routes, and which
      one applies is a config question.  Where [nr_cpu_ids] is a
      variable at all — kernel/smp.c guards
      [unsigned int nr_cpu_ids __read_mostly = NR_CPUS] with
      [#if (NR_CPUS > 1) && !defined(CONFIG_FORCE_NR_CPUS)] — it starts
      at [NR_CPUS] and [setup_nr_cpu_ids()] resets it to
      [find_last_bit(cpumask_bits(cpu_possible_mask), NR_CPUS) + 1], at
      least 1 for any argument because [find_last_bit]
      (include/linux/find.h and lib/find_bit.c, both arms) answers
      [size] when no bit is set, so an empty possible mask would give
      [NR_CPUS + 1] rather than 0.  The [nr_cpus=] boot parameter is
      the one knob that reaches it from outside and [nrcpus()] guards
      it with [nr_cpus > 0].  Otherwise include/linux/cpumask.h
      replaces the variable with the constant [((unsigned int)NR_CPUS)]
      and [set_nr_cpu_ids] degenerates to a [WARN_ON], so nothing can
      write it; [NR_CPUS] is then at least 1 because
      arch/riscv/Kconfig's [config NR_CPUS] is [depends on SMP] with
      every [range] starting at 2, and a [!SMP] build takes
      include/linux/threads.h's
      [#ifndef CONFIG_NR_CPUS / #define CONFIG_NR_CPUS 1].  What makes
      the riscv64 scoping checkable rather than a hedge: the cited
      tree has ten [set_nr_cpu_ids] call sites across seven files and
      none of them is under arch/riscv, so the arch never overrides the
      value and the two routes above are the whole story here.

    THE ORDER IS WHY [pid] AND [user_mask_ptr] ARE ABSENT FROM THE
    SIGNATURE.  Both gates run before [find_process_by_pid] is reached
    and before the pointer is touched at all: there is no [access_ok]
    anywhere in kernel/sched/syscalls.c, and the pointer's first and
    only use is the [copy_to_user] inside the [ret == 0] block.  A
    malformed length therefore beats -ESRCH and -EFAULT both.  The -ENOMEM from
    [zalloc_cpumask_var] sits behind both gates too, so it cannot
    pre-empt either answer.

    WHY THE REST IS DECLINED.  A length that is a nonzero multiple of 8
    whose bit count does not wrap either succeeds or is -EINVAL, and
    which one it is depends on [nr_cpu_ids].  Modeling that needs three
    facts about the machine, none of which this model represents:

    - [nr_cpu_ids], which decides the first gate;
    - [cpumask_size()], which decides the RETURN VALUE, since a success
      returns [min(len, cpumask_size())] and not 0.  It is
      [bitmap_size(large_cpumask_bits)] (include/linux/cpumask.h), and
      [large_cpumask_bits] is the compile-time [NR_CPUS] when
      [NR_CPUS <= 4*BITS_PER_LONG] and the runtime [nr_cpu_ids] above
      that — so the byte count a successful call returns is not a
      function of [len] alone;
    - the mask itself, [p->cpus_mask & cpu_active_mask], which is the
      bytes copied out.

    They are also not per-call choices.  A machine has one CPU count for
    the life of a process, so a [choose] resolved afresh at each call
    would admit a trace in which two [sched_getaffinity] calls disagree
    about how many CPUs exist — a trace no Linux machine produces.  The
    honest shape is a model-state field pinned at the first observation,
    the way [State.limst_core] pins RLIMIT_CORE and [State.procst_tid]
    pins the tid; that field does not exist yet, and adding it is what
    the successful path waits on.  [State.v]'s note above [Record Model]
    compares that mechanism against the two alternatives.

    Cost of the decline, stated plainly: a program that asks how many
    CPUs it may run on leaves the modeled surface on that call.  musl's
    [do_getaffinity] (musl 1.2.5, src/sched/affinity.c) passes [size]
    through unchanged and then uses the RETURNED byte count to zero the
    tail of the caller's [cpu_set_t] before answering 0 — so the count
    this spec declines to produce is the one that wrapper depends on,
    and a [CPU_COUNT] query over any plausible [cpu_set_t] lands in the
    declined band.  So does the Zig standard library's
    [std.Thread.getCpuCount].  A program that merely passes a malformed
    length — a zero, an unaligned one, or one of the wrapping ones —
    does not. *)

(** The two gates, as one predicate over the [unsigned int] the ABI
    delivers.  The disjunction's order is not the kernel's order (the
    size gate is first there); it does not have to be, because both
    gates answer -EINVAL and no execution can tell them apart.

    THE [abi_low32] IS DOCUMENTATION HERE, NOT ARITHMETIC, and saying so
    saves someone writing a test that cannot fail.  [len] really is
    narrowed to 32 bits before the kernel sees it ([__SC_CAST] in
    include/linux/syscalls.h, applied by [__SYSCALL_DEFINEx] out of
    arch/riscv/include/asm/syscall_wrapper.h), but this predicate cannot
    observe the narrowing.  [l mod 8] is unchanged by adding a multiple
    of 2^32 because 8 divides 2^32; [l * 8 mod 2^32] is unchanged because
    2^32 divides 8 * 2^32.  So deleting the truncation would leave every
    test in this tree passing.  A spec arm that compared [len] against a
    BOUND would be a different matter. *)
Definition affinity_len_einval_b (len : word) : bool :=
  let l := bv_unsigned (abi_low32 len) in
  (((l * 8) mod 2 ^ 32 =? 0)%Z || negb ((l mod 8 =? 0)%Z))%bool.

Definition sched_getaffinity_spec (len : word) : Sys SyscallEffect :=
  if affinity_len_einval_b len then err_ret EINVAL else unmodeled.

(* ---- sched_setscheduler (119) ------------------------------------------- *)

(** [sched_setscheduler pid policy param] (119).

    Every kernel citation below is at v6.18.46, commit 1f99e9ab748f.

    THE CALL, IN THE ORDER LINUX MAKES ITS DECISIONS.  Four functions,
    all in kernel/sched/syscalls.c bar the last hop:

      SYSCALL_DEFINE3(sched_setscheduler):
        if (policy < 0) return -EINVAL;
      do_sched_setscheduler(pid, policy, param):
        if (unlikely(!param || pid < 0)) return -EINVAL;
        if (copy_from_user(&lparam, param, sizeof(struct sched_param)))
          return -EFAULT;
        CLASS(find_get_task, p)(pid);   /* pid ? find_task_by_vpid(pid)
                                           : current */
        if (!p) return -ESRCH;
        return sched_setscheduler(p, policy, &lparam);
      _sched_setscheduler(p, policy, param, check = true):
        attr = { .sched_policy = policy,
                 .sched_priority = param->sched_priority,
                 .sched_nice = PRIO_TO_NICE(p->static_prio) };
        if (p->se.custom_slice) attr.sched_runtime = p->se.slice;
        if (policy & SCHED_RESET_ON_FORK) {      /* the legacy hack */
          attr.sched_flags |= SCHED_FLAG_RESET_ON_FORK;
          attr.sched_policy = policy &= ~SCHED_RESET_ON_FORK;
        }
      __sched_setscheduler(p, &attr, user = true, pi = true):
        if (!valid_policy(policy))                    return -EINVAL;
        if (attr->sched_flags & ~(SCHED_FLAG_ALL | SCHED_FLAG_SUGOV))
                                                      return -EINVAL;
        if (attr->sched_priority > MAX_RT_PRIO-1)      return -EINVAL;
        if ((dl_policy(policy) && !__checkparam_dl(attr)) ||
            (rt_policy(policy) != (attr->sched_priority != 0)))
                                                      return -EINVAL;
        user_check_sched_setscheduler(...)            /* -EPERM */
        security_task_setscheduler(p)                 /* an LSM's errno */
        ... scx_check_setscheduler, the SCHED_DEADLINE bandwidth check,
        and then the state change, which returns 0.

    [struct sched_param] is the single [int sched_priority]
    (include/linux/sched.h), so the copy is FOUR bytes and its width is
    not an argument of the call.  [attr.sched_priority] is a [__u32]
    (include/uapi/linux/sched/types.h), so a NEGATIVE [int] priority
    arrives at the [> MAX_RT_PRIO-1] comparison as a large unsigned and
    is -EINVAL — the same answer, by the opposite route, as a priority
    of 100.

    WHAT IS ANSWERED, AND THE ONE THING THAT MAKES IT ANSWERABLE.  Every
    decision above the [user_check_sched_setscheduler] line is a function
    of the ARGUMENTS alone: no [nr_cpu_ids], no credentials, no rlimit,
    no scheduling state.  So the whole prefix — the two -EINVALs, the
    -EFAULT, and the four -EINVALs [__sched_setscheduler] raises before
    it consults the task — is modeled exactly, in the kernel's order.
    Order is the load-bearing half of that: a call with a negative
    policy AND a null [param] AND an unreadable priority is -EINVAL and
    not -EFAULT, and the [policy < 0] test is why.

    Past that line the answer stops being a function of the arguments,
    with ONE exception, and that exception is this arm's reason to
    exist:

    - SCHED_IDLE AT PRIORITY 0, ON THE CALLING TASK, IS 0.  Walk
      [user_check_sched_setscheduler] with [policy = SCHED_IDLE]:
      [fair_policy(5)], [rt_policy(5)] and [dl_policy(5)] are all false
      (kernel/sched/sched.h), so the nice, RT-priority and DEADLINE
      gates are skipped; [task_has_idle_policy(p) && !idle_policy(5)] is
      false on its second conjunct WHATEVER [p->policy] is, which is the
      step that removes the scheduling state from the answer;
      [check_same_owner(p)] holds because [p] IS [current], so its
      [uid_eq(cred->euid, pcred->euid)] compares a task's euid with its
      own; and [p->sched_reset_on_fork] is 0 (below).  It returns 0
      without ever reaching [capable(CAP_SYS_NICE)], so no capability
      and no rlimit is consulted.  [scx_check_setscheduler]
      (kernel/sched/ext.c) is 0 for every [policy] but SCHED_EXT.  Both
      exits then return 0: if [p->policy] is already SCHED_IDLE the
      [policy == p->policy] fast path stores [reset_on_fork] and returns
      0, and if it is not, [change:] skips the RT-group and DEADLINE
      bandwidth gates (both [rt_policy]/[dl_policy] guarded), performs
      the change and returns 0.

    WHAT SCHED_IDLE ASSUMES, STATED AS SUCH.  Two facts about the
    process, and one about the kernel:

    - [p->sched_reset_on_fork] IS 0.  [sched_fork] (kernel/sched/core.c)
      clears it unconditionally on the branch that reads it —
      [if (unlikely(p->sched_reset_on_fork)) { ...; p->sched_reset_on_fork = 0; }]
      — so a task has it clear at the moment [fork] returns, whether or
      not the parent had it set.  It is the last gate of
      [user_check_sched_setscheduler], and with it SET an unprivileged
      SCHED_IDLE call is -EPERM rather than 0.
    - [p] IS NOT SCHED_DEADLINE.  The same [sched_fork] returns -EAGAIN
      for [dl_prio(p->prio)], so a SCHED_DEADLINE task cannot fork at
      all and no child is one.  Nothing in the modeled run can make the
      process one either: this arm answers -EINVAL for SCHED_DEADLINE
      (see below) and [sched_setattr] (274) has no arm.  If it were one,
      the [(dl_policy(policy) || dl_task(p)) && sched_dl_overflow(...)]
      gate would run.
    - NO LSM.  [security_task_setscheduler] (kernel/sched/syscalls.c)
      is 0 under the model's standing position that no LSM is
      registered, the same one
      [Fs.Fcntl.fcntl_spec] takes for [security_file_fcntl] and
      [Fs.Stat.newfstatat_spec] for [security_inode_getattr].

    The first two hold at [execve] and are preserved by every syscall
    the model admits; what they exclude is a LAUNCHER that changed the
    child's scheduling parameters between [fork] and [exec].  That is
    the same world [State.init_model] already pins by deriving the
    effective and saved ids from the real ones — an ordinary exec — and
    a run launched otherwise is outside this model, exactly as a run
    with file capabilities is.

    WHY THERE IS NO STATE FIELD, and what would falsify that.  A
    SCHED_IDLE call really does write [p->policy], [p->rt_priority],
    [p->prio] and [p->sched_class], and this model carries none of them.
    That is sound because the model DECLINES every call whose answer
    depends on them, and the declines are not incidental:
    SCHED_NORMAL and SCHED_BATCH are declined precisely because
    [task_has_idle_policy(p)] decides them — a task already SCHED_IDLE
    needs [RLIMIT_NICE] or CAP_SYS_NICE to leave, and this arm can PUT
    it there — and SCHED_FIFO/SCHED_RR because [RLIMIT_RTPRIO],
    [p->rt_priority] and CAP_SYS_NICE decide them.  No other modeled
    syscall reads a scheduling parameter; [sched_getscheduler] (120),
    [sched_getparam] (121), [sched_getattr] (274), [sched_setattr] (274)
    and [getpriority] (141) have no arms.  THIS STOPS BEING TRUE THE DAY
    ANY OF THOSE FIVE LANDS, or the day SCHED_NORMAL is answered: each
    of them needs a [Model] field pinned the way [State.limst_core] pins
    RLIMIT_CORE, and this arm has to gain it FIRST or it starts
    answering a call the reader can then observe was wrong.

    THE ONE PIECE OF STATE THAT IS READ ELSEWHERE is
    [p->timer_slack_ns], which [Kernel.Time.Hrtimer.nanosleep_spec]
    argues about.  [__setscheduler_params] (kernel/sched/syscalls.c)
    zeroes it for
    [rt_or_dl_task_policy(p)] and otherwise restores
    [p->default_timer_slack_ns] if it is 0, so a move to SCHED_IDLE
    either leaves it alone (the usual case, where it is nonzero) or
    RAISES it from 0 to the default.  Neither direction reaches the
    nanosleep model, whose remainder is deliberately unbounded from
    above; what the move cannot do is make the task RT or DL, which is
    the condition those arguments actually turn on.

    WHY SCHED_EXT (7) IS DECLINED AND NOT ANSWERED.  [valid_policy] is
    [idle_policy || fair_policy || rt_policy || dl_policy], and
    [normal_policy] — the first disjunct of [fair_policy] — reads
    [if (policy == SCHED_EXT) return true;] under
    [#ifdef CONFIG_SCHED_CLASS_EXT] (kernel/sched/sched.h).  So whether
    7 is a valid policy at all is a config question, and this model does
    not fix that config.  A priority the [> MAX_RT_PRIO-1] gate refuses,
    or a nonzero one the [rt_policy(7) != (priority != 0)] gate refuses,
    happens to be -EINVAL under BOTH configs; policy 7 at priority 0 is
    not, so the whole number is declined rather than half of it.

    WHY SCHED_DEADLINE (6) IS -EINVAL AND NEVER ANYTHING ELSE.  The
    legacy entry point cannot express a DEADLINE parameter set:
    [_sched_setscheduler] builds an [attr] whose [sched_deadline] is 0,
    and [__checkparam_dl] (kernel/sched/deadline.c) refuses
    [attr->sched_deadline == 0], so [dl_policy(policy) &&
    !__checkparam_dl(attr)] fires for every [param] a caller can pass.
    That is what makes the second assumption above self-maintaining.

    WHY A NONZERO pid THAT IS NOT THE CALLER IS DECLINED.  [pid = 0] is
    [current] by [find_process_by_pid], and a [pid] equal to the tid the
    model has pinned ([State.procst_tid], which musl's
    [pthread_setschedparam] supplies — it passes [t->tid], not 0) is
    that same task.  Any OTHER positive pid is a task this model has no
    representation of: whether one exists at all decides -ESRCH, and if
    one does, [check_same_owner] and its credentials decide the rest.
    So the model cannot tell -ESRCH from a permitted call, and declines.
    A pid the model has not pinned a tid for is declined for the same
    reason: with [m_tid] still [None] the model cannot say whether the
    number names the caller.

    THE COPY-IN IS RECORDED ON EVERY PATH PAST IT, including the four
    -EINVALs and every decline, because [copy_from_user] runs BEFORE the
    task lookup and before [__sched_setscheduler] sees the policy.  A
    -EFAULT records nothing: an [access_ok] refusal happens before any
    load.  A range [access_ok] admits that is not wholly mapped is
    [unmodeled] rather than -EFAULT, for the reason
    [Kernel.Sys.prlimit64_spec] gives for its own [new_rlim] — Linux
    answers -EFAULT there too, but which bytes it read first is not
    something the ledger can state.

    THE RANGE TEST COMES BEFORE THE WALK: the four bytes are read
    through [State.copy_bytes_map], whose note says why that order is
    the guard.  [do_sched_setscheduler]'s [copy_from_user] of [struct
    sched_param] (kernel/sched/syscalls.c) asks [access_ok] over all
    four bytes before it loads one, so a [param] whose range wraps past
    2^64 and reads back from 0 is -EFAULT with an empty ledger, and the
    priority those bytes would decode to is never judged.
    [Checks.Cases.Kernel.Sched.Syscalls]'s [sched_setscheduler_wrap_]
    group pins it, beside a neighbour at the top of what [access_ok]
    accepts.

    COST OF THE DECLINES.  A program that lowers itself to SCHED_IDLE
    stays inside the modeled surface, which is the shape a
    [pthread_setschedparam(self, SCHED_IDLE, {0})] takes; a program that
    RAISES its policy, that sets one on another task, or that returns
    from SCHED_IDLE to SCHED_NORMAL, leaves it. *)

(** [valid_policy] minus SCHED_EXT, which is declined before this test
    is reached.  Written as a membership test because the six numbers
    are not an interval: the header leaves 4 to an unimplemented
    SCHED_ISO. *)
Definition sched_valid_policy_b (pol : Z) : bool :=
  ((pol =? SCHED_NORMAL) || (pol =? SCHED_FIFO) || (pol =? SCHED_RR)
   || (pol =? SCHED_BATCH) || (pol =? SCHED_IDLE)
   || (pol =? SCHED_DEADLINE))%Z.

(** [rt_policy], which is config-independent. *)
Definition sched_rt_policy_b (pol : Z) : bool :=
  ((pol =? SCHED_FIFO) || (pol =? SCHED_RR))%Z.

(** Whether the call names the CALLING task, which is the only task this
    model represents.  [find_process_by_pid] is
    [pid ? find_task_by_vpid(pid) : current], so a zero pid always does;
    a positive one does exactly when it is the pinned tid.  The pid is
    read at [pid32] width because it arrives as a [pid_t], and the zero
    test is on those low 32 bits for the same reason — a register whose
    low half is zero IS a zero pid to the kernel. *)
Definition sched_targets_self_b (pid : word) (m : Model) : bool :=
  (w_is0 (pid32 pid)
   || match m_tid m with
      | Some tid => bv_eqb (pid32 pid) tid
      | None => false
      end)%bool.

(** EVERYTHING [__sched_setscheduler] DECIDES ONCE THE TASK IS IN HAND,
    as one function of the policy word and the copied-in priority:
    [Some r] is the value [a0] takes, [None] is the decline.  Written
    apart from the spec because it is the whole of what the checker in
    [Checks/Sys/Kernel/Sched/Syscalls.v] mirrors, and a single ordered
    chain is easier to compare against the kernel's than the same chain
    transcribed twice.

    THE ORDER IS THE KERNEL'S, and the two declines are placed where
    Linux's decision sits rather than at the front: [SCHED_RESET_ON_FORK]
    is stripped by [_sched_setscheduler] before [valid_policy] runs, and
    SCHED_EXT is a [valid_policy] question, so both precede every
    -EINVAL below them.  Declining early is what fail-closed costs here;
    answering early would be a wrong answer.

    [prio] is the [__u32] the [int sched_priority] was widened to, so
    the [> MAX_RT_PRIO-1] test catches a negative [int] as well as a
    priority of 100 or more, and [prio <> 0] is the [attr->sched_priority
    != 0] the RT/non-RT agreement test compares against. *)
Definition sched_setscheduler_answer (pol prio : Z) : option word :=
  if negb (Z.land pol SCHED_RESET_ON_FORK =? 0)%Z then None
  else if (pol =? SCHED_EXT)%Z then None
  else if negb (sched_valid_policy_b pol) then Some (errno_ret EINVAL)
  else if (MAX_RT_PRIO - 1 <? prio)%Z then Some (errno_ret EINVAL)
  else if (pol =? SCHED_DEADLINE)%Z then Some (errno_ret EINVAL)
  else if xorb (sched_rt_policy_b pol) (negb (prio =? 0)%Z)
       then Some (errno_ret EINVAL)
  else if (pol =? SCHED_IDLE)%Z then Some (Z_to_bv 64 0)
  else None.

Definition sched_setscheduler_spec (pid policy param : word)
    : Sys SyscallEffect :=
  if (sint32 policy <? 0)%Z then err_ret EINVAL
  else if (w_is0 param || (sint32 pid <? 0)%Z)%bool then err_ret EINVAL
  else
  i <- input ;;
  m <- get_model ;;
  match copy_bytes_map (in_mem i) param 4 with
  | None =>
      if negb (access_okb param 4) then err_ret EFAULT else unmodeled
  | Some bs =>
      record_copyins [(param, 4%nat)]
      (if negb (sched_targets_self_b pid m) then unmodeled
       else
         match sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                 (bv_unsigned (le_bytes_to_word bs)) with
         | Some r => ret_only r
         | None => unmodeled
         end)
  end.

(* ---- sched_yield (124) --------------------------------------------------- *)

(** [sched_yield] (124): 0, with nothing this model can see changed.

    (Linux v6.12.1, kernel/sched/syscalls.c,
    [SYSCALL_DEFINE0(sched_yield)], whose whole body is
    [do_sched_yield(); return 0;] and whose kernel-doc says "Return: 0."
    The number has one entry point: include/uapi/asm-generic/unistd.h
    wires 124 with [__SYSCALL] and not [__SC_COMP], so there is no
    compat body to land in the way [sched_getaffinity] above has.)

    NO ARGUMENT IS READ, and that is a fact about the declaration rather
    than about this spec's convenience.  riscv64 overrides
    [SYSCALL_DEFINE0] (arch/riscv/include/asm/syscall_wrapper.h) to take
    [const struct pt_regs *__unused] and to expand without
    [SC_RISCV_REGS_TO_ARGS], so no argument register reaches the body on
    this path.  Ignoring all six argument words is therefore exact, not
    an approximation, and a spec that refused some argument shape would
    be wrong about a call Linux answers 0.

    WHAT [do_sched_yield] DOES, and why none of it is modeled state: it
    takes the run queue lock, bumps [rq->yld_count], calls the
    scheduling class's [yield_task], and calls [schedule].  All four are
    per-run-queue scheduler bookkeeping.  Nothing there is reachable
    through the syscall interface this model covers — the model carries
    no run queue, no scheduling class and no notion of which task holds
    a CPU — so an arm that changed no model state is not discarding an
    effect a later call could observe.  What [schedule] really costs is
    TIME, and time is where this arm stops being the whole truth:
    another task may run in between, so a [sched_yield] can separate two
    of this process's observations.  That costs nothing here because
    this model has one process — [Fork.clone_fork_flags_b] admits
    [SIGCHLD] alone, [Fork.clone_ns_flags_b] adds only namespace bits,
    and every sharing flag forces [Unmodeled], so there
    is no second thread whose interleaving a yield could expose.  The
    day a shared-memory clone is modeled, this comment is what has to be
    re-read.

    Residual infidelity, stated rather than modeled, and shared with
    every zero-argument arm here: [SYSCALL_DEFINE0] emits
    [ALLOW_ERROR_INJECTION(..., ERRNO)], riscv's override included, so
    on a kernel built with [CONFIG_FUNCTION_ERROR_INJECTION] and running
    a BPF program that calls [bpf_override_return] the call can be made
    to return an errno.  The model describes a kernel with no such
    override attached; [Kernel.Sys.getpid_spec] carries the same note. *)
Definition sched_yield_spec : Sys SyscallEffect :=
  ret_only (Z_to_bv 64 0).
