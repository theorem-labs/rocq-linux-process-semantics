(** * LinuxProcessSem.Sys.Kernel.Futex.Syscalls — futex (98), set_robust_list (99)

    This file answers to Linux [kernel/futex/syscalls.c]: it holds what
    the kernel defines there, and nothing else.  Which file a spec
    belongs in is therefore not a judgement call — look up where the
    kernel defines the syscall.  [Specs.v] carries the whole map.

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

(** Linux checks the native 64-bit [struct robust_list_head] size before
    storing the pointer.  Its three fields are 64-bit words, so the only
    accepted length is 24.  It does not read or validate [head] here.
    QEMU user mode returns -ENOSYS for every length and pointer instead.
    The registered pointer is used only at thread exit; this model's exit
    step discards user-memory effects and has no later user step.
    See kernel/futex/syscalls.c and QEMU linux-user/syscall.c. *)
Definition set_robust_list_spec (len : word) : Sys SyscallEffect :=
  alt (err_ret ENOSYS)
      (if Z.eqb (bv_unsigned len) 24
       then ret_only (Z_to_bv 64 0)
       else err_ret EINVAL).

(** THE WAITER SET OF A PRIVATE FUTEX KEY IS EMPTY IN THIS MODEL, and
    everything below rests on it.  Citations are torvalds/linux read at
    v6.18.46, commit 1f99e9ab748f.

    A waiter is a [struct futex_q] on the plist of a hash bucket, put
    there by [futex_queue] (kernel/futex/core.c) and matched by
    [futex_match] on the [union futex_key] the queueing task computed.
    For an op carrying [FUTEX_PRIVATE_FLAG], [get_futex_key]
    (kernel/futex/core.c) builds that key from the caller's own mm:

        if (!fshared) { key->private.mm = mm;
                        key->private.address = address; return 0; }

    so only a task whose [current->mm] is the SAME POINTER can produce a
    key that [futex_match] accepts.  The hash bucket is global and holds
    other processes' waiters; the key is what excludes them.

    This model steps one task and can reach no second one that shares
    its mm.  The only entry points to [copy_process] (kernel/fork.c) are
    [clone] (220) and [clone3] (435), and neither ever grants [CLONE_VM]:
    [Kernel.Fork.clone_fork_flags_b] admits the single flag word
    [SIGCHLD] and [Kernel.Fork.clone3_fork_args_b] the same word in a
    struct, and every other word declines or fails.  A forked child gets
    a COPY of the mm
    ([copy_mm] calls [dup_mm] when [CLONE_VM] is clear), so its private
    keys are different keys — and it is not a configuration this
    development can be in anyway.

    THAT PREMISE IS CHECKED RATHER THAN ASSERTED.
    [Checks.Cases.Kernel.Futex.Syscalls.clone_fork_gate_grants_no_shared_mm]
    and its [clone3] twin prove that neither gate admits a word with
    [CLONE_VM] set, so widening either one breaks the build beside the
    prose saying why it matters.  An argument that spans two files is
    the kind that rots quietly, and this one is load-bearing for every
    answer below.

    So the count [futex_wake] returns is 0 by construction rather than by
    luck, and a FUTEX_WAIT whose value still matches would park forever.
    THE SECOND HALF IS WHY THIS SPEC IS NARROW: an operation whose answer
    depends on a waiter EXISTING is unanswerable here, and declines.

    WHAT THE EMPTY WAITER SET IS NOT AN ARGUMENT ABOUT.  It says nothing
    about a SHARED futex, whose key [get_futex_key] resolves through the
    page and can name an inode any process on the machine may hold; and
    nothing about [FUTEX_WAKE_OP] or the requeue and PI commands, which
    touch [uaddr2] or a lock word before they look at a waiter at all.
    Every one of those is outside the two op words below. *)

(** The address a futex operation names must be naturally aligned.

    [get_futex_key] (kernel/futex/core.c) is the first thing both
    modeled commands reach, and its first decision is

        key->both.offset = address % PAGE_SIZE;
        if (unlikely((address % size) != 0))
                return -EINVAL;

    with [size = futex_size(flags)], which is [FUTEX_WORD_SIZE] for
    every call this spec can see (see that constant).  The test is on
    the address the caller passed, before any page is resolved, so it
    outranks every other answer either command has. *)
Definition futex_aligned_b (uaddr : word) : bool :=
  Z.eqb (bv_unsigned uaddr mod FUTEX_WORD_SIZE) 0.

(** [get_futex_key]'s two refusals, in its own order, and then the
    command's own answer.

    After the alignment test comes

        if (unlikely(!access_ok(uaddr, size)))
                return -EFAULT;

    ([get_futex_key], kernel/futex/core.c) — the RANGE verdict
    [State.access_okb] decides, and the same [__access_ok] every other
    spec here goes through.  It is a range test and not a page lookup:
    on the private path [get_futex_key] returns as soon as it has the mm
    and the address, before any [get_user_pages_fast], so an address
    that is in range and has NOTHING MAPPED AT IT passes this and
    reaches the command.  That is the one shape where the natural
    implementation of a futex spec — resolve the buffer against the
    model's memory and answer -EFAULT when it is not there — would be
    wrong.  The wake
    on such an address answers 0, not
    -EFAULT; the WAIT on the same address, which does resolve the page,
    really is -EFAULT, and declines here.  The difference between them
    is the whole content of this paragraph.

    The third [get_futex_key] error, [should_fail_futex(fshared)], is
    reachable only with CONFIG_FAIL_FUTEX built in — and even then only
    for a SHARED key, because [fail_futex.ignore_private] starts true
    and short-circuits the private case.  Both modeled ops are private,
    so the fault injector cannot reach them from either of its two
    sites: the other, in [SYSCALL_DEFINE6(futex)]
    (kernel/futex/syscalls.c), is guarded by [!(op & FUTEX_PRIVATE_FLAG)]
    outright.  This is the rare environment obligation that the op gate
    discharges rather than states. *)
Definition futex_key_check (uaddr : word) (k : Sys SyscallEffect)
    : Sys SyscallEffect :=
  if negb (futex_aligned_b uaddr) then err_ret EINVAL
  else if negb (access_okb uaddr FUTEX_WORD_SIZE) then err_ret EFAULT
  else k.

(** FUTEX_WAKE with FUTEX_PRIVATE_FLAG: the number of waiters woken,
    which is 0.

    [futex_wake] (kernel/futex/waitwake.c) reaches its count through
    three gates and this spec answers past all three:

    - [if (!bitset) return -EINVAL;] cannot fire.  [do_futex]
      (kernel/futex/syscalls.c) overwrites [val3] with
      [FUTEX_BITSET_MATCH_ANY] on the [FUTEX_WAKE] arm before falling
      through to [FUTEX_WAKE_BITSET], so the bitset this command is
      given is never the caller's.  [FUTEX_WAKE_BITSET] is a DIFFERENT
      op word and is declined, which is what keeps that distinction from
      being a coincidence.
    - [if ((flags & FLAGS_STRICT) && !nr_wake) return 0;] cannot fire
      either, and would be harmless if it did: [futex_to_flags]
      (kernel/futex/futex.h) never sets [FLAGS_STRICT] — only
      [futex2_to_flags], for syscalls 454 and 455 — and the answer it
      guards is the same 0.
    - [if (!futex_hb_waiters_pending(hb)) return ret;] with [ret = 0] is
      the answer, by the empty-waiter-set argument at the top of this
      file.

    THE COUNT ARGUMENT IS NOT READ, deliberately.  [nr_wake] bounds a
    loop that runs zero times, so 0 is the answer for [INT_MAX] (what
    musl's [__wake] passes for a broadcast, src/thread/__wait.c) and for
    0 and for a negative alike.  A spec that gated on it would decline
    calls Linux answers and would be claiming the count mattered. *)
Definition futex_wake_private_spec (uaddr : word) : Sys SyscallEffect :=
  futex_key_check uaddr (ret_only (Z_to_bv 64 0)).

(** [FUTEX_WORD_SIZE] as a [nat], for the copy-in ledger.  The mirror is
    [Kernel.Fork.CLONE_ARGS_SIZE_nat], and the lemma below is what keeps
    the two spellings from drifting. *)
Definition FUTEX_WORD_SIZE_nat : nat := 4%nat.

Lemma futex_word_size_nat_ok : Z.of_nat FUTEX_WORD_SIZE_nat = FUTEX_WORD_SIZE.
Proof. reflexivity. Qed.

(** FUTEX_WAIT with FUTEX_PRIVATE_FLAG and no timeout: -EAGAIN when the
    word does not hold [val], and a decline when it does.

    [futex_wait_setup] (kernel/futex/waitwake.c) reads the word AFTER
    [get_futex_key] and compares it before it queues anything:

        ret = futex_get_value_locked(&uval, uaddr);
        ...
        if (uval != val) { futex_q_unlock(hb); return -EWOULDBLOCK; }

    and -EWOULDBLOCK IS -EAGAIN.  Every caller between that and the
    syscall boundary passes the value through unchanged — [__futex_wait]
    returns it before [futex_do_wait], and [futex_wait] returns it
    untouched when [to] is NULL.  So this arm is not an approximation of
    a wait: it is the branch on which Linux never waits, and the value
    test is what separates it.

    THE MATCHING CASE DECLINES, and that is the honest answer rather
    than a gap grudgingly left.  Once [uval == val] the caller is queued
    and [futex_do_wait] blocks in [schedule()]; the two things that
    could end it are a wake from another task and a timer, and the model
    has neither (the header argues the first, and this arm requires a
    NULL timeout).  There is no step that resumes it, so no outcome to
    admit — including the "returns 0 spuriously" one, which
    [__futex_wait] reaches only after [futex_unqueue] finds the entry
    gone, i.e. after some task really did wake it.

    A NON-NULL TIMEOUT IS DECLINED BEFORE ANY OF THIS, at [futex_spec].

    THE READ IS A COPY-IN.  [futex_get_value_locked]
    (kernel/futex/waitwake.c) is a [get_user]-class fetch of the four
    bytes at [uaddr], and it has happened on both the -EAGAIN arm and
    the declining one, so [record_copyins] wraps the whole [Some uval]
    arm.  The [None] arm carries no ledger and answers no errno: a word
    the model cannot read is one Linux would fault on
    ([futex_wait_setup] retries through [get_user] and returns its
    error), but the model's memory is a partial map rather than the
    kernel's page tables, so an absent byte is an absent FACT and this
    fails closed — the convention [Kernel.Time.Hrtimer.nanosleep_spec]
    states for its own request buffer. *)
Definition futex_wait_private_spec (uaddr val : word) : Sys SyscallEffect :=
  futex_key_check uaddr
    (i <- input ;;
     match read_bytes_map (in_mem i) uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) with
     | None => unmodeled   (* the word is not readable: fail closed *)
     | Some uval =>
         record_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
           (if bv_eqb (le_bytes_to_word uval) val
            then unmodeled   (* the caller would block, and nothing wakes it *)
            else err_ret EAGAIN)
     end).

(** The op word decides everything, and it is tested WHOLE.

    THE TEST IS ON THE FULL 64-BIT REGISTER, which is stricter than the
    kernel's own reading and deliberately so, exactly as
    [Kernel.Fork.clone_fork_flags_b] is.  [SYSCALL_DEFINE6(futex)]
    declares [int, op] (kernel/futex/syscalls.c), so Linux discards
    everything above bit 31 and a register of 0x1_00000081 is a private
    wake to it.  Declining is the fail-closed direction: the model
    refuses a call it could have answered rather than answering one it
    should not.  Nothing musl issues sets those bits — [__wake] and
    [__wait] (src/thread/__wait.c) build the word from
    [FUTEX_WAKE]/[FUTEX_WAIT] and [FUTEX_PRIVATE] alone.

    WHAT THE TWO WORDS EXCLUDE, and why each exclusion is a decline
    rather than an omission:

    - THE SHARED SPELLINGS, [FUTEX_WAKE] and [FUTEX_WAIT] with the
      private bit clear.  [futex_to_flags] (kernel/futex/futex.h) then
      sets [FLAGS_SHARED] and [get_futex_key] takes the page-resolving
      path, whose key can be one another process holds — so neither the
      empty waiter set nor the "-EFAULT is only the range verdict" claim
      survives, and both are load-bearing above.
    - [FUTEX_CLOCK_REALTIME] on either word.  [do_futex] tests
      [FLAGS_CLOCKRT] BEFORE its switch and permits the bit on only
      [FUTEX_WAIT_BITSET], [FUTEX_WAIT_REQUEUE_PI] and [FUTEX_LOCK_PI2],
      so a wake carrying it is -ENOSYS however well-formed the rest of
      the call is.  A spec that masked the op with [FUTEX_CMD_MASK] and
      threw the residue away would answer 0 there.
    - EVERY OTHER COMMAND.  The bitset forms take the caller's [val3]
      and so have an -EINVAL this spec does not model; [FUTEX_WAKE_OP]
      WRITES to [uaddr2] through [futex_atomic_op_inuser] before it
      looks at a waiter; the requeue and PI families need a second key,
      a lock word, or a waiter that exists.  All fall to [unmodeled],
      which is where [do_futex]'s own [default: return -ENOSYS;] also
      lives — and the model does not answer -ENOSYS for them, because
      the number IS in the kernel's table and the decline is this
      model's, not Linux's.

    THE TIMEOUT ARGUMENT IS ONLY READ FOR A WAIT, which is the kernel's
    asymmetry rather than a shortcut.  [SYSCALL_DEFINE6(futex)] fetches
    it under [if (utime && futex_cmd_has_timeout(cmd))], and
    [futex_cmd_has_timeout] (kernel/futex/syscalls.c) lists
    [FUTEX_WAIT], [FUTEX_LOCK_PI], [FUTEX_LOCK_PI2],
    [FUTEX_WAIT_BITSET] and [FUTEX_WAIT_REQUEUE_PI] — not [FUTEX_WAKE].
    So for a wake the third argument is dead, and gating on it would
    decline the very calls this arm exists for: musl's [__wake] and
    glib's uncontended broadcast both issue a three-argument
    [__syscall], leaving argument 3 whatever the register held.  A
    non-NULL [utime] on a WAIT reaches [get_timespec64] and
    [futex_init_timeout], which have an -EFAULT and an -EINVAL of their
    own AHEAD of everything above, and then arms a timer whose
    -ETIMEDOUT this model has no clock to produce; so it declines.

    Arguments 4 and 5 ([uaddr2] and [val3]) are read for neither word:
    [do_futex] overwrites [val3] on both arms and passes [uaddr2] only
    to commands outside them. *)
Definition futex_spec (uaddr op val utime : word) : Sys SyscallEffect :=
  if bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  then futex_wake_private_spec uaddr
  else if bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
  then (if negb (w_is0 utime) then unmodeled
        else futex_wait_private_spec uaddr (abi_low32 val))
  else unmodeled.

(** WHEN THE CALL READS USER MEMORY, as a predicate on the arguments
    alone.

    The copy-in ledger is not decoration: [Run.sstep_syscall] charges
    lazy anonymous backing against [vm_limit] for the ranges in it, and
    an empty ledger is independently a CLAIM — that the syscall read no
    user memory.

    This predicate answers the same question for [futex] as a
    definition, and
    [Checks.Sys.Kernel.Futex.Syscalls.futex_copyins_exact] proves it
    describes the ledger every answered call really carries.  So the tie is a theorem instead of a
    coincidence, which is what the mmap and mremap shape predicates buy
    with a shared definition and no lemma.

    IT IS A CONJUNCTION where the spec is a nest of ordered tests, and
    that costs nothing here because it is only ever read on an ANSWERED
    call: the two orderings differ on which of -EINVAL and -EFAULT wins,
    and neither of those arms reads anything. *)
Definition futex_wait_reads_b (uaddr op utime : word) : bool :=
  bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE) && w_is0 utime
  && futex_aligned_b uaddr && access_okb uaddr FUTEX_WORD_SIZE.

(** The two admitted op words are different words, so no call is both a
    wake and a wait.  Written out because the ledger argument below
    needs it and nothing else in this file does. *)
Lemma futex_wake_not_wait : forall op : word,
  bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE) = true ->
  bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE) = false.
Proof.
  intros op H. unfold bv_eqb in *.
  apply Z.eqb_eq in H. apply Z.eqb_neq. rewrite H. vm_compute. discriminate.
Qed.
