(** * LinuxProcessSem.Sys.Kernel.Signal — rt_sigaction (134), rt_sigprocmask (135), sigaltstack (132), tkill (130), tgkill (131)

    This file answers to Linux [kernel/signal.c]: it holds what the
    kernel defines there, and nothing else.  Which file a spec belongs
    in is therefore not a judgement call — look up where the kernel
    defines the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess.
(* [Kernel.Fork.SIGCHLD], the one signal number [sigchld_dfl_install]
   names; imported, not exported, so this module's namespace is
   unchanged for its importers. *)
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   rt_sigaction (134) — dispositions no modeled operation can consult
   ========================================================================= *)

(** WHY THIS IS SOUND, AND WHAT WOULD BREAK IT.

    The model has no signal delivery.  [Run.sstep] has no asynchronous
    transition, [State.event] has no signal constructor, and
    [State.Model] carries no disposition, mask or pending queue.  What it
    does have is [RiscvSemantics.MachineFault], which [Run.unmodeled_at]
    deliberately EXCLUDES from the coverage predicate on the grounds that
    "a real Linux process dies there too".  That justification is a claim
    about DISPOSITIONS: it holds only while no handler is installed for
    the signal the fault stands for.

    So a spec that lets [rt_sigaction] SUCCEED for a fault signal
    falsifies it, and the damage is not local.  A source could install a
    SIGSEGV handler, fault deliberately, and reach [Run.SError] on every
    execution; [Equivalence.bh_all_errors] would hold, the escape in
    [Equivalence.equiv] would admit an ARBITRARY target, and
    [Equivalence.modeled] would still be satisfied, because a fault is
    not [unmodeled].  The theorem would be true and say nothing, and
    nothing would notice.  On real Linux the handler runs and the
    process keeps going.

    This spec closes that by construction rather than by bookkeeping.
    No disposition is stored, and the accepted set is chosen so that
    none NEEDS to be.  What that takes is two things, and only one of them is
    the list below.

    WHAT SOUNDNESS ACTUALLY REQUIRES.  A no-op install is sound only if
    REALITY CANNOT RAISE THE SIGNAL AT ALL — not merely if no MODELED
    OPERATION can raise it.  Those are different conditions and the gap
    between them is exactly the accepted set: SIGINT and SIGTERM arrive
    only from outside the process, so both pass the operational test
    while reality could still deliver either.  If reality did, this spec
    would be wrong about a signal it ACCEPTS.  [State.event] is [ReadEv]/[WriteEv]/[ExitEv] only and
    the accepting arm is [ret_only 0] under the 24-byte copy-in of [act],
    recording no event and no disposition, so a source calling
    [sigaction(SIGTERM, &h, NULL, 8)] and a target that never calls
    [rt_sigaction] AT ALL have the same [Equivalence.bh_traces] wherever
    that copy-in's charge does not decide the budget, both satisfy
    [Equivalence.modeled], and [Equivalence.strong_equiv] can hold —
    while under a real SIGTERM the source runs [h] and continues and the
    target dies.

    THE OTHER HALF IS A PREMISE OF THE THEOREM, NOT A DERIVED FACT: THE
    ENVIRONMENT THE THEOREM QUANTIFIES OVER DELIVERS NO SIGNALS.
    [State.ProcInput] quantifies argv, envp, the file system and stdin
    and quantifies no signal source, and [Run.sstep] has no transition a
    signal could arrive on — so the premise is not stated as a hypothesis
    anywhere; it is built into the shape of the state machine, which is
    why it has to be written down in prose.  Without this spec it would be
    HARMLESS: if 134 fell through to [unmodeled], every covered
    binary would carry its inherited dispositions unchanged, and
    two such binaries would react identically to any outside signal whether
    the premise held or not.  Accepting an install is what
    makes the premise LOAD-BEARING.

    That tension is visible elsewhere in the model:
    [Random.getrandom_errnos] is [[EINTR]], justified there by a signal
    arriving while blocked on a large request — and an OBSERVABLE -EINTR
    requires a CAUGHT signal whose disposition lacks SA_RESTART, which is
    precisely what an accepted install here may be.  The two coexist
    only under the premise above.

    THE LIST BELOW IS THE OPERATIONAL HALF, AND IT IS NOT THE WHOLE
    ARGUMENT.  Read it as a necessary condition rather than a sufficient
    one: a disposition is accepted only for a signal that no modeled
    operation — machine step or syscall — can cause REALITY to raise.
    That test is about reality, not about the model: it is not enough
    that the model never raises the signal, because the model's silence
    is exactly what would be wrong.  A future reader widening the set is
    the person this warning is for — passing this test is not on its own
    grounds to add a signal, because a signal reality can deliver from
    outside still needs the premise, and the premise is only as good as
    the environments the theorem is applied to.

    Excluded, and the operation that excludes each — except the last,
    which is excluded ahead of the operation rather than by it:

      - SIGSEGV (11), SIGBUS (7), SIGILL (4), SIGTRAP (5) — every
        [MachineFault] site in [RiscvSemantics]: [EEbreak], the
        misaligned-atomic [EFault] and the defined-illegal
        [Sem.EDefinedIllegal] in [interp_eff], [ELoad]/[EStore]
        outside the view, [DecodeC.is_defined_illegal] in [decode_exec],
        and the odd-pc / unmapped / non-executable arms of
        [fetch_failure].
      - SIGPIPE (13) — a modeled [write], and the model RAISES it: the
        channel, pipe and socket arms of [ReadWrite.write_spec] send it
        through [ReadWrite.raise_sigpipe] when the far end has no
        reader.  That is exactly why it must stay off this list.  The
        model has one disposition for signal 13, SIG_DFL, and the
        launch premise above [Run.unmodeled_at] is what supplies it;
        an accepted [rt_sigaction] here would let a program install
        SIG_IGN or a handler and then take a write this spec answers as
        a death, which is a wrong MODELED answer.  It is out for
        SIGABRT's reason rather than for an absence, and that is the
        stronger of the two.
      - SIGXFSZ (25) — a modeled [write], and a modeled [ftruncate] as
        well: neither [ReadWrite.write_spec] nor [Open.ftruncate_spec]
        consults RLIMIT_FSIZE, where Linux raises SIGXFSZ alongside
        -EFBIG (the write path's [generic_write_check_limits],
        fs/read_write.c, when the position is already at or past the
        limit; [inode_newsize_ok], fs/attr.c, for a truncate).  Both
        skip that arm on exactly RLIM_INFINITY, which is a premise of
        the run rather than of the model: both calls that could lower it
        fail closed — prlimit64 because [Kernel.Sys.prlimit64_spec]
        covers RLIMIT_CORE and nothing else, setrlimit (164) because it
        has no arm.  The model itself cannot observe the limit that
        decides this, let alone rule it out.
      - SIGCHLD (17) — a child's exit.
        [Kernel.Fork.clone_resolve] has a succeeding arm, so a modeled
        syscall can make a child; the paragraph after the accepted
        list says more.

    Accepted: SIGINT (2), SIGTERM (15).  Both arrive only from outside
    the process, and nothing modeled sends a signal — [kill] (129) and
    [tgkill] (131) are both outside [modeled_sysnos], so a process
    cannot even signal itself.  [rt_sigprocmask] (135) IS modeled and
    does not disturb that: a mask decides DELIVERY, not sending, and
    what the premise below rules out is a signal arriving at all.

    TWO INSTALLS OUTSIDE THIS LIST ARE ANSWERED, AND NEITHER IS A NO-OP
    OF THE KIND THIS NOTE IS ABOUT.  Each sets SIG_DFL, the disposition
    the model already assumes for that signal, so neither rests on the
    signal being unraisable:
    - SIG_DFL FOR SIGABRT ([sigabrt_dfl_install]).  A modeled operation
      does raise SIGABRT ([tkill_self]), and the model delivers it at
      SIG_DFL.  After the install Linux has the disposition the model
      already assumes.  Every other SIGABRT install fails closed.
    - SIG_DFL FOR SIGCHLD ([sigchld_dfl_install]).  A child's exit
      raises SIGCHLD, and [Fork.clone_spec]'s argument that nothing
      comes of it is an argument about SIG_DFL, under which the signal
      is discarded when it is generated.  After the install that is the
      disposition.  Every other SIGCHLD install -- SIG_IGN, a handler --
      fails closed.

    SIGCHLD (17) IS NOT ACCEPTED, AND THAT IS THE INVARIANT BELOW
    BEING DISCHARGED.  That invariant says the
    change which GIVES THE MODEL A CHILD must take SIGCHLD out of this
    set.  A modeled [clone]/[clone3] parent side is
    that change — it is an admission that a child can exist — and so
    would be a modeled [wait4], which is an admission that one can be
    reaped.  An accepted set NARROWER than the operational test demands
    costs coverage and cannot cost soundness.  The SIG_DFL install
    above is not a member of the set: membership answers an install
    whatever its handler word, and SIGCHLD is answered for one handler
    word only.

    What it costs is the SIGCHLD install with a HANDLER, which the
    model declines: [sigaction(SIGCHLD, &act, NULL, 8)] with a reaping
    function, the shape dropbear uses.  A decline is not a wrong answer
    — it puts such a program outside the theorem's coverage rather than
    making a false claim about it.

    WHAT THE OPERATIONAL RULE NEVER ESTABLISHED IS THAT REALITY HAS NO
    SENDER.  This model begins AT [execve]: [State.ProcInput] carries
    argv, envp, the file system and stdin and nothing about the process
    that launched this one, so a source the theorem covers may already
    have a child, a parent or a terminal.  SIGINT and SIGTERM are in the
    accepted set on the strength of the PREMISE above — the environment
    delivers no signals — and not on the strength of the operational
    rule, which only narrows who could send it: "arrives only from
    outside the process" says the model cannot raise it, not that it is
    never raised.  That gap matters most for SIGCHLD, since
    a child survives [execve] and could raise a real one at any moment.
    The decline of every SIGCHLD handler and of SIG_IGN closes that
    instance rather than leaving it to the premise, and the one SIGCHLD
    install the model answers, SIG_DFL, does not reopen it: a real
    SIGCHLD arriving at SIG_DFL is discarded on arrival.  SIGINT and
    SIGTERM still need the premise in full.

    THE INVARIANT TO KEEP: this list is a claim about the REST of the
    model.  If a later change gives the model a timer, a controlling
    terminal, or any
    [kill]-shaped syscall, the corresponding signal must leave
    [sigaction_accepted] in the SAME commit — or better, in a commit
    AHEAD of it, so that no ordering of the
    two can open the window.  Adding delivery of any kind reopens the
    hole above outright.  And the premise is an invariant too: giving
    [State.ProcInput] a signal source, or [Run.sstep] a transition to
    deliver on, invalidates the accepted set WITHOUT touching a single
    modeled operation, so the operational list is not where such a change
    would announce itself. *)

(** The signal number is [int] ([SYSCALL_DEFINE4(rt_sigaction, int, sig,
    ...)], Linux v6.10-v6.15, kernel/signal.c, byte-identical across the
    window), so the kernel sees only the low half of the register — the
    same ABI truncation [fd32], [cmd32] and [whence32] apply, at the same
    boundary, in the arm that reads this syscall's arguments. *)
Definition sig32 (sig : word) : word := abi_low32 sig.

(** The signals whose disposition no modeled operation can consult AND
    which the theorem's signal-free environment therefore never delivers.
    BOTH halves are load-bearing, and the second is a premise rather than
    a fact about [rt_sigaction]: read the note above before touching this
    list.  Every other signal — the four fault signals above all, and
    SIGCHLD, because the model can have a child —
    fails closed at an install, with two exceptions that this list does
    not carry, both SIG_DFL: for SIGABRT, which [sigabrt_dfl_install]
    admits, and for SIGCHLD, which [sigchld_dfl_install] admits. *)
Definition sigaction_accepted (sig : word) : bool :=
  let s := bv_unsigned sig in
  (Z.eqb s 2 || Z.eqb s 15)%bool.

(** [do_sigaction] rejects a signal outside 1..[_NSIG]: [valid_signal]
    widens the [int] to [unsigned long], so a negative one becomes a huge
    value and fails the [sig <= _NSIG] bound, and an explicit [sig < 1]
    catches 0.  [_NSIG] is 64 on riscv64 (include/uapi/asm-generic/signal.h),
    which is what this model needs — it is not universal, mips defines
    128 — and the bound is INCLUSIVE: 64 is a valid signal, 65 is
    -EINVAL.  Applied to the
    already-truncated low half, an unsigned 1..64 test is exactly that
    predicate.  Note [rt_sigaction] differs from [kill] here: [kill]
    accepts signal 0 as a permission probe — [group_send_sig_info] runs
    the permission check and then skips delivery under [if (!ret && sig)]
    — while [rt_sigaction]'s [sig < 1] refuses it. *)
Definition sig_valid (sig : word) : bool :=
  let s := bv_unsigned sig in ((1 <=? s)%Z && (s <=? 64)%Z)%bool.

(** [sig_kernel_only] (include/linux/signal.h): SIGKILL and SIGSTOP can
    be neither caught nor ignored, so [do_sigaction] answers -EINVAL for
    them — but only when [act] is non-NULL.  With nothing to install the
    same call is a plain 0. *)
Definition sig_kernel_only (sig : word) : bool :=
  let s := bv_unsigned sig in (Z.eqb s 9 || Z.eqb s 19)%bool.

(** The [sa_flags] bits whose entire meaning is HOW a signal reaches a
    handler, or how a child's stop is reported.  Neither can happen, so
    an install carrying them is still a no-op:

      SA_NOCLDSTOP      0x00000001   SA_NOCLDWAIT 0x00000002
      SA_SIGINFO        0x00000004   SA_EXPOSE_TAGBITS 0x00000800
      SA_ONSTACK        0x08000000   SA_NODEFER   0x40000000
      SA_RESETHAND      0x80000000

    That is [UAPI_SA_FLAGS] (include/linux/signal_types.h), which is
    0xD8000807, minus SA_RESTART, on an architecture whose
    [__ARCH_UAPI_SA_FLAGS] is 0: riscv defines no SA_RESTORER, so it has
    neither that flag nor an [sa_restorer] field.

    SA_RESETHAND is accepted here but IS NOT REACHABLE THROUGH MUSL, so
    do not read its presence as coverage of a musl caller.  musl's
    [struct sigaction] declares [sa_flags] as an [int] (include/signal.h)
    and [__libc_sigaction] (src/signal/sigaction.c) assigns it straight
    into the [unsigned long] flags of [struct k_sigaction] —
    [ksa.flags = sa->sa_flags] — so the bit-31 value SIGN-EXTENDS and
    the kernel is handed 0xFFFFFFFF80000000.

    THE MUSL WINDOW IS v1.2.4-v1.2.6, and it is a bound rather than a
    formality.  Before v1.2.4, arch/riscv64/bits/signal.h defined
    SA_RESTORER as 0x04000000 and musl OR'd it into every [sigaction]
    call; that bit is outside [UAPI_SA_FLAGS], so [sa_flags_ok] would
    decline EVERY musl sigaction on those versions — a plain
    [sigaction(SIGTERM, &act, NULL)] — the modeled shape — included.
    musl commit 269d1938 (2023-02-09, "fix wrong sigaction syscall ABI
    on mips*, or1k, microblaze, riscv64") deleted the define, and v1.2.4
    is the first release carrying it.  src/signal/sigaction.c is identical
    at v1.2.4, v1.2.5 and v1.2.6.
    Linux answers 0 to that ([sa_flags &= UAPI_SA_FLAGS] drops bits
    32-63, leaving exactly SA_RESETHAND), while this spec sees those bits
    and fails closed, which is the SAFE direction: a decline where the
    kernel gives an answer.  The flag is therefore reachable only from a
    raw [syscall(SYS_rt_sigaction, ...)].

    Deliberately NOT here, each for its own reason:

      - SA_RESTART 0x10000000 is the one retained flag that changes a
        SYSCALL's return value rather than a delivery — it asks for an
        interrupted call to be restarted instead of returning -EINTR —
        and the model HAS a syscall that can return -EINTR:
        [Random.getrandom_errnos], whose short-delivery arm is justified
        by a signal arriving mid-request.  The model has no notion of
        restart, so SA_RESTART is unmodeled: fail closed.
      - every bit outside [UAPI_SA_FLAGS].  [do_sigaction] silently MASKS
        those away ([act->sa.sa_flags &= UAPI_SA_FLAGS]) rather than
        rejecting them, so answering 0 WOULD be sound — and not only
        today: [UAPI_SA_FLAGS] arrived in v5.11 already containing
        SA_EXPOSE_TAGBITS, together with the masking line, and its body
        is byte-identical from v5.11 to v6.17.  So this is NOT an
        argument about a moving constant.  The model declines anyway,
        because fail-closed is the default for a shape nothing needs:
        no real caller sets a bit outside the mask, so nothing is lost
        by not deciding what Linux does with it, and deciding would put
        a kernel constant the model otherwise never consults inside the
        modeled surface.

    musl's [signal()] wrapper sets SA_RESTART and passes a non-NULL
    [oldact], so it fails closed here twice over.  A direct
    [sigaction(sig, &act, NULL)] is the shape that is modeled, for a
    signal in [sigaction_accepted].  dropbear's install has that shape
    and names SIGCHLD, so it fails closed on the SIGNAL instead. *)
Definition sa_flags_accepted : Z := 0xC8000807%Z.

Definition sa_flags_ok (fl : word) : bool :=
  Z.eqb (Z.ldiff (bv_unsigned fl) sa_flags_accepted) 0.

(** The kernel's [struct sigaction] on riscv64 is [sa_handler](8) at 0,
    [sa_flags](8) at 8, [sa_mask](8) at 16 — 24 bytes, with NO
    [sa_restorer] field.  The struct the kernel compiles is the one in
    include/linux/signal_types.h (the [struct sigaction] in
    include/uapi/asm-generic/signal.h sits under [#ifndef __KERNEL__] and
    is not it), and its [sa_restorer] member is guarded by
    __ARCH_HAS_SA_RESTORER, which include/uapi/asm-generic/signal.h
    defines only under a SA_RESTORER that asm-generic never defines.
    riscv ships neither an [asm/signal.h] nor a [uapi/asm/signal.h] of
    its own, so it defines no SA_RESTORER, and both the field and
    [__ARCH_UAPI_SA_FLAGS] vanish.

    The size is load-bearing rather than incidental — musl's own
    [struct k_sigaction] for this architecture is 32 bytes, so a spec
    that read 32 would answer -EFAULT where Linux answers 0.  The extra 8
    bytes are TRAILING SLACK ONLY FROM musl v1.2.4.  Before that the 32
    bytes were handler, flags, [sa_restorer], mask, and the kernel read
    the restorer pointer at offset 16 as [sa_mask] — the very bug musl
    269d1938 fixed.  The -EFAULT argument survives either way, since
    32 >= 24; the characterisation does not, so it is bounded to the
    window the rest of this note uses.

    [SYSCALL_DEFINE4(rt_sigaction)] copies the whole struct with one
    [copy_from_user] before [do_sigaction] runs, so readability is
    all-or-nothing and -EFAULT precedes every -EINVAL [do_sigaction]
    would raise.  It does NOT precede the [sigsetsize] -EINVAL, which the
    syscall entry raises before the copy — arm 1 below — and the [oact]
    [copy_to_user] runs after [do_sigaction], so a bad [oact] with a bad
    [sig] is -EINVAL rather than -EFAULT.  This returns [sa_flags]
    exactly when [access_ok] admits all 24 bytes and they are readable.

    THE RANGE TEST IS ASKED, through [State.copy_bytes_map], rather than
    argued away.  [SYSCALL_DEFINE4(rt_sigaction)] (kernel/signal.c) reads
    the struct with [copy_from_user] before [do_sigaction] runs, and that
    is [access_ok] over all 24 bytes before a byte moves
    (include/linux/uaccess.h, [_inline_copy_from_user];
    include/asm-generic/access_ok.h, [__access_ok]; riscv overrides
    [access_ok] for pointer masking but not [__access_ok], see
    [State.TASK_SIZE]).  This note used to give two reasons for leaving
    the test out, and only one of them holds.  The WRAP half holds in a
    run, for a reason other than the one it gave: completing a wrap
    needs a mapped byte at 2^64-1 and one at 0, and
    [Equivalence.image_brk_satisfiable], a hypothesis of the IMAGE_WF
    ascription, bounds every loaded segment's end below 2^64.  The
    [TASK_SIZE] half does not hold.  That hypothesis bounds the image at
    2^64 and not at 2^47, and [Run.valid_brk] asks only that the break
    sit at or above the image's top, so an admissible image may carry a
    LOAD segment above the user limit whose bytes reach this spec through
    [in_mem] ([Run.sys_input]); and [Checks.ExecutableSpecs.check_syscall]
    takes an arbitrary [SyscallInput] besides.  A wholly readable range
    above [TASK_SIZE] therefore exists, the bare walk answered the call
    on it, and Linux answers -EFAULT.  The wrap itself is
    [State.copy_bytes_map]'s note and is not repeated here.

    For a signal in [sigaction_accepted] the flags word is the only field
    the model consults.  The handler (SIG_DFL, SIG_IGN or an address) and
    [sa_mask] describe delivery, which cannot occur for those signals, so
    their values change nothing — and for the same reason the kernel's two
    silent side effects here are unobservable: [sigdelsetmask] clearing
    SIGKILL and SIGSTOP from the stored mask, and the POSIX 3.3.1.3 flush
    of pending signals ([sig_handler_ignored] then [flush_sigqueue_mask])
    when the new disposition ignores them.  The model has neither a stored
    mask nor a pending queue for those signals, and [oact] — declined
    below — is the only window onto either.  The handler word is read
    once, by [sigaction_handler], and only for SIGABRT; see
    [sigabrt_dfl_install]. *)
Definition sigaction_flags (mp : word -> option byte) (act : word)
    : option word :=
  match copy_bytes_map mp act 24 with
  | Some _ => read_u64 mp (bv_add act (Z_to_bv 64 8))
  | None => None
  end.

(** [sa_handler], the eight bytes at offset 0 of the struct above, under
    the same range test and all-or-nothing readability as
    [sigaction_flags]: SIG_DFL is 0 and SIG_IGN is 1
    (include/uapi/asm-generic/signal-defs.h); any other value is the
    address of a handler. *)
Definition sigaction_handler (mp : word -> option byte) (act : word)
    : option word :=
  match copy_bytes_map mp act 24 with
  | Some _ => read_u64 mp act
  | None => None
  end.

(** The one install outside [sigaction_accepted] that the spec answers:
    SIG_DFL for SIGABRT.  musl's [abort] makes it on its second path
    (src/exit/abort.c, musl 1.2.6:
    [__syscall(SYS_rt_sigaction, SIGABRT,
    &(struct k_sigaction){.handler = SIG_DFL}, 0, _NSIG/8)]), which it
    takes when [raise(SIGABRT)] returns — in this model, when the signal
    mask at the call already blocks SIGABRT: the launch mask, or a mask
    the program installed with [rt_sigprocmask] (see [sigabrt_blocked]).

    WHY 0, AND NO STATE.  Linux answers 0 here: SIGABRT is in 1..64 and
    is not SIGKILL or SIGSTOP, and no live process has SA_IMMUTABLE set
    (see the note at [rt_sigaction_spec]).  Linux changes two things, and
    the model needs neither:

      - the disposition becomes SIG_DFL.  That is the disposition
        [tkill_self] delivers SIGABRT against ("WHY SIGABRT'S
        DISPOSITION IS SIG_DFL, BY CONSTRUCTION", below).  So after the
        call Linux is in the state the model assumes, also when the
        launcher left an inherited SIG_IGN ([execve]'s
        [flush_signal_handlers] keeps SIG_IGN; arm 2 of
        [rt_sigaction_spec]).
      - a pending SIGABRT is NOT discarded.  [do_sigaction] flushes the
        pending signal only when [sig_handler_ignored] holds for the new
        handler: SIG_IGN, or SIG_DFL for a signal whose default action is
        to ignore it ([sig_kernel_ignore]: SIGCONT, SIGCHLD, SIGWINCH,
        SIGURG).  SIGABRT's default action dumps core, so a pending
        SIGABRT stays pending, as [State.procst_sigabrt_pending] keeps it
        (kernel/signal.c, [do_sigaction] and [sig_handler_ignored];
        include/linux/signal.h; Linux v6.18.46, commit 1f99e9ab748f).

    [sa_flags] and [sa_mask] describe how a handler runs, and SIG_DFL
    runs none, so neither is read here; [sa_flags_ok] has already
    declined SA_RESTART and every bit outside [sa_flags_accepted].

    WHAT STAYS DECLINED: SIGABRT with any other handler word, SIG_IGN or
    an address.  Either would change what [tkill_self] must do, and the
    model has one answer for SIGABRT.  [sig] arrives as [sig32] made it;
    at this arm it is in 1..64, so [bv_unsigned sig] is the signal
    number. *)
Definition sigabrt_dfl_install (sig : word) (mp : word -> option byte) (act : word)
    : bool :=
  Z.eqb (bv_unsigned sig) SIGABRT &&
  match sigaction_handler mp act with
  | Some h => w_is0 h
  | None => false
  end.

(** The second install outside [sigaction_accepted] that the spec
    answers: SIG_DFL for SIGCHLD, under a flag word [sa_flags_ok]
    admits.  bwrap 0.13.1 makes it first thing in [main]
    ([struct sigaction sa = {}; sa.sa_handler = SIG_DFL;
    sigaction(SIGCHLD, &sa, NULL)], to undo a SIG_IGN its launcher may
    have left); musl passes that as [rt_sigaction(SIGCHLD, act, NULL,
    8)] with a zero flag word.

    kernel/signal.c [SYSCALL_DEFINE4(rt_sigaction)], [do_sigaction], [sig_handler_ignored], [do_notify_parent], read at v6.18.44; identical at v6.18.46.
    include/linux/signal.h [SIG_KERNEL_IGNORE_MASK], [sig_kernel_ignore], read at v6.18.44; identical at v6.18.46.

    WHY 0.  SIGCHLD (17) is in 1..64 and is not SIGKILL or SIGSTOP, and
    no live process carries SA_IMMUTABLE (the note at
    [rt_sigaction_spec]), so [do_sigaction] stores [*act] and returns 0,
    and with [oact] NULL so does the syscall.

    WHY NO STATE.  After the call SIGCHLD's disposition is SIG_DFL, and a
    SIG_DFL SIGCHLD is the disposition every SIGCHLD argument in this
    model is written against, so the install moves the process TOWARDS
    the model's assumption rather than away from it:
    - [Fork.clone_spec]'s header argues that the SIGCHLD a child's exit
      sends comes to nothing because it is discarded at generation:
      [sig_handler_ignored] holds for SIG_DFL on a signal in
      [SIG_KERNEL_IGNORE_MASK], SIGCHLD is in that mask, and
      [__send_signal_locked] skips the queue.  After this install that
      is certain; before it, the disposition is the launch's -- SIG_DFL,
      or a SIG_IGN [execve] kept -- and both discard.
    - [do_sigaction] itself flushes a pending SIGCHLD here, because
      [sig_handler_ignored(SIG_DFL, SIGCHLD)] holds (POSIX 3.3.1.3).
      The model carries no SIGCHLD queue, and a queued SIGCHLD would
      have been discarded at delivery anyway ([get_signal] finds
      SIG_DFL and [sig_kernel_ignore]), so nothing observable moves.
      [posixtimer_sig_unignore] is not reached: it runs only when the
      new handler is NOT ignored.
    - Of the flags [sa_flags_ok] admits, two are read for SIGCHLD.
      SA_NOCLDSTOP stops a child's STOP from raising SIGCHLD, which
      SIG_DFL discards anyway.  SA_NOCLDWAIT makes [do_notify_parent]
      autoreap an exiting child, which changes what a later [wait4]
      finds -- but [Exit.wait4_spec] answers only while
      [State.m_has_children] is false, when there is no child to reap,
      and declines once a modeled [clone] has recorded one.  The rest
      ([sa_mask], SA_SIGINFO, SA_ONSTACK, SA_NODEFER, SA_RESETHAND,
      SA_EXPOSE_TAGBITS) describe how a handler runs, and SIG_DFL runs
      none.

    WHAT STAYS DECLINED: SIGCHLD with SIG_IGN or a handler address.  A
    handler is unsound outright: it would run on each child's exit, and
    could interrupt a modeled call with an -EINTR or a restart this
    model does not have.  SIG_IGN discards as SIG_DFL does, but it also
    autoreaps every child and is the one disposition [execve] passes on
    ([flush_signal_handlers] keeps it), so admitting it would have to be
    argued against every child-facing arm; nothing in scope needs it,
    and declining it keeps the disposition after any answered SIGCHLD
    install exactly the SIG_DFL named above.  The tripwire is
    [Checks.Cases.Kernel.Signal.rt_sigaction_sigchld_unmodeled]. *)
Definition sigchld_dfl_install (sig : word) (mp : word -> option byte) (act : word)
    : bool :=
  Z.eqb (bv_unsigned sig) SIGCHLD &&
  match sigaction_handler mp act with
  | Some h => w_is0 h
  | None => false
  end.

(** [rt_sigaction sig act oact sigsetsize].  [sig] arrives already
    truncated (see [sig32]).  The arms follow the kernel's own order
    (Linux v6.10-v6.15, kernel/signal.c, [SYSCALL_DEFINE4(rt_sigaction)]
    then [do_sigaction]).  The syscall body is byte-identical across that
    window.  [do_sigaction] changes TWICE in it, both in v6.13, and
    neither moves an answer here: the [posixtimer_sig_unignore] path is
    reachable only through POSIX timers, which are not modeled, and
    [flush_sigqueue_mask] gains a task argument and frees through
    [sigqueue_free_ignored], which diverges from [__sigqueue_free] only
    for preallocated POSIX-timer sigqueue entries.

    NO STABLE-BRANCH EXCLUSIONS.  Both functions are byte-identical
    between each mainline tag and the head of its stable branch across
    linux-6.10.y through linux-6.15.y, and no backport crosses the
    window.  Stated because other windows in this model do have such
    exclusions, so silence here would be ambiguous.

    The arms:

      1. [sigsetsize != sizeof(sigset_t)] is -EINVAL before anything else
         is looked at, and [sizeof(sigset_t)] is 8 on a 64-bit kernel
         ([_NSIG] 64 over a 64-bit [_NSIG_BPW], one word).  So a bad size
         beats a wild [act] pointer.
      2. a non-NULL [oact] is UNMODELED.  The kernel writes the PREVIOUS
         disposition there, and the model stores none — nor could it
         honestly answer from a fixed initial state, since [execve]'s
         [flush_signal_handlers] preserves an inherited SIG_IGN, making
         the initial disposition a choice of the launching environment
         rather than a constant.  [State.ProcInput] quantifies argv,
         envp, the file system and stdin; it does not quantify that.
         Declining is the only sound arm, and it also removes the
         kernel's nastiest corner here: a [copy_to_user] fault on [oact]
         returns -EFAULT with the new disposition ALREADY installed and
         not rolled back.
      3. with [act] NULL nothing is installed, so the call is a pure
         no-op for EVERY valid signal, fault signals included: 0, or
         -EINVAL outside 1..64.  This is also why SIGKILL and SIGSTOP are
         only rejected in arm 4.
      4. with [act] non-NULL: -EFAULT unless [access_ok] admits all 24
         bytes and they are readable;
         then -EINVAL for an out-of-range signal and for SIGKILL/SIGSTOP;
         then fail closed on SA_RESTART and on any bit outside
         [sa_flags_accepted]; then 0 for a signal in
         [sigaction_accepted], storing no disposition; then 0 for SIGABRT
         with the handler SIG_DFL ([sigabrt_dfl_install]), storing no
         disposition; then 0 for SIGCHLD with the handler SIG_DFL
         ([sigchld_dfl_install]), storing no disposition; and UNMODELED
         for every other signal and handler.
         Every answer after the copy records the 24
         bytes in [State.eff_copyins]: [SYSCALL_DEFINE4(rt_sigaction)]
         (kernel/signal.c:4650, v6.18.46) has already read them with
         [copy_from_user], and [State.materialize_model_accesses] charges
         a lazy anonymous page the read faults in.  The -EFAULT records
         nothing, the convention [rt_sigprocmask_spec] states.

    Arm 4's last case is the one that matters: it is what keeps a
    SIGSEGV, SIGILL, SIGBUS or SIGTRAP handler out of the modeled
    surface, and with it the [MachineFault] vacuity described above.

    One -EINVAL the model does not reproduce: [do_sigaction] also
    refuses when the EXISTING action carries SA_IMMUTABLE.  That bit is
    set only by [force_sig_info_to_task] under HANDLER_EXIT — a path
    that terminates the process — so no surviving process can present it,
    and a fresh process starts with every FLAG WORD zero, which is the
    half this argument needs.  Not every disposition: [execve]'s
    [flush_signal_handlers] (called as [flush_signal_handlers(me, 0)]
    from [begin_new_exec], fs/exec.c) resets caught handlers to SIG_DFL
    but PRESERVES an inherited SIG_IGN, which is exactly why the [oact]
    arm above declines rather than answering from a fixed initial
    state. *)
Definition rt_sigaction_spec (sig act oact ss : word) : Sys SyscallEffect :=
  if negb (bv_eqb ss (Z_to_bv 64 8)) then err_ret EINVAL
  else if negb (w_is0 oact) then unmodeled
  else if w_is0 act
  then (if sig_valid sig then ret_only (Z_to_bv 64 0) else err_ret EINVAL)
  else
    i <- input ;;
    match sigaction_flags (in_mem i) act with
    | None => err_ret EFAULT   (* [access_ok] refuses the struct, or it is not
                                  wholly readable: real -EFAULT *)
    | Some fl =>
        record_copyins [(act, 24%nat)]
        (if negb (sig_valid sig) then err_ret EINVAL
         else if sig_kernel_only sig then err_ret EINVAL
         else if negb (sa_flags_ok fl) then unmodeled
         else if sigaction_accepted sig then ret_only (Z_to_bv 64 0)
         else if sigabrt_dfl_install sig (in_mem i) act then ret_only (Z_to_bv 64 0)
         else if sigchld_dfl_install sig (in_mem i) act then ret_only (Z_to_bv 64 0)
         else unmodeled)         (* a signal a modeled operation can raise: fail closed *)
    end.

(* =========================================================================
   rt_sigprocmask (135) - a mask no modeled operation can observe
   ========================================================================= *)

(** WHICH KERNEL THIS IS A MODEL OF.

    Cited by function name rather than by line number.  Every function
    named here is BYTE-IDENTICAL across v6.1 - v6.17:

      kernel/signal.c         [SYSCALL_DEFINE4(rt_sigprocmask, ...)],
                              [sigprocmask], [__set_current_blocked],
                              [__set_task_blocked]
      include/linux/signal.h  [sigdelsetmask]

    NO STABLE-BRANCH EXCLUSIONS, and that is CHECKED rather than
    assumed: all five are byte-identical at the heads of linux-6.1.y,
    linux-6.6.y, linux-6.12.y and linux-6.17.y as well as at the release
    tags.

    The constants are in [Uapi.v] with their own citations: [SIG_BLOCK],
    [SIG_UNBLOCK], [SIG_SETMASK] and [NSIG_BYTES], the last of which is
    why this call reads exactly eight bytes.

    THE MASK IS STATE, AND ITS INITIAL VALUE IS AN INPUT.

    [State.ProcState] carries [procst_sigmask], and it has to, because
    this spec answers [oset]: the kernel writes the mask the process had
    ON ENTRY there, and a spec that invented a value would be inventing
    the one thing the call exists to report.

    WHERE THE ENTRY VALUE COMES FROM IS THE WHOLE DIFFICULTY, and the
    answer is that the model cannot derive it — so it does not.  Unlike
    a disposition the mask is not even partly reset at [execve]:
    [begin_new_exec] (fs/exec.c) calls [flush_signal_handlers], which
    walks [sighand->action] and touches [current->blocked] nowhere, and
    fs/exec.c does not mention [blocked] at all.  The starting mask is
    entirely a choice of the launching environment, so it arrives the
    way every other such choice does — as a field of
    [State.ProcInput], [in_sigmask], quantified once in
    [Equivalence.strong_universal_T] and SHARED between source and
    target.  That sharing is what keeps the equivalence intact: both
    binaries read the same entry mask back, so a read-back cannot
    separate two programs the relation should call equal.

    [Run.valid_sigmask] is the one constraint on it — SIGKILL and
    SIGSTOP clear — and the argument for it is an enumeration of the
    kernel's writers, not the one-liner it looks like; see that
    definition, which also says why the enumeration is the fragile
    kind.

    WHAT THE MASK IS STILL NOT: OBSERVABLE IN THE TRACE.  [State.event]
    is [ReadEv] / [WriteEv] / [ExitEv] only and [Run.sstep] has no
    asynchronous transition, so the mask reaches a trace exactly one
    way — through the eight bytes this call copies to [oset], like any
    other syscall's answer.  It adds nothing to the trace alphabet.

    QUANTIFY THAT OVER THE SPECS, NOT OVER THE SYSCALL NUMBERS.  The
    claim "no modeled syscall sends a
    signal" is FALSE, and falsely in the direction that matters:
    three numbers in [Sys.SyscallTable.spec_table] name kernel paths
    that really do send one.  [write] (64) and [writev] (66) reach
    [anon_pipe_write] (fs/pipe.c:431, v6.18.46), whose two
    [send_sig(SIGPIPE, current, 0)] calls (:462, :503) answer a pipe with
    no reader, and both also reach
    [generic_write_check_limits] (fs/read_write.c), which sends SIGXFSZ
    past RLIMIT_FSIZE; [ftruncate] (46) reaches [inode_newsize_ok]
    (fs/attr.c), which sends SIGXFSZ on the same limit before returning
    -EFBIG.

    WHICH SPECS RAISE ONE, AND WHICH ASSUMPTION COVERS THE REST.
    [write_spec] DOES raise signal 13, through
    [ReadWrite.raise_sigpipe], on each of its three arms whose far end
    has no reader, and this spec is what decides between the death and
    the -EPIPE: the mask is READ there.  What stays assumed rather
    than raised is SIGXFSZ: neither [write_spec] nor
    [ftruncate_spec] carries a file-size
    limit.  The
    RLIMIT_FSIZE half of the limit is a premise of the run —
    RLIM_INFINITY at exec, and the set fails closed, see
    [Open.ftruncate_spec] — and the [s_maxbytes] half, which the model
    does not carry either, raises no signal:
    [inode_newsize_ok]'s [out_big] and [generic_write_check_limits]'s
    [s_maxbytes] arm both return -EFBIG without a [send_sig].

    That distinction is not pedantry, because this spec WIDENS what
    those assumptions cost.  Blocking SIGXFSZ succeeds here and is
    RECORDED, and the model still gives one answer to two source
    programs whose real behaviour at the next over-limit [ftruncate]
    differs:
    unblocked the process dies on the signal, blocked it takes -EFBIG
    and runs on.  Under the RLIM_INFINITY premise no run reaches
    that ftruncate, but the model does not carry the premise.  So this
    file adds no wrong answer — the missing limit owns it, with or
    without this file — but it is a pair the
    equivalence relation cannot separate.  The obligation the invariant below states
    therefore binds those specs too: a file-size limit in
    [ftruncate_spec] would turn a blocked mask into something the model
    reads, and must give this spec state in the same commit.  The
    -EPIPE arm in [ReadWrite.write_spec] is the case that already
    happened, and it brought [State.procst_sigpipe_pending] and
    [sigmask_deliver_model]'s second branch with it.

    With that stated, [oset] is the ONLY window onto the mask that is
    open, and this spec is the only thing that writes one.  The list
    below is what stays shut, and it is worth keeping precisely because
    the mask is real: each of these, on landing, has to move
    [procst_sigmask] rather than merely answer, and the value [oset]
    hands back goes stale the moment one of them does not.

      - EVERY SYSCALL THAT READS [->blocked], INSTALLS A MASK, OR
        CAN DELIVER OR SEND A SIGNAL — the three above excepted, since
        their SPECS raise nothing — is outside [Specs.modeled_sysnos]
        entirely, so the dispatcher declines it before any of this is
        reached.  That is the claim; the numbers are examples of it, not
        the claim itself — [rt_sigsuspend] (133),
        [rt_sigpending] (136), [rt_sigtimedwait]
        (137), [rt_sigreturn] (139), [ptrace] (117), whose
        PTRACE_GETSIGMASK / PTRACE_SETSIGMASK read and write [->blocked]
        outright,
        [epoll_pwait2] (441), [io_pgetevents] (292) and
        [io_uring_enter] (426), which really do install a temporary
        [->blocked] — [set_user_sigmask] on the way in and
        [restore_saved_sigmask_unless] on the way out, in fs/select.c,
        fs/eventpoll.c, fs/aio.c and io_uring/io_uring.c.
        [set_user_sigmask] both READS the mask (it saves
        [current->blocked] into [current->saved_sigmask]) and installs
        one, so each is a read-back window and not merely a writer.
        [pselect6] (72), [ppoll] (73) and [epoll_pwait] (22) belong to
        that family and are handled in the bullet below instead, because
        they have arms.
        Then [signalfd4] (74), which does NOT:
        [do_signalfd4] (fs/signalfd.c) stores the set in the fd's own
        [ctx->sigmask], and fs/signalfd.c does not name [blocked]
        anywhere.  It is on this list as a DELIVERY window instead,
        because [signalfd_dequeue] calls [dequeue_signal] against that
        [ctx->sigmask], so a read of the fd hands back exactly the
        signals a blocked mask left pending.  Sampled at v6.1, v6.6,
        v6.12 and v6.17, not diffed across the whole window:
        [do_signalfd4] is NOT identical over those four — the fd lookup
        and the anon-inode call both changed — but the two statements
        this rests on are, with only [dequeue_signal]'s leading
        [current] argument dropped at v6.12.  Then [kill] (129),
        [tgkill] (131), [rt_sigqueueinfo] (138), [rt_tgsigqueueinfo] (240) and
        [pidfd_send_signal] (424), so a process cannot even signal
        itself.  Checked against [Sys.SyscallTable.spec_table]: none of
        them has an arm.
      - [rt_sigaction] (134), [pselect6] (72), [ppoll] (73),
        [epoll_pwait] (22) and [sigaltstack] (132) ARE on the modeled
        surface, and their windows are shut one level down instead.
        132 is the easy one, and is called out separately so the others
        are not read as the pattern: it has NO window to shut.
        [do_sigaltstack] (kernel/signal.c) reads and writes
        [sas_ss_sp], [sas_ss_size] and [sas_ss_flags] and names
        [blocked] nowhere, and [SYSCALL_DEFINE2(sigaltstack)] calls no
        [set_user_sigmask]; it is listed here only because it sits in
        this file's kernel source, which is not the same thing.  Checked
        by [Checks.Cases.Kernel.Signal]'s
        [sigaltstack_leaves_the_mask_alone] rather than by absence.
        134's is [oact], the only way to read an [sa_mask] back, and
        [rt_sigaction_spec] declines a non-NULL [oact] outright; the
        [sa_mask] an accepted install carries is not stored either —
        that spec answers [ret_only 0] and stores no disposition — so there is
        no second window behind the first.  72's is [set_user_sigmask]
        itself, and it is a real read-back: it saves [current->blocked]
        into [current->saved_sigmask] on the way in.  [Fs.Select]'s
        [pselect_sigpack] classifies a call that would install a mask as
        [PsSigReal] and [pselect6_outcome] answers [None] for it, and
        the error arms decided ahead of that are decided before
        [set_user_sigmask] runs in the kernel too, so no admitted
        pselect6 installs a mask.  22's window is the SAME
        [set_user_sigmask], reached from [do_epoll_pwait]
        (fs/eventpoll.c) rather than from [do_pselect], and
        [Fs.EventPoll]'s [epoll_sigmask] classifies a call that would
        install a mask as [EpSigReal], for which [epoll_pwait_outcome]
        answers [None].  Its error arms are decided ahead of that in the
        same sense: [set_user_sigmask] is the FIRST fallible step of
        [do_epoll_pwait], so the only errnos this model admits before it
        are the two that function itself returns, -EINVAL on a wrong
        [sigsetsize] and -EFAULT on an unreadable mask, neither of which
        installs anything.  73's is that same [set_user_sigmask] a third
        time, reached from [SYSCALL_DEFINE5(ppoll, ...)] with the mask
        pointer and its size as two arguments rather than through an
        argpack; [Fs.Select]'s [ppoll_sigmask] classifies an install as
        [PpSigReal] and [ppoll_outcome] answers [None] for it, and the
        only errnos admitted ahead of that are the timeout's, which the
        kernel raises before [set_user_sigmask] runs.  Every number on
        this bullet is checked rather than asserted, by
        [Checks.Cases.Kernel.Signal]'s
        [rt_sigaction_oact_read_back_declined],
        [pselect6_real_mask_declined],
        [epoll_pwait_real_mask_declined],
        [ppoll_real_mask_declined] and
        [sigaltstack_leaves_the_mask_alone]; do not move any of these
        numbers back into the bullet above, where the check is absence
        from [spec_table] and every one of them would fail it.  There is
        no count here on purpose: a written total is what goes stale
        when the bullet grows.
      - [clone] (220) and [clone3] (435) are deliberately NOT on that
        list, because their window is not closed by the same fact and
        stating it that way would rot.  A child inherits the mask, so an
        arm for either WOULD be a read-back window — if the child ran.
        It never does: [Run.sstep] has no transition that starts a
        second task, and a parent-side arm for these numbers does not
        add one, so there is no child to read the mask back whether or
        not 220 and 435 have an arm.  Do not derive this one from
        [spec_table]: both numbers have arms there, and the argument
        does not depend on them.

    So this spec is the sole reader and the sole writer of the mask it
    keeps, which is what makes a single field enough.

    WHY THERE IS NO ACCEPTED-SIGNAL LIST.  This is the question to ask
    of a spec that answers every mask, because the obvious worry is a
    program that blocks SIGSEGV and then executes a wild jump: if
    blocking made the fault survivable, [Run.unmodeled_at]'s exclusion
    of [RiscvSemantics.MachineFault] — which rests on a real process
    dying there too — would be wrong, and this spec would have to
    refuse the mask.

    BLOCKING CANNOT DO THAT.  A synchronous fault is delivered by
    [force_sig_info_to_task] (kernel/signal.c), which reads
    [blocked = sigismember(&t->blocked, sig)] and, when the signal is
    blocked, resets the disposition — [action->sa.sa_handler = SIG_DFL]
    — and removes the signal from the mask — [sigdelset(&t->blocked,
    sig)] — BEFORE calling [send_signal_locked].  A process that blocks
    SIGSEGV and then faults dies exactly as one that never blocked it.
    Those three statements are byte-identical across the whole
    v6.1 - v6.17 window even though the enclosing function is not:
    v6.8 deleted [recalc_sigpending_and_wake] and moved the wake-up out
    of the [if (blocked)] arm into a [task_sigpending] test after
    [send_signal_locked] (commit b454ec29225cda, "kernel/signal.c:
    simplify force_sig_info_to_task(), kill
    recalc_sigpending_and_wake()"), changing nothing any of the three
    does.

    THE PREMISE THIS SHARES WITH THE THEOREM: THE ENVIRONMENT DELIVERS
    NO SIGNALS.  Because this spec answers [oset], the premise costs
    an ANSWER and not only coverage: Linux has two writers of [->blocked] that no
    program calls, [signal_delivered] (kernel/signal.c), which ORs in
    [sa_mask] and adds the signal itself unless SA_NODEFER before
    [set_current_blocked], and riscv's [SYSCALL_DEFINE0(rt_sigreturn)]
    (arch/riscv/kernel/signal.c), which restores the mask from the
    sigframe.  Under a delivered signal the value this spec copies to
    [oset] would be the wrong number, not merely an unmodeled
    distinction.  The premise is written down above [Run.unmodeled_at].

    One tension this neither creates nor closes: [getrandom_errnos] is
    [[EINTR]], and a program that blocks every signal makes that errno
    unreachable in reality while the model still admits it.  Same
    premise, seen from the other side.

    THE INVARIANT TO KEEP.  It is a property rather than a list
    because a list only catches what someone thought to write down:
    THE MOMENT A SECOND READER OR WRITER OF THE MASK LANDS, IT MUST
    MOVE [procst_sigmask] IN THE SAME COMMIT — because this spec
    commits to a VALUE, and a writer that does not update the field
    makes that value silently wrong rather than merely incomplete.
    Signal delivery of any kind is the obvious one.  So is any of the
    numbers enumerated above, and so is relaxing [Fs.Select]'s
    [PsSigReal] decline, which is the only such window inside
    [Specs.modeled_sysnos] today.  The reader that used to be named
    here as the one that would not announce itself -- an -EPIPE arm in
    [ReadWrite.write_spec] -- HAS LANDED, and it announced itself
    exactly as this paragraph asked: SIGPIPE blocked turns a write to a
    far end with no reader from process death into a return of -EPIPE,
    so the three write arms read the mask through
    [Uapi.sigpipe_blocked] at a call this model answers, and
    [State.procst_sigpipe_pending] records what the block left behind.
    [sigmask_deliver_model] above is the writer that pairs with it:
    the install that uncovers signal 13 kills there, in the same way
    the SIGABRT branch does, so [oset]'s value stays the value of a
    mask the next reader will agree with. *)

(** [how] is [int] ([SYSCALL_DEFINE4(rt_sigprocmask, int, how, ...)]),
    so the kernel sees only the low half of the register and
    [sigprocmask]'s [switch (how)] compares that half against
    [SIG_BLOCK], [SIG_UNBLOCK] and [SIG_SETMASK].  Signedness does not
    enter: the switch tests equality against three non-negative
    constants, so an unsigned reading of the truncated half decides them
    identically.

    The narrowing itself is [Syscall.how32], beside [fd32], [whence32]
    and [cmd32] — the dispatcher applies it, as it does for those. *)
Definition how_valid (how : word) : bool :=
  let h := bv_unsigned how in
  (Z.eqb h SIG_BLOCK || Z.eqb h SIG_UNBLOCK || Z.eqb h SIG_SETMASK)%bool.

(** [copy_from_user(&new_set, nset, sizeof(sigset_t))] is all-or-nothing
    at the syscall boundary: any shortfall is -EFAULT and nothing is
    installed.  [sizeof(sigset_t)] is [Uapi.NSIG_BYTES] = 8, so this is
    readability of eight bytes and no more.

    THE RANGE TEST IS ASKED, through [State.copy_bytes_map], rather than
    argued away.  [SYSCALL_DEFINE4(rt_sigprocmask)] (kernel/signal.c)
    copies [nset] with [copy_from_user] and answers -EFAULT before
    [sigprocmask] runs, and [copy_from_user] is [access_ok] over the
    eight bytes and then the copy (include/linux/uaccess.h,
    [_inline_copy_from_user]; include/asm-generic/access_ok.h,
    [__access_ok]).  This note used to give two reasons for leaving the
    test out, and only the first survives.  The WRAP is impossible in a
    run, and the reason is [Equivalence.image_brk_satisfiable], a
    hypothesis of the IMAGE_WF module type each example's generated
    Checker ascribes: it bounds every loaded segment's end below 2^64,
    so no image supplies both a byte at 2^64-1 and one at 0
    ([State.alloc_top] and [State.sp_window_hi] bound only the mmap, brk
    and stack sources, not the ELF ROM image [in_mem] merges in).  The
    [TASK_SIZE] half is false.  That same hypothesis bounds the image at
    2^64, not at 2^47, and [Run.valid_brk] asks only that the break sit
    at or above the image's top, so an admissible image may carry a LOAD
    segment above the user limit whose bytes [Run.sys_input] hands to
    this spec; and [Checks.ExecutableSpecs.check_syscall] takes an
    arbitrary [SyscallInput] besides.  A wholly readable [nset] above
    [TASK_SIZE] therefore exists, the bare walk installed a mask from it,
    and Linux answers -EFAULT.  The wrap itself is
    [State.copy_bytes_map]'s note.

    THE CONTENTS ARE READ: the value
    decides what gets installed, so the test and the read are one
    [option].  This helper lives in this file rather than in
    [Sys/Uaccess.v]: it is the [sigset_t] ABI shape, not a uaccess
    policy, and one syscall uses it. *)
Definition sigset_at (mp : word -> option byte) (p : word) : option word :=
  match copy_bytes_map mp p NSIG_BYTES with
  | Some bs => Some (le_bytes_to_word bs)
  | None => None
  end.


(** [rt_sigprocmask how nset oset ss].  [how] arrives already truncated
    (see [Syscall.how32]).  The arms follow the kernel's own order
    ([SYSCALL_DEFINE4(rt_sigprocmask)] then [sigprocmask],
    kernel/signal.c, the window above):

      1. [sigsetsize != sizeof(sigset_t)] is -EINVAL before anything else
         is looked at — so a bad size BEATS A WILD [nset] POINTER, which
         is the pair a naive implementation gets backwards.  [sigsetsize]
         is [size_t] and is compared full-width: unlike [how] it does
         NOT truncate, so a register whose low half is 8 is still wrong.
      2. [old_set = current->blocked] is snapshotted HERE, before
         anything is installed, and it is this value — not the mask the
         call leaves behind — that [oset] receives.  The kernel takes it
         on the line after the size check and passes NULL as
         [sigprocmask]'s own [oldset], so the syscall never uses
         [sigprocmask]'s copy.  Reporting the post-install mask is the
         mistake a reimplementation makes, and
         [Checks.Cases.Kernel.Signal.rt_sigprocmask_oldset_is_not_the_new_mask]
         is what fails when someone makes it.
      3. with [nset] NULL nothing is installed — and, because
         [sigprocmask] is reached only from inside [if (nset)], [how] IS
         NEVER LOOKED AT.  An out-of-range [how] with a NULL [nset]
         therefore returns 0, not -EINVAL.  That is the ordering, not an
         oversight, and it is pinned by
         [Checks.Cases.Kernel.Signal].  The call is
         not a no-op even so: arm 5 still runs, so a query WRITES.
      4. with [nset] non-NULL: -EFAULT unless [access_ok] admits the 8
         bytes and they are readable,
         then SIGKILL and SIGSTOP are stripped from the new set
         ([sigmask_strip], silently — the call succeeds), then -EINVAL
         for a [how] outside {0, 1, 2}, then the install
         ([sigmask_apply]).
      5. with [oset] non-NULL the entry mask is copied out, LAST.  Two
         things follow that arms 1-4 do not prepare you for.  A bad
         [how] returns before this runs, so a rejected call leaves
         [oset] untouched.  And a fault HERE returns -EFAULT with the
         new mask already installed and NOT rolled back — the kernel's
         nastiest corner in this syscall, and the one obligation
         [Kernel.Sys.prlimit64_spec] avoids by declining both pointers
         at once.  This spec takes it on because here the install IS the
         call.  See [write_oset] for the three-way split of that arm and
         why the middle case declines.

    Every arm past the copy records the COPY-FROM-USER RANGE, and that is not
    bookkeeping: [Syscall.record_copyins] exists to distinguish two paths
    that return the same errno before and after a user-memory read, and
    this syscall has exactly such a pair — arm 1's -EINVAL is answered
    before [nset] is looked at, arm 4b's is answered after eight bytes
    have been copied.  An empty ledger on 4b would be a false claim that
    the call read no user memory, and [State.materialize_model_accesses]
    charges those ranges' lazy anonymous backing against
    [State.vm_limit], so omitting them also diverges from Linux at the
    allocation budget.  Arm 4a records nothing because the copy FAILED —
    the same convention as [Kernel.Sys.prlimit64_spec], whose -EFAULT
    arm is likewise outside its [record_copyins].  Say what that
    convention costs, since "the copy failed, so it read nothing" is not
    literally what the kernel does: with [nset] straddling a page
    boundary, riscv's [raw_copy_from_user] copies forward with exception
    fixups and really does fault in the first page before failing, so
    Linux charges it and this model does not.  The return value is
    -EFAULT either way; the divergence is one page of budget, in the
    under-charging direction [State.v] already names as the one that
    lets the model grant an allocation the kernel refuses, and it would
    show up at a later [mmap] or [brk], never here.  It is the
    established convention rather than anything this spec chose —
    [prlimit64_spec] and [Kernel.Time.Hrtimer.nanosleep_spec] have the
    same shape — so it is named here and not re-argued.

    Arm 4's success records the installed mask, so the two kernel
    side effects it touches part company.
    [sigdelsetmask]'s silent strip of SIGKILL and SIGSTOP IS modeled:
    the call still SUCCEEDS rather than answering -EINVAL — no
    [sig_kernel_only] test belongs in this spec, which is the opposite
    of [rt_sigaction] — but the stripped bits are observable at the
    next read-back, so dropping them is a wrong answer rather than an
    unobservable one.  [__set_task_blocked]'s [retarget_shared_pending]
    is not represented, and needs no representation: it has
    no second thread to retarget in a single-threaded model. *)
(** [sigdelsetmask(&new_set, sigmask(SIGKILL)|sigmask(SIGSTOP))]
    (kernel/signal.c, [SYSCALL_DEFINE4(rt_sigprocmask)]).  Applied to the
    set the caller supplied and to nothing else — the [old_set] snapshot
    taken one line earlier goes out through [oset] unfiltered, which is
    why this is a separate function rather than a filter on the field.

    Blocking SIGKILL is not an error.  The call returns 0 having quietly
    dropped the bits, and a later read-back through [oset] is the only
    way a program can tell.  Because this spec answers [oset], the
    strip needs modeling. *)
Definition sigmask_strip (w : word) : word :=
  bv_and w (Z_to_bv 64 (Z.lxor (Z.ones 64) sig_kernel_only_mask)).

(** [sigprocmask]'s [switch (how)], kernel/signal.c: [sigorsets] for
    SIG_BLOCK, [sigandnsets] for SIG_UNBLOCK, plain assignment for
    SIG_SETMASK.  [how] has already been checked by [how_valid], so the
    default arm here is unreachable rather than a fall-through — it
    repeats SIG_SETMASK's answer, and the guard is what makes that
    choice inert.  A reader tempted to widen [how_valid] must fix this
    together with it. *)
Definition sigmask_apply (how old new : word) : word :=
  if Z.eqb (bv_unsigned how) SIG_BLOCK then bv_or old new
  else if Z.eqb (bv_unsigned how) SIG_UNBLOCK then bv_and old (bv_not new)
  else new.

(** THE WHOLE-RUN HALF OF [Run.valid_sigmask], AS A CHECK RATHER THAN A
    SENTENCE.  That predicate constrains the mask a process is LAUNCHED
    with; what makes it a property of the whole run is that nothing this
    spec does can put either bit back, and that is a claim about this
    file's contents, so it is stated here and proved rather than
    asserted in prose.

    It is what the second of this development's three priorities rests
    on for this syscall: [oset] copies the mask out verbatim, so a
    reachable state with SIGKILL or SIGSTOP set would be a trace Linux
    cannot produce. *)
Definition mask_launchable (w : word) : Prop :=
  bv_and w (Z_to_bv 64 sig_kernel_only_mask) = Z_to_bv 64 0.

Lemma sigmask_strip_launchable : forall w, mask_launchable (sigmask_strip w).
Proof.
  intros w. unfold mask_launchable, sigmask_strip.
  apply bv_eq. rewrite !bv_and_unsigned, !Z_to_bv_unsigned by (cbv; lia).
  rewrite <- Z.land_assoc.
  replace (Z.land (Z.lxor (Z.ones 64) sig_kernel_only_mask)
                  sig_kernel_only_mask) with 0%Z by reflexivity.
  now rewrite Z.land_0_r.
Qed.

Lemma sigmask_apply_launchable : forall how old new,
  mask_launchable old -> mask_launchable new ->
  mask_launchable (sigmask_apply how old new).
Proof.
  intros how old new Hold Hnew. unfold mask_launchable in *.
  unfold sigmask_apply.
  destruct (Z.eqb (bv_unsigned how) SIG_BLOCK) eqn:Hb; cbv beta iota.
  { (* SIG_BLOCK: [sigorsets] -- neither operand carries the bits *)
    apply bv_eq in Hold, Hnew. apply bv_eq.
    rewrite bv_and_unsigned, bv_or_unsigned in *.
    rewrite Z.land_lor_distr_l, Hold, Hnew. reflexivity. }
  destruct (Z.eqb (bv_unsigned how) SIG_UNBLOCK) eqn:Hu; cbv beta iota.
  { (* SIG_UNBLOCK: [sigandnsets] only CLEARS, so the second operand is
       irrelevant and the proof does not look at it *)
    apply bv_eq in Hold. apply bv_eq.
    rewrite !bv_and_unsigned in *.
    rewrite <- Z.land_assoc, (Z.land_comm (bv_unsigned (bv_not new))),
            Z.land_assoc, Hold. reflexivity. }
  (* SIG_SETMASK: the value installed is the caller's, already stripped *)
  exact Hnew.
Qed.


(** The [oset] copy-out, which is the LAST thing the syscall does:

      if (oset) { if (copy_to_user(oset, &old_set, sizeof(sigset_t)))
                          return -EFAULT; }
      return 0;

    [old] is the mask the process had ON ENTRY, snapshotted before any
    install, so this is called with the entry mask on every arm that
    reaches it — including the one that has already changed the mask.

    [access_ok] IS TESTED BEFORE THE MEMORY WALK, AND THE ORDER IS THE
    POINT.  [copy_to_user] is [access_ok] then [raw_copy_to_user]
    (include/linux/uaccess.h), and [State.access_okb] is written as a
    subtraction in [Z] rather than a sum in 64-bit words, so it is the
    only thing here that sees a range wrapping the top of the address
    space.
    [State.read_bytes_map] walks in WORD arithmetic and wraps: an [oset]
    of 2^64-4 would find four bytes below the top and four at address 0
    and call the range writable, and the model would answer 0 with a
    write where [__access_ok] refuses outright.  Testing the walk first
    and [access_ok] second is a real bug wearing this arm's shape.

    THE THIRD CASE IS WHY THIS IS NOT JUST TWO ARMS.  A destination that
    passes [access_ok] but is not wholly writable is DECLINED, not
    -EFAULT, because Linux's answer there is not only an errno: riscv's
    [raw_copy_to_user] copies forward with exception fixups, so an
    [oset] straddling a page boundary with only the first page writable
    really does store those bytes before faulting.  The return is
    -EFAULT either way, but the memory is not, and unlike the
    copy-from-user shortfall this spec already tolerates (arm 4a, whose
    cost is one page of allocation BUDGET) a partial copy-out is
    USER-VISIBLE STATE.  Answering -EFAULT with no write would be a
    plausible-looking answer Linux need not give.  So the arm fails
    closed and says so.

    This is the same shape as [Kernel.Sys.prlimit64_spec]'s read arm,
    with one difference worth naming because it reads as an
    inconsistency otherwise: [prlimit64_spec] declines BOTH pointers
    non-NULL precisely to avoid a failed call that has already mutated
    state, and this spec takes that obligation on instead.  The reason
    they differ is that here the mutation is the whole point of the
    call — declining it would decline [sigprocmask] itself — whereas
    there it was avoidable. *)
Definition write_oset (oset old : word) : Sys SyscallEffect :=
  if negb (access_okb oset NSIG_BYTES) then err_ret EFAULT
  else
    i <- input ;;
    match read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES) with
    | Some _ =>
        pure (mkEffect (Z_to_bv 64 0)
                       [(oset, Z_to_le_bytes (Z.to_nat NSIG_BYTES) (bv_unsigned old))] [])
    | None => unmodeled
    end.

(** WHERE THE ABORT ACTUALLY KILLS THE PROCESS, and it is not at the
    [tkill].

    musl's [abort] calls [raise(SIGABRT)], and [raise] blocks the
    application signals before it sends anything: [__block_app_sigs]
    (src/signal/block.c, musl 1.2.6) is
    [rt_sigprocmask(SIG_BLOCK, &app_mask, &oldset, 8)] with an
    [app_mask] of 0xfffffffc7fffffff, whose low half sets bits 0..30 --
    signals 1..31, SIGABRT among them.  So by the time [tkill] runs,
    SIGABRT is BLOCKED, and a blocked signal is added to the task's
    pending set and left there: [send_signal_locked] does the add and
    [recalc_sigpending] leaves TIF_SIGPENDING clear for a signal the
    mask covers, so the return to user space takes no signal
    (kernel/signal.c, Linux v6.18.46, commit 1f99e9ab748f).  [raise]
    then restores the old mask with
    [rt_sigprocmask(SIG_SETMASK, &oldset, 0, 8)], and THAT call is the
    one the process does not come back from: [set_current_blocked] ->
    [__set_current_blocked] -> [__set_task_blocked] ends with
    [recalc_sigpending], which now finds an unblocked pending SIGABRT,
    so [get_signal] runs on the way out, finds SIG_DFL, and takes the
    default action for a coredumping signal -- [do_coredump] then
    [do_group_exit] (kernel/signal.c).

    So the fatal step belongs to THIS syscall, and it is conditional on
    the mask the call installs rather than on the mask it was handed.
    [set_sigmask_deliver] is [Monad.set_sigmask] plus that condition, and
    the two coincide whenever nothing is pending
    ([set_sigmask_deliver_no_pending]), which is every state a run with
    the declaration off can reach.

    THE ORDER IS THE KERNEL'S.  The mask is installed first and the
    process dies afterwards, so a [tkill] that becomes fatal here does so
    against the NEW mask; and the [oset] copy-out below still happens,
    because [sys_rt_sigprocmask] finishes before the return path takes
    the signal.  What it wrote is never read by anybody -- the process is
    gone and the memory is its own -- so the effect this spec produces is
    discarded by [Run.sstep_killed] exactly as [Kernel.Exit.exit_spec]'s
    is by [Run.sstep_exit].

    A LAUNCH MASK THAT ALREADY BLOCKS SIGABRT IS A DEATH ONE PATH LATER.
    [oldset] is then a mask with bit 5 set, the restore does not unblock
    anything, [raise] RETURNS, and musl's [abort] goes on to its second
    path (src/exit/abort.c, musl 1.2.6): [__block_all_sigs], then
    [rt_sigaction(SIGABRT, {SIG_DFL}, 0, 8)], then [tkill] again, then
    [rt_sigprocmask(SIG_UNBLOCK, {SIGABRT}, 0, 8)].  Each step is
    answered here.  The block-all mask is installed with SIGKILL and
    SIGSTOP stripped ([sigmask_strip]).  [rt_sigaction_spec] answers the
    install 0 and changes nothing ([sigabrt_dfl_install]).  The second
    [tkill] finds SIGABRT already pending: Linux drops a second instance
    of a pending signal below SIGRTMIN ([legacy_queue], kernel/signal.c,
    Linux v6.18.46, commit 1f99e9ab748f), and [State.with_sigabrt_pending]
    sets a bit that is already set.  The unblock is the mask install that
    takes the pending signal, and [sigmask_deliver_model] kills there.
    [Run.valid_sigmask] does not forbid such a launch and should not: it
    is a launch Linux really performs.  A mask the program installs
    itself with [rt_sigprocmask] before [abort] takes the same path.
    [Checks.AbortWitness.abrt_blocked_dies_by_signal] and
    [Checks.AbortWitness.abrt_blocked_error_free] walk that run. *)
Definition sigabrt_blocked (mask : word) : bool :=
  negb (w_is0 (bv_and mask (Z_to_bv 64 sigabrt_mask))).

(** TWO SIGNALS, IN THE KERNEL'S ORDER.  A mask install that uncovers a
    pending signal delivers it on the way back to user space, and both
    signals this model can raise are FATAL at their default
    disposition, so the install that uncovers one ends the process.

    SIGABRT IS TESTED FIRST, and that is [next_signal]'s rule rather
    than a choice: kernel/signal.c [get_signal] dequeues through
    [dequeue_signal], which takes the LOWEST-numbered pending signal,
    and 6 is below 13.  A fatal one never returns to the loop, so a
    process with both pending and both uncovered dies of SIGABRT and
    signal 13 is never dequeued.  That is only visible in the NUMBER the
    trace carries, and it is visible: [State.KillEv] carries it, and a
    waiting parent reads it through WTERMSIG.  Linux v6.18.46, commit
    1f99e9ab748f.

    ONE [State] FUNCTION AND ONE [Monad.modify], rather than a branch
    over monadic steps, because that is what the checker and the
    witness can follow: [Checks.Sys.Kernel.Signal] and
    [Checks.Witness.Kernel.Signal] discharge this call with the same
    [modify_ok] they discharged the plain [set_sigmask] with, and the
    branch moves into the model function they compute. *)
Definition sigmask_deliver_model (new : word) (m : Model) : Model :=
  if (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool
  then with_killed (Z_to_bv 64 SIGABRT) (with_sigmask new m)
  else if (m_sigpipe_pending m && negb (sigpipe_blocked new))%bool
  then with_killed (Z_to_bv 64 SIGPIPE) (with_sigmask new m)
  else with_sigmask new m.

Definition set_sigmask_deliver (new : word) : Sys unit :=
  modify (sigmask_deliver_model new).

(** MEANING PRESERVED: with NEITHER signal pending, installing a mask is
    plain [with_sigmask].  [State.with_sigabrt_pending]'s only caller is
    [tkill_spec], which declines outright with the declaration off, so
    every state a run whose task did not declare the abort path can
    reach has the first bit clear; the second is clear until a write
    finds a far end with no reader while signal 13 is blocked
    ([Fs.ReadWrite.raise_sigpipe]), which is NOT behind a declaration. *)
Lemma sigmask_deliver_model_no_pending : forall new m,
  m_sigabrt_pending m = false ->
  m_sigpipe_pending m = false ->
  sigmask_deliver_model new m = with_sigmask new m.
Proof.
  intros new m Ha Hp. unfold sigmask_deliver_model.
  rewrite Ha, Hp. reflexivity.
Qed.

(** The two projections the checker and the witness need through the
    delivery: the mask installed is the mask asked for, and the address
    space is untouched.  Every branch of [sigmask_deliver_model] goes
    through [State.with_sigmask], and [State.with_killed] on top of it
    rebuilds [ProcState] alone. *)
Lemma m_sigmask_sigmask_deliver_model : forall new m,
  m_sigmask (sigmask_deliver_model new m) = new.
Proof.
  intros new m. unfold sigmask_deliver_model.
  destruct (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool;
    [autorewrite with model; reflexivity|].
  destruct (m_sigpipe_pending m && negb (sigpipe_blocked new))%bool;
    autorewrite with model; reflexivity.
Qed.

Lemma m_vmmaps_sigmask_deliver_model : forall new m,
  m_vmmaps (sigmask_deliver_model new m) = m_vmmaps m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  destruct (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool;
    [autorewrite with model; reflexivity|].
  destruct (m_sigpipe_pending m && negb (sigpipe_blocked new))%bool;
    autorewrite with model; reflexivity.
Qed.

Lemma set_sigmask_deliver_no_pending : forall new i m o,
  m_sigabrt_pending m = false ->
  m_sigpipe_pending m = false ->
  (set_sigmask_deliver new i m o <-> set_sigmask new i m o).
Proof.
  intros new i m o Ha Hp. unfold set_sigmask_deliver, set_sigmask, modify.
  rewrite sigmask_deliver_model_no_pending by assumption. reflexivity.
Qed.

Definition rt_sigprocmask_spec (how nset oset ss : word) : Sys SyscallEffect :=
  if negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES)) then err_ret EINVAL
  else
    m <- get_model ;;
    let old := m_sigmask m in
    if w_is0 nset then
      (if w_is0 oset then ret_only (Z_to_bv 64 0) else write_oset oset old)
    else
      i <- input ;;
      match sigset_at (in_mem i) nset with
      | None => err_ret EFAULT
      | Some raw =>
          record_copyins [(nset, Z.to_nat NSIG_BYTES)]
          (if negb (how_valid how) then err_ret EINVAL
           else
             set_sigmask_deliver (sigmask_apply how old (sigmask_strip raw)) ;;
             (if w_is0 oset then ret_only (Z_to_bv 64 0)
              else write_oset oset old))
      end.

(* =========================================================================
   sigaltstack (132) — a stack that is recorded as installed and never used
   ========================================================================= *)

(** WHICH KERNEL THIS IS A MODEL OF, AND WHAT IT COSTS TO ANSWER AT ALL.

    Linux v6.18.46, commit 1f99e9ab748f.  The whole call is
    [SYSCALL_DEFINE2(sigaltstack)] and [do_sigaltstack], both
    kernel/signal.c, over four helpers: [on_sig_stack], [__on_sig_stack]
    and [sas_ss_flags] (include/linux/sched/signal.h) and
    [sigaltstack_size_valid] (arch/riscv/kernel/signal.c under
    CONFIG_DYNAMIC_SIGFRAME, include/linux/signal.h without it).

    WHY AN INSTALLED STACK IS INVISIBLE HERE.  An alternate stack is
    consulted at ONE place, [sigsp] (include/linux/sched/signal.h), on
    the way into a handler for a disposition carrying SA_ONSTACK.  This
    model delivers no signal — [Run.sstep] has no asynchronous
    transition and [State.event] has no signal constructor — so nothing
    it admits ever reads the stack it records.  That is the same premise
    [rt_sigaction_spec] above rests on, not a second one.

    THE STATE IS ONE BIT, AND THE BIT IS NOT THE RECORD.  What the model
    keeps is [State.m_sigaltstack_installed]: whether a [sigaltstack] has
    left [sas_ss_size] NON-ZERO.  It does not keep [ss_sp] or [ss_size],
    and storing them would buy no answer, because BOTH READERS OF THE
    RECORD TAKE THE USER STACK POINTER AS AN ARGUMENT and
    [State.SyscallInput] carries a0..a5 and no sp:

      - [on_sig_stack(sp)] decides -EPERM;
      - [sas_ss_flags(sp)] is the [ss_flags] an [oss] answer reports.

    ZERO SIZE IS WHAT MAKES THEM ANSWERABLE, and it is the size and not
    the age of the record that does it.  While [sas_ss_size] is zero both
    are constant in sp — [__on_sig_stack] reduces to
    [sp > sas_ss_sp && sp - sas_ss_sp <= 0], whose two conjuncts
    contradict each other for every sp, and [sas_ss_flags] returns
    SS_DISABLE on its first line before it consults anything else.  A
    size of at least [Uapi.MINSIGSTKSZ] ends that, and -EPERM becomes a
    fact about a stack pointer this model cannot see.

    SO THE BIT IS SET BY ARM 9 AND NOT BY ARM 6.  [do_sigaltstack]
    reaches its three assignments on both, but the SS_DISABLE arm runs
    [ss_size = 0; ss_sp = NULL] first, so the record it leaves is
    (NULL, 0, [ss_flags]) — the same zero-size shape execve's is, with
    the same two constant readers.  Declining after it would give up an
    answer the model still has.  What a disable does change is the third
    field, from the inherited word to the caller's, and the spec buys
    nothing by that: the two arms that would need a flags word (2 and 7)
    decline whether it is known or not.

    THE INVARIANT THE OTHER ARMS REST ON: while the bit is false the
    record is (NULL, 0, F) for a flags word F the model does not track.
    It holds at [mkModel] (begin_new_exec), and each arm preserves it —
    2, 3, 4, 5, 7 and 8 store nothing at all, arm 6 stores
    (NULL, 0, [ss_flags]), and arm 9 breaks it and sets the bit in the
    same step.  Every answer below is therefore correct for EVERY F,
    which is what makes not tracking it sound rather than merely
    convenient.

    THE STARTING RECORD IS execve's, AND IT IS NOT WHOLLY KNOWN.
    [begin_new_exec] (fs/exec.c) clears TWO of the three fields —
    [me->sas_ss_sp = me->sas_ss_size = 0] — and leaves
    [me->sas_ss_flags] alone; the three-field reset [sas_ss_reset]
    (include/linux/sched/signal.h) is called from [copy_process]
    (kernel/fork.c) for a CLONE_VM child and from nowhere on the exec
    path.  So the starting flags word is INHERITED from whatever process
    called [execve], which makes it a choice of the launching
    environment in the way [State.in_sigmask] is, and
    [State.ProcInput] does not quantify it.  Two things follow, and they
    are the reason this spec has arms 2 and 7 rather than answering
    everything the kernel answers:

      - a non-NULL [uoss] is declined, because [do_sigaltstack] writes
        [sas_ss_flags(sp) | (current->sas_ss_flags & SS_FLAG_BITS)]
        there and the second half is the inherited bit.  This is
        [rt_sigaction_spec]'s [oact] decline with a sharper citation:
        there the unknown is a disposition execve only partly resets,
        here it is a field execve does not reset at all.
      - the no-change fast path is decided by comparing the caller's
        whole [ss_flags] word against the stored one — that inherited
        word, or whatever a previous SS_DISABLE put in its place — so a
        call that would take it is declined too, see arm 7.

    THE SUCCESS ARM CARRIES A PREMISE ABOUT THE ISA, AND IT IS WORTH
    STATING BECAUSE -ENOMEM IS NOT [MINSIGSTKSZ] ALONE ON THIS
    ARCHITECTURE.  [do_sigaltstack] applies a second lower bound,
    [sigaltstack_size_valid], and RISCV_ISA_V selects DYNAMIC_SIGFRAME
    (arch/riscv/Kconfig), under which riscv's implementation
    (arch/riscv/kernel/signal.c) is [ss_size > get_rt_frame_size(false)].
    That function adds [riscv_v_sc_size] — a size derived from the
    hardware's VLEN — whenever the calling task's vector state is not
    OFF, so on a vector-enabled task the boundary moves with the machine
    and this model could not state it.

    IT IS OFF FOR EVERY RUN THIS MODEL ADMITS.  [flush_thread]
    (arch/riscv/kernel/process.c) turns it off at [execve], and exactly
    one thing turns it back on: [riscv_v_first_use_handler]
    (arch/riscv/kernel/vector.c), the trap taken when the task executes a
    vector instruction, which is also the only caller of
    [riscv_v_vstate_on] (arch/riscv/include/asm/vector.h).  The modeled
    ISA is RV64IMAFD_Zicsr_Zifencei plus C (theories/Riscv/Decode.v,
    theories/Riscv/DecodeC.v) and contains no vector instruction at all,
    so no run this model admits reaches that handler.  With the state
    off, [get_rt_frame_size(false)] is
    [round_up(sizeof(struct rt_sigframe), 16)] = 1088 — [struct siginfo]
    128 plus [struct ucontext] 960, the latter being 176 bytes up to
    [uc_mcontext] and a [struct sigcontext] of 784 — which is below
    [Uapi.MINSIGSTKSZ] = 2048, so the second bound never decides a case
    the first has not.  Under RISCV_ISA_V=n the same conclusion holds for
    a second reason: [sigaltstack_size_valid] is then the trivial
    [return true] (include/linux/signal.h).

    WHAT WOULD BREAK THAT: a vector instruction in the decoder.  The day
    [theories/Riscv/Decode.v] gains one, a run can turn the vector state
    on, and this spec's arm 9 starts admitting a 0 where a real kernel on
    a wide-VLEN hart answers -ENOMEM.  The fix is not a wider envelope but
    a narrower one — decline arm 9 outright, since no [ss_size] is large
    enough for every VLEN.

    WHAT IS DELIBERATELY NOT MODELED, beyond the two declines above:
    every [sigaltstack] after the first size-raising install (arm 1), and
    [restore_altstack]'s path into the same function, which belongs to
    [rt_sigreturn] (139) and has no arm.

    A NOTE FOR [rt_sigprocmask_spec] ABOVE: this arm opens no window onto
    the blocked mask.  [do_sigaltstack] reads and writes [sas_ss_sp],
    [sas_ss_size] and [sas_ss_flags] and names [blocked] nowhere, and
    [SYSCALL_DEFINE2(sigaltstack)] calls no [set_user_sigmask].  132 is
    not on [Checks.Cases.Kernel.Signal]'s [sig_mask_windows]; as for
    134, 72, 73 and 22, the
    fact that actually shuts it is checked instead —
    [sigaltstack_leaves_the_mask_alone]. *)

(** The three fields of the [stack_t] the kernel copied in, decoded from
    its 24 bytes.  [ss_flags] is an [int]: the kernel reads it as
    [unsigned ss_flags = ss->ss_flags], four bytes at offset 8, and the
    four padding bytes above it are copied and never looked at. *)
Definition ss_sp_of (bs : list byte) : word :=
  le_bytes_to_word (firstn 8 bs).
Definition ss_flags_of (bs : list byte) : word :=
  le_bytes_to_word (firstn 4 (skipn (Z.to_nat SS_FLAGS_OFF) bs)).
Definition ss_size_of (bs : list byte) : word :=
  le_bytes_to_word (skipn (Z.to_nat SS_SIZE_OFF) bs).

(** [ss_mode = ss_flags & ~SS_FLAG_BITS] — the flags word with the one
    bit that is not a mode masked away. *)
Definition ss_mode (fl : word) : Z :=
  Z.ldiff (bv_unsigned fl) SS_AUTODISARM.

(** [do_sigaltstack] answers -EINVAL for a mode outside {SS_DISABLE,
    SS_ONSTACK, 0}.  SS_ONSTACK is ACCEPTED as an input mode — the
    kernel does not refuse a caller that claims to be on the stack it is
    installing — and is not the same thing as the SS_ONSTACK [oss]
    reports back. *)
Definition ss_mode_ok (fl : word) : bool :=
  let md := ss_mode fl in
  (Z.eqb md 0 || Z.eqb md SS_ONSTACK || Z.eqb md SS_DISABLE)%bool.

Definition ss_disabling (fl : word) : bool := Z.eqb (ss_mode fl) SS_DISABLE.

(** The [stack_t] at [uss], or [None] if [access_ok] refuses its 24
    bytes or any of them is unreadable.  All-or-nothing because
    [SYSCALL_DEFINE2(sigaltstack)]
    fetches the struct with ONE [copy_from_user] before [do_sigaltstack]
    runs, so -EFAULT precedes every other answer this call has.

    THE RANGE TEST IS ASKED, through [State.copy_bytes_map]:
    [SYSCALL_DEFINE2(sigaltstack)] (kernel/signal.c) copies with
    [copy_from_user], which is [access_ok] over the 24 bytes before the
    copy, and both come before [do_sigaltstack] runs.  This note used to
    lean on [sigaction_flags]'s argument for leaving the test out, and
    that argument is withdrawn there for the reason given there: the
    wrap is impossible in a run, because
    [Equivalence.image_brk_satisfiable] bounds the image below 2^64, but
    nothing bounds a wholly readable range below [TASK_SIZE], so the
    test is asked rather than argued.  The wrap itself is
    [State.copy_bytes_map]'s note. *)
Definition sigaltstack_at (mp : word -> option byte) (uss : word)
    : option (list byte) :=
  copy_bytes_map mp uss SIGALTSTACK_BYTES.

(** [sigaltstack uss uoss].  The arms follow the kernel's own order:

      1. a stack is installed — [sas_ss_size] is non-zero — so nothing
         below can be decided from a stack pointer this model does not
         have: UNMODELED.  This is the arm that makes one bit enough.
      2. a non-NULL [uoss] is UNMODELED — the inherited SS_AUTODISARM
         bit is part of the answer.
      3. with both pointers NULL [do_sigaltstack] runs and does nothing:
         0.
      4. -EFAULT unless [access_ok] admits the 24 bytes at [uss] and
         they are readable.
      5. -EINVAL for a mode outside {0, SS_ONSTACK, SS_DISABLE}.  It is
         decided AFTER the copy and BEFORE the fast path, exactly where
         the kernel decides it, and after an -EPERM that cannot fire —
         [on_sig_stack] is false for every sp while the recorded size is
         zero, which arm 1 guarantees it is.
      6. SS_DISABLE succeeds whatever [ss_sp] and [ss_size] say: the
         kernel zeroes both before storing, so no size check applies.
         The record moves to (NULL, 0, [ss_flags]) — or was already
         exactly that and the fast path returned first, which is the same
         record, since that path is taken only when all three fields
         already match.  Either way the answer is 0 and the size stays
         zero, so the bit is NOT set and the arms below keep answering.
      7. a zero [ss_sp] AND a zero [ss_size] under a non-disabling mode
         is UNMODELED, and this is the only arm that is not a kernel
         answer.  It is the fast path's shadow: the kernel returns 0 when
         all three fields equal the stored ones and -ENOMEM otherwise
         (the size is zero, so the bound below refuses it), and which of
         the two it is turns on the stored flags word — execve's
         inherited one, or the one arm 6 wrote over it.  Neither is
         tracked, so both decline.
      8. -ENOMEM below [Uapi.MINSIGSTKSZ].  The fast path cannot have
         fired above it: it needs [ss_sp] and [ss_size] to equal a
         stored pair that the invariant makes (NULL, 0), and that shape
         is arm 7's, already declined.
      9. otherwise the install succeeds: 0, and the bit is set — this is
         the only arm that raises [sas_ss_size] above zero, and the
         [Uapi.MINSIGSTKSZ] bound arm 8 just applied is why.

    No arm writes user memory.  Every answer after the copy records the
    24 bytes at [uss] in [State.eff_copyins]: [SYSCALL_DEFINE2(sigaltstack)]
    (kernel/signal.c:4459, v6.18.46) has read them with [copy_from_user]
    before [do_sigaltstack] runs, and [State.materialize_model_accesses]
    charges a lazy anonymous page that read faults in.  The -EFAULT of
    arm 4 records nothing, the convention [rt_sigprocmask_spec] states. *)
Definition sigaltstack_spec (uss uoss : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if m_sigaltstack_installed m then unmodeled
  else if negb (w_is0 uoss) then unmodeled
  else if w_is0 uss then ret_only (Z_to_bv 64 0)
  else
    i <- input ;;
    match sigaltstack_at (in_mem i) uss with
    | None => err_ret EFAULT
    | Some bs =>
        record_copyins [(uss, Z.to_nat SIGALTSTACK_BYTES)]
        (let fl := ss_flags_of bs in
         if negb (ss_mode_ok fl) then err_ret EINVAL
         else if ss_disabling fl
         then ret_only (Z_to_bv 64 0)
         else if (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))%bool
         then unmodeled
         else if (bv_unsigned (ss_size_of bs) <? MINSIGSTKSZ)%Z
         then err_ret ENOMEM
         else set_sigaltstack_installed ;; ret_only (Z_to_bv 64 0))
    end.

(* =========================================================================
   tkill (130) and tgkill (131) — the abort path, and only under a
   task's declaration
   ========================================================================= *)

(** WHY THESE TWO NUMBERS HAVE AN ARM AT ALL.

    A dataset whose
    reference must not abort wants "the reference can abort" to be a
    PROOF OBLIGATION — proving the abort unreachable is proving the
    program's property — and leaving 130 and 131 unmodeled is what makes
    it one: the run leaves the modeled surface, [Run.reaches_unmodeled]
    holds, and [Equivalence.modeled] is false.  That is not right for
    every dataset.  A reference whose abort is EXPECTED on some inputs —
    a parser that rejects malformed input by aborting — is then
    unprovable for a reason that has nothing to do with the property
    being checked.

    So the stance is the task's, and it is declared in the INPUT:
    [State.in_abort_terminal], pinned [false] by [Run.valid_input] and
    [true] by [Run.valid_input_abort].  With the declaration off this
    arm answers [unmodeled] for every argument shape, which is what the
    dispatcher does for a number with no arm — the decline is the FIRST
    test below for exactly that reason, ahead of the -EINVAL a real
    kernel would answer first, because a coverage gate is not a kernel
    test and putting it anywhere else would leave a shape that answers
    with the declaration off.

    ** WHAT abort() ISSUES, WHICH IS NOT WHAT THE NAME SUGGESTS

    musl 1.2.6 on riscv64, static and single-threaded
    (src/exit/abort.c, src/signal/raise.c, src/signal/block.c):

      rt_sigprocmask(SIG_BLOCK, app_mask, &oldset, 8)
      tkill(tid, SIGABRT)
      rt_sigprocmask(SIG_SETMASK, &oldset, 0, 8)

    [raise] issues TKILL, not tgkill, and it issues no [gettid]: the tid
    comes from [__pthread_self()->tid], which [__init_tp]
    (src/env/__init_tls.c) seeded from the return value of
    [set_tid_address] (96) at start-up — the same number
    [Kernel.Sys.gettid_spec] and [Kernel.Sys.getpid_spec] answer, and the
    same [State.m_tid] this spec compares against.  tgkill is here
    anyway because it is the same kernel path with one more test, and
    other libcs raise through it.

    ** THE MODELED ENVELOPE

    Answered:

    - [pid] <= 0 (and, for tgkill, [tgid] <= 0): -EINVAL, tested before
      anything else looks at a task.  [SYSCALL_DEFINE2(tkill)] refuses
      [pid <= 0] and [SYSCALL_DEFINE3(tgkill)] refuses either being
      <= 0 (kernel/signal.c, Linux v6.18.46, commit 1f99e9ab748f).
    - tgkill with [pid] the caller's own tid but [tgid] something else:
      -ESRCH.  [do_send_specific] finds the task and then requires
      [task_tgid_vnr(p) == tgid] before it will deliver, leaving the
      seeded -ESRCH when it does not match (kernel/signal.c, same
      version).  In this model the caller's tgid IS its tid — one
      thread, one group, which is the same fact
      [State.procst_tid] rests on — so a mismatch is decidable here.
    - [sig] above 64, which after the [int] truncation is also every
      negative one: -EINVAL from [check_kill_permission]'s
      [valid_signal] test, which the caller reaches because the task
      lookup succeeded (kernel/signal.c, same version).
    - [sig] = SIGABRT to the caller's own tid: the abort path, below.

    Unmodeled, each because the answer is not this model's to give:

    - [pid] positive and NOT the caller's tid.  [find_task_by_vpid]
      searches the whole pid namespace, and this model knows about one
      task; -ESRCH would be a guess about every other process on the
      machine.
    - [sig] = 0, the permission-and-existence probe.  [valid_signal(0)]
      is true and delivery is skipped under [if (!error && sig)], so the
      answer is whatever [security_task_kill] says, which is an LSM
      question rather than a kernel one.
    - any other signal in 1..64.  The model has a disposition for
      SIGABRT and for no other signal: [rt_sigaction_spec] answers an
      install only for SIGINT and SIGTERM, and for SIGABRT and SIGCHLD
      only with the handler SIG_DFL, so what SIGKILL or SIGUSR1 would do to this
      process is not something the model can read off its own state.
    - [State.m_tid] not yet pinned.  Nothing has made the tid
      observable, so there is no value to compare [pid] against.

    ** WHY SIGABRT'S DISPOSITION IS SIG_DFL, BY CONSTRUCTION

    The whole arm rests on it.  INSIDE THE MODELED SURFACE it is not an
    assumption: SIGABRT's disposition cannot be changed there.
    [rt_sigaction_spec] answers an install for signal 6 in one case
    only: the handler word is SIG_DFL ([sigabrt_dfl_install]), which is
    musl's own install on abort's second path.  Signal 6 with SIG_IGN or
    a handler address is [unmodeled].  So the one install the model
    admits sets the disposition it already has.  What the model DOES
    assume is the start: that the launch leaves SIGABRT at SIG_DFL.  It
    cannot derive that, because [execve] keeps an inherited SIG_IGN, so
    it is the launch premise written down above [Run.unmodeled_at]
    ("THE PROCESS STARTS WITH SIGABRT AT ITS DEFAULT DISPOSITION").
    Under that premise SIGABRT keeps its boot-time
    disposition in every run this model covers, which is SIG_CORE:
    terminate, and dump core (kernel/signal.c, SIG_KERNEL_COREDUMP_MASK;
    the core dump is a file the process never sees, so nothing of it
    reaches the trace).  On abort's second path Linux agrees with the
    model even after an inherited SIG_IGN: a blocked signal is never
    ignored at send time ([sig_ignored]), the SIG_DFL install does not
    discard it ([do_sigaction]), and the unblock delivers it at SIG_DFL
    (kernel/signal.c, Linux v6.18.46, commit 1f99e9ab748f).

    That is the sentence [sigaction_accepted]'s own note has to be read
    against: its list is "the signals whose disposition no modeled
    operation can consult AND which the environment therefore never
    delivers", and this arm is a modeled operation that DOES
    deliver one.  It delivers SIGABRT alone, and SIGABRT is not on that
    list, so the list's second half still holds for the two signals on
    it.

    ** THE LSM GAP

    [check_kill_permission] ends with [security_task_kill], which an
    enabled LSM can answer -EPERM to even for a signal to oneself.  This
    spec answers rather than declining, so it does not admit that
    -EPERM.  That is a known gap, of the same shape as [getdents64]'s
    LSM and fanotify denial gap. *)

(** [pid] and [tgid] arrive as [pid_t], an [int]: [Syscall.pid32] has
    already truncated to 32 bits, so "positive" is 1..2^31-1 and every
    negative value has become something at or above 2^31. *)
Definition pid_positive (p : word) : bool :=
  let v := bv_unsigned p in ((1 <=? v)%Z && (v <? 2 ^ 31)%Z)%bool.

(** [valid_signal(sig)] widens the [int] to [unsigned long] and tests
    [sig <= _NSIG], with [_NSIG] 64 on riscv64.  A negative [int] widens
    to something enormous and fails; so does anything above 64.  Applied
    to the already-truncated low half, an unsigned [<= 64] test is that
    predicate — and unlike [sig_valid], which [rt_sigaction] uses, 0
    PASSES it: [rt_sigaction]'s [sig < 1] is its own test, and the
    signal-sending paths keep 0 as the permission probe. *)
Definition tkill_sig_valid (sig : word) : bool :=
  (bv_unsigned sig <=? 64)%Z.

(** The delivery, once every check has passed and the target is the
    caller itself.  BLOCKED means pending: [send_signal_locked] adds the
    signal to [task->pending] and [recalc_sigpending] leaves it there
    while the mask covers it, so the syscall returns 0 and the process
    runs on — see [set_sigmask_deliver] for where it is taken.
    UNBLOCKED means the process does not come back: [get_signal] runs on
    the return to user space, finds SIG_DFL for a coredumping signal, and
    reaches [do_group_exit] (kernel/signal.c, Linux v6.18.46, commit
    1f99e9ab748f).  The 0 this returns on that branch is never observed,
    for [Kernel.Exit.exit_spec]'s reason: [Run.sstep_killed] ends the
    trace with a [State.KillEv] and discards the effect. *)
Definition send_sigabrt : Sys SyscallEffect :=
  m <- get_model ;;
  (if sigabrt_blocked (m_sigmask m)
   then set_sigabrt_pending
   else set_killed (Z_to_bv 64 SIGABRT)) ;;
  ret_only (Z_to_bv 64 0).

(** Everything [tkill] and [tgkill] share: the caller has named a
    positive [pid], and what remains is whether it is this process and
    what signal it is. *)
Definition tkill_self (pid sig : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if negb (m_abort_terminal m) then unmodeled
  else
    match m_tid m with
    | None => unmodeled
    | Some t =>
        if negb (bv_eqb pid t) then unmodeled
        else if negb (tkill_sig_valid sig) then err_ret EINVAL
        else if bv_eqb sig (Z_to_bv 64 SIGABRT) then send_sigabrt
        else unmodeled
    end.

Definition tkill_spec (pid sig : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if negb (m_abort_terminal m) then unmodeled
  else if negb (pid_positive pid) then err_ret EINVAL
  else tkill_self pid sig.

Definition tgkill_spec (tgid pid sig : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if negb (m_abort_terminal m) then unmodeled
  else if negb (pid_positive pid && pid_positive tgid)%bool then err_ret EINVAL
  else
    match m_tid m with
    | None => unmodeled
    | Some t =>
        if negb (bv_eqb pid t) then unmodeled
        else if negb (bv_eqb tgid t) then err_ret ESRCH
        else tkill_self pid sig
    end.

(** WITH THE DECLARATION OFF, BOTH ARMS ARE UNMODELED.  Both specs test it
    first, so with it clear the only outcome either admits is
    [Unmodeled] — which is what [Sys.Dispatch.dispatch] produces for a
    number with no arm.  This is the half of the compatibility
    claim that lives at the spec; the other half is
    [set_sigmask_deliver_no_pending], and the step-level half is
    [Run.sstep_off_no_kill]. *)
Lemma tkill_spec_off_unmodeled : forall pid sig i m o,
  m_abort_terminal m = false -> tkill_spec pid sig i m o -> o = Unmodeled.
Proof.
  intros pid sig i m o Hoff H. unfold tkill_spec in H.
  rewrite bind_get_model, Hoff in H. exact H.
Qed.

Lemma tgkill_spec_off_unmodeled : forall tgid pid sig i m o,
  m_abort_terminal m = false -> tgkill_spec tgid pid sig i m o -> o = Unmodeled.
Proof.
  intros tgid pid sig i m o Hoff H. unfold tgkill_spec in H.
  rewrite bind_get_model, Hoff in H. exact H.
Qed.
