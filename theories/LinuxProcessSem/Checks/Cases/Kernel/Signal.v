(** * LinuxProcessSem.Checks.Cases.Kernel.Signal — worked examples over rt_sigaction (134), rt_sigprocmask (135) and sigaltstack (132)

    Mirrors [Sys/Kernel/Signal.v], which answers to Linux
    [kernel/signal.c]: this file holds the worked examples for the
    syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    WHAT THE rt_sigprocmask CASES PIN, AND WHERE THEIR LIMIT IS.  The
    call keeps a mask and answers [oset] out of it, so these cases
    are about a VALUE and not only about a return code: the ORDER the
    error conditions are decided in, the fact that a NULL new set makes
    [how] unreachable, and that an effect claiming a write the arm did
    not make is rejected rather than waved through.  What no case here
    can catch is the mask's MEANING.  Nothing in the model delivers a
    signal, so two programs that block different signals differ only
    where one of them READS the mask back; under a real signal they
    differ everywhere.  That is the premise the spec's header states,
    not a gap in these examples. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** rt_sigreturn (139) fails closed like any other unmodeled number, and
    this is where it is pinned.  A bare
    rt_sigreturn restores every register — pc and sp included — from
    whatever the stack happens to hold, so the process does not survive
    the call.  Reaching
    139 the natural way, through a delivered signal, needs [kill] or
    [tgkill] first — themselves unmodeled — so the verdict would fix at
    THAT call. *)
Example rt_sigreturn_unmodeled :
  check_syscall (mkInput 139 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** kill (129) likewise.  This example is the
    universally quantified claim no finite set of traces can give: the
    decline at the NUMBER, with no argument and no return value in the
    picture at all. *)
Example kill_unmodeled :
  check_syscall (mkInput 129 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** rt_sigaction (134) IS modeled, and the case the whole spec exists for
    is the one it must DECLINE: an install for SIGSEGV.  Accepting it
    would put a fault signal's disposition inside the modeled surface,
    and [Run.unmodeled_at]'s exclusion of [RiscvSemantics.MachineFault]
    — "a real Linux process dies there too" — is only true while no
    such handler exists; a source could then fault deliberately, reach
    [Run.SError] on every execution, and [Equivalence.equiv]'s
    [bh_all_errors] escape would admit an ARBITRARY target.

    The examples below are the shape of that claim: the SAME call, at
    the SAME fully readable 24-byte [struct sigaction], differing only
    in the signal number.  SIGINT is accepted and answers 0, storing no
    disposition; SIGSEGV and SIGCHLD fail closed -- the first because
    every [MachineFault] site raises it, the second because a child's
    exit raises it and the model has a parent side that admits a child
    can exist.  SIGPIPE is the exception, answered WITH STATE: its action
    is the one the model stores ([Signal.rt_sigaction_sigpipe]), and a
    SIG_DFL or SIG_IGN install is answered and recorded.
    What these add is the decline against the
    acceptance in the SAME file, so that a widened
    [Signal.sigaction_accepted] cannot pass the Rocq build. *)
Definition mem_sigaction_zero : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 24) then Some 0 else None.

Example rt_sigaction_sigsegv_unmodeled :
  check_syscall (mkInput 134 [11; 4096; 0; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** SIGPIPE's SIG_DFL install IS ANSWERED: 0, the 24 bytes of [act] in
    the ledger, and the action stored ([State.with_sigpipe_install] of
    SIG_DFL, flags 0, mask 0).  This is the pass-after half of a pair.
    The fail-before half was [rt_sigaction_sigpipe_unmodeled], the same
    call on the same model judged [CheckUnmodeled], which held while the
    model stored no SIGPIPE action and declined every SIGPIPE install;
    it is false by design now, and this statement replaces it.  As for
    [rt_sigaction_sigint_accepted] below, the same answer with an empty
    ledger is rejected rather than declined. *)
Example rt_sigaction_sigpipe_dfl_answered :
  check_syscall (mkInput 134 [13; 4096; 0; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (with_copyins [(4096, 24%nat)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (with_sigpipe_install (mkSigpipeAction true 0 0)
               (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))) [] /\
  check_syscall (mkInput 134 [13; 4096; 0; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** SIGCHLD (17) declines because the model has a modeled
    [clone]/[clone3] parent side and a modeled [wait4], so a child can
    exist.  The note above [Signal.sigaction_accepted] requires the
    signal to stay out of the set while the model can have a child.
    This example is what stops it coming back unnoticed: nothing else in
    the tree fails if a future edit puts 17 back, because the operational
    test the set is chosen by still passes for it. *)
Example rt_sigaction_sigchld_unmodeled :
  check_syscall (mkInput 134 [17; 4096; 0; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** SIGABRT (6), AND THESE THREE ARE LOAD-BEARING FOR ANOTHER ARM.
    [Kernel.Signal.tkill_self] delivers SIGABRT with the DEFAULT
    disposition and never asks whether a handler is installed, and what
    makes that sound is the two declines below rather than a test: an
    install for signal 6 whose handler word is an address or SIG_IGN is
    [unmodeled], so no run this model covers can reach the abort path
    with a handler, or with SIGABRT ignored.  The argument is at
    [Kernel.Signal.tkill_self]; these are the checks that fail if
    [Signal.sigaction_accepted] ever grows a 6, or if
    [Signal.sigabrt_dfl_install] ever admits a handler word other than
    SIG_DFL.

    The one install for signal 6 that IS answered is SIG_DFL, musl's own
    on abort's second path: it sets the disposition [tkill_self] already
    assumes ([Signal.sigabrt_dfl_install] says why that is sound).  The
    SIG_DFL case for SIGSEGV and SIGCHLD above is still declined:
    [mem_sigaction_zero] is a SIG_DFL install, so those two say that the
    acceptance is for SIGABRT and not for SIG_DFL as such.  (SIGPIPE's
    SIG_DFL is answered by its own arm, which stores the action.)

    THE THREE DIFFER FROM EACH OTHER IN THE HANDLER WORD ONLY, which is
    what makes them say that the HANDLER is the reason.  And
    [rt_sigaction_sigabrt_dfl_accepted] differs from
    [rt_sigaction_sigint_accepted] below in the signal number only.  Two
    OTHER gates sit in front of the handler test — a non-NULL [oact],
    and a flag word outside
    [Signal.sa_flags_accepted] — and both would decline a handler install
    for reasons that have nothing to do with SIGABRT: musl's [signal(3)]
    trips both, since it returns the old handler and passes SA_RESTART.
    That is why these examples pass a NULL [oact] and a zero flag word:
    written the other way they would keep passing if the declines were
    removed. *)
Definition mem_sigaction_handler : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 24)
           then Some (if bv_eqb a 4097 then 16 else 0)
           else None.

Definition mem_sigaction_ign : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 24)
           then Some (if bv_eqb a 4096 then 1 else 0)
           else None.

(** A handler at 0x1000: declined. *)
Example rt_sigaction_sigabrt_handler_unmodeled :
  check_syscall (mkInput 134 [6; 4096; 0; 8; 0; 0] mem_sigaction_handler
                   (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** SIG_IGN (1): declined. *)
Example rt_sigaction_sigabrt_ign_unmodeled :
  check_syscall (mkInput 134 [6; 4096; 0; 8; 0; 0] mem_sigaction_ign
                   (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** SIG_DFL (0): answered 0, and the model is left as it was.  Like the
    SIGINT acceptance below, it carries the 24 bytes of [act] the syscall
    copied before it answered. *)
Example rt_sigaction_sigabrt_dfl_accepted :
  check_syscall (mkInput 134 [6; 4096; 0; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (with_copyins [(4096, 24%nat)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [].
Proof. vm_compute. reflexivity. Qed.

(** ...and the acceptance the declines above are AGAINST, so that a spec
    that declined everything would not pass this file either.  It
    carries the 24 bytes of [act] the syscall copied before it answered,
    and the same answer with an empty ledger is rejected: an effect that
    claims the call read nothing would leave a lazy page uncharged that
    Linux faults in. *)
Example rt_sigaction_sigint_accepted :
  check_syscall (mkInput 134 [2; 4096; 0; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (with_copyins [(4096, 24%nat)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [] /\
  check_syscall (mkInput 134 [2; 4096; 0; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** SIGPIPE'S ACTION IS STORED AND READ BACK.  [rt_sigaction_sigpipe]
    is the one rt_sigaction arm with state, so its cases are about the
    VALUE kept, in three parts the [rt_sigaction_sigpipe_dfl_answered]
    case above cannot show, since its install of SIG_DFL over a launch
    at SIG_DFL leaves the record as it was.

    [wmem_oact] is 24 writable bytes at 8192 and nothing else writable;
    [sigpipe_model mask] is the launch at SIG_DFL with the given blocked
    mask.  4096 is [sigmask(SIGPIPE)], 1 << 12. *)
Definition wmem_oact : word -> option byte :=
  fun a => if bv_leu 8192 a && bv_ltu a (8192 + 24) then Some 0 else None.

Definition sigpipe_model (mask : word) : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
       default_nofile mask demo_hwcap false Sv48).

(** FIRST: SIG_IGN installed with [oact] set.  The 24 bytes written to
    [oact] are the action BEFORE the install (SIG_DFL, flags 0, mask 0:
    all zero), and the model keeps SIG_IGN.  SECOND: a read with [act]
    NULL then writes the action the model KEPT, whose handler word is
    SIG_IGN (1), and installs nothing.  A spec that wrote the new action
    to [oact], or that stored nothing, fails one of the two. *)
Example rt_sigaction_sigpipe_ign_stored_and_read_back :
  check_syscall (mkInput 134 [13; 4096; 8192; 8; 0; 0] mem_sigaction_ign wmem_oact)
    (with_copyins [(4096, 24%nat)]
       (mkEffect 0 [(8192, sigpipe_action_bytes (mkSigpipeAction true 0 0))] []))
    (sigpipe_model 0)
  = CheckOk (with_sigpipe_install (mkSigpipeAction false 0 0) (sigpipe_model 0)) [] /\
  check_syscall (mkInput 134 [13; 0; 8192; 8; 0; 0] (fun _ => None) wmem_oact)
    (mkEffect 0 [(8192, sigpipe_action_bytes (mkSigpipeAction false 0 0))] [])
    (with_sigpipe_install (mkSigpipeAction false 0 0) (sigpipe_model 0))
  = CheckOk (with_sigpipe_install (mkSigpipeAction false 0 0) (sigpipe_model 0)) [] /\
  check_syscall (mkInput 134 [13; 0; 8192; 8; 0; 0] (fun _ => None) wmem_oact)
    (mkEffect 0 [(8192, sigpipe_action_bytes (mkSigpipeAction true 0 0))] [])
    (with_sigpipe_install (mkSigpipeAction false 0 0) (sigpipe_model 0))
  = CheckReject.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(** THIRD: SIG_DFL over SIG_IGN DECLINES WHILE SIGPIPE IS BLOCKED -- the
    spec's hidden-pending rule ([Signal.sigpipe_hidden_pending_possible]):
    Linux may hold a SIGPIPE pending there that the model does not, and
    an install of SIG_DFL keeps it, so the unblock would kill on Linux
    and not in the model.  The same install with SIGPIPE open in the
    mask is answered, so the decline is the mask's and not the
    handler's. *)
Example rt_sigaction_sigpipe_dfl_over_hidden_pending :
  check_syscall (mkInput 134 [13; 4096; 0; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (with_copyins [(4096, 24%nat)] (mkEffect 0 [] []))
    (with_sigpipe_install (mkSigpipeAction false 0 0) (sigpipe_model 4096))
  = CheckUnmodeled /\
  check_syscall (mkInput 134 [13; 4096; 0; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (with_copyins [(4096, 24%nat)] (mkEffect 0 [] []))
    (with_sigpipe_install (mkSigpipeAction false 0 0) (sigpipe_model 0))
  = CheckOk (with_sigpipe_install (mkSigpipeAction true 0 0)
               (with_sigpipe_install (mkSigpipeAction false 0 0) (sigpipe_model 0))) [].
Proof. split; vm_compute; reflexivity. Qed.

(** Eight readable bytes at 4096 holding [sigmask(SIGSEGV)] = 1 << 10,
    little-endian, with NOTHING readable on either side.  The extent is
    the point as well as the contents: eight bytes is the kernel's
    [sigset_t], and a spec that read nine would answer -EFAULT here. *)
Definition mem_sigset_sigsegv : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 8)
           then Some (if bv_eqb a 4097 then 4 else 0)
           else None.

(** Eight readable bytes at 4096 holding [sigmask(SIGABRT)] = 1 << 5 =
    32, little-endian, laid out exactly as [mem_sigset_sigsegv] is.  It
    is the set musl's [abort] path hands [SIG_UNBLOCK]. *)
Definition mem_sigset_sigabrt : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 8)
           then Some (if bv_eqb a 4096 then 32 else 0)
           else None.

(** The initial model, spelled once.  Its blocked mask is
    [demo_input]'s, which is 0.

    THAT ZERO IS WHY THE SECOND MODEL EXISTS.  A case that installs a
    mask over an entry mask of 0 cannot tell an install of 0 from no
    install at all: [with_sigmask 0 sig_model] and [sig_model] reduce to
    the same record, so [vm_compute] equates them and a spec that
    dropped the install entirely would still pass.  [sig_model_blocked]
    carries a non-zero entry mask so every arithmetic below lands on a
    number that is neither the entry mask nor 0.

    0x10006 is SIGINT (2), SIGQUIT (3) and SIGCHLD (17): [sigmask(n)] is
    [1 << (n - 1)] (include/linux/signal.h), so bit 1 | bit 2 | bit 16.

    SIGCHLD IS IN IT TO PUT A BIT ABOVE BYTE 0, and that is the second
    coincidence this fixture exists to break.  The copy-out is eight
    little-endian bytes, so a mask under 256 leaves bytes 1..7 all zero
    — and a spec that wrote [bv_unsigned old mod 256], or that applied
    [sigmask_strip] to the value going OUT as well as the one coming in,
    would be indistinguishable from a correct one.  Byte 2 of 0x10006 is
    1, so both mistakes are caught. *)
Definition sig_model : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

Definition sig_entry_mask : word := Z_to_bv 64 65542.

Definition sig_model_blocked : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
       default_nofile sig_entry_mask hwcap_rv64gc false Sv48).

(** The copy-from-user ledger every arm PAST the copy must carry: the
    eight bytes of [sigset_t] at [nset].  [Sys.Kernel.Signal]'s
    [record_copyins] puts it there, and [State.materialize_model_accesses]
    charges its lazy anonymous backing against [State.vm_limit]. *)
Definition sig_copyin : list (word * nat) := [(4096, 8%nat)].

(** BLOCKING SIGSEGV IS ACCEPTED.  This is the case the spec exists to
    justify: the model excludes [RiscvSemantics.MachineFault] from
    [Run.unmodeled_at] on the grounds that a real process dies there
    too, and blocking SIGSEGV does not change that —
    [force_sig_info_to_task] (kernel/signal.c) resets the disposition to
    SIG_DFL and calls [sigdelset(&t->blocked, sig)] before sending.  So
    there is no accepted-signal list here, and pinning that in Rocq
    means the over-cautious "fix" that adds one fails the build rather
    than passing it quietly. *)
Example rt_sigprocmask_block_sigsegv_accepted :
  check_syscall (mkInput 135 [0; 4096; 0; 8; 0; 0] mem_sigset_sigsegv
                   (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model
  = CheckOk (with_sigmask (Z_to_bv 64 1024) sig_model) [].
Proof. check_eq. Qed.

(** SIGKILL and SIGSTOP are STRIPPED, not refused.
    [sigdelsetmask(&new_set, sigmask(SIGKILL)|sigmask(SIGSTOP))] runs
    before [sigprocmask] and says nothing, so the call SUCCEEDS with the
    two bits simply gone.  [sigmask(SIGKILL)] is 1 << 8 = 0x100 and
    [sigmask(SIGSTOP)] is 1 << 18 = 0x40000.

    THE SET IS 0x40105, NOT 0x40100, and the difference is the whole
    value of the fixture: SIGHUP (1) and SIGQUIT (3) ride along, so the
    strip leaves 0x5 rather than 0.  A set of exactly the two
    kernel-only signals would install 0 — which is both what a spec that
    skipped the install over an entry mask of 0 leaves behind and what
    one that installed nothing at all does.  Surviving bits are what
    make the three [how] arithmetics land on three different numbers. *)
Definition mem_sigset_kill_stop : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 8)
           then Some (if bv_eqb a 4096 then 5
                      else if bv_eqb a 4097 then 1
                      else if bv_eqb a 4098 then 4 else 0)
           else None.

(** Over an entry mask of 0 this case cannot discriminate, for the
    reason [sig_model_blocked] exists — so it is stated over the blocked
    model.  The entry mask is 0x10006 and the strip lands on 0x5.  A
    spec that skipped the strip would install 0x40105; one that skipped
    the install would leave 0x10006; one that dropped the surviving bits
    with the kernel-only ones would leave 0.  All three differ from the
    0x5 asserted here. *)
Example rt_sigprocmask_kill_stop_stripped_not_refused :
  check_syscall (mkInput 135 [2; 4096; 0; 8; 0; 0] mem_sigset_kill_stop
                   (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
  = CheckOk (with_sigmask (Z_to_bv 64 5) sig_model_blocked) [].
Proof. check_eq. Qed.

(** THE OTHER TWO ARITHMETICS, over the same entry mask and the same
    stripped set, so the three land on three different numbers:

      SIG_BLOCK    0x10006 | 0x5  = 0x10007
      SIG_UNBLOCK  0x10006 & ~0x5 = 0x10002
      SIG_SETMASK                   0x5      (above)

    WHY ALL THREE AND NOT JUST ONE.  [sigmask_apply] is three lines and
    each is a different Linux function ([sigorsets], [sigandnsets],
    assignment — kernel/signal.c, [sigprocmask]), so a case set that
    pins one arm constrains the other two not at all.  With only the
    SIG_SETMASK case above, every one of these wrong implementations
    would still pass this file: SIG_BLOCK ignoring [old], SIG_UNBLOCK
    returning [old] unchanged, and SIG_UNBLOCK computing [old & new]
    instead of [old & ~new].  The operand 0x5 and the entry mask 0x10006
    share exactly one bit, which is what makes [and] and [andnot] give
    different answers here. *)
Example rt_sigprocmask_block_unions :
  check_syscall (mkInput 135 [0; 4096; 0; 8; 0; 0] mem_sigset_kill_stop
                   (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
  = CheckOk (with_sigmask (Z_to_bv 64 65543) sig_model_blocked) [].
Proof. check_eq. Qed.

Example rt_sigprocmask_unblock_clears :
  check_syscall (mkInput 135 [1; 4096; 0; 8; 0; 0] mem_sigset_kill_stop
                   (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
  = CheckOk (with_sigmask (Z_to_bv 64 65538) sig_model_blocked) [].
Proof. check_eq. Qed.

(** ...and SIG_UNBLOCK is not SIG_BLOCK's answer, stated as a rejection
    so the pair cannot both be satisfied by a spec that confuses them. *)
Example rt_sigprocmask_unblock_is_not_block :
  check_syscall (mkInput 135 [1; 4096; 0; 8; 0; 0] mem_sigset_kill_stop
                   (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model_blocked
  = CheckOk (with_sigmask (Z_to_bv 64 65543) sig_model_blocked) [] -> False.
Proof. vm_compute. discriminate. Qed.

(** The family it declines: an [oldset] the
    copy-out cannot be shown to succeed at.  The model has the mask,
    so this is not about the value but about the DESTINATION.  Nothing
    in this input's writable map is at 8192, so the copy-out finds the
    range short — and short is declined rather than answered -EFAULT,
    because riscv's forward-copying [raw_copy_to_user] may have stored
    the leading bytes before faulting and a partial store is user-visible
    state this model does not represent.  Same call as the first, but
    for the third argument. *)
Example rt_sigprocmask_oldset_unmodeled :
  check_syscall (mkInput 135 [0; 4096; 8192; 8; 0; 0] mem_sigset_sigsegv
                   (fun _ => None))
    (mkEffect 0 [] []) sig_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** A writable eight bytes at 8192, so the copy-out can be shown to
    succeed.  Contents are irrelevant — [copy_to_user] overwrites them —
    but the map has to be TOTAL over the range, because a short range is
    what [rt_sigprocmask_oldset_unmodeled] above declines on. *)
Definition wmem_oldset : word -> option byte :=
  fun a => if bv_leu 8192 a && bv_ltu a (8192 + 8) then Some 0 else None.

(** THE READ-BACK.  A pure query — NULL
    [nset], non-NULL [oset] — hands back the mask the process is holding,
    as eight little-endian bytes, and installs nothing.  The entry mask
    is 6, so byte 0 is 6 and the other seven are 0.

    Not reachable by a real run, and that is why it is here: the value
    asserted is [State.ProcInput]'s [in_sigmask], which the environment
    chooses.  A program can only ever check a mask IT installed, so no
    program can pin what an untouched entry mask reports.  The model
    changes not at all — [sigprocmask] is reached only from inside
    [if (nset)] (kernel/signal.c,
    [SYSCALL_DEFINE4(rt_sigprocmask)]), so a query with a garbage [how]
    would answer identically. *)
Example rt_sigprocmask_oldset_reports_entry_mask :
  check_syscall (mkInput 135 [0; 0; 8192; 8; 0; 0] (fun _ => None)
                   wmem_oldset)
    (mkEffect 0 [(8192, [6; 0; 1; 0; 0; 0; 0; 0])] []) sig_model_blocked
  = CheckOk sig_model_blocked [].
Proof. vm_compute. reflexivity. Qed.

(** A MASK THE PROCESS COULD NOT HAVE HAD, REFUSED.  0x40100 is
    {SIGKILL, SIGSTOP} — [Run.valid_sigmask] excludes it from every entry
    mask, and no install can introduce it because
    [sigdelsetmask(&new_set, sigmask(SIGKILL)|sigmask(SIGSTOP))] clears
    both.  So no kernel answer puts those bits in [oset], and a lying
    one is rejected.

    WHICH ARM DOES THE REFUSING MATTERS, because the obvious reading is
    wrong: it is NOT any invariant about which masks are possible — the
    checker holds no such invariant.  It is the byte-for-byte equality
    against the mask the model is carrying.  Any wrong value is refused
    the same way, which is the stronger property; this one is pinned
    because it is the value an adversary would pick. *)
Example rt_sigprocmask_oldset_impossible_mask_rejected :
  check_syscall (mkInput 135 [0; 0; 8192; 8; 0; 0] (fun _ => None)
                   wmem_oldset)
    (mkEffect 0 [(8192, [0; 1; 4; 0; 0; 0; 0; 0])] []) sig_model_blocked
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** And the same refusal for the value a POST-INSTALL snapshot would
    produce.  [old_set = current->blocked] is taken before
    [sigprocmask] runs, so a SIG_SETMASK to {SIGKILL, SIGSTOP} over an
    entry mask of 6 reports 6 and installs 0.  A kernel that reported
    the installed 0 instead is refused — and, unlike the case above,
    this one separates two orderings rather than two values, which is
    the mistake a reimplementation actually makes. *)
Example rt_sigprocmask_oldset_is_not_the_new_mask :
  check_syscall (mkInput 135 [2; 4096; 8192; 8; 0; 0] mem_sigset_kill_stop
                   wmem_oldset)
    (with_copyins sig_copyin (mkEffect 0 [(8192, [5; 0; 0; 0; 0; 0; 0; 0])] []))
    sig_model_blocked
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** The same call told truthfully: [oset] gets the entry mask 6, the
    installed mask is the stripped 0, and the copy-in ledger carries the
    eight bytes at [nset] that the -EINVAL arm before it would not. *)
Example rt_sigprocmask_oldset_snapshot_precedes_install :
  check_syscall (mkInput 135 [2; 4096; 8192; 8; 0; 0] mem_sigset_kill_stop
                   wmem_oldset)
    (with_copyins sig_copyin (mkEffect 0 [(8192, [6; 0; 1; 0; 0; 0; 0; 0])] []))
    sig_model_blocked
  = CheckOk (with_sigmask (Z_to_bv 64 5) sig_model_blocked) [].
Proof. check_eq. Qed.

(** THE NO-ROLLBACK CORNER.  [copy_to_user] is the syscall's last
    statement and there is no restore path, so an [oset] whose range
    ends past [State.TASK_SIZE] returns -EFAULT WITH THE NEW MASK ALREADY
    INSTALLED.  The model has to record the install on a failing call,
    which is the one obligation [Kernel.Sys.prlimit64_spec] declines
    rather than take on.

    2^64-8 is the address shape that reaches this arm: [State.access_okb]
    subtracts in [Z], so the range ends at 2^64 and is over
    [State.TASK_SIZE].  A merely unmapped [oset] below that limit is
    declined instead, which is [rt_sigprocmask_oldset_unmodeled]. *)
Example rt_sigprocmask_oldset_efault_still_installs :
  check_syscall (mkInput 135 [2; 4096; Z_to_bv 64 (2^64 - 8); 8; 0; 0]
                   mem_sigset_kill_stop wmem_oldset)
    (with_copyins sig_copyin (mkEffect (errno_ret EFAULT) [] []))
    sig_model_blocked
  = CheckOk (with_sigmask (Z_to_bv 64 5) sig_model_blocked) [].
Proof. check_eq. Qed.

(** ...and the same call answering 0 is refused, because [access_ok]
    refuses that range outright — a success there would be a kernel
    answer no [__access_ok] permits
    (include/asm-generic/access_ok.h). *)
Example rt_sigprocmask_oldset_over_task_size_never_succeeds :
  check_syscall (mkInput 135 [2; 4096; Z_to_bv 64 (2^64 - 8); 8; 0; 0]
                   mem_sigset_kill_stop wmem_oldset)
    (with_copyins sig_copyin (mkEffect 0 [] []))
    sig_model_blocked
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** And the ordering nobody expects: [sigprocmask] is reached only from
    inside [if (nset)], so with a NULL new set its [switch (how)] — and
    its -EINVAL — never run.  A [how] of 999 is a plain 0.  Pinning it
    here means a "fix" to -EINVAL cannot compile. *)
Example rt_sigprocmask_null_set_ignores_how :
  check_syscall (mkInput 135 [999; 0; 0; 8; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [] []) sig_model
  = CheckOk sig_model [].
Proof. vm_compute. reflexivity. Qed.

(** THE THREE ORDERINGS, each pinned against the answer the next rule
    down would give.

    1. A wrong [sigsetsize] beats a wild [nset]: the size test is the
       first statement of [SYSCALL_DEFINE4(rt_sigprocmask)], before
       [old_set = current->blocked] and before the [if (nset)] that
       holds the only [copy_from_user].  So an unreadable set with size
       0 is -EINVAL, NOT -EFAULT. *)
Example rt_sigprocmask_bad_size_beats_unreadable_set :
  check_syscall (mkInput 135 [1; 8192; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) sig_model
  = CheckOk sig_model []
  /\ check_syscall (mkInput 135 [1; 8192; 0; 0; 0; 0] (fun _ => None)
                     (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) sig_model
     = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** 2. And it beats the [oldset] decline too, which is the one pair
       where the model is narrower than Linux in the other direction:
       the size is wrong, so nothing about [oldset] is ever reached. *)
Example rt_sigprocmask_bad_size_beats_oldset_decline :
  check_syscall (mkInput 135 [1; 0; 8192; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) sig_model
  = CheckOk sig_model [].
Proof. vm_compute. reflexivity. Qed.

(** 3. An unreadable set beats a bad [how]: inside [if (nset)] the
       [copy_from_user] runs two statements before [sigprocmask], so
       -EFAULT is the answer and the honest -EINVAL is rejected. *)
Example rt_sigprocmask_efault_beats_bad_how :
  check_syscall (mkInput 135 [3; 8192; 0; 8; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) sig_model
  = CheckOk sig_model []
  /\ check_syscall (mkInput 135 [3; 8192; 0; 8; 0; 0] (fun _ => None)
                     (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) sig_model
     = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** [how] is [int], so only its low half decides: [(1 << 32) | 1] is
    SIG_UNBLOCK, and [(1 << 32) | 3] is still the -EINVAL that 3 is.
    [sigsetsize] is [size_t] and does NOT narrow, so a register whose
    low half is 8 is the wrong size.

    The first conjunct installs, and over [sig_model]'s empty entry mask
    SIG_UNBLOCK of SIGSEGV installs 0 — so this case cannot tell that
    install from no install at all.  It does not need to: what it
    separates is the truncated [how], which decides success against
    -EINVAL here, and the arithmetic is pinned over a non-empty entry
    mask by [rt_sigprocmask_unblock_clears] and its two siblings. *)
Example rt_sigprocmask_how_truncates_size_does_not :
  check_syscall (mkInput 135 [Z_to_bv 64 (2 ^ 32 + 1); 4096; 0; 8; 0; 0]
                   mem_sigset_sigsegv (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [] [])) sig_model
  = CheckOk (with_sigmask (Z_to_bv 64 0) sig_model) []
  /\ check_syscall (mkInput 135 [Z_to_bv 64 (2 ^ 32 + 3); 4096; 0; 8; 0; 0]
                     mem_sigset_sigsegv (fun _ => None))
       (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) sig_model
     = CheckOk sig_model []
  /\ check_syscall (mkInput 135 [1; 4096; 0; Z_to_bv 64 (2 ^ 32 + 8); 0; 0]
                     mem_sigset_sigsegv (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) sig_model
     = CheckOk sig_model [].
Proof. repeat split; check_eq. Qed.

(** THE COPY-FROM-USER LEDGER SEPARATES THE TWO -EINVALs, which is the
    one thing about this call that an empty ledger would silently get
    wrong.  Both of these return -EINVAL.  The first is arm 1: the
    [sigsetsize] test is the first statement of
    [SYSCALL_DEFINE4(rt_sigprocmask)], so it is answered before [nset]
    is looked at and NO user memory is read.  The second is arm 4b: the
    size was right, the eight bytes were copied, and only then did
    [sigprocmask]'s [switch (how)] reject the [how].  Same return, same
    model, same events — and different ledgers.  Swapping either
    expectation is rejected, which is what makes the distinction
    load-bearing rather than decorative. *)
Example rt_sigprocmask_copyins_separate_the_two_einvals :
  (* arm 1: size wrong, nothing read *)
  check_syscall (mkInput 135 [0; 4096; 0; 0; 0; 0] mem_sigset_sigsegv
                   (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) sig_model
  = CheckOk sig_model []
  (* arm 4b: size right, eight bytes read, then the how rejected *)
  /\ check_syscall (mkInput 135 [3; 4096; 0; 8; 0; 0] mem_sigset_sigsegv
                     (fun _ => None))
       (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) sig_model
     = CheckOk sig_model []
  (* and neither ledger is admissible in the other's place *)
  /\ check_syscall (mkInput 135 [0; 4096; 0; 0; 0; 0] mem_sigset_sigsegv
                     (fun _ => None))
       (with_copyins sig_copyin (mkEffect (errno_ret EINVAL) [] [])) sig_model
     = CheckReject
  /\ check_syscall (mkInput 135 [3; 4096; 0; 8; 0; 0] mem_sigset_sigsegv
                     (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) sig_model
     = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** An -EFAULT records NOTHING, because the copy FAILED.  Same
    convention as [Kernel.Sys.prlimit64_spec]'s -EFAULT arm, which sits
    outside its [record_copyins]. *)
Example rt_sigprocmask_efault_records_no_copyin :
  check_syscall (mkInput 135 [1; 8192; 0; 8; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) sig_model
  = CheckOk sig_model []
  /\ check_syscall (mkInput 135 [1; 8192; 0; 8; 0; 0] (fun _ => None)
                     (fun _ => None))
       (with_copyins [(8192, 8%nat)] (mkEffect (errno_ret EFAULT) [] []))
       sig_model
     = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** THE LEDGER SEPARATES THE TWO -EINVALs for an out-of-range signal.
    With [act] NULL nothing is copied and arm 3 answers -EINVAL; with
    [act] readable, [SYSCALL_DEFINE4(rt_sigaction)] copies the 24 bytes
    first and [do_sigaction] answers the same -EINVAL after it.  Same
    return, same model, different ledgers, and neither ledger is
    admissible in the other's place.  An unreadable [act] is -EFAULT and
    records nothing, because the copy failed. *)
Example rt_sigaction_copyins_separate_the_two_einvals :
  check_syscall (mkInput 134 [65; 0; 0; 8; 0; 0] mem_sigaction_zero (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) sig_model
  = CheckOk sig_model []
  /\ check_syscall (mkInput 134 [65; 4096; 0; 8; 0; 0] mem_sigaction_zero
                     (fun _ => None))
       (with_copyins [(4096, 24%nat)] (mkEffect (errno_ret EINVAL) [] [])) sig_model
     = CheckOk sig_model []
  /\ check_syscall (mkInput 134 [65; 0; 0; 8; 0; 0] mem_sigaction_zero (fun _ => None))
       (with_copyins [(4096, 24%nat)] (mkEffect (errno_ret EINVAL) [] [])) sig_model
     = CheckReject
  /\ check_syscall (mkInput 134 [65; 4096; 0; 8; 0; 0] mem_sigaction_zero
                     (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) sig_model
     = CheckReject
  /\ check_syscall (mkInput 134 [2; 8192; 0; 8; 0; 0] mem_sigaction_zero (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) sig_model
     = CheckOk sig_model []
  /\ check_syscall (mkInput 134 [2; 8192; 0; 8; 0; 0] mem_sigaction_zero (fun _ => None))
       (with_copyins [(8192, 24%nat)] (mkEffect (errno_ret EFAULT) [] [])) sig_model
     = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** WRITING NOTHING IS AN OBLIGATION, NOT AN ABSENCE.  This arm changes
    model state — it installs a mask — and touches no user memory, and an
    arm that touches no user memory could be satisfied by any effect at
    all if the checker only looked at the return value.  It demands all
    five effect lists be empty instead, so an effect claiming a write —
    here one byte at the new set's own address — is REJECTED.  Without
    this, a target could smuggle a store through a call whose only
    visible answer is 0. *)
Example rt_sigprocmask_success_admits_no_write :
  check_syscall (mkInput 135 [0; 4096; 0; 8; 0; 0] mem_sigset_sigsegv
                   (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [(4096, [0])] [])) sig_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** THE CLOSED-SURFACE ENUMERATION, MACHINE-CHECKED.

    [Kernel.Signal]'s header argues that the mask this model tracks is
    the one Linux would have, and it discharges the in-model half of
    that by enumerating every syscall that reads [->blocked], installs a
    mask, or can deliver or send a signal, and asserting none of them
    has an arm.  The model writes its mask at ONE place, this syscall;
    every number below is a second writer or a second reader, and any of
    them would make the value [oset] hands back stale.  This pair of
    examples makes that assertion a check the build reads rather than a
    HAND check written into a comment: a later change that modeled any
    of these numbers fails here, rather than leaving the header quietly
    claiming a window it had just opened.

    Two numbers the header names are deliberately NOT here: [clone]
    (220) and [clone3] (435).  The header excludes them on purpose and
    says why — their window is shut by [Run.sstep] having no transition
    that starts a second task, not by the table, so it stays shut
    whether or not they have an arm.  Listing them would make this
    lemma fail the day someone adds a parent-side arm for either,
    which is exactly the rot the header warns against.

    MORE ARE NOT HERE, and the reason is the
    whole point of the list rather than an exception to it:
    [rt_sigaction] (134), [pselect6] (72), [epoll_pwait] (22),
    [ppoll] (73) and [sigaltstack] (132) HAVE
    arms.  No window is open, but none is shut by absence from
    [Specs.modeled_sysnos] — each is shut by its own SPEC, one
    level down:

      - 132 has no window to shut, and it is worth saying so rather
        than leaving the reader to infer it from the shape of the
        others.  [do_sigaltstack] (kernel/signal.c) reads and writes
        [sas_ss_sp], [sas_ss_size] and [sas_ss_flags], names [blocked]
        nowhere, and [SYSCALL_DEFINE2(sigaltstack)] calls no
        [set_user_sigmask]; it is only defined in the
        same kernel file, which is not the same thing.
        [sigaltstack_leaves_the_mask_alone] below checks
        the arm's post-model.

      - 134's window is [oact], the only way to read an [sa_mask] back,
        and [Signal.rt_sigaction_spec] declines a non-NULL [oact].  The
        [sa_mask] an accepted install carries is not stored either —
        that spec answers [ret_only 0] and stores no disposition — so there is
        no second window behind the first.
      - 72's window is the real thing: [set_user_sigmask] saves
        [current->blocked] into [current->saved_sigmask] and installs
        the caller's, which is a read AND a write.  [Fs.Select]'s
        [pselect_sigpack] classifies exactly that case as [PsSigReal]
        and [pselect6_outcome] answers [None] for it, so the modeled
        surface contains pselect6 only where no mask is installed.  The
        error arms that are answered ahead of it — an unreadable
        argpack, a bad timeout — are answered before
        [set_user_sigmask] runs in the kernel too, so none of them
        installs a mask either.
      - 22's window is the SAME [set_user_sigmask], reached from
        [do_epoll_pwait] rather than [do_pselect].  [Fs.EventPoll]'s
        [epoll_sigmask] classifies a call that would install a mask as
        [EpSigReal], and [epoll_pwait_outcome] answers [None] for it.
        There is no error arm ahead of it that installs one either, and
        for a tighter reason than pselect6's: [set_user_sigmask] is the
        FIRST fallible step of [do_epoll_pwait], so the only errnos
        admitted before the epfd is even looked up are the two
        [set_user_sigmask] itself returns.
      - 130's and 131's window is neither a read-back nor an install: it
        is DELIVERY.  [tkill] and [tgkill] can put a signal in
        [task->pending], and the mask is what decides whether the process
        takes it now or later, so a modeled signal-sender is a second
        thing the mask's value governs.
        [Signal.tkill_self] reads the mask through
        [Signal.sigabrt_blocked] and writes NOTHING to it — the pending
        bit goes in [State.procst_sigabrt_pending], beside the mask
        rather than in it — so [oset] still hands back the value
        [rt_sigprocmask] itself last installed.  What the pair adds is on
        the OTHER side of the same coin, and is modeled too: with a
        signal pending, installing a mask can end the process, which is [Signal.set_sigmask_deliver] inside
        [rt_sigprocmask] itself rather than a second writer.  The
        envelope is one signal (SIGABRT) to one target (the caller's own
        tid) under one declaration ([State.in_abort_terminal]); every
        other shape is [unmodeled], so no other signal can become pending
        and no other mask bit can matter.
      - 73's is that same [set_user_sigmask] a third time, reached from
        [SYSCALL_DEFINE5(ppoll, ...)] with the mask pointer and the size
        as separate arguments rather than through an argpack.
        [Fs.Select]'s [ppoll_sigmask] classifies a call that would
        install a mask as [PpSigReal] and [ppoll_outcome] answers [None]
        for it.  The two error arms ahead of it are the timeout's, which
        the kernel raises before [set_user_sigmask] runs, so neither
        installs a mask either — pselect6's argument exactly, one
        argument shape over.

    Any of them on this list would fail the build with a message
    blaming the wrong thing; leaving one off silently would drop a check.
    So each has a check of the fact that actually closes it,
    [rt_sigaction_oact_read_back_declined], [pselect6_real_mask_declined],
    [epoll_pwait_real_mask_declined], [ppoll_real_mask_declined] and
    [sigaltstack_leaves_the_mask_alone] below — the same treatment the
    header gives the raising specs it excepts, and 130 and 131
    get [tkill_reads_the_mask_and_writes_none] and [tkill_off_declined]
    for the same reason.  The numbers are named and not counted: when
    this group grows, a count is the part that goes stale. *)
Definition sig_mask_windows : list Z :=
  ([ 74   (* signalfd4         *) ; 117 (* ptrace            *)
   ; 129  (* kill              *)
   ; 133  (* rt_sigsuspend     *)
   ; 136  (* rt_sigpending     *) ; 137 (* rt_sigtimedwait   *)
   ; 138  (* rt_sigqueueinfo   *) ; 139 (* rt_sigreturn      *)
   ; 240  (* rt_tgsigqueueinfo *) ; 292 (* io_pgetevents     *)
   ; 424  (* pidfd_send_signal *) ; 426 (* io_uring_enter    *)
   ; 441  (* epoll_pwait2      *) ])%Z.

(** ADMISSION REASON (the third at the top of [Checks/Examples.v]): this
    pins a model CONSTANT, [Specs.modeled_sysnos], that no observation of
    a real execution reveals.  A run can show that ONE number fails
    closed on ONE input; it cannot establish what a constant does not
    contain, and the header's argument is about the whole set at once.

    POSITIVE: every window in the list is outside [Specs.modeled_sysnos],
    so [DispatchSurface.syscall_spec_unmodeled_outside] carries each of
    them to [Unmodeled] without this file re-deriving it.  Adding an arm
    for any number on the list fails HERE, which is the point.

    The list is spelled out in full rather than counted, and it is worth
    saying why: a list that silently dropped a member would still read
    as a complete check of the header's enumeration while leaving that
    member unchecked.  A count in the prose would not catch that — it
    would only have to agree with itself.  What catches it is
    reading the header's numbers off and comparing them to these. *)
Example sig_mask_windows_all_declined :
  forallb (fun n => negb (existsb (Z.eqb n) modeled_sysnos))
    sig_mask_windows = true.
Proof.
  lazymatch eval vm_compute in
    (forallb (fun n => negb (existsb (Z.eqb n) modeled_sysnos))
       sig_mask_windows) with
  | true => vm_compute; reflexivity
  | _ => fail "a syscall that reads ->blocked, installs a mask, or can deliver or send a signal now HAS a dispatch arm -- it is a second reader or writer of the mask rt_sigprocmask tracks, so the value oset hands back may now be stale; model what that syscall does to the mask in the same commit"
  end.
Qed.

(** THE OTHER HALF OF THE ENUMERATION: the one signal-mask window that
    is on the modeled surface, shut by its spec rather than by its
    absence.  [rt_sigaction]'s [oact] would hand an [sa_mask] back;
    [Signal.rt_sigaction_spec] declines a non-NULL one, so nothing
    modeled can read a mask through 134 either.

    ADMISSION REASON: the same third reason as the list above — this
    pins where a spec's decline sits relative to the modeled surface,
    and a run cannot show that a decline is the only way out.

    The anti-vacuity control is already in this file:
    [rt_sigaction_sigint_accepted] is the same signal and the same
    struct with [oact] NULL, and it is [CheckOk].  If that one ever
    became [CheckUnmodeled] this example would pass for the wrong
    reason — 134 declining everything — and stop measuring [oact]. *)
Example rt_sigaction_oact_read_back_declined :
  check_syscall (mkInput 134 [2; 4096; 4096; 8; 0; 0] mem_sigaction_zero
                   (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** The memory the two pselect6 cases below share: a [struct
    sigset_argpack] at 4096 naming a REAL mask — the [sigset_t *] is 8192
    (little-endian, so 0x20 at offset 1) and the [size_t] is the kernel's
    8 — and a zero [struct timespec] at 4128.  The pointed-to mask is
    deliberately NOT readable: [Fs.Select.pselect_sigpack] never reads it,
    and the extent is part of what these pin.

    The timeout is there so the two cases differ in ONE thing.  With a
    NULL timeout pselect6 is declined for a different reason entirely —
    an infinite wait it cannot return from — which would make the control
    below pass without saying anything about the mask. *)
Definition mem_pselect_mask_and_timeout : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 16)
           then Some (if bv_eqb a 4097 then 32
                      else if bv_eqb a 4104 then 8
                      else 0)
           else if bv_leu 4128 a && bv_ltu a (4128 + 16)
           then Some 0
           else None.

Definition wmem_pselect_timeout : word -> option byte :=
  fun a => if bv_leu 4128 a && bv_ltu a (4128 + 16) then Some 0 else None.

(** THE SECOND MASK WINDOW ON THE MODELED SURFACE, and the one that is a
    genuine read-back rather than a hypothetical: [set_user_sigmask]
    saves [current->blocked] into [current->saved_sigmask] before
    installing the caller's mask.  [pselect6] declines every call that
    would reach it.

    ADMISSION REASON: the same third reason as the list above — it pins
    where a spec's decline sits relative to the modeled surface, which no
    observation of one execution establishes.

    Its control is the example below, identical but for a NULL sixth
    argument. *)
Example pselect6_real_mask_declined :
  check_syscall (mkInput 72 [0; 0; 0; 0; 4128; 4096]
                   mem_pselect_mask_and_timeout wmem_pselect_timeout)
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** THE CONTROL, and the reason it is a [<>] rather than an equality:
    what it has to rule out is pselect6 having become unconditionally
    [CheckUnmodeled], which would make the example above pass while
    measuring nothing about the mask.  Any other verdict does that — a
    [CheckReject] here means the checker got past the decline and reached
    the effect comparison, which is exactly the fact in question.  Pinning
    the accepted effect instead would pin [poll_select_finish]'s
    timeout write-back, which belongs to [Checks.Cases.Fs.Select] and not
    to this file. *)
Example pselect6_no_mask_is_not_declined :
  check_syscall (mkInput 72 [0; 0; 0; 0; 4128; 0]
                   mem_pselect_mask_and_timeout wmem_pselect_timeout)
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

(** THE THIRD MASK WINDOW ON THE MODELED SURFACE, and it is the same
    [set_user_sigmask] read-back [pselect6] has — reached from
    [do_epoll_pwait] (fs/eventpoll.c) instead of from [do_pselect].
    [epoll_pwait] declines every call that would reach the install.

    ADMISSION REASON: the same third reason as the list above — it pins
    where a spec's decline sits relative to the modeled surface, which no
    observation of one execution establishes.

    The arguments are [epfd = 0], [events = 4096], [maxevents = 1],
    [timeout = 0], then the mask pair — and the mask is at 4128, NOT at
    4096.  [mem_pselect_mask_and_timeout] is reused rather than a fresh
    fixture because all this needs of it is eight readable bytes at each
    of two addresses, which it already has; the mask's CONTENTS are
    immaterial, since what is being declined is that a mask would be
    installed at all.  The two addresses are DIFFERENT on purpose: a
    fixture that put the events buffer and the mask at one address could
    not tell argument 1 from argument 4, so a spec that read the wrong
    one would satisfy this example unchanged.

    Its control is the example below, identical but for a NULL fifth
    argument — one changed argument, so a pass cannot come from
    somewhere else. *)
Example epoll_pwait_real_mask_declined :
  check_syscall (mkInput 22 [0; 4096; 1; 0; 4128; 8]
                   mem_pselect_mask_and_timeout (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** THE CONTROL, a [<>] for the same reason [pselect6]'s is: what it has
    to rule out is [epoll_pwait] having become unconditionally
    [CheckUnmodeled], which would make the example above pass while
    measuring nothing about the mask.  With a NULL mask the call runs on
    to -EINVAL (fd 0 is open, [maxevents] is in range, and the [events]
    range passes [access_ok]), and the effect offered here is a bare 0,
    so the checker reaches the effect comparison and rejects — which is
    exactly the fact in question. *)
Example epoll_pwait_no_mask_is_not_declined :
  check_syscall (mkInput 22 [0; 4096; 1; 0; 0; 0]
                   mem_pselect_mask_and_timeout (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

(** THE FOURTH MASK WINDOW ON THE MODELED SURFACE, and it is
    [set_user_sigmask] once more — reached from
    [SYSCALL_DEFINE5(ppoll, ...)] (fs/select.c), which passes the mask
    pointer and the size as two arguments where pselect6 packs them into
    one.  [ppoll] declines every call that would reach the install.

    ADMISSION REASON: the same third reason as the list above — it pins
    where a spec's decline sits relative to the modeled surface, which no
    observation of one execution establishes.

    The arguments are [ufds = 0], [nfds = 0], [tsp = 4128], then the mask
    at 4096 and the size 8.  [mem_pselect_mask_and_timeout] is reused
    because the eight readable bytes it already has at 4096 are all a
    real mask needs here, and its zero timespec at 4128 is what keeps the
    control below from being declined for a different reason: a NULL
    timeout with nothing requested never returns, which [Fs.Select]
    declines whatever the mask is.

    Its control is the example below, identical but for a NULL fourth
    argument. *)
Example ppoll_real_mask_declined :
  check_syscall (mkInput 73 [0; 0; 4128; 4096; 8; 0]
                   mem_pselect_mask_and_timeout wmem_pselect_timeout)
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** THE CONTROL, a [<>] for the same reason the two above are: what it
    has to rule out is [ppoll] having become unconditionally
    [CheckUnmodeled], which would make the example above pass while
    measuring nothing about the mask.  With a NULL mask the call is an
    ordinary zero-timeout poll of nothing, which returns 0 and writes
    nothing. *)
Example ppoll_no_mask_is_not_declined :
  check_syscall (mkInput 73 [0; 0; 4128; 0; 0; 0]
                   mem_pselect_mask_and_timeout wmem_pselect_timeout)
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

(** NEGATIVE: the same computation is FALSE the moment a number on the
    modeled surface joins the list.  Without this, an empty
    [modeled_sysnos] — or a [Z.eqb] that never matched — would satisfy
    the example above and prove nothing at all.  135 is the witness
    because it is the arm this file exists for.

    Why this is a [= false] and not a [= CheckReject]: a [CheckReject]
    rejects an EFFECT, and this
    claim has no effect in it — it is about the contents of a list.  The
    constructed-wrong-behaviour half is therefore the same computation
    run over a list that has been made wrong, which is what the second
    conjunct is.  Planting 135 into [sig_mask_windows] stops the file
    with the failure message above. *)
Example sig_mask_windows_not_vacuous :
  existsb (Z.eqb 135) modeled_sysnos = true
  /\ forallb (fun n => negb (existsb (Z.eqb n) modeled_sysnos))
       ((135%Z) :: sig_mask_windows) = false.
Proof. split; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------ sigaltstack *)

(** A [stack_t] at 4096 that [Kernel.Signal.sigaltstack_spec] accepts:
    [ss_sp] = 0x2000, [ss_flags] = 0, [ss_size] = 0x4000 (16 KiB, which
    is above [Uapi.MINSIGSTKSZ]).  Exactly 24 bytes are readable and
    nothing on either side is, so a spec that read the 32-byte struct
    some libcs declare would answer -EFAULT here. *)
Definition mem_sigaltstack_ok : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 24)
           then Some (if bv_eqb a 4097 then 32
                      else if bv_eqb a 4113 then 64
                      else 0)
           else None.

(** The copy-from-user ledger every sigaltstack arm PAST the copy must
    carry: the 24 bytes of [stack_t] at [uss] = 4096, which
    [SYSCALL_DEFINE2(sigaltstack)] reads before [do_sigaltstack] runs. *)
Definition sas_copyin : list (word * nat) := [(4096, 24%nat)].

(** WHAT STANDS IN FOR 132 IN [sig_mask_windows].  132 has an arm, so
    the claim that [rt_sigprocmask]'s [oset] answer cannot go stale has
    to be made, for this number, about what the arm DOES: the
    post-model differs from the pre-model in the alternate-stack bit and
    in nothing else, the blocked mask included.  [do_sigaltstack]
    (kernel/signal.c) names [blocked] nowhere and
    [SYSCALL_DEFINE2(sigaltstack)] calls no [set_user_sigmask], so there
    is no window here; this example checks that fact rather than
    inferring it from an absence.

    ADMISSION REASON (the third at the top of [Checks/Examples.v]): it
    pins MODEL-INTERNAL STATE.  No observation of a real execution
    reveals the mask a process holds unless the process reads it back,
    and a program that read it back would be measuring [rt_sigprocmask].

    [sig_model_blocked] rather than [sig_model], for the reason that
    fixture exists: over an entry mask of 0 a spec that CLEARED the mask
    would pass this too. *)
Example sigaltstack_leaves_the_mask_alone :
  check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_ok
                   (fun _ => None))
    (with_copyins sas_copyin (mkEffect 0 [] [])) sig_model_blocked
  = CheckOk (with_sigaltstack_installed sig_model_blocked) []
  /\ m_sigmask (with_sigaltstack_installed sig_model_blocked) = sig_entry_mask.
Proof. split; vm_compute; reflexivity. Qed.

(** THE BIT IS WHAT MAKES ONE BIT ENOUGH, so the decline it produces is
    pinned against the model state directly rather than through a
    program that calls twice.  Same input, same memory, and the only
    difference is the bit [with_sigaltstack_installed] sets: the answer
    goes from the [CheckOk] above to [CheckUnmodeled].  The reason is in
    [Kernel.Signal.sigaltstack_spec]'s header — after an install both
    readers of the record take the user stack pointer, which no
    [SyscallInput] carries.

    ADMISSION REASON: the third again, and it is the same fixture used
    as its own control.  A program reaches the same decline the long
    way, by calling twice; what this adds is the decline stated on the
    STATE, so a spec
    that declined the second call for some unrelated reason — a wrong
    errno order, say — could not pass in its place. *)
Example sigaltstack_after_an_install_declined :
  check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_ok
                   (fun _ => None))
    (mkEffect 0 [] []) (with_sigaltstack_installed sig_model_blocked)
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** AN ERRNO LEAVES THE RECORD ALONE, which is the other half of the bit
    being sound: [do_sigaltstack] assigns the three fields under
    [if (!ret)], so the -ENOMEM path stores nothing and a later call
    still answers from execve's record.  A spec that set the bit on
    every path would decline everything after one undersized install.

    ADMISSION REASON: the third — the model state after a call is not
    something one trace shows. *)
Definition mem_sigaltstack_small : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 24)
           then Some (if bv_eqb a 4097 then 32
                      else if bv_eqb a 4113 then 4
                      else 0)
           else None.

Example sigaltstack_enomem_keeps_the_record :
  check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_small
                   (fun _ => None))
    (with_copyins sas_copyin (mkEffect (errno_ret ENOMEM) [] [])) sig_model_blocked
  = CheckOk sig_model_blocked [].
Proof. vm_compute. reflexivity. Qed.

(** WRITING NOTHING IS AN OBLIGATION, NOT AN ABSENCE — the same argument
    [rt_sigprocmask_success_admits_no_write] above makes, and it applies
    to every arm here because [sigaltstack] answers a bare return on all
    of them.  A checker that looked only at the return value would let a
    target smuggle a store through the call that installs its stack.

    ADMISSION REASON: the fourth — a [CheckReject] needs a kernel
    behaving inadmissibly, which no truthful run produces. *)
Example sigaltstack_success_admits_no_write :
  check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_ok
                   (fun _ => None))
    (with_copyins sas_copyin (mkEffect 0 [(4096, [0])] [])) sig_model_blocked
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** A DISABLE IS A SUCCESSFUL WRITE THAT DOES NOT SHUT THE DOOR, which
    is the one place where "the record has been written" and "a stack is
    installed" come apart.  [do_sigaltstack] (kernel/signal.c, Linux
    v6.18.46, commit 1f99e9ab748f) runs [ss_size = 0; ss_sp = NULL]
    before the store on its SS_DISABLE branch, so all three fields are
    assigned and the record it leaves is (NULL, 0, [ss_flags]) -- the
    same zero-size shape [begin_new_exec] left, in which [on_sig_stack]
    is false for every sp and [sas_ss_flags] returns SS_DISABLE for
    every sp.  Declining after it would give up answers the model still
    has, so [State.m_sigaltstack_installed] tracks a NON-ZERO
    [sas_ss_size] and not an assignment.

    The struct at 4096 is the ordinary disable: [ss_sp] 0, [ss_flags]
    SS_DISABLE at offset 8, [ss_size] 0.

    ADMISSION REASON (the third at the top of [Checks/Examples.v]): it
    pins MODEL-INTERNAL STATE.  A program sees the RETURN of the call
    after a disable; what no trace shows is which model the disable
    handed back. *)
Definition mem_sigaltstack_disable : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 24)
           then Some (if bv_eqb a 4104 then 2 else 0)
           else None.

(** The three conjuncts are the arm, what it buys, and the mistake it
    avoids.

    ONE: the disable answers 0 and hands back the model UNCHANGED -- had
    it set the bit the answer would be
    [CheckOk (with_sigaltstack_installed sig_model_blocked) []], which is
    a different term, so this equality is what pins the arm.

    TWO: a later call against that same model is still ANSWERED, and
    answered with a kernel errno rather than a shrug.  [mem_sigaltstack_small]
    is a 1 KiB stack under mode 0, which -ENOMEM refuses; the fast path
    cannot rescue it because that would need [ss_sp] and [ss_size] both
    equal to the stored (NULL, 0), which is the shape arm 7 declines.

    THREE, THE CONSTRUCTED MISTAKE: the very same call against the model
    a bit-setting disable WOULD hand back is [CheckUnmodeled].  That is
    the decline the arm avoids, stated on the state it would come from,
    so a suite that lost conjunct one would not quietly keep passing. *)
Example sigaltstack_disable_leaves_the_record_answerable :
  check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_disable
                   (fun _ => None))
    (with_copyins sas_copyin (mkEffect 0 [] [])) sig_model_blocked
  = CheckOk sig_model_blocked []
  /\ check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_small
                     (fun _ => None))
       (with_copyins sas_copyin (mkEffect (errno_ret ENOMEM) [] [])) sig_model_blocked
     = CheckOk sig_model_blocked []
  /\ check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_small
                     (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] [])
       (with_sigaltstack_installed sig_model_blocked)
     = CheckUnmodeled.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(** THE INSTALL STILL SHUTS IT.  Leaving the bit out of the disable arm
    would be worth nothing if it also went missing from the arm that
    raises the size, so the two arms are pinned against each other on
    the same fixture pair: [mem_sigaltstack_disable] hands the model back
    and [mem_sigaltstack_ok] -- 16 KiB, above [Uapi.MINSIGSTKSZ] -- sets
    the bit.  A spec that set the bit nowhere would satisfy the example
    above and fail this one.

    ADMISSION REASON: the third again, for the same reason. *)
Example sigaltstack_install_still_sets_the_bit :
  check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_ok
                   (fun _ => None))
    (with_copyins sas_copyin (mkEffect 0 [] [])) sig_model_blocked
  = CheckOk (with_sigaltstack_installed sig_model_blocked) []
  /\ check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_disable
                     (fun _ => None))
       (with_copyins sas_copyin (mkEffect 0 [] [])) sig_model_blocked
     <> CheckOk (with_sigaltstack_installed sig_model_blocked) [].
Proof. split; vm_compute; [reflexivity|discriminate]. Qed.

(** AND A DISABLE IS NOT A LICENCE, which is what stops the arm above
    from having been widened into "answer anything once disabled".  The
    same -ENOMEM call, offered a 0 instead, is REJECTED rather than
    admitted, and the smuggled store is rejected on the disable arm
    itself -- the arm writes no user memory, exactly like the other
    eight.

    ADMISSION REASON: the fourth -- a [CheckReject] needs a kernel
    behaving inadmissibly, which no truthful run produces. *)
Example sigaltstack_after_a_disable_rejects_a_false_success :
  check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_small
                   (fun _ => None))
    (with_copyins sas_copyin (mkEffect 0 [] [])) sig_model_blocked
  = CheckReject
  /\ check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_disable
                     (fun _ => None))
       (with_copyins sas_copyin (mkEffect 0 [(4096, [0])] [])) sig_model_blocked
     = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** THE LEDGER ON THE ERRNO ARMS.  A mode outside {0, SS_ONSTACK,
    SS_DISABLE} is -EINVAL from [do_sigaltstack], after the 24 bytes at
    [uss] were copied, so it carries them, and the same -EINVAL claiming
    no read is rejected.  An unreadable [uss] is -EFAULT from the copy
    itself and records nothing; claiming the read is rejected. *)
Definition mem_sigaltstack_badmode : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (4096 + 24)
           then Some (if bv_eqb a 4104 then 3 else 0)
           else None.

Example sigaltstack_errnos_and_their_ledgers :
  check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_badmode
                   (fun _ => None))
    (with_copyins sas_copyin (mkEffect (errno_ret EINVAL) [] [])) sig_model_blocked
  = CheckOk sig_model_blocked []
  /\ check_syscall (mkInput 132 [4096; 0; 0; 0; 0; 0] mem_sigaltstack_badmode
                     (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) sig_model_blocked
     = CheckReject
  /\ check_syscall (mkInput 132 [8192; 0; 0; 0; 0; 0] mem_sigaltstack_badmode
                     (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked
     = CheckOk sig_model_blocked []
  /\ check_syscall (mkInput 132 [8192; 0; 0; 0; 0; 0] mem_sigaltstack_badmode
                     (fun _ => None))
       (with_copyins [(8192, 24%nat)] (mkEffect (errno_ret EFAULT) [] []))
       sig_model_blocked
     = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* =========================================================================
   tkill (130), tgkill (131) and the abort path
   ========================================================================= *)

(** The two models the abort cases run against.  Both DECLARE the abort
    path ([State.in_abort_terminal] [true], which [Run.valid_input_abort]
    is the statement-level form of) and both pin a tid, because
    [Signal.tkill_self] has nothing to compare [pid] against until one
    is pinned — on a real process [set_tid_address] pins it at start-up,
    which is where musl's [__pthread_self()->tid] comes from.

    They differ in ONE thing, the entry mask, and that is what the pair
    is for: musl's [raise] blocks the application signals before it
    sends, so the interesting state is the one where SIGABRT is already
    blocked, and the other is the control. *)
Definition abort_tid : word := Z_to_bv 64 4242.

Definition abort_input (mask : word) : ProcInput :=
  mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile mask demo_hwcap true Sv48.

Definition abort_model_unblocked : Model :=
  with_tid abort_tid
    (init_model [] 0 0 demo_sp demo_limit (abort_input (Z_to_bv 64 0))).

(** SIGABRT blocked: bit 5, so 32 ([Uapi.sigabrt_mask]).  This is the
    state musl's [__block_app_sigs] leaves, restricted to the one bit
    this model reads. *)
Definition abort_model_blocked : Model :=
  with_tid abort_tid
    (init_model [] 0 0 demo_sp demo_limit
       (abort_input (Z_to_bv 64 sigabrt_mask))).

(** The same launch with the declaration OFF, which is what every
    statement that does not declare the abort path quantifies over. *)
Definition abort_model_undeclared : Model :=
  with_tid abort_tid
    (init_model [] 0 0 demo_sp demo_limit
       (mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
          default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48)).

(** POSITIVE, and the case the whole arm exists for: with SIGABRT
    unblocked, [tkill(tid, SIGABRT)] ends the process.  The post-model is
    [State.with_killed], which is what [Run.sstep_killed] reads to emit a
    [State.KillEv] instead of an [State.ExitEv].

    ADMISSION REASON (the first at the top of [Checks/Examples.v]): a
    real run CAN reach this; what it cannot do is run under the
    declaration, which a statement makes and a plain launch does not.
    So the answered shape is pinned here. *)
Example tkill_sigabrt_unblocked_kills :
  check_syscall (mkInput 130 [4242; 6; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [] []) abort_model_unblocked
  = CheckOk (with_killed (Z_to_bv 64 6) abort_model_unblocked) [].
Proof. check_eq. Qed.

(** POSITIVE: with SIGABRT blocked the same call does NOT kill.  It
    returns 0 and leaves the signal pending, which is exactly where
    musl's [raise] leaves it — the death comes at the [rt_sigprocmask]
    that restores the mask, two calls later. *)
Example tkill_sigabrt_blocked_pends :
  check_syscall (mkInput 130 [4242; 6; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [] []) abort_model_blocked
  = CheckOk (with_sigabrt_pending abort_model_blocked) [].
Proof. check_eq. Qed.

(** POSITIVE, the step that actually kills: unblocking a pending SIGABRT.
    [SIG_UNBLOCK] with the SIGABRT bit, from the state the call above
    left, ends the process — and the [rt_sigprocmask] still returns 0,
    because the kernel finishes the syscall before the return path takes
    the signal. *)
Example rt_sigprocmask_unblock_pending_sigabrt_kills :
  check_syscall (mkInput 135 [1; 4096; 0; 8; 0; 0] mem_sigset_sigabrt
                   (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [] []))
    (with_sigabrt_pending abort_model_blocked)
  = CheckOk (with_killed (Z_to_bv 64 6)
               (with_sigmask (Z_to_bv 64 0)
                  (with_sigabrt_pending abort_model_blocked))) [].
Proof. check_eq. Qed.

(** POSITIVE: with nothing pending the same call is the plain mask
    install it always was.  This is the control for the one above — if
    [set_sigmask_deliver] ever killed unconditionally, this would stop
    being a [with_sigmask]. *)
Example rt_sigprocmask_unblock_nothing_pending_lives :
  check_syscall (mkInput 135 [1; 4096; 0; 8; 0; 0] mem_sigset_sigabrt
                   (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [] [])) abort_model_blocked
  = CheckOk (with_sigmask (Z_to_bv 64 0) abort_model_blocked) [].
Proof. check_eq. Qed.

(** POSITIVE: tgkill with the caller's own tgid and tid reaches the same
    place, which is what makes 131 an alias of 130 here rather than a
    second model. *)
Example tgkill_self_sigabrt_kills :
  check_syscall (mkInput 131 [4242; 4242; 6; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [] []) abort_model_unblocked
  = CheckOk (with_killed (Z_to_bv 64 6) abort_model_unblocked) [].
Proof. check_eq. Qed.

(** POSITIVE, an errno the model can give: [pid <= 0] is -EINVAL before
    any task is looked up. *)
Example tkill_nonpositive_pid_einval :
  check_syscall (mkInput 130 [0; 6; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) abort_model_unblocked
  = CheckOk abort_model_unblocked [].
Proof. check_eq. Qed.

(** POSITIVE: tgkill naming the caller's tid under someone else's tgid is
    -ESRCH, because the task is found and its thread-group id does not
    match. *)
Example tgkill_wrong_tgid_esrch :
  check_syscall (mkInput 131 [7; 4242; 6; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect (errno_ret ESRCH) [] []) abort_model_unblocked
  = CheckOk abort_model_unblocked [].
Proof. check_eq. Qed.

(** NEGATIVE, the one that matters most: with the declaration OFF the
    very call that kills above is DECLINED, byte for byte the behaviour
    of a number with no arm in the table at all.  This is the check that
    a task which said nothing about the abort path did not silently
    acquire a terminal outcome.

    ADMISSION REASON (the third at the top of [Checks/Examples.v]): it
    pins where a decline sits relative to a MODEL CONSTANT that no
    observation of one execution reveals — the declaration is a property
    of the statement, not of the launch. *)
Example tkill_off_declined :
  check_syscall (mkInput 130 [4242; 6; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [] []) abort_model_undeclared
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example tgkill_off_declined :
  check_syscall (mkInput 131 [4242; 4242; 6; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [] []) abort_model_undeclared
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** NEGATIVE: a signal that is not SIGABRT is declined even under the
    declaration.  The model has a disposition for SIGABRT and for no
    other signal, so answering SIGUSR1 would be a guess. *)
Example tkill_other_signal_declined :
  check_syscall (mkInput 130 [4242; 10; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [] []) abort_model_unblocked
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** NEGATIVE: a pid that is not the caller's own is declined.  Another
    task on the machine may hold it, and -ESRCH would be a claim about
    every other process. *)
Example tkill_other_pid_declined :
  check_syscall (mkInput 130 [4243; 6; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [] []) abort_model_unblocked
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** NEGATIVE: signal 0, the permission-and-existence probe, is declined
    rather than answered 0.  [valid_signal(0)] passes and delivery is
    skipped, so what the call returns is [security_task_kill]'s verdict —
    an LSM question. *)
Example tkill_signal_zero_declined :
  check_syscall (mkInput 130 [4242; 0; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [] []) abort_model_unblocked
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** NEGATIVE: a lying kernel that claims the abort SUCCEEDED WITH A
    WRITE is refused.  Neither call writes user memory on any branch, so
    a forged write is a [CheckReject] rather than a decline — this is the
    half of the arm no real run can exercise, since no kernel
    writes here. *)
Example tkill_forged_write_rejected :
  check_syscall (mkInput 130 [4242; 6; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect 0 [(Z_to_bv 64 4096, [Z_to_bv 8 0])] []) abort_model_unblocked
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** NEGATIVE: a kernel that answered the kill with something other than 0
    is refused too.  The value is unobservable — the process is gone and
    [Run.sstep_killed] discards the effect — but the acceptor is total on
    the shape, so a different return cannot slip past it. *)
Example tkill_forged_return_rejected :
  check_syscall (mkInput 130 [4242; 6; 0; 0; 0; 0] (fun _ => None)
                   (fun _ => None))
    (mkEffect (errno_ret EPERM) [] []) abort_model_unblocked
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** THE MASK CLAIM THE HEADER'S ENUMERATION OWES, positive and
    negative in one: [tkill] READS the blocked mask — the two answers
    above differ in nothing else — and WRITES none, so the value
    [rt_sigprocmask] hands back through [oset] is still the one it
    installed. *)
Example tkill_reads_the_mask_and_writes_none :
  m_sigmask (with_killed (Z_to_bv 64 6) abort_model_unblocked)
    = m_sigmask abort_model_unblocked
  /\ m_sigmask (with_sigabrt_pending abort_model_blocked)
    = m_sigmask abort_model_blocked
  /\ check_syscall (mkInput 130 [4242; 6; 0; 0; 0; 0] (fun _ => None)
                     (fun _ => None))
       (mkEffect 0 [] []) abort_model_unblocked
     <> check_syscall (mkInput 130 [4242; 6; 0; 0; 0; 0] (fun _ => None)
                        (fun _ => None))
          (mkEffect 0 [] []) abort_model_blocked.
Proof.
  split; [reflexivity | split; [reflexivity |]].
  vm_compute. discriminate.
Qed.

(* =========================================================================
   The one-sided frame, refuted
   ========================================================================= *)

(** WHY [Run.decl_off_frame] CARRIES THE PENDING BIT, as a refutation
    rather than as a sentence.

    The tempting reading of the abort declaration is that it is the
    guard: nothing can be killed while [State.m_abort_terminal] is
    clear, so a frame quantified over that field alone should hold.  It
    does not.  [Kernel.Signal.sigmask_deliver_model] — the delivery
    inside [rt_sigprocmask], not the send — branches on
    [State.m_sigabrt_pending] and never looks at the declaration, because
    a signal ALREADY PENDING has to be taken by the mask install that
    uncovers it whatever the task declared.  [State.with_sigabrt_pending]
    is total, so a model with the declaration clear and the bit set is
    directly constructible, and this is one.

    That model is not REACHABLE with the declaration clear — the only
    writer of the pending bit is [Kernel.Signal.send_sigabrt], which is
    behind the declaration — which is exactly why the frame has to say
    "both bits clear" rather than "the declaration is clear".  A
    one-sided [Run.decl_off_frame_one_sided] is false, so every theorem
    stated with it as a hypothesis would be vacuous, and this is what
    stops that shape coming back.

    ADMISSION REASON (the third at the top of [Checks/Examples.v]): no
    real run can reach the state this refutation is about, since
    a launch starts with the bit clear and only a declared
    abort path sets it.  The claim is about what the SPEC admits at a
    state, which no observation of one execution reaches. *)
Definition one_sided_input : ProcInput :=
  mkProcInput [] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 sigabrt_mask) demo_hwcap false Sv48.

(** The declaration is clear and SIGABRT is both BLOCKED and PENDING: the
    state the one-sided frame claims cannot be killed. *)
Definition one_sided_model : Model :=
  with_sigabrt_pending
    (with_tid abort_tid (init_model [] 0 0 demo_sp demo_limit one_sided_input)).

Example one_sided_model_is_declaration_off :
  m_abort_terminal one_sided_model = false
  /\ m_sigabrt_pending one_sided_model = true.
Proof. split; reflexivity. Qed.

(** An ordinary [rt_sigprocmask(SIG_UNBLOCK, {SIGABRT}, NULL, 8)] — a call
    with no [tkill] anywhere near it — kills that model. *)
Example one_sided_unblock_kills :
  check_syscall (mkInput 135 [1; 4096; 0; 8; 0; 0] mem_sigset_sigabrt
                   (fun _ => None))
    (with_copyins sig_copyin (mkEffect 0 [] [])) one_sided_model
  = CheckOk (with_killed (Z_to_bv 64 6)
               (with_sigmask (Z_to_bv 64 0) one_sided_model)) [].
Proof. check_eq. Qed.

Theorem decl_off_frame_one_sided_refuted : ~ Run.decl_off_frame_one_sided.
Proof.
  intros H.
  destruct (H (mkInput 135 [1; 4096; 0; 8; 0; 0] mem_sigset_sigabrt
                 (fun _ => None))
              one_sided_model
              (with_copyins sig_copyin (mkEffect 0 [] []))
              (with_killed (Z_to_bv 64 6)
                 (with_sigmask (Z_to_bv 64 0) one_sided_model)) []
              (check_syscall_sound_ok _ _ _ _ _ one_sided_unblock_kills)
              eq_refl)
    as (_ & Hk & _).
  vm_compute in Hk. discriminate.
Qed.

(** ...and the invariant form is not vacuous in the other direction
    either: its hypotheses are inhabited.  Same call, same shape, from a
    model with BOTH bits clear — which the frame then obliges to stay
    that way, and it does. *)
Example decl_off_frame_hypotheses_inhabited :
  m_abort_terminal abort_model_undeclared = false
  /\ m_sigabrt_pending abort_model_undeclared = false
  /\ check_syscall (mkInput 135 [1; 4096; 0; 8; 0; 0] mem_sigset_sigabrt
                     (fun _ => None))
       (with_copyins sig_copyin (mkEffect 0 [] [])) abort_model_undeclared
     = CheckOk (with_sigmask (Z_to_bv 64 0) abort_model_undeclared) [].
Proof. split; [reflexivity | split; [reflexivity | check_eq]]. Qed.

(* =========================================================================
   THE THREE USER READS THAT WERE ARGUED OUT OF A RANGE TEST

   [Kernel.Signal.sigset_at] (rt_sigprocmask's [nset]),
   [Kernel.Signal.sigaltstack_at] (sigaltstack's [uss]) and
   [Kernel.Signal.sigaction_flags] with [sigaction_handler]
   (rt_sigaction's [act]) read user memory with the bare walk, on the
   argument that a wholly readable range must sit below
   [State.TASK_SIZE].  That argument was false -- the IMAGE_WF
   hypothesis bounds an image below 2^64 and not below 2^47, and
   [check_syscall] takes an arbitrary input -- and the walk wraps at
   2^64 besides, so a pointer in the last bytes of the address space
   read the bytes below the wrap and then the bytes from 0 on and the
   call was answered on them.  Each now goes through
   [State.copy_bytes_map], [State.access_okb] and then the walk.

   EACH GROUP IS A TRIPLE, in the shape [Checks.Cases.Net.Socket] and
   [Checks.Cases.Fs.Select] take: the wrapping call refused, a
   neighbouring ordinary call at the top of what [State.access_okb]
   accepts still answered, and the control that the bare walk really
   would have passed -- without it the refusal would also hold if the
   memory quietly stopped mapping the range.

   THE MEMORIES MAP EXACTLY THEIR OWN RANGE and nothing else, for that
   reason.
   ========================================================================= *)

(* ---- rt_sigprocmask (135): the new set ---------------------------------- *)

(** Four bytes below the top and four from 0: the 8-byte [sigset_t]
    covers both halves.  The byte at [nset + 1] is 4, so the set is
    [sigmask(SIGSEGV)] = 1 << 10, the set
    [rt_sigprocmask_block_sigsegv_accepted] installs.  Before the guard
    this call installed it and returned 0.
    [SYSCALL_DEFINE4(rt_sigprocmask)] (kernel/signal.c) copies with
    [copy_from_user] before [sigprocmask] runs, and its [access_ok]
    refuses the range, so the answer is -EFAULT with nothing installed
    and nothing recorded. *)
Definition sig_wrap_nset : word := Z_to_bv 64 (2 ^ 64 - 4).

Definition sig_wrap_nset_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 4)%Z || (2 ^ 64 - 4 <=? bv_unsigned a)%Z)%bool
           then Some (if bv_eqb a (Z_to_bv 64 (2 ^ 64 - 3)) then Z_to_bv 8 4
                      else Z_to_bv 8 0)
           else None.

Example sigprocmask_wrap_would_pass_the_bare_walk :
  read_bytes_map sig_wrap_nset_mem sig_wrap_nset (Z_to_bv 64 8) <> None.
Proof. vm_compute. discriminate. Qed.

Example sigprocmask_wrap_set_is_not_copied :
  sigset_at sig_wrap_nset_mem sig_wrap_nset = None.
Proof. vm_compute. reflexivity. Qed.

Example sigprocmask_wrapping_set_is_efault :
  check_syscall (mkInput 135 [0; sig_wrap_nset; 0; 8; 0; 0] sig_wrap_nset_mem
                   (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) sig_model
  = CheckOk sig_model []
  /\ check_syscall (mkInput 135 [0; sig_wrap_nset; 0; 8; 0; 0] sig_wrap_nset_mem
                     (fun _ => None))
       (with_copyins [(sig_wrap_nset, 8%nat)] (mkEffect 0 [] [])) sig_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** THE NEIGHBOUR: the last eight bytes [State.access_okb] accepts,
    readable end to end, holding the same set.  The set is still
    copied and installed -- [with_sigmask 1024], with the eight bytes on
    the ledger -- and -EFAULT is refused there. *)
Definition sig_top_nset : word := Z_to_bv 64 (TASK_SIZE - 8).

Definition sig_top_nset_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 8 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (if bv_eqb a (Z_to_bv 64 (TASK_SIZE - 7)) then Z_to_bv 8 4
                      else Z_to_bv 8 0)
           else None.

Example sigprocmask_set_at_the_top_still_installs :
  check_syscall (mkInput 135 [0; sig_top_nset; 0; 8; 0; 0] sig_top_nset_mem
                   (fun _ => None))
    (with_copyins [(sig_top_nset, 8%nat)] (mkEffect 0 [] [])) sig_model
  = CheckOk (with_sigmask (Z_to_bv 64 1024) sig_model) []
  /\ check_syscall (mkInput 135 [0; sig_top_nset; 0; 8; 0; 0] sig_top_nset_mem
                     (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) sig_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(* ---- sigaltstack (132): the [stack_t] ----------------------------------- *)

(** Eight bytes below the top and sixteen from 0: [ss_sp] sits at the
    top, [ss_flags] and [ss_size] wrap to address 0.  The bytes are
    [mem_sigaltstack_ok]'s -- [ss_sp] = 0x2000, [ss_flags] = 0,
    [ss_size] = 0x4000 -- so before the guard this call installed a
    stack, set the bit and returned 0.  [SYSCALL_DEFINE2(sigaltstack)]
    (kernel/signal.c) copies with [copy_from_user] before
    [do_sigaltstack] runs, and its [access_ok] refuses the range. *)
Definition sig_wrap_uss : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition sig_wrap_uss_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 16)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (if bv_eqb a (Z_to_bv 64 (2 ^ 64 - 7)) then Z_to_bv 8 32
                      else if bv_eqb a (Z_to_bv 64 9) then Z_to_bv 8 64
                      else Z_to_bv 8 0)
           else None.

Example sigaltstack_wrap_would_pass_the_bare_walk :
  read_bytes_map sig_wrap_uss_mem sig_wrap_uss (Z_to_bv 64 24) <> None.
Proof. vm_compute. discriminate. Qed.

Example sigaltstack_wrap_struct_is_not_copied :
  sigaltstack_at sig_wrap_uss_mem sig_wrap_uss = None.
Proof. vm_compute. reflexivity. Qed.

Example sigaltstack_wrapping_struct_is_efault :
  check_syscall (mkInput 132 [sig_wrap_uss; 0; 0; 0; 0; 0] sig_wrap_uss_mem
                   (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked
  = CheckOk sig_model_blocked []
  /\ check_syscall (mkInput 132 [sig_wrap_uss; 0; 0; 0; 0; 0] sig_wrap_uss_mem
                     (fun _ => None))
       (with_copyins [(sig_wrap_uss, 24%nat)] (mkEffect 0 [] []))
       sig_model_blocked
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** THE NEIGHBOUR: the last twenty-four bytes [State.access_okb]
    accepts, readable end to end, holding the same [stack_t].  The
    install still succeeds and sets the bit, with the twenty-four bytes
    on the ledger, and -EFAULT is refused there. *)
Definition sig_top_uss : word := Z_to_bv 64 (TASK_SIZE - 24).

Definition sig_top_uss_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 24 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (if bv_eqb a (Z_to_bv 64 (TASK_SIZE - 23)) then Z_to_bv 8 32
                      else if bv_eqb a (Z_to_bv 64 (TASK_SIZE - 7)) then Z_to_bv 8 64
                      else Z_to_bv 8 0)
           else None.

Example sigaltstack_struct_at_the_top_still_installs :
  check_syscall (mkInput 132 [sig_top_uss; 0; 0; 0; 0; 0] sig_top_uss_mem
                   (fun _ => None))
    (with_copyins [(sig_top_uss, 24%nat)] (mkEffect 0 [] [])) sig_model_blocked
  = CheckOk (with_sigaltstack_installed sig_model_blocked) []
  /\ check_syscall (mkInput 132 [sig_top_uss; 0; 0; 0; 0; 0] sig_top_uss_mem
                     (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) sig_model_blocked
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(* ---- rt_sigaction (134): the [struct sigaction] ------------------------- *)

(** Eight bytes below the top and sixteen from 0, all zero: [sa_handler]
    is SIG_DFL at the top and [sa_flags] and [sa_mask] wrap to address
    0.  Before the guard SIGINT's install was answered 0 with the 24
    bytes on the ledger.  [SYSCALL_DEFINE4(rt_sigaction)]
    (kernel/signal.c) copies with [copy_from_user] before
    [do_sigaction] runs, and its [access_ok] refuses the range.  SIGABRT
    with the same struct -- the install [sigabrt_dfl_install] answers,
    which reads the handler word through [sigaction_handler] -- is
    refused the same way.  The control states both the walk the guard
    now sits in front of and the [readable_bytes] test the old
    definition used. *)
Definition sig_wrap_act : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition sig_wrap_act_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 16)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example sigaction_wrap_would_pass_the_bare_walk :
  read_bytes_map sig_wrap_act_mem sig_wrap_act (Z_to_bv 64 24) <> None
  /\ Nat.eqb (length (readable_bytes sig_wrap_act_mem sig_wrap_act
                        (Z_to_bv 64 24))) 24
     = true.
Proof. split; [vm_compute; discriminate | vm_compute; reflexivity]. Qed.

Example sigaction_wrap_struct_is_not_copied :
  sigaction_flags sig_wrap_act_mem sig_wrap_act = None
  /\ sigaction_handler sig_wrap_act_mem sig_wrap_act = None.
Proof. split; vm_compute; reflexivity. Qed.

Example sigaction_wrapping_struct_is_efault :
  check_syscall (mkInput 134 [2; sig_wrap_act; 0; 8; 0; 0] sig_wrap_act_mem
                   (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) sig_model
  = CheckOk sig_model []
  /\ check_syscall (mkInput 134 [2; sig_wrap_act; 0; 8; 0; 0] sig_wrap_act_mem
                     (fun _ => None))
       (with_copyins [(sig_wrap_act, 24%nat)] (mkEffect 0 [] [])) sig_model
     = CheckReject
  /\ check_syscall (mkInput 134 [6; sig_wrap_act; 0; 8; 0; 0] sig_wrap_act_mem
                     (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) sig_model
     = CheckOk sig_model [].
Proof. split; [check_eq | split; [vm_compute; reflexivity | check_eq]]. Qed.

(** THE NEIGHBOUR: the last twenty-four bytes [State.access_okb]
    accepts, readable end to end, all zero.  SIGINT's install is still
    answered 0 with the twenty-four bytes on the ledger, -EFAULT is
    refused there, and SIGABRT's SIG_DFL install -- the one that goes on
    to [sigaction_handler] -- is still answered 0 too. *)
Definition sig_top_act : word := Z_to_bv 64 (TASK_SIZE - 24).

Definition sig_top_act_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 24 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example sigaction_struct_at_the_top_still_answers :
  check_syscall (mkInput 134 [2; sig_top_act; 0; 8; 0; 0] sig_top_act_mem
                   (fun _ => None))
    (with_copyins [(sig_top_act, 24%nat)] (mkEffect 0 [] [])) sig_model
  = CheckOk sig_model []
  /\ check_syscall (mkInput 134 [2; sig_top_act; 0; 8; 0; 0] sig_top_act_mem
                     (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) sig_model
     = CheckReject
  /\ check_syscall (mkInput 134 [6; sig_top_act; 0; 8; 0; 0] sig_top_act_mem
                     (fun _ => None))
       (with_copyins [(sig_top_act, 24%nat)] (mkEffect 0 [] [])) sig_model
     = CheckOk sig_model [].
Proof. split; [check_eq | split; [vm_compute; reflexivity | check_eq]]. Qed.
