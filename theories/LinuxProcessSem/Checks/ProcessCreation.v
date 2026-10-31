(** * LinuxProcessSem.Checks.ProcessCreation — process creation, pinned

    Not part of the trusted specification: this file is QA on the
    definitions, in the sense of [Checks.Examples]'s header.  It earns
    its place under that file's FIRST reason — every statement here is
    UNIVERSALLY QUANTIFIED over models, arguments and memories, which no
    finite set of traces can establish.  One run can show
    that ONE flag word was declined, or that ONE forged zero was
    refused; only a [forall] can say that every one is.

    ** What this pins, and why it is not decoration

    Three arguments in this development are load-bearing and rest on
    something stated here.  Two rest on a syscall NUMBER being outside
    the modeled surface; the middle one rests on a FLAG WORD:

    - [State.access_okb] is claimed EXACT rather than an
      under-approximation — a claim scoped to a build with [CONFIG_MMU]
      and without [CONFIG_ALTERNATE_USER_ADDRESS_SPACE], for reasons
      this file does not pin and the note below records.  What it does
      pin: riscv64's [access_ok] wraps its address in [untagged_addr],
      which is the identity exactly when [PMLEN = 0].  [PMLEN] is zeroed
      on every [execve] and is written
      afterwards only by [set_tagged_addr_ctrl]
      (arch/riscv/kernel/process.c), which has TWO callers:
      [prctl(PR_SET_TAGGED_ADDR_CTRL, ...)] (kernel/sys.c, [SYSCALL_DEFINE5(prctl)])
      and [PTRACE_SETREGSET] with [NT_RISCV_TAGGED_ADDR_CTRL]
      (arch/riscv/kernel/ptrace.c, [tagged_addr_ctrl_set]).  Declining
      option 55 of 167, and all of 117, rules out both routes FROM
      INSIDE the model: the traced process cannot enable masking on
      itself.  An external tracer is a separate matter, below.  The
      prctl half is one OPTION, not the whole NUMBER; why
      the weaker-looking statement carries the same weight is at
      [prctl_option_unmodeled] below.
    - [Fork.set_tid_address_spec] accepts and ignores its [tidptr], and
      NOT for any reason on this list.  [set_tid_address] records the
      pointer in the CALLER's [current->clear_child_tid], while
      [copy_process] sets a different task's [p->clear_child_tid] under
      [CLONE_CHILD_CLEARTID]; the two share only a field name.  The
      caller's write fires from [mm_release] when the CALLER exits or
      execs, gated on [mm_users > 1], so what rules it out is that this
      model admits no second holder of an mm — a closed-world statement
      about the environment, not a flag test.  See that spec's header;
      do not re-derive it from the bit below.
    - [Fork.clone_spec]'s header argues that the SIGCHLD the admitted
      flag word requests, and which the child's exit sends to this
      process, comes to nothing.  The argument has two halves — a
      [SIG_DFL] SIGCHLD is discarded, a blocked one is queued but sets
      no [TIF_SIGPENDING].  NEITHER half is a statement about a
      declined number: 134 and 135 are both modeled.  What
      carries the whole argument is [Signal.sigaction_accepted], which
      excludes SIGCHLD, so an install for it fails closed at the SIGNAL
      rather than at the number.  A changeable mask does not reopen
      anything: unblocking a queued SIGCHLD hands it to [get_signal],
      which finds [SIG_DFL] and [sig_kernel_ignore] and discards it, so
      the blocked case funnels into the unblocked one rather than into
      a third.  The exclusion is pinned in
      [Checks.Cases.Kernel.Signal.rt_sigaction_sigchld_unmodeled].

    Not everything in the neighbourhood is.  [State.access_okb]'s note
    ALSO relies on there being no second process to be the tracer, and
    nothing about 220 gives it that — not its parent-side model, and
    not a decline either.  A tracer is an
    independently started process, and a child this model does not step
    could equally attach to its parent and [PTRACE_POKEDATA] it with
    [CLONE_VM] clear.  That half is a closed-world assumption about the
    ENVIRONMENT (Yama's [ptrace_scope], uid separation) — undischarged.
    What this
    file pins for it is the IN-MODEL half: [prctl]'s tagging option and
    all of 117 are declined, so the traced process cannot enable masking
    on itself.

    And the tagging argument is not the only precondition that note has.
    [__access_ok] returns true for every range, ahead of the comparison
    [access_okb] transcribes, under [CONFIG_ALTERNATE_USER_ADDRESS_SPACE]
    or with [CONFIG_MMU] off; on such a build [access_okb] declines
    ranges the kernel accepts and is an under-approximation whatever
    [PMLEN] is.  riscv cannot select the first (arch/Kconfig, [config
    ALTERNATE_USER_ADDRESS_SPACE]: no prompt, and selected only by
    parisc, s390, [SPARC64] and m68k, v6.9 through v6.17), so that half
    is closed by the architecture.  The second is a real choice —
    arch/riscv/Kconfig's [config MMU] is a prompted bool with no [depends
    on], and arch/riscv/configs/nommu_virt_defconfig ships an RV64 build
    with it off — so the claim holds by BUILD CONFIGURATION, which no
    decline proved here touches and no syscall number can rule out.

    Prose alone does not protect these arguments: adding an arm for
    [prctl] would leave every one of those comments false with a
    green build.  The corollaries below are proved DIRECTLY against
    [syscall_spec] rather than through [Specs.modeled_sysnos] and its
    companion file, so each one is a tripwire: give any of these numbers
    an arm and its proof stops closing.

    ** What it does NOT claim

    Nothing here says these syscalls SHOULD stay unmodeled, and nothing
    here is a model of them.  Declining is what the dispatcher
    does; this file states it, in the one place a future change would have
    to look at. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase State Monad Fs Specs RiscvSemantics MemImageType Run StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Where the general list-to-dispatcher link belongs, and what it says
   ========================================================================= *)

(** [Checks.DispatchSurface] is a companion QA file.  Neither file
    [Require]s the other — this one sits over [Checks.ExecutableSpecs]
    and that one over [Checks.Progress] — and this one names it rather
    than importing it because the tripwires below would be WEAKER if
    they went through it, not because it is missing.

    [Specs.modeled_sysnos] is documentation: the trace semantics never
    consults it, so on its own it is a comment that happens to be typed.
    The general link to [Specs.syscall_spec] is what that companion file
    proves, in BOTH directions.  Neither direction is used below — the
    tripwires are deliberately independent of both — but which statements
    are and are not true about that list is what the arguments above rest
    on, so it is worth being exact about them here.

    - FAIL-CLOSED: outside the list the dispatcher admits nothing but
      [Unmodeled] ([syscall_spec_unmodeled_outside] there), with the
      introduction form — outside the list [Unmodeled] IS an admissible
      outcome — derived from it in two steps via [Progress.receptive]
      ([syscall_spec_declines_outside]).  The introduction form alone
      would be strictly weaker: [Sys] is a relation, so "admits
      [Unmodeled]" does not by itself rule out a number that both
      declines and answers.  This is the direction the coverage argument
      needs.

    - THE CONVERSE: every number the list DOES name is answered on SOME
      input ([modeled_sysnos_dispatched] there).  That is a theorem, and
      together with the first direction it makes [modeled_sysnos] exactly
      the dispatched set ([modeled_sysnos_exact]).

    What is NOT true is the universally quantified reading — "a number
    the list names never yields [Unmodeled]".  That is not the converse
    of anything above: a listed number still declines the argument
    shapes its own spec rejects, which is the whole point of
    [Monad.unmodeled]. *)

(* =========================================================================
   The tripwires — one per number, proved against the dispatcher itself
   ========================================================================= *)

(** Deliberately NOT proved via the companion file's
    [syscall_spec_declines_outside].  Going through
    the list would make each of these a statement about
    [modeled_sysnos], and a change that added an arm without touching
    the list would leave them all provable.  Proved against
    [syscall_spec], adding an arm for the number breaks the proof, which
    is the point. *)
(* The number is not in [Sys.SyscallTable.spec_table], so the lookup is [None]
   and the dispatcher declines.  This is one computation over the table,
   and it breaks, as it should, the moment someone gives the number an arm. *)
Local Ltac declined_at Hno :=
  unfold syscall_spec; apply dispatch_unmodeled; rewrite Hno; reflexivity.

(** [clone] (220) and [clone3] (435) — MODELED, parent-side, and stated
    here in the negative.  The model does not cover all of clone: its
    spec answers exactly one flag word, [SIGCHLD], and the
    three statements below say what it still declines.

    [Fork.clone_spec]'s header has the reasoning.  In short: the model
    creates no second process, so a child's effect on the PARENT is the
    only thing that can make ignoring it unsound.  The flag bits that
    carry such an effect are outside the admitted word — but flag bits
    are not the only carrier, and that header names five channels no
    flag test can close.  What a lemma buys over a comment is that
    widening the flag test breaks the build. *)
Definition CLONE_VM             : Z := 0x00000100.
Definition CLONE_FS             : Z := 0x00000200.
Definition CLONE_FILES          : Z := 0x00000400.
Definition CLONE_SIGHAND        : Z := 0x00000800.
Definition CLONE_PIDFD          : Z := 0x00001000.
Definition CLONE_VFORK          : Z := 0x00004000.
Definition CLONE_THREAD         : Z := 0x00010000.
Definition CLONE_SYSVSEM        : Z := 0x00040000.
Definition CLONE_SETTLS         : Z := 0x00080000.
Definition CLONE_PARENT_SETTID  : Z := 0x00100000.
Definition CLONE_CHILD_CLEARTID : Z := 0x00200000.
Definition CLONE_CHILD_SETTID   : Z := 0x01000000.
Definition CLONE_IO             : Z := 0x80000000.

(** The bits [Fork.clone_fork_flags_b] has to keep out.  Most are bits
    whose absence something elsewhere in this development STATES;
    [CLONE_SYSVSEM] and [CLONE_IO] are here with nothing in this
    development resting on them, so the list is not merely the bits some
    argument happens to cite.  It is not the complete set of bits a
    child could share either — [CLONE_PARENT], which redirects the exit
    signal to the GRANDparent, is absent, and so is the ptrace pair —
    and it does not need to be: the gate is the [clone_fork_flags_b]
    allowlist and this lemma is a sufficient condition over it, not the
    thing doing the refusing.  Five kinds:

    - the child reaches back into the parent — a shared address space
      ([CLONE_VM], and [CLONE_VFORK] which suspends the parent inside
      one), a shared descriptor table ([CLONE_FILES]), a shared
      [fs_struct] whose [chdir] moves the parent's [AT_FDCWD]
      ([CLONE_FS]), a shared System V semaphore undo list
      ([CLONE_SYSVSEM]) and a shared [io_context] ([CLONE_IO]) — the two
      this development states nothing about, since it models neither
      semaphores nor io priorities;
    - the call itself touches the parent — a new descriptor installed in
      the parent's own table and an int written through its
      [parent_tidptr] ([CLONE_PIDFD]), and the child tid written through
      the same pointer ([CLONE_PARENT_SETTID]);
    - a THREAD GROUP with more than one member ([CLONE_THREAD], and
      [CLONE_SIGHAND] which it requires).  Not because the CALLER would
      stop leading it — it would not — but because
      [Sys.getpid_spec = Fork.set_tid_address_spec] needs every task
      the model describes to be its own group leader, and a task created
      with [CLONE_THREAD] whose leader later exits is not.  See
      [Fork.set_tid_address_spec] and [State.m_tid]'s note;
    - a write fires when a CHILD exits ([CLONE_CHILD_CLEARTID]).  This
      is a reason to decline the BIT; it is NOT what
      [Fork.set_tid_address_spec] rests on, which is a different writer
      into a same-named field — see the note above;
    - the call would use an argument this spec does not fetch.
      [CLONE_CHILD_SETTID] gates the read of [child_tidptr]; on riscv64
      [CLONE_SETTLS] copies nothing — [copy_thread] assigns
      [childregs->tp = args->tls] — but it is the bit that makes [tls]
      mean anything.  TWO comments say in so many words that neither
      argument is read: [Fork.clone_spec]'s header and the dispatcher's own
      note at the [clone] arm.

    Every citation of the lemma below names a bit in THIS list, which is
    the point of listing more than the address-space pair: widening
    [Fork.clone_fork_flags_b] to admit any of them stops the proof
    closing rather than silently falsifying the comment that cites it. *)
Definition clone_sharing_bits : Z :=
  fold_left Z.lor
    [CLONE_VM; CLONE_FS; CLONE_FILES; CLONE_SIGHAND; CLONE_PIDFD;
     CLONE_VFORK; CLONE_THREAD; CLONE_SYSVSEM; CLONE_SETTLS;
     CLONE_PARENT_SETTID; CLONE_CHILD_CLEARTID; CLONE_CHILD_SETTID;
     CLONE_IO] 0%Z.

Lemma clone_sharing_flags_unmodeled : forall flags i m,
  (Z.land (bv_unsigned flags) clone_sharing_bits <> 0)%Z ->
  clone_spec flags i m Unmodeled.
Proof.
  intros flags i m Hbit. unfold clone_spec.
  destruct (clone_fork_flags_b flags) eqn:Hf; [|apply unmodeled_intro].
  exfalso. unfold clone_fork_flags_b in Hf.
  apply bv_eqb_eq in Hf. subst flags. apply Hbit. vm_compute. reflexivity.
Qed.

(** The same statement for [clone3], where the flag word is a field of a
    struct in user memory rather than a register.  The premise is the
    COPY, [State.copy_bytes_map], and not the bare walk: a range
    [access_ok] refuses is -EFAULT before any field is judged
    ([Fork.clone3_spec]), so the flags never reach a decision there. *)
Lemma clone3_sharing_flags_unmodeled : forall uargs size i m bs,
  copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE = Some bs ->
  (Z.land (bv_unsigned (clone_args_field bs 0)) clone_sharing_bits <> 0)%Z ->
  clone3_spec uargs size i m Unmodeled.
Proof.
  intros uargs size i m bs Hread Hbit. unfold clone3_spec.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)));
    cbv iota; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  rewrite Hread. cbv iota.
  destruct (clone3_fork_args_b bs) eqn:Ha; [|apply unmodeled_intro].
  exfalso. unfold clone3_fork_args_b in Ha.
  repeat (apply andb_true_iff in Ha as [Ha ?]).
  unfold w_is0 in Ha. apply bv_eqb_eq in Ha. apply Hbit.
  rewrite Ha. vm_compute. reflexivity.
Qed.

(** The FILE OFFSET is the one thing a plain fork still shares:
    [copy_files] duplicates the descriptor table while both tables point
    at the same [struct file], and [State.FdEntry] inlines the offset
    into the descriptor, so the sharing is not expressible.  The spec
    declines rather than pretending otherwise, and this says so. *)
Lemma clone_open_file_unmodeled : forall flags i m,
  clone_no_shared_file_b (m_fds m) = false -> clone_spec flags i m Unmodeled.
Proof.
  intros flags i m Hfd. unfold clone_spec.
  destruct (clone_fork_flags_b flags); [|apply unmodeled_intro].
  unfold clone_resolve.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  rewrite Hfd. cbv iota. apply unmodeled_intro.
Qed.

(** No admitted errno encodes 0. *)
Lemma clone_errno_ret_nonzero : forall e,
  In e clone_errnos -> errno_ret e <> Z_to_bv 64 0.
Proof.
  intros e Hin Hc. apply (f_equal bv_unsigned) in Hc.
  unfold clone_errnos in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; vm_compute in Hc; discriminate.
Qed.

(** ZERO IS NEVER AN ANSWER.  Zero is what the CHILD sees returned from
    [clone]; following it would run the child's branch of the caller's
    own code inside a model that has no child.  [Fork.clone_spec]'s
    header states that as a design decision; this states it as a
    theorem, over every flag word, every model and every resolution. *)
Lemma clone_never_returns_zero : forall flags i m eff m' evs,
  clone_spec flags i m (Ok eff m' evs) -> eff_ret eff <> Z_to_bv 64 0.
Proof.
  intros flags i m eff m' evs H.
  unfold clone_spec in H.
  destruct (clone_fork_flags_b flags); [|unfold unmodeled in H; discriminate].
  unfold clone_resolve in H. sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg; hall Hg; inv_ok.
  all: cbn [eff_ret].
  all: try (match goal with
            | Hin : In ?e clone_errnos |- _ =>
                exact (clone_errno_ret_nonzero e Hin)
            end).
  all: match goal with
       | Hv : clone_pid_ok_b ?mm ?r = true |- _ =>
           unfold clone_pid_ok_b in Hv;
           apply andb_true_iff in Hv as [Hr _];
           apply andb_true_iff in Hr as [Hlo _];
           apply Z.ltb_lt in Hlo;
           intro Hc; subst r;
           change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hlo; lia
       end.
Qed.

Lemma clone3_never_returns_zero : forall uargs size i m eff m' evs,
  clone3_spec uargs size i m (Ok eff m' evs) -> eff_ret eff <> Z_to_bv 64 0.
Proof.
  intros uargs size i m eff m' evs H.
  unfold clone3_spec in H.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)));
    cbv iota in H; [unfold unmodeled in H; discriminate|].
  sys_unfold. cbv iota in H. inv_ok.
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE)
    as [bs|] eqn:Hbs; hall Hbs; inv_ok.
  2: { (* a refused range answers -EFAULT, which is not 0 either *)
       destruct (negb (access_okb uargs CLONE_ARGS_SIZE)) eqn:Hs; hall Hs; inv_ok.
       cbn [eff_ret]. intro Hc. apply (f_equal bv_unsigned) in Hc.
       vm_compute in Hc. discriminate. }
  destruct (clone3_fork_args_b bs) eqn:Ha; hall Ha; inv_ok.
  match goal with
  | Hr : clone3_resolve _ _ _ (Ok _ _ _) |- _ =>
      apply clone3_resolve_inv in Hr as (e0 & H0 & Hret); rewrite Hret
  end.
  eapply (clone_never_returns_zero (Z_to_bv 64 SIGCHLD) i m).
  unfold clone_spec, clone_fork_flags_b. rewrite bv_eqb_refl.
  unfold clone_resolve. sys_unfold. cbv iota. eassumption.
Qed.

(** THE ARM IS THE ONE IT CLAIMS TO BE.  Every lemma above pins what
    [clone] and [clone3] REFUSE, and a refusal lemma characterises its
    number completely only because [Unmodeled] is the whole answer.  The
    positive direction needs saying too: that 220 and 435 reach
    [Fork.clone_spec] and [Fork.clone3_spec] and not some other total
    spec that happens to refuse the same inputs.  [Sys.Dispatch.dispatch_arm]
    already states that biconditional for any table and arm, so this
    costs a lookup and a [reflexivity]. *)
Lemma clone_is_clone_spec : forall i m o,
  bv_unsigned (in_sysno i) = 220%Z ->
  (syscall_spec i m o <-> clone_spec (in_arg i 0) i m o).
Proof.
  intros i m o H. unfold syscall_spec.
  apply (dispatch_arm spec_table i m o
           (mkSpecArm 220%Z (fun i => clone_spec (in_arg i 0) i))).
  rewrite H. reflexivity.
Qed.

Lemma clone3_is_clone3_spec : forall i m o,
  bv_unsigned (in_sysno i) = 435%Z ->
  (syscall_spec i m o <-> clone3_spec (in_arg i 0) (in_arg i 1) i m o).
Proof.
  intros i m o H. unfold syscall_spec.
  apply (dispatch_arm spec_table i m o
           (mkSpecArm 435%Z (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i))).
  rewrite H. reflexivity.
Qed.

(** The separation [clone_resolve_declines_or_sets_children] below states,
    for ANY errno list [es] that contains [Fork.clone_errnos] and stays
    inside the errno band: an answer in [es] leaves the model untouched,
    and any answer outside it records the child.  Both obligations survive
    the widening — a pid is outside every such list, by
    [errno_ret_in_below] — so an entry point that answers more errnos than
    [clone_resolve] does names its own list here, and the decline it adds
    is stated, not excluded.  The lemma below the note is the instance at
    [Fork.clone_errnos]. *)
Lemma clone_resolve_declines_or_sets_children_in : forall es i m eff m' evs,
  incl clone_errnos es -> errnos_ok es = true ->
  clone_resolve i m (Ok eff m' evs) ->
  (errno_ret_in es (eff_ret eff) = true -> m' = m) /\
  (errno_ret_in es (eff_ret eff) = false -> m_has_children m' = true).
Proof.
  intros es i m eff m' evs Hincl Hok H.
  unfold clone_resolve in H. sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg; hall Hg; inv_ok.
  (* one goal per alternative: an errno from [clone_errnos], and a pid *)
  - match goal with
    | Hin : In ?e clone_errnos |- _ =>
        assert (Hyes := errno_ret_in_intro es e (Hincl e Hin))
    end.
    cbn [eff_ret]. split; intros He; [reflexivity | congruence].
  - match goal with
    | Hv : clone_pid_ok_b ?mm ?r = true |- _ =>
        assert (Hno : errno_ret_in es r = false);
        [ unfold clone_pid_ok_b in Hv;
          apply andb_true_iff in Hv as [Hrange _];
          apply andb_true_iff in Hrange as [_ Hhi]; apply Z.ltb_lt in Hhi;
          apply errno_ret_in_below; [exact Hok|];
          change PID_MAX_ENVELOPE with 4194304%Z in Hhi;
          unfold two_pow_64; lia
        | ]
    end.
    cbn [eff_ret]. split; intros He; [congruence | reflexivity].
Qed.

(** ** EITHER IT DECLINES, OR IT RECORDS THE CHILD

    [Kernel.Exit.wait4_spec]'s -ECHILD is correct only for a caller with
    nothing to reap, and what it reads to decide that is
    [State.m_has_children].  The two specs therefore compose on a claim
    no single model can carry: that every resolution of 220 and 435
    which returns a PID leaves that field set.  [clone_checker_admits_a_pid]
    below pins one model and one pid; this is the [forall], and it is the
    statement [Kernel.Fork.clone_resolve]'s [modify with_children] exists
    to make true.

    THE TWO ARMS ARE SEPARATED, NOT MERELY COVERED.  The statement is a
    pair of implications keyed on the observed return rather than a
    disjunction, and that is what it buys over "declines or sets it": an
    inclusive disjunction is satisfied by an implementation that applies
    [State.with_children] on the ERRNO arm as well, which is a real
    mistake — a [clone] that answered -EAGAIN made no child, and a
    [wait4] after it must still answer -ECHILD, so a model that recorded
    one would decline a call Linux answers.
    [clone_checker_admits_eagain] below
    pins ONE model and ONE errno, exactly as
    [clone_checker_admits_a_pid] does for the other arm; the disjunction
    would say nothing about either.

    The keying is total because the two answers cannot overlap: every
    admitted pid is below [Fork.PID_MAX_ENVELOPE] and every member of
    [Fork.clone_errnos] encodes just under 2^64, which is
    [Checks.Sys.Kernel.Fork.clone_pid_not_errno].  So naming the errno
    set is what keeps the decline from widening — no answer
    outside [Fork.clone_errnos] can take that arm — and it also
    forces the other arm to fire everywhere else.

    Which of [Checks.Examples]'s four reasons: the FIRST, a [forall] over
    every model, every argument shape and every admissible resolution,
    and the THIRD — [State.m_has_children] is model-internal, and one
    run reaches the set state for one model and one pid only. *)
Lemma clone_resolve_declines_or_sets_children : forall i m eff m' evs,
  clone_resolve i m (Ok eff m' evs) ->
  (errno_ret_in clone_errnos (eff_ret eff) = true -> m' = m) /\
  (errno_ret_in clone_errnos (eff_ret eff) = false -> m_has_children m' = true).
Proof.
  intros i m eff m' evs H.
  exact (clone_resolve_declines_or_sets_children_in clone_errnos i m eff m' evs
           (incl_refl clone_errnos) eq_refl H).
Qed.

(** The same claim at the dispatcher, over both entry points at once.
    [clone3] adds a copy-in ledger and nothing else — [clone3_resolve_inv]
    strips it and hands back the very [clone_resolve] outcome, with the
    same post-model — so one lemma covers 220 and 435 and the two cannot
    drift apart.

    -EFAULT JOINED THE LIST because [copy_struct_from_user]'s [access_ok]
    now answers it for a [uargs] range it refuses ([Fork.clone3_spec]),
    and that answer creates no child: the first implication covers it and
    says the model is left untouched. *)
Lemma clone_success_sets_children : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 220%Z \/ bv_unsigned (in_sysno i) = 435%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  (errno_ret_in (EFAULT :: clone_errnos) (eff_ret eff) = true -> m' = m) /\
  (errno_ret_in (EFAULT :: clone_errnos) (eff_ret eff) = false ->
   m_has_children m' = true).
Proof.
  intros i m eff m' evs [Hno|Hno] H.
  - apply (clone_is_clone_spec i m _ Hno) in H.
    unfold clone_spec in H.
    destruct (clone_fork_flags_b (in_arg i 0));
      [|unfold unmodeled in H; discriminate].
    exact (clone_resolve_declines_or_sets_children_in (EFAULT :: clone_errnos)
             _ _ _ _ _ (incl_tl EFAULT (incl_refl clone_errnos)) eq_refl H).
  - apply (clone3_is_clone3_spec i m _ Hno) in H.
    unfold clone3_spec in H.
    destruct (negb (bv_eqb (in_arg i 1) (Z_to_bv 64 CLONE_ARGS_SIZE)));
      cbv iota in H; [unfold unmodeled in H; discriminate|].
    sys_unfold. cbv iota in H. inv_ok.
    destruct (copy_bytes_map (in_mem i) (in_arg i 0) CLONE_ARGS_SIZE)
      as [bs|] eqn:Hbs; hall Hbs; inv_ok.
    2: { (* the refused range: -EFAULT is in the list, and the model is
            untouched *)
         destruct (negb (access_okb (in_arg i 0) CLONE_ARGS_SIZE)) eqn:Hs;
           hall Hs; inv_ok.
         cbn [eff_ret]. split; intros He; [reflexivity|].
         rewrite (errno_ret_in_intro (EFAULT :: clone_errnos) EFAULT
                    (in_eq _ _)) in He.
         discriminate He. }
    destruct (clone3_fork_args_b bs) eqn:Ha; hall Ha; inv_ok.
    match goal with
    | Hr : clone3_resolve _ _ _ (Ok _ _ _) |- _ =>
        apply clone3_resolve_inv in Hr as (e0 & H0 & Hret); rewrite Hret
    end.
    exact (clone_resolve_declines_or_sets_children_in (EFAULT :: clone_errnos)
             _ _ _ _ _ (incl_tl EFAULT (incl_refl clone_errnos)) eq_refl H0).
Qed.

(** And for the executable checker, which is the half a
    statement about [Specs.syscall_spec] does not reach: the extracted
    acceptor cannot admit a pid and hand back a model with the field
    clear either.  It is a corollary rather than a second proof —
    [ExecutableSpecs.check_syscall_sound_ok] says every [CheckOk] is an
    admissible outcome — so the two halves cannot disagree about what
    "declines" means. *)
Corollary check_clone_success_sets_children : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 220%Z \/ bv_unsigned (in_sysno i) = 435%Z ->
  check_syscall i eff m = CheckOk m' evs ->
  (errno_ret_in (EFAULT :: clone_errnos) (eff_ret eff) = true -> m' = m) /\
  (errno_ret_in (EFAULT :: clone_errnos) (eff_ret eff) = false ->
   m_has_children m' = true).
Proof.
  intros i m eff m' evs Hno H.
  apply clone_success_sets_children with (i := i) (eff := eff) (evs := evs);
    [exact Hno|].
  now apply check_syscall_sound_ok.
Qed.

(** [execve] (221).  A successful exec replaces the address space, which
    this development cannot express at all: the loaded segments are a
    SECTION PARAMETER of [Run.WithMemImage], fixed for the whole run, so
    no step can replace them.  [begin_new_exec] (fs/exec.c) also resets
    signal dispositions, closes the close-on-exec descriptors
    ([do_close_on_exec]) and — on riscv64 — zeroes the pointer-masking
    length through [activate_mm] and [flush_thread].  The failure returns
    are not separable either: [do_open_execat] opens with [MAY_EXEC], and
    [Fs.Fs] records no file modes, so a spec that answered [-EFAULT] for
    a bad argv would be REJECTING the [-EACCES] a real kernel returns for
    the same call on a non-executable file. *)
Lemma execve_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 221%Z -> syscall_spec i m Unmodeled.
Proof. intros i m Hno. declined_at Hno. Qed.

(** [execveat] (281).  [execve] plus a dirfd and [AT_EMPTY_PATH] /
    [AT_SYMLINK_NOFOLLOW]; [execveat(AT_FDCWD, p, a, e, 0)] is
    [execve(p, a, e)].  Everything said of 221 applies, over a resolution
    base the model would additionally have to carry. *)
Lemma execveat_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 281%Z -> syscall_spec i m Unmodeled.
Proof. intros i m Hno. declined_at Hno. Qed.

(** [getrlimit] (163) and [setrlimit] (164), registered because
    arguments rest on each of them having no arm, and the two
    arguments are different ones.

    164 WRITES.  [State.limst_nofile] holds ONE soft RLIMIT_NOFILE for a
    whole run and [Fs.File.dup3_spec] compares [newfd] against it, which
    are both claims that nothing modeled can change the limit.  Three
    system calls reach [do_prlimit] with a [new_rlim] (kernel/sys.c,
    Linux v6.18.46, commit 1f99e9ab748f): 164, its compat twin, and
    [prlimit64] (261).  261 IS inside [Specs.modeled_sysnos], and is
    closed by an arm rather than by this register —
    [Kernel.Sys.prlimit64_spec] declines every resource but RLIMIT_CORE
    — which is why only 164 needs an entry here.  Everything else that
    writes [signal->rlim] runs at exec, at boot or on a core dump, and
    is out of reach for the same reason 221 is; [Run.valid_nofile]
    enumerates those.

    163 READS, and passes [NULL] for [new_rlim] (kernel/sys.c,
    [SYSCALL_DEFINE2(getrlimit)]), so it changes nothing.  Its decline
    is load-bearing on the other side: no modeled syscall reads the
    limit back.

    Neither is modeled, and neither is merely undone work: they enter
    [do_prlimit] DIRECTLY, skipping [check_prlimit_permission] and the
    [security_task_prlimit] hook (kernel/sys.c, Linux v6.18.46, commit
    1f99e9ab748f), so they are a different call from [prlimit64] and
    would need their own argument.  musl reaches the limits through
    [prlimit64] regardless — [Kernel.Sys.prlimit64_spec] says why. *)
Lemma getrlimit_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 163%Z -> syscall_spec i m Unmodeled.
Proof. intros i m Hno. declined_at Hno. Qed.

Lemma setrlimit_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 164%Z -> syscall_spec i m Unmodeled.
Proof. intros i m Hno. declined_at Hno. Qed.

(** [wait4] (260) — MODELED, and stated here in the negative.  A file of
    tripwires is only worth reading if it stops being one when the fact
    changes.

    A faithful [wait4] at a caller WITH a child needs a
    child to wait for and a status ENCODING the model cannot produce —
    the signal-death half, [WIFSIGNALED] / [WTERMSIG] and the core-dump
    bit, which [Monad.outcome]'s two constructors cannot tell apart
    from a voluntary exit.  BOTH HALVES OF THAT ARGUMENT ARE ABOUT
    MODELING THE CHILD.  A caller with NO child has a complete, decidable
    answer that needs neither: -ECHILD.  [Exit.wait4_spec] gives that
    answer and nothing else — no pid, no status word, no encoding, so
    [Monad.outcome] never has to widen.

    THE ARGUMENT RUNS THROUGH THIS FILE, which is why the statement
    belongs here rather than beside the spec alone.  [Exit.wait4_spec]
    is correct only for a caller whose children and tracees are both
    empty, and this file is HALF of what makes that decidable: 220 and
    435 create a child in-model, and what makes the composition sound
    is that their success branch RECORDS it, which is
    [clone_resolve_declines_or_sets_children] above.  A creating arm
    that skipped [State.with_children] is the change that would make
    [Exit.wait4_spec] WRONG rather than merely incomplete; for 220 and
    435 that lemma is what breaks first, and a new child-creating
    number owes an instance of its own.

    THE OTHER HALF IS NOT DISCHARGED IN THE MODEL, and saying so is
    the point of this paragraph.  The lists must also have STARTED empty,
    and that is a property of the LAUNCHER: Linux's [execve] empties
    neither, so a process that forked a grandchild or attached a
    tracee before exec'ing this image hands it something to wait for.
    That is a closed-world assumption about the environment of exactly
    the shape [State.access_okb]'s is above.

    This statement is carried by two different
    facts at once: at a childless caller -ECHILD really is the only
    answer, and at a caller with a child there is no [Ok] outcome at all
    because [Exit.wait4_spec] declines.  Both halves are needed —
    dropping the gate would leave the first covering a case it is false
    for.  [Checks.Examples.wait4_with_a_child_is_unmodeled] is the
    statement of the second half that does NOT live in this file.

    See [Exit.wait4_spec] for the three guards that decline: any
    [upid] but -1, any [options] but [Uapi.WNOHANG] (a blocking wait is
    a wait-queue sleep, and can answer -EINTR), and a non-NULL
    [rusage].  [stat_addr] is not among them and is not read at all —
    [kernel_wait4] guards its copy-out on [ret > 0], so no -ECHILD
    touches the pointer — which is why the lemma below needs no
    hypothesis about it.

    WHAT THIS OWES A SIBLING.  [Kernel.Fork.clone_resolve] has a
    succeeding arm, so a child can exist, and
    [Signal.sigaction_accepted] is {SIGINT, SIGTERM}: it excludes
    SIGCHLD (17).  What [Exit.wait4_spec] rests on is not that no child can
    exist, but that the model RECORDS whether one does.  That is
    [clone_success_sets_children] above. *)
Lemma wait4_not_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 260%Z ->
  bv_unsigned (pid32 (in_arg i 0)) = WAIT_ANY32 ->
  bv_unsigned (waitopts32 (in_arg i 2)) = WNOHANG ->
  w_is0 (in_arg i 3) = true ->
  m_has_children m = false ->
  ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hup Hop Hru Hch H.
  apply (check_syscall_complete_unmodeled i m (mkEffect (errno_ret ECHILD) [] []))
    in H.
  rewrite (check_syscall_wait4 i _ m Hno) in H.
  unfold check_wait4 in H.
  rewrite Hup, Hop, Hru, !Z.eqb_refl in H. cbn [negb] in H.
  rewrite Hch in H. cbv iota in H.
  rewrite bv_eqb_refl in H. discriminate.
Qed.

(** ...and what it is not declined TO, which is the half a
    [~ Unmodeled] statement cannot carry.  This is the soundness claim
    for 260 in one line: EVERY admissible resolution of the number, at
    every argument shape and in every model, is -ECHILD with no memory
    moved.  No argument hypothesis is needed — outside the modeled
    shape there is no [Ok] outcome to constrain.

    One run reaches the accepting half of this and one
    rejection at a time; only a [forall] says that a reaped pid,
    WNOHANG's bare 0 and an -EFAULT are ALL absent, and that no arm
    anywhere writes through [stat_addr].  That is [Checks.Examples]'s
    first reason, and it is the statement priority 2 turns on: a
    childless process cannot reap, so a model admitting a reap would
    admit a trace Linux cannot produce. *)
Lemma wait4_answers_only_echild : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 260%Z ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (errno_ret ECHILD) [] [] /\ m' = m /\ evs = [].
Proof.
  intros i m [ret ws zs us cs ins] m' evs Hno H.
  apply check_syscall_complete_ok in H.
  rewrite (check_syscall_wait4 i _ m Hno) in H.
  unfold check_wait4 in H.
  destruct (negb (Z.eqb (bv_unsigned (pid32 (in_arg i 0))) WAIT_ANY32));
    [discriminate|].
  destruct (negb (Z.eqb (bv_unsigned (waitopts32 (in_arg i 2))) WNOHANG));
    [discriminate|].
  destruct (negb (w_is0 (in_arg i 3))); [discriminate|].
  (* a caller WITH a child declines, so it contributes no [Ok] to
     constrain; the claim below is about the childless case, which is
     the only one that answers *)
  destruct (m_has_children m); [discriminate|].
  destruct ws as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct ins as [|? ?]; [|discriminate].
  destruct (bv_eqb ret (errno_ret ECHILD)) eqn:Hr; [|discriminate].
  apply bv_eqb_eq in Hr. subst ret. inversion H; clear H; subst.
  split; [reflexivity|]. split; reflexivity.
Qed.

(** [setsid] (157) — MODELED, and stated here in the negative.  A file of tripwires
    is only worth reading if it stops being one when the fact changes:
    the statement below fails to compile the moment 157 loses its arm,
    exactly as its neighbours fail the moment one of theirs gains one.

    The call needs little state.  [ksys_setsid] (kernel/sys.c — its two tests, their
    order and the returned session id unchanged in mainline v4.17..v7.2
    and stable linux-4.19.y..linux-7.1.y; see
    [Kernel.Sys.setsid_spec] for the one edit to the function's TEXT in
    that window) fails when the caller already carries
    [group_leader->signal->leader], or when
    [pid_task(sid, PIDTYPE_PGID)] finds a live task whose process-group
    id is the caller's own pid.  Neither is something [State.ProcInput]
    carries, so every call admits -EPERM.  But the first condition, once
    true, is PERMANENT — setsid is its only writer, it never clears it,
    and [SYSCALL_DEFINE2(setpgid)] will not move a session leader — so a
    call that SUCCEEDS makes every later one fail.  The second can
    outlive the caller's membership of the group it names, so a call
    that FAILS may still be followed by one that succeeds and records
    nothing.  One bit, and it is only ever set by success:
    [State.m_setsid_succeeded].  See [Kernel.Sys.setsid_spec]. *)
Lemma setsid_not_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 157%Z -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno H.
  apply (check_syscall_complete_unmodeled i m (mkEffect (errno_ret EPERM) [] []))
    in H.
  unfold check_syscall in H. rewrite Hno in H.
  autorewrite with arm_unfold in H.
  cbn [lookup_ca checked_table Z.eqb Pos.eqb] in H.
  autorewrite with arm_unfold in H.
  eapply check_setsid_no_unmodeled. exact H.
Qed.

(** AND THE FULL CHARACTERIZATION, which is what makes 157's entry as
    strong as its neighbours rather than merely non-vacuous.

    Every other number here is pinned by a decline lemma, and a decline
    lemma says EVERYTHING about that number: [Unmodeled] is the whole
    answer.  [setsid_not_unmodeled] above says much less — it rules out
    one answer, and would still hold if 157 dispatched to some other
    total spec that never declines.  This closes that gap: at 157 the
    dispatcher is [Kernel.Sys.setsid_spec] and nothing else, for every
    input, model and outcome.  Replace the arm and this breaks; remove
    it and [setsid_not_unmodeled] breaks.

    It is free because [Sys.Dispatch.dispatch_arm] already states the
    biconditional for any table and any arm — the table-driven
    dispatcher is what makes a per-number characterization a lookup
    rather than a case analysis over a chain. *)
Lemma setsid_is_setsid_spec : forall i m o,
  bv_unsigned (in_sysno i) = 157%Z ->
  (syscall_spec i m o <-> setsid_spec i m o).
Proof.
  intros i m o Hno. unfold syscall_spec.
  apply (dispatch_arm spec_table i m o (mkSpecArm 157%Z (fun i => setsid_spec i))).
  rewrite Hno. reflexivity.
Qed.

(** [prctl] (167).  Load-bearing as an ABSENCE, and the ABSENCE IS
    AN OPTION RATHER THAN A NUMBER.  This is the first of the two callers
    of riscv's [set_tagged_addr_ctrl], and so one half of why
    [State.access_okb] is exact.  Modeling any option has a cost: the
    fact moves from membership in [Specs.modeled_sysnos] — a closed
    list — to the body of a multiplexer, where the next option added
    silently decides whether [readv]'s address check is still exact.

    THE ANSWER TO THAT COST IS ANOTHER CLOSED
    LIST.  [Kernel.Sys.prctl_modeled_options] is the set of options the
    arm answers, written as a definition rather than left implicit in a
    [match], and [prctl_modeled_options_are] pins it EXACTLY — not that
    55 is absent from it, which a widening could preserve, but that the
    list is [[PR_CAPBSET_READ]] and nothing else.  So the tripwire keeps
    its shape: an edit that teaches [prctl] a second
    option fails a named proof in this file, and whoever makes that edit
    has to come back here and say what it does to the tagging argument.
    The three statements below are that argument, from the general to
    the particular.
    [PR_SET_TAGGED_ADDR_CTRL] is option 55; the sign-extending shift it
    enables lives in [__untagged_addr_remote]
    (arch/riscv/include/asm/uaccess.h) and is
    applied per uaccess primitive, not once at the syscall boundary, so
    it could not be modeled by masking registers on entry either. *)

Example prctl_modeled_options_are :
  prctl_modeled_options = [PR_CAPBSET_READ].
Proof. reflexivity. Qed.

(** Every option outside that list falls through [prctl_spec]'s first
    test.  Stated over [Syscall.int32] of a0 because that is what the
    dispatcher's arm passes: [prctl]'s [option] is an [int] in
    [SYSCALL_DEFINE5(prctl)], so the kernel never sees the register's
    high half either. *)
Lemma prctl_option_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 167%Z ->
  ~ In (bv_unsigned (int32 (in_arg i 0))) prctl_modeled_options ->
  syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hopt. unfold syscall_spec.
  apply (dispatch_arm spec_table i m Unmodeled
           (mkSpecArm 167%Z
              (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i)));
    [rewrite Hno; reflexivity|].
  cbn [sa_spec]. unfold prctl_spec.
  destruct (Z.eqb_spec (bv_unsigned (int32 (in_arg i 0))) PR_CAPBSET_READ)
    as [Heq|_]; cbn [negb].
  - exfalso. apply Hopt. unfold prctl_modeled_options. rewrite Heq.
    now left.
  - apply unmodeled_intro.
Qed.

(** The particular case the tagging argument needs. *)
Lemma prctl_tagged_addr_ctrl_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 167%Z ->
  bv_unsigned (int32 (in_arg i 0)) = 55%Z ->
  syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hopt. apply prctl_option_unmodeled; [exact Hno|].
  rewrite Hopt. unfold prctl_modeled_options, PR_CAPBSET_READ.
  intros [H|H]; [discriminate H|exact H].
Qed.

(** [ptrace] (117).  The OTHER caller of [set_tagged_addr_ctrl], through
    [PTRACE_SETREGSET] with [NT_RISCV_TAGGED_ADDR_CTRL]
    (arch/riscv/kernel/ptrace.c).  Both routes arrived in v6.13 in one
    series, so there is no version window in which 167 alone would have
    sufficed — which is why this number is pinned beside it rather than
    left to the argument about there being no second task. *)
Lemma ptrace_unmodeled : forall i m,
  bv_unsigned (in_sysno i) = 117%Z -> syscall_spec i m Unmodeled.
Proof. intros i m Hno. declined_at Hno. Qed.

(** [rt_sigprocmask] (135) and [rt_sigaction] (134) are NOT pinned
    here: each has an arm, so a lemma saying it falls through the
    dispatcher would be false.  The obligation a decline of them would
    carry is still live, and this note says where it is.

    WHAT THE OBLIGATION IS.  The flag word [Fork.clone_fork_flags_b] admits is
    [SIGCHLD], which REQUESTS a signal to the caller when the child
    exits.  [Fork.clone_spec]'s header argues that nothing comes of it,
    through the caller's disposition and mask: a [SIG_DFL] SIGCHLD is
    discarded, a blocked one is queued but sets no [TIF_SIGPENDING].

    WHY A CHANGEABLE MASK DOES NOT REOPEN IT.  With an arm for 135 a program can
    [SIG_UNBLOCK] SIGCHLD, so "a blocked SIGCHLD is queued and sets no
    [TIF_SIGPENDING]" does not cover every case on its own.  It does
    not need to.  Unblocking a queued SIGCHLD is what makes it
    deliverable, and delivery goes through [get_signal] (kernel/signal.c),
    which re-reads the DISPOSITION: [SIG_DFL] together with
    [sig_kernel_ignore] discards it there.  So the blocked case funnels
    into the unblocked one, and both land on the disposition half.  That
    half is where all the weight sits.

    AND THE DISPOSITION HALF IS NOT A NUMBER EITHER.  134 is modeled, so
    what carries it is [Signal.sigaction_accepted], whose accepted set is
    {SIGINT, SIGTERM}: an install FOR SIGCHLD fails closed at the SIGNAL.
    The note above that definition states the invariant in the direction
    that matters — the accepted set is a claim about the rest of the
    model, and any change giving the model a child owes SIGCHLD's removal.

    THE TRIPWIRE IS AT THE SIGNAL.  An edit that puts 17
    back into the accepted set is caught by
    [Checks.Cases.Kernel.Signal.rt_sigaction_sigchld_unmodeled], which
    fails to compute the moment it is accepted.  That is a tighter guard
    than a decline of either number, because it holds with both of them
    modeled. *)

(* =========================================================================
   What a declined syscall does to a RUN
   ========================================================================= *)

Section Runs.

Variable segs : list Segment.

(** The syscall counterpart of [Run.reaches_unmodeled_intro], which
    covers only the INSTRUCTION arm.  Stated at the configuration level
    so the numbers above compose with it. *)
Lemma unmodeled_at_syscall : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model Unmodeled ->
  unmodeled_at segs (mkCfg ms model).
Proof.
  intros ms model x8 Hh Hsvc Hspec.
  split; [exact Hh|]. right. exists x8. split; assumption.
Qed.

(** …and what that costs a source binary: reaching such a configuration
    on ANY execution refutes [Equivalence.modeled], so no equivalence
    theorem can be proved about it.  This is the coverage cost of
    declining, stated once and precisely.  It is NOT a soundness risk and
    NOT a vacuous pass: [modeled] is a conjunct of
    [Equivalence.strong_equiv] that the proof must DISCHARGE, so a
    forking source makes the theorem unprovable rather than free. *)
Lemma reaches_unmodeled_syscall : forall c0 tr ms model x8,
  star segs c0 tr (mkCfg ms model) ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model Unmodeled ->
  reaches_unmodeled segs c0.
Proof.
  intros c0 tr ms model x8 Hstar Hh Hsvc Hspec.
  exists tr, (mkCfg ms model). split; [exact Hstar|].
  eapply unmodeled_at_syscall; eassumption.
Qed.

(** The two composed, at a declined number: a run that
    reaches a pending [execve] is a run this model does not cover.
    [clone] (220) is modeled parent-side, and 221 is the number a
    forked child reaches immediately afterwards. *)
Corollary execve_refutes_coverage : forall c0 tr ms model x8,
  star segs c0 tr (mkCfg ms model) ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 221%Z ->
  reaches_unmodeled segs c0.
Proof.
  intros c0 tr ms model x8 Hstar Hh Hsvc Hno.
  eapply reaches_unmodeled_syscall; try eassumption.
  apply execve_unmodeled. exact Hno.
Qed.

End Runs.

(* =========================================================================
   The checker agrees — the other half of every statement above
   ========================================================================= *)

(** The lemmas above are about [Specs.syscall_spec], the definition.  The
    extracted acceptor is [ExecutableSpecs.check_syscall].  These
    close the loop for each number, so the definition and the checker
    are pinned to the same verdict rather than to two independent
    claims.  [check_syscall_err_iff] is what makes them one statement.

    Concrete rather than quantified because [check_syscall] is a
    function: [vm_compute] settles it, and the universally quantified
    content is already above. *)
(* None of the process input's fields reaches the checks below — every
   syscall number here is outside [Specs.modeled_sysnos] and is declined
   before any model state is read — so the ids are an ordinary
   unprivileged pair rather than a claim. *)
Definition pc_model : Model :=
  init_model [] 0 0 (Z_to_bv 64 sp_window_lo) 0x40000000%Z
    (mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
                 net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48).

Definition pc_input (n : Z) : SyscallInput :=
  mkInput (Z_to_bv 64 n) [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** [clone] and [clone3] are modeled, so their examples run the other
    way round: the checker must DECLINE the flag words the spec does not
    admit, and answer the one it does.  [pc_input] passes zero in every
    argument register, which is a flag word of 0 — not [SIGCHLD] — and a
    [clone3] whose [size] is 0. *)
Example clone_checker_declines_flags_zero :
  check_syscall (pc_input 220) (mkEffect 0 [] []) pc_model = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example clone3_checker_declines_size_zero :
  check_syscall (pc_input 435) (mkEffect 0 [] []) pc_model = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** [clone(SIGCHLD, 0, 0, 0, 0)] against the same model, which has no
    open regular file: a pid inside the envelope is accepted, so is one
    of the four admitted errnos, and 0 — the CHILD's answer — is not.
    These are the concrete
    companions this section exists for: the statements above are about
    [Specs.syscall_spec], and these run the same facts through
    [ExecutableSpecs.check_syscall], the extracted checker. *)
Definition pc_clone_input : SyscallInput :=
  mkInput (Z_to_bv 64 220) [Z_to_bv 64 SIGCHLD; 0; 0; 0; 0; 0]
    (fun _ => None) (fun _ => None).

(** The success arm records the child: [Kernel.Fork.clone_resolve] calls
    [State.with_children] on this branch, so the post-model is not
    [pc_model].  That is what [Kernel.Exit.wait4_spec]'s -ECHILD gate
    reads, and pinning it here is what makes the two compose. *)
Example clone_checker_admits_a_pid :
  check_syscall pc_clone_input (mkEffect (Z_to_bv 64 4242) [] []) pc_model
  = CheckOk (with_children pc_model) [].
Proof. vm_compute. reflexivity. Qed.

Example clone_checker_admits_eagain :
  check_syscall pc_clone_input (mkEffect (errno_ret EAGAIN) [] []) pc_model
  = CheckOk pc_model [].
Proof. vm_compute. reflexivity. Qed.

Example clone_checker_refuses_zero :
  check_syscall pc_clone_input (mkEffect 0 [] []) pc_model = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example clone_checker_refuses_the_envelope_bound :
  check_syscall pc_clone_input
    (mkEffect (Z_to_bv 64 PID_MAX_ENVELOPE) [] []) pc_model = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** [ENFILE] is 23 and [EMFILE], which IS admitted, is 24 — so this
    refuses the nearest neighbour of an admitted errno rather than a
    distant one. *)
Example clone_checker_refuses_another_errno :
  check_syscall pc_clone_input (mkEffect (errno_ret ENFILE) [] []) pc_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** THE SHARED FILE OFFSET.  The quantified statement is
    [clone_open_file_unmodeled] above; this is its concrete checker
    companion, over one model and one descriptor shape.  [pc_model]'s own
    descriptors are the three [FdChannel] seeds [State.init_model]
    installs, which the gate does not close on, and that is what makes
    the accepting examples above non-vacuous. *)
Definition pc_model_open_file : Model :=
  with_fds ((Z_to_bv 64 3, FdFile [] (Z_to_bv 64 0)) :: m_fds pc_model)
    pc_model.

Example clone_checker_declines_with_a_file_open :
  check_syscall pc_clone_input (mkEffect (Z_to_bv 64 4242) [] [])
    pc_model_open_file = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** 135 is not in this group: [rt_sigprocmask] is modeled — see
    the note on it above — and a concrete decline example for it
    would only assert that a modeled
    number is unmodeled.  The obligation is pinned by
    [Checks.Cases.Kernel.Signal.rt_sigaction_sigchld_unmodeled].
    Every number below has its quantified statement above; if one
    of these ever has to go, check that the statement went first. *)
Example execve_checker_unmodeled :
  check_syscall (pc_input 221) (mkEffect 0 [] []) pc_model = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example execveat_checker_unmodeled :
  check_syscall (pc_input 281) (mkEffect 0 [] []) pc_model = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example getrlimit_checker_unmodeled :
  check_syscall (pc_input 163) (mkEffect 0 [] []) pc_model = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example setrlimit_checker_unmodeled :
  check_syscall (pc_input 164) (mkEffect 0 [] []) pc_model = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** [wait4] is MODELED, so its concrete cases pin what the checker
    ACCEPTS and what it REJECTS rather than that it declines.
    [pc_input] carries all-zero arguments, which is [upid = 0] — a
    declining shape — so these use [wait4_input_any], the shape both
    dropbear call sites issue: [waitpid(-1, NULL, WNOHANG)].

    TWO CASES.  [wait4_checker_echild] is [wait4_not_unmodeled]'s
    checker half at the shape its hypotheses name.
    [wait4_checker_rejects_a_reap] is the concrete witness for
    [wait4_answers_only_echild]: a kernel claiming to have reaped pid
    4321 is REJECTED, which is the whole soundness point and the case
    that catches a [wait4] that admits a reap.  Without it
    the accept above is satisfied by a checker that answers [CheckOk]
    to everything.  The argument gates are left to the
    lemmas' hypotheses. *)
Definition wait4_input_any : SyscallInput :=
  mkInput (Z_to_bv 64 260)
    [Z_to_bv 64 (-1); 0; Z_to_bv 64 1; 0; 0; 0]
    (fun _ => None) (fun _ => None).

Example wait4_checker_echild :
  check_syscall wait4_input_any (mkEffect (errno_ret ECHILD) [] []) pc_model
  = CheckOk pc_model [].
Proof. vm_compute. reflexivity. Qed.

Example wait4_checker_rejects_a_reap :
  check_syscall wait4_input_any (mkEffect (Z_to_bv 64 4321) [] []) pc_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** setsid is the one number PINNED here that the checker admits, so it
    gets the shape rather than the refusal.  ([read] (63) is admitted
    too, at the bottom of this file, but only as a non-vacuity witness.)  Five executions: the two answers a
    first call may give, the forged answer that is neither, and the two
    a call after a SUCCESSFUL one may give — where the whole content of
    the model is that a repeat success is not among them.  Note what is
    NOT here: nothing pins a second call after a FAILED one, because
    Linux allows it to succeed (the group that blocked the first can
    empty out) and so does the model — [pc_model] itself is the state a
    failed call leaves behind. *)
Example setsid_checker_first_call_eperm :
  check_syscall (pc_input 157) (mkEffect (errno_ret EPERM) [] []) pc_model
  = CheckOk pc_model [].
Proof. vm_compute. reflexivity. Qed.

Example setsid_checker_first_call_session_id :
  check_syscall (pc_input 157) (mkEffect (Z_to_bv 64 1234) [] []) pc_model
  = CheckOk (with_setsid_succeeded (with_tid (Z_to_bv 64 1234) pc_model)) [].
Proof. vm_compute. reflexivity. Qed.

Example setsid_checker_rejects_zero :
  check_syscall (pc_input 157) (mkEffect 0 [] []) pc_model = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example setsid_checker_after_success_rejects_success :
  check_syscall (pc_input 157) (mkEffect (Z_to_bv 64 1234) [] [])
    (with_setsid_succeeded (with_tid (Z_to_bv 64 1234) pc_model)) = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example setsid_checker_after_success_eperm :
  check_syscall (pc_input 157) (mkEffect (errno_ret EPERM) [] [])
    (with_setsid_succeeded (with_tid (Z_to_bv 64 1234) pc_model))
  = CheckOk (with_setsid_succeeded (with_tid (Z_to_bv 64 1234) pc_model)) [].
Proof. vm_compute. reflexivity. Qed.

(** The two examples above set the bit AND pin the tid, so between them
    they cannot say WHICH of the two a rejection came from: a checker
    that refused a second success because [m_tid] was already [Some _]
    would satisfy both.  This one pins the bit alone -- [pc_model] has
    [m_tid = None], and [with_setsid_succeeded] does not change it -- so
    it rejects only if the bit is what is being read. *)
Example setsid_checker_bit_alone_rejects_success :
  check_syscall (pc_input 157) (mkEffect (Z_to_bv 64 1234) [] [])
    (with_setsid_succeeded pc_model) = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** The concrete companions.  [pc_input] leaves a0 at 0, which is no
    prctl option at all, so on its own it would decline for a reason
    weaker than the one this file is about; [pc_prctl_input 55] is
    [PR_SET_TAGGED_ADDR_CTRL], the option the tagging argument names. *)
Definition pc_prctl_input (opt : Z) : SyscallInput :=
  mkInput (Z_to_bv 64 167) [Z_to_bv 64 opt; 0; 0; 0; 0; 0]
          (fun _ => None) (fun _ => None).

Example prctl_checker_tagged_addr_ctrl_unmodeled :
  check_syscall (pc_prctl_input 55) (mkEffect 0 [] []) pc_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** NAMED FOR THE OPTION, NOT THE NUMBER, and deliberately: an
    [Example <syscall>_checker_unmodeled] asserts that the NUMBER has no
    dispatcher arm, and 167 has one.  Both examples here assert
    something narrower — that a particular OPTION declines — so neither
    may carry that name. *)
Example prctl_checker_option_zero_unmodeled :
  check_syscall (pc_input 167) (mkEffect 0 [] []) pc_model = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** And the other side of the multiplexer, so the two examples above
    are not satisfied by an arm that declines everything:
    [PR_CAPBSET_READ] on a valid capability is 1, and the model is left
    alone. *)
Example prctl_checker_capbset_read :
  check_syscall (pc_prctl_input 23) (mkEffect (Z_to_bv 64 1) [] []) pc_model
  = CheckOk pc_model [].
Proof. vm_compute. reflexivity. Qed.

Example ptrace_checker_unmodeled :
  check_syscall (pc_input 117) (mkEffect 0 [] []) pc_model = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** NON-VACUITY.  Most of what is above rules something OUT, and a
    dispatcher answering [CheckUnmodeled] for EVERY number would satisfy
    all of it, so it is worth pinning that the shape can also come out
    the other way.  This file does not rest on that alone:
    [setsid_not_unmodeled],
    [setsid_is_setsid_spec], the setsid executions and the clone
    lemmas above are each violated by an all-[CheckUnmodeled]
    dispatcher too.  This example stays because it says it of a number this file
    does not otherwise mention, and because it is the only one here
    that is a pure witness rather than a constraint: [read] (63) is on
    the modeled surface and does not decline. *)
Example modeled_number_is_not_unmodeled :
  check_syscall (pc_input 63) (mkEffect 0 [] []) pc_model <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.
