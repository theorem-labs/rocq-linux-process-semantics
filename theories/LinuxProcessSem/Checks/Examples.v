(** * LinuxProcessSem.Checks.Examples — what the definitions MEAN

    Not part of the trusted specification: this file is QA on the
    definitions, written to be READ.

    ** What belongs here

    The syscall model has two checkers, and they answer different
    questions.  The extracted, verified acceptor can be folded over
    every syscall a real riscv64 run makes, so it decides *does Linux
    do what the model says*.  This file
    decides *does the model say what we meant*, on cases chosen by hand.

    A case earns its place here only if one real run cannot show it.  Four
    reasons recur, and each example below says which one applies:

    - it is UNIVERSALLY QUANTIFIED — a [forall] over admissible outcomes,
      which no finite set of traces can establish (the [Lemma]s here);
    - it compares TWO RUNS — "these two programs emit the same events" is
      a statement about a pair of traces, and the acceptor folds over one
      trace per run and never compares across runs;
    - it pins MODEL-INTERNAL STATE, or a model CONSTANT, that no
      observation of a real execution reveals;
    - the environment cannot be made to produce it: a [CheckReject] needs
      a kernel behaving inadmissibly, which no truthful run shows, and
      the case here is where the rejected answer is named exactly.

    ** Types

    Event payload bytes are [bv 8] (so [b < 256] side conditions are
    typed away, and inc-cat's [(b + 1) mod 256] is just wrapping [bv 8]
    addition), channel ids / exit codes are [word = bv 64], and the
    concrete checker inputs use [word]/[byte] literals. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit Classifier.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.

From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Uaccess VaSize MmapBase Hwcap Brk
  Fs.File Fs.ReadWrite Fs.Open Fs.Stat Fs.Sync Fs.Select
  Fs.Ioctl Fs.Fcntl Fs.Locks Fs.Namei Fs.Readdir Fs.Timerfd Fs.Pipe Fs.EventFd
  Mm.Mmap Mm.Mremap Mm.Mprotect Mm.Madvise Kernel.Fork Kernel.Futex.Syscalls
  Kernel.Groups
  Kernel.Sched.Syscalls Kernel.Signal Kernel.Sys
  Kernel.Time.Hrtimer Kernel.Time.PosixTimers Kernel.Time.Time
  Net.Socket Drivers.Char.Random.

(** All prefixes of one maximal trace. *)
Definition prefixes (tr : list event) : list event -> Prop :=
  fun t => is_prefix t tr.

(** A behavior with the given trace set, no reachable error, and
    therefore nothing unmodeled. *)
Definition pure_behavior (T : list event -> Prop) : behavior :=
  {| bh_traces := T; bh_errors := False; bh_all_errors := False;
     bh_unmodeled := False |}.

(** A synthetic behavior that has at least one erroring execution.  The
    [all] parameter distinguishes "some execution errors" from "every
    execution errors", which is the quantifier boundary [equiv] must
    enforce. *)
Definition error_behavior (T : list event -> Prop) (all : Prop) : behavior :=
  {| bh_traces := T; bh_errors := True; bh_all_errors := all;
     bh_unmodeled := False |}.

(** If every source execution errors, the target is unconstrained. *)
Example all_source_traces_error_frees_target :
  equiv (error_behavior (prefixes []) True)
        (error_behavior (prefixes [ExitEv 7 []]) True).
Proof. left. exact I. Qed.

(** No existential escape: one source error is not
    enough when the source also has a non-error execution.  Even with
    identical observable prefix sets, an erroring target is rejected. *)
Example one_source_trace_survives_rejects_erroring_target :
  ~ equiv (error_behavior (prefixes [ExitEv 0 []]) False)
          (error_behavior (prefixes [ExitEv 0 []]) False).
Proof.
  intros [Hall | [_ Htarget]].
  - exact Hall.
  - apply Htarget. exact I.
Qed.

(** The same mixed source can still be matched by an error-free target. *)
Example one_source_trace_survives_accepts_safe_target :
  equiv (error_behavior (prefixes [ExitEv 0 []]) False)
        (pure_behavior (prefixes [ExitEv 0 []])).
Proof. right. split; [intro tr; tauto | tauto]. Qed.

(** The operational universal predicate is non-vacuous: it always
    supplies an existential error witness as well. *)
Example operational_all_errors_implies_may_error : forall segs c,
  all_traces_error segs c -> reaches_error segs c.
Proof. exact all_traces_error_reaches_error. Qed.

(** Same exit code — provable; different exit codes — disprovable. *)
Example same_exit_code :
  equiv (pure_behavior (prefixes [ExitEv 42 []]))
        (pure_behavior (prefixes [ExitEv 42 []])).
Proof.
  unfold equiv. right. split.
  - intro tr. tauto.
  - tauto.
Qed.

Example different_exit_code :
  ~ equiv (pure_behavior (prefixes [ExitEv 42 []]))
          (pure_behavior (prefixes [ExitEv 7 []])).
Proof.
  intro H. unfold equiv in H.
  destruct H as [H | [H _]]; [exact H|].
  specialize (H [ExitEv 42 []]). destruct H as [Hf _].
  assert (HL : is_prefix [ExitEv 42 []] [ExitEv 42 []]) by apply is_prefix_refl.
  apply Hf in HL. cbn in HL. destruct HL as [Heq _]. discriminate Heq.
Qed.

(** Exit vs. silent divergence — disprovable.  This validates
    termination-as-an-event: the diverging program's prefix set is just
    {[]}, which is missing the [ExitEv] prefix. *)
Example exit_vs_divergence :
  ~ equiv (pure_behavior (prefixes [ExitEv 0 []]))
          (pure_behavior (prefixes [])).
Proof.
  intro H. unfold equiv in H.
  destruct H as [H | [H _]]; [exact H|].
  specialize (H [ExitEv 0 []]). destruct H as [Hf _].
  assert (HL : is_prefix [ExitEv 0 []] [ExitEv 0 []]) by apply is_prefix_refl.
  apply Hf in HL. cbn in HL. exact HL.
Qed.

(** Channel liveness: stdout-write-then-diverge vs. diverge is
    disprovable, because channel bytes are observable as they happen.
    Contrast [file_write_emits_nothing] below — a write to a FILE emits
    no events, so file-write-then-diverge and diverge share the prefix
    set {[]} and ARE equivalent.  The file system is observed only at
    exit. *)
Example write_then_diverge_vs_diverge :
  ~ equiv (pure_behavior (prefixes [WriteEv 1 104]))
          (pure_behavior (prefixes [])).
Proof.
  intro H. unfold equiv in H.
  destruct H as [H | [H _]]; [exact H|].
  specialize (H [WriteEv 1 104]). destruct H as [Hf _].
  assert (HL : is_prefix [WriteEv 1 104] [WriteEv 1 104]) by apply is_prefix_refl.
  apply Hf in HL. cbn in HL. exact HL.
Qed.

(** cat vs. byte-increment cat — the input-modeling test.  Idealized
    trace sets: `cat` echoes each byte it reads; `inc-cat` writes each
    byte plus one (mod 256 — which is just wrapping [bv 8] addition).
    Because [ReadEv] CARRIES the byte read, the trace
    [ReadEv 0 0; WriteEv 1 0] belongs to cat but not to inc-cat, and the
    two are distinguishable.  (If read events
    did not carry the byte, both programs would have the same
    [ReadEv; WriteEv b] traces — the design this example guards
    against.) *)
Inductive cat_tr : list event -> Prop :=
| cat_tr_nil : cat_tr []
| cat_tr_rw : forall (b : byte) tr, cat_tr tr ->
    cat_tr (ReadEv 0 b :: WriteEv 1 b :: tr).

Inductive inc_tr : list event -> Prop :=
| inc_tr_nil : inc_tr []
| inc_tr_rw : forall (b : byte) tr, inc_tr tr ->
    inc_tr (ReadEv 0 b :: WriteEv 1 (b + 1) :: tr).

Definition cat_behavior : behavior :=
  pure_behavior (fun t => exists tr, cat_tr tr /\ is_prefix t tr).
Definition inc_behavior : behavior :=
  pure_behavior (fun t => exists tr, inc_tr tr /\ is_prefix t tr).

Example cat_vs_byte_increment_cat : ~ equiv cat_behavior inc_behavior.
Proof.
  intros [H | [H _]]; [exact H|].
  destruct (H [ReadEv 0 0; WriteEv 1 0]) as [Hf _].
  lapply Hf.
  2:{ exists [ReadEv 0 0; WriteEv 1 0]. split.
      - apply cat_tr_rw with (b := 0). apply cat_tr_nil.
      - apply is_prefix_refl. }
  intro Hincex. cbn in Hincex.
  destruct Hincex as [tr [Hinc Hpre]].
  inversion Hinc; subst; cbn in Hpre.
  - contradiction.
  - destruct Hpre as [Hr Hpre2]. destruct Hpre2 as [Hw _].
    inversion Hr; subst. vm_compute in Hw. discriminate Hw.
Qed.

(** [Equivalence.modeled] is a NEGATIVE statement — [~ bh_unmodeled] — so
    it would be free, and worthless, if [Run.reaches_unmodeled] could
    never hold.  These examples show it can, at both levels: a machine
    state the model declines to interpret, and a whole [run] whose
    [bh_unmodeled] holds and which therefore FAILS the [modeled] clause
    of [Equivalence.strong_equiv].  (Compare
    [Run.reaches_unmodeled_reaches_error] for the other direction: being
    unmodeled is strictly rarer than erroring.)

    The image is a four-byte executable segment holding 0xffffffff, a
    word this development's decoder does not decode. *)
Definition undecodable_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 4;
  seg_perms := "r-x"%string;
  seg_bytes := ["ffffffff"%pstring]
|}.
Definition undecodable_segments : list Segment := [undecodable_segment].

Example undecodable_word_is_not_decoded :
  decode_any (Z_to_bv 32 0xffffffff) = None.
Proof. vm_compute. reflexivity. Qed.

(** A concrete image's program-header record, reused by the auxv checks
    in part 5: the shape [elf-snapshot] emits for a static
    riscv64 binary whose phdr table sits at file offset 64 in the first
    LOAD segment (mapped at 0x10000), with 6 ELF64 program headers. *)
Example undecodable_step_unmodeled :
  RiscvSemantics.step undecodable_segments
    (init_machine_state undecodable_segments 0x100 demo_phdrs
       (Z_to_bv 64 65536) demo_draw [[]] [] demo_uid demo_hwcap)
  = MachineUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** …and therefore the run is NOT modeled.  Any [strong_universal_T]
    naming this image as its source is unprovable, however the target is
    chosen — which is exactly the vacuity the clause exists to block. *)
Example run_of_undecodable_image_is_unmodeled :
  bh_unmodeled (run (mkImage undecodable_segments 0x100 demo_phdrs)
                  demo_limit
                  (mkEntry (Z_to_bv 64 65536) (Z_to_bv 64 1048576)
                     (Z_to_bv 64 mmap_base_max) demo_draw)
                  (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                     default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48)).
Proof.
  cbn [run bh_unmodeled]. unfold init_config.
  apply reaches_unmodeled_intro; [reflexivity | reflexivity |].
  match goal with
  | |- mi_account_step ?segs ?ms ?model = _ =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
  cbn [mkProcInput in_argv in_envp in_uid in_hwcap].
  rewrite undecodable_step_unmodeled. reflexivity.
Qed.

Example run_of_undecodable_image_refutes_modeled :
  ~ Equivalence.modeled
      (run (mkImage undecodable_segments 0x100 demo_phdrs)
         demo_limit
         (mkEntry (Z_to_bv 64 65536) (Z_to_bv 64 1048576)
                     (Z_to_bv 64 mmap_base_max) demo_draw)
         (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                     default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48)).
Proof. intro H. exact (H run_of_undecodable_image_is_unmodeled). Qed.

(** The extracted acceptor's outcomes, read back as [Run.sstep] transitions.
    UNIVERSALLY QUANTIFIED — a [forall] over every input the acceptor can be
    handed, which no finite set of traces establishes.

    [ExecutableSpecs.v] does not import [Run], so nothing it proves can
    mention [sstep]: its theorems reach [syscall_spec] and
    [syscall_post_model], but cannot say that the accounting it applies
    IS the accounting the run performs.  These
    three say it in the one place that can see both.

    What that buys, exactly: they run acceptor-to-run only, so ADDING or
    ALTERING a premise of a syscall [sstep] constructor breaks one of them,
    while DELETING a premise, or adding a laxer constructor, does not.  The
    simulation proofs in [Common/] also break on the first kind; these
    make the break land on a proof naming
    [check_syscall_for_run], so it cannot be repaired by updating the
    simulations while the extracted acceptor keeps the old accounting.

    [SError] carries no reason, so the two error theorems pin the run's
    verdict and not which constructor delivered it -- that is named only in
    their proofs.

    [CheckReject] has no companion.  What it wants is a NEGATIVE statement
    -- a rejected effect admits no syscall [sstep] -- which follows from
    [check_syscall_complete_ok] by inversion and is not written yet. *)
Theorem checker_ok_is_run_step : forall segs ms model x8 eff model'' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall_for_run (sys_input segs ms x8) eff model
    = Some (CheckOk model'' evs) ->
  (m_halted model'' = None /\
   sstep segs (mkCfg ms model) evs
     (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')))
  \/ (exists code,
        m_halted model'' = Some code /\ m_killed model'' = None /\
        sstep segs (mkCfg ms model) (evs ++ [ExitEv code (m_fs model'')])
          (SNext (mkCfg ms model'')))
  \/ (exists sig,
        m_killed model'' = Some sig /\
        sstep segs (mkCfg ms model) (evs ++ [KillEv sig (m_fs model'')])
          (SNext (mkCfg ms model''))).
Proof.
  intros segs ms model x8 eff model'' evs Hh Hsvc Hchk.
  apply check_syscall_for_run_ok_iff in Hchk.
  destruct Hchk as (model' & Hspec & Hpost).
  destruct (m_halted model') as [code|] eqn:Hhalt.
  - rewrite (syscall_post_model_halted _ _ _ Hhalt) in Hpost.
    injection Hpost as Hpost; subst model''.
    destruct (m_killed model') as [sig|] eqn:Hkill.
    + right; right. exists sig. split; [reflexivity|].
      eapply sstep_killed; eassumption.
    + right; left. exists code. split; [exact Hhalt|]. split; [reflexivity|].
      eapply sstep_exit; eassumption.
  - rewrite (syscall_post_model_running _ _ Hhalt) in Hpost.
    pose proof (materialize_model_accesses_frame _ _ _ Hpost) as Hframe.
    destruct Hframe as (_ & _ & _ & _ & _ & Hproc & _).
    left. split.
    + unfold m_halted in *. rewrite Hproc. exact Hhalt.
    + eapply sstep_syscall; eassumption.
Qed.

Theorem checker_fault_is_run_error : forall segs ms model x8 eff,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall_for_run (sys_input segs ms x8) eff model = None ->
  sstep segs (mkCfg ms model) [] SError.
Proof.
  intros segs ms model x8 eff Hh Hsvc Hchk.
  apply check_syscall_for_run_fault_iff in Hchk.
  destruct Hchk as (model' & evs & Hspec & Hhalt & Hfault).
  eapply sstep_syscall_materialization_fault; eassumption.
Qed.

Theorem checker_unmodeled_is_run_error : forall segs ms model x8 eff,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall_for_run (sys_input segs ms x8) eff model = Some CheckUnmodeled ->
  sstep segs (mkCfg ms model) [] SError.
Proof.
  intros segs ms model x8 eff Hh Hsvc Hchk.
  apply check_syscall_for_run_unmodeled_iff in Hchk.
  eapply sstep_syscall_unmodeled; eassumption.
Qed.

(* =========================================================================
   PART 2 — model-level lemmas about the SPECS

   Every statement here is a [forall] over admissible outcomes: it says
   what NO execution may do.  One run exhibits one outcome, so
   it can never establish any of them.
   ========================================================================= *)

(** ** [wait4] must stop answering once something can create a child

    [Kernel.Exit.wait4_spec] answers -ECHILD, and that answer is only
    correct for a caller that has nothing to reap.  Something can create
    a child, so
    these are not vacuous: [Kernel.Fork.clone_resolve]'s success
    branch applies [State.with_children], so a [clone] or [clone3] that
    returns a pid lands in a model with [State.m_has_children] set, and
    the two lemmas below constrain a state a modeled trace really reaches
    rather than quantifying over an empty one.  [Kernel.Fork] pays for
    that here, by setting the field.  Every other arm owes the same — a
    [ptrace] that attaches, or anything else that acquires something to
    reap: apply [State.with_children], or a [wait4_spec] still answering
    -ECHILD stops compiling here.

    Without this, the failure is silent and it is a PRIORITY 2 defect
    rather than a decline: a process that really has a live child would
    get -ECHILD from the model, which Linux never returns for it, while
    the two answers Linux does give (a bare 0 under WNOHANG, or the
    child's pid) would both be rejected.  A model admitting a trace Linux
    cannot produce.

    WHY THESE LIVE HERE AND NOT BESIDE [wait4]'s OTHER LEMMAS.  The rest
    of them are in [Checks.ProcessCreation], which is exactly the file a
    change that gives a number a creating arm has to edit, and such a
    change can delete a guard there as a natural part of making it.  A
    guard the guarded party can remove is not a guard.  Nothing about adding a process-creation arm
    requires touching this file.

    Which of the four reasons at the top of this file: the THIRD, it pins
    model-internal state ([State.m_has_children]) that no observation of
    a real execution reveals — one run reaches the set state
    for one model and one pid, never for every
    model — and the FIRST, a [forall] over every model and every
    argument shape. *)
Lemma wait4_with_a_child_is_unmodeled : forall i eff m,
  bv_unsigned (in_sysno i) = 260%Z ->
  m_has_children m = true ->
  check_syscall i eff m = CheckUnmodeled.
Proof.
  intros i eff m Hno Hch.
  rewrite (check_syscall_wait4 i _ m Hno). unfold check_wait4.
  destruct (negb (Z.eqb (bv_unsigned (pid32 (in_arg i 0))) WAIT_ANY32));
    [reflexivity|].
  destruct (negb (Z.eqb (bv_unsigned (waitopts32 (in_arg i 2))) WNOHANG));
    [reflexivity|].
  destruct (negb (w_is0 (in_arg i 3))); [reflexivity|].
  rewrite Hch. reflexivity.
Qed.

(** ...and the half that names the wrong answer directly: with a child,
    -ECHILD is not merely undecided, it is not admitted at all.  This is
    the one that fails loudly if [wait4_spec]'s gate is dropped while
    something still sets the field. *)
Lemma wait4_with_a_child_admits_no_answer : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 260%Z ->
  m_has_children m = true ->
  ~ syscall_spec i m (Ok eff m' evs).
Proof.
  intros i m eff m' evs Hno Hch H.
  apply check_syscall_complete_ok in H.
  rewrite (wait4_with_a_child_is_unmodeled i eff m Hno Hch) in H.
  discriminate.
Qed.

(** On the first [set_tid_address] call, EVERY environment choice is a
    positive tid inside the modeled envelope.  This is the universal half
    no finite set of runs can establish: Linux returns
    [task_pid_vnr(current)], and [2^22] is the ceiling of both arms of
    [PID_MAX_LIMIT] on a 64-bit kernel, so every configuration and every
    runtime [pid_max] setting lands at or inside it.  The citations and the
    kernel version range they hold over are on [PID_MAX_ENVELOPE] in
    [Specs.v].  The upper bound matters in addition to positivity: a
    positive 64-bit value such as [2^32] truncates to 0 in musl's 32-bit
    tid field and recreates a model-only crash in musl's exit
    lock. *)

(* =========================================================================
   PART 6 — must-terminate: a binary that exits 0, and one that cannot

   [MustExit.must_exit_with] is a statement about the whole run tree —
   EVERY resolution of the nondeterminism halts with the named code,
   none errors, none diverges — so it is admission reason 1 twice over:
   a [forall] over admissible outcomes on the positive side, and the
   negation of one on the refutation side.  One run exhibits a
   single outcome and can establish neither.

   [MustExit] itself proves the predicate's introduction and refutation
   rules against ABSTRACT configurations, which pins what the definition
   means without showing that any image meets it.  Both run-level cases
   are here instead: an image that satisfies it, and one that refutes it.
   The positive one matters most, because the predicate's premises are
   easy to write and hard to meet all at once — a predicate no image
   satisfies would have made every downstream statement about
   classifiers vacuously safe.  The image is about as small as such a
   program gets: three instructions, no memory traffic, ending in
   exit(0).
   ========================================================================= *)

(** ** Reading the exit syscall back out of the relational spec

    This sub-part is proof INFRASTRUCTURE rather than examples: five
    lemmas over one definition, inverting [Specs.syscall_spec] at the
    exit syscall number.  An image-level termination proof needs them and
    no earlier statement in this file does.

    [Common/ExitSim.v] proves the same facts for the example binaries,
    and this file cannot use them: [Common] is a separate theory built ON
    TOP of [LinuxProcessSemantics], so the dependency would run
    backwards.  Keeping the duplicate small is the mitigation — all five
    are consequences of [Exit.exit_spec] having exactly one outcome
    shape.

    They are also deliberately named APART from their [Common/ExitSim.v]
    counterparts, none reusing a name from there.  Two identical
    statements under one name in two theories is how a divergence hides:
    a file that imported both would get last-import-wins shadowing with
    nothing to notice if one copy were later edited, and the shadowing
    would be silent precisely while the two agree. *)

(** The syscall numbers that route to [Exit.exit_spec]: exit (93) and
    exit_group (94), which the dispatcher gives the same spec. *)
Definition exit_sysno (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

(** At either number the dispatcher IS the exit spec.  The whole of
    [Dispatch.dispatch] at a known number is a table lookup that reduces,
    so both directions are one rewrite. *)
Lemma exit_dispatch_iff : forall i m o,
  exit_sysno (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
  intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

(** The exit spec admits an outcome — the run is not stuck at the ecall.
    [Run.sstep_exit] needs this to fire. *)
Lemma exit_dispatch_admits : forall i m,
  exit_sysno (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
  intros i m Hno. apply (proj2 (exit_dispatch_iff i m _ Hno)).
  unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
  eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
    [], []. repeat split; reflexivity.
Qed.

(** ... and admits NO OTHER.  This is the uniqueness that turns "some
    execution exits 0" into "every execution does": the exit spec is a
    [set_halted] followed by a return, with no [choose] anywhere, so the
    post-model, the effect and the event list are all forced. *)
Lemma exit_dispatch_forced : forall i m eff m' evs,
  exit_sysno (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
  intros i m eff m' evs Hno Hspec.
  apply (proj1 (exit_dispatch_iff i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.

(** The consequence the run tree cares about: every admissible exit
    outcome HALTS, with the low byte of the status as
    [Sys/Kernel/Exit.v] masks it.  It is what rules out
    [Run.sstep_syscall] and [Run.sstep_syscall_materialization_fault] at
    an exit ecall — both require a post-model that is still running. *)
(** The same, for the OTHER terminal field: an exit's post-model is
    [State.with_halted]'s, so it is not a killed one — which is what
    keeps [Run.sstep_exit] and [Run.sstep_killed] apart at an [exit]
    ecall. *)
Lemma exit_dispatch_not_killed : forall i m eff m' evs,
  exit_sysno (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  m_killed m' = None.
Proof.
  intros i m eff m' evs Hno Hspec.
  destruct (exit_dispatch_forced _ _ _ _ _ Hno Hspec) as (_ & -> & _).
  apply m_killed_with_halted.
Qed.

Lemma exit_dispatch_halts : forall i m eff m' evs,
  exit_sysno (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  m_halted m' = Some (bv_and (in_arg i 0) (Z_to_bv 64 255)).
Proof.
  intros i m eff m' evs Hno Hspec.
  destruct (exit_dispatch_forced _ _ _ _ _ Hno Hspec) as (_ & -> & _).
  apply m_halted_with_halted.
Qed.

(** Exit is inside the modeled surface, so [Run.sstep_syscall_unmodeled]
    cannot fire at it either.  With the two above this closes every
    error route out of an exit ecall. *)
Lemma exit_dispatch_modeled : forall i m,
  exit_sysno (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hspec.
  apply (proj1 (exit_dispatch_iff i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct.
Qed.

(** [Run.sstep]'s syscall constructors each bind their own name for the
    pending syscall number, and inversion introduces it fresh; this
    identifies it with the one the surrounding proof already has.  Every
    such name is equal to it — they all come from the same
    [RiscvSemantics.ms_svc_pending] — but nothing in the goal says so
    until this runs. *)
Ltac unify_svc x8 :=
  repeat match goal with
  | [ H : ms_svc_pending ?m = Some ?y, H2 : ms_svc_pending ?m = Some x8 |- _ ] =>
      first [ constr_eq y x8; fail 1
            | let E := fresh "Esvc" in
              assert (E : y = x8) by congruence; subst y ]
  end.

(** ** A fuel-bounded executable witness for [MustExit.must_exit_at]

    A straight-line binary that ends in exit is checked by RUNNING it:
    [exits_c] walks [RiscvSemantics.step] until a syscall is pending, and
    then asks whether it is an exit carrying the right code.  Written as
    a [bool] on purpose — the machine states it passes through stay
    inside the computation, so [vm_compute] never has to build one as a
    term.  (Reducing a successor machine state INTO a goal costs about a
    minute per image here, since the state carries memory as a closure;
    reducing this function to [true] costs milliseconds.)

    This is the same shape as [Common/ExitSim.v]'s [sim_c], for the same
    reason, landing on a different predicate. *)
Fixpoint exits_c (segs : list Segment) (code : word) (fuel : nat)
    (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match ms_svc_pending ms with
      | Some x8 =>
          ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
          && bv_eqb (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) code
      | None =>
          match RiscvSemantics.step segs ms with
          | MachineOk ms' => exits_c segs code fuel' ms'
          | MachineFault | MachineUnmodeled => false
          end
      end
  end.

(** [exits_c] is sound for [MustExit.must_exit_at]: a program it accepts
    really has NO other execution.  Both premises on the model are needed
    and both are discharged by [reflexivity] at an initial configuration:
    a halted model would put the configuration in the base case with
    whatever code it already carries, and a model with lazy anonymous
    mappings could take the accounting fault transition
    ([Run.mi_account_step_no_lazy] is what erases accounting here, and it
    is also what keeps the model FIXED across an instruction step, so the
    induction hypothesis applies unchanged).

    The two [Run.sstep] error premises of
    [MustExit.must_exit_at_running] are where the work is.  At an
    instruction they follow from [Run.mi_account_step] being a function
    that answered [MachineOk]; at the ecall they are the exit-dispatch
    lemmas above. *)
Lemma exits_c_must_exit_at : forall segs code fuel ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  exits_c segs code fuel ms = true ->
  must_exit_at segs code (mkCfg ms model).
Proof.
  intros segs code fuel. induction fuel as [|fuel IH]; intros ms model Hh Hlazy Hc;
    [discriminate|].
  cbn [exits_c] in Hc.
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - (* the terminating ecall *)
    apply andb_true_iff in Hc as [Hx8 Hcode].
    apply bv_eqb_eq in Hcode.
    assert (Hno : exit_sysno (in_sysno (sys_input segs ms x8))).
    { cbn [in_sysno sys_input].
      apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
        [left|right]; exact H. }
    assert (Harg : in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0) by reflexivity.
    set (m' := with_halted (bv_and (in_arg (sys_input segs ms x8) 0)
                                   (Z_to_bv 64 255)) model).
    apply must_exit_at_running.
    + cbn [cfg_model]. exact Hh.
    + exists ([] ++ [ExitEv (bv_and (in_arg (sys_input segs ms x8) 0)
                                    (Z_to_bv 64 255)) (m_fs m')]),
        (SNext (mkCfg ms m')).
      eapply sstep_exit; [exact Hh | exact Hsvc | | | ].
      * subst m'. exact (exit_dispatch_admits _ model Hno).
      * subst m'. reflexivity.
      * subst m'. apply m_killed_with_halted.
    + intros evs Hss. inversion Hss; subst; try congruence; unify_svc x8.
      * (* materialization fault: an exit outcome halts, so its premise fails *)
        match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        congruence.
      * (* unmodeled syscall: exit is modeled *)
        match goal with
        | [ H : syscall_spec _ _ Unmodeled |- _ ] =>
            exact (exit_dispatch_modeled _ _ Hno H)
        end.
    + intros evs c' Hss. inversion Hss; subst; try congruence; unify_svc x8.
      * (* an ordinary syscall step: its post-model would have to run on *)
        match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        congruence.
      * (* the exit transition, into the halted configuration *)
        match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        apply must_exit_at_halted; cbn [cfg_model].
        -- rewrite Hhalts, Harg. reflexivity.
        -- match goal with
           | [ H : m_killed ?m' = None |- m_killed ?m' = None ] => exact H
           end.
      * (* the kill transition: an exit's post-model is not a killed one *)
        exfalso.
        match goal with
        | [ H : syscall_spec _ _ (Ok _ ?m' _), Hk : m_killed ?m' = Some _ |- _ ] =>
            rewrite (exit_dispatch_not_killed _ _ _ _ _ Hno H) in Hk;
            discriminate
        end.
  - (* an ordinary instruction *)
    destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [|discriminate|discriminate].
    assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
    { rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity. }
    apply must_exit_at_running.
    + cbn [cfg_model]. exact Hh.
    + exists [], (SNext (mkCfg ms' model)).
      eapply sstep_instr; eassumption.
    + intros evs Hss. inversion Hss; subst; congruence.
    + intros evs c' Hss. inversion Hss; subst; try congruence.
      match goal with
      | [ H : mi_account_step _ _ _ = MachineOk (?a, ?b) |- _ ] =>
          rewrite Hacc in H; injection H as -> ->
      end.
      apply IH; assumption.
Qed.

(** ** The image, and the entry a real [execve] could have chosen

    Three instructions at 0x100, written out as the hex the loader would
    have produced: [addi a7, x0, 93] (0x05d00893), [addi a0, x0, 0]
    (0x00000513), [ecall] (0x00000073), little-endian.  The program makes
    no memory access at all beyond its own instruction fetches, which is
    what keeps the statements below short: nothing depends on the stack
    the entry describes, though they are still proved at one concrete
    entry rather than quantified over them. *)
Definition exit0_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 12;
  seg_perms := "r-x"%string;
  seg_bytes := ["9308d0051305000073000000"%pstring]
|}.
Definition exit0_segments : list Segment := [exit0_segment].
Definition exit0_image : Image := mkImage exit0_segments 0x100 demo_phdrs.

(** The undecodable image from part 1, as an [MemImageType.Image]: the
    same [undecodable_segments] those examples run. *)
Definition undecodable_image : Image :=
  mkImage undecodable_segments 0x100 demo_phdrs.

(** An [execve] placement that really satisfies [Run.valid_entry] —
    unlike the fixture entry used by the earlier examples, whose stack
    pointer (65536) sits far below [State.sp_window_lo] and which those
    examples never had to validate.  Validity is what the statements
    below need: [Classifier.agree] quantifies its trace comparison over
    VALID entries only, so a refutation that named an invalid one would
    refute nothing. *)
Definition demo_entry : ExecEntry :=
  mkEntry (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000)
          (Z_to_bv 64 mmap_base_max) demo_draw.

(** Both images put their only segment inside the first page, so both
    reserve exactly that page and the same break base is valid for
    either.  These two are premises for the statements below rather than
    cases in their own right; as cases they would be admission reason 3,
    since the three windows [Run.valid_entry] checks against are model
    constants no observation of a running process reveals.

    Stated for EVERY valid input rather than at the one below, because
    that is what is true: [Run.valid_entry]'s fourth conjunct asks that
    the entry stack image fit under [State.sp_window_hi], [demo_entry]
    puts [sp] at [State.sp_window_lo], and [Run.entry_stack_span_bound]
    caps a valid input's image at [Run.entry_stack_span_max] — 2238671
    bytes against the window's two gigabytes.  Naming the input here
    instead would say less and would have to be restated at each use. *)
Example demo_entry_valid_exit0 : forall inp,
  valid_input inp -> valid_entry exit0_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [exit0_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

Example demo_entry_valid_undecodable : forall inp,
  valid_input inp -> valid_entry undecodable_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [undecodable_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

(** [Run.valid_mmap_base]'s cap, pinned from outside (reason 3: the band
    is a model constant no trace reveals).  [State.mmap_base_max] is the
    base a v6.18.46 kernel computes with randomisation off — [STACK_TOP -
    MIN_GAP], mm/util.c [mmap_base] — and one page above it no kernel
    computes.  The third value is the top of the default 18-bit band
    (8 MiB rlimit, [PF_RANDOMIZE]); it is an ordinary real-kernel
    draw, so the band must admit it. *)
Example mmap_base_cap_admitted : valid_mmap_base (Z_to_bv 64 0x7ffff8000000).
Proof.
  unfold valid_mmap_base, mmap_base_min, mmap_base_max, sp_window_hi, page_size.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  repeat split; try lia; vm_compute; reflexivity.
Qed.

Example mmap_base_above_cap_rejected :
  ~ valid_mmap_base (Z_to_bv 64 (0x7ffff8000000 + 4096)).
Proof.
  unfold valid_mmap_base, mmap_base_min, mmap_base_max, sp_window_hi, page_size.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  intros (_ & H & _). lia.
Qed.

Example mmap_base_default_band_top_admitted :
  valid_mmap_base (Z_to_bv 64 0x7fffbf701000).
Proof.
  unfold valid_mmap_base, mmap_base_min, mmap_base_max, sp_window_hi, page_size.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  repeat split; try lia; vm_compute; reflexivity.
Qed.

(** The process input the statements below run on is a valid one — one
    empty argument, no environment, an empty file system, end of input.
    Needed for the same reason the entry validity is: the obligations
    quantify over VALID inputs, so a refutation naming an invalid one
    would refute nothing. *)
Example demo_input_valid :
  valid_input
    (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48).
Proof.
  unfold valid_input, valid_argv, valid_envp.
  cbn [mkProcInput in_argv in_envp in_fs].
  (* [Run.valid_nofile] is discharged FIRST and by a guarded tactic of
     its own, because the generic chain below destroys it: [Z.le] unfolds
     to a negation, so [intros []] strips the comparison and leaves a bare
     [False] that nothing can close.  The [unfold] is what keeps this arm
     off the other conjuncts -- it fails, and the [try] moves on, wherever
     [valid_nofile] does not occur.
     [State.default_nofile] is INR_OPEN_CUR (1024), far under the
     2^31 - 64 ceiling do_prlimit enforces through sysctl_nr_open, and
     the comparison is decided as a boolean because [vm_compute] does not
     leave [bv_unsigned] as a literal [lia] can read.

     [Run.valid_sigmask] takes an arm of the same shape and for the same
     reason -- guarded by its own [unfold] so it is skipped wherever
     [valid_sigmask] does not occur.  It is already an EQUALITY
     rather than a comparison, so it needs no [Z.leb_le] step -- but it
     DOES need [bv_eq], and that is the part worth writing down: the two
     sides are equal masks, and [vm_compute] alone leaves them as
     bitvector records whose well-formedness proofs are built
     differently, which [reflexivity] will not close.  [bv_eq] reduces
     the goal to the underlying integers first.  It is the same reason
     [Cases.Prelude.check_eq] exists.

     [Run.valid_hwcap] is the only DISJUNCTION in [valid_input], so its
     arm picks a side rather than deciding a comparison:
     [Cases.Prelude.demo_hwcap] is [hwcap_rv64gc], the left one.  Which side is chosen is not arbitrary and not the
     model's preference — see the AT_HWCAP note in [StackLayout] for
     why both masks are admitted and
     [Cases.Prelude.demo_hwcap] for why the fixtures take this one. *)
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  (* [Run.valid_urandom], the eighth, is the only COINDUCTIVE conjunct,
     so no computation decides it and the fixture discharges it by
     naming the witness its declaration is: [State.default_urandom],
     which is what [State.mkProcInput] fills the field with. *)
  all: try valid_urandom_default.
Qed.

(** THE RANDOM-STREAM CLAUSE, FIRED IN BOTH DIRECTIONS.  Admission
    reason 2: the clause is on the
    LAUNCH's declaration, and one run declares one stream.

    THE POSITIVE HALF says the fixture above really carries the clause
    rather than passing it by accident: [State.mkProcInput] fills
    [State.in_urandom] with [State.default_urandom], which is endless.
    THE NEGATIVE HALF is the point of the clause: the SAME launch with
    [State.IEof] in that field is not a valid input at all.  That is
    exactly what the clause excludes — the declaration under which
    [Sys.Fs.ReadWrite.read_urandom] declines, which
    [Checks.Cases.Fs.Open.urandom_stream_runs_out] keeps as a literal.
    Without the negative half the clause could be satisfied by every
    input and nothing would notice. *)
Example the_random_clause_is_what_the_fixture_carries :
  valid_urandom
    (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                 default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48)
  /\ ~ valid_input
        (mkProcInput_full [[]] [] [] IEof demo_uid demo_gid demo_groups
                          net_silent default_nofile (Z_to_bv 64 0) demo_hwcap
                          false Sv48 IEof []).
Proof.
  split.
  - valid_urandom_default.
  - intro H. exact (State.stream_infinite_not_eof (valid_input_urandom _ H)).
Qed.

(** ** The two witnesses

    UNIVERSALLY QUANTIFIED (admission reason 1): every execution of this
    image from this entry halts with exit code 0, which is a claim about
    the whole run tree.  It is the first place a concrete image SATISFIES
    [MustExit.must_exit_with]: up to here the predicate had refutations
    and introduction rules stated of abstract configurations, and a
    predicate nothing satisfies would have made every one of those
    refutations free. *)
Example exit0_image_must_exit_zero :
  must_exit_with verdict_accept exit0_image demo_limit demo_entry
    (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48).
Proof.
  cbn [must_exit_with exit0_image demo_entry]. unfold init_config.
  apply (exits_c_must_exit_at _ _ 8); [reflexivity | reflexivity |].
  vm_compute. reflexivity.
Qed.

(** ... and the other side.  UNIVERSALLY QUANTIFIED (reason 1) again, as
    the negation of one: the undecodable image errors on its first fetch,
    and [MustExit.must_exit_with] forbids an error anywhere in the tree,
    at every code — so this refutes exit 0 and exit 1 alike.  The route
    is the one [MustExit.must_exit_with_refuted_by_error] was written
    for, through [Equivalence.run_unmodeled_errors]: leaving the modeled
    surface is a special case of erroring. *)
Example undecodable_image_refutes_must_exit :
  ~ must_exit_with verdict_accept undecodable_image demo_limit
      (mkEntry (Z_to_bv 64 65536) (Z_to_bv 64 1048576)
         (Z_to_bv 64 mmap_base_max) demo_draw)
      (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48).
Proof.
  apply must_exit_with_refuted_by_error, run_unmodeled_errors,
    run_of_undecodable_image_is_unmodeled.
Qed.

(** ** Two runs that do not agree

    COMPARES TWO RUNS (admission reason 2): [Classifier.agree] is a
    statement about a pair of trace sets, and the acceptor folds over
    one trace per run.

    The refutation goes through the trace conjunct rather than through
    the three error iffs, and that is not an accident: refuting an
    existential-over-entries iff needs a claim about EVERY valid entry of
    one image, while the trace conjunct is universally quantified over
    entry pairs and so one valid pair refutes it.  Here the pair is
    [demo_entry] against itself. *)

(** The undecodable image is unmodeled on its first fetch at
    [demo_entry] too, exactly as [undecodable_step_unmodeled] shows at
    the older fixture entry: the fetch reads the segment image, which
    none of the three [execve] placements touches. *)
Example undecodable_step_unmodeled_at_demo_entry :
  RiscvSemantics.step undecodable_segments
    (init_machine_state undecodable_segments 0x100 demo_phdrs
       (Z_to_bv 64 0x7fff80000000) demo_draw [[]] [] demo_uid demo_hwcap)
  = MachineUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** A configuration the model declines to interpret has no successor at
    all: [Run.sstep_instr] needs [Run.mi_account_step] to have answered
    [MachineOk], and every syscall constructor needs a pending syscall
    number. *)
Lemma unmodeled_no_next : forall segs ms model evs c',
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineUnmodeled ->
  ~ sstep segs (mkCfg ms model) evs (SNext c').
Proof.
  intros segs ms model evs c' Hsvc Hacc Hss.
  inversion Hss; subst; congruence.
Qed.

(** ... and therefore emits nothing: the only [Run.star] from it is the
    empty one, so its whole trace set is the empty trace.  This is the
    negative half the trace comparison needs, and it is not available
    from [Run.reaches_error] — erroring says the run CAN fault, not that
    it emitted nothing on the way. *)
Lemma no_next_obs_trace_nil : forall segs c0 tr,
  (forall evs c', ~ sstep segs c0 evs (SNext c')) ->
  obs_trace segs c0 tr ->
  tr = [].
Proof.
  intros segs c0 tr Hno (tr' & c & Hstar & Hp).
  inversion Hstar; subst.
  - destruct tr as [|e tr]; [reflexivity | destruct Hp].
  - exfalso. eapply Hno; eassumption.
Qed.

(** This one is UNIVERSALLY QUANTIFIED (admission reason 1) rather than
    a two-run comparison like the banner above it: it quantifies over one
    run's whole trace set, which no fold of one observed trace can
    establish.  It is the half of the comparison that says what the
    undecodable image does NOT emit. *)
Example undecodable_image_emits_nothing : forall tr,
  bh_traces (run undecodable_image demo_limit demo_entry
               (mkProcInput [[]] [] [] IEof
                  demo_uid demo_gid demo_groups net_silent default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48)) tr ->
  tr = [].
Proof.
  intros tr Htr.
  cbn [run bh_traces undecodable_image demo_entry] in Htr.
  eapply no_next_obs_trace_nil; [|exact Htr].
  intros evs c'. unfold init_config.
  apply unmodeled_no_next; [reflexivity|].
  match goal with
  | |- mi_account_step ?segs ?ms ?model = _ =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
  cbn [mkProcInput in_argv in_envp in_uid in_hwcap].
  rewrite undecodable_step_unmodeled_at_demo_entry. reflexivity.
Qed.

(** The exit-0 image and the undecodable image do not agree on this
    input: one of them has a trace ending in [State.ExitEv], and the
    other has no trace but the empty one.  The
    [MustExit.must_exit_with_realizes]
    step is what turns "must exit 0" into an observable event — without
    it, must-termination and trace equality would be statements about
    different things. *)
Example exit0_disagrees_with_undecodable :
  ~ agree exit0_image undecodable_image demo_limit
      (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48).
Proof.
  intros (Htraces & _).
  destruct (must_exit_with_realizes _ _ _ _ _ exit0_image_must_exit_zero)
    as (tr & fs & Hexit).
  apply (proj1 (Htraces demo_entry demo_entry
                  (demo_entry_valid_exit0 _ demo_input_valid)
                  (demo_entry_valid_undecodable _ demo_input_valid)
                  (tr ++ [ExitEv verdict_accept fs]))) in Hexit.
  apply undecodable_image_emits_nothing in Hexit.
  destruct tr; discriminate.
Qed.

(** ** The error-free obligation, refuted at run level

    UNIVERSALLY QUANTIFIED (admission reason 1), as the negation of one:
    [Equivalence.strong_universal_error_free_T] says no execution of either
    binary faults, on any valid input at any valid entry, and one
    faulting execution at one valid triple is enough to refute it.  The
    image is compared against ITSELF, which the error-free shape does not
    make free — unlike [Equivalence.equiv], which an all-erroring source
    satisfies against any target, this shape is refuted BY the error
    ([Equivalence.strong_equiv_error_free_no_all_errors_escape] is the
    definition-level form).

    This is the witness [Equivalence]'s non-vacuity comment on the
    error-free shape points at.  It needs the
    same fetch fact at the ASLR-valid entry, this time at
    [State.source_alloc_limit] rather than [demo_limit] — the budget the
    error-free obligation seeds the source run with. *)
Example run_of_undecodable_image_is_unmodeled_at_demo_entry :
  bh_unmodeled (run undecodable_image source_alloc_limit demo_entry
                  (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48)).
Proof.
  cbn [run bh_unmodeled undecodable_image demo_entry]. unfold init_config.
  apply reaches_unmodeled_intro; [reflexivity | reflexivity |].
  match goal with
  | |- mi_account_step ?segs ?ms ?model = _ =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
  cbn [mkProcInput in_argv in_envp in_uid in_hwcap].
  rewrite undecodable_step_unmodeled_at_demo_entry. reflexivity.
Qed.

(** The abort-declared twin of this one is
    [Checks.AbortWitness.abrt_refutes_error_free_abort], and it is a
    separate file only because it needs [Checks.Omni]'s stepping
    helpers, which are downstream of this one.  The two are worth
    reading together: this refutation goes through the ERROR conjunct
    (the image is unmodeled on its first fetch), and that one through
    the KILLED conjunct [Equivalence.error_free_unkilled] adds, on an
    image the model follows to the end without erroring once. *)
Example undecodable_image_refutes_error_free_equivalence :
  ~ strong_universal_error_free_T undecodable_image undecodable_image.
Proof.
  apply (strong_universal_error_free_refuted_by_source_error
           undecodable_image undecodable_image demo_entry demo_entry
           (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48)
           (demo_entry_valid_undecodable _ demo_input_valid)
           (demo_entry_valid_undecodable _ demo_input_valid)
           demo_input_valid).
  apply run_unmodeled_errors,
    run_of_undecodable_image_is_unmodeled_at_demo_entry.
Qed.
