(** * LinuxProcessSem.Checks.ExecutableSpecs — verified executable acceptors for each syscall

    Representation: syscall inputs/returns are [word = bv 64],
    buffer bytes are [byte = bv 8], errnos are [Z], and length/bound
    comparisons happen in [Z] over unsigned values, mirroring Specs.v
    exactly.  [bytes_ok] / [Forall (b < 256)] checker conditions are
    unnecessary — they are enforced by the [byte] type.

    The relational specs in Specs.v are the TRUSTED semantics; they are
    not executable (non-determinism is set-valued).  For conformance
    testing against real Linux we need a runnable acceptor: given the
    syscall's input, the OBSERVED effect (return value + captured output
    buffers), and the model
    state, decide whether the observation is admissible.

    [check_syscall] decides the syscall body and returns:
    - [CheckOk m' evs] — admissible; the model steps to [m'] emitting [evs];
    - [CheckUnmodeled]       — the spec relation says [Unmodeled] (unmodeled syscall
                         number / unmodeled use of a modeled syscall /
                         invalid user buffer); independent of the observed
                         effect;
    - [CheckReject]    — the observed effect is NOT admissible: the real
                         kernel did something the model forbids (a
                         conformance failure).

    VERIFICATION (below): the checker is proved sound AND complete
    against the relational specs —
      [check_syscall i eff m = CheckOk m' evs  <->  syscall_spec i m (Ok eff m' evs)]
      [check_syscall i eff m = CheckUnmodeled        <->  syscall_spec i m Unmodeled]
    so [CheckReject] means exactly "no admissible outcome has this effect".

    The public entry point [check_syscall_for_run] then applies the
    same atomic first-touch accounting as [Run.sstep_syscall] to a successful
    post-model.  Its OUTER [None] is the modeled error transition for a
    backing-limit failure, kept distinct from both checker rejection and
    unmodeled behavior.  That "same as [Run.sstep_syscall]" cannot be a
    theorem HERE — this file does not import [Run] — so [Checks/Examples.v]
    proves it, reading each outcome back as the transition it stands for.
    These proofs are QA on the checker, not part of the trust story: the spec
    stays the definition. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Dispatch
  Prelude Uaccess Fs.DPath Fs.File Fs.ReadWrite Fs.Open Fs.Sync Fs.Stat Fs.Select
  Fs.Ioctl Fs.Fcntl Fs.Locks Fs.Namei Fs.Readdir Fs.Timerfd Fs.Pipe
  Fs.EventPoll Fs.EventFd Fs.Signalfd Mm.Mmap Mm.Mremap Mm.Mprotect Mm.Madvise Kernel.Exit
  Kernel.Capability
  Kernel.Fork Kernel.Futex.Syscalls Kernel.Groups
  Kernel.Sched.Syscalls Kernel.Signal Kernel.Sys
  Kernel.Time.Hrtimer Kernel.Time.PosixTimers Kernel.Time.Time
  Net.Socket
  Drivers.Char.Random.

(** Dispatch on the syscall number, through the one table the relational
    spec dispatches over as well.  The two cannot disagree about which
    numbers are modeled, because they read the same list. *)
Definition check_syscall (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match lookup_ca checked_table (bv_unsigned (in_sysno i)) with
  | Some c => ca_check c i eff m
  | None   => CheckUnmodeled
  end.

(** Postprocess the relational syscall post-model exactly as the run does.
    A halted model is [Run.sstep_exit] and stays unchanged.  A running model
    is one of [Run.sstep_syscall]/[Run.sstep_syscall_materialization_fault],
    decided by the same shared access aggregation and atomic materializer. *)
Definition syscall_post_model (m : Model) (eff : SyscallEffect)
    : option Model :=
  match m_halted m with
  | Some _ => Some m
  | None => materialize_model_accesses m (syscall_effect_accesses eff)
  end.

(** Public conformance-checker boundary.  The outer option is the run's
    error-transition boundary: [None] exposes no partially updated model and
    is deliberately not conflated with either [CheckReject] or
    [CheckUnmodeled]. *)
Definition check_syscall_for_run (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : option check_result :=
  match check_syscall i eff m with
  | CheckOk m' evs =>
      match syscall_post_model m' eff with
      | Some m'' => Some (CheckOk m'' evs)
      | None => None
      end
  | CheckReject => Some CheckReject
  | CheckUnmodeled => Some CheckUnmodeled
  end.

(* =========================================================================
   Verification: the checker is sound and complete for the relational specs
   ========================================================================= *)

(* --------------------------------------------------------- prlimit64 *)

(** [lookup_ca_arm] is what lets a goal about [Specs.syscall_spec] -- which
    dispatches over [spec_table] -- be closed by a [CheckedArm]'s field: the
    two tables are the same surface ([checked_table_arms]).  Both sides of
    every theorem below therefore turn on the SAME lookup, so each one is a
    destruct and a field.

    None of the four mentions a syscall, and none of them grows when one is
    added. *)

Theorem check_syscall_sound_ok : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs ->
  syscall_spec i m (Ok eff m' evs).
Proof.
  intros i eff m m' evs H. unfold check_syscall in H.
  unfold syscall_spec, dispatch.
  rewrite <- checked_table_arms, lookup_ca_arm.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    cbn [option_map]; [ apply (ca_sound_ok c), H | discriminate H ].
Qed.

Theorem check_syscall_sound_unmodeled : forall i eff m,
  check_syscall i eff m = CheckUnmodeled -> syscall_spec i m Unmodeled.
Proof.
  intros i eff m H. unfold check_syscall in H.
  unfold syscall_spec, dispatch.
  rewrite <- checked_table_arms, lookup_ca_arm.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    cbn [option_map];
    [ apply (ca_sound_unmodeled c) with (eff := eff), H | apply unmodeled_intro ].
Qed.

Theorem check_syscall_complete_ok : forall i eff m m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  check_syscall i eff m = CheckOk m' evs.
Proof.
  intros i eff m m' evs H. unfold syscall_spec, dispatch in H.
  rewrite <- checked_table_arms, lookup_ca_arm in H.
  unfold check_syscall.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    cbn [option_map] in H; [ apply (ca_complete_ok c), H | discriminate H ].
Qed.

Theorem check_syscall_complete_unmodeled : forall i m eff,
  syscall_spec i m Unmodeled -> check_syscall i eff m = CheckUnmodeled.
Proof.
  intros i m eff H. unfold syscall_spec, dispatch in H.
  rewrite <- checked_table_arms, lookup_ca_arm in H.
  unfold check_syscall.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    cbn [option_map] in H; [ apply (ca_complete_unmodeled c), H | reflexivity ].
Qed.

Theorem check_syscall_ok_iff : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs <-> syscall_spec i m (Ok eff m' evs).
Proof.
  split; [apply check_syscall_sound_ok | apply check_syscall_complete_ok].
Qed.

Theorem check_syscall_err_iff : forall i eff m,
  check_syscall i eff m = CheckUnmodeled <-> syscall_spec i m Unmodeled.
Proof.
  split; [apply check_syscall_sound_unmodeled | intro H; now eapply check_syscall_complete_unmodeled].
Qed.

(* =========================================================================
   Verification: the public checker, against the relational spec

   These four cover [option check_result] exhaustively.  They are stated
   against [syscall_spec] and [syscall_post_model] rather than against
   [Run.sstep], because this file does not import [Run];
   [Checks.Examples.checker_ok_is_run_step] and its two companions close
   that last step.
   ========================================================================= *)

Lemma syscall_post_model_running : forall m eff,
  m_halted m = None ->
  syscall_post_model m eff =
    materialize_model_accesses m (syscall_effect_accesses eff).
Proof. intros m eff H. unfold syscall_post_model. rewrite H. reflexivity. Qed.

Lemma syscall_post_model_halted : forall m eff code,
  m_halted m = Some code -> syscall_post_model m eff = Some m.
Proof. intros m eff code H. unfold syscall_post_model. rewrite H. reflexivity. Qed.

(** A public-checker success contains exactly a relational syscall outcome
    followed by the post-model premise shared with the run constructors. *)
Theorem check_syscall_for_run_ok_iff : forall i eff m m'' evs,
  check_syscall_for_run i eff m = Some (CheckOk m'' evs) <->
  exists m',
    syscall_spec i m (Ok eff m' evs) /\
    syscall_post_model m' eff = Some m''.
Proof.
  intros i eff m m'' evs. split.
  - unfold check_syscall_for_run.
    destruct (check_syscall i eff m) as [m' evs'| |] eqn:Hcheck;
      try discriminate.
    destruct (syscall_post_model m' eff)
      as [accounted|] eqn:Haccount; [|discriminate].
    intro H. inversion H; subst.
    exists m'. split; [now apply check_syscall_sound_ok in Hcheck | exact Haccount].
  - intros (m' & Hspec & Haccount).
    unfold check_syscall_for_run.
    rewrite (check_syscall_complete_ok _ _ _ _ _ Hspec), Haccount.
    reflexivity.
Qed.

(** The outer [None] is exactly the non-halting materialization-fault premise
    of [Run.sstep_syscall_materialization_fault]. *)
Theorem check_syscall_for_run_fault_iff : forall i eff m,
  check_syscall_for_run i eff m = None <->
  exists m' evs,
    syscall_spec i m (Ok eff m' evs) /\
    m_halted m' = None /\
    materialize_model_accesses m' (syscall_effect_accesses eff) = None.
Proof.
  intros i eff m. split.
  - unfold check_syscall_for_run.
    destruct (check_syscall i eff m) as [m' evs| |] eqn:Hcheck;
      try discriminate.
    destruct (syscall_post_model m' eff) as [accounted|] eqn:Hpost;
      [discriminate|].
    intro Hnone. exists m', evs. split.
    + now apply check_syscall_sound_ok in Hcheck.
    + unfold syscall_post_model in Hpost.
      destruct (m_halted m') as [code|] eqn:Hhalt; [discriminate|].
      split; [reflexivity | exact Hpost].
  - intros (m' & evs & Hspec & Hhalt & Hmaterialize).
    unfold check_syscall_for_run.
    rewrite (check_syscall_complete_ok _ _ _ _ _ Hspec).
    unfold syscall_post_model. rewrite Hhalt, Hmaterialize. reflexivity.
Qed.

(** Raw rejection stays raw rejection; accounting faults use the outer
    [None] and cannot reach this result. *)
Theorem check_syscall_for_run_reject_iff : forall i eff m,
  check_syscall_for_run i eff m = Some CheckReject <->
  check_syscall i eff m = CheckReject.
Proof.
  intros i eff m. unfold check_syscall_for_run.
  destruct (check_syscall i eff m) as [m' evs| |] eqn:Hcheck.
  - destruct (syscall_post_model m' eff); split; intro H; discriminate.
  - tauto.
  - split; intro H; discriminate.
Qed.

(** Fail-closed syscall outcomes pass through the run adapter unchanged. *)
Theorem check_syscall_for_run_unmodeled_iff : forall i eff m,
  check_syscall_for_run i eff m = Some CheckUnmodeled <->
  syscall_spec i m Unmodeled.
Proof.
  intros i eff m. split.
  - intro H. unfold check_syscall_for_run in H.
    destruct (check_syscall i eff m) as [m' evs| |] eqn:Hcheck.
    + destruct (syscall_post_model m' eff);
        discriminate.
    + discriminate.
    + now apply check_syscall_sound_unmodeled in Hcheck.
  - intro Hspec. unfold check_syscall_for_run.
    rewrite (check_syscall_complete_unmodeled i m eff Hspec). reflexivity.
Qed.
