(** * LinuxProcessSem.Checks.Cases.Fs.SigpipeLaunch — the readerless pipe write, on launches proved valid

    THE PAIR THE PIN-THE-TOP CHANGE TURNS ON, and a third case beside it.
    Each starts from the model [State.init_model] builds for a LAUNCH, and
    each launch is proved to satisfy the predicate it is named for, by
    [Qed], before anything is run on it:

    - [ordinary_launch] satisfies [Run.valid_input]
      ([ordinary_launch_valid]);
    - [kills_launch] satisfies [Run.valid_input_sigpipe_kills]
      ([kills_launch_valid]), and differs from [ordinary_launch] only in
      the SIGPIPE-death declaration, [State.in_sigpipe_terminal];
    - [blocked_launch] satisfies [Run.valid_input] too
      ([blocked_launch_valid]), and differs from [ordinary_launch] only in
      its signal mask, which blocks SIGPIPE.

    On each the program makes a pipe with [pipe2], closes the read end
    with [close], and writes two bytes to the write end -- a pipe the
    program made and left with no reader, the case that killed under
    [Run.valid_input] at revision/all-fixes.  [after_close] runs the first
    two calls through [check_syscall] and hands back the model they reach;
    each example then checks the write there.

    - Under [Run.valid_input] the write DECLINES ([CheckUnmodeled]): an
      error, as it was at the published model.
    - Under [Run.valid_input_sigpipe_kills] the same write is answered
      with -EPIPE over [State.with_killed] 13, which [Run.sstep_killed]
      turns into [KillEv 13].
    - Under [Run.valid_input] with SIGPIPE BLOCKED the write declines too,
      rather than leaving a pending signal that the [rt_sigprocmask]
      unblocking it would turn into a death.

    [Checks.KillFree.valid_input_no_kill] is the general statement these
    illustrate: no trace of a run under [Run.valid_input] carries a kill. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Examples.
Import ListNotations.
Open Scope bv_scope.

(* -------------------------------------------------------------------------
   The three launches, each proved valid
   ------------------------------------------------------------------------- *)

(** [Checks.Examples.demo_input_valid]'s input: the ordinary launch. *)
Definition ordinary_launch : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

(** The same launch, declaring the SIGPIPE death (the last field). *)
Definition kills_launch : ProcInput :=
  mkProcInput_full [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48
                   default_urandom [] default_kernel default_execfn
                   true true true (Z_to_bv 64 0) (Z_to_bv 64 0) [] false false no_clone_refusers
                   true.

(** The ordinary launch with SIGPIPE blocked: bit 12 of the mask is
    signal 13. *)
Definition blocked_launch : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (Z_to_bv 64 4096) demo_hwcap false Sv48.

Lemma ordinary_launch_valid : valid_input ordinary_launch.
Proof. exact demo_input_valid. Qed.

(** Every clause but the declaration is [demo_input_valid]'s, taken
    without counting conjuncts; the declaration closes by computation. *)
Lemma kills_launch_valid : valid_input_sigpipe_kills kills_launch.
Proof.
  pose proof demo_input_valid as H. red in H |- *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; try assumption; reflexivity.
Qed.

(** Every clause but the mask is [demo_input_valid]'s; the mask clears
    no kernel-only bit, which [Run.valid_sigmask] asks. *)
Lemma blocked_launch_valid : valid_input blocked_launch.
Proof.
  pose proof demo_input_valid as H. red in H |- *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; try assumption;
    try reflexivity.
  unfold valid_sigmask. apply bv_eq. vm_compute. reflexivity.
Qed.

Example blocked_launch_blocks_sigpipe :
  sigpipe_blocked (in_sigmask blocked_launch) = true
  /\ sigpipe_blocked (in_sigmask ordinary_launch) = false.
Proof. split; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   pipe2, close the read end, write
   ------------------------------------------------------------------------- *)

Definition start_model (inp : ProcInput) : Model :=
  init_model [] 0 0 demo_sp demo_limit inp.

(** [pipe2(fildes, 0)] installing read end 3 and write end 4, as
    [Checks.Cases.Fs.Pipe.pipe2_unwrapped_fildes_still_installs_the_pair]
    does on the demo launch. *)
Definition pipe2_in : SyscallInput :=
  mkInput 59 [pipe2_flat_fildes; 0; 0; 0; 0; 0] (fun _ => None) pipe2_flat_mem.
Definition pipe2_eff : SyscallEffect :=
  mkEffect (Z_to_bv 64 0) [(pipe2_flat_fildes, [3;0;0;0;4;0;0;0])] [].

(** [close(3)]: the read end goes. *)
Definition close3_in : SyscallInput :=
  mkInput 57 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).
Definition close_eff : SyscallEffect := mkEffect (Z_to_bv 64 0) [] [].

(** [write(4, "ab", 2)] to the write end. *)
Definition write4_in : SyscallInput :=
  mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None).
Definition epipe_eff : SyscallEffect := mkEffect (errno_ret EPIPE) [] [].

(** The model the first two calls reach, when both succeed with no
    events; [None] otherwise, which every example below refutes. *)
Definition after_close (inp : ProcInput) : option Model :=
  match check_syscall pipe2_in pipe2_eff (start_model inp) with
  | CheckOk m1 [] =>
      match check_syscall close3_in close_eff m1 with
      | CheckOk m2 [] => Some m2
      | _ => None
      end
  | _ => None
  end.

(* -------------------------------------------------------------------------
   The three cases
   ------------------------------------------------------------------------- *)

(** THE ORDINARY LAUNCH: the write declines.  And the pipe really has no
    reader there: the read end is gone and the write end is still
    open. *)
Example ordinary_launch_write_declines :
  match after_close ordinary_launch with
  | Some m2 =>
      fd_lookup (m_fds m2) (Z_to_bv 64 3) = None
      /\ check_syscall write4_in epipe_eff m2 = CheckUnmodeled
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** THE LAUNCH THAT DECLARES THE DEATH: the same write, from the same
    state but for the declaration, is -EPIPE over a model that records
    death by signal 13. *)
Example kills_launch_write_kills :
  match after_close kills_launch with
  | Some m2 =>
      check_syscall write4_in epipe_eff m2
      = CheckOk (with_killed (Z_to_bv 64 13) m2) []
  | None => False
  end.
Proof. check_eq. Qed.

(** ...and the death is what [Run.sstep_killed] reads: [State.m_killed]
    names signal 13. *)
Example kills_launch_records_signal_13 :
  match after_close kills_launch with
  | Some m2 => m_killed (with_killed (Z_to_bv 64 13) m2) = Some (Z_to_bv 64 13)
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** THE ORDINARY LAUNCH WITH SIGPIPE BLOCKED: the write declines too.
    The decline does not read the mask, so no SIGPIPE is ever left
    pending for a later unblock to deliver. *)
Example blocked_launch_write_declines :
  match after_close blocked_launch with
  | Some m2 =>
      sigpipe_blocked (m_sigmask m2) = true
      /\ check_syscall write4_in epipe_eff m2 = CheckUnmodeled
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** The same decline, read off the launch predicate rather than off a
    fixture: on every input [Run.valid_input] admits, the model the run
    starts from has the death undeclared, so every write that would raise
    SIGPIPE at SIG_DFL declines ([Sys.Fs.ReadWrite.sigpipe_write_off_unmodeled]). *)
Lemma valid_input_model_declines_sigpipe :
  forall reserved brk0 mbase sp lim inp,
  valid_input inp ->
  m_sigpipe_terminal (init_model reserved brk0 mbase sp lim inp) = false.
Proof.
  intros reserved brk0 mbase sp lim inp Hv.
  rewrite m_sigpipe_terminal_init_model. exact (valid_input_sigpipe_terminal _ Hv).
Qed.
