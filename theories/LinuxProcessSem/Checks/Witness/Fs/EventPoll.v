(** * LinuxProcessSem.Checks.Witness.Fs.EventPoll — the epoll_create1 (20), epoll_ctl (21), epoll_pwait (22) witnesses, and their proofs

    Mirrors [Sys/Fs/EventPoll.v], which answers to Linux
    [fs/eventpoll.c]: this file holds the witnesses for the syscalls
    defined there, and no others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

(** Each of the three arms is deterministic: the spec admits exactly one
    outcome per input, and where it admits none it is [Unmodeled].  So
    every witness here is the spec's own [*_outcome] read back, and
    [Unmodeled] is itself the admissible outcome on the declining
    inputs — which is what makes progress hold for a syscall whose
    success arm is not modeled at all. *)

Definition epoll_create1_witness (flags32 : word) (m : Model)
    : outcome SyscallEffect :=
  match epoll_create1_outcome flags32 with
  | None => Unmodeled
  | Some r => ret_outcome r m
  end.

Lemma epoll_create1_witness_ok : forall flags32 i m,
  epoll_create1_spec flags32 i m (epoll_create1_witness flags32 m).
Proof.
  intros. unfold epoll_create1_spec, epoll_create1_witness.
  destruct (epoll_create1_outcome flags32) as [r|];
    [apply pure_ok|apply unmodeled_intro].
Qed.

Definition epoll_ctl_witness (epfd op32 tfd event : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match epoll_ctl_outcome i m epfd op32 tfd event with
  | None => Unmodeled
  | Some r => Ok (with_copyins (epoll_ctl_reads i op32 event) (mkEffect r [] [])) m []
  end.

Lemma epoll_ctl_witness_ok : forall epfd op32 tfd event i m,
  epoll_ctl_spec epfd op32 tfd event i m
    (epoll_ctl_witness epfd op32 tfd event i m).
Proof.
  intros. unfold epoll_ctl_spec, epoll_ctl_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (epoll_ctl_outcome i m epfd op32 tfd event) as [r|];
    [apply pure_ok|apply unmodeled_intro].
Qed.

Definition epoll_pwait_witness (epfd events maxevents32 sigmask sigsetsize : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | None => Unmodeled
  | Some r => ret_outcome r m
  end.

Lemma epoll_pwait_witness_ok :
  forall epfd events maxevents32 sigmask sigsetsize i m,
  epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m
    (epoll_pwait_witness epfd events maxevents32 sigmask sigsetsize i m).
Proof.
  intros. unfold epoll_pwait_spec, epoll_pwait_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize)
    as [r|]; [apply pure_ok|apply unmodeled_intro].
Qed.
