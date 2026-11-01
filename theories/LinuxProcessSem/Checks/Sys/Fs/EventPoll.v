(** * LinuxProcessSem.Checks.Sys.Fs.EventPoll — the epoll_create1 (20), epoll_ctl (21), epoll_pwait (22) checkers, and their proofs

    Mirrors [Sys/Fs/EventPoll.v], which answers to Linux
    [fs/eventpoll.c]: this file holds the checkers for the syscalls
    defined there, and no others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

(** All three arms are deterministic and write no user memory, so each
    acceptor is the spec's own computation plus one equality on the
    return value.  [check_ret_only] carries the rest of the obligation:
    it rejects any effect with a non-empty write, zero, unmap, copy or
    copy-in ledger, which is what pins that a conforming run may not
    smuggle a store past an arm that stores nothing.

    Everything that makes epoll hard — readiness, the interest set, the
    ready list, blocking — is decided by the spec's [*_outcome]
    answering [None], which is [CheckUnmodeled] here. *)

Definition check_epoll_create1 (flags32 : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match epoll_create1_outcome flags32 with
  | None => CheckUnmodeled
  | Some r => check_ret_only eff r m []
  end.

Lemma check_epoll_create1_sound_ok : forall flags32 eff m m' evs i,
  check_epoll_create1 flags32 eff m = CheckOk m' evs ->
  epoll_create1_spec flags32 i m (Ok eff m' evs).
Proof.
  intros flags32 eff m m' evs i H.
  unfold check_epoll_create1 in H. unfold epoll_create1_spec.
  destruct (epoll_create1_outcome flags32) as [r|] eqn:Ho; [|discriminate].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  apply pure_ok.
Qed.

Lemma check_epoll_create1_sound_unmodeled : forall flags32 eff m i,
  check_epoll_create1 flags32 eff m = CheckUnmodeled ->
  epoll_create1_spec flags32 i m Unmodeled.
Proof.
  intros flags32 eff m i H.
  unfold check_epoll_create1 in H. unfold epoll_create1_spec.
  destruct (epoll_create1_outcome flags32) as [r|] eqn:Ho;
    [|apply unmodeled_intro].
  unfold check_ret_only in H.
  destruct eff as [ret ws zs us cs ks];
    destruct ws; destruct zs; destruct us; destruct cs; destruct ks;
    try discriminate; destruct (bv_eqb ret r); discriminate.
Qed.

Lemma check_epoll_create1_complete_ok : forall flags32 eff m m' evs i,
  epoll_create1_spec flags32 i m (Ok eff m' evs) ->
  check_epoll_create1 flags32 eff m = CheckOk m' evs.
Proof.
  intros flags32 eff m m' evs i H.
  unfold epoll_create1_spec in H. unfold check_epoll_create1.
  destruct (epoll_create1_outcome flags32) as [r|] eqn:Ho.
  - unfold pure in H. inv_ok.
    apply check_ret_only_ok_iff. repeat split; reflexivity.
  - unfold unmodeled in H. inv_ok.
Qed.

Lemma check_epoll_create1_complete_unmodeled : forall flags32 m eff i,
  epoll_create1_spec flags32 i m Unmodeled ->
  check_epoll_create1 flags32 eff m = CheckUnmodeled.
Proof.
  intros flags32 m eff i H.
  unfold epoll_create1_spec in H. unfold check_epoll_create1.
  destruct (epoll_create1_outcome flags32) as [r|] eqn:Ho; [|reflexivity].
  unfold pure in H. inv_ok.
Qed.

Definition check_epoll_ctl (i : SyscallInput) (epfd op32 tfd event : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match epoll_ctl_outcome i m epfd op32 tfd event with
  | None => CheckUnmodeled
  | Some r => check_ret_only_copyins (epoll_ctl_reads i op32 event) eff r m []
  end.

Lemma check_epoll_ctl_sound_ok : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs ->
  epoll_ctl_spec epfd op32 tfd event i m (Ok eff m' evs).
Proof.
  intros i epfd op32 tfd event eff m m' evs H.
  unfold check_epoll_ctl in H. unfold epoll_ctl_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (epoll_ctl_outcome i m epfd op32 tfd event) as [r|] eqn:Ho;
    cbv iota; [|discriminate].
  apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
  apply pure_ok.
Qed.

Lemma check_epoll_ctl_sound_unmodeled : forall i epfd op32 tfd event eff m,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckUnmodeled ->
  epoll_ctl_spec epfd op32 tfd event i m Unmodeled.
Proof.
  intros i epfd op32 tfd event eff m H.
  unfold check_epoll_ctl in H. unfold epoll_ctl_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (epoll_ctl_outcome i m epfd op32 tfd event) as [r|] eqn:Ho;
    cbv iota; [|apply unmodeled_intro].
  now apply check_ret_only_copyins_no_unmodeled in H.
Qed.

Lemma check_epoll_ctl_complete_ok : forall i epfd op32 tfd event eff m m' evs,
  epoll_ctl_spec epfd op32 tfd event i m (Ok eff m' evs) ->
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs.
Proof.
  intros i epfd op32 tfd event eff m m' evs H.
  unfold epoll_ctl_spec in H. unfold check_epoll_ctl. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (epoll_ctl_outcome i m epfd op32 tfd event) as [r|] eqn:Ho;
    hall Ho; inv_ok.
  apply check_ret_only_copyins_ok_iff. repeat split; reflexivity.
Qed.

Lemma check_epoll_ctl_complete_unmodeled : forall i epfd op32 tfd event m eff,
  epoll_ctl_spec epfd op32 tfd event i m Unmodeled ->
  check_epoll_ctl i epfd op32 tfd event eff m = CheckUnmodeled.
Proof.
  intros i epfd op32 tfd event m eff H.
  unfold epoll_ctl_spec in H. unfold check_epoll_ctl. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (epoll_ctl_outcome i m epfd op32 tfd event) as [r|] eqn:Ho;
    hall Ho; inv_ok; reflexivity.
Qed.

Definition check_epoll_pwait (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | None => CheckUnmodeled
  | Some r => check_ret_only eff r m []
  end.

Lemma check_epoll_pwait_sound_ok :
  forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckOk m' evs ->
  epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m
    (Ok eff m' evs).
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H.
  unfold check_epoll_pwait in H. unfold epoll_pwait_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize)
    as [r|] eqn:Ho; cbv iota; [|discriminate].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  apply pure_ok.
Qed.

Lemma check_epoll_pwait_sound_unmodeled :
  forall i epfd events maxevents32 sigmask sigsetsize eff m,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckUnmodeled ->
  epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m Unmodeled.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m H.
  unfold check_epoll_pwait in H. unfold epoll_pwait_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize)
    as [r|] eqn:Ho; cbv iota; [|apply unmodeled_intro].
  unfold check_ret_only in H.
  destruct eff as [ret ws zs us cs ks];
    destruct ws; destruct zs; destruct us; destruct cs; destruct ks;
    try discriminate; destruct (bv_eqb ret r); discriminate.
Qed.

Lemma check_epoll_pwait_complete_ok :
  forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m
    (Ok eff m' evs) ->
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckOk m' evs.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H.
  unfold epoll_pwait_spec in H. unfold check_epoll_pwait. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize)
    as [r|] eqn:Ho; hall Ho; inv_ok.
  apply check_ret_only_ok_iff. repeat split; reflexivity.
Qed.

Lemma check_epoll_pwait_complete_unmodeled :
  forall i epfd events maxevents32 sigmask sigsetsize m eff,
  epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m Unmodeled ->
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckUnmodeled.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize m eff H.
  unfold epoll_pwait_spec in H. unfold check_epoll_pwait. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize)
    as [r|] eqn:Ho; hall Ho; inv_ok; reflexivity.
Qed.
