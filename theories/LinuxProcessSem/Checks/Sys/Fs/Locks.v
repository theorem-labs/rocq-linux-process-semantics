(** * LinuxProcessSem.Checks.Sys.Fs.Locks — the flock (32) checker, and its proofs

    Mirrors [Sys/Fs/Locks.v], which answers to Linux [fs/locks.c]: this
    file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Fs.ReadWrite.

(** flock: a LOCK_MAND word answers 0 without reading the fd, an
    unrecognized operation answers -EINVAL still without reading it, a
    closed fd is then -EBADF, an unlock on any open fd is 0, and a
    shared or exclusive request is 0 only on a file descriptor whose
    path no other descriptor names. *)
Definition check_flock (fd cmd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if flock_mand_b cmd then check_ret_only eff (Z_to_bv 64 0) m []
  else if negb (flock_cmd_ok_b cmd) then check_ret_only eff (errno_ret EINVAL) m []
  else
    match fd_lookup (m_fds m) fd with
    | None => check_ret_only eff (errno_ret EBADF) m []
    | Some e =>
        if flock_unlock_b cmd then check_ret_only eff (Z_to_bv 64 0) m []
        else
          match e with
          | FdFile p _ =>
              if flock_sole_opener (m_fds m) p
              then check_ret_only eff (Z_to_bv 64 0) m []
              else CheckUnmodeled
          | FdFileW p _ =>
              if flock_sole_opener (m_fds m) p
              then check_ret_only eff (Z_to_bv 64 0) m []
              else CheckUnmodeled
          | FdFileA p _ =>
              if flock_sole_opener (m_fds m) p
              then check_ret_only eff (Z_to_bv 64 0) m []
              else CheckUnmodeled
          | FdFileRW p _ =>
              if flock_sole_opener (m_fds m) p
              then check_ret_only eff (Z_to_bv 64 0) m []
              else CheckUnmodeled
          | FdChannel _ => CheckUnmodeled
          | FdDir       => CheckUnmodeled
          | FdSocket _  => CheckUnmodeled
          | FdPipe _ _  => CheckUnmodeled
          | FdDevNull _ _ => CheckUnmodeled
          | FdUrandom => CheckUnmodeled
          | FdStream _ _ _ => CheckUnmodeled
          | FdDgram _ => CheckUnmodeled
          | FdEventfd _ => CheckUnmodeled
          end
    end.

(** The two cmd-only tests are substituted into the GOAL by their own
    [destruct], because neither mentions the model the bind introduces;
    only the two that read [m] need an [srw] to reach the goal's copy.
    That asymmetry is why the arms below are not one uniform script. *)

Lemma check_flock_sound_ok : forall fd cmd eff m m' evs i,
  check_flock fd cmd eff m = CheckOk m' evs -> flock_spec fd cmd i m (Ok eff m' evs).
Proof.
  intros fd cmd eff m m' evs i H.
  unfold check_flock in H. unfold flock_spec.
  destruct (flock_mand_b cmd) eqn:Hmand.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. apply pure_ok. }
  destruct (negb (flock_cmd_ok_b cmd)) eqn:Hok.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. apply pure_ok. }
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd;
    [| apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
       eapply bind_ok0; [apply get_model_ok|]; cbv beta iota;
       srw Hfd; apply pure_ok ].
  destruct (flock_unlock_b cmd) eqn:Hun.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply pure_ok. }
  destruct e as [c|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd sst|ctx|fam]; try discriminate;
    destruct (flock_sole_opener (m_fds m) p) eqn:Hsole; try discriminate;
    apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
    (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
    srw Hfd; srw Hsole; apply pure_ok.
Qed.

Lemma check_flock_sound_unmodeled : forall fd cmd eff m i,
  check_flock fd cmd eff m = CheckUnmodeled -> flock_spec fd cmd i m Unmodeled.
Proof.
  intros fd cmd eff m i H.
  unfold check_flock in H. unfold flock_spec.
  destruct (flock_mand_b cmd) eqn:Hmand;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (negb (flock_cmd_ok_b cmd)) eqn:Hok;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd;
    [|now apply check_ret_only_no_unmodeled in H].
  destruct (flock_unlock_b cmd) eqn:Hun;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct e as [c|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd sst|ctx|fam].
  - eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
      [now apply check_ret_only_no_unmodeled in H|].
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hsole. apply unmodeled_intro.
  - destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
      [now apply check_ret_only_no_unmodeled in H|].
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hsole. apply unmodeled_intro.
  - destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
      [now apply check_ret_only_no_unmodeled in H|].
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hsole. apply unmodeled_intro.
  - destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
      [now apply check_ret_only_no_unmodeled in H|].
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hsole. apply unmodeled_intro.
  - eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - (* /dev/null: declined *)
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - (* /dev/urandom: declined *)
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - (* a stream-pair end: declined, the [FdSocket] case *)
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - (* an eventfd: declined, fail-closed on the shared anonymous inode *)
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
  - (* a datagram socket: declined, the [FdSocket] case *)
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply unmodeled_intro.
Qed.

Lemma check_flock_complete_ok : forall fd cmd eff m m' evs i,
  flock_spec fd cmd i m (Ok eff m' evs) -> check_flock fd cmd eff m = CheckOk m' evs.
Proof.
  intros fd cmd eff m m' evs i H.
  unfold flock_spec in H. unfold check_flock. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (flock_mand_b cmd) eqn:Hmand; hall Hmand; inv_ok;
    try (destruct (negb (flock_cmd_ok_b cmd)) eqn:Hok; hall Hok; inv_ok;
         try (destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
              try (destruct (flock_unlock_b cmd) eqn:Hun; hall Hun; inv_ok;
                   try (destruct e as [c|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd sst|ctx|fam]; hall Hfd; inv_ok;
                        try (destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
                             hall Hsole; inv_ok)))));
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_flock_complete_unmodeled : forall fd cmd m i eff,
  flock_spec fd cmd i m Unmodeled -> check_flock fd cmd eff m = CheckUnmodeled.
Proof.
  intros fd cmd m i eff H.
  unfold flock_spec in H. unfold check_flock. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (flock_mand_b cmd) eqn:Hmand; hall Hmand; inv_ok;
    try (destruct (negb (flock_cmd_ok_b cmd)) eqn:Hok; hall Hok; inv_ok;
         try (destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
              try (destruct (flock_unlock_b cmd) eqn:Hun; hall Hun; inv_ok;
                   try (destruct e as [c|p off|p off|p off|p off| |sk|id w|rd wr| |sid sd sst|ctx|fam]; hall Hfd; inv_ok;
                        try (destruct (flock_sole_opener (m_fds m) p) eqn:Hsole;
                             hall Hsole; inv_ok)))));
    reflexivity.
Qed.
