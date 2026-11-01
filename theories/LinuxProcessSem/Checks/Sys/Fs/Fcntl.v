(** * LinuxProcessSem.Checks.Sys.Fs.Fcntl — the fcntl (25) checker, and its proofs

    Mirrors [Sys/Fs/Fcntl.v], which answers to Linux [fs/fcntl.c]: this
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

(** Mirrors [Fcntl.stream_setfl]: an [arg] carrying no bit of
    [setfl_acted_on] but O_NONBLOCK answers 0 and records that bit in
    the end's [se_nonblock]; any other [arg] is declined.

    An abbreviation rather than a [Definition] so that [check_fcntl]'s
    body carries the test itself: the frame lemmas over the dispatcher
    ([Checks/VmMapsDisjoint.v]'s [check_fcntl_frame]) unfold
    [check_fcntl] and walk its branches, and a folded helper would stop
    them. *)
Local Abbreviation check_stream_setfl fd id side st arg eff m :=
  (if Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0
   then check_ret_only eff (Z_to_bv 64 0)
          (with_fds (fd_insert (m_fds m) fd
                       (FdStream id side
                          (se_set_nonblock st (Z.testbit (bv_unsigned arg) 11)))) m) []
   else CheckUnmodeled).

(** Mirrors [Fcntl.eventfd_setfl]: the [check_stream_setfl] test, with
    the bit recorded in the context's [ef_nonblock].  An abbreviation
    for [check_stream_setfl]'s reason. *)
Local Abbreviation check_eventfd_setfl fd ctx arg eff m :=
  (if Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0
   then check_ret_only eff (Z_to_bv 64 0)
          (with_fds (fd_insert (m_fds m) fd
                       (FdEventfd
                          (ef_set_nonblock ctx (Z.testbit (bv_unsigned arg) 11)))) m) []
   else CheckUnmodeled).

(** fcntl: a closed fd is -EBADF whatever the command; on an open one
    F_SETFD answers 0 for any arg, F_GETFD answers 0 or FD_CLOEXEC,
    F_SETFL on a stream-pair end or an eventfd records O_NONBLOCK
    ([check_stream_setfl], [check_eventfd_setfl]) and on every other
    kind answers 0 only when it provably changes nothing, F_GETFL
    answers the flag word on the fd kinds [Fcntl.getfl_f_flags] can
    derive it for, and every other command is unmodeled. *)
Definition check_fcntl (fd cmd arg : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some e =>
      if bv_eqb cmd F_SETFD then check_ret_only eff (Z_to_bv 64 0) m []
      else if bv_eqb cmd F_GETFD then
        match eff with
        | mkEffectU r [] [] [] [] [] =>
            if bv_eqb r (Z_to_bv 64 0) || bv_eqb r FD_CLOEXEC
            then CheckOk m [] else CheckReject
        | _ => CheckReject
        end
      else if bv_eqb cmd F_SETFL then
        match e with
        | FdStream id side st => check_stream_setfl fd id side st arg eff m
        | FdEventfd ctx => check_eventfd_setfl fd ctx arg eff m
        | _ =>
            if setfl_noop_on e arg then check_ret_only eff (Z_to_bv 64 0) m []
            else CheckUnmodeled
        end
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | Some fl => check_ret_only eff fl m []
        | None => CheckUnmodeled
        end
      else CheckUnmodeled
  end.

Lemma check_stream_setfl_sound_ok : forall fd id side st arg eff m m' evs i,
  check_stream_setfl fd id side st arg eff m = CheckOk m' evs ->
  stream_setfl fd id side st arg m i m (Ok eff m' evs).
Proof.
  intros fd id side st arg eff m m' evs i H.
  unfold stream_setfl.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv beta iota; [|discriminate].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_stream_setfl_sound_unmodeled : forall fd id side st arg eff m i,
  check_stream_setfl fd id side st arg eff m = CheckUnmodeled ->
  stream_setfl fd id side st arg m i m Unmodeled.
Proof.
  intros fd id side st arg eff m i H.
  unfold stream_setfl.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv beta iota.
  - now apply check_ret_only_no_unmodeled in H.
  - apply unmodeled_intro.
Qed.

Lemma check_stream_setfl_complete_ok : forall fd id side st arg eff m m' evs i,
  stream_setfl fd id side st arg m i m (Ok eff m' evs) ->
  check_stream_setfl fd id side st arg eff m = CheckOk m' evs.
Proof.
  intros fd id side st arg eff m m' evs i H.
  unfold stream_setfl in H. sys_unfold.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv iota in H; inv_ok;
    cbn; try rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_stream_setfl_complete_unmodeled : forall fd id side st arg eff m i,
  stream_setfl fd id side st arg m i m Unmodeled ->
  check_stream_setfl fd id side st arg eff m = CheckUnmodeled.
Proof.
  intros fd id side st arg eff m i H.
  unfold stream_setfl in H. sys_unfold.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv iota in H; inv_ok; reflexivity.
Qed.

Lemma check_eventfd_setfl_sound_ok : forall fd ctx arg eff m m' evs i,
  check_eventfd_setfl fd ctx arg eff m = CheckOk m' evs ->
  eventfd_setfl fd ctx arg m i m (Ok eff m' evs).
Proof.
  intros fd ctx arg eff m m' evs i H.
  unfold eventfd_setfl.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv beta iota; [|discriminate].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_eventfd_setfl_sound_unmodeled : forall fd ctx arg eff m i,
  check_eventfd_setfl fd ctx arg eff m = CheckUnmodeled ->
  eventfd_setfl fd ctx arg m i m Unmodeled.
Proof.
  intros fd ctx arg eff m i H.
  unfold eventfd_setfl.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv beta iota.
  - now apply check_ret_only_no_unmodeled in H.
  - apply unmodeled_intro.
Qed.

Lemma check_eventfd_setfl_complete_ok : forall fd ctx arg eff m m' evs i,
  eventfd_setfl fd ctx arg m i m (Ok eff m' evs) ->
  check_eventfd_setfl fd ctx arg eff m = CheckOk m' evs.
Proof.
  intros fd ctx arg eff m m' evs i H.
  unfold eventfd_setfl in H. sys_unfold.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv iota in H; inv_ok;
    cbn; try rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_eventfd_setfl_complete_unmodeled : forall fd ctx arg eff m i,
  eventfd_setfl fd ctx arg m i m Unmodeled ->
  check_eventfd_setfl fd ctx arg eff m = CheckUnmodeled.
Proof.
  intros fd ctx arg eff m i H.
  unfold eventfd_setfl in H. sys_unfold.
  destruct (Z.eqb (Z.land (bv_unsigned arg) (setfl_acted_on - O_NONBLOCK)) 0);
    cbv iota in H; inv_ok; reflexivity.
Qed.

Lemma check_fcntl_sound_ok : forall fd cmd arg eff m m' evs i,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> fcntl_spec fd cmd arg i m (Ok eff m' evs).
Proof.
  intros fd cmd arg eff m m' evs i H.
  unfold check_fcntl in H. unfold fcntl_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - destruct (bv_eqb cmd F_SETFD) eqn:Hd.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply pure_ok.
    + destruct (bv_eqb cmd F_GETFD) eqn:Hgd.
      * eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
        srw Hfd.
        destruct eff as [r ws zs us cs ci];
          destruct ws, zs, us, cs, ci; cbv beta iota in H; try discriminate.
        destruct (bv_eqb r (Z_to_bv 64 0)) eqn:H0;
          [|destruct (bv_eqb r FD_CLOEXEC) eqn:H1]; try discriminate.
        -- apply bv_eqb_eq in H0; subst r. inversion H; subst.
           apply alt_l. apply pure_ok.
        -- apply bv_eqb_eq in H1; subst r. inversion H; subst.
           apply alt_r. apply pure_ok.
      * destruct (bv_eqb cmd F_SETFL) eqn:Hs.
        -- (* F_SETFL: the stream-pair end records its O_NONBLOCK; every
              other kind answers only a provable no-op *)
           destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |id side st|ctx|fam];
             cbv beta iota in H;
             (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
             [ ..
             | now apply check_stream_setfl_sound_ok
             | now apply check_eventfd_setfl_sound_ok
             | idtac ];
             match type of H with
             | context [setfl_noop_on ?e arg] =>
                 destruct (setfl_noop_on e arg) eqn:Hl; [|discriminate]
             end;
             cbv beta iota;
             apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
             apply pure_ok.
        -- destruct (bv_eqb cmd F_GETFL) eqn:Hg; [|discriminate].
           destruct (getfl_f_flags e) as [fl|] eqn:Hgf; [|discriminate].
           apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
           eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
           srw Hfd. srw Hgf. apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply pure_ok.
Qed.

Lemma check_fcntl_sound_unmodeled : forall fd cmd arg eff m i,
  check_fcntl fd cmd arg eff m = CheckUnmodeled -> fcntl_spec fd cmd arg i m Unmodeled.
Proof.
  intros fd cmd arg eff m i H.
  unfold check_fcntl in H. unfold fcntl_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - destruct (bv_eqb cmd F_SETFD) eqn:Hd.
    + now apply check_ret_only_no_unmodeled in H.
    + destruct (bv_eqb cmd F_GETFD) eqn:Hgd.
      * destruct eff as [r ws zs us cs ci];
          destruct ws, zs, us, cs, ci; cbv beta iota in H; try discriminate.
        destruct (bv_eqb r (Z_to_bv 64 0)); destruct (bv_eqb r FD_CLOEXEC);
          discriminate.
      * destruct (bv_eqb cmd F_SETFL) eqn:Hs.
        -- destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |id side st|ctx|fam];
             cbv beta iota in H;
             [ ..
             | eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
               srw Hfd; eapply check_stream_setfl_sound_unmodeled; exact H
             | eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
               srw Hfd; eapply check_eventfd_setfl_sound_unmodeled; exact H
             | idtac ];
             match type of H with
             | context [setfl_noop_on ?e arg] =>
                 destruct (setfl_noop_on e arg) eqn:Hl;
                 [ now apply check_ret_only_no_unmodeled in H
                 | eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
                   srw Hfd; srw Hl; apply unmodeled_intro ]
             end.
        -- destruct (bv_eqb cmd F_GETFL) eqn:Hg.
           ++ destruct (getfl_f_flags e) as [fl|] eqn:Hgf.
              ** now apply check_ret_only_no_unmodeled in H.
              ** eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
                 srw Hfd. srw Hgf. apply unmodeled_intro.
           ++ eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
              srw Hfd. apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_fcntl_complete_ok : forall fd cmd arg eff m m' evs i,
  fcntl_spec fd cmd arg i m (Ok eff m' evs) -> check_fcntl fd cmd arg eff m = CheckOk m' evs.
Proof.
  intros fd cmd arg eff m m' evs i H.
  unfold fcntl_spec in H. unfold check_fcntl. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    try (destruct (bv_eqb cmd F_SETFD) eqn:Hd; hall Hd; inv_ok;
         try (destruct (bv_eqb cmd F_GETFD) eqn:Hgd; hall Hgd; inv_ok;
              try (destruct (bv_eqb cmd F_SETFL) eqn:Hs; hall Hs; inv_ok;
                   [ (* F_SETFL: one arm per fd kind *)
                     destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |id side st|ctx|fam];
                     cbv beta iota zeta in *;
                     [ ..
                     | now apply check_stream_setfl_complete_ok with (i := i)
                     | now apply check_eventfd_setfl_complete_ok with (i := i)
                     | idtac ];
                     match goal with
                     | |- context [setfl_noop_on ?e arg] =>
                         destruct (setfl_noop_on e arg) eqn:Hl; hall Hl; inv_ok
                     end
                   | try (destruct (bv_eqb cmd F_GETFL) eqn:Hg; hall Hg; inv_ok;
                          try (destruct (getfl_f_flags e) as [fl|] eqn:Hgf;
                               hall Hgf; inv_ok)) ])));
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_fcntl_complete_unmodeled : forall fd cmd arg m i eff,
  fcntl_spec fd cmd arg i m Unmodeled -> check_fcntl fd cmd arg eff m = CheckUnmodeled.
Proof.
  intros fd cmd arg m i eff H.
  unfold fcntl_spec in H. unfold check_fcntl. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    try (destruct (bv_eqb cmd F_SETFD) eqn:Hd; hall Hd; inv_ok;
         try (destruct (bv_eqb cmd F_GETFD) eqn:Hgd; hall Hgd; inv_ok;
              try (destruct (bv_eqb cmd F_SETFL) eqn:Hs; hall Hs; inv_ok;
                   [ (* F_SETFL: one arm per fd kind *)
                     destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |id side st|ctx|fam];
                     cbv beta iota zeta in *;
                     [ ..
                     | now apply check_stream_setfl_complete_unmodeled with (i := i)
                     | now apply check_eventfd_setfl_complete_unmodeled with (i := i)
                     | idtac ];
                     match goal with
                     | |- context [setfl_noop_on ?e arg] =>
                         destruct (setfl_noop_on e arg) eqn:Hl; hall Hl; inv_ok
                     end
                   | try (destruct (bv_eqb cmd F_GETFL) eqn:Hg; hall Hg; inv_ok;
                          try (destruct (getfl_f_flags e) as [fl|] eqn:Hgf;
                               hall Hgf; inv_ok)) ])));
    reflexivity.
Qed.
