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

(** fcntl: a closed fd is -EBADF whatever the command; on an open one
    F_SETFD answers 0 for any arg, F_GETFD answers 0 or FD_CLOEXEC, an
    F_SETFL that provably changes nothing answers 0, F_GETFL answers the
    flag word on the fd kinds [Fcntl.getfl_f_flags] can derive it for,
    and every other command is unmodeled. *)
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
      else if bv_eqb cmd F_SETFL && setfl_noop_on e arg
      then check_ret_only eff (Z_to_bv 64 0) m []
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | Some fl => check_ret_only eff fl m []
        | None => CheckUnmodeled
        end
      else CheckUnmodeled
  end.

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
      * destruct (bv_eqb cmd F_SETFL && setfl_noop_on e arg) eqn:Hl.
        -- apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
           eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
           srw Hfd. srw Hl. apply pure_ok.
        -- destruct (bv_eqb cmd F_GETFL) eqn:Hg; [|discriminate].
           destruct (getfl_f_flags e) as [fl|] eqn:Hgf; [|discriminate].
           apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
           eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
           srw Hfd. srw Hl. srw Hgf. apply pure_ok.
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
      * destruct (bv_eqb cmd F_SETFL && setfl_noop_on e arg) eqn:Hl.
        -- now apply check_ret_only_no_unmodeled in H.
        -- destruct (bv_eqb cmd F_GETFL) eqn:Hg.
           ++ destruct (getfl_f_flags e) as [fl|] eqn:Hgf.
              ** now apply check_ret_only_no_unmodeled in H.
              ** eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
                 srw Hfd. srw Hl. srw Hgf. apply unmodeled_intro.
           ++ eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
              srw Hfd. srw Hl. apply unmodeled_intro.
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
              try (destruct (bv_eqb cmd F_SETFL && setfl_noop_on e arg) eqn:Hl;
                   hall Hl; inv_ok;
                   try (destruct (bv_eqb cmd F_GETFL) eqn:Hg; hall Hg; inv_ok;
                        try (destruct (getfl_f_flags e) as [fl|] eqn:Hgf;
                             hall Hgf; inv_ok)))));
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
              try (destruct (bv_eqb cmd F_SETFL && setfl_noop_on e arg) eqn:Hl;
                   hall Hl; inv_ok;
                   try (destruct (bv_eqb cmd F_GETFL) eqn:Hg; hall Hg; inv_ok;
                        try (destruct (getfl_f_flags e) as [fl|] eqn:Hgf;
                             hall Hgf; inv_ok)))));
    reflexivity.
Qed.
