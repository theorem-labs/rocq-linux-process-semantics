(** * LinuxProcessSem.Checks.Sys.Fs.Signalfd — the signalfd4 (74) checker, and its proofs

    Mirrors [Sys/Fs/Signalfd.v], which answers to Linux [fs/signalfd.c]:
    this file holds the checkers for the syscalls defined there, and no
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
  Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import
  Fs.Open.

(** [Fs.Signalfd.signalfd4_spec] as an acceptor.  The flag gate is
    written out rather than taken from [signalfd4_einval_b], as
    [Checks.Sys.Fs.EventFd] writes out its own.  A new descriptor is
    [Open.check_new_fd_result]'s shape, checked on the effect with its
    copy-in ledger cleared, and the ledger must be exactly the 8 mask
    bytes read. *)
Definition check_signalfd4 (i : SyscallInput) (ufd mask sizemask flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (Z.eqb (bv_unsigned sizemask) NSIG_BYTES)
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    match sigset_at (in_mem i) mask with
    | None => check_ret_only eff (errno_ret EFAULT) m []
    | Some raw =>
        if negb (Z.eqb (Z.ldiff (bv_unsigned flags) SFD_FLAGS_SET) 0)
        then check_ret_only_copyins [(mask, Z.to_nat NSIG_BYTES)] eff (errno_ret EINVAL) m []
        else if negb (bv_eqb ufd signalfd_new_ufd) then CheckUnmodeled
        else check_copyins_after [(mask, Z.to_nat NSIG_BYTES)] eff
               (check_new_fd_result signalfd4_errnos (clear_copyins eff) m
                  (fun fd => with_fds (fd_insert (m_fds m) fd
                                        (FdOpaque (OSignalFd (sigmask_strip raw) flags))) m))
    end.

Lemma check_signalfd4_sound_ok : forall i ufd mask sizemask flags eff m m' evs,
  check_signalfd4 i ufd mask sizemask flags eff m = CheckOk m' evs ->
  signalfd4_spec ufd mask sizemask flags i m (Ok eff m' evs).
Proof.
  intros i ufd mask sizemask flags eff m m' evs H.
  unfold check_signalfd4 in H. unfold signalfd4_spec, signalfd4_einval_b.
  destruct (negb (Z.eqb (bv_unsigned sizemask) NSIG_BYTES)); cbv iota in H |- *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (sigset_at (in_mem i) mask) as [raw|]; cbv iota in H |- *.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      unfold err_ret, ret_only. apply pure_ok. }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) SFD_FLAGS_SET) 0);
    cbn [negb] in H |- *; cbv iota in H |- *.
  2:{ apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      apply record_copyins_ok_empty; [reflexivity|].
      unfold err_ret, ret_only. apply pure_ok. }
  destruct (bv_eqb ufd signalfd_new_ufd); cbn [negb] in H |- *; cbv iota in H |- *;
    [|discriminate H].
  apply check_copyins_after_ok_iff in H. destruct H as [Hreads H].
  apply record_copyins_clear_ok; [exact Hreads|].
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  unfold check_new_fd_result in H.
  destruct (clear_copyins eff) as [ret ws zs us cs cis];
    destruct ws as [|w ws']; destruct zs as [|z zs']; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  destruct (errno_ret_in signalfd4_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
    apply pure_ok.
  - destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
    destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq.
    apply alt_r.
    eapply bind_ok0; [apply (choose_ok _ ret); split; assumption|].
    cbv beta. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_signalfd4_sound_unmodeled : forall i ufd mask sizemask flags eff m,
  check_signalfd4 i ufd mask sizemask flags eff m = CheckUnmodeled ->
  signalfd4_spec ufd mask sizemask flags i m Unmodeled.
Proof.
  intros i ufd mask sizemask flags eff m H.
  unfold check_signalfd4 in H. unfold signalfd4_spec, signalfd4_einval_b.
  destruct (negb (Z.eqb (bv_unsigned sizemask) NSIG_BYTES)); cbv iota in H |- *.
  { exfalso. now apply check_ret_only_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (sigset_at (in_mem i) mask) as [raw|]; cbv iota in H |- *.
  2:{ exfalso. now apply check_ret_only_no_unmodeled in H. }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) SFD_FLAGS_SET) 0);
    cbn [negb] in H |- *; cbv iota in H |- *.
  2:{ exfalso. now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (bv_eqb ufd signalfd_new_ufd); cbn [negb] in H |- *; cbv iota in H |- *.
  - exfalso. apply check_copyins_after_unmodeled in H.
    exact (check_new_fd_result_no_unmodeled _ _ _ _ H).
  - (* the declined update of an existing signalfd *)
    unfold record_copyins. apply bind_unmodeled1. apply unmodeled_intro.
Qed.

Lemma check_signalfd4_complete_ok : forall i ufd mask sizemask flags eff m m' evs,
  signalfd4_spec ufd mask sizemask flags i m (Ok eff m' evs) ->
  check_signalfd4 i ufd mask sizemask flags eff m = CheckOk m' evs.
Proof.
  intros i ufd mask sizemask flags eff m m' evs H.
  unfold signalfd4_spec, signalfd4_einval_b in H. unfold check_signalfd4.
  destruct (negb (Z.eqb (bv_unsigned sizemask) NSIG_BYTES)); cbv iota in H |- *.
  { sys_unfold. inv_ok. apply check_ret_only_ok_iff. auto. }
  apply input_bind_ok_inv in H. cbv beta in H.
  destruct (sigset_at (in_mem i) mask) as [raw|]; cbv iota in H |- *.
  2:{ sys_unfold. inv_ok. apply check_ret_only_ok_iff. auto. }
  apply record_copyins_ok_inv in H. destruct H as (core & Hcore & ->).
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) SFD_FLAGS_SET) 0);
    cbn [negb] in Hcore |- *; cbv iota in Hcore |- *.
  2:{ sys_unfold. inv_ok. apply check_ret_only_copyins_ok_iff. auto. }
  destruct (bv_eqb ufd signalfd_new_ufd); cbn [negb] in Hcore |- *; cbv iota in Hcore |- *.
  2:{ unfold unmodeled in Hcore. discriminate Hcore. }
  sys_unfold. cbv iota in Hcore. inv_ok.
  - apply check_copyins_after_ok_iff. split; [reflexivity|].
    unfold check_new_fd_result, clear_copyins, with_copyins. cbn [eff_ret eff_writes
      eff_zeros eff_unmaps eff_copies].
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - apply check_copyins_after_ok_iff. split; [reflexivity|].
    unfold check_new_fd_result, clear_copyins, with_copyins. cbn [eff_ret eff_writes
      eff_zeros eff_unmaps eff_copies].
    rewrite errno_ret_in_alloc_fd by reflexivity.
    match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
    rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma check_signalfd4_complete_unmodeled : forall i ufd mask sizemask flags m eff,
  signalfd4_spec ufd mask sizemask flags i m Unmodeled ->
  check_signalfd4 i ufd mask sizemask flags eff m = CheckUnmodeled.
Proof.
  intros i ufd mask sizemask flags m eff H.
  unfold signalfd4_spec, signalfd4_einval_b in H. unfold check_signalfd4.
  destruct (negb (Z.eqb (bv_unsigned sizemask) NSIG_BYTES)); cbv iota in H |- *.
  { exfalso. sys_unfold. inv_ok. }
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  destruct (sigset_at (in_mem i) mask) as [raw|]; cbv iota in H |- *.
  2:{ exfalso. sys_unfold. inv_ok. }
  apply record_copyins_unmodeled_inv in H.
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) SFD_FLAGS_SET) 0);
    cbn [negb] in H |- *; cbv iota in H |- *.
  2:{ exfalso. sys_unfold. inv_ok. }
  destruct (bv_eqb ufd signalfd_new_ufd); cbn [negb] in H |- *; cbv iota in H |- *;
    [|reflexivity].
  exfalso. sys_unfold. cbv iota in H. inv_ok.
Qed.
