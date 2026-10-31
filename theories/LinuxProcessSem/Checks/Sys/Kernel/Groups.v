(** * LinuxProcessSem.Checks.Sys.Kernel.Groups — the getgroups (158) and setgroups (159) checkers, and their proofs

    Mirrors [Sys/Kernel/Groups.v], which answers to Linux
    [kernel/groups.c]: this file holds the checkers for the syscalls
    defined there, and no others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export Prelude.

(** [getgroups] (158): the count, or one of the two -EINVALs, and
    [CheckUnmodeled] on the writing path.  Mirrors
    [Kernel.Groups.getgroups_spec] branch for branch — read that spec
    for the kernel order the branches are in and why the [grouplist]
    pointer is not an argument here either. *)
Definition check_getgroups (gidsetsize : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  let n := sint32 gidsetsize in
  if (n <? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
  else
    let ng := Z.of_nat (length (cr_groups (m_creds m))) in
    if (NGROUPS_MAX <? ng)%Z then CheckUnmodeled
    else if (n =? 0)%Z then check_ret_only eff (Z_to_bv 64 ng) m []
    else if (n <? ng)%Z then check_ret_only eff (errno_ret EINVAL) m []
    else if (ng =? 0)%Z then check_ret_only eff (Z_to_bv 64 0) m []
    else CheckUnmodeled.

Lemma check_getgroups_sound_ok : forall gidsetsize eff m m' evs i,
  check_getgroups gidsetsize eff m = CheckOk m' evs ->
  getgroups_spec gidsetsize i m (Ok eff m' evs).
Proof.
  intros gidsetsize eff m m' evs i H.
  unfold check_getgroups in H. unfold getgroups_spec. cbv zeta in *.
  destruct (Z.ltb (sint32 gidsetsize) 0) eqn:Hneg.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (Z.ltb NGROUPS_MAX
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hmax;
    [discriminate|].
  destruct (Z.eqb (sint32 gidsetsize) 0) eqn:Hzero.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold ret_only. apply pure_ok. }
  destruct (Z.ltb (sint32 gidsetsize)
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hsmall.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (Z.eqb (Z.of_nat (length (cr_groups (m_creds m)))) 0) eqn:Hempty;
    [|discriminate].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  unfold ret_only. apply pure_ok.
Qed.

(** Both declines are the writing path and the impossible-length guard;
    everything else answers. *)
Lemma check_getgroups_sound_unmodeled : forall gidsetsize eff m i,
  check_getgroups gidsetsize eff m = CheckUnmodeled ->
  getgroups_spec gidsetsize i m Unmodeled.
Proof.
  intros gidsetsize eff m i H.
  unfold check_getgroups in H. unfold getgroups_spec. cbv zeta in *.
  destruct (Z.ltb (sint32 gidsetsize) 0) eqn:Hneg.
  { now apply check_ret_only_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (Z.ltb NGROUPS_MAX
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hmax;
    [apply unmodeled_intro|].
  destruct (Z.eqb (sint32 gidsetsize) 0) eqn:Hzero.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (Z.ltb (sint32 gidsetsize)
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hsmall.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (Z.eqb (Z.of_nat (length (cr_groups (m_creds m)))) 0) eqn:Hempty.
  { now apply check_ret_only_no_unmodeled in H. }
  apply unmodeled_intro.
Qed.

Lemma check_getgroups_complete_ok : forall gidsetsize eff m m' evs i,
  getgroups_spec gidsetsize i m (Ok eff m' evs) ->
  check_getgroups gidsetsize eff m = CheckOk m' evs.
Proof.
  intros gidsetsize eff m m' evs i H.
  unfold getgroups_spec in H. unfold check_getgroups. sys_unfold.
  cbv iota zeta in H. cbv zeta.
  destruct (Z.ltb (sint32 gidsetsize) 0) eqn:Hneg; hall Hneg; inv_ok;
    [cbn; rewrite bv_eqb_refl; reflexivity|].
  destruct (Z.ltb NGROUPS_MAX
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hmax;
    hall Hmax; inv_ok.
  destruct (Z.eqb (sint32 gidsetsize) 0) eqn:Hzero; hall Hzero; inv_ok;
    [cbn; rewrite bv_eqb_refl; reflexivity|].
  destruct (Z.ltb (sint32 gidsetsize)
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hsmall;
    hall Hsmall; inv_ok;
    [cbn; rewrite bv_eqb_refl; reflexivity|].
  destruct (Z.eqb (Z.of_nat (length (cr_groups (m_creds m)))) 0) eqn:Hempty;
    hall Hempty; inv_ok.
  cbn; rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_getgroups_complete_unmodeled : forall gidsetsize m i eff,
  getgroups_spec gidsetsize i m Unmodeled ->
  check_getgroups gidsetsize eff m = CheckUnmodeled.
Proof.
  intros gidsetsize m i eff H.
  unfold getgroups_spec in H. unfold check_getgroups. sys_unfold.
  cbv iota zeta in H. cbv zeta.
  destruct (Z.ltb (sint32 gidsetsize) 0) eqn:Hneg; hall Hneg; inv_ok.
  destruct (Z.ltb NGROUPS_MAX
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hmax;
    hall Hmax; inv_ok; [reflexivity|].
  destruct (Z.eqb (sint32 gidsetsize) 0) eqn:Hzero; hall Hzero; inv_ok.
  destruct (Z.ltb (sint32 gidsetsize)
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hsmall;
    hall Hsmall; inv_ok.
  destruct (Z.eqb (Z.of_nat (length (cr_groups (m_creds m)))) 0) eqn:Hempty;
    hall Hempty; inv_ok; reflexivity.
Qed.

(** [setgroups] (159): an unprivileged caller is refused -EPERM before
    either argument is read; a privileged one with a [gidsetsize] whose
    [int] is 0 gets -ENOMEM with the model kept, or 0 with [cr_groups]
    cleared; every other privileged size is DECLINED, because the model
    does not import the list it would write (kernel/groups.c
    [SYSCALL_DEFINE2(setgroups)], [may_setgroups], [set_current_groups],
    read at v6.18.44; identical at v6.18.46).
    [Kernel.Groups.setgroups_spec] carries the argument for each answer
    and for the decline. *)
Definition check_setgroups (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (creds_privileged (m_creds m))
  then check_ret_only eff (errno_ret EPERM) m []
  else if negb (Z.eqb (sint32 (in_arg i 0)) 0) then CheckUnmodeled
  else
    match eff with
    | mkEffectU ret [] [] [] [] [] =>
        if bv_eqb ret (errno_ret ENOMEM) then CheckOk m []
        else if bv_eqb ret (Z_to_bv 64 0)
        then CheckOk (with_creds (set_cred_groups [] (m_creds m)) m) []
        else CheckReject
    | _ => CheckReject
    end.

Lemma check_setgroups_sound_ok : forall i eff m m' evs,
  check_setgroups i eff m = CheckOk m' evs -> setgroups_spec i m (Ok eff m' evs).
Proof.
  intros i eff m m' evs H.
  unfold check_setgroups in H. unfold setgroups_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (creds_privileged (m_creds m))).
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (Z.eqb (sint32 (in_arg i 0)) 0)); [discriminate|].
  destruct eff as [ret ws zs us cs copyins].
  destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  destruct (bv_eqb ret (errno_ret ENOMEM)) eqn:He.
  { apply bv_eqb_eq in He. subst ret. inversion H; clear H; subst.
    apply alt_l. apply pure_ok. }
  destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:Hz; [|discriminate].
  apply bv_eqb_eq in Hz. subst ret. inversion H; clear H; subst.
  apply alt_r. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

(** The non-empty privileged list is where both sides fail closed; every
    other branch answers. *)
Lemma check_setgroups_sound_unmodeled : forall i eff m,
  check_setgroups i eff m = CheckUnmodeled -> setgroups_spec i m Unmodeled.
Proof.
  intros i eff m H. unfold check_setgroups in H. unfold setgroups_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (creds_privileged (m_creds m))).
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (Z.eqb (sint32 (in_arg i 0)) 0)); [apply unmodeled_intro|].
  exfalso.
  destruct eff as [ret [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]]; try discriminate.
  destruct (bv_eqb ret (errno_ret ENOMEM)); [discriminate|].
  destruct (bv_eqb ret (Z_to_bv 64 0)); discriminate.
Qed.

Lemma check_setgroups_complete_ok : forall i eff m m' evs,
  setgroups_spec i m (Ok eff m' evs) -> check_setgroups i eff m = CheckOk m' evs.
Proof.
  intros i eff m m' evs H.
  unfold setgroups_spec in H. unfold check_setgroups.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta in H.
  destruct (negb (creds_privileged (m_creds m))).
  { unfold err_ret, ret_only, pure in H. inversion H; subst.
    cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (negb (Z.eqb (sint32 (in_arg i 0)) 0)); [now inversion H|].
  assert (Hz : bv_eqb (Z_to_bv 64 0) (errno_ret ENOMEM) = false) by reflexivity.
  destruct H as [H|H].
  - unfold err_ret, ret_only, pure in H. inversion H; subst.
    cbv beta iota. rewrite bv_eqb_refl. reflexivity.
  - sys_unfold. inv_ok. cbv beta iota.
    rewrite Hz, bv_eqb_refl. reflexivity.
Qed.

Lemma check_setgroups_complete_unmodeled : forall i m eff,
  setgroups_spec i m Unmodeled -> check_setgroups i eff m = CheckUnmodeled.
Proof.
  intros i m eff H.
  unfold setgroups_spec in H. unfold check_setgroups.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply get_model_bind_unmodeled_inv in H. cbv beta in H.
  destruct (negb (creds_privileged (m_creds m))).
  { unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (negb (Z.eqb (sint32 (in_arg i 0)) 0)); [reflexivity|].
  exfalso. destruct H as [H|H].
  - unfold err_ret, ret_only, pure in H. discriminate H.
  - sys_unfold. inv_ok.
Qed.
