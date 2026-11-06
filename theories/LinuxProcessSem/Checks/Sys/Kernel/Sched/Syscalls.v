(** * LinuxProcessSem.Checks.Sys.Kernel.Sched.Syscalls — the sched_getaffinity (123), sched_setscheduler (119) and sched_yield (124) checkers, and their proofs

    Mirrors [Sys/Kernel/Sched/Syscalls.v], which answers to Linux
    [kernel/sched/syscalls.c]: this file holds the checkers for the
    syscalls defined there, and no others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export Prelude.

(** [sched_getaffinity] (123): -EINVAL on a length either kernel gate
    refuses, and [CheckUnmodeled] on every length they let through.
    Mirrors [Kernel.Sched.Syscalls.sched_getaffinity_spec] branch for
    branch — read that spec for why neither [pid] nor [user_mask_ptr] is
    an argument here either, and for what the decline costs. *)
Definition check_sched_getaffinity (len : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if affinity_len_einval_b len
  then check_ret_only eff (errno_ret EINVAL) m []
  else CheckUnmodeled.

Lemma check_sched_getaffinity_sound_ok : forall len eff m m' evs i,
  check_sched_getaffinity len eff m = CheckOk m' evs ->
  sched_getaffinity_spec len i m (Ok eff m' evs).
Proof.
  intros len eff m m' evs i H.
  unfold check_sched_getaffinity in H. unfold sched_getaffinity_spec.
  destruct (affinity_len_einval_b len) eqn:Hlen; [|discriminate].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  unfold err_ret, ret_only. apply pure_ok.
Qed.

(** The one decline is every length the gates let through: the answer
    there depends on [nr_cpu_ids] and [cpumask_size()], which this model
    does not carry. *)
Lemma check_sched_getaffinity_sound_unmodeled : forall len eff m i,
  check_sched_getaffinity len eff m = CheckUnmodeled ->
  sched_getaffinity_spec len i m Unmodeled.
Proof.
  intros len eff m i H.
  unfold check_sched_getaffinity in H. unfold sched_getaffinity_spec.
  destruct (affinity_len_einval_b len) eqn:Hlen.
  - now apply check_ret_only_no_unmodeled in H.
  - apply unmodeled_intro.
Qed.

Lemma check_sched_getaffinity_complete_ok : forall len eff m m' evs i,
  sched_getaffinity_spec len i m (Ok eff m' evs) ->
  check_sched_getaffinity len eff m = CheckOk m' evs.
Proof.
  intros len eff m m' evs i H.
  unfold sched_getaffinity_spec in H. unfold check_sched_getaffinity. sys_unfold.
  cbv iota in H.
  destruct (affinity_len_einval_b len) eqn:Hlen; hall Hlen; inv_ok.
  cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_sched_getaffinity_complete_unmodeled : forall len m i eff,
  sched_getaffinity_spec len i m Unmodeled ->
  check_sched_getaffinity len eff m = CheckUnmodeled.
Proof.
  intros len m i eff H.
  unfold sched_getaffinity_spec in H. unfold check_sched_getaffinity. sys_unfold.
  cbv iota in H.
  destruct (affinity_len_einval_b len) eqn:Hlen; hall Hlen; inv_ok;
    first [reflexivity | discriminate].
Qed.

(** [sched_setscheduler] (119).  Mirrors
    [Kernel.Sched.Syscalls.sched_setscheduler_spec] branch for branch,
    and shares [sched_setscheduler_answer] with it rather than
    transcribing the kernel's ordered chain a second time — read that
    spec for the envelope, for what the SCHED_IDLE answer assumes, and
    for why the model carries no scheduling state.

    The [i] is here for the four bytes at [param]: the copy-in runs
    before the task lookup, so its ledger rides on every path past it. *)
Definition check_sched_setscheduler (i : SyscallInput)
    (pid policy param : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if (sint32 policy <? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
  else if (w_is0 param || (sint32 pid <? 0)%Z)%bool
  then check_ret_only eff (errno_ret EINVAL) m []
  else
  match copy_bytes_map (in_mem i) param 4 with
  | None =>
      if negb (access_okb param 4)
      then check_ret_only eff (errno_ret EFAULT) m []
      else CheckUnmodeled
  | Some bs =>
      if negb (sched_targets_self_b pid m) then CheckUnmodeled
      else
        match sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                (bv_unsigned (le_bytes_to_word bs)) with
        | Some r => check_ret_only_copyins [(param, 4%nat)] eff r m []
        | None => CheckUnmodeled
        end
  end.

Lemma check_sched_setscheduler_sound_ok :
  forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs ->
  sched_setscheduler_spec pid policy param i m (Ok eff m' evs).
Proof.
  intros i pid policy param eff m m' evs H.
  unfold check_sched_setscheduler in H. unfold sched_setscheduler_spec.
  destruct ((sint32 policy <? 0)%Z) eqn:Hpolneg.
  { apply check_ret_only_ok_iff in H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  cbv iota.
  destruct ((w_is0 param || (sint32 pid <? 0)%Z)%bool) eqn:Hearly.
  { apply check_ret_only_ok_iff in H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  cbv iota.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (copy_bytes_map (in_mem i) param 4) as [bs|] eqn:Hread.
  - destruct (negb (sched_targets_self_b pid m)) eqn:Hself; [discriminate|].
    cbv iota.
    destruct (sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                (bv_unsigned (le_bytes_to_word bs))) as [r|] eqn:Hans;
      [|discriminate].
    apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
    apply record_copyins_ok. unfold ret_only. apply pure_ok.
  - destruct (negb (access_okb param 4)) eqn:Hacc; [|discriminate].
    apply check_ret_only_ok_iff in H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok.
Qed.

(** The four declines, in the order the kernel reaches them: a [param]
    range [access_ok] admits but memory does not back, a pid naming a
    task this model has no representation of, and the two shapes
    [sched_setscheduler_answer] answers [None] for. *)
Lemma check_sched_setscheduler_sound_unmodeled :
  forall i pid policy param eff m,
  check_sched_setscheduler i pid policy param eff m = CheckUnmodeled ->
  sched_setscheduler_spec pid policy param i m Unmodeled.
Proof.
  intros i pid policy param eff m H.
  unfold check_sched_setscheduler in H. unfold sched_setscheduler_spec.
  destruct ((sint32 policy <? 0)%Z) eqn:Hpolneg.
  { now apply check_ret_only_no_unmodeled in H. }
  cbv iota.
  destruct ((w_is0 param || (sint32 pid <? 0)%Z)%bool) eqn:Hearly.
  { now apply check_ret_only_no_unmodeled in H. }
  cbv iota.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (copy_bytes_map (in_mem i) param 4) as [bs|] eqn:Hread.
  - apply record_copyins_unmodeled.
    destruct (negb (sched_targets_self_b pid m)) eqn:Hself.
    { cbv iota. apply unmodeled_intro. }
    cbv iota.
    destruct (sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                (bv_unsigned (le_bytes_to_word bs))) as [r|] eqn:Hans.
    + now apply check_ret_only_copyins_no_unmodeled in H.
    + apply unmodeled_intro.
  - destruct (negb (access_okb param 4)) eqn:Hacc.
    + now apply check_ret_only_no_unmodeled in H.
    + apply unmodeled_intro.
Qed.

Lemma check_sched_setscheduler_complete_ok :
  forall i pid policy param eff m m' evs,
  sched_setscheduler_spec pid policy param i m (Ok eff m' evs) ->
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs.
Proof.
  intros i pid policy param eff m m' evs H.
  unfold sched_setscheduler_spec in H. unfold check_sched_setscheduler.
  destruct ((sint32 policy <? 0)%Z) eqn:Hpolneg.
  { cbv iota in H. unfold err_ret, ret_only in H. inversion H; subst.
    now apply check_ret_only_ok_iff. }
  cbv iota in H.
  destruct ((w_is0 param || (sint32 pid <? 0)%Z)%bool) eqn:Hearly.
  { cbv iota in H. unfold err_ret, ret_only in H. inversion H; subst.
    now apply check_ret_only_ok_iff. }
  cbv iota in H.
  apply bind_input_model_inv in H.
  destruct (copy_bytes_map (in_mem i) param 4) as [bs|] eqn:Hread.
  - apply record_copyins_ok_inv in H as (core & Hcore & ->).
    destruct (negb (sched_targets_self_b pid m)) eqn:Hself.
    { cbv iota in Hcore. discriminate Hcore. }
    cbv iota in Hcore.
    destruct (sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                (bv_unsigned (le_bytes_to_word bs))) as [r|] eqn:Hans.
    + unfold ret_only in Hcore. inversion Hcore; subst.
      apply check_ret_only_copyins_ok_iff. now repeat split.
    + discriminate Hcore.
  - destruct (negb (access_okb param 4)) eqn:Hacc.
    + unfold err_ret, ret_only in H. inversion H; subst.
      now apply check_ret_only_ok_iff.
    + discriminate H.
Qed.

Lemma check_sched_setscheduler_complete_unmodeled :
  forall i pid policy param eff m,
  sched_setscheduler_spec pid policy param i m Unmodeled ->
  check_sched_setscheduler i pid policy param eff m = CheckUnmodeled.
Proof.
  intros i pid policy param eff m H.
  unfold sched_setscheduler_spec in H. unfold check_sched_setscheduler.
  destruct ((sint32 policy <? 0)%Z) eqn:Hpolneg.
  { cbv iota in H. unfold err_ret, ret_only in H. discriminate H. }
  cbv iota in H.
  destruct ((w_is0 param || (sint32 pid <? 0)%Z)%bool) eqn:Hearly.
  { cbv iota in H. unfold err_ret, ret_only in H. discriminate H. }
  cbv iota in H.
  apply bind_input_model_inv in H.
  destruct (copy_bytes_map (in_mem i) param 4) as [bs|] eqn:Hread.
  - apply record_copyins_unmodeled_inv in H.
    destruct (negb (sched_targets_self_b pid m)) eqn:Hself; [reflexivity|].
    cbv iota in H.
    destruct (sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                (bv_unsigned (le_bytes_to_word bs))) as [r|] eqn:Hans;
      [|reflexivity].
    unfold ret_only in H. discriminate H.
  - destruct (negb (access_okb param 4)) eqn:Hacc; [|reflexivity].
    unfold err_ret, ret_only in H. discriminate H.
Qed.

(** [sched_yield] (124): 0, no writes, no state change, no events, and
    nothing else admitted.  Mirrors
    [Kernel.Sched.Syscalls.sched_yield_spec], which is where the reading
    of [SYSCALL_DEFINE0(sched_yield)] lives — above all why ignoring
    every argument word is exact here rather than an approximation.  The
    arm has no decline at all, which is what the two [_unmodeled]
    obligations below come to. *)
Definition check_sched_yield (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_ret_only eff (Z_to_bv 64 0) m [].

Lemma check_sched_yield_sound_ok : forall eff m m' evs i,
  check_sched_yield eff m = CheckOk m' evs ->
  sched_yield_spec i m (Ok eff m' evs).
Proof.
  intros eff m m' evs i H.
  unfold check_sched_yield in H. unfold sched_yield_spec.
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  unfold ret_only. apply pure_ok.
Qed.

(** Vacuously: the checker never declines, so there is no answer to
    carry over.  That is the honest shape for an arm with no
    fail-closed branch — see [check_sched_yield_complete_unmodeled] for
    the direction that has content. *)
Lemma check_sched_yield_sound_unmodeled : forall eff m i,
  check_sched_yield eff m = CheckUnmodeled -> sched_yield_spec i m Unmodeled.
Proof.
  intros eff m i H. unfold check_sched_yield in H.
  now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_sched_yield_complete_ok : forall eff m m' evs i,
  sched_yield_spec i m (Ok eff m' evs) -> check_sched_yield eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H.
  unfold sched_yield_spec in H. unfold check_sched_yield.
  unfold ret_only in H. inversion H; subst.
  now apply check_ret_only_ok_iff.
Qed.

(** The spec has no [Unmodeled] outcome either, so this side is the one
    that says so: [sched_yield_spec] going unmodeled is impossible, and
    the proof is the impossibility rather than an appeal to the
    checker. *)
Lemma check_sched_yield_complete_unmodeled : forall m i eff,
  sched_yield_spec i m Unmodeled -> check_sched_yield eff m = CheckUnmodeled.
Proof.
  intros m i eff H.
  unfold sched_yield_spec in H. unfold ret_only in H. discriminate H.
Qed.
