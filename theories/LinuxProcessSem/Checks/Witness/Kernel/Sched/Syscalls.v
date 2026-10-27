(** * LinuxProcessSem.Checks.Witness.Kernel.Sched.Syscalls — the sched_getaffinity (123), sched_setscheduler (119) and sched_yield (124) witnesses, and their proofs

    Mirrors [Sys/Kernel/Sched/Syscalls.v], which answers to Linux
    [kernel/sched/syscalls.c]: this file holds the witnesses for the
    syscalls defined there, and no others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.

(** [sched_getaffinity] (123) is deterministic on both branches, so the
    witness is the branch itself: the -EINVAL, or the [Unmodeled] every
    length the two gates let through answers.  Failing closed is an
    admissible outcome, which is what makes progress hold on the
    second. *)
Definition sched_getaffinity_witness (len : word) (m : Model)
    : outcome SyscallEffect :=
  if affinity_len_einval_b len then ret_outcome (errno_ret EINVAL) m
  else Unmodeled.

Lemma sched_getaffinity_witness_ok : forall len i m,
  sched_getaffinity_spec len i m (sched_getaffinity_witness len m).
Proof.
  intros. unfold sched_getaffinity_spec, sched_getaffinity_witness.
  destruct (affinity_len_einval_b len) eqn:Hlen.
  - unfold err_ret, ret_only. apply pure_ok.
  - apply unmodeled_intro.
Qed.

(** [sched_setscheduler] (119) is deterministic on every branch — it
    draws nothing and the one success changes no model state — so the
    witness is the branch itself, ledger included.  Failing closed is an
    admissible outcome, which is what makes progress hold on the four
    declines. *)
Definition sched_setscheduler_witness (pid policy param : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if (sint32 policy <? 0)%Z then ret_outcome (errno_ret EINVAL) m
  else if (w_is0 param || (sint32 pid <? 0)%Z)%bool
  then ret_outcome (errno_ret EINVAL) m
  else
  match user_read i m param (Z_to_bv 64 4) with
  | USpecial => Unmodeled
  | UFault =>
      if negb (access_okb param 4)
      then ret_outcome (errno_ret EFAULT) m
      else Unmodeled
  | UOk bs =>
      if negb (sched_targets_self_b pid m) then Unmodeled
      else
        match sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                (bv_unsigned (le_bytes_to_word bs)) with
        | Some r =>
            Ok (with_copyins [(param, 4%nat)] (mkEffect r [] [])) m []
        | None => Unmodeled
        end
  end.

Lemma sched_setscheduler_witness_ok : forall i pid policy param m,
  sched_setscheduler_spec pid policy param i m
    (sched_setscheduler_witness pid policy param i m).
Proof.
  intros. unfold sched_setscheduler_spec, sched_setscheduler_witness.
  destruct ((sint32 policy <? 0)%Z) eqn:Hpolneg;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  destruct ((w_is0 param || (sint32 pid <? 0)%Z)%bool) eqn:Hearly;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (user_read i m param (Z_to_bv 64 4)) as [bs| |] eqn:Hread.
  - destruct (negb (sched_targets_self_b pid m)) eqn:Hself;
      [apply record_copyins_unmodeled; apply unmodeled_intro|].
    destruct (sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                (bv_unsigned (le_bytes_to_word bs))) as [r|] eqn:Hans.
    + apply record_copyins_ok_empty; [reflexivity|]. apply pure_ok.
    + apply record_copyins_unmodeled; apply unmodeled_intro.
  - destruct (negb (access_okb param 4)) eqn:Hacc;
      [unfold err_ret, ret_only, ret_outcome; apply pure_ok
      |apply unmodeled_intro].
  - apply unmodeled_intro.
Qed.

(** [sched_yield] (124) has one outcome and no branch at all, so the
    witness is that outcome.  It is also the only arm here whose witness
    is never [Unmodeled]: the spec has no fail-closed branch to exhibit
    (see [Kernel.Sched.Syscalls.sched_yield_spec]). *)
Definition sched_yield_witness (m : Model) : outcome SyscallEffect :=
  ret_outcome (Z_to_bv 64 0) m.

Lemma sched_yield_witness_ok : forall i m,
  sched_yield_spec i m (sched_yield_witness m).
Proof.
  intros. unfold sched_yield_spec, sched_yield_witness.
  unfold ret_only, ret_outcome. apply pure_ok.
Qed.
