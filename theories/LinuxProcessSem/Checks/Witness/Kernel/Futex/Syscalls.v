(** * LinuxProcessSem.Checks.Witness.Kernel.Futex.Syscalls — the futex (98) and set_robust_list (99) witnesses

    Mirrors [Sys/Kernel/Futex/Syscalls.v], which answers to Linux
    [kernel/futex/syscalls.c]: this file holds the witnesses for the
    syscalls defined there, and no others.

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

Definition set_robust_list_witness (m : Model) : outcome SyscallEffect :=
  ret_outcome (errno_ret ENOSYS) m.

Lemma set_robust_list_witness_ok : forall len i m,
  set_robust_list_spec len i m (set_robust_list_witness m).
Proof.
  intros. unfold set_robust_list_spec, set_robust_list_witness.
  apply alt_l. unfold err_ret, ret_only, ret_outcome. apply pure_ok.
Qed.

(** The gate is written out for the third time; [Checks/Sys/Fs/Timerfd]
    says why the three layers restate it rather than share one
    predicate.

    [Unmodeled] IS an admissible outcome, so the declined halves need no
    invented answer — the spec's own arm is [unmodeled], and exhibiting
    it is what makes this total.  [timerfd_create_witness] takes the
    same shape for the same reason.  Every arm of this spec is a single
    answer rather than a choice, so the witness is the spec read back:
    there is no environment nondeterminism here for it to pick a member
    of. *)
Definition futex_witness (uaddr op val utime : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  then (if negb (Z.eqb (bv_unsigned uaddr mod FUTEX_WORD_SIZE) 0)
        then ret_outcome (errno_ret EINVAL) m
        else if negb (access_okb uaddr FUTEX_WORD_SIZE)
        then ret_outcome (errno_ret EFAULT) m
        else ret_outcome (Z_to_bv 64 0) m)
  else if bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
  then (if negb (w_is0 utime) then Unmodeled
        else if negb (Z.eqb (bv_unsigned uaddr mod FUTEX_WORD_SIZE) 0)
        then ret_outcome (errno_ret EINVAL) m
        else if negb (access_okb uaddr FUTEX_WORD_SIZE)
        then ret_outcome (errno_ret EFAULT) m
        else
          match read_bytes_map (in_mem i) uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) with
          | None => Unmodeled
          | Some uval =>
              if bv_eqb (le_bytes_to_word uval) (abi_low32 val) then Unmodeled
              else Ok (with_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
                        (mkEffect (errno_ret EAGAIN) [] [])) m []
          end)
  else Unmodeled.

Lemma futex_witness_ok : forall uaddr op val utime i m,
  futex_spec uaddr op val utime i m (futex_witness uaddr op val utime i m).
Proof.
  intros uaddr op val utime i m.
  unfold futex_spec, futex_witness,
         futex_wake_private_spec, futex_wait_private_spec,
         futex_key_check, futex_aligned_b.
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)).
  { destruct (Z.eqb (bv_unsigned uaddr mod FUTEX_WORD_SIZE) 0),
             (access_okb uaddr FUTEX_WORD_SIZE);
      cbn [negb]; cbv iota; apply pure_ok. }
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)); [|apply unmodeled_intro].
  destruct (negb (w_is0 utime)); [apply unmodeled_intro|].
  destruct (Z.eqb (bv_unsigned uaddr mod FUTEX_WORD_SIZE) 0),
           (access_okb uaddr FUTEX_WORD_SIZE);
    cbn [negb]; cbv iota; try apply pure_ok.
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_mem i) uaddr (Z_to_bv 64 FUTEX_WORD_SIZE))
    as [uval|]; cbv iota; [|apply unmodeled_intro].
  destruct (bv_eqb (le_bytes_to_word uval) (abi_low32 val)); cbv iota.
  - apply record_copyins_unmodeled. apply unmodeled_intro.
  - apply (record_copyins_ok_empty _ _ _ _ (mkEffect (errno_ret EAGAIN) [] []));
      [reflexivity|apply pure_ok].
Qed.
