(** * LinuxProcessSem.Checks.Cases.Kernel.Futex.Syscalls — worked examples over futex (98)

    Mirrors [Sys/Kernel/Futex/Syscalls.v], which answers to Linux
    [kernel/futex/syscalls.c]: this file holds the worked examples for
    the syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** THREE ANSWERS AND NO FOURTH, for every address at once.

    ADMISSION REASON: universally quantified.  A run can reach each of
    the three on one address apiece; what no set of traces can show is
    that there is
    no address at all for which a private wake answers something else.
    The statement also pins two things a program's view of a return value
    does not reveal: the model that comes back is the SAME model, and the
    event list is empty — a wake is inert.

    Read the disjunction as [get_futex_key]'s two refusals
    (kernel/futex/core.c) followed by the count [futex_wake]
    (kernel/futex/waitwake.c) returns, which is 0 because the waiter set
    of a private key is empty here (the spec's header argues it).  That
    the count is 0 rather than the errno of an unresolvable page is the
    content: no arm of this disjunction depends on what is mapped. *)
Lemma futex_wake_private_answers : forall uaddr i m eff m' evs,
  futex_wake_private_spec uaddr i m (Ok eff m' evs) ->
  m' = m /\ evs = [] /\
  (eff = mkEffect (errno_ret EINVAL) [] []
   \/ eff = mkEffect (errno_ret EFAULT) [] []
   \/ eff = mkEffect (Z_to_bv 64 0) [] []).
Proof.
  intros uaddr i m eff m' evs H.
  unfold futex_wake_private_spec, futex_key_check, err_ret, ret_only,
         pure in H.
  destruct (negb (futex_aligned_b uaddr)),
           (negb (access_okb uaddr FUTEX_WORD_SIZE));
    cbv iota in H; inversion H; subst; repeat split; auto.
Qed.

(** A WAIT NEVER SUCCEEDS, for every address and every expected value at
    once.

    ADMISSION REASON: universally quantified, and the same two
    model-internal facts.  A private [FUTEX_WAIT] this model answers has
    exactly one non-gate answer, -EAGAIN, and it carries the four-byte
    copy-in — so a run in which the wait slept and was woken, which is
    what a 0 return means ([__futex_wait] reaches its [return 0] only
    after [futex_unqueue] finds the entry already dequeued), is not an
    outcome this spec admits on any input.  That is the claim the
    single-task argument rests on, stated where it can be checked: there
    is no address on which a 0 would be accepted. *)
Lemma futex_wait_private_answers : forall uaddr val i m eff m' evs,
  futex_wait_private_spec uaddr val i m (Ok eff m' evs) ->
  m' = m /\ evs = [] /\
  (eff = mkEffect (errno_ret EINVAL) [] []
   \/ eff = mkEffect (errno_ret EFAULT) [] []
   \/ eff = with_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
              (mkEffect (errno_ret EAGAIN) [] [])).
Proof.
  intros uaddr val i m eff m' evs H.
  unfold futex_wait_private_spec, futex_key_check in H.
  destruct (negb (futex_aligned_b uaddr)),
           (negb (access_okb uaddr FUTEX_WORD_SIZE));
    cbv iota in H;
    try (unfold err_ret, ret_only, pure in H; inversion H; subst;
         repeat split; auto; fail).
  apply bind_input_model_inv in H.
  destruct (user_read i m uaddr (Z_to_bv 64 FUTEX_WORD_SIZE))
    as [uval| |]; cbv iota in H;
    [|unfold unmodeled in H; discriminate|unfold unmodeled in H; discriminate].
  apply record_copyins_ok_inv in H. destruct H as (core & Hcore & ->).
  destruct (bv_eqb (le_bytes_to_word uval) val); cbv iota in Hcore;
    [unfold unmodeled in Hcore; discriminate|].
  unfold err_ret, ret_only, pure in Hcore. inversion Hcore; subst.
  repeat split; auto.
Qed.

(** NO CLONE GATE EVER GRANTS [CLONE_VM], which is the one cross-file
    premise the answers above rest on.

    ADMISSION REASON: universally quantified, and about a syscall this
    file does not otherwise concern itself with.  [futex_wake_private_spec]
    answers 0 because no task shares the caller's mm, and the reason no
    task does is that [Kernel.Fork]'s two gates admit one flag word each
    and neither sets the bit.  That is an argument across two files, so
    it is exactly the kind that rots silently: a later change widening
    [clone] to a flag MASK, or adding a second admitted word, would leave
    every futex proof closing and the count wrong.

    These two make the premise a compile-time fact instead.  Widening
    either gate to admit [CLONE_VM] breaks the build HERE, next to the
    prose that says why it matters, rather than nowhere. *)
Lemma clone_fork_gate_grants_no_shared_mm : forall flags,
  clone_fork_flags_b flags = true ->
  Z.land (bv_unsigned flags) CLONE_VM = 0%Z.
Proof.
  intros flags H. unfold clone_fork_flags_b, bv_eqb in H.
  apply Z.eqb_eq in H. rewrite H. vm_compute. reflexivity.
Qed.

Lemma clone3_fork_gate_grants_no_shared_mm : forall bs,
  clone3_fork_args_b bs = true ->
  Z.land (bv_unsigned (clone_args_field bs 0)) CLONE_VM = 0%Z.
Proof.
  intros bs H. unfold clone3_fork_args_b in H.
  repeat (apply andb_true_iff in H as [H ?]).
  unfold w_is0, bv_eqb in H. apply Z.eqb_eq in H. rewrite H.
  vm_compute. reflexivity.
Qed.
