(** * LinuxProcessSem.Checks.Sys.Kernel.Futex.Syscalls — the futex (98) and set_robust_list (99) checkers

    Mirrors [Sys/Kernel/Futex/Syscalls.v], which answers to Linux
    [kernel/futex/syscalls.c]: this file holds the checkers for the
    syscalls defined there, and no others.

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

(** Linux checks only [len]; QEMU user mode always returns -ENOSYS. *)
Definition check_set_robust_list (len : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if bv_eqb (eff_ret eff) (errno_ret ENOSYS) then
    check_ret_only eff (errno_ret ENOSYS) m []
  else if Z.eqb (bv_unsigned len) 24 then
    check_ret_only eff (Z_to_bv 64 0) m []
  else check_ret_only eff (errno_ret EINVAL) m [].

Lemma check_set_robust_list_sound_ok : forall len eff m m' evs i,
  check_set_robust_list len eff m = CheckOk m' evs ->
  set_robust_list_spec len i m (Ok eff m' evs).
Proof.
  intros len eff m m' evs i H.
  unfold check_set_robust_list in H.
  unfold set_robust_list_spec, alt.
  destruct (bv_eqb (eff_ret eff) (errno_ret ENOSYS)) eqn:Hr.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->).
    left. unfold err_ret, ret_only. apply pure_ok.
  - destruct (Z.eqb (bv_unsigned len) 24);
      apply check_ret_only_ok_iff in H as (-> & -> & ->);
      right; unfold err_ret, ret_only; apply pure_ok.
Qed.

Lemma check_set_robust_list_sound_unmodeled : forall len eff m i,
  check_set_robust_list len eff m = CheckUnmodeled ->
  set_robust_list_spec len i m Unmodeled.
Proof.
  intros len eff m i H. unfold check_set_robust_list in H.
  destruct (bv_eqb (eff_ret eff) (errno_ret ENOSYS));
    try destruct (Z.eqb (bv_unsigned len) 24);
    now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_set_robust_list_complete_ok : forall len eff m m' evs i,
  set_robust_list_spec len i m (Ok eff m' evs) ->
  check_set_robust_list len eff m = CheckOk m' evs.
Proof.
  intros len eff m m' evs i H.
  unfold set_robust_list_spec, alt in H.
  unfold check_set_robust_list.
  destruct H as [H|H].
  - unfold err_ret, ret_only, pure in H. inversion H; subst.
    cbn [eff_ret]. rewrite bv_eqb_refl.
    now apply check_ret_only_ok_iff.
  - destruct (Z.eqb (bv_unsigned len) 24) eqn:Hlen.
    + unfold ret_only, pure in H. inversion H; subst.
      cbn [eff_ret].
      change (bv_eqb (Z_to_bv 64 0) (errno_ret ENOSYS)) with false.
      now apply check_ret_only_ok_iff.
    + unfold err_ret, ret_only, pure in H. inversion H; subst.
      cbn [eff_ret].
      change (bv_eqb (errno_ret EINVAL) (errno_ret ENOSYS)) with false.
      now apply check_ret_only_ok_iff.
Qed.

Lemma check_set_robust_list_complete_unmodeled : forall len m i eff,
  set_robust_list_spec len i m Unmodeled ->
  check_set_robust_list len eff m = CheckUnmodeled.
Proof.
  intros len m i eff H.
  unfold set_robust_list_spec, alt in H.
  destruct H as [H|H];
    [unfold err_ret, ret_only, pure in H; discriminate|
     destruct (Z.eqb (bv_unsigned len) 24);
       unfold err_ret, ret_only, pure in H; discriminate].
Qed.

(** The two [get_futex_key] gates are WRITTEN OUT rather than taken from
    [Sys.Kernel.Futex.Syscalls.futex_aligned_b], and the four lemmas
    below are what make the repetition worth its cost: they force this
    statement and the spec's to coincide.  [Checks/Sys/Fs/Timerfd] says
    why the layers restate a gate instead of sharing one predicate, and
    what the repetition does NOT buy — an identical MISTAKE in both
    files still closes every proof.  These proofs do not show that the
    alignment really is the kernel's, or that -EFAULT really is the
    range verdict and not a page lookup. *)
Definition check_futex_wake_private (uaddr : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (Z.eqb (bv_unsigned uaddr mod FUTEX_WORD_SIZE) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (access_okb uaddr FUTEX_WORD_SIZE)
  then check_ret_only eff (errno_ret EFAULT) m []
  else check_ret_only eff (Z_to_bv 64 0) m [].

(** The wait arm's accepting answer carries the four-byte ledger the
    spec records, so it is [check_ret_only_copyins] rather than
    [check_ret_only]: plain [check_ret_only] would insist the ledger be
    empty and reject the truthful effect.  The two gate answers use the
    plain form, because nothing was read on either. *)
Definition check_futex_wait_private (i : SyscallInput) (uaddr val : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (Z.eqb (bv_unsigned uaddr mod FUTEX_WORD_SIZE) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (access_okb uaddr FUTEX_WORD_SIZE)
  then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map (in_mem i) uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) with
    | None => CheckUnmodeled
    | Some uval =>
        if bv_eqb (le_bytes_to_word uval) val then CheckUnmodeled
        else check_ret_only_copyins [(uaddr, FUTEX_WORD_SIZE_nat)] eff
               (errno_ret EAGAIN) m []
    end.

Definition check_futex (i : SyscallInput) (uaddr op val utime : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)
  then check_futex_wake_private uaddr eff m
  else if bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)
  then (if negb (w_is0 utime) then CheckUnmodeled
        else check_futex_wait_private i uaddr (abi_low32 val) eff m)
  else CheckUnmodeled.

(** Both sides of every proof below branch on the same two booleans, in
    the same order.  Splitting them rather than the assembled condition
    keeps the tactic from depending on the two files spelling the gate
    the same way, which is the coincidence the restatement exists to
    avoid relying on. *)
Ltac futex_gate uaddr :=
  unfold futex_key_check, futex_aligned_b in *;
  destruct (Z.eqb (bv_unsigned uaddr mod FUTEX_WORD_SIZE) 0),
           (access_okb uaddr FUTEX_WORD_SIZE);
  cbn [negb] in *.

Lemma check_futex_wake_private_sound_ok : forall uaddr eff m m' evs i,
  check_futex_wake_private uaddr eff m = CheckOk m' evs ->
  futex_wake_private_spec uaddr i m (Ok eff m' evs).
Proof.
  intros uaddr eff m m' evs i H.
  unfold check_futex_wake_private in H. unfold futex_wake_private_spec.
  futex_gate uaddr; cbv iota;
    apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
    apply pure_ok.
Qed.

Lemma check_futex_wake_private_sound_unmodeled : forall uaddr eff m i,
  check_futex_wake_private uaddr eff m = CheckUnmodeled ->
  futex_wake_private_spec uaddr i m Unmodeled.
Proof.
  intros uaddr eff m i H.
  unfold check_futex_wake_private in H.
  futex_gate uaddr; now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_futex_wake_private_complete_ok : forall uaddr eff m m' evs i,
  futex_wake_private_spec uaddr i m (Ok eff m' evs) ->
  check_futex_wake_private uaddr eff m = CheckOk m' evs.
Proof.
  intros uaddr eff m m' evs i H.
  unfold futex_wake_private_spec in H. unfold check_futex_wake_private.
  futex_gate uaddr; cbv iota in H |- *;
    sys_unfold; inv_ok; apply check_ret_only_ok_iff; auto.
Qed.

Lemma check_futex_wake_private_complete_unmodeled : forall uaddr m i eff,
  futex_wake_private_spec uaddr i m Unmodeled ->
  check_futex_wake_private uaddr eff m = CheckUnmodeled.
Proof.
  intros uaddr m i eff H.
  unfold futex_wake_private_spec in H. unfold check_futex_wake_private.
  futex_gate uaddr; cbv iota in H; unfold err_ret, ret_only, pure in H;
    discriminate.
Qed.

Lemma check_futex_wait_private_sound_ok : forall i uaddr val eff m m' evs,
  check_futex_wait_private i uaddr val eff m = CheckOk m' evs ->
  futex_wait_private_spec uaddr val i m (Ok eff m' evs).
Proof.
  intros i uaddr val eff m m' evs H.
  unfold check_futex_wait_private in H. unfold futex_wait_private_spec.
  futex_gate uaddr; cbv iota; cbv iota in H;
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         apply pure_ok).
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_mem i) uaddr (Z_to_bv 64 FUTEX_WORD_SIZE))
    as [uval|] eqn:Hr; cbv iota; cbv iota in H; [|discriminate].
  destruct (bv_eqb (le_bytes_to_word uval) val) eqn:Hv;
    cbv iota; cbv iota in H; [discriminate|].
  apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
  apply record_copyins_ok_empty; [reflexivity|]. apply pure_ok.
Qed.

Lemma check_futex_wait_private_sound_unmodeled : forall i uaddr val eff m,
  check_futex_wait_private i uaddr val eff m = CheckUnmodeled ->
  futex_wait_private_spec uaddr val i m Unmodeled.
Proof.
  intros i uaddr val eff m H.
  unfold check_futex_wait_private in H. unfold futex_wait_private_spec.
  futex_gate uaddr; cbv iota; cbv iota in H;
    try (now apply check_ret_only_no_unmodeled in H).
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_mem i) uaddr (Z_to_bv 64 FUTEX_WORD_SIZE))
    as [uval|] eqn:Hr; cbv iota; cbv iota in H; [|apply unmodeled_intro].
  destruct (bv_eqb (le_bytes_to_word uval) val) eqn:Hv;
    cbv iota; cbv iota in H;
    [apply record_copyins_unmodeled; apply unmodeled_intro
    |now apply check_ret_only_copyins_no_unmodeled in H].
Qed.

Lemma check_futex_wait_private_complete_ok : forall i uaddr val eff m m' evs,
  futex_wait_private_spec uaddr val i m (Ok eff m' evs) ->
  check_futex_wait_private i uaddr val eff m = CheckOk m' evs.
Proof.
  intros i uaddr val eff m m' evs H.
  unfold futex_wait_private_spec in H. unfold check_futex_wait_private.
  futex_gate uaddr; cbv iota in H |- *;
    try (sys_unfold; inv_ok; apply check_ret_only_ok_iff; auto).
  apply input_bind_ok_inv in H. cbv beta in H.
  destruct (read_bytes_map (in_mem i) uaddr (Z_to_bv 64 FUTEX_WORD_SIZE))
    as [uval|] eqn:Hr; cbv iota in H |- *;
    [|unfold unmodeled in H; discriminate].
  apply record_copyins_ok_inv in H. destruct H as (core & Hcore & ->).
  destruct (bv_eqb (le_bytes_to_word uval) val) eqn:Hv;
    cbv iota in Hcore |- *; [unfold unmodeled in Hcore; discriminate|].
  unfold err_ret, ret_only, pure in Hcore. inversion Hcore; subst.
  cbn [eff_copyins with_copyins app]. apply check_ret_only_copyins_refl.
Qed.

Lemma check_futex_wait_private_complete_unmodeled : forall i uaddr val m eff,
  futex_wait_private_spec uaddr val i m Unmodeled ->
  check_futex_wait_private i uaddr val eff m = CheckUnmodeled.
Proof.
  intros i uaddr val m eff H.
  unfold futex_wait_private_spec in H. unfold check_futex_wait_private.
  futex_gate uaddr; cbv iota in H |- *;
    try (unfold err_ret, ret_only, pure in H; discriminate).
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  destruct (read_bytes_map (in_mem i) uaddr (Z_to_bv 64 FUTEX_WORD_SIZE))
    as [uval|] eqn:Hr; cbv iota in H |- *; [|reflexivity].
  apply record_copyins_unmodeled_inv in H.
  destruct (bv_eqb (le_bytes_to_word uval) val) eqn:Hv;
    cbv iota in H |- *; [reflexivity|].
  unfold err_ret, ret_only, pure in H. discriminate.
Qed.

(** The op word is tested WHOLE, so the three arms are disjoint by
    construction and each of the four lemmas is one [destruct] over the
    two equalities followed by the matching arm's lemma. *)
Lemma check_futex_sound_ok : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs ->
  futex_spec uaddr op val utime i m (Ok eff m' evs).
Proof.
  intros i uaddr op val utime eff m m' evs H.
  unfold check_futex in H. unfold futex_spec.
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE));
    [now apply check_futex_wake_private_sound_ok|].
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)); [|discriminate].
  destruct (negb (w_is0 utime)); [discriminate|].
  now apply check_futex_wait_private_sound_ok.
Qed.

Lemma check_futex_sound_unmodeled : forall i uaddr op val utime eff m,
  check_futex i uaddr op val utime eff m = CheckUnmodeled ->
  futex_spec uaddr op val utime i m Unmodeled.
Proof.
  intros i uaddr op val utime eff m H.
  unfold check_futex in H. unfold futex_spec.
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE));
    [now apply check_futex_wake_private_sound_unmodeled with (eff := eff)|].
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)); [|apply unmodeled_intro].
  destruct (negb (w_is0 utime)); [apply unmodeled_intro|].
  now apply check_futex_wait_private_sound_unmodeled with (eff := eff).
Qed.

Lemma check_futex_complete_ok : forall i uaddr op val utime eff m m' evs,
  futex_spec uaddr op val utime i m (Ok eff m' evs) ->
  check_futex i uaddr op val utime eff m = CheckOk m' evs.
Proof.
  intros i uaddr op val utime eff m m' evs H.
  unfold futex_spec in H. unfold check_futex.
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE));
    [now apply check_futex_wake_private_complete_ok with (i := i)|].
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE));
    [|unfold unmodeled in H; discriminate].
  destruct (negb (w_is0 utime)); [unfold unmodeled in H; discriminate|].
  now apply check_futex_wait_private_complete_ok.
Qed.

Lemma check_futex_complete_unmodeled : forall i uaddr op val utime m eff,
  futex_spec uaddr op val utime i m Unmodeled ->
  check_futex i uaddr op val utime eff m = CheckUnmodeled.
Proof.
  intros i uaddr op val utime m eff H.
  unfold futex_spec in H. unfold check_futex.
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE));
    [now apply check_futex_wake_private_complete_unmodeled with (i := i)|].
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)); [|reflexivity].
  destruct (negb (w_is0 utime)); [reflexivity|].
  now apply check_futex_wait_private_complete_unmodeled.
Qed.

(** Every answered [futex] carries the ledger [futex_wait_reads_b]
    predicts, and no other.

    Stated over [Ok] outcomes only, which is exactly the question a
    user of the checker asks: it builds an effect for a call the kernel
    really made and asks which ranges to claim.  The one shape where the two could still
    part company is a WAIT whose word the model cannot read — the
    predicate is true and the spec answers [Unmodeled] — and there the
    verdict does not depend on the effect at all, because
    [Checks.Sys.Kernel.Futex.Syscalls.check_futex] answers
    [CheckUnmodeled] before it looks at one. *)
Lemma futex_copyins_exact : forall uaddr op val utime i m eff m' evs,
  futex_spec uaddr op val utime i m (Ok eff m' evs) ->
  eff_copyins eff =
    (if futex_wait_reads_b uaddr op utime
     then [(uaddr, FUTEX_WORD_SIZE_nat)] else []).
Proof.
  intros uaddr op val utime i m eff m' evs H.
  unfold futex_spec, futex_wait_reads_b in *.
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE)) eqn:Hwake;
    cbv iota in H.
  { rewrite (futex_wake_not_wait op Hwake). cbn [andb].
    unfold futex_wake_private_spec, futex_key_check, err_ret, ret_only,
           pure in H.
    destruct (negb (futex_aligned_b uaddr)), (negb (access_okb uaddr FUTEX_WORD_SIZE));
      cbv iota in H; inversion H; reflexivity. }
  destruct (bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE)) eqn:Hwait;
    cbv iota in H; [|unfold unmodeled in H; discriminate].
  cbn [andb].
  destruct (w_is0 utime) eqn:Hu; cbn [negb andb] in H |- *;
    [|unfold unmodeled in H; discriminate].
  unfold futex_wait_private_spec, futex_key_check in H.
  destruct (futex_aligned_b uaddr) eqn:Ha; cbn [negb andb] in H |- *;
    [|cbv iota in H; unfold err_ret, ret_only, pure in H;
      inversion H; reflexivity].
  destruct (access_okb uaddr FUTEX_WORD_SIZE) eqn:Hok;
    cbn [negb andb] in H |- *;
    [|cbv iota in H; unfold err_ret, ret_only, pure in H;
      inversion H; reflexivity].
  cbv iota in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  destruct (read_bytes_map (in_mem i) uaddr (Z_to_bv 64 FUTEX_WORD_SIZE))
    as [uval|]; cbv iota in H; [|unfold unmodeled in H; discriminate].
  apply record_copyins_ok_inv in H. destruct H as (core & Hcore & ->).
  destruct (bv_eqb (le_bytes_to_word uval) (abi_low32 val)); cbv iota in Hcore;
    [unfold unmodeled in Hcore; discriminate|].
  unfold err_ret, ret_only, pure in Hcore. inversion Hcore; subst.
  reflexivity.
Qed.
