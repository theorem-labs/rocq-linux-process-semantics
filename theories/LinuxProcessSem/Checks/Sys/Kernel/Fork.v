(** * LinuxProcessSem.Checks.Sys.Kernel.Fork — the set_tid_address (96), clone (220) and clone3 (435) checkers, and their proofs

    Mirrors [Sys/Kernel/Fork.v], which answers to Linux [kernel/fork.c]:
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
  Prelude Fs.ReadWrite.

Definition check_set_tid_address (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      match m_tid m with
      | Some tid => if bv_eqb ret tid then CheckOk m [] else CheckReject
      | None =>
          if (0 <? bv_unsigned ret)%Z &&
             (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z
          then CheckOk (with_tid ret m) [] else CheckReject
      end
  | _ => CheckReject
  end.

Lemma check_set_tid_address_sound_ok : forall eff m m' evs i,
  check_set_tid_address eff m = CheckOk m' evs ->
  set_tid_address_spec i m (Ok eff m' evs).
Proof.
  intros [ret ws zs us cs copyins] m m' evs i H.
  unfold check_set_tid_address in H. unfold set_tid_address_spec.
  destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  destruct (m_tid m) as [tid|] eqn:Htid.
  - destruct (bv_eqb ret tid) eqn:Hr; [|discriminate].
    apply bv_eqb_eq in Hr. inversion H; clear H; subst.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta.
    srw Htid. apply pure_ok.
  - destruct ((0 <? bv_unsigned ret)%Z &&
              (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)
      eqn:Hvalid; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hvalid as [Hlo Hhi].
    apply Z.ltb_lt in Hlo. apply Z.ltb_lt in Hhi.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta.
    srw Htid.
    eapply bind_ok0.
    { apply (choose_ok _ ret). lia. }
    eapply bind_ok0; [apply modify_ok|].
    apply pure_ok.
Qed.

Lemma check_set_tid_address_sound_unmodeled : forall eff m i,
  check_set_tid_address eff m = CheckUnmodeled -> set_tid_address_spec i m Unmodeled.
Proof.
  intros [ret ws zs us cs copyins] m i H. unfold check_set_tid_address in H.
  destruct ws;
    [destruct zs;
      [destruct us;
        [destruct cs;
          [destruct copyins;
            [destruct (m_tid m) as [tid|];
            [destruct (bv_eqb ret tid)
            |destruct ((0 <? bv_unsigned ret)%Z &&
                       (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)]|]|]|]|]|];
    discriminate.
Qed.

Lemma check_set_tid_address_complete_ok : forall eff m m' evs i,
  set_tid_address_spec i m (Ok eff m' evs) ->
  check_set_tid_address eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H.
  unfold set_tid_address_spec in H. unfold check_set_tid_address.
  destruct (m_tid m) as [tid|] eqn:Htid; sys_unfold; inv_ok;
    hall Htid; inv_ok; cbv iota.
  - bool_true; reflexivity.
  - match goal with
    | Hlo : (0 < ?r)%Z, Hhi : (?r < PID_MAX_ENVELOPE)%Z
      |- context [(0 <? ?r)%Z && (?r <? PID_MAX_ENVELOPE)%Z] =>
        rewrite (proj2 (Z.ltb_lt 0 r) Hlo),
                (proj2 (Z.ltb_lt r PID_MAX_ENVELOPE) Hhi);
        reflexivity
    end.
Qed.

Lemma check_set_tid_address_complete_unmodeled : forall m i eff,
  set_tid_address_spec i m Unmodeled -> check_set_tid_address eff m = CheckUnmodeled.
Proof.
  intros m i eff H.
  unfold set_tid_address_spec in H.
  destruct (m_tid m) as [tid|] eqn:Htid; sys_unfold; inv_ok;
    hall Htid; inv_ok; discriminate.
Qed.

(* ----------------------------------------------------------- clone/clone3 *)

(** clone / clone3: no writes; only the success arm updates the model.  The two arms of
    [Fork.clone_resolve] are disjoint on the observed return — every
    admissible pid is below [PID_MAX_ENVELOPE] and every member of
    [Fork.clone_errnos] reads as an unsigned value just under 2^64 — so
    this is a function of the return rather than a choice.  A return of
    0 falls through both tests to [CheckReject]: it is the CHILD's
    answer, and [Fork.clone_spec]'s header says why that is a decision.
    See [Checks.ProcessCreation.clone_never_returns_zero]. *)
(** The admitted ANSWER, shared by both entry points so the pid envelope
    and the errno set cannot drift between them.  The two differ only in
    the copy-in ledger they require, which is the whole observable
    difference between [clone] and [clone3]. *)
(** The success arm records the child in the model the caller keeps
    ([Kernel.Fork.forfeit_model]: each live inherited descriptor without
    its offset), mirroring [Kernel.Fork.clone_resolve]'s success branch.
    The errno arm returns [m] unchanged: it created nothing. *)
Definition check_clone_answer (ret : word) (m : Model) : check_result :=
  if errno_ret_in clone_errnos ret then CheckOk m []
  else if clone_pid_ok_b m ret then CheckOk (with_child ret (forfeit_model m)) []
  else CheckReject.

Definition check_clone_resolve (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))) then CheckUnmodeled
  else match eff with
  | mkEffectU ret [] [] [] [] [] => check_clone_answer ret m
  | _ => CheckReject
  end.

(** [clone3] read [CLONE_ARGS_SIZE] bytes at [uargs] before resolving, so
    its effect must carry exactly that range and no other.  An empty
    ledger here is not a harmless omission: it is a claim that the call
    read no user memory, which would let the model admit an allocation
    the kernel refuses.  The descriptor gate is tested FIRST, so a model
    the resolution declines answers [CheckUnmodeled] whatever ledger the
    effect carries. *)
Definition check_clone3_resolve (uargs : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))) then CheckUnmodeled
  else match eff with
  | mkEffectU ret [] [] [] [] ((a, n) :: nil) =>
      if bv_eqb a uargs && Nat.eqb n CLONE_ARGS_SIZE_nat
      then check_clone_answer ret m
      else CheckReject
  | _ => CheckReject
  end.

(** The namespace word's answer: an error-encoded return other than
    -EINTR ([errno_any_b], the acceptor of [Syscall.errno_any], which
    excludes -EINTR) leaves the model alone, and an admissible pid
    records the child in the model the caller keeps
    ([Kernel.Fork.forfeit_model]: each live inherited descriptor without
    its offset), mirroring [Kernel.Fork.clone_ns_resolve].  The
    two are disjoint on the observed return ([clone_pid_not_error]), so
    this too is a function of the return rather than a choice.  Keyed on
    [addr_is_error_b] instead, the soundness proof below would fail: it
    would accept a -EINTR the spec no longer admits. *)
Definition check_clone_ns_answer (ret : word) (m : Model) : check_result :=
  if errno_any_b ret then CheckOk m []
  else if clone_pid_ok_b m ret then CheckOk (with_child ret (forfeit_model m)) []
  else CheckReject.

Definition check_clone_ns_resolve (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))) then CheckUnmodeled
  else match eff with
  | mkEffectU ret [] [] [] [] [] => check_clone_ns_answer ret m
  | _ => CheckReject
  end.

(** A word the argument checks refuse answers -EINVAL and nothing else,
    behind the descriptor gate ([Kernel.Fork.clone_einval]). *)
Definition check_clone_einval (eff : SyscallEffect) (m : Model)
    : check_result :=
  if clone_no_shared_file_b (forfeit_inherited (m_fds m))
  then check_ret_only eff (errno_ret EINVAL) m []
  else CheckUnmodeled.

(** [CLONE_NEWIPC] with [CLONE_SYSVSEM]: an errno other than -EINTR, the
    model as it was ([Kernel.Fork.clone_ns_refused]). *)
Definition check_clone_ns_refused (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))) then CheckUnmodeled
  else match eff with
  | mkEffectU ret [] [] [] [] [] => if errno_any_b ret then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

(** The effect a refusal of 220 leaves ([Kernel.Fork.clone_refused_fail]):
    an error-encoded return and nothing else.  [addr_is_error_b] accepts
    exactly the returns of the errnos from 1 to 4095
    ([addr_is_error_b_errno], [errno_ret_error_b]). *)
Definition clone_refused_eff_b (eff : SyscallEffect) : bool :=
  match eff with
  | mkEffectU ret [] [] [] [] [] => addr_is_error_b ret
  | _ => false
  end.

(** ...and of 435, which carries the struct's copy-in ledger
    ([Kernel.Fork.clone3_refused_fail]). *)
Definition clone3_refused_eff_b (uargs : word) (eff : SyscallEffect) : bool :=
  match eff with
  | mkEffectU ret [] [] [] [] ((a, n) :: nil) =>
      bv_eqb a uargs && Nat.eqb n CLONE_ARGS_SIZE_nat && addr_is_error_b ret
  | _ => false
  end.

(** [Kernel.Fork.clone_refusable] as a checker: at an answered call, with
    a refuser present and the descriptor gate open, a refusal's effect is
    accepted with the model unchanged; everything else is the lists'
    checker [r].  A refusal's effect the lists also accept (an errno of
    [Fork.clone_errnos]) gets the same answer from both, the model
    unchanged ([check_clone_lists_refused_shape]). *)
Definition check_refusable (answered refused_eff : bool) (m : Model)
    (r : check_result) : check_result :=
  if answered && clone_refused_b (m_clone_refusers m)
     && clone_no_shared_file_b (forfeit_inherited (m_fds m)) && refused_eff
  then CheckOk m [] else r.

(** [Kernel.Fork.clone_refusable_arm] as a checker, around the checker
    [inner] of the arm's body: every call of the arm counts as answered. *)
Definition check_refusable_arm (inner : SyscallEffect -> Model -> check_result)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_refusable true (clone_refused_eff_b eff) m (inner eff m).

(** The effect a body of [Kernel.Fork.clone_with_stores] gave, with the
    caller's [CLONE_PARENT_SETTID] store taken out: the store is appended
    only to a successful answer ([Kernel.Fork.tid_store_effect]), and the
    two bodies write nothing of their own. *)
Definition strip_tid_writes (eff : SyscallEffect) : SyscallEffect :=
  if addr_is_error_b (eff_ret eff) then eff
  else mkEffectU (eff_ret eff) [] (eff_zeros eff) (eff_unmaps eff) (eff_copies eff)
         (eff_copyins eff).

(** [Kernel.Fork.clone_with_stores]' checker, around the checker [inner]
    of its body: the stores decide first, then the body decides the
    stripped effect, and a successful answer must carry exactly the store
    [Kernel.Fork.tid_writes] gives. *)
Definition check_with_stores (i : SyscallInput) (r : CloneArgs)
    (inner : SyscallEffect -> Model -> check_result) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (clone_stores_ok i m r) then CheckUnmodeled
  else match inner (strip_tid_writes eff) m with
       | CheckOk m' evs =>
           if addr_is_error_b (eff_ret eff)
              || writes_eqb (eff_writes eff)
                   (tid_writes (in_wmem i) (clone_parent_tid r) (eff_ret eff))
           then CheckOk m' evs else CheckReject
       | res => res
       end.

(** [Kernel.Fork.clone_spec_lists], branch for branch: the record comes
    from the call's registers, as the spec decodes it. *)
Definition check_clone_lists (i : SyscallInput) (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if clone_fork_flags_b flags then check_clone_resolve eff m
  else if clone_ns_flags_b flags then check_clone_ns_resolve eff m
  else match clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) with
       | Some r =>
           if clone_arg_checks r then check_clone_einval eff m
           else match clone_class r with
                | CcFork => check_with_stores i r (check_refusable_arm check_clone_resolve) eff m
                | CcNs => check_with_stores i r (check_refusable_arm check_clone_ns_resolve) eff m
                | CcNsRefused => check_refusable_arm check_clone_ns_refused eff m
                | CcNone => CheckUnmodeled
                end
       | None => CheckUnmodeled
       end.

(** [clone3]'s -EINVAL carries the struct in its ledger
    ([Kernel.Fork.clone3_einval]). *)
Definition check_clone3_einval (uargs : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_ret_only_copyins [(uargs, CLONE_ARGS_SIZE_nat)] eff (errno_ret EINVAL) m [].

(** [Kernel.Fork.clone3_with_stores]: the struct in the ledger, and the
    rest decided on the effect with the ledger cleared. *)
Definition check_clone3_stores (i : SyscallInput) (uargs : word) (r : CloneArgs)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_copyins_after [(uargs, CLONE_ARGS_SIZE_nat)] eff
    (check_with_stores i r (check_refusable_arm check_clone_resolve) (clear_copyins eff) m).

(** A [uargs] range [access_ok] refuses is -EFAULT with an EMPTY ledger,
    asked through [State.copy_bytes_map] before the walk; one it admits
    that the memory does not wholly back declines (see
    [Fork.clone3_spec]). *)
Definition check_clone3_lists (i : SyscallInput) (uargs size : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)) then CheckUnmodeled
  else match copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE with
       | None =>
           if negb (access_okb uargs CLONE_ARGS_SIZE)
           then check_ret_only eff (errno_ret EFAULT) m []
           else CheckUnmodeled
       | Some bs =>
           if clone3_fork_args_b bs then check_clone3_resolve uargs eff m
           else if clone3_einval_b bs then check_clone3_einval uargs eff m
           else match clone3_pre bs with
                | CdArgs r =>
                    match clone_class r with
                    | CcFork => check_clone3_stores i uargs r eff m
                    | _ => CheckUnmodeled
                    end
                | _ => CheckUnmodeled
                end
       end.

(** [Kernel.Fork.clone_spec] and [Kernel.Fork.clone3_spec]: the lists'
    checkers, and a refusal's effect at the calls those specs' tests count
    as answered (the fork and namespace words, [clone3]'s fork image). *)
Definition check_clone (i : SyscallInput) (flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_refusable (clone_fork_flags_b flags || clone_ns_flags_b flags)
    (clone_refused_eff_b eff) m (check_clone_lists i flags eff m).

Definition check_clone3 (i : SyscallInput) (uargs size : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_refusable (clone3_answered_b uargs size i)
    (clone3_refused_eff_b uargs eff) m (check_clone3_lists i uargs size eff m).

(** No admissible pid can be mistaken for an admissible errno.  Every
    member of [Fork.clone_errnos] reads as an unsigned 64-bit value just
    under 2^64, and every pid the spec chooses is below
    [PID_MAX_ENVELOPE], so [errno_ret_in_below] separates them whatever
    the list holds.  This is what keeps [check_clone_resolve] a function
    of the observed return, for every [Model] rather than merely every
    reachable one. *)
Lemma clone_pid_not_errno : forall m (r : word),
  clone_pid_ok_b m r = true -> errno_ret_in clone_errnos r = false.
Proof.
  intros m r Hok.
  unfold clone_pid_ok_b in Hok.
  apply andb_true_iff in Hok as [Hrange _].
  apply andb_true_iff in Hrange as [_ Hhi]. apply Z.ltb_lt in Hhi.
  apply errno_ret_in_below; [reflexivity|].
  change PID_MAX_ENVELOPE with 4194304%Z in Hhi.
  unfold two_pow_64. lia.
Qed.

(** No admissible pid is error-encoded, which is what keeps
    [check_clone_ns_answer] a function of the observed return. *)
Lemma clone_pid_not_error : forall m (r : word),
  clone_pid_ok_b m r = true -> addr_is_error_b r = false.
Proof.
  intros m r Hok.
  unfold clone_pid_ok_b in Hok.
  apply andb_true_iff in Hok as [Hrange _].
  apply andb_true_iff in Hrange as [_ Hhi]. apply Z.ltb_lt in Hhi.
  unfold addr_is_error_b. apply Z.ltb_ge.
  change PID_MAX_ENVELOPE with 4194304%Z in Hhi.
  unfold two_pow_64. lia.
Qed.

(** Every word the namespace gate admits is [SIGCHLD] plus bits of
    [clone_ns_mask], so it shares no bit with any [b] that is disjoint
    from both.  The pins on what the gate keeps out
    ([Checks.ProcessCreation.clone_sharing_flags_unmodeled],
    [Checks.Cases.Kernel.Futex.Syscalls.clone_ns_gate_grants_no_shared_mm])
    are instances. *)
Lemma clone_ns_flags_disjoint : forall flags b,
  clone_ns_flags_b flags = true ->
  Z.land clone_ns_mask b = 0%Z -> Z.land SIGCHLD b = 0%Z ->
  Z.land (bv_unsigned flags) b = 0%Z.
Proof.
  intros flags b H Hm Hs. unfold clone_ns_flags_b in H.
  apply andb_true_iff in H as [H _]. apply Z.eqb_eq in H.
  rewrite <- (Z.land_m1_r (bv_unsigned flags)),
    <- (Z.lor_lnot_diag clone_ns_mask), Z.land_lor_distr_r, H,
    Z.land_lor_distr_l, <- Z.land_assoc, Hm, Hs, Z.land_0_r.
  reflexivity.
Qed.

Lemma check_clone_einval_sound_ok : forall eff m m' evs i,
  check_clone_einval eff m = CheckOk m' evs -> clone_einval i m (Ok eff m' evs).
Proof.
  intros eff m m' evs i H. unfold check_clone_einval in H. unfold clone_einval.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (clone_no_shared_file_b (forfeit_inherited (m_fds m)));
    cbv iota in H |- *; [|discriminate].
  apply check_ret_only_ok_iff in H as (-> & -> & ->).
  unfold err_ret, ret_only. apply pure_ok.
Qed.

Lemma check_clone_einval_sound_unmodeled : forall eff m i,
  check_clone_einval eff m = CheckUnmodeled -> clone_einval i m Unmodeled.
Proof.
  intros eff m i H. unfold check_clone_einval in H. unfold clone_einval.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (clone_no_shared_file_b (forfeit_inherited (m_fds m)));
    cbv iota in H |- *; [|apply unmodeled_intro].
  exfalso. exact (check_ret_only_no_unmodeled _ _ _ _ H).
Qed.

Lemma check_clone_einval_complete_ok : forall eff m m' evs i,
  clone_einval i m (Ok eff m' evs) -> check_clone_einval eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H. unfold clone_einval in H. unfold check_clone_einval.
  sys_unfold. cbv iota in H. inv_ok.
  destruct (clone_no_shared_file_b (forfeit_inherited (m_fds m))) eqn:Hg;
    hall Hg; inv_ok.
  apply check_ret_only_ok_iff. now repeat split.
Qed.

Lemma check_clone_einval_complete_unmodeled : forall m i eff,
  clone_einval i m Unmodeled -> check_clone_einval eff m = CheckUnmodeled.
Proof.
  intros m i eff H. unfold clone_einval in H. unfold check_clone_einval.
  sys_unfold. cbv iota in H. inv_ok.
  destruct (clone_no_shared_file_b (forfeit_inherited (m_fds m))) eqn:Hg;
    hall Hg; inv_ok; reflexivity.
Qed.

Lemma check_clone3_einval_sound_ok : forall uargs eff m m' evs i,
  check_clone3_einval uargs eff m = CheckOk m' evs ->
  clone3_einval uargs i m (Ok eff m' evs).
Proof.
  intros uargs eff m m' evs i H. unfold check_clone3_einval in H.
  apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
  unfold clone3_einval.
  apply record_copyins_ok_empty; [reflexivity|].
  unfold err_ret, ret_only. apply pure_ok.
Qed.

Lemma check_clone3_einval_complete_ok : forall uargs eff m m' evs i,
  clone3_einval uargs i m (Ok eff m' evs) ->
  check_clone3_einval uargs eff m = CheckOk m' evs.
Proof.
  intros uargs eff m m' evs i H. unfold clone3_einval in H.
  apply record_copyins_ok_inv in H as (core & Hc & ->).
  unfold err_ret, ret_only, pure in Hc. injection Hc as -> -> ->.
  unfold check_clone3_einval. exact (check_ret_only_copyins_refl _ _ _ _).
Qed.

Lemma clone3_einval_not_unmodeled : forall uargs i m,
  ~ clone3_einval uargs i m Unmodeled.
Proof.
  intros uargs i m H. unfold clone3_einval in H.
  apply record_copyins_unmodeled_inv in H.
  unfold err_ret, ret_only, pure in H. discriminate H.
Qed.

Lemma check_clone_ns_resolve_sound_ok : forall eff m m' evs i,
  check_clone_ns_resolve eff m = CheckOk m' evs ->
  clone_ns_resolve i m (Ok eff m' evs).
Proof.
  intros [ret ws zs us cs copyins] m m' evs i H.
  unfold check_clone_ns_resolve in H. unfold clone_ns_resolve.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    cbv iota; cbv iota in H; [discriminate|].
  destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  unfold check_clone_ns_answer in H.
  destruct (errno_any_b ret) eqn:He.
  { injection H as Hm Hevs; subst m' evs. apply alt_l.
    apply errno_any_b_errno in He as (e & He & ->).
    eapply bind_ok0; [apply (choose_ok _ e); exact He|].
    apply pure_ok. }
  destruct (clone_pid_ok_b m ret) eqn:Hv; [|discriminate].
  injection H as Hm Hevs; subst m' evs.
  apply alt_r.
  eapply bind_ok0; [apply (choose_ok _ ret); exact Hv|].
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_clone_ns_resolve_sound_unmodeled : forall eff m i,
  check_clone_ns_resolve eff m = CheckUnmodeled ->
  clone_ns_resolve i m Unmodeled.
Proof.
  intros [ret ws zs us cs copyins] m i H.
  unfold check_clone_ns_resolve in H. unfold clone_ns_resolve.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    cbv iota; cbv iota in H; [apply unmodeled_intro|].
  exfalso.
  destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  unfold check_clone_ns_answer in H.
  destruct (errno_any_b ret); [discriminate|].
  destruct (clone_pid_ok_b m ret); discriminate.
Qed.

Lemma check_clone_ns_resolve_complete_ok : forall eff m m' evs i,
  clone_ns_resolve i m (Ok eff m' evs) ->
  check_clone_ns_resolve eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H.
  unfold clone_ns_resolve, errno_any in H. unfold check_clone_ns_resolve.
  sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    hall Hg; inv_ok.
  (* one goal per alternative: an errno in 1..4095 but -EINTR, and a pid *)
  all: cbv beta iota; unfold check_clone_ns_answer.
  all: try (rewrite errno_any_b_ret by (intuition lia); reflexivity).
  all: match goal with
       | Hv : clone_pid_ok_b ?mm ?r = true |- _ =>
           unfold errno_any_b; rewrite (clone_pid_not_error mm r Hv), Hv; reflexivity
       end.
Qed.

Lemma check_clone_ns_resolve_complete_unmodeled : forall m i eff,
  clone_ns_resolve i m Unmodeled -> check_clone_ns_resolve eff m = CheckUnmodeled.
Proof.
  intros m i eff H.
  unfold clone_ns_resolve, errno_any in H. unfold check_clone_ns_resolve.
  sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    hall Hg; inv_ok;
    reflexivity.
Qed.

Lemma check_clone_resolve_sound_ok : forall eff m m' evs i,
  check_clone_resolve eff m = CheckOk m' evs -> clone_resolve i m (Ok eff m' evs).
Proof.
  intros [ret ws zs us cs copyins] m m' evs i H.
  unfold check_clone_resolve in H. unfold clone_resolve.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    cbv iota; cbv iota in H; [discriminate|].
  destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  unfold check_clone_answer in H.
  destruct (errno_ret_in clone_errnos ret) eqn:He.
  { injection H as Hm Hevs; subst m' evs. apply alt_l.
    apply errno_ret_in_true in He as (e & Hin & ->).
    eapply bind_ok0; [apply (choose_ok _ e); exact Hin|]. apply pure_ok. }
  destruct (clone_pid_ok_b m ret) eqn:Hv; [|discriminate].
  injection H as Hm Hevs; subst m' evs.
  apply alt_r.
  eapply bind_ok0; [apply (choose_ok _ ret); exact Hv|].
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_clone_resolve_sound_unmodeled : forall eff m i,
  check_clone_resolve eff m = CheckUnmodeled -> clone_resolve i m Unmodeled.
Proof.
  intros [ret ws zs us cs copyins] m i H.
  unfold check_clone_resolve in H. unfold clone_resolve.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    cbv iota; cbv iota in H; [apply unmodeled_intro|].
  exfalso.
  destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  unfold check_clone_answer in H.
  destruct (errno_ret_in clone_errnos ret); [discriminate|].
  destruct (clone_pid_ok_b m ret); discriminate.
Qed.

Lemma check_clone_resolve_complete_ok : forall eff m m' evs i,
  clone_resolve i m (Ok eff m' evs) -> check_clone_resolve eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H.
  unfold clone_resolve in H. unfold check_clone_resolve. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    hall Hg; inv_ok.
  (* one goal per alternative: an errno from [clone_errnos], and a pid *)
  all: cbv beta iota; unfold check_clone_answer.
  all: try (erewrite errno_ret_in_intro by eassumption; reflexivity).
  all: match goal with
       | Hv : clone_pid_ok_b ?mm ?r = true |- _ =>
           rewrite (clone_pid_not_errno mm r Hv), Hv; reflexivity
       end.
Qed.

Lemma check_clone_resolve_complete_unmodeled : forall m i eff,
  clone_resolve i m Unmodeled -> check_clone_resolve eff m = CheckUnmodeled.
Proof.
  intros m i eff H.
  unfold clone_resolve in H. unfold check_clone_resolve. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    hall Hg; inv_ok; reflexivity.
Qed.

(** The same four, for the resolution that carries a ledger.  Each goes
    through the plain one on the effect with the ledger stripped, so the
    admitted answer is decided in exactly one place. *)
Lemma check_clone3_resolve_sound_ok : forall uargs eff m m' evs i,
  check_clone3_resolve uargs eff m = CheckOk m' evs ->
  clone3_resolve uargs i m (Ok eff m' evs).
Proof.
  intros uargs [ret ws zs us cs cis] m m' evs i H.
  unfold check_clone3_resolve in H.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    cbv iota in H; [discriminate|].
  destruct ws as [|? ?]; try discriminate.
  destruct zs as [|? ?]; try discriminate.
  destruct us as [|? ?]; try discriminate.
  destruct cs as [|? ?]; try discriminate.
  destruct cis as [|[a n] [|? ?]]; try discriminate.
  destruct (bv_eqb a uargs && Nat.eqb n CLONE_ARGS_SIZE_nat) eqn:Hl;
    cbv iota in H; [|discriminate].
  apply andb_true_iff in Hl as [Ha Hn].
  apply bv_eqb_eq in Ha. apply Nat.eqb_eq in Hn. subst a n.
  unfold clone3_resolve.
  apply (record_copyins_ok_empty _ _ _ _ (mkEffect ret [] [])); [reflexivity|].
  apply check_clone_resolve_sound_ok.
  unfold check_clone_resolve. rewrite Hg. cbv iota. exact H.
Qed.

Lemma check_clone3_resolve_sound_unmodeled : forall uargs eff m i,
  check_clone3_resolve uargs eff m = CheckUnmodeled ->
  clone3_resolve uargs i m Unmodeled.
Proof.
  intros uargs eff m i H.
  unfold check_clone3_resolve in H.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    cbv iota in H.
  - unfold clone3_resolve. apply record_copyins_unmodeled.
    apply (check_clone_resolve_sound_unmodeled eff).
    unfold check_clone_resolve. rewrite Hg. cbv iota. reflexivity.
  - exfalso. destruct eff as [ret ws zs us cs cis].
    destruct ws as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct cis as [|[a n] [|? ?]]; try discriminate.
    destruct (bv_eqb a uargs && Nat.eqb n CLONE_ARGS_SIZE_nat);
      cbv iota in H; [|discriminate].
    unfold check_clone_answer in H.
    destruct (errno_ret_in clone_errnos ret); [discriminate|].
    destruct (clone_pid_ok_b m ret); discriminate.
Qed.

Lemma check_clone3_resolve_complete_ok : forall uargs eff m m' evs i,
  clone3_resolve uargs i m (Ok eff m' evs) ->
  check_clone3_resolve uargs eff m = CheckOk m' evs.
Proof.
  intros uargs eff m m' evs i H.
  unfold clone3_resolve, record_copyins in H.
  destruct H as (e0 & m0 & evs0 & evs2 & H0 & Hp & Hevs).
  unfold pure in Hp. inversion Hp; clear Hp; subst.
  try rewrite app_nil_r.
  pose proof (check_clone_resolve_complete_ok e0 m _ evs0 i H0) as Hc.
  unfold check_clone_resolve in Hc.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    cbv iota in Hc; [discriminate|].
  destruct e0 as [ret ws zs us cs cis].
  destruct ws as [|? ?]; try discriminate.
  destruct zs as [|? ?]; try discriminate.
  destruct us as [|? ?]; try discriminate.
  destruct cs as [|? ?]; try discriminate.
  destruct cis as [|? ?]; try discriminate.
  unfold check_clone3_resolve, with_copyins. cbn [eff_copyins].
  rewrite Hg. cbv iota. cbn [app].
  rewrite bv_eqb_refl, Nat.eqb_refl. cbv iota. exact Hc.
Qed.

Lemma check_clone3_resolve_complete_unmodeled : forall uargs m i eff,
  clone3_resolve uargs i m Unmodeled ->
  check_clone3_resolve uargs eff m = CheckUnmodeled.
Proof.
  intros uargs m i eff H.
  unfold clone3_resolve, record_copyins in H.
  destruct H as [H|H]; [|destruct H as [? [? [? [_ Hp]]]];
                          unfold pure in Hp; discriminate].
  pose proof (check_clone_resolve_complete_unmodeled m i eff H) as Hc.
  unfold check_clone_resolve in Hc. unfold check_clone3_resolve.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    cbv iota in Hc; cbv iota; [reflexivity|].
  destruct eff as [ret ws zs us cs cis].
  destruct ws as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct cis as [|? ?]; [|discriminate].
  unfold check_clone_answer in Hc.
  destruct (errno_ret_in clone_errnos ret); [discriminate|].
  destruct (clone_pid_ok_b m ret); discriminate.
Qed.

(* ------------------------------------- CLONE_NEWIPC with CLONE_SYSVSEM *)

Lemma check_clone_ns_refused_sound_ok : forall eff m m' evs i,
  check_clone_ns_refused eff m = CheckOk m' evs -> clone_ns_refused i m (Ok eff m' evs).
Proof.
  intros [ret ws zs us cs ci] m m' evs i H.
  unfold check_clone_ns_refused in H. unfold clone_ns_refused.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))));
    cbv iota in H |- *; [discriminate H|].
  destruct ws, zs, us, cs, ci; try discriminate H.
  destruct (errno_any_b ret) eqn:He; [|discriminate H].
  injection H as <- <-.
  apply errno_any_b_errno in He as (e & He & ->).
  unfold errno_any. eapply bind_ok0; [apply (choose_ok _ e); exact He|].
  unfold err_ret, ret_only. apply pure_ok.
Qed.

Lemma check_clone_ns_refused_sound_unmodeled : forall eff m i,
  check_clone_ns_refused eff m = CheckUnmodeled -> clone_ns_refused i m Unmodeled.
Proof.
  intros [ret ws zs us cs ci] m i H.
  unfold check_clone_ns_refused in H. unfold clone_ns_refused.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))));
    cbv iota in H |- *; [apply unmodeled_intro|].
  exfalso. destruct ws, zs, us, cs, ci; try discriminate H.
  destruct (errno_any_b ret); discriminate H.
Qed.

Lemma check_clone_ns_refused_complete_ok : forall eff m m' evs i,
  clone_ns_refused i m (Ok eff m' evs) -> check_clone_ns_refused eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H.
  unfold clone_ns_refused, errno_any in H. unfold check_clone_ns_refused.
  sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    hall Hg; inv_ok.
  cbv beta iota. rewrite errno_any_b_ret by (intuition lia). reflexivity.
Qed.

Lemma check_clone_ns_refused_complete_unmodeled : forall m i eff,
  clone_ns_refused i m Unmodeled -> check_clone_ns_refused eff m = CheckUnmodeled.
Proof.
  intros m i eff H.
  unfold clone_ns_refused, errno_any in H. unfold check_clone_ns_refused.
  sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))) eqn:Hg;
    hall Hg; inv_ok; reflexivity.
Qed.

(* ------------------------------------------------- the host's clone refusers *)

(** The four obligations, once, for any answered test, refusal and lists. *)
Lemma check_refusable_sound_ok : forall answered fail k re r i m m' eff evs,
  (re = true -> fail i m (Ok eff m [])) ->
  (r = CheckOk m' evs -> k i m (Ok eff m' evs)) ->
  check_refusable (answered i) re m r = CheckOk m' evs ->
  clone_refusable answered fail k i m (Ok eff m' evs).
Proof.
  intros answered fail k re r i m m' eff evs Hf Hk H. unfold check_refusable in H.
  destruct (answered i && clone_refused_b (m_clone_refusers m)
            && clone_no_shared_file_b (forfeit_inherited (m_fds m))) eqn:Hc;
    cbn [andb] in H.
  - destruct re; cbv beta iota in H.
    + injection H as <- <-. unfold clone_refusable. rewrite Hc.
      change (alt fail k i m (Ok eff m [])). apply alt_l. apply Hf. reflexivity.
    + apply clone_refusable_lists. apply Hk. exact H.
  - apply clone_refusable_lists. apply Hk. exact H.
Qed.

Lemma check_refusable_sound_unmodeled : forall answered fail k re r i m,
  (r = CheckUnmodeled -> k i m Unmodeled) ->
  check_refusable (answered i) re m r = CheckUnmodeled ->
  clone_refusable answered fail k i m Unmodeled.
Proof.
  intros answered fail k re r i m Hk H. unfold check_refusable in H.
  apply clone_refusable_lists. apply Hk.
  destruct (answered i && clone_refused_b (m_clone_refusers m)
            && clone_no_shared_file_b (forfeit_inherited (m_fds m)) && re);
    [discriminate H | exact H].
Qed.

Lemma check_refusable_complete_ok : forall answered fail k re r i m m' eff evs,
  (fail i m (Ok eff m' evs) -> re = true /\ m' = m /\ evs = []) ->
  (k i m (Ok eff m' evs) -> r = CheckOk m' evs) ->
  (re = true -> r = CheckOk m' evs -> m' = m /\ evs = []) ->
  clone_refusable answered fail k i m (Ok eff m' evs) ->
  check_refusable (answered i) re m r = CheckOk m' evs.
Proof.
  intros answered fail k re r i m m' eff evs Hf Hk Hs H.
  unfold clone_refusable in H. unfold check_refusable.
  destruct (answered i && clone_refused_b (m_clone_refusers m)
            && clone_no_shared_file_b (forfeit_inherited (m_fds m))); cbn [andb].
  - destruct H as [H | H].
    + destruct (Hf H) as (-> & -> & ->). reflexivity.
    + pose proof (Hk H) as Hr. destruct re.
      * destruct (Hs eq_refl Hr) as [-> ->]. reflexivity.
      * exact Hr.
  - exact (Hk H).
Qed.

Lemma check_refusable_complete_unmodeled : forall answered fail k re r i m,
  (fail i m Unmodeled -> False) ->
  (k i m Unmodeled -> r = CheckUnmodeled) ->
  (answered i = true -> clone_no_shared_file_b (forfeit_inherited (m_fds m)) = true ->
   k i m Unmodeled -> False) ->
  clone_refusable answered fail k i m Unmodeled ->
  check_refusable (answered i) re m r = CheckUnmodeled.
Proof.
  intros answered fail k re r i m Hf Hk Hn H.
  unfold clone_refusable in H. unfold check_refusable.
  destruct (answered i && clone_refused_b (m_clone_refusers m)
            && clone_no_shared_file_b (forfeit_inherited (m_fds m))) eqn:Hc; cbn [andb].
  - exfalso. destruct H as [H | H]; [exact (Hf H)|].
    apply andb_true_iff in Hc as [Hc Hg]. apply andb_true_iff in Hc as [Ha _].
    exact (Hn Ha Hg H).
  - exact (Hk H).
Qed.

(** An answer [check_refusable] accepts is a refusal's, the model and the
    events unchanged, or the inner checker's. *)
Lemma check_refusable_ok_inv : forall a re m r m' evs,
  check_refusable a re m r = CheckOk m' evs ->
  (re = true /\ m' = m /\ evs = []) \/ r = CheckOk m' evs.
Proof.
  intros a re m r m' evs H. unfold check_refusable in H.
  destruct re; [|rewrite Bool.andb_false_r in H; right; exact H].
  destruct (a && clone_refused_b (m_clone_refusers m)
            && clone_no_shared_file_b (forfeit_inherited (m_fds m))); cbn [andb] in H.
  - left. injection H as <- <-. split; [reflexivity|]. split; reflexivity.
  - right. exact H.
Qed.

(** The refusal's effects, both ways. *)
Lemma clone_refused_eff_b_ok : forall eff i m,
  clone_refused_eff_b eff = true -> clone_refused_fail i m (Ok eff m []).
Proof.
  intros [ret ws zs us cs cis] i m H.
  destruct ws, zs, us, cs, cis; try discriminate H.
  cbn [clone_refused_eff_b] in H.
  apply addr_is_error_b_errno in H as (e & H1 & H2 & ->).
  apply clone_refused_fail_ok. lia.
Qed.

Lemma clone_refused_fail_shape : forall i m eff m' evs,
  clone_refused_fail i m (Ok eff m' evs) ->
  clone_refused_eff_b eff = true /\ m' = m /\ evs = [].
Proof.
  intros i m eff m' evs H.
  apply clone_refused_fail_inv in H as (e & He & Heq).
  injection Heq as -> -> ->. split; [|split; reflexivity].
  cbn [clone_refused_eff_b]. apply errno_ret_error_b; lia.
Qed.

Lemma clone3_refused_eff_b_ok : forall uargs eff i m,
  clone3_refused_eff_b uargs eff = true -> clone3_refused_fail uargs i m (Ok eff m []).
Proof.
  intros uargs [ret ws zs us cs cis] i m H.
  destruct ws, zs, us, cs; try discriminate H.
  destruct cis as [|[a n] [|? ?]]; try discriminate H.
  cbn [clone3_refused_eff_b] in H.
  apply andb_true_iff in H as [H He]. apply andb_true_iff in H as [Ha Hn].
  apply bv_eqb_eq in Ha. apply Nat.eqb_eq in Hn. subst a n.
  apply addr_is_error_b_errno in He as (e & H1 & H2 & ->).
  apply clone3_refused_fail_ok. lia.
Qed.

Lemma clone3_refused_fail_shape : forall uargs i m eff m' evs,
  clone3_refused_fail uargs i m (Ok eff m' evs) ->
  clone3_refused_eff_b uargs eff = true /\ m' = m /\ evs = [].
Proof.
  intros uargs i m eff m' evs H.
  apply clone3_refused_fail_inv in H as (e & He & Heq).
  injection Heq as -> -> ->. split; [|split; reflexivity].
  cbn [clone3_refused_eff_b]. rewrite bv_eqb_refl, Nat.eqb_refl. cbn [andb].
  apply errno_ret_error_b; lia.
Qed.

(** A refusal's effect is error-encoded and writes and reads nothing. *)
Lemma clone_refused_eff_b_error : forall eff,
  clone_refused_eff_b eff = true -> addr_is_error_b (eff_ret eff) = true.
Proof.
  intros [ret ws zs us cs ci] H. destruct ws, zs, us, cs, ci; try discriminate H. exact H.
Qed.

Lemma clone_refused_eff_b_no_writes : forall eff,
  clone_refused_eff_b eff = true -> eff_writes eff = [] /\ eff_copyins eff = [].
Proof.
  intros [ret ws zs us cs ci] H. destruct ws, zs, us, cs, ci; try discriminate H.
  split; reflexivity.
Qed.

(** THE SHAPE OF AN ACCEPTED ANSWER: no event, and either an
    error-encoded return with the model as it was, or an admissible pid
    with the child recorded over the model the caller keeps
    ([Kernel.Fork.forfeit_model]).  The memory the answer writes is not
    part of it. *)
Definition clone_answer_shape (eff : SyscallEffect) (m m' : Model) (evs : list event)
    : Prop :=
  evs = []
  /\ ((m' = m /\ addr_is_error_b (eff_ret eff) = true)
      \/ (m' = with_child (eff_ret eff) (forfeit_model m)
          /\ clone_pid_ok_b m (eff_ret eff) = true)).

Lemma check_clone_answer_shape : forall ret m m' evs,
  check_clone_answer ret m = CheckOk m' evs ->
  clone_answer_shape (mkEffect ret [] []) m m' evs.
Proof.
  intros ret m m' evs H. unfold check_clone_answer in H. unfold clone_answer_shape.
  cbn [eff_ret].
  destruct (errno_ret_in clone_errnos ret) eqn:He.
  - injection H as <- <-. split; [reflexivity|]. left. split; [reflexivity|].
    apply errno_ret_in_true in He as (e & Hin & ->).
    destruct (errnos_ok_range clone_errnos e eq_refl Hin) as [H1 H2].
    exact (errno_ret_error_b e H1 H2).
  - destruct (clone_pid_ok_b m ret) eqn:Hv; [|discriminate H].
    injection H as <- <-. split; [reflexivity|]. right.
    split; [reflexivity | first [exact Hv | reflexivity]].
Qed.

Lemma check_clone_ns_answer_shape : forall ret m m' evs,
  check_clone_ns_answer ret m = CheckOk m' evs ->
  clone_answer_shape (mkEffect ret [] []) m m' evs.
Proof.
  intros ret m m' evs H. unfold check_clone_ns_answer in H. unfold clone_answer_shape.
  cbn [eff_ret].
  destruct (errno_any_b ret) eqn:He.
  - injection H as <- <-. split; [reflexivity|]. left. split; [reflexivity|].
    unfold errno_any_b in He. apply andb_true_iff in He as [He _]. exact He.
  - destruct (clone_pid_ok_b m ret) eqn:Hv; [|discriminate H].
    injection H as <- <-. split; [reflexivity|]. right.
    split; [reflexivity | first [exact Hv | reflexivity]].
Qed.

Lemma check_clone_resolve_shape : forall eff m m' evs,
  check_clone_resolve eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros [ret ws zs us cs ci] m m' evs H. unfold check_clone_resolve in H.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); cbv iota in H;
    [discriminate H|].
  destruct ws, zs, us, cs, ci; try discriminate H.
  exact (check_clone_answer_shape _ _ _ _ H).
Qed.

Lemma check_clone_ns_resolve_shape : forall eff m m' evs,
  check_clone_ns_resolve eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros [ret ws zs us cs ci] m m' evs H. unfold check_clone_ns_resolve in H.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); cbv iota in H;
    [discriminate H|].
  destruct ws, zs, us, cs, ci; try discriminate H.
  exact (check_clone_ns_answer_shape _ _ _ _ H).
Qed.

Lemma check_clone_einval_shape : forall eff m m' evs,
  check_clone_einval eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros eff m m' evs H. unfold check_clone_einval in H.
  destruct (clone_no_shared_file_b (forfeit_inherited (m_fds m))); cbv iota in H;
    [|discriminate H].
  apply check_ret_only_ok_iff in H as (-> & -> & ->).
  split; [reflexivity|]. left. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

Lemma check_clone_ns_refused_shape : forall eff m m' evs,
  check_clone_ns_refused eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros [ret ws zs us cs ci] m m' evs H. unfold check_clone_ns_refused in H.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); cbv iota in H;
    [discriminate H|].
  destruct ws, zs, us, cs, ci; try discriminate H.
  destruct (errno_any_b ret) eqn:He; [|discriminate H].
  injection H as <- <-. split; [reflexivity|]. left. split; [reflexivity|].
  cbn [eff_ret]. unfold errno_any_b in He. apply andb_true_iff in He as [He _]. exact He.
Qed.

Lemma check_clone3_resolve_shape : forall uargs eff m m' evs,
  check_clone3_resolve uargs eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros uargs [ret ws zs us cs ci] m m' evs H. unfold check_clone3_resolve in H.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m)))); cbv iota in H;
    [discriminate H|].
  destruct ws, zs, us, cs; try discriminate H.
  destruct ci as [|[a n] [|? ?]]; try discriminate H.
  destruct (bv_eqb a uargs && Nat.eqb n CLONE_ARGS_SIZE_nat); cbv iota in H;
    [|discriminate H].
  exact (check_clone_answer_shape _ _ _ _ H).
Qed.

Lemma clone_answer_shape_ret : forall e eff m m' evs,
  eff_ret e = eff_ret eff -> clone_answer_shape e m m' evs -> clone_answer_shape eff m m' evs.
Proof. intros e eff m m' evs Hr H. unfold clone_answer_shape in *. rewrite <- Hr. exact H. Qed.

(** An error-encoded answer of that shape leaves the model and the events
    as they were: no admissible pid is error-encoded. *)
Lemma clone_answer_shape_refused : forall eff m m' evs,
  addr_is_error_b (eff_ret eff) = true -> clone_answer_shape eff m m' evs ->
  m' = m /\ evs = [].
Proof.
  intros eff m m' evs He [Hev [[Hm _] | [_ Hv]]]; [split; assumption|].
  rewrite (clone_pid_not_error _ _ Hv) in He. discriminate He.
Qed.

(** With the descriptor gate open, the three bodies the refusers wrap
    answer: none of them declines. *)
Lemma clone_resolve_gate_answers : forall i m,
  clone_no_shared_file_b (forfeit_inherited (m_fds m)) = true ->
  clone_resolve i m Unmodeled -> False.
Proof.
  intros i m Hg H.
  pose proof (check_clone_resolve_complete_unmodeled m i
                (mkEffectU (Z_to_bv 64 0) [] [] [] [] []) H) as Hc.
  unfold check_clone_resolve, check_clone_answer in Hc. rewrite Hg in Hc.
  cbn [negb] in Hc. cbv iota in Hc.
  repeat match type of Hc with
         | context [if ?b then _ else _] => destruct b; cbv iota in Hc
         end; discriminate Hc.
Qed.

Lemma clone_ns_resolve_gate_answers : forall i m,
  clone_no_shared_file_b (forfeit_inherited (m_fds m)) = true ->
  clone_ns_resolve i m Unmodeled -> False.
Proof.
  intros i m Hg H.
  pose proof (check_clone_ns_resolve_complete_unmodeled m i
                (mkEffectU (Z_to_bv 64 0) [] [] [] [] []) H) as Hc.
  unfold check_clone_ns_resolve, check_clone_ns_answer in Hc. rewrite Hg in Hc.
  cbn [negb] in Hc. cbv iota in Hc.
  repeat match type of Hc with
         | context [if ?b then _ else _] => destruct b; cbv iota in Hc
         end; discriminate Hc.
Qed.

Lemma clone_ns_refused_gate_answers : forall i m,
  clone_no_shared_file_b (forfeit_inherited (m_fds m)) = true ->
  clone_ns_refused i m Unmodeled -> False.
Proof.
  intros i m Hg H.
  pose proof (check_clone_ns_refused_complete_unmodeled m i
                (mkEffectU (Z_to_bv 64 0) [] [] [] [] []) H) as Hc.
  unfold check_clone_ns_refused in Hc. rewrite Hg in Hc.
  cbn [negb] in Hc. cbv iota in Hc.
  repeat match type of Hc with
         | context [if ?b then _ else _] => destruct b; cbv iota in Hc
         end; discriminate Hc.
Qed.

(** [check_refusable_arm] against [Kernel.Fork.clone_refusable_arm], for
    any body and checker of it that agree. *)
Lemma check_refusable_arm_sound_ok : forall (body : Sys SyscallEffect) inner i eff m m' evs,
  (inner eff m = CheckOk m' evs -> body i m (Ok eff m' evs)) ->
  check_refusable_arm inner eff m = CheckOk m' evs ->
  clone_refusable_arm body i m (Ok eff m' evs).
Proof.
  intros body inner i eff m m' evs Hk H.
  unfold check_refusable_arm in H. unfold clone_refusable_arm.
  apply (check_refusable_sound_ok (fun _ => true) clone_refused_fail body
           (clone_refused_eff_b eff) (inner eff m) i m m' eff evs); [ | exact Hk | exact H].
  intros Hr. apply clone_refused_eff_b_ok. exact Hr.
Qed.

Lemma check_refusable_arm_sound_unmodeled : forall (body : Sys SyscallEffect) inner i eff m,
  (inner eff m = CheckUnmodeled -> body i m Unmodeled) ->
  check_refusable_arm inner eff m = CheckUnmodeled ->
  clone_refusable_arm body i m Unmodeled.
Proof.
  intros body inner i eff m Hk H.
  unfold check_refusable_arm in H. unfold clone_refusable_arm.
  exact (check_refusable_sound_unmodeled (fun _ => true) clone_refused_fail body
           (clone_refused_eff_b eff) (inner eff m) i m Hk H).
Qed.

Lemma check_refusable_arm_complete_ok : forall (body : Sys SyscallEffect) inner i eff m m' evs,
  (body i m (Ok eff m' evs) -> inner eff m = CheckOk m' evs) ->
  (clone_refused_eff_b eff = true -> inner eff m = CheckOk m' evs -> m' = m /\ evs = []) ->
  clone_refusable_arm body i m (Ok eff m' evs) ->
  check_refusable_arm inner eff m = CheckOk m' evs.
Proof.
  intros body inner i eff m m' evs Hk Hs H.
  unfold clone_refusable_arm in H. unfold check_refusable_arm.
  exact (check_refusable_complete_ok (fun _ => true) clone_refused_fail body
           (clone_refused_eff_b eff) (inner eff m) i m m' eff evs
           (clone_refused_fail_shape i m eff m' evs) Hk Hs H).
Qed.

Lemma check_refusable_arm_complete_unmodeled : forall (body : Sys SyscallEffect) inner i eff m,
  (body i m Unmodeled -> inner eff m = CheckUnmodeled) ->
  (clone_no_shared_file_b (forfeit_inherited (m_fds m)) = true -> body i m Unmodeled -> False) ->
  clone_refusable_arm body i m Unmodeled ->
  check_refusable_arm inner eff m = CheckUnmodeled.
Proof.
  intros body inner i eff m Hk Hn H.
  unfold clone_refusable_arm in H. unfold check_refusable_arm.
  apply (check_refusable_complete_unmodeled (fun _ => true) clone_refused_fail body
           (clone_refused_eff_b eff) (inner eff m) i m); [ | exact Hk | | exact H].
  - intros Hf. apply clone_refused_fail_inv in Hf as (e & _ & Heq). discriminate Heq.
  - intros _ Hg Hb. exact (Hn Hg Hb).
Qed.

(** An answer [check_refusable_arm] accepts is a refusal's or [inner]'s. *)
Lemma check_refusable_arm_ok_inv : forall inner eff m m' evs,
  check_refusable_arm inner eff m = CheckOk m' evs ->
  (m' = m /\ evs = [] /\ addr_is_error_b (eff_ret eff) = true)
  \/ inner eff m = CheckOk m' evs.
Proof.
  intros inner eff m m' evs H. unfold check_refusable_arm in H.
  apply check_refusable_ok_inv in H as [(Hr & -> & ->) | H]; [left | right; exact H].
  split; [reflexivity|]. split; [reflexivity|]. exact (clone_refused_eff_b_error _ Hr).
Qed.

(** A body checker that writes and reads nothing keeps that around a
    refusal. *)
Lemma check_refusable_arm_no_writes : forall inner eff m m' evs,
  (forall e m1 evs1, inner e m = CheckOk m1 evs1 -> eff_writes e = [] /\ eff_copyins e = []) ->
  check_refusable_arm inner eff m = CheckOk m' evs ->
  eff_writes eff = [] /\ eff_copyins eff = [].
Proof.
  intros inner eff m m' evs Hi H. unfold check_refusable_arm in H.
  apply check_refusable_ok_inv in H as [(Hr & _ & _) | H].
  - exact (clone_refused_eff_b_no_writes _ Hr).
  - exact (Hi _ _ _ H).
Qed.

(** The answer shape of each wrapped body survives the refusal. *)
Lemma check_refusable_arm_shape : forall inner eff m m' evs,
  (inner eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs) ->
  check_refusable_arm inner eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros inner eff m m' evs Hi H.
  apply check_refusable_arm_ok_inv in H as [(-> & -> & He) | H]; [|exact (Hi H)].
  split; [reflexivity|]. left. split; [reflexivity | exact He].
Qed.

(** A refusal's effect the body checker accepts leaves the model and the
    events as they were. *)
Lemma check_refused_shape : forall inner eff m m' evs,
  (inner eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs) ->
  clone_refused_eff_b eff = true -> inner eff m = CheckOk m' evs -> m' = m /\ evs = [].
Proof.
  intros inner eff m m' evs Hi Hr H.
  exact (clone_answer_shape_refused _ _ _ _ (clone_refused_eff_b_error _ Hr) (Hi H)).
Qed.

(* ------------------------------------------------ the stores of a record *)

(** The two bodies of [Kernel.Fork.clone_with_stores] write nothing and
    read nothing of their own. *)
Lemma check_clone_resolve_no_writes : forall eff m m' evs,
  check_clone_resolve eff m = CheckOk m' evs -> eff_writes eff = [] /\ eff_copyins eff = [].
Proof.
  intros [ret ws zs us cs ci] m m' evs H. unfold check_clone_resolve in H.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))));
    [discriminate H|].
  destruct ws, zs, us, cs, ci; try discriminate H. split; reflexivity.
Qed.

Lemma check_clone_ns_resolve_no_writes : forall eff m m' evs,
  check_clone_ns_resolve eff m = CheckOk m' evs -> eff_writes eff = [] /\ eff_copyins eff = [].
Proof.
  intros [ret ws zs us cs ci] m m' evs H. unfold check_clone_ns_resolve in H.
  destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))));
    [discriminate H|].
  destruct ws, zs, us, cs, ci; try discriminate H. split; reflexivity.
Qed.

Lemma writes_eqb_refl : forall l, writes_eqb l l = true.
Proof. intros l. apply writes_eqb_eq. reflexivity. Qed.

(** The three bodies with the refusers ([Kernel.Fork.clone_refusable_arm])
    against their checkers, each the four ways, with what they write and
    the shape of what they accept. *)
Lemma check_arm_resolve_sound_ok : forall i e m m1 evs1,
  check_refusable_arm check_clone_resolve e m = CheckOk m1 evs1 ->
  clone_refusable_arm clone_resolve i m (Ok e m1 evs1).
Proof.
  intros i e m m1 evs1 H.
  apply (check_refusable_arm_sound_ok clone_resolve check_clone_resolve); [|exact H].
  intros He. now apply check_clone_resolve_sound_ok.
Qed.

Lemma check_arm_resolve_sound_unmodeled : forall i e m,
  check_refusable_arm check_clone_resolve e m = CheckUnmodeled ->
  clone_refusable_arm clone_resolve i m Unmodeled.
Proof.
  intros i e m H.
  apply (check_refusable_arm_sound_unmodeled clone_resolve check_clone_resolve i e m);
    [|exact H].
  intros He. now apply check_clone_resolve_sound_unmodeled with (eff := e).
Qed.

Lemma check_arm_resolve_complete_ok : forall i e m m1 evs1,
  clone_refusable_arm clone_resolve i m (Ok e m1 evs1) ->
  check_refusable_arm check_clone_resolve e m = CheckOk m1 evs1.
Proof.
  intros i e m m1 evs1 H.
  apply (check_refusable_arm_complete_ok clone_resolve check_clone_resolve i);
    [ | | exact H].
  - intros Hb. now apply check_clone_resolve_complete_ok with (i := i).
  - apply check_refused_shape. apply check_clone_resolve_shape.
Qed.

Lemma check_arm_resolve_complete_unmodeled : forall i e m,
  clone_refusable_arm clone_resolve i m Unmodeled ->
  check_refusable_arm check_clone_resolve e m = CheckUnmodeled.
Proof.
  intros i e m H.
  apply (check_refusable_arm_complete_unmodeled clone_resolve check_clone_resolve i);
    [ | | exact H].
  - intros Hb. now apply check_clone_resolve_complete_unmodeled with (i := i).
  - apply clone_resolve_gate_answers.
Qed.

Lemma check_arm_resolve_no_writes : forall e m m1 evs1,
  check_refusable_arm check_clone_resolve e m = CheckOk m1 evs1 ->
  eff_writes e = [] /\ eff_copyins e = [].
Proof.
  intros e m m1 evs1 H.
  apply (check_refusable_arm_no_writes check_clone_resolve e m m1 evs1); [|exact H].
  intros e0 m0 evs0 H0. exact (check_clone_resolve_no_writes _ _ _ _ H0).
Qed.

Lemma check_arm_resolve_shape : forall e m m1 evs1,
  check_refusable_arm check_clone_resolve e m = CheckOk m1 evs1 ->
  clone_answer_shape e m m1 evs1.
Proof.
  intros e m m1 evs1. apply check_refusable_arm_shape. apply check_clone_resolve_shape.
Qed.

Lemma check_arm_ns_resolve_sound_ok : forall i e m m1 evs1,
  check_refusable_arm check_clone_ns_resolve e m = CheckOk m1 evs1 ->
  clone_refusable_arm clone_ns_resolve i m (Ok e m1 evs1).
Proof.
  intros i e m m1 evs1 H.
  apply (check_refusable_arm_sound_ok clone_ns_resolve check_clone_ns_resolve); [|exact H].
  intros He. now apply check_clone_ns_resolve_sound_ok.
Qed.

Lemma check_arm_ns_resolve_sound_unmodeled : forall i e m,
  check_refusable_arm check_clone_ns_resolve e m = CheckUnmodeled ->
  clone_refusable_arm clone_ns_resolve i m Unmodeled.
Proof.
  intros i e m H.
  apply (check_refusable_arm_sound_unmodeled clone_ns_resolve check_clone_ns_resolve i e m);
    [|exact H].
  intros He. now apply check_clone_ns_resolve_sound_unmodeled with (eff := e).
Qed.

Lemma check_arm_ns_resolve_complete_ok : forall i e m m1 evs1,
  clone_refusable_arm clone_ns_resolve i m (Ok e m1 evs1) ->
  check_refusable_arm check_clone_ns_resolve e m = CheckOk m1 evs1.
Proof.
  intros i e m m1 evs1 H.
  apply (check_refusable_arm_complete_ok clone_ns_resolve check_clone_ns_resolve i);
    [ | | exact H].
  - intros Hb. now apply check_clone_ns_resolve_complete_ok with (i := i).
  - apply check_refused_shape. apply check_clone_ns_resolve_shape.
Qed.

Lemma check_arm_ns_resolve_complete_unmodeled : forall i e m,
  clone_refusable_arm clone_ns_resolve i m Unmodeled ->
  check_refusable_arm check_clone_ns_resolve e m = CheckUnmodeled.
Proof.
  intros i e m H.
  apply (check_refusable_arm_complete_unmodeled clone_ns_resolve check_clone_ns_resolve i);
    [ | | exact H].
  - intros Hb. now apply check_clone_ns_resolve_complete_unmodeled with (i := i).
  - apply clone_ns_resolve_gate_answers.
Qed.

Lemma check_arm_ns_resolve_no_writes : forall e m m1 evs1,
  check_refusable_arm check_clone_ns_resolve e m = CheckOk m1 evs1 ->
  eff_writes e = [] /\ eff_copyins e = [].
Proof.
  intros e m m1 evs1 H.
  apply (check_refusable_arm_no_writes check_clone_ns_resolve e m m1 evs1); [|exact H].
  intros e0 m0 evs0 H0. exact (check_clone_ns_resolve_no_writes _ _ _ _ H0).
Qed.

Lemma check_arm_ns_resolve_shape : forall e m m1 evs1,
  check_refusable_arm check_clone_ns_resolve e m = CheckOk m1 evs1 ->
  clone_answer_shape e m m1 evs1.
Proof.
  intros e m m1 evs1. apply check_refusable_arm_shape. apply check_clone_ns_resolve_shape.
Qed.

Lemma check_arm_ns_refused_sound_ok : forall i e m m1 evs1,
  check_refusable_arm check_clone_ns_refused e m = CheckOk m1 evs1 ->
  clone_refusable_arm clone_ns_refused i m (Ok e m1 evs1).
Proof.
  intros i e m m1 evs1 H.
  apply (check_refusable_arm_sound_ok clone_ns_refused check_clone_ns_refused); [|exact H].
  intros He. now apply check_clone_ns_refused_sound_ok.
Qed.

Lemma check_arm_ns_refused_sound_unmodeled : forall i e m,
  check_refusable_arm check_clone_ns_refused e m = CheckUnmodeled ->
  clone_refusable_arm clone_ns_refused i m Unmodeled.
Proof.
  intros i e m H.
  apply (check_refusable_arm_sound_unmodeled clone_ns_refused check_clone_ns_refused i e m);
    [|exact H].
  intros He. now apply check_clone_ns_refused_sound_unmodeled with (eff := e).
Qed.

Lemma check_arm_ns_refused_complete_ok : forall i e m m1 evs1,
  clone_refusable_arm clone_ns_refused i m (Ok e m1 evs1) ->
  check_refusable_arm check_clone_ns_refused e m = CheckOk m1 evs1.
Proof.
  intros i e m m1 evs1 H.
  apply (check_refusable_arm_complete_ok clone_ns_refused check_clone_ns_refused i);
    [ | | exact H].
  - intros Hb. now apply check_clone_ns_refused_complete_ok with (i := i).
  - apply check_refused_shape. apply check_clone_ns_refused_shape.
Qed.

Lemma check_arm_ns_refused_complete_unmodeled : forall i e m,
  clone_refusable_arm clone_ns_refused i m Unmodeled ->
  check_refusable_arm check_clone_ns_refused e m = CheckUnmodeled.
Proof.
  intros i e m H.
  apply (check_refusable_arm_complete_unmodeled clone_ns_refused check_clone_ns_refused i);
    [ | | exact H].
  - intros Hb. now apply check_clone_ns_refused_complete_unmodeled with (i := i).
  - apply clone_ns_refused_gate_answers.
Qed.

Lemma check_arm_ns_refused_shape : forall e m m1 evs1,
  check_refusable_arm check_clone_ns_refused e m = CheckOk m1 evs1 ->
  clone_answer_shape e m m1 evs1.
Proof.
  intros e m m1 evs1. apply check_refusable_arm_shape. apply check_clone_ns_refused_shape.
Qed.

(** [check_with_stores] against [Kernel.Fork.clone_with_stores], for any
    body and checker of it that agree. *)
Lemma check_with_stores_sound_ok : forall (body : Sys SyscallEffect) inner i r eff m m' evs,
  (forall e m1 evs1, inner e m = CheckOk m1 evs1 -> body i m (Ok e m1 evs1)) ->
  check_with_stores i r inner eff m = CheckOk m' evs ->
  clone_with_stores r body i m (Ok eff m' evs).
Proof.
  intros body inner i r [ret ws zs us cs ci] m m' evs Hs H.
  unfold check_with_stores in H. apply clone_with_stores_iff.
  destruct (clone_stores_ok i m r) eqn:Hok; cbn [negb] in H; [|discriminate H].
  left. split; [reflexivity|]. cbv iota.
  destruct (inner (strip_tid_writes (mkEffectU ret ws zs us cs ci)) m)
    as [m1 evs1| |] eqn:Hin; cbv iota in H; try discriminate H.
  cbn [eff_ret eff_writes] in H.
  destruct (addr_is_error_b ret
            || writes_eqb ws (tid_writes (in_wmem i) (clone_parent_tid r) ret)) eqn:Hc;
    cbv iota in H; [|discriminate H].
  injection H as <- <-.
  exists (strip_tid_writes (mkEffectU ret ws zs us cs ci)).
  split; [exact (Hs _ _ _ Hin)|].
  unfold strip_tid_writes, tid_store_effect. cbn [eff_ret].
  destruct (addr_is_error_b ret) eqn:He; cbn [eff_ret eff_writes eff_zeros eff_unmaps
                                               eff_copies eff_copyins]; rewrite ?He.
  - reflexivity.
  - rewrite ?He in Hc. cbn [orb] in Hc. apply writes_eqb_eq in Hc. subst ws. reflexivity.
Qed.

Lemma check_with_stores_sound_unmodeled : forall (body : Sys SyscallEffect) inner i r eff m,
  (forall e, inner e m = CheckUnmodeled -> body i m Unmodeled) ->
  check_with_stores i r inner eff m = CheckUnmodeled ->
  clone_with_stores r body i m Unmodeled.
Proof.
  intros body inner i r eff m Hs H.
  unfold check_with_stores in H. apply clone_with_stores_iff.
  destruct (clone_stores_ok i m r) eqn:Hok; cbn [negb] in H.
  - left. split; [reflexivity|]. cbv iota.
    destruct (inner (strip_tid_writes eff) m) eqn:Hin; cbv iota in H.
    + destruct (addr_is_error_b (eff_ret eff)
                || writes_eqb (eff_writes eff)
                     (tid_writes (in_wmem i) (clone_parent_tid r) (eff_ret eff)));
        cbv iota in H; discriminate H.
    + discriminate H.
    + exact (Hs _ Hin).
  - right. split; reflexivity.
Qed.

Lemma check_with_stores_complete_ok : forall (body : Sys SyscallEffect) inner i r eff m m' evs,
  (forall e m1 evs1, body i m (Ok e m1 evs1) -> inner e m = CheckOk m1 evs1) ->
  (forall e m1 evs1, inner e m = CheckOk m1 evs1 -> eff_writes e = []) ->
  clone_with_stores r body i m (Ok eff m' evs) ->
  check_with_stores i r inner eff m = CheckOk m' evs.
Proof.
  intros body inner i r eff m m' evs Hc Hw H.
  apply clone_with_stores_iff in H as [[Hok (e0 & Hb & ->)] | [_ Hu]]; [|discriminate Hu].
  unfold check_with_stores. rewrite Hok. cbn [negb].
  pose proof (Hc _ _ _ Hb) as Hin. pose proof (Hw _ _ _ Hin) as Hw0.
  destruct e0 as [ret ws zs us cs ci]. cbn [eff_writes] in Hw0. subst ws.
  unfold tid_store_effect, strip_tid_writes. cbn [eff_ret].
  destruct (addr_is_error_b ret) eqn:He; cbn [eff_ret eff_writes eff_zeros eff_unmaps
                                               eff_copies eff_copyins app]; rewrite ?He;
    cbv iota; rewrite Hin; cbv iota.
  - reflexivity.
  - rewrite writes_eqb_refl. reflexivity.
Qed.

Lemma check_with_stores_complete_unmodeled : forall (body : Sys SyscallEffect) inner i r eff m,
  (forall e, body i m Unmodeled -> inner e m = CheckUnmodeled) ->
  clone_with_stores r body i m Unmodeled ->
  check_with_stores i r inner eff m = CheckUnmodeled.
Proof.
  intros body inner i r eff m Hc H.
  unfold check_with_stores.
  apply clone_with_stores_iff in H as [[Hok Hb] | [Hok _]]; rewrite Hok; cbn [negb];
    [|reflexivity].
  rewrite (Hc _ Hb). reflexivity.
Qed.

(** The same four for [clone3]'s, which carries the struct in its
    ledger. *)
Lemma check_clone3_stores_sound_ok : forall i uargs r eff m m' evs,
  check_clone3_stores i uargs r eff m = CheckOk m' evs ->
  clone3_with_stores uargs r i m (Ok eff m' evs).
Proof.
  intros i uargs r eff m m' evs H. unfold check_clone3_stores in H.
  apply check_copyins_after_ok_iff in H as [Hci H].
  unfold clone3_with_stores. apply record_copyins_clear_ok; [exact Hci|].
  apply (check_with_stores_sound_ok (clone_refusable_arm clone_resolve)
           (check_refusable_arm check_clone_resolve)); [|exact H].
  intros e m1 evs1 He. now apply check_arm_resolve_sound_ok.
Qed.

Lemma check_clone3_stores_sound_unmodeled : forall i uargs r eff m,
  check_clone3_stores i uargs r eff m = CheckUnmodeled ->
  clone3_with_stores uargs r i m Unmodeled.
Proof.
  intros i uargs r eff m H. unfold check_clone3_stores in H.
  apply check_copyins_after_unmodeled in H.
  unfold clone3_with_stores. apply record_copyins_unmodeled.
  apply (check_with_stores_sound_unmodeled (clone_refusable_arm clone_resolve)
           (check_refusable_arm check_clone_resolve) i r (clear_copyins eff) m); [|exact H].
  intros e He. now apply check_arm_resolve_sound_unmodeled with (e := e).
Qed.

Lemma check_clone3_stores_complete_ok : forall i uargs r eff m m' evs,
  clone3_with_stores uargs r i m (Ok eff m' evs) ->
  check_clone3_stores i uargs r eff m = CheckOk m' evs.
Proof.
  intros i uargs r eff m m' evs H. unfold clone3_with_stores in H.
  apply record_copyins_ok_inv in H as (core & Hcore & ->).
  assert (Hci : eff_copyins core = []).
  { pose proof Hcore as Hc0.
    apply clone_with_stores_iff in Hc0 as [[_ (e0 & Hb & ->)] | [_ Hu]]; [|discriminate Hu].
    pose proof (check_arm_resolve_complete_ok _ _ _ _ _ Hb) as Hk.
    destruct (check_arm_resolve_no_writes _ _ _ _ Hk) as [_ Hci0].
    unfold tid_store_effect. destruct (addr_is_error_b (eff_ret e0)); [exact Hci0|].
    cbn [eff_copyins]. exact Hci0. }
  unfold check_clone3_stores. apply check_copyins_after_ok_iff. split.
  - unfold with_copyins. cbn [eff_copyins]. rewrite Hci, app_nil_r. reflexivity.
  - replace (clear_copyins (with_copyins ([(uargs, CLONE_ARGS_SIZE_nat)] ++ eff_copyins core)
                              core)) with core.
    + apply (check_with_stores_complete_ok (clone_refusable_arm clone_resolve));
        [| |exact Hcore].
      * intros e m1 evs1 He. now apply check_arm_resolve_complete_ok with (i := i).
      * intros e m1 evs1 He. exact (proj1 (check_arm_resolve_no_writes _ _ _ _ He)).
    + destruct core as [ret ws zs us cs ci]. cbn [eff_copyins] in Hci. subst ci.
      reflexivity.
Qed.

Lemma check_clone3_stores_complete_unmodeled : forall i uargs r eff m,
  clone3_with_stores uargs r i m Unmodeled ->
  check_clone3_stores i uargs r eff m = CheckUnmodeled.
Proof.
  intros i uargs r eff m H. unfold clone3_with_stores in H.
  apply record_copyins_unmodeled_inv in H.
  unfold check_clone3_stores.
  rewrite (check_with_stores_complete_unmodeled (clone_refusable_arm clone_resolve)
             (check_refusable_arm check_clone_resolve) i r (clear_copyins eff) m).
  - reflexivity.
  - intros e Hb. now apply check_arm_resolve_complete_unmodeled with (i := i).
  - exact H.
Qed.

(* ------------------------------------------------------ the lists *)

Lemma check_clone_lists_sound_ok : forall flags eff m m' evs i,
  check_clone_lists i flags eff m = CheckOk m' evs ->
  clone_spec_lists flags i m (Ok eff m' evs).
Proof.
  intros flags eff m m' evs i H.
  unfold check_clone_lists in H. unfold clone_spec_lists.
  destruct (clone_fork_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_resolve_sound_ok|].
  destruct (clone_ns_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_ns_resolve_sound_ok|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4))
    as [r|]; cbv iota in H |- *; [|discriminate].
  destruct (clone_arg_checks r); cbv iota in H |- *;
    [now apply check_clone_einval_sound_ok|].
  destruct (clone_class r); cbv iota in H |- *; try discriminate H.
  - apply (check_with_stores_sound_ok (clone_refusable_arm clone_resolve)
             (check_refusable_arm check_clone_resolve)); [|exact H].
    intros e m1 evs1 He. now apply check_arm_resolve_sound_ok.
  - apply (check_with_stores_sound_ok (clone_refusable_arm clone_ns_resolve)
             (check_refusable_arm check_clone_ns_resolve)); [|exact H].
    intros e m1 evs1 He. now apply check_arm_ns_resolve_sound_ok.
  - now apply check_arm_ns_refused_sound_ok.
Qed.

Lemma check_clone_lists_sound_unmodeled : forall flags eff m i,
  check_clone_lists i flags eff m = CheckUnmodeled -> clone_spec_lists flags i m Unmodeled.
Proof.
  intros flags eff m i H.
  unfold check_clone_lists in H. unfold clone_spec_lists.
  destruct (clone_fork_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_resolve_sound_unmodeled with (eff := eff)|].
  destruct (clone_ns_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_ns_resolve_sound_unmodeled with (eff := eff)|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4))
    as [r|]; cbv iota in H |- *; [|apply unmodeled_intro].
  destruct (clone_arg_checks r); cbv iota in H |- *;
    [now apply check_clone_einval_sound_unmodeled with (eff := eff)|].
  destruct (clone_class r); cbv iota in H |- *.
  - apply (check_with_stores_sound_unmodeled (clone_refusable_arm clone_resolve)
             (check_refusable_arm check_clone_resolve) i r eff m); [|exact H].
    intros e He. now apply check_arm_resolve_sound_unmodeled with (e := e).
  - apply (check_with_stores_sound_unmodeled (clone_refusable_arm clone_ns_resolve)
             (check_refusable_arm check_clone_ns_resolve) i r eff m); [|exact H].
    intros e He. now apply check_arm_ns_resolve_sound_unmodeled with (e := e).
  - now apply check_arm_ns_refused_sound_unmodeled with (e := eff).
  - apply unmodeled_intro.
Qed.

Lemma check_clone_lists_complete_ok : forall flags eff m m' evs i,
  clone_spec_lists flags i m (Ok eff m' evs) ->
  check_clone_lists i flags eff m = CheckOk m' evs.
Proof.
  intros flags eff m m' evs i H.
  unfold clone_spec_lists in H. unfold check_clone_lists.
  destruct (clone_fork_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_resolve_complete_ok with (i := i)|].
  destruct (clone_ns_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_ns_resolve_complete_ok with (i := i)|].
  apply input_bind_ok_inv in H. cbv beta in H.
  destruct (clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4))
    as [r|]; cbv iota in H |- *; [|unfold unmodeled in H; discriminate].
  destruct (clone_arg_checks r); cbv iota in H |- *;
    [now apply check_clone_einval_complete_ok with (i := i)|].
  destruct (clone_class r); cbv iota in H |- *;
    try (unfold unmodeled in H; discriminate H).
  - apply (check_with_stores_complete_ok (clone_refusable_arm clone_resolve)); [| |exact H].
    + intros e m1 evs1 He. now apply check_arm_resolve_complete_ok with (i := i).
    + intros e m1 evs1 He. exact (proj1 (check_arm_resolve_no_writes _ _ _ _ He)).
  - apply (check_with_stores_complete_ok (clone_refusable_arm clone_ns_resolve)); [| |exact H].
    + intros e m1 evs1 He. now apply check_arm_ns_resolve_complete_ok with (i := i).
    + intros e m1 evs1 He. exact (proj1 (check_arm_ns_resolve_no_writes _ _ _ _ He)).
  - now apply check_arm_ns_refused_complete_ok with (i := i).
Qed.

Lemma check_clone_lists_complete_unmodeled : forall flags m i eff,
  clone_spec_lists flags i m Unmodeled -> check_clone_lists i flags eff m = CheckUnmodeled.
Proof.
  intros flags m i eff H.
  unfold clone_spec_lists in H. unfold check_clone_lists.
  destruct (clone_fork_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_resolve_complete_unmodeled with (i := i)|].
  destruct (clone_ns_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_ns_resolve_complete_unmodeled with (i := i)|].
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  destruct (clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4))
    as [r|]; cbv iota in H |- *; [|reflexivity].
  destruct (clone_arg_checks r); cbv iota in H |- *;
    [now apply check_clone_einval_complete_unmodeled with (i := i)|].
  destruct (clone_class r); cbv iota in H |- *.
  - apply (check_with_stores_complete_unmodeled (clone_refusable_arm clone_resolve)); [|exact H].
    intros e Hb. now apply check_arm_resolve_complete_unmodeled with (i := i).
  - apply (check_with_stores_complete_unmodeled (clone_refusable_arm clone_ns_resolve));
      [|exact H].
    intros e Hb. now apply check_arm_ns_resolve_complete_unmodeled with (i := i).
  - now apply check_arm_ns_refused_complete_unmodeled with (i := i).
  - reflexivity.
Qed.

Lemma check_clone3_lists_sound_ok : forall i uargs size eff m m' evs,
  check_clone3_lists i uargs size eff m = CheckOk m' evs ->
  clone3_spec_lists uargs size i m (Ok eff m' evs).
Proof.
  intros i uargs size eff m m' evs H.
  unfold check_clone3_lists in H. unfold clone3_spec_lists.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE))) eqn:Hsz;
    cbv iota; cbv iota in H; [discriminate|].
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE)
    as [bs|] eqn:Hbs; cbv iota; cbv iota in H.
  2: { (* the walk declined: only a refused range answers, with -EFAULT *)
       destruct (negb (access_okb uargs CLONE_ARGS_SIZE)) eqn:Hs;
         cbv iota; cbv iota in H; [|discriminate].
       apply check_ret_only_ok_iff in H as (-> & -> & ->).
       unfold err_ret, ret_only. apply pure_ok. }
  destruct (clone3_fork_args_b bs) eqn:Ha;
    cbv iota; cbv iota in H; [now apply check_clone3_resolve_sound_ok|].
  destruct (clone3_einval_b bs) eqn:He;
    cbv iota; cbv iota in H; [now apply check_clone3_einval_sound_ok|].
  destruct (clone3_pre bs) as [| |r]; cbv iota in H |- *; try discriminate H.
  destruct (clone_class r); cbv iota in H |- *; try discriminate H.
  now apply check_clone3_stores_sound_ok.
Qed.

Lemma check_clone3_lists_sound_unmodeled : forall i uargs size eff m,
  check_clone3_lists i uargs size eff m = CheckUnmodeled ->
  clone3_spec_lists uargs size i m Unmodeled.
Proof.
  intros i uargs size eff m H.
  unfold check_clone3_lists in H. unfold clone3_spec_lists.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE))) eqn:Hsz;
    cbv iota; cbv iota in H; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE)
    as [bs|] eqn:Hbs; cbv iota; cbv iota in H.
  2: { destruct (negb (access_okb uargs CLONE_ARGS_SIZE)) eqn:Hs;
         cbv iota; cbv iota in H;
         [now apply check_ret_only_no_unmodeled in H|apply unmodeled_intro]. }
  destruct (clone3_fork_args_b bs) eqn:Ha;
    cbv iota; cbv iota in H;
    [now apply check_clone3_resolve_sound_unmodeled with (eff := eff)|].
  destruct (clone3_einval_b bs) eqn:He; cbv iota; cbv iota in H.
  { exfalso. unfold check_clone3_einval in H.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ H). }
  destruct (clone3_pre bs) as [| |r]; cbv iota in H |- *; [apply unmodeled_intro
                                                           | apply unmodeled_intro|].
  destruct (clone_class r); cbv iota in H |- *;
    [now apply check_clone3_stores_sound_unmodeled with (eff := eff)
    | apply unmodeled_intro | apply unmodeled_intro | apply unmodeled_intro].
Qed.

Lemma check_clone3_lists_complete_ok : forall i uargs size eff m m' evs,
  clone3_spec_lists uargs size i m (Ok eff m' evs) ->
  check_clone3_lists i uargs size eff m = CheckOk m' evs.
Proof.
  intros i uargs size eff m m' evs H.
  unfold clone3_spec_lists in H. unfold check_clone3_lists.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE))) eqn:Hsz;
    cbv iota in H; [unfold unmodeled in H; discriminate|].
  sys_unfold. cbv iota in H. inv_ok.
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE)
    as [bs|] eqn:Hbs; hall Hbs; inv_ok.
  2: { (* -EFAULT with nothing recorded, the only answer of a refused range *)
       destruct (negb (access_okb uargs CLONE_ARGS_SIZE)) eqn:Hs; hall Hs; inv_ok.
       apply check_ret_only_ok_iff. now repeat split. }
  destruct (clone3_fork_args_b bs) eqn:Ha; hall Ha; inv_ok.
  { now apply check_clone3_resolve_complete_ok with (i := i). }
  destruct (clone3_einval_b bs) eqn:He; hall He; inv_ok.
  { now apply check_clone3_einval_complete_ok with (i := i). }
  destruct (clone3_pre bs) as [| |r] eqn:Hp3; hall Hp3; inv_ok.
  destruct (clone_class r) eqn:Hcc; hall Hcc; inv_ok.
  match goal with Hx : clone3_with_stores _ _ _ _ _ |- _ =>
    now apply check_clone3_stores_complete_ok end.
Qed.

Lemma check_clone3_lists_complete_unmodeled : forall i uargs size m eff,
  clone3_spec_lists uargs size i m Unmodeled ->
  check_clone3_lists i uargs size eff m = CheckUnmodeled.
Proof.
  intros i uargs size m eff H.
  unfold clone3_spec_lists in H. unfold check_clone3_lists.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE))) eqn:Hsz;
    cbv iota in H; [reflexivity|].
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE)
    as [bs|] eqn:Hbs; cbv iota in H |- *.
  2: { destruct (negb (access_okb uargs CLONE_ARGS_SIZE)) eqn:Hs; cbv iota in H |- *;
         [unfold err_ret, ret_only, pure in H; discriminate H | reflexivity]. }
  destruct (clone3_fork_args_b bs) eqn:Ha; cbv iota in H |- *.
  { now apply check_clone3_resolve_complete_unmodeled with (i := i). }
  destruct (clone3_einval_b bs) eqn:He; cbv iota in H |- *.
  { exfalso; eapply clone3_einval_not_unmodeled; eassumption. }
  destruct (clone3_pre bs) as [| |r]; cbv iota in H |- *; try reflexivity.
  destruct (clone_class r); cbv iota in H |- *; try reflexivity.
  now apply check_clone3_stores_complete_unmodeled.
Qed.

(* ------------------------------------------- what an accepted answer is *)

(** An accepted answer of [check_with_stores] is its body's checker's
    answer on the stripped effect, with the same return. *)
Lemma check_with_stores_ok_inv : forall i r inner eff m m' evs,
  check_with_stores i r inner eff m = CheckOk m' evs ->
  inner (strip_tid_writes eff) m = CheckOk m' evs.
Proof.
  intros i r inner eff m m' evs H. unfold check_with_stores in H.
  destruct (negb (clone_stores_ok i m r)); cbv iota in H; [discriminate H|].
  destruct (inner (strip_tid_writes eff) m) as [m1 evs1| |] eqn:Hin; cbv iota in H;
    try discriminate H.
  destruct (addr_is_error_b (eff_ret eff)
            || writes_eqb (eff_writes eff)
                 (tid_writes (in_wmem i) (clone_parent_tid r) (eff_ret eff)));
    cbv iota in H; [|discriminate H].
  injection H as <- <-. reflexivity.
Qed.

Lemma strip_tid_writes_ret : forall eff, eff_ret (strip_tid_writes eff) = eff_ret eff.
Proof.
  intros eff. unfold strip_tid_writes. destruct (addr_is_error_b (eff_ret eff)); reflexivity.
Qed.

(** Every answer [check_clone_lists] accepts is a refusal's inside an arm
    of a decoded record (the model and the events as they were), or one
    of four checkers' answers with the same return: the frame lemmas over
    the dispatcher read the model and events off these. *)
Lemma check_clone_lists_ok_inv : forall i flags eff m m' evs,
  check_clone_lists i flags eff m = CheckOk m' evs ->
  (m' = m /\ evs = [] /\ addr_is_error_b (eff_ret eff) = true)
  \/ (exists e, check_clone_resolve e m = CheckOk m' evs /\ eff_ret e = eff_ret eff)
  \/ (exists e, check_clone_ns_resolve e m = CheckOk m' evs /\ eff_ret e = eff_ret eff)
  \/ check_clone_einval eff m = CheckOk m' evs
  \/ check_clone_ns_refused eff m = CheckOk m' evs.
Proof.
  intros i flags eff m m' evs H. unfold check_clone_lists in H.
  destruct (clone_fork_flags_b flags); cbv iota in H.
  { right; left. exists eff. split; [exact H | reflexivity]. }
  destruct (clone_ns_flags_b flags); cbv iota in H.
  { right; right; left. exists eff. split; [exact H | reflexivity]. }
  destruct (clone_args_of_clone flags (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4))
    as [r|]; cbv iota in H; [|discriminate H].
  destruct (clone_arg_checks r); cbv iota in H.
  { right; right; right; left. exact H. }
  destruct (clone_class r); cbv iota in H.
  - apply check_with_stores_ok_inv in H.
    apply check_refusable_arm_ok_inv in H as [(-> & -> & He) | H].
    + left. rewrite strip_tid_writes_ret in He.
      split; [reflexivity|]. split; [reflexivity | exact He].
    + right; left. exists (strip_tid_writes eff).
      split; [exact H | apply strip_tid_writes_ret].
  - apply check_with_stores_ok_inv in H.
    apply check_refusable_arm_ok_inv in H as [(-> & -> & He) | H].
    + left. rewrite strip_tid_writes_ret in He.
      split; [reflexivity|]. split; [reflexivity | exact He].
    + right; right; left. exists (strip_tid_writes eff).
      split; [exact H | apply strip_tid_writes_ret].
  - apply check_refusable_arm_ok_inv in H as [(-> & -> & He) | H].
    + left. split; [reflexivity|]. split; [reflexivity | exact He].
    + right; right; right; right. exact H.
  - discriminate H.
Qed.

Lemma check_clone3_lists_ok_inv : forall i uargs size eff m m' evs,
  check_clone3_lists i uargs size eff m = CheckOk m' evs ->
  (m' = m /\ evs = [] /\ addr_is_error_b (eff_ret eff) = true)
  \/ check_clone3_resolve uargs eff m = CheckOk m' evs
  \/ check_ret_only eff (errno_ret EFAULT) m [] = CheckOk m' evs
  \/ check_clone3_einval uargs eff m = CheckOk m' evs
  \/ (exists e, check_clone_resolve e m = CheckOk m' evs /\ eff_ret e = eff_ret eff).
Proof.
  intros i uargs size eff m m' evs H. unfold check_clone3_lists in H.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE))); cbv iota in H;
    [discriminate H|].
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE) as [bs|]; cbv iota in H.
  2: { destruct (negb (access_okb uargs CLONE_ARGS_SIZE)); cbv iota in H; [|discriminate H].
       right; right; left. exact H. }
  destruct (clone3_fork_args_b bs); cbv iota in H; [right; left; exact H|].
  destruct (clone3_einval_b bs); cbv iota in H; [right; right; right; left; exact H|].
  destruct (clone3_pre bs) as [| |r]; cbv iota in H; try discriminate H.
  destruct (clone_class r); cbv iota in H; try discriminate H.
  unfold check_clone3_stores in H.
  apply check_copyins_after_ok_iff in H as [_ H].
  apply check_with_stores_ok_inv in H.
  apply check_refusable_arm_ok_inv in H as [(-> & -> & He) | H].
  - left. rewrite strip_tid_writes_ret in He.
    split; [reflexivity|]. split; [reflexivity | exact He].
  - right; right; right; right. exists (strip_tid_writes (clear_copyins eff)).
    split; [exact H|]. rewrite strip_tid_writes_ret. reflexivity.
Qed.

Lemma check_clone_lists_shape : forall i flags eff m m' evs,
  check_clone_lists i flags eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros i flags eff m m' evs H.
  destruct (check_clone_lists_ok_inv _ _ _ _ _ _ H)
    as [(-> & -> & He)|[(e & He & Hr)|[(e & He & Hr)|[He|He]]]].
  - split; [reflexivity|]. left. split; [reflexivity | exact He].
  - exact (clone_answer_shape_ret _ _ _ _ _ Hr (check_clone_resolve_shape _ _ _ _ He)).
  - exact (clone_answer_shape_ret _ _ _ _ _ Hr (check_clone_ns_resolve_shape _ _ _ _ He)).
  - exact (check_clone_einval_shape _ _ _ _ He).
  - exact (check_clone_ns_refused_shape _ _ _ _ He).
Qed.

Lemma check_clone3_lists_shape : forall i uargs size eff m m' evs,
  check_clone3_lists i uargs size eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros i uargs size eff m m' evs H.
  destruct (check_clone3_lists_ok_inv _ _ _ _ _ _ _ H)
    as [(-> & -> & He)|[He|[He|[He|(e & He & Hr)]]]].
  - split; [reflexivity|]. left. split; [reflexivity | exact He].
  - exact (check_clone3_resolve_shape _ _ _ _ _ He).
  - apply check_ret_only_ok_iff in He as (-> & -> & ->).
    split; [reflexivity|]. left. split; [reflexivity|]. vm_compute. reflexivity.
  - unfold check_clone3_einval in He.
    apply check_ret_only_copyins_ok_iff in He as (-> & -> & ->).
    split; [reflexivity|]. left. split; [reflexivity|]. vm_compute. reflexivity.
  - exact (clone_answer_shape_ret _ _ _ _ _ Hr (check_clone_resolve_shape _ _ _ _ He)).
Qed.

(* ----------------------------------------- the host refusers at the top *)

Lemma clone3_refused_eff_b_error : forall uargs eff,
  clone3_refused_eff_b uargs eff = true -> addr_is_error_b (eff_ret eff) = true.
Proof.
  intros uargs [ret ws zs us cs ci] H. destruct ws, zs, us, cs; try discriminate H.
  destruct ci as [|[a n] [|? ?]]; try discriminate H.
  cbn [clone3_refused_eff_b] in H. apply andb_true_iff in H as [_ H]. exact H.
Qed.

(** A refusal's effect the lists accept leaves the model unchanged: an
    error-encoded return is no admissible pid ([clone_pid_not_error]). *)
Lemma check_clone_lists_refused_shape : forall flags eff m m' evs i,
  clone_refused_eff_b eff = true ->
  check_clone_lists i flags eff m = CheckOk m' evs -> m' = m /\ evs = [].
Proof.
  intros flags eff m m' evs i Hr H.
  exact (clone_answer_shape_refused _ _ _ _ (clone_refused_eff_b_error _ Hr)
           (check_clone_lists_shape _ _ _ _ _ _ H)).
Qed.

Lemma check_clone3_lists_refused_shape : forall i uargs size eff m m' evs,
  clone3_refused_eff_b uargs eff = true ->
  check_clone3_lists i uargs size eff m = CheckOk m' evs -> m' = m /\ evs = [].
Proof.
  intros i uargs size eff m m' evs Hr H.
  exact (clone_answer_shape_refused _ _ _ _ (clone3_refused_eff_b_error _ _ Hr)
           (check_clone3_lists_shape _ _ _ _ _ _ _ H)).
Qed.

(** An answered word with the gate open never declines. *)
Lemma check_clone_lists_answered : forall flags eff m i,
  (clone_fork_flags_b flags || clone_ns_flags_b flags) = true ->
  clone_no_shared_file_b (forfeit_inherited (m_fds m)) = true ->
  check_clone_lists i flags eff m <> CheckUnmodeled.
Proof.
  intros flags [ret ws zs us cs cis] m i Ha Hg H.
  unfold check_clone_lists, check_clone_resolve, check_clone_ns_resolve in H.
  destruct (clone_fork_flags_b flags);
    [|destruct (clone_ns_flags_b flags); [|discriminate Ha]];
    cbv iota in H; rewrite Hg in H; cbn [negb] in H;
    destruct ws, zs, us, cs, cis; cbv beta iota in H; try discriminate H;
    unfold check_clone_answer, check_clone_ns_answer in H;
    repeat match type of H with
           | context [if ?b then _ else _] => destruct b; cbv beta iota in H
           end;
    discriminate H.
Qed.

Lemma check_clone3_lists_answered : forall i uargs size eff m,
  clone3_answered_b uargs size i = true ->
  clone_no_shared_file_b (forfeit_inherited (m_fds m)) = true ->
  check_clone3_lists i uargs size eff m <> CheckUnmodeled.
Proof.
  intros i uargs size eff m Ha Hg H.
  unfold clone3_answered_b in Ha. apply andb_true_iff in Ha as [Hs Hb].
  unfold check_clone3_lists in H. rewrite Hs in H. cbn [negb] in H.
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE) as [bs|];
    cbv beta iota in Hb, H; [|discriminate Hb].
  rewrite Hb in H. cbv beta iota in H.
  unfold check_clone3_resolve in H. rewrite Hg in H. cbn [negb] in H.
  destruct eff as [ret ws zs us cs cis].
  destruct ws, zs, us, cs; cbv beta iota in H; try discriminate H.
  destruct cis as [|[a n] [|? ?]]; cbv beta iota in H; try discriminate H.
  destruct (bv_eqb a uargs && Nat.eqb n CLONE_ARGS_SIZE_nat); cbv beta iota in H;
    [|discriminate H].
  unfold check_clone_answer in H.
  repeat match type of H with
           | context [if ?b then _ else _] => destruct b; cbv beta iota in H
           end;
    discriminate H.
Qed.

Lemma check_clone_sound_ok : forall i flags eff m m' evs,
  check_clone i flags eff m = CheckOk m' evs -> clone_spec flags i m (Ok eff m' evs).
Proof.
  intros i flags eff m m' evs H. unfold check_clone in H. unfold clone_spec.
  apply (check_refusable_sound_ok _ _ _ (clone_refused_eff_b eff)
           (check_clone_lists i flags eff m)); [ | | exact H].
  - intros Hr. apply clone_refused_eff_b_ok. exact Hr.
  - intros Hl. apply check_clone_lists_sound_ok. exact Hl.
Qed.

Lemma check_clone_sound_unmodeled : forall i flags eff m,
  check_clone i flags eff m = CheckUnmodeled -> clone_spec flags i m Unmodeled.
Proof.
  intros i flags eff m H. unfold check_clone in H. unfold clone_spec.
  apply (check_refusable_sound_unmodeled _ _ _ (clone_refused_eff_b eff)
           (check_clone_lists i flags eff m)); [|exact H].
  intros Hl. apply (check_clone_lists_sound_unmodeled flags eff). exact Hl.
Qed.

Lemma check_clone_complete_ok : forall i flags eff m m' evs,
  clone_spec flags i m (Ok eff m' evs) -> check_clone i flags eff m = CheckOk m' evs.
Proof.
  intros i flags eff m m' evs H. unfold clone_spec in H. unfold check_clone.
  apply (check_refusable_complete_ok
           (fun _ => clone_fork_flags_b flags || clone_ns_flags_b flags)
           clone_refused_fail (clone_spec_lists flags) _ _ i m m' eff evs);
    [ | | | exact H].
  - apply clone_refused_fail_shape.
  - intros Hk. exact (check_clone_lists_complete_ok flags eff m m' evs i Hk).
  - intros Hr Hl. exact (check_clone_lists_refused_shape flags eff m m' evs i Hr Hl).
Qed.

Lemma check_clone_complete_unmodeled : forall i flags m eff,
  clone_spec flags i m Unmodeled -> check_clone i flags eff m = CheckUnmodeled.
Proof.
  intros i flags m eff H. unfold clone_spec in H. unfold check_clone.
  apply (check_refusable_complete_unmodeled
           (fun _ => clone_fork_flags_b flags || clone_ns_flags_b flags)
           clone_refused_fail (clone_spec_lists flags) _ _ i); [ | | | exact H].
  - intros Hf. apply clone_refused_fail_inv in Hf as (e & _ & Heq). discriminate Heq.
  - intros Hk. exact (check_clone_lists_complete_unmodeled flags m i eff Hk).
  - intros Ha Hg Hk.
    exact (check_clone_lists_answered flags eff m i Ha Hg
             (check_clone_lists_complete_unmodeled flags m i eff Hk)).
Qed.

Lemma check_clone3_sound_ok : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs ->
  clone3_spec uargs size i m (Ok eff m' evs).
Proof.
  intros i uargs size eff m m' evs H. unfold check_clone3 in H. unfold clone3_spec.
  apply (check_refusable_sound_ok _ _ _ (clone3_refused_eff_b uargs eff)
           (check_clone3_lists i uargs size eff m)); [ | | exact H].
  - intros Hr. apply clone3_refused_eff_b_ok. exact Hr.
  - intros Hl. apply check_clone3_lists_sound_ok. exact Hl.
Qed.

Lemma check_clone3_sound_unmodeled : forall i uargs size eff m,
  check_clone3 i uargs size eff m = CheckUnmodeled ->
  clone3_spec uargs size i m Unmodeled.
Proof.
  intros i uargs size eff m H. unfold check_clone3 in H. unfold clone3_spec.
  apply (check_refusable_sound_unmodeled _ _ _ (clone3_refused_eff_b uargs eff)
           (check_clone3_lists i uargs size eff m)); [|exact H].
  intros Hl. apply (check_clone3_lists_sound_unmodeled i uargs size eff). exact Hl.
Qed.

Lemma check_clone3_complete_ok : forall i uargs size eff m m' evs,
  clone3_spec uargs size i m (Ok eff m' evs) ->
  check_clone3 i uargs size eff m = CheckOk m' evs.
Proof.
  intros i uargs size eff m m' evs H. unfold clone3_spec in H. unfold check_clone3.
  apply (check_refusable_complete_ok (clone3_answered_b uargs size)
           (clone3_refused_fail uargs) (clone3_spec_lists uargs size) _ _ i m m' eff evs);
    [ | | | exact H].
  - apply clone3_refused_fail_shape.
  - intros Hk. exact (check_clone3_lists_complete_ok i uargs size eff m m' evs Hk).
  - intros Hr Hl.
    exact (check_clone3_lists_refused_shape i uargs size eff m m' evs Hr Hl).
Qed.

Lemma check_clone3_complete_unmodeled : forall i uargs size m eff,
  clone3_spec uargs size i m Unmodeled ->
  check_clone3 i uargs size eff m = CheckUnmodeled.
Proof.
  intros i uargs size m eff H. unfold clone3_spec in H. unfold check_clone3.
  apply (check_refusable_complete_unmodeled (clone3_answered_b uargs size)
           (clone3_refused_fail uargs) (clone3_spec_lists uargs size) _ _ i);
    [ | | | exact H].
  - intros Hf. apply clone3_refused_fail_inv in Hf as (e & _ & Heq). discriminate Heq.
  - intros Hk. exact (check_clone3_lists_complete_unmodeled i uargs size m eff Hk).
  - intros Ha Hg Hk.
    exact (check_clone3_lists_answered i uargs size eff m Ha Hg
             (check_clone3_lists_complete_unmodeled i uargs size m eff Hk)).
Qed.

(** Every answer [check_clone] accepts is a refusal's, with the model and
    the events unchanged, or the lists' checker's: the shape the frame
    lemmas of [Checks] take the checker apart by. *)
Lemma check_clone_cases : forall i flags eff m m' evs,
  check_clone i flags eff m = CheckOk m' evs ->
  (m' = m /\ evs = [] /\ addr_is_error_b (eff_ret eff) = true)
  \/ check_clone_lists i flags eff m = CheckOk m' evs.
Proof.
  intros i flags eff m m' evs H. unfold check_clone in H.
  apply check_refusable_ok_inv in H as [(Hr & -> & ->) | H]; [left | right; exact H].
  split; [reflexivity|]. split; [reflexivity | exact (clone_refused_eff_b_error _ Hr)].
Qed.

Lemma check_clone3_cases : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs ->
  (m' = m /\ evs = [] /\ addr_is_error_b (eff_ret eff) = true)
  \/ check_clone3_lists i uargs size eff m = CheckOk m' evs.
Proof.
  intros i uargs size eff m m' evs H. unfold check_clone3 in H.
  apply check_refusable_ok_inv in H as [(Hr & -> & ->) | H]; [left | right; exact H].
  split; [reflexivity|]. split; [reflexivity | exact (clone3_refused_eff_b_error _ _ Hr)].
Qed.

(** [check_clone_lists_ok_inv] and [check_clone3_lists_ok_inv] through the
    refusers' layer: a refusal there has the same shape as one inside an
    arm. *)
Lemma check_clone_ok_inv : forall i flags eff m m' evs,
  check_clone i flags eff m = CheckOk m' evs ->
  (m' = m /\ evs = [] /\ addr_is_error_b (eff_ret eff) = true)
  \/ (exists e, check_clone_resolve e m = CheckOk m' evs /\ eff_ret e = eff_ret eff)
  \/ (exists e, check_clone_ns_resolve e m = CheckOk m' evs /\ eff_ret e = eff_ret eff)
  \/ check_clone_einval eff m = CheckOk m' evs
  \/ check_clone_ns_refused eff m = CheckOk m' evs.
Proof.
  intros i flags eff m m' evs H.
  apply check_clone_cases in H as [Hr | H]; [left; exact Hr|].
  exact (check_clone_lists_ok_inv _ _ _ _ _ _ H).
Qed.

Lemma check_clone3_ok_inv : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs ->
  (m' = m /\ evs = [] /\ addr_is_error_b (eff_ret eff) = true)
  \/ check_clone3_resolve uargs eff m = CheckOk m' evs
  \/ check_ret_only eff (errno_ret EFAULT) m [] = CheckOk m' evs
  \/ check_clone3_einval uargs eff m = CheckOk m' evs
  \/ (exists e, check_clone_resolve e m = CheckOk m' evs /\ eff_ret e = eff_ret eff).
Proof.
  intros i uargs size eff m m' evs H.
  apply check_clone3_cases in H as [Hr | H]; [left; exact Hr|].
  exact (check_clone3_lists_ok_inv _ _ _ _ _ _ _ H).
Qed.

Lemma check_clone_shape : forall i flags eff m m' evs,
  check_clone i flags eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros i flags eff m m' evs H.
  apply check_clone_cases in H as [(-> & -> & He) | H].
  - split; [reflexivity|]. left. split; [reflexivity | exact He].
  - exact (check_clone_lists_shape _ _ _ _ _ _ H).
Qed.

Lemma check_clone3_shape : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs -> clone_answer_shape eff m m' evs.
Proof.
  intros i uargs size eff m m' evs H.
  apply check_clone3_cases in H as [(-> & -> & He) | H].
  - split; [reflexivity|]. left. split; [reflexivity | exact He].
  - exact (check_clone3_lists_shape _ _ _ _ _ _ _ H).
Qed.
