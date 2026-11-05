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

Definition check_clone_lists (flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if clone_fork_flags_b flags then check_clone_resolve eff m
  else if clone_ns_flags_b flags then check_clone_ns_resolve eff m
  else CheckUnmodeled.

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
           else CheckUnmodeled
       end.

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

Lemma check_clone_lists_sound_ok : forall flags eff m m' evs i,
  check_clone_lists flags eff m = CheckOk m' evs -> clone_spec_lists flags i m (Ok eff m' evs).
Proof.
  intros flags eff m m' evs i H.
  unfold check_clone_lists in H. unfold clone_spec_lists.
  destruct (clone_fork_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_resolve_sound_ok|].
  destruct (clone_ns_flags_b flags); cbv iota in H |- *; [|discriminate].
  now apply check_clone_ns_resolve_sound_ok.
Qed.

Lemma check_clone_lists_sound_unmodeled : forall flags eff m i,
  check_clone_lists flags eff m = CheckUnmodeled -> clone_spec_lists flags i m Unmodeled.
Proof.
  intros flags eff m i H.
  unfold check_clone_lists in H. unfold clone_spec_lists.
  destruct (clone_fork_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_resolve_sound_unmodeled with (eff := eff)|].
  destruct (clone_ns_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_ns_resolve_sound_unmodeled with (eff := eff)
    |apply unmodeled_intro].
Qed.

Lemma check_clone_lists_complete_ok : forall flags eff m m' evs i,
  clone_spec_lists flags i m (Ok eff m' evs) -> check_clone_lists flags eff m = CheckOk m' evs.
Proof.
  intros flags eff m m' evs i H.
  unfold clone_spec_lists in H. unfold check_clone_lists.
  destruct (clone_fork_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_resolve_complete_ok with (i := i)|].
  destruct (clone_ns_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_ns_resolve_complete_ok with (i := i)
    |unfold unmodeled in H; discriminate].
Qed.

Lemma check_clone_lists_complete_unmodeled : forall flags m i eff,
  clone_spec_lists flags i m Unmodeled -> check_clone_lists flags eff m = CheckUnmodeled.
Proof.
  intros flags m i eff H.
  unfold clone_spec_lists in H. unfold check_clone_lists.
  destruct (clone_fork_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_resolve_complete_unmodeled with (i := i)|].
  destruct (clone_ns_flags_b flags); cbv iota in H |- *;
    [now apply check_clone_ns_resolve_complete_unmodeled with (i := i)
    |reflexivity].
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
    cbv iota; cbv iota in H; [|discriminate].
  now apply check_clone3_resolve_sound_ok.
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
    cbv iota; cbv iota in H; [|apply unmodeled_intro].
  now apply check_clone3_resolve_sound_unmodeled with (eff := eff).
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
  now apply check_clone3_resolve_complete_ok with (i := i).
Qed.

Lemma check_clone3_lists_complete_unmodeled : forall i uargs size m eff,
  clone3_spec_lists uargs size i m Unmodeled ->
  check_clone3_lists i uargs size eff m = CheckUnmodeled.
Proof.
  intros i uargs size m eff H.
  unfold clone3_spec_lists in H. unfold check_clone3_lists.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE))) eqn:Hsz;
    cbv iota in H; [reflexivity|].
  sys_unfold. cbv iota in H. inv_ok.
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE)
    as [bs|] eqn:Hbs; hall Hbs; inv_ok.
  2: { destruct (negb (access_okb uargs CLONE_ARGS_SIZE)) eqn:Hs; hall Hs;
         inv_ok; reflexivity. }
  destruct (clone3_fork_args_b bs) eqn:Ha; hall Ha; inv_ok; [|reflexivity].
  now apply check_clone3_resolve_complete_unmodeled with (i := i).
Qed.


(* ------------------------------------------------- the host's clone refusers *)

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

Definition check_clone (flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_refusable (clone_fork_flags_b flags || clone_ns_flags_b flags)
    (clone_refused_eff_b eff) m (check_clone_lists flags eff m).

Definition check_clone3 (i : SyscallInput) (uargs size : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_refusable (clone3_answered_b uargs size i)
    (clone3_refused_eff_b uargs eff) m (check_clone3_lists i uargs size eff m).

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

(** A refusal's effect the lists accept leaves the model unchanged: an
    error-encoded return is no admissible pid ([clone_pid_not_error]). *)
Lemma check_clone_lists_refused_shape : forall flags eff m m' evs,
  clone_refused_eff_b eff = true ->
  check_clone_lists flags eff m = CheckOk m' evs -> m' = m /\ evs = [].
Proof.
  intros flags [ret ws zs us cs cis] m m' evs Hr H.
  destruct ws, zs, us, cs, cis; try discriminate Hr.
  cbn [clone_refused_eff_b] in Hr.
  unfold check_clone_lists, check_clone_resolve, check_clone_ns_resolve in H.
  destruct (clone_fork_flags_b flags); [|destruct (clone_ns_flags_b flags)];
    destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))));
    cbv beta iota in H; try discriminate H.
  - unfold check_clone_answer in H.
    destruct (errno_ret_in clone_errnos ret); [injection H as <- <-; split; reflexivity|].
    destruct (clone_pid_ok_b m ret) eqn:Hv; [|discriminate H].
    rewrite (clone_pid_not_error m ret Hv) in Hr. discriminate Hr.
  - unfold check_clone_ns_answer in H.
    destruct (errno_any_b ret); [injection H as <- <-; split; reflexivity|].
    destruct (clone_pid_ok_b m ret) eqn:Hv; [|discriminate H].
    rewrite (clone_pid_not_error m ret Hv) in Hr. discriminate Hr.
Qed.

Lemma check_clone3_lists_refused_shape : forall i uargs size eff m m' evs,
  clone3_refused_eff_b uargs eff = true ->
  check_clone3_lists i uargs size eff m = CheckOk m' evs -> m' = m /\ evs = [].
Proof.
  intros i uargs size eff m m' evs Hr H.
  unfold check_clone3_lists in H.
  destruct (negb (bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE))); cbv beta iota in H;
    [discriminate H|].
  destruct (copy_bytes_map (in_mem i) uargs CLONE_ARGS_SIZE) as [bs|];
    cbv beta iota in H.
  - destruct (clone3_fork_args_b bs); cbv beta iota in H; [|discriminate H].
    unfold check_clone3_resolve in H.
    destruct (negb (clone_no_shared_file_b (forfeit_inherited (m_fds m))));
      cbv beta iota in H; [discriminate H|].
    destruct eff as [ret ws zs us cs cis].
    destruct ws, zs, us, cs; cbv beta iota in H; try discriminate H.
    destruct cis as [|[a n] [|? ?]]; cbv beta iota in H; try discriminate H.
    destruct (bv_eqb a uargs && Nat.eqb n CLONE_ARGS_SIZE_nat); cbv beta iota in H;
      [|discriminate H].
    unfold check_clone_answer in H. cbn [clone3_refused_eff_b] in Hr.
    apply andb_true_iff in Hr as [_ Hr].
    destruct (errno_ret_in clone_errnos ret); [injection H as <- <-; split; reflexivity|].
    destruct (clone_pid_ok_b m ret) eqn:Hv; [|discriminate H].
    rewrite (clone_pid_not_error m ret Hv) in Hr. discriminate Hr.
  - destruct (negb (access_okb uargs CLONE_ARGS_SIZE)); cbv beta iota in H;
      [|discriminate H].
    apply check_ret_only_ok_iff in H as (_ & -> & ->). split; reflexivity.
Qed.

(** An answered word with the gate open never declines. *)
Lemma check_clone_lists_answered : forall flags eff m,
  (clone_fork_flags_b flags || clone_ns_flags_b flags) = true ->
  clone_no_shared_file_b (forfeit_inherited (m_fds m)) = true ->
  check_clone_lists flags eff m <> CheckUnmodeled.
Proof.
  intros flags [ret ws zs us cs cis] m Ha Hg H.
  unfold check_clone_lists, check_clone_resolve, check_clone_ns_resolve in H.
  rewrite Hg in H. cbn [negb] in H.
  destruct (clone_fork_flags_b flags);
    [|destruct (clone_ns_flags_b flags); [|discriminate Ha]];
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

Lemma check_clone_sound_ok : forall flags eff m m' evs i,
  check_clone flags eff m = CheckOk m' evs -> clone_spec flags i m (Ok eff m' evs).
Proof.
  intros flags eff m m' evs i H. unfold check_clone in H. unfold clone_spec.
  apply (check_refusable_sound_ok _ _ _ (clone_refused_eff_b eff)
           (check_clone_lists flags eff m)); [ | | exact H].
  - intros Hr. apply clone_refused_eff_b_ok. exact Hr.
  - intros Hl. apply check_clone_lists_sound_ok. exact Hl.
Qed.

Lemma check_clone_sound_unmodeled : forall flags eff m i,
  check_clone flags eff m = CheckUnmodeled -> clone_spec flags i m Unmodeled.
Proof.
  intros flags eff m i H. unfold check_clone in H. unfold clone_spec.
  apply (check_refusable_sound_unmodeled _ _ _ (clone_refused_eff_b eff)
           (check_clone_lists flags eff m)); [|exact H].
  intros Hl. apply (check_clone_lists_sound_unmodeled flags eff). exact Hl.
Qed.

Lemma check_clone_complete_ok : forall flags eff m m' evs i,
  clone_spec flags i m (Ok eff m' evs) -> check_clone flags eff m = CheckOk m' evs.
Proof.
  intros flags eff m m' evs i H. unfold clone_spec in H. unfold check_clone.
  apply (check_refusable_complete_ok
           (fun _ => clone_fork_flags_b flags || clone_ns_flags_b flags)
           clone_refused_fail (clone_spec_lists flags) _ _ i m m' eff evs);
    [ | | | exact H].
  - apply clone_refused_fail_shape.
  - intros Hk. exact (check_clone_lists_complete_ok flags eff m m' evs i Hk).
  - intros Hr Hl. exact (check_clone_lists_refused_shape flags eff m m' evs Hr Hl).
Qed.

Lemma check_clone_complete_unmodeled : forall flags m i eff,
  clone_spec flags i m Unmodeled -> check_clone flags eff m = CheckUnmodeled.
Proof.
  intros flags m i eff H. unfold clone_spec in H. unfold check_clone.
  apply (check_refusable_complete_unmodeled
           (fun _ => clone_fork_flags_b flags || clone_ns_flags_b flags)
           clone_refused_fail (clone_spec_lists flags) _ _ i); [ | | | exact H].
  - intros Hf. apply clone_refused_fail_inv in Hf as (e & _ & Heq). discriminate Heq.
  - intros Hk. exact (check_clone_lists_complete_unmodeled flags m i eff Hk).
  - intros Ha Hg Hk.
    exact (check_clone_lists_answered flags eff m Ha Hg
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
Lemma check_clone_cases : forall flags eff m m' evs,
  check_clone flags eff m = CheckOk m' evs ->
  (m' = m /\ evs = [] /\ addr_is_error_b (eff_ret eff) = true)
  \/ check_clone_lists flags eff m = CheckOk m' evs.
Proof.
  intros flags eff m m' evs H. unfold check_clone, check_refusable in H.
  destruct ((clone_fork_flags_b flags || clone_ns_flags_b flags)
            && clone_refused_b (m_clone_refusers m)
            && clone_no_shared_file_b (forfeit_inherited (m_fds m))
            && clone_refused_eff_b eff) eqn:Hc; cbv beta iota in H.
  - left. injection H as <- <-. split; [reflexivity|]. split; [reflexivity|].
    apply andb_true_iff in Hc as [_ Hr].
    destruct eff as [ret ws zs us cs cis]. cbn [eff_ret].
    destruct ws, zs, us, cs, cis; try discriminate Hr. exact Hr.
  - right. exact H.
Qed.

Lemma check_clone3_cases : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs ->
  (m' = m /\ evs = [] /\ addr_is_error_b (eff_ret eff) = true)
  \/ check_clone3_lists i uargs size eff m = CheckOk m' evs.
Proof.
  intros i uargs size eff m m' evs H. unfold check_clone3, check_refusable in H.
  destruct (clone3_answered_b uargs size i
            && clone_refused_b (m_clone_refusers m)
            && clone_no_shared_file_b (forfeit_inherited (m_fds m))
            && clone3_refused_eff_b uargs eff) eqn:Hc; cbv beta iota in H.
  - left. injection H as <- <-. split; [reflexivity|]. split; [reflexivity|].
    apply andb_true_iff in Hc as [_ Hr].
    destruct eff as [ret ws zs us cs cis]. cbn [eff_ret].
    destruct ws, zs, us, cs; try discriminate Hr.
    destruct cis as [|[a n] [|? ?]]; try discriminate Hr.
    cbn [clone3_refused_eff_b] in Hr. apply andb_true_iff in Hr as [_ Hr]. exact Hr.
  - right. exact H.
Qed.
