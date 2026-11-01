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

(** clone / clone3: no writes, no model update.  The two arms of
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
(** The success arm returns the model WITH the child recorded, mirroring
    [Kernel.Fork.clone_resolve]'s [with_children] on the same branch.  The
    errno arm returns [m] unchanged: it created nothing. *)
Definition check_clone_answer (ret : word) (m : Model) : check_result :=
  if errno_ret_in clone_errnos ret then CheckOk m []
  else if clone_pid_ok_b m ret then CheckOk (with_children m) []
  else CheckReject.

Definition check_clone_resolve (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (clone_no_shared_file_b (m_fds m)) then CheckUnmodeled
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
  if negb (clone_no_shared_file_b (m_fds m)) then CheckUnmodeled
  else match eff with
  | mkEffectU ret [] [] [] [] ((a, n) :: nil) =>
      if bv_eqb a uargs && Nat.eqb n CLONE_ARGS_SIZE_nat
      then check_clone_answer ret m
      else CheckReject
  | _ => CheckReject
  end.

Definition check_clone (flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if clone_fork_flags_b flags then check_clone_resolve eff m
  else CheckUnmodeled.

(** A [uargs] range [access_ok] refuses is -EFAULT with an EMPTY ledger,
    asked through [State.copy_bytes_map] before the walk; one it admits
    that the memory does not wholly back declines (see
    [Fork.clone3_spec]). *)
Definition check_clone3 (i : SyscallInput) (uargs size : word)
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

Lemma check_clone_resolve_sound_ok : forall eff m m' evs i,
  check_clone_resolve eff m = CheckOk m' evs -> clone_resolve i m (Ok eff m' evs).
Proof.
  intros [ret ws zs us cs copyins] m m' evs i H.
  unfold check_clone_resolve in H. unfold clone_resolve.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg;
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
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg;
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
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg; hall Hg; inv_ok.
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
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg; hall Hg; inv_ok;
    reflexivity.
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
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg;
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
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg; cbv iota in H.
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
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg;
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
  destruct (negb (clone_no_shared_file_b (m_fds m))) eqn:Hg;
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

Lemma check_clone_sound_ok : forall flags eff m m' evs i,
  check_clone flags eff m = CheckOk m' evs -> clone_spec flags i m (Ok eff m' evs).
Proof.
  intros flags eff m m' evs i H.
  unfold check_clone in H. unfold clone_spec.
  destruct (clone_fork_flags_b flags); [|discriminate].
  now apply check_clone_resolve_sound_ok.
Qed.

Lemma check_clone_sound_unmodeled : forall flags eff m i,
  check_clone flags eff m = CheckUnmodeled -> clone_spec flags i m Unmodeled.
Proof.
  intros flags eff m i H.
  unfold check_clone in H. unfold clone_spec.
  destruct (clone_fork_flags_b flags);
    [now apply check_clone_resolve_sound_unmodeled with (eff := eff)
    |apply unmodeled_intro].
Qed.

Lemma check_clone_complete_ok : forall flags eff m m' evs i,
  clone_spec flags i m (Ok eff m' evs) -> check_clone flags eff m = CheckOk m' evs.
Proof.
  intros flags eff m m' evs i H.
  unfold clone_spec in H. unfold check_clone.
  destruct (clone_fork_flags_b flags);
    [now apply check_clone_resolve_complete_ok with (i := i)
    |unfold unmodeled in H; discriminate].
Qed.

Lemma check_clone_complete_unmodeled : forall flags m i eff,
  clone_spec flags i m Unmodeled -> check_clone flags eff m = CheckUnmodeled.
Proof.
  intros flags m i eff H.
  unfold clone_spec in H. unfold check_clone.
  destruct (clone_fork_flags_b flags);
    [now apply check_clone_resolve_complete_unmodeled with (i := i)|reflexivity].
Qed.

Lemma check_clone3_sound_ok : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs ->
  clone3_spec uargs size i m (Ok eff m' evs).
Proof.
  intros i uargs size eff m m' evs H.
  unfold check_clone3 in H. unfold clone3_spec.
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

Lemma check_clone3_sound_unmodeled : forall i uargs size eff m,
  check_clone3 i uargs size eff m = CheckUnmodeled ->
  clone3_spec uargs size i m Unmodeled.
Proof.
  intros i uargs size eff m H.
  unfold check_clone3 in H. unfold clone3_spec.
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

Lemma check_clone3_complete_ok : forall i uargs size eff m m' evs,
  clone3_spec uargs size i m (Ok eff m' evs) ->
  check_clone3 i uargs size eff m = CheckOk m' evs.
Proof.
  intros i uargs size eff m m' evs H.
  unfold clone3_spec in H. unfold check_clone3.
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

Lemma check_clone3_complete_unmodeled : forall i uargs size m eff,
  clone3_spec uargs size i m Unmodeled ->
  check_clone3 i uargs size eff m = CheckUnmodeled.
Proof.
  intros i uargs size m eff H.
  unfold clone3_spec in H. unfold check_clone3.
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
