(** * LinuxProcessSem.Checks.Sys.Fs.File — the dup (23), dup3 (24) and close_range (436) checkers, and their proofs

    Mirrors [Sys/Fs/File.v], which answers to Linux [fs/file.c]: this
    file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module.

    It imports the [Fs.Open] mirror rather than [Prelude] alone because
    [Open.errno_ret_in_alloc_fd] — an allocated fd never matches an
    injectable errno — is proved there, beside the [openat] acceptor
    that first needed it. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Fs.Open.

(** The acceptor for [File.dup_spec]'s allocating branch: the same
    shape as [Open.check_open_result], but over [dup_errnos] rather than
    [openat_errnos] — dup takes a second reference to an existing
    [struct file], so it can exhaust the fd table but never the
    system-wide open-file limit.

    Kept separate from that acceptor rather than sharing a common one
    taking the errno set: sharing costs a second [unfold] in every proof
    that consumes either — here, in [Common/FileSim.v]'s two lemmas
    about it, in [Common/FileMixSim.v], and in [Examples/cp_ns] — which
    is churn in a shared proof library and an example for a change about
    dup.  The two are one definition apart if that trade ever stops
    being worth it. *)
Definition check_dup_result (eff : SyscallEffect) (m : Model)
    (mk : word -> Model) : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in dup_errnos ret then CheckOk m []
      else
        match fd_lookup (m_fds m) ret with
        | Some _ => CheckReject
        | None => if bv_eqb ret (alloc_fd (m_fds m)) then CheckOk (mk ret) []
                  else CheckReject
        end
  | _ => CheckReject
  end.

(** [dup]/[dup3]: the [FdFile]/[FdFileW] arms decline, because the
    model cannot represent two fds sharing one file offset, and dup3
    declines a free [newfd] at or above [Uapi.NR_OPEN_DEFAULT], where
    the answer turns on the descriptor table's size.  Kernel citations
    live on [File.dup_spec] and [File.dup3_spec]. *)
Definition check_dup (oldfd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) oldfd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some e =>
      if negb (dup_modeled_entry e) then CheckUnmodeled
      else check_dup_result eff m
             (fun fd => with_fds (fd_insert (m_fds m) fd e) m)
  end.

Definition check_dup3 (oldfd newfd flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (dup3_flags_ok flags) then check_ret_only eff (errno_ret EINVAL) m []
  else if bv_eqb oldfd newfd then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (dup3_newfd_under_limit newfd m)
       then check_ret_only eff (errno_ret EBADF) m []
  else
    match fd_lookup (m_fds m) oldfd with
    | None => check_ret_only eff (errno_ret EBADF) m []
    | Some e =>
        if negb (dup_modeled_entry e) then CheckUnmodeled
        else
          match fd_lookup (m_fds m) newfd with
          | None =>
              if Z.ltb (bv_unsigned newfd) NR_OPEN_DEFAULT
              then check_ret_only eff newfd
                     (with_fds (fd_insert (m_fds m) newfd e) m) []
              else CheckUnmodeled
          | Some _ =>
              check_ret_only eff newfd
                (with_fds (fd_insert (m_fds m) newfd e) m) []
          end
    end.

Lemma check_dup_sound_ok : forall oldfd eff m m' evs i,
  check_dup oldfd eff m = CheckOk m' evs ->
  dup_spec oldfd i m (Ok eff m' evs).
Proof.
  intros oldfd eff m m' evs i H.
  unfold check_dup in H. unfold dup_spec.
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd.
  - destruct (negb (dup_modeled_entry e)) eqn:Hk; [discriminate|].
    unfold check_dup_result in H.
    destruct eff as [ret ws zs us cs copyins]; destruct ws as [|w ws'];
      [destruct zs as [|z zs']|]; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
    destruct (errno_ret_in dup_errnos ret) eqn:He.
    + inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (er & HIn & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hk.
      apply alt_l. eapply bind_ok0.
      { apply (choose_ok _ er). exact HIn. }
      apply pure_ok.
    + destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
      destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
      inversion H; clear H; subst. apply bv_eqb_eq in Heq.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd. srw Hk.
      apply alt_r. eapply bind_ok0.
      { apply (choose_ok _ ret). split; assumption. }
      cbv beta. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hfd.
    apply pure_ok.
Qed.

Lemma check_dup_sound_unmodeled : forall oldfd eff m i,
  check_dup oldfd eff m = CheckUnmodeled -> dup_spec oldfd i m Unmodeled.
Proof.
  intros oldfd eff m i H. unfold check_dup in H. unfold dup_spec.
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd;
    [|now apply check_ret_only_no_unmodeled in H].
  destruct (negb (dup_modeled_entry e)) eqn:Hk.
  - eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. srw Hk. apply unmodeled_intro.
  - unfold check_dup_result in H.
    destruct eff as [ret ws zs us cs copyins]; destruct ws as [|w ws'];
      [destruct zs as [|z zs']|]; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
    destruct (errno_ret_in dup_errnos ret); [discriminate|].
    destruct (fd_lookup (m_fds m) ret); [discriminate|].
    destruct (bv_eqb ret (alloc_fd (m_fds m))); discriminate.
Qed.

Lemma check_dup_complete_ok : forall oldfd eff m m' evs i,
  dup_spec oldfd i m (Ok eff m' evs) -> check_dup oldfd eff m = CheckOk m' evs.
Proof.
  intros oldfd eff m m' evs i H.
  unfold dup_spec in H. unfold check_dup. sys_unfold. cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    [|cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity].
  destruct (negb (dup_modeled_entry e)) eqn:Hk; hall Hk; inv_ok.
  - (* the injected errno *)
    unfold check_dup_result.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?er)] =>
        rewrite (errno_ret_in_intro es er) by assumption
    end.
    reflexivity.
  - (* success: the lowest free fd *)
    unfold check_dup_result.
    rewrite errno_ret_in_alloc_fd by reflexivity.
    match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
    rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma check_dup_complete_unmodeled : forall oldfd m i eff,
  dup_spec oldfd i m Unmodeled -> check_dup oldfd eff m = CheckUnmodeled.
Proof.
  intros oldfd m i eff H.
  unfold dup_spec in H. unfold check_dup. sys_unfold. cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd; hall Hfd; inv_ok.
  destruct (negb (dup_modeled_entry e)) eqn:Hk; hall Hk; inv_ok.
  reflexivity.
Qed.

Lemma check_dup3_sound_ok : forall oldfd newfd flags eff m m' evs i,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs ->
  dup3_spec oldfd newfd flags i m (Ok eff m' evs).
Proof.
  intros oldfd newfd flags eff m m' evs i H.
  unfold check_dup3 in H. unfold dup3_spec.
  destruct (negb (dup3_flags_ok flags)) eqn:Hf.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    apply pure_ok. }
  destruct (bv_eqb oldfd newfd) eqn:Hne.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    apply pure_ok. }
  destruct (negb (dup3_newfd_under_limit newfd m)) eqn:Hl.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hl.
    apply pure_ok. }
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd.
  - destruct (negb (dup_modeled_entry e)) eqn:Hk; [discriminate|].
    destruct (fd_lookup (m_fds m) newfd) as [e2|] eqn:Hnf.
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hl. srw Hfd. srw Hk. srw Hnf.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + destruct (Z.ltb (bv_unsigned newfd) NR_OPEN_DEFAULT) eqn:Hb;
        [|discriminate].
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
      srw Hl. srw Hfd. srw Hk. srw Hnf.
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hl. srw Hfd. apply pure_ok.
Qed.

Lemma check_dup3_sound_unmodeled : forall oldfd newfd flags eff m i,
  check_dup3 oldfd newfd flags eff m = CheckUnmodeled ->
  dup3_spec oldfd newfd flags i m Unmodeled.
Proof.
  intros oldfd newfd flags eff m i H.
  unfold check_dup3 in H. unfold dup3_spec.
  destruct (negb (dup3_flags_ok flags)) eqn:Hf;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (bv_eqb oldfd newfd) eqn:Hne;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (negb (dup3_newfd_under_limit newfd m)) eqn:Hl;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd;
    [|now apply check_ret_only_no_unmodeled in H].
  destruct (negb (dup_modeled_entry e)) eqn:Hk.
  - eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hl. srw Hfd. srw Hk. apply unmodeled_intro.
  - destruct (fd_lookup (m_fds m) newfd) as [e2|] eqn:Hnf;
      [now apply check_ret_only_no_unmodeled in H|].
    destruct (Z.ltb (bv_unsigned newfd) NR_OPEN_DEFAULT) eqn:Hb;
      [now apply check_ret_only_no_unmodeled in H|].
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hl. srw Hfd. srw Hk. srw Hnf. apply unmodeled_intro.
Qed.

Lemma check_dup3_complete_ok : forall oldfd newfd flags eff m m' evs i,
  dup3_spec oldfd newfd flags i m (Ok eff m' evs) ->
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs.
Proof.
  intros oldfd newfd flags eff m m' evs i H.
  unfold dup3_spec in H. unfold check_dup3. sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (dup3_flags_ok flags)) eqn:Hf; hall Hf; inv_ok;
    [cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity|].
  destruct (bv_eqb oldfd newfd) eqn:Hne; hall Hne; inv_ok;
    [cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity|].
  destruct (negb (dup3_newfd_under_limit newfd m)) eqn:Hl; hall Hl; inv_ok;
    [cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity|].
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    [|cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity].
  destruct (negb (dup_modeled_entry e)) eqn:Hk; hall Hk; inv_ok.
  destruct (fd_lookup (m_fds m) newfd) as [e2|] eqn:Hnf; hall Hnf; inv_ok;
    [cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity|].
  destruct (Z.ltb (bv_unsigned newfd) NR_OPEN_DEFAULT) eqn:Hb; hall Hb; inv_ok.
  cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_dup3_complete_unmodeled : forall oldfd newfd flags m i eff,
  dup3_spec oldfd newfd flags i m Unmodeled ->
  check_dup3 oldfd newfd flags eff m = CheckUnmodeled.
Proof.
  intros oldfd newfd flags m i eff H.
  unfold dup3_spec in H. unfold check_dup3. sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (dup3_flags_ok flags)) eqn:Hf; hall Hf; inv_ok.
  destruct (bv_eqb oldfd newfd) eqn:Hne; hall Hne; inv_ok.
  destruct (negb (dup3_newfd_under_limit newfd m)) eqn:Hl; hall Hl; inv_ok.
  destruct (fd_lookup (m_fds m) oldfd) as [e|] eqn:Hfd; hall Hfd; inv_ok.
  destruct (negb (dup_modeled_entry e)) eqn:Hk; hall Hk; inv_ok;
    [reflexivity|].
  destruct (fd_lookup (m_fds m) newfd) as [e2|] eqn:Hnf; hall Hnf; inv_ok.
  destruct (Z.ltb (bv_unsigned newfd) NR_OPEN_DEFAULT) eqn:Hb; hall Hb; inv_ok.
  reflexivity.
Qed.

(* ------------------------------------------------------------ close_range *)

(** [close_range] (436): the unknown-flag -EINVAL, then the [fd > max_fd]
    -EINVAL, in the kernel's order; then a decline for either known
    flag; then 0 with every descriptor of the range removed
    ([File.close_range_fds]).  Deterministic on every branch it answers,
    so each is a bare return compared against its one answer.  Kernel
    citations live on [File.close_range_spec]. *)
Definition check_close_range (fd max_fd flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags)
                          (Z.lor CLOSE_RANGE_UNSHARE CLOSE_RANGE_CLOEXEC)) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if (bv_unsigned max_fd <? bv_unsigned fd)%Z
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (Z.eqb (bv_unsigned flags) 0) then CheckUnmodeled
  else check_ret_only eff (Z_to_bv 64 0)
         (with_fds (close_range_fds fd max_fd (m_fds m)) m) [].

Lemma check_close_range_sound_ok : forall fd max_fd flags eff m m' evs i,
  check_close_range fd max_fd flags eff m = CheckOk m' evs ->
  close_range_spec fd max_fd flags i m (Ok eff m' evs).
Proof.
  intros fd max_fd flags eff m m' evs i H.
  unfold check_close_range in H. unfold close_range_spec.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags)
                                 (Z.lor CLOSE_RANGE_UNSHARE CLOSE_RANGE_CLOEXEC)) 0)).
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct ((bv_unsigned max_fd <? bv_unsigned fd)%Z).
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (Z.eqb (bv_unsigned flags) 0)); [discriminate|].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

(** Only a known flag declines, on both sides. *)
Lemma check_close_range_sound_unmodeled : forall fd max_fd flags eff m i,
  check_close_range fd max_fd flags eff m = CheckUnmodeled ->
  close_range_spec fd max_fd flags i m Unmodeled.
Proof.
  intros fd max_fd flags eff m i H.
  unfold check_close_range in H. unfold close_range_spec.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags)
                                 (Z.lor CLOSE_RANGE_UNSHARE CLOSE_RANGE_CLOEXEC)) 0)).
  { now apply check_ret_only_no_unmodeled in H. }
  destruct ((bv_unsigned max_fd <? bv_unsigned fd)%Z).
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (Z.eqb (bv_unsigned flags) 0)); [apply unmodeled_intro|].
  now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_close_range_complete_ok : forall fd max_fd flags eff m m' evs i,
  close_range_spec fd max_fd flags i m (Ok eff m' evs) ->
  check_close_range fd max_fd flags eff m = CheckOk m' evs.
Proof.
  intros fd max_fd flags eff m m' evs i H.
  unfold close_range_spec in H. unfold check_close_range.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags)
                                 (Z.lor CLOSE_RANGE_UNSHARE CLOSE_RANGE_CLOEXEC)) 0)).
  { unfold err_ret, ret_only, pure in H. inversion H; subst.
    cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct ((bv_unsigned max_fd <? bv_unsigned fd)%Z).
  { unfold err_ret, ret_only, pure in H. inversion H; subst.
    cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (negb (Z.eqb (bv_unsigned flags) 0)); [now inversion H|].
  apply get_model_bind_ok_inv in H. cbv beta in H. sys_unfold. inv_ok.
  cbn; try rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_close_range_complete_unmodeled : forall fd max_fd flags m i eff,
  close_range_spec fd max_fd flags i m Unmodeled ->
  check_close_range fd max_fd flags eff m = CheckUnmodeled.
Proof.
  intros fd max_fd flags m i eff H.
  unfold close_range_spec in H. unfold check_close_range.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags)
                                 (Z.lor CLOSE_RANGE_UNSHARE CLOSE_RANGE_CLOEXEC)) 0)).
  { unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct ((bv_unsigned max_fd <? bv_unsigned fd)%Z).
  { unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (negb (Z.eqb (bv_unsigned flags) 0)); [reflexivity|].
  exfalso. apply get_model_bind_unmodeled_inv in H. cbv beta in H.
  sys_unfold. inv_ok.
Qed.
