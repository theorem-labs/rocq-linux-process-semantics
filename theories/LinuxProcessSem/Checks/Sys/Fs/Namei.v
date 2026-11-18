(** * LinuxProcessSem.Checks.Sys.Fs.Namei — the mkdirat (34) and unlinkat (35) checkers, and their proofs

    Mirrors [Sys/Fs/Namei.v], which answers to Linux [fs/namei.c]: this
    file holds the checkers for the syscalls defined there, and no
    others.

    Split out of [Checks/ExecutableSpecs.v], which keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module.

    Ported from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

(** The acceptor for an arm that can SUCCEED: either an injectable
    errno with no state change, or the removal itself, returning 0 and
    leaving the file system [fs'].  Both take a bare return and FIVE
    EMPTY ledgers — the kernel's unlinkat and rmdir write, zero, unmap
    and copy nothing — so only a forged ledger reaches the other half of
    the claim. *)
Definition check_unlink_result (fs' : Fs.Fs) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in unlinkat_errnos ret then CheckOk m []
      else if bv_eqb ret (Z_to_bv 64 0)
           then CheckOk (with_fs fs' m) []
           else CheckReject
  | _ => CheckReject
  end.

(** The same acceptor for [mkdirat], which adds instead of removing and
    draws from its own errno set. *)
Definition check_mkdir_result (fs' : Fs.Fs) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in mkdirat_errnos ret then CheckOk m []
      else if bv_eqb ret (Z_to_bv 64 0)
           then CheckOk (with_fs fs' m) []
           else CheckReject
  | _ => CheckReject
  end.

(** Accepts a type answer [e] or a refusal from [l], chosen for the
    kernel route: [unlink_before_type_errnos] for [may_delete],
    [unlink_before_slashes_errnos] for [slashes:] and for the absent
    name's -ENOENT, [unlinkat_errnos] beside rmdir's -ENOTEMPTY.  Each
    is a bare return with five empty ledgers and no state change. *)
Definition check_unlink_type_result (l : list Z) (e : Z) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in l ret then CheckOk m []
      else if bv_eqb ret (errno_ret e) then CheckOk m []
      else CheckReject
  | _ => CheckReject
  end.

(** Mirrors [Fs.Namei.unlinkat_file_spec] row for row. *)
Local Definition check_unlinkat_file (r : Fs.Resolved) (lk : Fs.LastKind)
    (ts : bool) (eff : SyscallEffect) (m : Model) : check_result :=
  match r with
  | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
  | Fs.RParent _ _ => CheckUnmodeled
  | Fs.ROutside => CheckUnmodeled
  | Fs.RMissing _ _ =>
      match unlink_nonnorm_errno lk with
      | Some e => check_ret_only eff (errno_ret e) m []
      | None => check_unlink_type_result unlink_before_slashes_errnos ENOENT eff m
      end
  | Fs.RFound k e =>
      match unlink_nonnorm_errno lk with
      | Some er => check_ret_only eff (errno_ret er) m []
      | None =>
          match e with
          | EDir =>
              if ts
              then check_unlink_type_result unlink_before_slashes_errnos EISDIR eff m
              else check_unlink_type_result unlink_before_type_errnos EISDIR eff m
          | EDev _ => CheckUnmodeled
          | EFile ino =>
              if ts
              then check_unlink_type_result unlink_before_slashes_errnos ENOTDIR eff m
              else check_unlink_result
                     (Fs.fs_unlink_file (m_fs m) k ino (ino_held (m_fds m) ino)) eff m
          | ELink _ =>
              if ts
              then check_unlink_type_result unlink_before_slashes_errnos ENOTDIR eff m
              else check_unlink_result (fs_remove (m_fs m) k) eff m
          end
      end
  end.

(** Mirrors [Fs.Namei.rmdir_spec] row for row. *)
Local Definition check_rmdir (r : Fs.Resolved) (lk : Fs.LastKind)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match r with
  | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
  | Fs.RParent _ _ => CheckUnmodeled
  | Fs.ROutside => CheckUnmodeled
  | Fs.RMissing _ _ =>
      match rmdir_nonnorm_errno lk with
      | Some e => check_ret_only eff (errno_ret e) m []
      | None => check_unlink_type_result unlink_before_slashes_errnos ENOENT eff m
      end
  | Fs.RFound k e =>
      match rmdir_nonnorm_errno lk with
      | Some er => check_ret_only eff (errno_ret er) m []
      | None =>
          match e with
          | EFile _ | EDev _ | ELink _ =>
              check_unlink_type_result unlink_before_type_errnos ENOTDIR eff m
          | EDir =>
              if path_eqb k (m_cwd m) then CheckUnmodeled
              else if key_strictly_under k (m_cwd m) then CheckUnmodeled
              else if fd_names_dir (m_fds m) k then CheckUnmodeled
              else if negb (fs_dir_empty (m_fs m) k)
              then check_unlink_type_result unlinkat_errnos ENOTEMPTY eff m
              else check_unlink_result (Fs.fs_rmdir (m_fs m) k) eff m
          end
      end
  end.

Local Definition check_unlinkat_body (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | CstrOk p =>
      if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
      else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
      else
        match Fs.resolve_parent (m_fs m) (m_cwd m) p with
        | (r, lk, ts) =>
            if unlink_rmdir flags then check_rmdir r lk eff m
            else check_unlinkat_file r lk ts eff m
        end
  end.

Local Definition check_mkdirat_body (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | CstrOk p =>
      if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
      else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
      else
        match Fs.resolve_parent (m_fs m) (m_cwd m) p with
        | (r, lk, _) =>
            match r with
            | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
            | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
            | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
            | Fs.RParent _ _ => CheckUnmodeled
            | Fs.ROutside => CheckUnmodeled
            | Fs.RFound _ _ =>
                match mkdir_nonnorm_errno lk with
                | Some e => check_ret_only eff (errno_ret e) m []
                | None => check_ret_only eff (errno_ret EEXIST) m []
                end
            | Fs.RMissing par nm =>
                match mkdir_nonnorm_errno lk with
                | Some e => check_ret_only eff (errno_ret e) m []
                | None =>
                    if Nat.ltb Fs.dir_count_max
                         (S (Fs.dl_counting (Fs.fs_dir_links (m_fs m) par)))
                    then CheckUnmodeled
                    else check_mkdir_result (Fs.fs_mkdir (m_fs m) (Fs.child_key par nm)) eff m
                end
            end
        end
  end.

(** The pathname copy-in, as [Fs.Open.check_openat] checks it: decide the
    body against the effect with the ledger cleared, then require the
    claimed ledger to be exactly that one range.  The flag arm is outside
    the wrapper because the kernel decides it before [getname()], so an
    honest -EINVAL there carries no copy-in at all.  Inside the wrapper,
    the walk's own refusals ([check_walk_refusals]); around it,
    [getname_flags]' own ([check_getname_refusals]), which fail before
    the copy is done. *)
Definition check_unlinkat (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (modeled_unlink_flags flags)
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let reads := [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] in
    check_getname_refusals i pathp eff m
      (check_copyins_after reads eff
         (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
            (check_unlinkat_body i dirfd pathp flags (clear_copyins eff) m))).

(** mkdirat has no flag word at all, so the whole call sits inside the
    wrappers. *)
Definition check_mkdirat (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let reads := [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] in
  check_getname_refusals i pathp eff m
    (check_copyins_after reads eff
       (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
          (check_mkdirat_body i dirfd pathp (clear_copyins eff) m))).

(** Read the input and the model, the two steps [unlinkat_spec] takes
    before the flag test. *)
Ltac ul_open :=
  eapply bind_ok0; [apply input_ok|]; cbv beta;
  eapply bind_ok0; [apply get_model_ok|]; cbv beta iota.

(** The same two steps when the outcome being justified is [Unmodeled]. *)
Ltac ul_open_u :=
  eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
  eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota.

(** 0 is not an injectable errno on either set, so the state change and
    the failure alternative never both accept the same return. *)
Lemma errno_ret_in_unlinkat_zero :
  errno_ret_in unlinkat_errnos (Z_to_bv 64 0) = false.
Proof.
  apply errno_ret_in_fd; [reflexivity|].
  rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia). lia.
Qed.

Lemma errno_ret_in_mkdirat_zero :
  errno_ret_in mkdirat_errnos (Z_to_bv 64 0) = false.
Proof.
  apply errno_ret_in_fd; [reflexivity|].
  rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia). lia.
Qed.

Local Lemma check_unlink_result_sound_ok : forall i k eff m m' evs,
  check_unlink_result k eff m = CheckOk m' evs ->
  alt (e <- errno_from unlinkat_errnos ;; err_ret e)
      (set_fs k ;; ret_only (Z_to_bv 64 0))
      i m (Ok eff m' evs).
Proof.
  intros i k eff m m' evs H. unfold check_unlink_result in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws as [|w ws'];
    [destruct zs as [|z zs']|]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  destruct (errno_ret_in unlinkat_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    unfold err_ret, ret_only. apply pure_ok.
  - destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq; subst ret.
    apply alt_r. unfold set_fs, ret_only.
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Local Lemma check_unlink_result_no_unmodeled : forall k eff m,
  check_unlink_result k eff m <> CheckUnmodeled.
Proof.
  intros k [ret ws zs us cs cis] m. unfold check_unlink_result.
  destruct ws; [destruct zs|]; destruct us; destruct cs; destruct cis;
    try discriminate.
  destruct (errno_ret_in unlinkat_errnos ret); [discriminate|].
  destruct (bv_eqb ret (Z_to_bv 64 0)); discriminate.
Qed.

Local Lemma check_unlink_result_no_copyin : forall k eff m m' evs,
  check_unlink_result k eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros k [ret ws zs us cs cis] m m' evs H. unfold check_unlink_result in H.
  destruct ws; [destruct zs|]; destruct us; destruct cs; destruct cis;
    try discriminate; reflexivity.
Qed.

Local Lemma check_unlink_result_complete_ok : forall i k eff m m' evs,
  alt (e <- errno_from unlinkat_errnos ;; err_ret e)
      (set_fs k ;; ret_only (Z_to_bv 64 0))
      i m (Ok eff m' evs) ->
  check_unlink_result k eff m = CheckOk m' evs.
Proof.
  intros i k eff m m' evs H. unfold check_unlink_result. sys_unfold.
  destruct H as [H | H]; inv_ok.
  - match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - rewrite errno_ret_in_unlinkat_zero, bv_eqb_refl. reflexivity.
Qed.

Local Lemma check_unlink_result_complete_unmodeled : forall i k m,
  ~ alt (e <- errno_from unlinkat_errnos ;; err_ret e)
        (set_fs k ;; ret_only (Z_to_bv 64 0))
        i m Unmodeled.
Proof. intros i k m H. sys_unfold. destruct H as [H | H]; inv_ok. Qed.

Local Lemma check_mkdir_result_sound_ok : forall i k eff m m' evs,
  check_mkdir_result k eff m = CheckOk m' evs ->
  alt (e <- errno_from mkdirat_errnos ;; err_ret e)
      (set_fs k ;; ret_only (Z_to_bv 64 0))
      i m (Ok eff m' evs).
Proof.
  intros i k eff m m' evs H. unfold check_mkdir_result in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws as [|w ws'];
    [destruct zs as [|z zs']|]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  destruct (errno_ret_in mkdirat_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    unfold err_ret, ret_only. apply pure_ok.
  - destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq; subst ret.
    apply alt_r. unfold set_fs, ret_only.
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Local Lemma check_mkdir_result_no_unmodeled : forall k eff m,
  check_mkdir_result k eff m <> CheckUnmodeled.
Proof.
  intros k [ret ws zs us cs cis] m. unfold check_mkdir_result.
  destruct ws; [destruct zs|]; destruct us; destruct cs; destruct cis;
    try discriminate.
  destruct (errno_ret_in mkdirat_errnos ret); [discriminate|].
  destruct (bv_eqb ret (Z_to_bv 64 0)); discriminate.
Qed.

Local Lemma check_mkdir_result_no_copyin : forall k eff m m' evs,
  check_mkdir_result k eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros k [ret ws zs us cs cis] m m' evs H. unfold check_mkdir_result in H.
  destruct ws; [destruct zs|]; destruct us; destruct cs; destruct cis;
    try discriminate; reflexivity.
Qed.

Local Lemma check_mkdir_result_complete_ok : forall i k eff m m' evs,
  alt (e <- errno_from mkdirat_errnos ;; err_ret e)
      (set_fs k ;; ret_only (Z_to_bv 64 0))
      i m (Ok eff m' evs) ->
  check_mkdir_result k eff m = CheckOk m' evs.
Proof.
  intros i k eff m m' evs H. unfold check_mkdir_result. sys_unfold.
  destruct H as [H | H]; inv_ok.
  - match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - rewrite errno_ret_in_mkdirat_zero, bv_eqb_refl. reflexivity.
Qed.

Local Lemma check_mkdir_result_complete_unmodeled : forall i k m,
  ~ alt (e <- errno_from mkdirat_errnos ;; err_ret e)
        (set_fs k ;; ret_only (Z_to_bv 64 0))
        i m Unmodeled.
Proof. intros i k m H. sys_unfold. destruct H as [H | H]; inv_ok. Qed.

(** Closing a leaf that is a bare errno return: the same three moves on
    every one of them. *)
Local Ltac nam_ret_ok :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckOk _ _ |- _ =>
      apply check_ret_only_ok_iff in Hx; destruct Hx as (-> & -> & ->);
      unfold err_ret, ret_only; apply pure_ok
  end.
Local Ltac nam_ret_nu :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckUnmodeled |- _ =>
      now apply check_ret_only_no_unmodeled in Hx
  end.
Local Ltac nam_ret_co :=
  unfold err_ret, ret_only, pure in *; inv_ok;
  apply check_ret_only_ok_iff; now repeat split.
Local Ltac nam_ret_cnil :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckOk _ _ |- _ =>
      apply check_ret_only_ok_iff in Hx; destruct Hx as (-> & _ & _);
      reflexivity
  end.

(** [check_unlink_type_result] against the [alt] each type answer
    takes, in both directions, and the two facts the wrappers need: it
    never declines, and what it accepts claims no copy-in. *)
Local Lemma check_unlink_type_result_sound : forall i l e eff m m' evs,
  check_unlink_type_result l e eff m = CheckOk m' evs ->
  alt (bind (errno_from l) (fun x => err_ret x))
      (err_ret e) i m (Ok eff m' evs).
Proof.
  intros i l e eff m m' evs H.
  unfold check_unlink_type_result in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws as [|w ws'];
    [destruct zs as [|z zs']|]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  destruct (errno_ret_in l ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (x & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ x). exact HIn. }
    apply pure_ok.
  - destruct (bv_eqb ret (errno_ret e)) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq; subst ret.
    apply alt_r. unfold err_ret, ret_only. apply pure_ok.
Qed.

Local Lemma check_unlink_type_result_complete : forall i l e eff m m' evs,
  alt (bind (errno_from l) (fun x => err_ret x))
      (err_ret e) i m (Ok eff m' evs) ->
  check_unlink_type_result l e eff m = CheckOk m' evs.
Proof.
  intros i l e eff m m' evs H. sys_unfold. cbv beta iota zeta in H.
  (* one leaf per side of the [alt]: a listed refusal, whose membership
     is a hypothesis, or the type errno itself *)
  inv_ok; unfold check_unlink_type_result;
    first
    [ match goal with
      | Hin : In _ l |- _ =>
          rewrite (errno_ret_in_intro _ _ Hin)
      end; reflexivity
    | destruct (errno_ret_in l (errno_ret e));
        [|rewrite bv_eqb_refl]; reflexivity ].
Qed.

Local Lemma check_unlink_type_result_complete_unmodeled : forall i l e m,
  ~ alt (bind (errno_from l) (fun x => err_ret x)) (err_ret e) i m Unmodeled.
Proof. intros i l e m H. sys_unfold. destruct H as [H | H]; inv_ok. Qed.

Local Lemma check_unlink_type_result_no_unmodeled : forall l e eff m,
  check_unlink_type_result l e eff m <> CheckUnmodeled.
Proof.
  intros l e eff m H.
  unfold check_unlink_type_result in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws; [destruct zs|];
    destruct us; destruct cs; destruct cis; try discriminate.
  destruct (errno_ret_in l ret); [discriminate|].
  destruct (bv_eqb ret (errno_ret e)); discriminate.
Qed.

Local Lemma check_unlink_type_result_ok_copyins_nil : forall l e eff m m' evs,
  check_unlink_type_result l e eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros l e eff m m' evs H.
  unfold check_unlink_type_result in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws; [destruct zs|];
    destruct us; destruct cs; destruct cis; try discriminate; reflexivity.
Qed.

Local Lemma check_unlinkat_file_sound_ok : forall i r lk ts eff m m' evs,
  check_unlinkat_file r lk ts eff m = CheckOk m' evs ->
  unlinkat_file_spec r lk ts m i m (Ok eff m' evs).
Proof.
  intros i r lk ts eff m m' evs H.
  unfold check_unlinkat_file in H. unfold unlinkat_file_spec.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try nam_ret_ok; try discriminate.
  - destruct lk; cbn [unlink_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try nam_ret_ok.
    destruct e as [data| |dk|lb]; cbv iota in H |- *; [| |discriminate|].
    + destruct ts; cbv iota in H |- *;
        [now apply check_unlink_type_result_sound|].
      unfold unlink_file_spec. now apply check_unlink_result_sound_ok.
    + destruct ts; now apply check_unlink_type_result_sound.
    + destruct ts; cbv iota in H |- *;
        [now apply check_unlink_type_result_sound|].
      unfold unlink_remove_spec. now apply check_unlink_result_sound_ok.
  - destruct lk; cbn [unlink_nonnorm_errno] in H |- *;
      cbv iota in H |- *;
      first [nam_ret_ok | now apply check_unlink_type_result_sound].
Qed.

Local Lemma check_unlinkat_file_sound_unmodeled : forall i r lk ts eff m,
  check_unlinkat_file r lk ts eff m = CheckUnmodeled ->
  unlinkat_file_spec r lk ts m i m Unmodeled.
Proof.
  intros i r lk ts eff m H.
  unfold check_unlinkat_file in H. unfold unlinkat_file_spec.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try nam_ret_nu; try apply unmodeled_intro.
  - destruct lk; cbn [unlink_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try nam_ret_nu.
    destruct e as [data| |dk|lb]; cbv iota in H |- *; [| |apply unmodeled_intro|].
    + destruct ts; cbv iota in H |- *;
        [exfalso; eapply check_unlink_type_result_no_unmodeled; exact H|].
      exfalso. eapply check_unlink_result_no_unmodeled. exact H.
    + exfalso. destruct ts;
        eapply check_unlink_type_result_no_unmodeled; exact H.
    + destruct ts; cbv iota in H |- *;
        [exfalso; eapply check_unlink_type_result_no_unmodeled; exact H|].
      exfalso. eapply check_unlink_result_no_unmodeled. exact H.
  - destruct lk; cbn [unlink_nonnorm_errno] in H |- *;
      cbv iota in H |- *;
      first [nam_ret_nu
            | exfalso; eapply check_unlink_type_result_no_unmodeled; exact H].
Qed.

Local Lemma check_unlinkat_file_no_copyin : forall r lk ts eff m m' evs,
  check_unlinkat_file r lk ts eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros r lk ts eff m m' evs H. unfold check_unlinkat_file in H.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try nam_ret_cnil; try discriminate.
  - destruct lk; cbn [unlink_nonnorm_errno] in H; cbv iota in H;
      try nam_ret_cnil.
    destruct e as [data| |dk|lb]; cbv iota in H; [| |discriminate|].
    + destruct ts; cbv iota in H;
        [eapply check_unlink_type_result_ok_copyins_nil; exact H
        |eapply check_unlink_result_no_copyin; exact H].
    + destruct ts; eapply check_unlink_type_result_ok_copyins_nil; exact H.
    + destruct ts; cbv iota in H;
        [eapply check_unlink_type_result_ok_copyins_nil; exact H
        |eapply check_unlink_result_no_copyin; exact H].
  - destruct lk; cbn [unlink_nonnorm_errno] in H; cbv iota in H;
      first [nam_ret_cnil
            | eapply check_unlink_type_result_ok_copyins_nil; exact H].
Qed.

Local Lemma check_unlinkat_file_complete_ok : forall i r lk ts eff m m' evs,
  unlinkat_file_spec r lk ts m i m (Ok eff m' evs) ->
  check_unlinkat_file r lk ts eff m = CheckOk m' evs.
Proof.
  intros i r lk ts eff m m' evs H.
  unfold unlinkat_file_spec in H. unfold check_unlinkat_file.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try nam_ret_co; try (unfold unmodeled in H; inv_ok; fail).
  - destruct lk; cbn [unlink_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try nam_ret_co.
    destruct e as [data| |dk|lb]; cbv iota in H |- *;
      [| |unfold unmodeled in H; inv_ok|].
    + destruct ts; cbv iota in H |- *;
        [eapply check_unlink_type_result_complete; exact H|].
      unfold unlink_file_spec in H.
      eapply check_unlink_result_complete_ok. exact H.
    + destruct ts; eapply check_unlink_type_result_complete; exact H.
    + destruct ts; cbv iota in H |- *;
        [eapply check_unlink_type_result_complete; exact H|].
      unfold unlink_remove_spec in H.
      eapply check_unlink_result_complete_ok. exact H.
  - destruct lk; cbn [unlink_nonnorm_errno] in H |- *;
      cbv iota in H |- *;
      first [nam_ret_co | eapply check_unlink_type_result_complete; exact H].
Qed.

Local Lemma check_unlinkat_file_complete_unmodeled : forall i r lk ts m eff,
  unlinkat_file_spec r lk ts m i m Unmodeled ->
  check_unlinkat_file r lk ts eff m = CheckUnmodeled.
Proof.
  intros i r lk ts m eff H.
  unfold unlinkat_file_spec in H. unfold check_unlinkat_file.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail); try reflexivity.
  - destruct lk; cbn [unlink_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try (sys_unfold; inv_ok; fail).
    destruct e as [data| |dk|lb]; cbv iota in H |- *; [| |reflexivity|].
    + destruct ts; cbv iota in H |- *;
        [exfalso; eapply check_unlink_type_result_complete_unmodeled; exact H|].
      exfalso. unfold unlink_file_spec in H.
      eapply check_unlink_result_complete_unmodeled. exact H.
    + exfalso. destruct ts;
        eapply check_unlink_type_result_complete_unmodeled; exact H.
    + destruct ts; cbv iota in H |- *;
        [exfalso; eapply check_unlink_type_result_complete_unmodeled; exact H|].
      exfalso. unfold unlink_remove_spec in H.
      eapply check_unlink_result_complete_unmodeled. exact H.
  - destruct lk; cbn [unlink_nonnorm_errno] in H |- *;
      cbv iota in H |- *;
      first [(sys_unfold; inv_ok; fail)
            | exfalso; eapply check_unlink_type_result_complete_unmodeled; exact H].
Qed.

Local Lemma check_rmdir_sound_ok : forall i r lk eff m m' evs,
  check_rmdir r lk eff m = CheckOk m' evs ->
  rmdir_spec r lk m i m (Ok eff m' evs).
Proof.
  intros i r lk eff m m' evs H.
  unfold check_rmdir in H. unfold rmdir_spec.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try nam_ret_ok; try discriminate.
  - destruct lk; cbn [rmdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try nam_ret_ok.
    destruct e as [data| |dk|lb]; cbv iota in H |- *;
      [now apply check_unlink_type_result_sound
      |
      |now apply check_unlink_type_result_sound
      |now apply check_unlink_type_result_sound].
    destruct (path_eqb k (m_cwd m)); cbv iota in H |- *; [discriminate|].
    destruct (key_strictly_under k (m_cwd m)); cbv iota in H |- *;
      [discriminate|].
    destruct (fd_names_dir (m_fds m) k); cbv iota in H |- *; [discriminate|].
    destruct (negb (fs_dir_empty (m_fs m) k)); cbv iota in H |- *;
      [now apply check_unlink_type_result_sound|].
    now apply check_unlink_result_sound_ok.
  - destruct lk; cbn [rmdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *;
      first [nam_ret_ok | now apply check_unlink_type_result_sound].
Qed.

Local Lemma check_rmdir_sound_unmodeled : forall i r lk eff m,
  check_rmdir r lk eff m = CheckUnmodeled ->
  rmdir_spec r lk m i m Unmodeled.
Proof.
  intros i r lk eff m H.
  unfold check_rmdir in H. unfold rmdir_spec.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try nam_ret_nu; try apply unmodeled_intro.
  - destruct lk; cbn [rmdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try nam_ret_nu.
    destruct e as [data| |dk|lb]; cbv iota in H |- *;
      [exfalso; eapply check_unlink_type_result_no_unmodeled; exact H
      |
      |exfalso; eapply check_unlink_type_result_no_unmodeled; exact H
      |exfalso; eapply check_unlink_type_result_no_unmodeled; exact H].
    destruct (path_eqb k (m_cwd m)); cbv iota in H |- *;
      [apply unmodeled_intro|].
    destruct (key_strictly_under k (m_cwd m)); cbv iota in H |- *;
      [apply unmodeled_intro|].
    destruct (fd_names_dir (m_fds m) k); cbv iota in H |- *;
      [apply unmodeled_intro|].
    destruct (negb (fs_dir_empty (m_fs m) k)); cbv iota in H |- *;
      [exfalso; eapply check_unlink_type_result_no_unmodeled; exact H|].
    exfalso. eapply check_unlink_result_no_unmodeled. exact H.
  - destruct lk; cbn [rmdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *;
      first [nam_ret_nu
            | exfalso; eapply check_unlink_type_result_no_unmodeled; exact H].
Qed.

Local Lemma check_rmdir_no_copyin : forall r lk eff m m' evs,
  check_rmdir r lk eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros r lk eff m m' evs H. unfold check_rmdir in H.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try nam_ret_cnil; try discriminate.
  - destruct lk; cbn [rmdir_nonnorm_errno] in H; cbv iota in H;
      try nam_ret_cnil.
    destruct e as [data| |dk|lb]; cbv iota in H;
      [eapply check_unlink_type_result_ok_copyins_nil; exact H
      |
      |eapply check_unlink_type_result_ok_copyins_nil; exact H
      |eapply check_unlink_type_result_ok_copyins_nil; exact H].
    destruct (path_eqb k (m_cwd m)); cbv iota in H; [discriminate|].
    destruct (key_strictly_under k (m_cwd m)); cbv iota in H; [discriminate|].
    destruct (fd_names_dir (m_fds m) k); cbv iota in H; [discriminate|].
    destruct (negb (fs_dir_empty (m_fs m) k)); cbv iota in H;
      [eapply check_unlink_type_result_ok_copyins_nil; exact H|].
    eapply check_unlink_result_no_copyin. exact H.
  - destruct lk; cbn [rmdir_nonnorm_errno] in H; cbv iota in H;
      first [nam_ret_cnil
            | eapply check_unlink_type_result_ok_copyins_nil; exact H].
Qed.

Local Lemma check_rmdir_complete_ok : forall i r lk eff m m' evs,
  rmdir_spec r lk m i m (Ok eff m' evs) ->
  check_rmdir r lk eff m = CheckOk m' evs.
Proof.
  intros i r lk eff m m' evs H.
  unfold rmdir_spec in H. unfold check_rmdir.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try nam_ret_co; try (unfold unmodeled in H; inv_ok; fail).
  - destruct lk; cbn [rmdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try nam_ret_co.
    destruct e as [data| |dk|lb]; cbv iota in H |- *;
      [eapply check_unlink_type_result_complete; exact H
      |
      |eapply check_unlink_type_result_complete; exact H
      |eapply check_unlink_type_result_complete; exact H].
    destruct (path_eqb k (m_cwd m)); cbv iota in H |- *;
      [unfold unmodeled in H; inv_ok|].
    destruct (key_strictly_under k (m_cwd m)); cbv iota in H |- *;
      [unfold unmodeled in H; inv_ok|].
    destruct (fd_names_dir (m_fds m) k); cbv iota in H |- *;
      [unfold unmodeled in H; inv_ok|].
    destruct (negb (fs_dir_empty (m_fs m) k)); cbv iota in H |- *;
      [eapply check_unlink_type_result_complete; exact H|].
    eapply check_unlink_result_complete_ok. exact H.
  - destruct lk; cbn [rmdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *;
      first [nam_ret_co | eapply check_unlink_type_result_complete; exact H].
Qed.

Local Lemma check_rmdir_complete_unmodeled : forall i r lk m eff,
  rmdir_spec r lk m i m Unmodeled ->
  check_rmdir r lk eff m = CheckUnmodeled.
Proof.
  intros i r lk m eff H.
  unfold rmdir_spec in H. unfold check_rmdir.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail); try reflexivity.
  - destruct lk; cbn [rmdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try (sys_unfold; inv_ok; fail).
    destruct e as [data| |dk|lb]; cbv iota in H |- *;
      [exfalso; eapply check_unlink_type_result_complete_unmodeled; exact H
      |
      |exfalso; eapply check_unlink_type_result_complete_unmodeled; exact H
      |exfalso; eapply check_unlink_type_result_complete_unmodeled; exact H].
    destruct (path_eqb k (m_cwd m)); cbv iota in H |- *; [reflexivity|].
    destruct (key_strictly_under k (m_cwd m)); cbv iota in H |- *;
      [reflexivity|].
    destruct (fd_names_dir (m_fds m) k); cbv iota in H |- *; [reflexivity|].
    destruct (negb (fs_dir_empty (m_fs m) k)); cbv iota in H |- *;
      [exfalso; eapply check_unlink_type_result_complete_unmodeled; exact H|].
    exfalso. eapply check_unlink_result_complete_unmodeled. exact H.
  - destruct lk; cbn [rmdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *;
      first [(sys_unfold; inv_ok; fail)
            | exfalso; eapply check_unlink_type_result_complete_unmodeled; exact H].
Qed.

Local Lemma check_unlinkat_body_sound_ok : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat_body i dirfd pathp flags eff m = CheckOk m' evs ->
  unlinkat_body_spec dirfd pathp flags i m i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat_body in H. unfold unlinkat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try nam_ret_ok.
  destruct (path_eqb p []); cbv iota in H |- *; [nam_ret_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [discriminate|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  destruct (unlink_rmdir flags); cbv iota in H |- *;
    [now apply check_rmdir_sound_ok | now apply check_unlinkat_file_sound_ok].
Qed.

Local Lemma check_unlinkat_body_sound_unmodeled : forall i dirfd pathp flags eff m,
  check_unlinkat_body i dirfd pathp flags eff m = CheckUnmodeled ->
  unlinkat_body_spec dirfd pathp flags i m i m Unmodeled.
Proof.
  intros i dirfd pathp flags eff m H.
  unfold check_unlinkat_body in H. unfold unlinkat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try nam_ret_nu.
  destruct (path_eqb p []); cbv iota in H |- *; [nam_ret_nu|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [apply unmodeled_intro|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  destruct (unlink_rmdir flags); cbv iota in H |- *;
    [eapply check_rmdir_sound_unmodeled; exact H
    |eapply check_unlinkat_file_sound_unmodeled; exact H].
Qed.

Local Lemma check_unlinkat_body_complete_ok : forall i dirfd pathp flags eff m m' evs,
  unlinkat_body_spec dirfd pathp flags i m i m (Ok eff m' evs) ->
  check_unlinkat_body i dirfd pathp flags eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold unlinkat_body_spec in H. unfold check_unlinkat_body.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try nam_ret_co.
  destruct (path_eqb p []); cbv iota in H |- *; [nam_ret_co|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [unfold unmodeled in H; inv_ok|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  destruct (unlink_rmdir flags); cbv iota in H |- *;
    [eapply check_rmdir_complete_ok; exact H
    |eapply check_unlinkat_file_complete_ok; exact H].
Qed.

Local Lemma check_unlinkat_body_complete_unmodeled : forall i dirfd pathp flags m eff,
  unlinkat_body_spec dirfd pathp flags i m i m Unmodeled ->
  check_unlinkat_body i dirfd pathp flags eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  unfold unlinkat_body_spec in H. unfold check_unlinkat_body.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail).
  destruct (path_eqb p []); cbv iota in H |- *; [sys_unfold; inv_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [reflexivity|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  destruct (unlink_rmdir flags); cbv iota in H |- *;
    [eapply check_rmdir_complete_unmodeled; exact H
    |eapply check_unlinkat_file_complete_unmodeled; exact H].
Qed.

(** No arm of the body claims a copy-in of its own: each returns either
    through [check_ret_only], which forces every ledger empty, or through
    [check_unlink_result], which matches six empty lists.  That is what
    lets the wrapper below equate the WHOLE claimed ledger with the one
    pathname range rather than with a prefix of it. *)
Local Lemma check_unlinkat_body_ok_copyins_nil :
    forall i dirfd pathp flags eff m m' evs,
  check_unlinkat_body i dirfd pathp flags eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat_body in H.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H;
    try nam_ret_cnil.
  destruct (path_eqb p []); cbv iota in H; [nam_ret_cnil|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H; [discriminate|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H.
  destruct (unlink_rmdir flags); cbv iota in H;
    [eapply check_rmdir_no_copyin; exact H
    |eapply check_unlinkat_file_no_copyin; exact H].
Qed.

Local Lemma check_mkdirat_body_sound_ok : forall i dirfd pathp eff m m' evs,
  check_mkdirat_body i dirfd pathp eff m = CheckOk m' evs ->
  mkdirat_body_spec dirfd pathp i m i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp eff m m' evs H.
  unfold check_mkdirat_body in H. unfold mkdirat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try nam_ret_ok.
  destruct (path_eqb p []); cbv iota in H |- *; [nam_ret_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [discriminate|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try nam_ret_ok; try discriminate.
  - destruct lk; cbn [mkdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; nam_ret_ok.
  - destruct lk; cbn [mkdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try nam_ret_ok.
    destruct (Nat.ltb Fs.dir_count_max (S (Fs.dl_counting (Fs.fs_dir_links (m_fs m) par))));
      cbv iota in H |- *;
      [discriminate|].
    now apply check_mkdir_result_sound_ok.
Qed.

Local Lemma check_mkdirat_body_sound_unmodeled : forall i dirfd pathp eff m,
  check_mkdirat_body i dirfd pathp eff m = CheckUnmodeled ->
  mkdirat_body_spec dirfd pathp i m i m Unmodeled.
Proof.
  intros i dirfd pathp eff m H.
  unfold check_mkdirat_body in H. unfold mkdirat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try nam_ret_nu.
  destruct (path_eqb p []); cbv iota in H |- *; [nam_ret_nu|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [apply unmodeled_intro|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try nam_ret_nu; try apply unmodeled_intro.
  - destruct lk; cbn [mkdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; nam_ret_nu.
  - destruct lk; cbn [mkdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try nam_ret_nu.
    destruct (Nat.ltb Fs.dir_count_max (S (Fs.dl_counting (Fs.fs_dir_links (m_fs m) par))));
      cbv iota in H |- *;
      [apply unmodeled_intro|].
    exfalso. eapply check_mkdir_result_no_unmodeled. exact H.
Qed.

Local Lemma check_mkdirat_body_complete_ok : forall i dirfd pathp eff m m' evs,
  mkdirat_body_spec dirfd pathp i m i m (Ok eff m' evs) ->
  check_mkdirat_body i dirfd pathp eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp eff m m' evs H.
  unfold mkdirat_body_spec in H. unfold check_mkdirat_body.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try nam_ret_co.
  destruct (path_eqb p []); cbv iota in H |- *; [nam_ret_co|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [unfold unmodeled in H; inv_ok|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try nam_ret_co; try (unfold unmodeled in H; inv_ok; fail).
  - destruct lk; cbn [mkdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; nam_ret_co.
  - destruct lk; cbn [mkdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try nam_ret_co.
    destruct (Nat.ltb Fs.dir_count_max (S (Fs.dl_counting (Fs.fs_dir_links (m_fs m) par))));
      cbv iota in H |- *;
      [unfold unmodeled in H; inv_ok|].
    eapply check_mkdir_result_complete_ok. exact H.
Qed.

Local Lemma check_mkdirat_body_complete_unmodeled : forall i dirfd pathp m eff,
  mkdirat_body_spec dirfd pathp i m i m Unmodeled ->
  check_mkdirat_body i dirfd pathp eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp m eff H.
  unfold mkdirat_body_spec in H. unfold check_mkdirat_body.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail).
  destruct (path_eqb p []); cbv iota in H |- *; [sys_unfold; inv_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [reflexivity|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail); try reflexivity.
  - destruct lk; cbn [mkdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; sys_unfold; inv_ok.
  - destruct lk; cbn [mkdir_nonnorm_errno] in H |- *;
      cbv iota in H |- *; try (sys_unfold; inv_ok; fail).
    destruct (Nat.ltb Fs.dir_count_max (S (Fs.dl_counting (Fs.fs_dir_links (m_fs m) par))));
      cbv iota in H |- *;
      [reflexivity|].
    exfalso. eapply check_mkdir_result_complete_unmodeled. exact H.
Qed.

Local Lemma check_mkdirat_body_ok_copyins_nil :
    forall i dirfd pathp eff m m' evs,
  check_mkdirat_body i dirfd pathp eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros i dirfd pathp eff m m' evs H.
  unfold check_mkdirat_body in H.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H;
    try nam_ret_cnil.
  destruct (path_eqb p []); cbv iota in H; [nam_ret_cnil|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H; [discriminate|].
  destruct (Fs.resolve_parent (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try nam_ret_cnil; try discriminate.
  - destruct lk; cbn [mkdir_nonnorm_errno] in H; cbv iota in H; nam_ret_cnil.
  - destruct lk; cbn [mkdir_nonnorm_errno] in H; cbv iota in H;
      try nam_ret_cnil.
    destruct (Nat.ltb Fs.dir_count_max (S (Fs.dl_counting (Fs.fs_dir_links (m_fs m) par))));
      cbv iota in H;
      [discriminate|].
    eapply check_mkdir_result_no_copyin. exact H.
Qed.

(* ------------------------------------------------------- the walk's refusals

   Each body with [check_walk_refusals] around it, from the body's four
   and [Checks.Sys.Prelude]'s section lemmas. *)

Local Lemma check_unlinkat_walked_sound_ok : forall i dirfd pathp flags m eff m' evs,
  check_walk_refusals Fs.WalkParent i pathp eff m (check_unlinkat_body i dirfd pathp flags eff m)
    = CheckOk m' evs ->
  walk_refusals Fs.WalkParent pathp (unlinkat_body_spec dirfd pathp flags i m) i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags m.
  apply (check_walk_refusals_sound_ok Fs.WalkParent _
           (fun e => check_unlinkat_body i dirfd pathp flags e m)).
  - intros. eapply check_unlinkat_body_sound_ok. eassumption.
  - intros. eapply check_unlinkat_body_sound_unmodeled. eassumption.
  - intros. eapply check_unlinkat_body_complete_ok. eassumption.
  - intros. eapply check_unlinkat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_unlinkat_walked_sound_unmodeled : forall i dirfd pathp flags m eff,
  check_walk_refusals Fs.WalkParent i pathp eff m (check_unlinkat_body i dirfd pathp flags eff m)
    = CheckUnmodeled ->
  walk_refusals Fs.WalkParent pathp (unlinkat_body_spec dirfd pathp flags i m) i m Unmodeled.
Proof.
  intros i dirfd pathp flags m.
  apply (check_walk_refusals_sound_unmodeled Fs.WalkParent _
           (fun e => check_unlinkat_body i dirfd pathp flags e m)).
  - intros. eapply check_unlinkat_body_sound_ok. eassumption.
  - intros. eapply check_unlinkat_body_sound_unmodeled. eassumption.
  - intros. eapply check_unlinkat_body_complete_ok. eassumption.
  - intros. eapply check_unlinkat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_unlinkat_walked_complete_ok : forall i dirfd pathp flags m eff m' evs,
  walk_refusals Fs.WalkParent pathp (unlinkat_body_spec dirfd pathp flags i m) i m (Ok eff m' evs) ->
  check_walk_refusals Fs.WalkParent i pathp eff m (check_unlinkat_body i dirfd pathp flags eff m)
    = CheckOk m' evs.
Proof.
  intros i dirfd pathp flags m.
  apply (check_walk_refusals_complete_ok Fs.WalkParent _
           (fun e => check_unlinkat_body i dirfd pathp flags e m)).
  - intros. eapply check_unlinkat_body_sound_ok. eassumption.
  - intros. eapply check_unlinkat_body_sound_unmodeled. eassumption.
  - intros. eapply check_unlinkat_body_complete_ok. eassumption.
  - intros. eapply check_unlinkat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_unlinkat_walked_complete_unmodeled : forall i dirfd pathp flags m eff,
  walk_refusals Fs.WalkParent pathp (unlinkat_body_spec dirfd pathp flags i m) i m Unmodeled ->
  check_walk_refusals Fs.WalkParent i pathp eff m (check_unlinkat_body i dirfd pathp flags eff m)
    = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m.
  apply (check_walk_refusals_complete_unmodeled Fs.WalkParent _
           (fun e => check_unlinkat_body i dirfd pathp flags e m)).
  - intros. eapply check_unlinkat_body_sound_ok. eassumption.
  - intros. eapply check_unlinkat_body_sound_unmodeled. eassumption.
  - intros. eapply check_unlinkat_body_complete_ok. eassumption.
  - intros. eapply check_unlinkat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_unlinkat_walked_ok_copyins_nil :
    forall i dirfd pathp flags eff m m' evs,
  check_walk_refusals Fs.WalkParent i pathp eff m (check_unlinkat_body i dirfd pathp flags eff m)
    = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  eapply check_walk_refusals_copyins_nil; [|exact H].
  intros. eapply check_unlinkat_body_ok_copyins_nil. eassumption.
Qed.

Local Lemma check_mkdirat_walked_sound_ok : forall i dirfd pathp m eff m' evs,
  check_walk_refusals Fs.WalkParent i pathp eff m (check_mkdirat_body i dirfd pathp eff m)
    = CheckOk m' evs ->
  walk_refusals Fs.WalkParent pathp (mkdirat_body_spec dirfd pathp i m) i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp m.
  apply (check_walk_refusals_sound_ok Fs.WalkParent _
           (fun e => check_mkdirat_body i dirfd pathp e m)).
  - intros. eapply check_mkdirat_body_sound_ok. eassumption.
  - intros. eapply check_mkdirat_body_sound_unmodeled. eassumption.
  - intros. eapply check_mkdirat_body_complete_ok. eassumption.
  - intros. eapply check_mkdirat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_mkdirat_walked_sound_unmodeled : forall i dirfd pathp m eff,
  check_walk_refusals Fs.WalkParent i pathp eff m (check_mkdirat_body i dirfd pathp eff m)
    = CheckUnmodeled ->
  walk_refusals Fs.WalkParent pathp (mkdirat_body_spec dirfd pathp i m) i m Unmodeled.
Proof.
  intros i dirfd pathp m.
  apply (check_walk_refusals_sound_unmodeled Fs.WalkParent _
           (fun e => check_mkdirat_body i dirfd pathp e m)).
  - intros. eapply check_mkdirat_body_sound_ok. eassumption.
  - intros. eapply check_mkdirat_body_sound_unmodeled. eassumption.
  - intros. eapply check_mkdirat_body_complete_ok. eassumption.
  - intros. eapply check_mkdirat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_mkdirat_walked_complete_ok : forall i dirfd pathp m eff m' evs,
  walk_refusals Fs.WalkParent pathp (mkdirat_body_spec dirfd pathp i m) i m (Ok eff m' evs) ->
  check_walk_refusals Fs.WalkParent i pathp eff m (check_mkdirat_body i dirfd pathp eff m)
    = CheckOk m' evs.
Proof.
  intros i dirfd pathp m.
  apply (check_walk_refusals_complete_ok Fs.WalkParent _
           (fun e => check_mkdirat_body i dirfd pathp e m)).
  - intros. eapply check_mkdirat_body_sound_ok. eassumption.
  - intros. eapply check_mkdirat_body_sound_unmodeled. eassumption.
  - intros. eapply check_mkdirat_body_complete_ok. eassumption.
  - intros. eapply check_mkdirat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_mkdirat_walked_complete_unmodeled : forall i dirfd pathp m eff,
  walk_refusals Fs.WalkParent pathp (mkdirat_body_spec dirfd pathp i m) i m Unmodeled ->
  check_walk_refusals Fs.WalkParent i pathp eff m (check_mkdirat_body i dirfd pathp eff m)
    = CheckUnmodeled.
Proof.
  intros i dirfd pathp m.
  apply (check_walk_refusals_complete_unmodeled Fs.WalkParent _
           (fun e => check_mkdirat_body i dirfd pathp e m)).
  - intros. eapply check_mkdirat_body_sound_ok. eassumption.
  - intros. eapply check_mkdirat_body_sound_unmodeled. eassumption.
  - intros. eapply check_mkdirat_body_complete_ok. eassumption.
  - intros. eapply check_mkdirat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_mkdirat_walked_ok_copyins_nil :
    forall i dirfd pathp eff m m' evs,
  check_walk_refusals Fs.WalkParent i pathp eff m (check_mkdirat_body i dirfd pathp eff m)
    = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros i dirfd pathp eff m m' evs H.
  eapply check_walk_refusals_copyins_nil; [|exact H].
  intros. eapply check_mkdirat_body_ok_copyins_nil. eassumption.
Qed.

(* ------------------------------------------------------- the fetched call

   Each walked body with the pathname copy-in threaded: the part of the
   call [getname_flags]' own refusals wrap.  The lemmas are stated over
   the checker's own expression, not over a name for it: a name the
   kernel has to unfold against that expression costs minutes per
   [Qed]. *)

Local Lemma check_unlinkat_fetched_sound_ok : forall i dirfd pathp flags m eff m' evs,
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
       (check_unlinkat_body i dirfd pathp flags (clear_copyins eff) m))
  = CheckOk m' evs ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals Fs.WalkParent pathp (unlinkat_body_spec dirfd pathp flags i m))
    i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags m eff m' evs H.
  apply check_copyins_after_ok_iff in H. destruct H as (Hreads & Hbody).
  apply record_copyins_clear_ok; [exact Hreads|].
  now apply check_unlinkat_walked_sound_ok.
Qed.

Local Lemma check_unlinkat_fetched_sound_unmodeled : forall i dirfd pathp flags m eff,
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
       (check_unlinkat_body i dirfd pathp flags (clear_copyins eff) m))
  = CheckUnmodeled ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals Fs.WalkParent pathp (unlinkat_body_spec dirfd pathp flags i m))
    i m Unmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  apply check_copyins_after_unmodeled in H.
  apply record_copyins_unmodeled.
  eapply check_unlinkat_walked_sound_unmodeled. exact H.
Qed.

Local Lemma check_unlinkat_fetched_complete_ok : forall i dirfd pathp flags m eff m' evs,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals Fs.WalkParent pathp (unlinkat_body_spec dirfd pathp flags i m))
    i m (Ok eff m' evs) ->
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
       (check_unlinkat_body i dirfd pathp flags (clear_copyins eff) m))
  = CheckOk m' evs.
Proof.
  intros i dirfd pathp flags m eff m' evs H.
  apply record_copyins_ok_inv in H.
  destruct H as (core & Hcore & ->).
  apply check_unlinkat_walked_complete_ok in Hcore.
  pose proof (check_unlinkat_walked_ok_copyins_nil _ _ _ _ _ _ _ _ Hcore) as Hnil.
  apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
  - cbn [with_copyins eff_copyins]. rewrite Hnil, app_nil_r. reflexivity.
  - destruct core as [ret ws zs us cs copyins].
    cbn in Hnil. subst copyins. exact Hcore.
Qed.

Local Lemma check_unlinkat_fetched_complete_unmodeled : forall i dirfd pathp flags m eff,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals Fs.WalkParent pathp (unlinkat_body_spec dirfd pathp flags i m))
    i m Unmodeled ->
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
       (check_unlinkat_body i dirfd pathp flags (clear_copyins eff) m))
  = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  apply record_copyins_unmodeled_inv in H.
  unfold check_copyins_after.
  rewrite (check_unlinkat_walked_complete_unmodeled i dirfd pathp flags m
             (clear_copyins eff) H). reflexivity.
Qed.

Local Lemma check_mkdirat_fetched_sound_ok : forall i dirfd pathp m eff m' evs,
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
       (check_mkdirat_body i dirfd pathp (clear_copyins eff) m))
  = CheckOk m' evs ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals Fs.WalkParent pathp (mkdirat_body_spec dirfd pathp i m))
    i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp m eff m' evs H.
  apply check_copyins_after_ok_iff in H. destruct H as (Hreads & Hbody).
  apply record_copyins_clear_ok; [exact Hreads|].
  now apply check_mkdirat_walked_sound_ok.
Qed.

Local Lemma check_mkdirat_fetched_sound_unmodeled : forall i dirfd pathp m eff,
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
       (check_mkdirat_body i dirfd pathp (clear_copyins eff) m))
  = CheckUnmodeled ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals Fs.WalkParent pathp (mkdirat_body_spec dirfd pathp i m))
    i m Unmodeled.
Proof.
  intros i dirfd pathp m eff H.
  apply check_copyins_after_unmodeled in H.
  apply record_copyins_unmodeled.
  eapply check_mkdirat_walked_sound_unmodeled. exact H.
Qed.

Local Lemma check_mkdirat_fetched_complete_ok : forall i dirfd pathp m eff m' evs,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals Fs.WalkParent pathp (mkdirat_body_spec dirfd pathp i m))
    i m (Ok eff m' evs) ->
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
       (check_mkdirat_body i dirfd pathp (clear_copyins eff) m))
  = CheckOk m' evs.
Proof.
  intros i dirfd pathp m eff m' evs H.
  apply record_copyins_ok_inv in H. destruct H as (core & Hcore & ->).
  apply check_mkdirat_walked_complete_ok in Hcore.
  pose proof (check_mkdirat_walked_ok_copyins_nil _ _ _ _ _ _ _ Hcore) as Hnil.
  apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
  - cbn [with_copyins eff_copyins]. rewrite Hnil, app_nil_r. reflexivity.
  - destruct core as [ret ws zs us cs copyins].
    cbn in Hnil. subst copyins. exact Hcore.
Qed.

Local Lemma check_mkdirat_fetched_complete_unmodeled : forall i dirfd pathp m eff,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals Fs.WalkParent pathp (mkdirat_body_spec dirfd pathp i m))
    i m Unmodeled ->
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
       (check_mkdirat_body i dirfd pathp (clear_copyins eff) m))
  = CheckUnmodeled.
Proof.
  intros i dirfd pathp m eff H.
  apply record_copyins_unmodeled_inv in H.
  unfold check_copyins_after.
  rewrite (check_mkdirat_walked_complete_unmodeled i dirfd pathp m
             (clear_copyins eff) H). reflexivity.
Qed.

(* ------------------------------------------------------- the four exports

   Each is the fetched call above with [getname_flags]' own refusals
   around it ([Checks.Sys.Prelude]'s section lemmas) and, for unlinkat,
   the flag arm in front.  The flag arm carries no copy-in: the kernel
   decides it before [getname()]. *)

Lemma check_unlinkat_sound_ok : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs ->
  unlinkat_spec dirfd pathp flags i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat in H. unfold unlinkat_spec.
  destruct (negb (modeled_unlink_flags flags)) eqn:Hfl; cbv iota in H.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    ul_open. apply pure_ok. }
  cbv zeta in H. ul_open.
  exact (check_getname_refusals_sound_ok pathp _ _ i m
           (check_unlinkat_fetched_sound_ok i dirfd pathp flags m)
           (check_unlinkat_fetched_sound_unmodeled i dirfd pathp flags m)
           (check_unlinkat_fetched_complete_ok i dirfd pathp flags m)
           (check_unlinkat_fetched_complete_unmodeled i dirfd pathp flags m)
           eff m' evs H).
Qed.

Lemma check_unlinkat_sound_unmodeled : forall i dirfd pathp flags eff m,
  check_unlinkat i dirfd pathp flags eff m = CheckUnmodeled ->
  unlinkat_spec dirfd pathp flags i m Unmodeled.
Proof.
  intros i dirfd pathp flags eff m H.
  unfold check_unlinkat in H. unfold unlinkat_spec.
  destruct (negb (modeled_unlink_flags flags)) eqn:Hfl; cbv iota in H;
    [now apply check_ret_only_no_unmodeled in H|].
  cbv zeta in H. ul_open_u.
  exact (check_getname_refusals_sound_unmodeled pathp _ _ i m
           (check_unlinkat_fetched_sound_ok i dirfd pathp flags m)
           (check_unlinkat_fetched_sound_unmodeled i dirfd pathp flags m)
           (check_unlinkat_fetched_complete_ok i dirfd pathp flags m)
           (check_unlinkat_fetched_complete_unmodeled i dirfd pathp flags m)
           eff H).
Qed.

Lemma check_unlinkat_complete_ok : forall i dirfd pathp flags eff m m' evs,
  unlinkat_spec dirfd pathp flags i m (Ok eff m' evs) ->
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold unlinkat_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta iota in H.
  unfold check_unlinkat.
  destruct (negb (modeled_unlink_flags flags)) eqn:Hfl.
  { cbv iota in H. unfold err_ret, ret_only, pure in H. inversion H; subst.
    cbn. rewrite bv_eqb_refl. reflexivity. }
  cbv iota in H. cbv zeta.
  exact (check_getname_refusals_complete_ok pathp _ _ i m
           (check_unlinkat_fetched_sound_ok i dirfd pathp flags m)
           (check_unlinkat_fetched_sound_unmodeled i dirfd pathp flags m)
           (check_unlinkat_fetched_complete_ok i dirfd pathp flags m)
           (check_unlinkat_fetched_complete_unmodeled i dirfd pathp flags m)
           eff m' evs H).
Qed.

Lemma check_unlinkat_complete_unmodeled : forall i dirfd pathp flags m eff,
  unlinkat_spec dirfd pathp flags i m Unmodeled ->
  check_unlinkat i dirfd pathp flags eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  unfold unlinkat_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply get_model_bind_unmodeled_inv in H. cbv beta iota in H.
  unfold check_unlinkat.
  destruct (negb (modeled_unlink_flags flags)) eqn:Hfl.
  { cbv iota in H. unfold err_ret, ret_only, pure in H. discriminate H. }
  cbv iota in H. cbv zeta.
  exact (check_getname_refusals_complete_unmodeled pathp _ _ i m
           (check_unlinkat_fetched_sound_ok i dirfd pathp flags m)
           (check_unlinkat_fetched_sound_unmodeled i dirfd pathp flags m)
           (check_unlinkat_fetched_complete_ok i dirfd pathp flags m)
           (check_unlinkat_fetched_complete_unmodeled i dirfd pathp flags m)
           eff H).
Qed.

(* ------------------------------------------------------- mkdirat's four

   The same shape as unlinkat's, with no flag arm in front: mkdirat has
   no flag word at all, so the whole call sits inside the wrappers. *)

(** [check_mkdirat] unfolded, as an equation.  The two soundness
    exports rewrite their hypothesis with it: with no flag test to case
    on first, handing the kernel the hypothesis itself where its
    unfolded type is expected cost about 150 s per [Qed]. *)
Local Lemma check_mkdirat_eq : forall i dirfd pathp eff m,
  check_mkdirat i dirfd pathp eff m
  = check_getname_refusals i pathp eff m
      (check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
         (check_walk_refusals Fs.WalkParent i pathp (clear_copyins eff) m
            (check_mkdirat_body i dirfd pathp (clear_copyins eff) m))).
Proof. intros. unfold check_mkdirat. cbv zeta. reflexivity. Qed.

Lemma check_mkdirat_sound_ok : forall i dirfd pathp eff m m' evs,
  check_mkdirat i dirfd pathp eff m = CheckOk m' evs ->
  mkdirat_spec dirfd pathp i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp eff m m' evs H.
  rewrite check_mkdirat_eq in H. unfold mkdirat_spec. ul_open.
  exact (check_getname_refusals_sound_ok pathp _ _ i m
           (check_mkdirat_fetched_sound_ok i dirfd pathp m)
           (check_mkdirat_fetched_sound_unmodeled i dirfd pathp m)
           (check_mkdirat_fetched_complete_ok i dirfd pathp m)
           (check_mkdirat_fetched_complete_unmodeled i dirfd pathp m)
           eff m' evs H).
Qed.

Lemma check_mkdirat_sound_unmodeled : forall i dirfd pathp eff m,
  check_mkdirat i dirfd pathp eff m = CheckUnmodeled ->
  mkdirat_spec dirfd pathp i m Unmodeled.
Proof.
  intros i dirfd pathp eff m H.
  rewrite check_mkdirat_eq in H. unfold mkdirat_spec. ul_open_u.
  exact (check_getname_refusals_sound_unmodeled pathp _ _ i m
           (check_mkdirat_fetched_sound_ok i dirfd pathp m)
           (check_mkdirat_fetched_sound_unmodeled i dirfd pathp m)
           (check_mkdirat_fetched_complete_ok i dirfd pathp m)
           (check_mkdirat_fetched_complete_unmodeled i dirfd pathp m)
           eff H).
Qed.

Lemma check_mkdirat_complete_ok : forall i dirfd pathp eff m m' evs,
  mkdirat_spec dirfd pathp i m (Ok eff m' evs) ->
  check_mkdirat i dirfd pathp eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp eff m m' evs H.
  unfold mkdirat_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta iota in H.
  unfold check_mkdirat. cbv zeta.
  exact (check_getname_refusals_complete_ok pathp _ _ i m
           (check_mkdirat_fetched_sound_ok i dirfd pathp m)
           (check_mkdirat_fetched_sound_unmodeled i dirfd pathp m)
           (check_mkdirat_fetched_complete_ok i dirfd pathp m)
           (check_mkdirat_fetched_complete_unmodeled i dirfd pathp m)
           eff m' evs H).
Qed.

Lemma check_mkdirat_complete_unmodeled : forall i dirfd pathp m eff,
  mkdirat_spec dirfd pathp i m Unmodeled ->
  check_mkdirat i dirfd pathp eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp m eff H.
  unfold mkdirat_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply get_model_bind_unmodeled_inv in H. cbv beta iota in H.
  unfold check_mkdirat. cbv zeta.
  exact (check_getname_refusals_complete_unmodeled pathp _ _ i m
           (check_mkdirat_fetched_sound_ok i dirfd pathp m)
           (check_mkdirat_fetched_sound_unmodeled i dirfd pathp m)
           (check_mkdirat_fetched_complete_ok i dirfd pathp m)
           (check_mkdirat_fetched_complete_unmodeled i dirfd pathp m)
           eff H).
Qed.
