(** * LinuxProcessSem.Checks.Sys.Fs.Namei — the unlinkat (35) checker, and its proofs

    Mirrors [Sys/Fs/Namei.v], which answers to Linux [fs/namei.c]: this
    file holds the checkers for the syscalls defined there, and no
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
  Prelude.

(** The acceptor for the arm of [Fs.Namei.unlinkat_spec] that can
    succeed: either an injectable errno with no state change, or the
    removal itself, returning 0.  Both take a bare return and FIVE EMPTY
    ledgers — the kernel's unlinkat writes, zeroes, unmaps and copies
    nothing — so only a forged ledger reaches the other half of the
    claim. *)
Definition check_unlink_result (p : path) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in unlinkat_errnos ret then CheckOk m []
      else if bv_eqb ret (Z_to_bv 64 0)
           then CheckOk (with_fs (fs_remove (m_fs m) p) m) []
           else CheckReject
  | _ => CheckReject
  end.

(** Mirrors [Fs.Namei.unlink_found_spec], the tail both arms share. *)
Local Definition check_unlink_found (p c : path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if unlink_rmdir flags then check_ret_only eff (errno_ret ENOTDIR) m []
  else if path_trailing_slash p
  then check_ret_only eff (errno_ret ENOTDIR) m []
  else if fd_names_path (m_fds m) c then CheckUnmodeled
  else check_unlink_result c eff m.

(** Mirrors [Fs.Namei.unlinkat_tmp_spec]; that definition carries the
    premise, says what the absent key's -ENOENT rests on, and says what
    each decline is for. *)
Local Definition check_unlinkat_tmp (n p c : path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if unlink_rmdir flags then CheckUnmodeled
  else if Nat.ltb NAME_MAX (length n) then CheckUnmodeled
  else if fs_under (m_fs m) c then check_ret_only eff (errno_ret EISDIR) m []
  else
    match fs_lookup (m_fs m) c with
    | None => check_ret_only eff (errno_ret ENOENT) m []
    | Some _ => check_unlink_found p c flags eff m
    end.

Local Definition check_unlinkat_body (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
    match user_read_cstr i m pathp with
    | UOk CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
    | UFault | UOk CstrFault => check_ret_only eff (errno_ret EFAULT) m []
    | USpecial => CheckUnmodeled
    | UOk (CstrOk p) =>
        if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
        else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
        else
          let c := path_strip_trailing_slashes p in
          if path_eqb c [] then
            (if unlink_rmdir flags
             then check_ret_only eff (errno_ret EBUSY) m []
             else check_ret_only eff (errno_ret EISDIR) m [])
          else if path_has_slash c then
            (match tmp_name c with
             | Some n => check_unlinkat_tmp n p c flags eff m
             | None => CheckUnmodeled
             end)
          else if path_eqb c dot_path then
            (if unlink_rmdir flags
             then check_ret_only eff (errno_ret EINVAL) m []
             else check_ret_only eff (errno_ret EISDIR) m [])
          else if path_eqb c dotdot_path then
            (if unlink_rmdir flags
             then check_ret_only eff (errno_ret ENOTEMPTY) m []
             else check_ret_only eff (errno_ret EISDIR) m [])
          else if Nat.ltb NAME_MAX (length c) then CheckUnmodeled
          else if fs_under (m_fs m) c then CheckUnmodeled
          else
          match fs_lookup (m_fs m) c with
          | None => check_ret_only eff (errno_ret ENOENT) m []
          | Some _ => check_unlink_found p c flags eff m
          end
    end.

(** The pathname copy-in, as [Fs.Open.check_openat] checks it: decide the
    body against the effect with the ledger cleared, then require the
    claimed ledger to be exactly that one range.  The flag arm is outside
    the wrapper because the kernel decides it before [getname()], so an
    honest -EINVAL there carries no copy-in at all. *)
Definition check_unlinkat (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (modeled_unlink_flags flags)
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let reads := [(pathp, user_cstr_access_len i m pathp)] in
    check_copyins_after reads eff
      (check_unlinkat_body i dirfd pathp flags (clear_copyins eff) m).

(** Read the input and the model, the two steps [unlinkat_spec] takes
    before the flag test. *)
Ltac ul_open :=
  eapply bind_ok0; [apply input_ok|]; cbv beta;
  eapply bind_ok0; [apply get_model_ok|]; cbv beta iota.

(** The same two steps when the outcome being justified is [Unmodeled]. *)
Ltac ul_open_u :=
  eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
  eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota.

Local Lemma check_unlink_found_sound_ok : forall i p c flags eff m m' evs,
  check_unlink_found p c flags eff m = CheckOk m' evs ->
  unlink_found_spec p c flags m i m (Ok eff m' evs).
Proof.
  intros i p c flags eff m m' evs H.
  unfold check_unlink_found in H. unfold unlink_found_spec.
  destruct (unlink_rmdir flags).
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (path_trailing_slash p).
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (fd_names_path (m_fds m) c); [discriminate|].
  unfold check_unlink_result in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws as [|w ws'];
    [destruct zs as [|z zs']|]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  destruct (errno_ret_in unlinkat_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    apply pure_ok.
  - destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq; subst ret.
    apply alt_r. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Local Lemma check_unlink_found_sound_unmodeled : forall i p c flags eff m,
  check_unlink_found p c flags eff m = CheckUnmodeled ->
  unlink_found_spec p c flags m i m Unmodeled.
Proof.
  intros i p c flags eff m H.
  unfold check_unlink_found in H. unfold unlink_found_spec.
  destruct (unlink_rmdir flags);
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (path_trailing_slash p);
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (fd_names_path (m_fds m) c); [apply unmodeled_intro|].
  exfalso. unfold check_unlink_result in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws; [destruct zs|];
    destruct us; destruct cs; destruct cis; try discriminate.
  destruct (errno_ret_in unlinkat_errnos ret); [discriminate|].
  destruct (bv_eqb ret (Z_to_bv 64 0)); discriminate.
Qed.

Local Lemma check_unlink_found_ok_copyins_nil : forall p c flags eff m m' evs,
  check_unlink_found p c flags eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros p c flags eff m m' evs H.
  unfold check_unlink_found in H.
  destruct (unlink_rmdir flags);
    [apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity|].
  destruct (path_trailing_slash p);
    [apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity|].
  destruct (fd_names_path (m_fds m) c); [discriminate|].
  unfold check_unlink_result in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws; [destruct zs|];
    destruct us; destruct cs; destruct cis; try discriminate; reflexivity.
Qed.

Local Lemma check_unlinkat_tmp_sound_ok : forall i n p c flags eff m m' evs,
  check_unlinkat_tmp n p c flags eff m = CheckOk m' evs ->
  unlinkat_tmp_spec n p c flags m i m (Ok eff m' evs).
Proof.
  intros i n p c flags eff m m' evs H.
  unfold check_unlinkat_tmp in H. unfold unlinkat_tmp_spec.
  destruct (unlink_rmdir flags); [discriminate|].
  destruct (Nat.ltb NAME_MAX (length n)); [discriminate|].
  destruct (fs_under (m_fs m) c).
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (fs_lookup (m_fs m) c) as [data|].
  2: { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
       apply pure_ok. }
  now apply check_unlink_found_sound_ok.
Qed.

Local Lemma check_unlinkat_tmp_sound_unmodeled : forall i n p c flags eff m,
  check_unlinkat_tmp n p c flags eff m = CheckUnmodeled ->
  unlinkat_tmp_spec n p c flags m i m Unmodeled.
Proof.
  intros i n p c flags eff m H.
  unfold check_unlinkat_tmp in H. unfold unlinkat_tmp_spec.
  destruct (unlink_rmdir flags); [apply unmodeled_intro|].
  destruct (Nat.ltb NAME_MAX (length n)); [apply unmodeled_intro|].
  destruct (fs_under (m_fs m) c);
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (fs_lookup (m_fs m) c) as [data|];
    [|now apply check_ret_only_no_unmodeled in H].
  eapply check_unlink_found_sound_unmodeled. exact H.
Qed.

Local Lemma check_unlinkat_tmp_ok_copyins_nil : forall n p c flags eff m m' evs,
  check_unlinkat_tmp n p c flags eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros n p c flags eff m m' evs H.
  unfold check_unlinkat_tmp in H.
  destruct (unlink_rmdir flags); [discriminate|].
  destruct (Nat.ltb NAME_MAX (length n)); [discriminate|].
  destruct (fs_under (m_fs m) c);
    [apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _);
     reflexivity|].
  destruct (fs_lookup (m_fs m) c) as [data|];
    [|apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _);
      reflexivity].
  eapply check_unlink_found_ok_copyins_nil. exact H.
Qed.

Local Lemma check_unlinkat_body_sound_ok : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat_body i dirfd pathp flags eff m = CheckOk m' evs ->
  unlinkat_body_spec dirfd pathp flags i m i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat_body in H. unfold unlinkat_body_spec.
  destruct (user_read_cstr i m pathp) as [[p| |]| |] eqn:Hp.
  2-4: apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
       apply pure_ok.
  2: discriminate.
  destruct (path_eqb p []) eqn:Hpe.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; [discriminate|].
  cbv zeta in H |- *.
  destruct (path_eqb (path_strip_trailing_slashes p) []) eqn:Hroot.
  { destruct (unlink_rmdir flags) eqn:Hrm;
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      apply pure_ok. }
  destruct (path_has_slash (path_strip_trailing_slashes p)) eqn:Hsl.
  { destruct (tmp_name (path_strip_trailing_slashes p)) as [n|] eqn:Htn;
      [now apply check_unlinkat_tmp_sound_ok|discriminate]. }
  destruct (path_eqb (path_strip_trailing_slashes p) dot_path) eqn:Hdot.
  { destruct (unlink_rmdir flags) eqn:Hrm;
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      apply pure_ok. }
  destruct (path_eqb (path_strip_trailing_slashes p) dotdot_path) eqn:Hdd.
  { destruct (unlink_rmdir flags) eqn:Hrm;
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      apply pure_ok. }
  destruct (Nat.ltb NAME_MAX (length (path_strip_trailing_slashes p))) eqn:Hnm;
    [discriminate|].
  destruct (fs_under (m_fs m) (path_strip_trailing_slashes p)) eqn:Hun;
    [discriminate|].
  destruct (fs_lookup (m_fs m) (path_strip_trailing_slashes p)) as [data|] eqn:Hfs.
  2: { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
       apply pure_ok. }
  now apply check_unlink_found_sound_ok.
Qed.

Local Lemma check_unlinkat_body_sound_unmodeled : forall i dirfd pathp flags eff m,
  check_unlinkat_body i dirfd pathp flags eff m = CheckUnmodeled ->
  unlinkat_body_spec dirfd pathp flags i m i m Unmodeled.
Proof.
  intros i dirfd pathp flags eff m H.
  unfold check_unlinkat_body in H. unfold unlinkat_body_spec.
  destruct (user_read_cstr i m pathp) as [[p| |]| |] eqn:Hp;
    [|now apply check_ret_only_no_unmodeled in H
     |now apply check_ret_only_no_unmodeled in H
     |now apply check_ret_only_no_unmodeled in H
     |apply unmodeled_intro].
  destruct (path_eqb p []) eqn:Hpe;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd.
  { apply unmodeled_intro. }
  cbv zeta in H |- *.
  destruct (path_eqb (path_strip_trailing_slashes p) []) eqn:Hroot.
  { destruct (unlink_rmdir flags); now apply check_ret_only_no_unmodeled in H. }
  destruct (path_has_slash (path_strip_trailing_slashes p)) eqn:Hsl.
  { destruct (tmp_name (path_strip_trailing_slashes p)) as [n|] eqn:Htn;
      [eapply check_unlinkat_tmp_sound_unmodeled; exact H
      |apply unmodeled_intro]. }
  destruct (path_eqb (path_strip_trailing_slashes p) dot_path) eqn:Hdot.
  { destruct (unlink_rmdir flags); now apply check_ret_only_no_unmodeled in H. }
  destruct (path_eqb (path_strip_trailing_slashes p) dotdot_path) eqn:Hdd.
  { destruct (unlink_rmdir flags); now apply check_ret_only_no_unmodeled in H. }
  destruct (Nat.ltb NAME_MAX (length (path_strip_trailing_slashes p))) eqn:Hnm.
  { apply unmodeled_intro. }
  destruct (fs_under (m_fs m) (path_strip_trailing_slashes p)) eqn:Hun.
  { apply unmodeled_intro. }
  destruct (fs_lookup (m_fs m) (path_strip_trailing_slashes p)) as [data|] eqn:Hfs;
    [|now apply check_ret_only_no_unmodeled in H].
  eapply check_unlink_found_sound_unmodeled. exact H.
Qed.

(** 0 is not an injectable errno, so the removal and the failure
    alternative never both accept the same return. *)
Lemma errno_ret_in_unlinkat_zero :
  errno_ret_in unlinkat_errnos (Z_to_bv 64 0) = false.
Proof.
  apply errno_ret_in_fd; [reflexivity|].
  rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia). lia.
Qed.

Local Lemma check_unlink_found_complete_ok : forall i p c flags eff m m' evs,
  unlink_found_spec p c flags m i m (Ok eff m' evs) ->
  check_unlink_found p c flags eff m = CheckOk m' evs.
Proof.
  intros i p c flags eff m m' evs H.
  unfold unlink_found_spec in H. unfold check_unlink_found. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok;
    [cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (path_trailing_slash p) eqn:Hts; hall Hts; inv_ok;
    [cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (fd_names_path (m_fds m) c) eqn:Hfd; hall Hfd; inv_ok.
  - (* the injectable failure: no state change *)
    unfold check_unlink_result.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - (* the removal itself *)
    unfold check_unlink_result.
    rewrite errno_ret_in_unlinkat_zero, bv_eqb_refl. reflexivity.
Qed.

Local Lemma check_unlink_found_complete_unmodeled : forall i p c flags m eff,
  unlink_found_spec p c flags m i m Unmodeled ->
  check_unlink_found p c flags eff m = CheckUnmodeled.
Proof.
  intros i p c flags m eff H.
  unfold unlink_found_spec in H. unfold check_unlink_found. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok; try discriminate.
  destruct (path_trailing_slash p) eqn:Hts; hall Hts; inv_ok; try discriminate.
  destruct (fd_names_path (m_fds m) c) eqn:Hfd; hall Hfd; inv_ok;
    try discriminate. reflexivity.
Qed.

Local Lemma check_unlinkat_tmp_complete_ok : forall i n p c flags eff m m' evs,
  unlinkat_tmp_spec n p c flags m i m (Ok eff m' evs) ->
  check_unlinkat_tmp n p c flags eff m = CheckOk m' evs.
Proof.
  intros i n p c flags eff m m' evs H.
  unfold unlinkat_tmp_spec in H. unfold check_unlinkat_tmp. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok.
  destruct (Nat.ltb NAME_MAX (length n)) eqn:Hnm; hall Hnm; inv_ok.
  destruct (fs_under (m_fs m) c) eqn:Hun; hall Hun; inv_ok;
    [cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (fs_lookup (m_fs m) c) as [data|] eqn:Hfs; hall Hfs; inv_ok;
    [|cbn; try rewrite bv_eqb_refl; reflexivity].
  now apply check_unlink_found_complete_ok with (i := i).
Qed.

Local Lemma check_unlinkat_tmp_complete_unmodeled :
    forall i n p c flags m eff,
  unlinkat_tmp_spec n p c flags m i m Unmodeled ->
  check_unlinkat_tmp n p c flags eff m = CheckUnmodeled.
Proof.
  intros i n p c flags m eff H.
  unfold unlinkat_tmp_spec in H. unfold check_unlinkat_tmp. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok; [reflexivity|].
  destruct (Nat.ltb NAME_MAX (length n)) eqn:Hnm; hall Hnm; inv_ok;
    [reflexivity|].
  destruct (fs_under (m_fs m) c) eqn:Hun; hall Hun; inv_ok; try discriminate.
  destruct (fs_lookup (m_fs m) c) as [data|] eqn:Hfs; hall Hfs; inv_ok;
    try discriminate.
  now apply check_unlink_found_complete_unmodeled with (i := i).
Qed.

Local Lemma check_unlinkat_body_complete_ok : forall i dirfd pathp flags eff m m' evs,
  unlinkat_body_spec dirfd pathp flags i m i m (Ok eff m' evs) ->
  check_unlinkat_body i dirfd pathp flags eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold unlinkat_body_spec in H. unfold check_unlinkat_body. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (user_read_cstr i m pathp) as [[p| |]| |] eqn:Hp; hall Hp; inv_ok;
    try (cbn; try rewrite bv_eqb_refl; reflexivity).
  destruct (path_eqb p []) eqn:Hpe; hall Hpe; inv_ok;
    [cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; hall Hd; inv_ok.
  cbv zeta in H |- *.
  destruct (path_eqb (path_strip_trailing_slashes p) []) eqn:Hroot;
    hall Hroot; inv_ok;
    [destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok;
     cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (path_has_slash (path_strip_trailing_slashes p)) eqn:Hsl;
    hall Hsl; inv_ok.
  { destruct (tmp_name (path_strip_trailing_slashes p)) as [n|] eqn:Htn;
      hall Htn; inv_ok.
    now apply check_unlinkat_tmp_complete_ok with (i := i). }
  destruct (path_eqb (path_strip_trailing_slashes p) dot_path) eqn:Hdot;
    hall Hdot; inv_ok;
    [destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok;
     cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (path_eqb (path_strip_trailing_slashes p) dotdot_path) eqn:Hdd;
    hall Hdd; inv_ok;
    [destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok;
     cbn; try rewrite bv_eqb_refl; reflexivity|].
  destruct (Nat.ltb NAME_MAX (length (path_strip_trailing_slashes p))) eqn:Hnm;
    hall Hnm; inv_ok.
  destruct (fs_under (m_fs m) (path_strip_trailing_slashes p)) eqn:Hun;
    hall Hun; inv_ok.
  destruct (fs_lookup (m_fs m) (path_strip_trailing_slashes p)) as [data|]
    eqn:Hfs; hall Hfs; inv_ok;
    [|cbn; try rewrite bv_eqb_refl; reflexivity].
  now apply check_unlink_found_complete_ok with (i := i).
Qed.

Local Lemma check_unlinkat_body_complete_unmodeled : forall i dirfd pathp flags m eff,
  unlinkat_body_spec dirfd pathp flags i m i m Unmodeled ->
  check_unlinkat_body i dirfd pathp flags eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  unfold unlinkat_body_spec in H. unfold check_unlinkat_body. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (user_read_cstr i m pathp) as [[p| |]| |] eqn:Hp; hall Hp; inv_ok;
    try discriminate; [|reflexivity].
  destruct (path_eqb p []) eqn:Hpe; hall Hpe; inv_ok; try discriminate.
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; hall Hd; inv_ok;
    try discriminate; [reflexivity|].
  cbv zeta in H |- *.
  destruct (path_eqb (path_strip_trailing_slashes p) []) eqn:Hroot;
    hall Hroot; inv_ok; try discriminate;
    [destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok; discriminate|].
  destruct (path_has_slash (path_strip_trailing_slashes p)) eqn:Hsl;
    hall Hsl; inv_ok; try discriminate.
  { destruct (tmp_name (path_strip_trailing_slashes p)) as [n|] eqn:Htn;
      hall Htn; inv_ok; [|reflexivity].
    now apply check_unlinkat_tmp_complete_unmodeled with (i := i). }
  destruct (path_eqb (path_strip_trailing_slashes p) dot_path) eqn:Hdot;
    hall Hdot; inv_ok; try discriminate;
    [destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok; discriminate|].
  destruct (path_eqb (path_strip_trailing_slashes p) dotdot_path) eqn:Hdd;
    hall Hdd; inv_ok; try discriminate;
    [destruct (unlink_rmdir flags) eqn:Hrm; hall Hrm; inv_ok; discriminate|].
  destruct (Nat.ltb NAME_MAX (length (path_strip_trailing_slashes p))) eqn:Hnm;
    hall Hnm; inv_ok; try discriminate; [reflexivity|].
  destruct (fs_under (m_fs m) (path_strip_trailing_slashes p)) eqn:Hun;
    hall Hun; inv_ok; try discriminate; [reflexivity|].
  destruct (fs_lookup (m_fs m) (path_strip_trailing_slashes p)) as [data|]
    eqn:Hfs; hall Hfs; inv_ok; try discriminate.
  now apply check_unlink_found_complete_unmodeled with (i := i).
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
  destruct (user_read_cstr i m pathp) as [[p| |]| |];
    [ | apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity
      | apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity
      | apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity
      | discriminate ].
  destruct (path_eqb p []);
    [apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); [discriminate|].
  cbv zeta in H.
  destruct (path_eqb (path_strip_trailing_slashes p) []);
    [destruct (unlink_rmdir flags);
     apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity|].
  destruct (path_has_slash (path_strip_trailing_slashes p)).
  { destruct (tmp_name (path_strip_trailing_slashes p)) as [n|];
      [eapply check_unlinkat_tmp_ok_copyins_nil; exact H|discriminate]. }
  destruct (path_eqb (path_strip_trailing_slashes p) dot_path);
    [destruct (unlink_rmdir flags);
     apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity|].
  destruct (path_eqb (path_strip_trailing_slashes p) dotdot_path);
    [destruct (unlink_rmdir flags);
     apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity|].
  destruct (Nat.ltb NAME_MAX (length (path_strip_trailing_slashes p)));
    [discriminate|].
  destruct (fs_under (m_fs m) (path_strip_trailing_slashes p)); [discriminate|].
  destruct (fs_lookup (m_fs m) (path_strip_trailing_slashes p)) as [data|];
    [|apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity].
  eapply check_unlink_found_ok_copyins_nil. exact H.
Qed.

(* ------------------------------------------------------- the four exports

   Each is the body lemma above with the flag arm in front and the
   pathname copy-in threaded, exactly as [Fs.Open]'s four are.  The flag
   arm carries no copy-in: the kernel decides it before [getname()]. *)

Lemma check_unlinkat_sound_ok : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs ->
  unlinkat_spec dirfd pathp flags i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat in H. unfold unlinkat_spec.
  destruct (negb (modeled_unlink_flags flags)) eqn:Hfl; cbv iota in H.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    ul_open. apply pure_ok. }
  cbv zeta in H. apply check_copyins_after_ok_iff in H.
  destruct H as (Hreads & Hbody).
  ul_open. apply record_copyins_clear_ok; [exact Hreads|].
  now apply check_unlinkat_body_sound_ok.
Qed.

Lemma check_unlinkat_sound_unmodeled : forall i dirfd pathp flags eff m,
  check_unlinkat i dirfd pathp flags eff m = CheckUnmodeled ->
  unlinkat_spec dirfd pathp flags i m Unmodeled.
Proof.
  intros i dirfd pathp flags eff m H.
  unfold check_unlinkat in H. unfold unlinkat_spec.
  destruct (negb (modeled_unlink_flags flags)) eqn:Hfl; cbv iota in H;
    [now apply check_ret_only_no_unmodeled in H|].
  cbv zeta in H. apply check_copyins_after_unmodeled in H.
  ul_open_u. apply record_copyins_unmodeled.
  eapply check_unlinkat_body_sound_unmodeled. exact H.
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
  cbv iota in H. apply record_copyins_ok_inv in H.
  destruct H as (core & Hcore & ->).
  apply check_unlinkat_body_complete_ok in Hcore.
  pose proof (check_unlinkat_body_ok_copyins_nil _ _ _ _ _ _ _ _ Hcore) as Hnil.
  cbv zeta. apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
  - cbn [with_copyins eff_copyins]. rewrite Hnil, app_nil_r. reflexivity.
  - destruct core as [ret ws zs us cs copyins].
    cbn in Hnil. subst copyins. exact Hcore.
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
  cbv iota in H. apply record_copyins_unmodeled_inv in H.
  cbv zeta. unfold check_copyins_after.
  rewrite (check_unlinkat_body_complete_unmodeled i dirfd pathp flags m
             (clear_copyins eff) H). reflexivity.
Qed.
