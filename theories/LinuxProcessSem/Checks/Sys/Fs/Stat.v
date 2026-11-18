(** * LinuxProcessSem.Checks.Sys.Fs.Stat — the readlinkat (78), newfstatat (79) and fstat (80) checkers, and their proofs

    Mirrors [Sys/Fs/Stat.v], which answers to Linux [fs/stat.c]: this
    file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

(** readlinkat (78): the [bufsiz] gate, then the pathname, then the
    walk, which never follows the last link.  Mirrors
    [Fs.Stat.readlinkat_spec] branch for branch.

    THE GATE ARM CARRIES NO COPY-IN, because [do_readlinkat] answers it
    before [getname_flags]; every other arm carries the one pathname
    range, as [Open.check_openat] does.  The only write is a found
    link's body ([check_readlink_copy]). *)
Definition check_readlink_copy (i : SyscallInput) (b : path) (buf bufsiz : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let n := readlink_count b bufsiz in
  if negb (access_okb buf (Z.of_nat n)) then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map (in_wmem i) buf (Z_to_bv 64 (Z.of_nat n)) with
    | None => CheckUnmodeled
    | Some _ =>
        match eff with
        | mkEffectU ret ws [] [] [] [] =>
            if bv_eqb ret (Z_to_bv 64 (Z.of_nat n))
               && writes_eqb ws (delivered_writes buf (firstn n (Fs.link_text b)))
            then CheckOk m []
            else CheckReject
        | _ => CheckReject
        end
    end.

Definition check_readlinkat_body (i : SyscallInput) (dirfd pathp buf bufsiz : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | CstrOk p =>
      if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
      else if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
      else
        let '(r, _, _) := Fs.resolve (Fs.WalkFull false false) (m_fs m) (m_cwd m) p in
        match r with
        | Fs.RFound _ (ELink b) => check_readlink_copy i b buf bufsiz eff m
        | Fs.RFound _ _ => check_ret_only eff (errno_ret EINVAL) m []
        | Fs.RMissing _ _ => check_ret_only eff (errno_ret ENOENT) m []
        | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
        | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
        | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
        | Fs.ROutside => CheckUnmodeled
        | Fs.RParent _ _ => CheckUnmodeled
        end
  end.

(** The count test first, outside every wrapper, as the spec has it;
    then the walked body under its pathname ledger, and [getname_flags]'
    own refusals around that ([check_getname_refusals]). *)
Definition check_readlinkat (i : SyscallInput) (dirfd pathp buf bufsiz : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if (sint32 bufsiz <=? 0)%Z
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let reads := [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] in
    check_getname_refusals i pathp eff m
      (check_copyins_after reads eff
         (check_walk_refusals (Fs.WalkFull false false) i pathp (clear_copyins eff) m
            (check_readlinkat_body i dirfd pathp buf bufsiz (clear_copyins eff) m))).

Local Ltac rl_ret_ok :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckOk _ _ |- _ =>
      apply check_ret_only_ok_iff in Hx; destruct Hx as (-> & -> & ->);
      unfold err_ret, ret_only; apply pure_ok
  end.
Local Ltac rl_ret_nu :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckUnmodeled |- _ =>
      now apply check_ret_only_no_unmodeled in Hx
  end.
Local Ltac rl_ret_co :=
  unfold err_ret, ret_only, pure in *; inv_ok;
  apply check_ret_only_ok_iff; now repeat split.
Local Ltac rl_ret_cnil :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckOk _ _ |- _ =>
      apply check_ret_only_ok_iff in Hx; destruct Hx as (-> & _ & _);
      reflexivity
  end.

Local Lemma check_readlink_copy_sound_ok : forall i b buf bufsiz eff m m' evs,
  check_readlink_copy i b buf bufsiz eff m = CheckOk m' evs ->
  readlink_copy_spec i b buf bufsiz i m (Ok eff m' evs).
Proof.
  intros i b buf bufsiz eff m m' evs H.
  unfold check_readlink_copy in H. unfold readlink_copy_spec. cbv zeta in H |- *.
  destruct (negb (access_okb buf (Z.of_nat (readlink_count b bufsiz))));
    cbv iota in H |- *; [rl_ret_ok|].
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (Z.of_nat (readlink_count b bufsiz))));
    cbv iota in H |- *; [|discriminate].
  destruct eff as [ret ws zs us cs cis]; destruct zs; destruct us; destruct cs;
    destruct cis; try discriminate.
  match type of H with
  | context [bv_eqb ret ?x] => destruct (bv_eqb ret x) eqn:Hr; cbn [andb] in H;
                                [|discriminate]
  end.
  match type of H with
  | context [writes_eqb ws ?y] => destruct (writes_eqb ws y) eqn:Hws; [|discriminate]
  end.
  inversion H; clear H; subst.
  apply bv_eqb_eq in Hr; subst ret. apply writes_eqb_eq in Hws; subst ws.
  apply pure_ok.
Qed.

Local Lemma check_readlink_copy_sound_unmodeled : forall i b buf bufsiz eff m,
  check_readlink_copy i b buf bufsiz eff m = CheckUnmodeled ->
  readlink_copy_spec i b buf bufsiz i m Unmodeled.
Proof.
  intros i b buf bufsiz eff m H.
  unfold check_readlink_copy in H. unfold readlink_copy_spec. cbv zeta in H |- *.
  destruct (negb (access_okb buf (Z.of_nat (readlink_count b bufsiz))));
    cbv iota in H |- *; [rl_ret_nu|].
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (Z.of_nat (readlink_count b bufsiz))));
    cbv iota in H |- *; [|apply unmodeled_intro].
  exfalso. destruct eff as [ret ws zs us cs cis]; destruct zs; destruct us;
    destruct cs; destruct cis; try discriminate.
  match type of H with
  | context [if ?c then _ else _] => destruct c; discriminate
  end.
Qed.

Local Lemma check_readlink_copy_complete_ok : forall i b buf bufsiz eff m m' evs,
  readlink_copy_spec i b buf bufsiz i m (Ok eff m' evs) ->
  check_readlink_copy i b buf bufsiz eff m = CheckOk m' evs
  /\ eff_copyins eff = [].
Proof.
  intros i b buf bufsiz eff m m' evs H.
  unfold readlink_copy_spec in H. unfold check_readlink_copy. cbv zeta in H |- *.
  destruct (negb (access_okb buf (Z.of_nat (readlink_count b bufsiz))));
    cbv iota in H |- *;
    [split; [rl_ret_co|unfold err_ret, ret_only, pure in *; inv_ok; reflexivity]|].
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (Z.of_nat (readlink_count b bufsiz))));
    cbv iota in H |- *; [|unfold unmodeled in H; inv_ok].
  unfold pure in H. inv_ok. split; [|reflexivity].
  cbv beta iota. rewrite bv_eqb_refl.
  rewrite (proj2 (writes_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Local Lemma check_readlink_copy_complete_unmodeled : forall i b buf bufsiz eff m,
  readlink_copy_spec i b buf bufsiz i m Unmodeled ->
  check_readlink_copy i b buf bufsiz eff m = CheckUnmodeled.
Proof.
  intros i b buf bufsiz eff m H.
  unfold readlink_copy_spec in H. unfold check_readlink_copy. cbv zeta in H |- *.
  destruct (negb (access_okb buf (Z.of_nat (readlink_count b bufsiz))));
    cbv iota in H |- *; [sys_unfold; inv_ok|].
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (Z.of_nat (readlink_count b bufsiz))));
    cbv iota in H |- *; [unfold pure in H; discriminate H|reflexivity].
Qed.

Local Lemma check_readlinkat_body_sound_ok :
  forall i dirfd pathp buf bufsiz eff m m' evs,
  check_readlinkat_body i dirfd pathp buf bufsiz eff m = CheckOk m' evs ->
  readlinkat_body_spec dirfd pathp buf bufsiz i m i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp buf bufsiz eff m m' evs H.
  unfold check_readlinkat_body in H. unfold readlinkat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try rl_ret_ok.
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [discriminate|].
  destruct (path_eqb p []); cbv iota in H |- *; [rl_ret_ok|].
  destruct (Fs.resolve (Fs.WalkFull false false) (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try rl_ret_ok; try discriminate.
  destruct e as [ino| |dk|lb]; cbv iota in H |- *;
    [rl_ret_ok|rl_ret_ok|rl_ret_ok|now apply check_readlink_copy_sound_ok].
Qed.

Local Lemma check_readlinkat_body_sound_unmodeled :
  forall i dirfd pathp buf bufsiz eff m,
  check_readlinkat_body i dirfd pathp buf bufsiz eff m = CheckUnmodeled ->
  readlinkat_body_spec dirfd pathp buf bufsiz i m i m Unmodeled.
Proof.
  intros i dirfd pathp buf bufsiz eff m H.
  unfold check_readlinkat_body in H. unfold readlinkat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try rl_ret_nu.
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [apply unmodeled_intro|].
  destruct (path_eqb p []); cbv iota in H |- *; [rl_ret_nu|].
  destruct (Fs.resolve (Fs.WalkFull false false) (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try rl_ret_nu; try apply unmodeled_intro.
  destruct e as [ino| |dk|lb]; cbv iota in H |- *;
    [rl_ret_nu|rl_ret_nu|rl_ret_nu
    |eapply check_readlink_copy_sound_unmodeled; exact H].
Qed.

Local Lemma check_readlinkat_body_complete_ok :
  forall i dirfd pathp buf bufsiz core m m' evs,
  readlinkat_body_spec dirfd pathp buf bufsiz i m i m (Ok core m' evs) ->
  check_readlinkat_body i dirfd pathp buf bufsiz core m = CheckOk m' evs
  /\ eff_copyins core = [].
Proof.
  intros i dirfd pathp buf bufsiz core m m' evs H.
  unfold check_readlinkat_body. unfold readlinkat_body_spec in H.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try (split; [rl_ret_co
                |unfold err_ret, ret_only, pure in *; inv_ok; reflexivity]).
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [unfold unmodeled in H; inv_ok|].
  destruct (path_eqb p []); cbv iota in H |- *;
    [split; [rl_ret_co
            |unfold err_ret, ret_only, pure in *; inv_ok; reflexivity]|].
  destruct (Fs.resolve (Fs.WalkFull false false) (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (split; [rl_ret_co
                |unfold err_ret, ret_only, pure in *; inv_ok; reflexivity]);
    try (unfold unmodeled in H; inv_ok; fail).
  destruct e as [ino| |dk|lb]; cbv iota in H |- *;
    try (split; [rl_ret_co
                |unfold err_ret, ret_only, pure in *; inv_ok; reflexivity]).
  now apply check_readlink_copy_complete_ok.
Qed.

Local Lemma check_readlinkat_body_complete_unmodeled :
  forall i dirfd pathp buf bufsiz m eff,
  readlinkat_body_spec dirfd pathp buf bufsiz i m i m Unmodeled ->
  check_readlinkat_body i dirfd pathp buf bufsiz eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp buf bufsiz m eff H.
  unfold check_readlinkat_body. unfold readlinkat_body_spec in H.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail).
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [reflexivity|].
  destruct (path_eqb p []); cbv iota in H |- *; [sys_unfold; inv_ok; fail|].
  destruct (Fs.resolve (Fs.WalkFull false false) (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail); try reflexivity.
  destruct e as [ino| |dk|lb]; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail).
  now apply check_readlink_copy_complete_unmodeled.
Qed.

(** The body with [check_walk_refusals] around it, from the body's four
    and [Checks.Sys.Prelude]'s section lemmas. *)
Local Lemma check_readlinkat_walked_sound_ok :
  forall i dirfd pathp buf bufsiz m eff m' evs,
  check_walk_refusals (Fs.WalkFull false false) i pathp eff m
    (check_readlinkat_body i dirfd pathp buf bufsiz eff m) = CheckOk m' evs ->
  walk_refusals (Fs.WalkFull false false) pathp
    (readlinkat_body_spec dirfd pathp buf bufsiz i m) i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp buf bufsiz m.
  apply (check_walk_refusals_sound_ok (Fs.WalkFull false false) _
           (fun e => check_readlinkat_body i dirfd pathp buf bufsiz e m)).
  - intros. eapply check_readlinkat_body_sound_ok. eassumption.
  - intros. eapply check_readlinkat_body_sound_unmodeled. eassumption.
  - intros e m1 evs1 Hs.
    exact (proj1 (check_readlinkat_body_complete_ok _ _ _ _ _ _ _ _ _ Hs)).
  - intros. eapply check_readlinkat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_readlinkat_walked_sound_unmodeled :
  forall i dirfd pathp buf bufsiz m eff,
  check_walk_refusals (Fs.WalkFull false false) i pathp eff m
    (check_readlinkat_body i dirfd pathp buf bufsiz eff m) = CheckUnmodeled ->
  walk_refusals (Fs.WalkFull false false) pathp
    (readlinkat_body_spec dirfd pathp buf bufsiz i m) i m Unmodeled.
Proof.
  intros i dirfd pathp buf bufsiz m.
  apply (check_walk_refusals_sound_unmodeled (Fs.WalkFull false false) _
           (fun e => check_readlinkat_body i dirfd pathp buf bufsiz e m)).
  - intros. eapply check_readlinkat_body_sound_ok. eassumption.
  - intros. eapply check_readlinkat_body_sound_unmodeled. eassumption.
  - intros e m1 evs1 Hs.
    exact (proj1 (check_readlinkat_body_complete_ok _ _ _ _ _ _ _ _ _ Hs)).
  - intros. eapply check_readlinkat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_readlinkat_walked_complete_ok :
  forall i dirfd pathp buf bufsiz core m m' evs,
  walk_refusals (Fs.WalkFull false false) pathp
    (readlinkat_body_spec dirfd pathp buf bufsiz i m) i m (Ok core m' evs) ->
  check_walk_refusals (Fs.WalkFull false false) i pathp core m
    (check_readlinkat_body i dirfd pathp buf bufsiz core m) = CheckOk m' evs
  /\ eff_copyins core = [].
Proof.
  intros i dirfd pathp buf bufsiz core m m' evs H.
  assert (Hc : check_walk_refusals (Fs.WalkFull false false) i pathp core m
                 (check_readlinkat_body i dirfd pathp buf bufsiz core m)
               = CheckOk m' evs).
  { revert core m' evs H.
    apply (check_walk_refusals_complete_ok (Fs.WalkFull false false) _
             (fun e => check_readlinkat_body i dirfd pathp buf bufsiz e m)).
    - intros. eapply check_readlinkat_body_sound_ok. eassumption.
    - intros. eapply check_readlinkat_body_sound_unmodeled. eassumption.
    - intros e m1 evs1 Hs.
      exact (proj1 (check_readlinkat_body_complete_ok _ _ _ _ _ _ _ _ _ Hs)).
    - intros. eapply check_readlinkat_body_complete_unmodeled. eassumption. }
  split; [exact Hc|].
  eapply check_walk_refusals_copyins_nil; [|exact Hc].
  intros m1 evs1 Hb.
  exact (proj2 (check_readlinkat_body_complete_ok _ _ _ _ _ _ _ _ _
                  (check_readlinkat_body_sound_ok _ _ _ _ _ _ _ _ _ Hb))).
Qed.

Local Lemma check_readlinkat_walked_complete_unmodeled :
  forall i dirfd pathp buf bufsiz m eff,
  walk_refusals (Fs.WalkFull false false) pathp
    (readlinkat_body_spec dirfd pathp buf bufsiz i m) i m Unmodeled ->
  check_walk_refusals (Fs.WalkFull false false) i pathp eff m
    (check_readlinkat_body i dirfd pathp buf bufsiz eff m) = CheckUnmodeled.
Proof.
  intros i dirfd pathp buf bufsiz m.
  apply (check_walk_refusals_complete_unmodeled (Fs.WalkFull false false) _
           (fun e => check_readlinkat_body i dirfd pathp buf bufsiz e m)).
  - intros. eapply check_readlinkat_body_sound_ok. eassumption.
  - intros. eapply check_readlinkat_body_sound_unmodeled. eassumption.
  - intros e m1 evs1 Hs.
    exact (proj1 (check_readlinkat_body_complete_ok _ _ _ _ _ _ _ _ _ Hs)).
  - intros. eapply check_readlinkat_body_complete_unmodeled. eassumption.
Qed.

(** The walked body under its pathname ledger: the part
    [getname_flags]' own refusals wrap.  The four are stated over
    [check_readlinkat]'s own expression, not over a name for it: a
    name the kernel has to unfold against that expression cost about
    three minutes per [Qed]. *)
Local Lemma check_readlinkat_fetched_sound_ok :
  forall i dirfd pathp buf bufsiz m eff m' evs,
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals (Fs.WalkFull false false) i pathp (clear_copyins eff) m
       (check_readlinkat_body i dirfd pathp buf bufsiz (clear_copyins eff) m))
  = CheckOk m' evs ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals (Fs.WalkFull false false) pathp
       (readlinkat_body_spec dirfd pathp buf bufsiz i m)) i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp buf bufsiz m eff m' evs H.
  apply check_copyins_after_ok_iff in H as (Hreads & Hbody).
  apply record_copyins_clear_ok; [exact Hreads|].
  now apply check_readlinkat_walked_sound_ok.
Qed.

Local Lemma check_readlinkat_fetched_sound_unmodeled :
  forall i dirfd pathp buf bufsiz m eff,
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals (Fs.WalkFull false false) i pathp (clear_copyins eff) m
       (check_readlinkat_body i dirfd pathp buf bufsiz (clear_copyins eff) m))
  = CheckUnmodeled ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals (Fs.WalkFull false false) pathp
       (readlinkat_body_spec dirfd pathp buf bufsiz i m)) i m Unmodeled.
Proof.
  intros i dirfd pathp buf bufsiz m eff H.
  apply check_copyins_after_unmodeled in H.
  apply record_copyins_unmodeled.
  now apply check_readlinkat_walked_sound_unmodeled with (eff := clear_copyins eff).
Qed.

Local Lemma check_readlinkat_fetched_complete_ok :
  forall i dirfd pathp buf bufsiz m eff m' evs,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals (Fs.WalkFull false false) pathp
       (readlinkat_body_spec dirfd pathp buf bufsiz i m)) i m (Ok eff m' evs) ->
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals (Fs.WalkFull false false) i pathp (clear_copyins eff) m
       (check_readlinkat_body i dirfd pathp buf bufsiz (clear_copyins eff) m))
  = CheckOk m' evs.
Proof.
  intros i dirfd pathp buf bufsiz m eff m' evs H.
  apply record_copyins_ok_inv in H. destruct H as (core & H & ->).
  apply check_readlinkat_walked_complete_ok in H as (Hchecked & Hcopyins).
  apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
  - cbn [with_copyins eff_copyins]. rewrite Hcopyins, app_nil_r. reflexivity.
  - destruct core as [ret ws zs us cs copyins].
    cbn in Hcopyins. subst copyins. exact Hchecked.
Qed.

Local Lemma check_readlinkat_fetched_complete_unmodeled :
  forall i dirfd pathp buf bufsiz m eff,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals (Fs.WalkFull false false) pathp
       (readlinkat_body_spec dirfd pathp buf bufsiz i m)) i m Unmodeled ->
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals (Fs.WalkFull false false) i pathp (clear_copyins eff) m
       (check_readlinkat_body i dirfd pathp buf bufsiz (clear_copyins eff) m))
  = CheckUnmodeled.
Proof.
  intros i dirfd pathp buf bufsiz m eff H.
  apply record_copyins_unmodeled_inv in H.
  unfold check_copyins_after.
  rewrite (check_readlinkat_walked_complete_unmodeled i dirfd pathp buf bufsiz m
             (clear_copyins eff) H).
  reflexivity.
Qed.

Lemma check_readlinkat_sound_ok : forall i dirfd pathp buf bufsiz eff m m' evs,
  check_readlinkat i dirfd pathp buf bufsiz eff m = CheckOk m' evs ->
  readlinkat_spec dirfd pathp buf bufsiz i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp buf bufsiz eff m m' evs H.
  unfold check_readlinkat in H. unfold readlinkat_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
  destruct ((sint32 bufsiz <=? 0)%Z); cbv iota; [rl_ret_ok|].
  cbv zeta in H.
  exact (check_getname_refusals_sound_ok pathp _ _ i m
           (check_readlinkat_fetched_sound_ok i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_sound_unmodeled i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_complete_ok i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_complete_unmodeled i dirfd pathp buf bufsiz m)
           eff m' evs H).
Qed.

Lemma check_readlinkat_sound_unmodeled :
  forall i dirfd pathp buf bufsiz eff m,
  check_readlinkat i dirfd pathp buf bufsiz eff m = CheckUnmodeled ->
  readlinkat_spec dirfd pathp buf bufsiz i m Unmodeled.
Proof.
  intros i dirfd pathp buf bufsiz eff m H.
  unfold check_readlinkat in H. unfold readlinkat_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
  destruct ((sint32 bufsiz <=? 0)%Z); cbv iota; [rl_ret_nu|].
  cbv zeta in H.
  exact (check_getname_refusals_sound_unmodeled pathp _ _ i m
           (check_readlinkat_fetched_sound_ok i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_sound_unmodeled i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_complete_ok i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_complete_unmodeled i dirfd pathp buf bufsiz m)
           eff H).
Qed.

Lemma check_readlinkat_complete_ok :
  forall i dirfd pathp buf bufsiz eff m m' evs,
  readlinkat_spec dirfd pathp buf bufsiz i m (Ok eff m' evs) ->
  check_readlinkat i dirfd pathp buf bufsiz eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp buf bufsiz eff m m' evs H.
  unfold readlinkat_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta iota in H.
  unfold check_readlinkat.
  destruct ((sint32 bufsiz <=? 0)%Z); cbv iota in H |- *;
    [rl_ret_co|].
  cbv zeta.
  exact (check_getname_refusals_complete_ok pathp _ _ i m
           (check_readlinkat_fetched_sound_ok i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_sound_unmodeled i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_complete_ok i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_complete_unmodeled i dirfd pathp buf bufsiz m)
           eff m' evs H).
Qed.

Lemma check_readlinkat_complete_unmodeled :
  forall i dirfd pathp buf bufsiz m eff,
  readlinkat_spec dirfd pathp buf bufsiz i m Unmodeled ->
  check_readlinkat i dirfd pathp buf bufsiz eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp buf bufsiz m eff H.
  unfold readlinkat_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply get_model_bind_unmodeled_inv in H. cbv beta iota in H.
  unfold check_readlinkat.
  destruct ((sint32 bufsiz <=? 0)%Z); cbv iota in H |- *;
    [sys_unfold; inv_ok|].
  cbv zeta.
  exact (check_getname_refusals_complete_unmodeled pathp _ _ i m
           (check_readlinkat_fetched_sound_ok i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_sound_unmodeled i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_complete_ok i dirfd pathp buf bufsiz m)
           (check_readlinkat_fetched_complete_unmodeled i dirfd pathp buf bufsiz m)
           eff H).
Qed.

(** The four inversions the completeness lemmas need, to strip
    [newfstatat_spec]'s [input] bind and its [record_copyins] wrapper.
    They are mirrored from [Checks.Sys.Fs.Open], where the same four are
    [Local], rather than hoisted into [Checks.Sys.Prelude]: the two
    checkers are kept arm-for-arm side by side on purpose (see the
    SHARED WITH paragraph on [Stat.newfstatat_spec]), and the shared
    combinator is worth extracting when [readlinkat] becomes the third
    call site, not before. *)
Local Lemma input_bind_ok_inv {A : Type} : forall (k : SyscallInput -> Sys A)
    i m x m' evs,
  bind input k i m (Ok x m' evs) -> k i i m (Ok x m' evs).
Proof.
  intros k i m x m' evs H.
  unfold bind, input in H. cbv beta iota in H.
  destruct H as (i' & m1 & evs1 & evs2 & Hinput & Hk & Hevs).
  inversion Hinput; clear Hinput; subst.
  exact Hk.
Qed.

Local Lemma input_bind_unmodeled_inv {A : Type} :
    forall (k : SyscallInput -> Sys A) i m,
  bind input k i m Unmodeled -> k i i m Unmodeled.
Proof.
  intros k i m H. unfold bind, input in H. cbv beta iota in H.
  destruct H as [Hinput | (i' & m1 & evs1 & Hinput & Hk)].
  - discriminate Hinput.
  - inversion Hinput; clear Hinput; subst. exact Hk.
Qed.

Local Lemma bind_get_model_ok_inv {A : Type} : forall (k : Model -> Sys A)
    i m x m' evs,
  bind get_model k i m (Ok x m' evs) -> k m i m (Ok x m' evs).
Proof.
  intros k i m x m' evs H.
  unfold bind, get_model in H. cbv beta iota in H.
  destruct H as (m1 & m2 & evs1 & evs2 & Hget & Hk & Hevs).
  inversion Hget; clear Hget; subst. exact Hk.
Qed.

Local Lemma bind_get_model_unmodeled_inv {A : Type} :
    forall (k : Model -> Sys A) i m,
  bind get_model k i m Unmodeled -> k m i m Unmodeled.
Proof.
  intros k i m H. unfold bind, get_model in H. cbv beta iota in H.
  destruct H as [Hget | (m1 & m2 & evs1 & Hget & Hk)].
  - discriminate Hget.
  - inversion Hget; clear Hget; subst. exact Hk.
Qed.

Local Lemma record_copyins_ok_inv : forall reads spec i m eff m' evs,
  record_copyins reads spec i m (Ok eff m' evs) ->
  exists core,
    spec i m (Ok core m' evs) /\
    eff = with_copyins (reads ++ eff_copyins core) core.
Proof.
  intros reads spec i m eff m' evs H.
  unfold record_copyins, bind, pure in H. cbv beta iota in H.
  destruct H as (core & m1 & evs1 & evs2 & Hcore & Hpure & Hevs).
  inversion Hpure; clear Hpure; subst.
  exists core. split; [rewrite app_nil_r; exact Hcore|reflexivity].
Qed.

Local Lemma record_copyins_unmodeled_inv : forall reads spec i m,
  record_copyins reads spec i m Unmodeled -> spec i m Unmodeled.
Proof.
  intros reads spec i m H. unfold record_copyins, bind, pure in H.
  cbv beta iota in H.
  destruct H as [Hcore | (core & m1 & evs1 & Hcore & Hpure)].
  - exact Hcore.
  - discriminate Hpure.
Qed.

(** The delivering half of [Stat.fstat_file_spec] and its twins,
    mirroring their [choose] arm for arm.  The effect must be ONE
    128-byte write at [statbuf] returning 0 and nothing else — no zero
    range, no unmap, no symbolic copy, and an EMPTY copy-in ledger,
    because [fstat] takes its descriptor in a register and reads no user
    byte at all.  The bytes themselves are then judged by [ok], and
    against [held], the pinned bytes whose stable members they must
    repeat when there is a pin.  [post] is the model the delivery leaves,
    as a function of the bytes.

    THE PIN IS INSTALLED THROUGH [post] on the branch that had none,
    exactly as [Checks.Sys.Kernel.Sys]'s [check_uname_copy] installs the
    UTS name: the bytes are the KERNEL's, so the model records what it
    was shown rather than reconstructing it. *)
Definition check_fstat_deliver_gen (ok : list byte -> bool) (statbuf : word)
    (held : option (list byte)) (post : list byte -> Model) (eff : SyscallEffect)
    : check_result :=
  match eff with
  | mkEffectU r [(a, bs)] [] [] [] [] =>
      if negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf)%bool then CheckReject
      else if negb (stat_buf_wf bs && ok bs)%bool then CheckReject
      else match held with
           | Some b0 => if stat_stable_eqb bs b0 then CheckOk (post bs) [] else CheckReject
           | None => CheckOk (post bs) []
           end
  | _ => CheckReject
  end.

(** What a regular file's [struct stat] must carry beside
    [Uapi.stat_buf_wf], in [Stat.fstat_file_spec]'s [choose] order:
    S_IFREG, the contents' length [n] and the link count [l]. *)
Definition stat_reg_ok (n l : nat) (bs : list byte) : bool :=
  (stat_is_reg bs && stat_size_ok n bs && stat_nlink_ok l bs)%bool.

(** What a folder's must carry: S_IFDIR and the link count of the rule
    the pin chose ([Stat.dir_nlink_ok]). *)
Definition stat_dir_ok (d : Fs.DirLinks) (r : option DirRule) (bs : list byte)
    : bool :=
  (stat_is_dir bs && dir_nlink_ok d r bs)%bool.

Lemma check_fstat_deliver_gen_no_unmodeled : forall ok statbuf held post eff,
  check_fstat_deliver_gen ok statbuf held post eff <> CheckUnmodeled.
Proof.
  intros ok statbuf held post [r ws zs us cs copyins].
  unfold check_fstat_deliver_gen.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf)%bool);
    [discriminate|].
  destruct (negb (stat_buf_wf bs && ok bs)%bool); [discriminate|].
  destruct held as [b0|]; [destruct (stat_stable_eqb bs b0)|]; discriminate.
Qed.

(** What a [CheckOk] out of the delivery tells you: the effect is one
    128-byte write of a well-formed [struct stat] at [statbuf] returning
    0, it repeats the held bytes' stable members, and the model is
    [post] of the bytes. *)
Lemma check_fstat_deliver_gen_ok : forall ok statbuf held post eff m' evs,
  check_fstat_deliver_gen ok statbuf held post eff = CheckOk m' evs ->
  exists bs, eff = mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []
             /\ evs = []
             /\ stat_buf_wf bs = true
             /\ ok bs = true
             /\ (forall b0, held = Some b0 -> stat_stable_eqb bs b0 = true)
             /\ m' = post bs.
Proof.
  intros ok statbuf held post [r ws zs us cs copyins] m' evs H.
  unfold check_fstat_deliver_gen in H.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf)%bool) eqn:HG;
    [discriminate|].
  apply Bool.negb_false_iff in HG. apply andb_true_iff in HG as [HR HA].
  apply bv_eqb_eq in HR; subst r. apply bv_eqb_eq in HA; subst a.
  destruct (negb (stat_buf_wf bs && ok bs)%bool) eqn:HW;
    [discriminate|].
  apply Bool.negb_false_iff in HW. apply andb_true_iff in HW as [HWF HOK].
  exists bs. destruct held as [b0|].
  - destruct (stat_stable_eqb bs b0) eqn:HS; [|discriminate].
    inversion H; clear H; subst.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HWF|].
    split; [exact HOK|]. split; [|reflexivity].
    intros b1 Hb1. inversion Hb1; subst b1. exact HS.
  - inversion H; clear H; subst.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HWF|].
    split; [exact HOK|]. split; [|reflexivity].
    intros b1 Hb1. discriminate Hb1.
Qed.

(** The file arms of [Stat.fstat_spec] and the [Fs.EFile] row of
    [newfstatat], branch for branch with [Stat.fstat_file_spec]: a
    partially writable destination declines, [access_ok]'s refusal is
    -EFAULT, a pin no S_IFREG delivery can repeat declines, and the rest
    is the delivery above under the inode's pin, which leaves
    [Stat.file_pin_after]'s model on a pinned file. *)
Definition check_fstat_file (i : SyscallInput) (ino : Fs.ino) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb statbuf STAT_SIZE)
  then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => CheckUnmodeled
    | Some _ =>
        match statpin_lookup (m_statpins m) (IdIno ino) with
        | Some sp =>
            if negb (stat_buf_wf (sp_bytes sp) && stat_is_reg (sp_bytes sp))%bool
            then CheckUnmodeled
            else check_fstat_deliver_gen
                   (stat_reg_ok (length (Fs.fs_ino_data (m_fs m) ino))
                                (Fs.fs_ino_nlink (m_fs m) ino))
                   statbuf (Some (sp_bytes sp)) (fun bs => file_pin_after ino sp bs m) eff
        | None =>
            check_fstat_deliver_gen
              (stat_reg_ok (length (Fs.fs_ino_data (m_fs m) ino))
                           (Fs.fs_ino_nlink (m_fs m) ino))
              statbuf None (fun bs => with_statpin (IdIno ino) (mkStatPin bs None) m) eff
        end
    end.

Lemma check_fstat_file_sound_ok : forall i ino statbuf eff m m' evs,
  check_fstat_file i ino statbuf eff m = CheckOk m' evs ->
  fstat_file_spec ino statbuf i m (Ok eff m' evs).
Proof.
  intros i ino statbuf eff m m' evs H.
  unfold check_fstat_file in H. unfold fstat_file_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|discriminate].
    cbv iota.
    destruct (statpin_lookup (m_statpins m) (IdIno ino)) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_reg (sp_bytes sp))%bool)
        eqn:Hb0; [discriminate|].
      cbv iota.
      apply check_fstat_deliver_gen_ok in H as (bs & -> & -> & HWF & HOK & HS & ->).
      specialize (HS _ eq_refl).
      unfold stat_reg_ok in HOK. apply andb_true_iff in HOK as [HOK HNL].
      apply andb_true_iff in HOK as [HREG HSZ].
      eapply bind_ok0; [apply (choose_ok _ bs); repeat split; eassumption|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + apply check_fstat_deliver_gen_ok in H as (bs & -> & -> & HWF & HOK & _ & ->).
      unfold stat_reg_ok in HOK. apply andb_true_iff in HOK as [HOK HNL].
      apply andb_true_iff in HOK as [HREG HSZ].
      eapply bind_ok0; [apply (choose_ok _ bs); repeat split; eassumption|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_fstat_file_sound_unmodeled : forall i ino statbuf eff m,
  check_fstat_file i ino statbuf eff m = CheckUnmodeled ->
  fstat_file_spec ino statbuf i m Unmodeled.
Proof.
  intros i ino statbuf eff m H.
  unfold check_fstat_file in H. unfold fstat_file_spec.
  eapply bind_unmodeled2; [apply input_ok|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [cbv iota|cbv iota; apply unmodeled_intro].
    destruct (statpin_lookup (m_statpins m) (IdIno ino)) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_reg (sp_bytes sp))%bool)
        eqn:Hb0; [cbv iota; apply unmodeled_intro|].
      now apply check_fstat_deliver_gen_no_unmodeled in H.
    + now apply check_fstat_deliver_gen_no_unmodeled in H.
Qed.

Lemma check_fstat_file_complete_ok : forall i ino statbuf eff m m' evs,
  fstat_file_spec ino statbuf i m (Ok eff m' evs) ->
  check_fstat_file i ino statbuf eff m = CheckOk m' evs.
Proof.
  intros i ino statbuf eff m m' evs H.
  unfold fstat_file_spec in H. unfold check_fstat_file.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - sys_unfold; inv_ok; hall Ha; inv_ok.
    apply check_ret_only_ok_iff. now repeat split.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|sys_unfold; inv_ok; hall Ha; hall Hw; inv_ok].
    destruct (statpin_lookup (m_statpins m) (IdIno ino)) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_reg (sp_bytes sp))%bool)
        eqn:Hb0;
        [sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok|].
      sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok.
      unfold check_fstat_deliver_gen, stat_reg_ok.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : stat_is_reg ?b = true,
        H4 : stat_size_ok _ ?b = true, H5 : stat_nlink_ok _ ?b = true,
        H3 : stat_stable_eqb ?b _ = true |- _ =>
          rewrite H1, H2, H4, H5; cbn [andb negb]; rewrite H3
      end.
      reflexivity.
    + sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; inv_ok.
      unfold check_fstat_deliver_gen, stat_reg_ok.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : stat_is_reg ?b = true,
        H4 : stat_size_ok _ ?b = true, H5 : stat_nlink_ok _ ?b = true |- _ =>
          rewrite H1, H2, H4, H5
      end.
      cbn [andb negb]. reflexivity.
Qed.

Lemma check_fstat_file_complete_unmodeled : forall i ino statbuf m eff,
  fstat_file_spec ino statbuf i m Unmodeled ->
  check_fstat_file i ino statbuf eff m = CheckUnmodeled.
Proof.
  intros i ino statbuf m eff H.
  unfold fstat_file_spec in H. unfold check_fstat_file.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - exfalso. sys_unfold; inv_ok; hall Ha; inv_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|reflexivity].
    destruct (statpin_lookup (m_statpins m) (IdIno ino)) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_reg (sp_bytes sp))%bool)
        eqn:Hb0; [reflexivity|].
      exfalso. sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok.
    + exfalso. sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; inv_ok.
Qed.

(** The pinned-identity arm, branch for branch with
    [Stat.fstat_pinned_spec]: the identity's pin checked against both
    predicates, and the delivery judged under [ok].  The character
    devices ([State.IdDev] of the node's key) and a link the walk did
    not follow ([State.IdLink]) are its instances, as the spec's are. *)
Definition check_fstat_pinned (id : StatId) (ok : list byte -> bool)
    (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb statbuf STAT_SIZE)
  then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => CheckUnmodeled
    | Some _ =>
        match statpin_lookup (m_statpins m) id with
        | Some sp =>
            if negb (stat_buf_wf (sp_bytes sp) && ok (sp_bytes sp))%bool then CheckUnmodeled
            else check_fstat_deliver_gen ok statbuf (Some (sp_bytes sp)) (fun _ => m) eff
        | None =>
            check_fstat_deliver_gen ok statbuf None
              (fun bs => with_statpin id (mkStatPin bs None) m) eff
        end
    end.

Lemma check_fstat_pinned_sound_ok : forall id ok i statbuf eff m m' evs,
  check_fstat_pinned id ok i statbuf eff m = CheckOk m' evs ->
  fstat_pinned_spec id ok statbuf i m (Ok eff m' evs).
Proof.
  intros id ok i statbuf eff m m' evs H.
  unfold check_fstat_pinned in H. unfold fstat_pinned_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|discriminate].
    cbv iota.
    destruct (statpin_lookup (m_statpins m) id) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && ok (sp_bytes sp))%bool) eqn:Hb0;
        [discriminate|].
      cbv iota.
      apply check_fstat_deliver_gen_ok in H as (bs & -> & -> & HWF & HOK & HS & ->).
      specialize (HS _ eq_refl).
      eapply bind_ok0; [apply (choose_ok _ bs); repeat split; eassumption|].
      apply pure_ok.
    + apply check_fstat_deliver_gen_ok in H as (bs & -> & -> & HWF & HOK & _ & ->).
      eapply bind_ok0; [apply (choose_ok _ bs); split; eassumption|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_fstat_pinned_sound_unmodeled : forall id ok i statbuf eff m,
  check_fstat_pinned id ok i statbuf eff m = CheckUnmodeled ->
  fstat_pinned_spec id ok statbuf i m Unmodeled.
Proof.
  intros id ok i statbuf eff m H.
  unfold check_fstat_pinned in H. unfold fstat_pinned_spec.
  eapply bind_unmodeled2; [apply input_ok|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [cbv iota|cbv iota; apply unmodeled_intro].
    destruct (statpin_lookup (m_statpins m) id) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && ok (sp_bytes sp))%bool) eqn:Hb0;
        [cbv iota; apply unmodeled_intro|].
      now apply check_fstat_deliver_gen_no_unmodeled in H.
    + now apply check_fstat_deliver_gen_no_unmodeled in H.
Qed.

Lemma check_fstat_pinned_complete_ok : forall id ok i statbuf eff m m' evs,
  fstat_pinned_spec id ok statbuf i m (Ok eff m' evs) ->
  check_fstat_pinned id ok i statbuf eff m = CheckOk m' evs.
Proof.
  intros id ok i statbuf eff m m' evs H.
  unfold fstat_pinned_spec in H. unfold check_fstat_pinned.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - sys_unfold; inv_ok; hall Ha; inv_ok.
    apply check_ret_only_ok_iff. now repeat split.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|sys_unfold; inv_ok; hall Ha; hall Hw; inv_ok].
    destruct (statpin_lookup (m_statpins m) id) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && ok (sp_bytes sp))%bool) eqn:Hb0;
        [sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok|].
      sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok.
      unfold check_fstat_deliver_gen.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : ok ?b = true,
        H3 : stat_stable_eqb ?b _ = true |- _ =>
          rewrite H1, H2; cbn [andb negb]; rewrite H3
      end.
      reflexivity.
    + sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; inv_ok.
      unfold check_fstat_deliver_gen.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : ok ?b = true |- _ =>
          rewrite H1, H2
      end.
      cbn [andb negb]. reflexivity.
Qed.

Lemma check_fstat_pinned_complete_unmodeled : forall id ok i statbuf m eff,
  fstat_pinned_spec id ok statbuf i m Unmodeled ->
  check_fstat_pinned id ok i statbuf eff m = CheckUnmodeled.
Proof.
  intros id ok i statbuf m eff H.
  unfold fstat_pinned_spec in H. unfold check_fstat_pinned.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - exfalso. sys_unfold; inv_ok; hall Ha; inv_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|reflexivity].
    destruct (statpin_lookup (m_statpins m) id) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && ok (sp_bytes sp))%bool) eqn:Hb0;
        [reflexivity|].
      exfalso. sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok.
    + exfalso. sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; inv_ok.
Qed.

(** A device node's arm: its key's pin ([Stat.fstat_chrdev_spec]). *)
Definition check_fstat_chrdev (ok : list byte -> bool) (k : Fs.path)
    (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_fstat_pinned (IdDev k) ok i statbuf eff m.

Lemma check_fstat_chrdev_sound_ok : forall ok k i statbuf eff m m' evs,
  check_fstat_chrdev ok k i statbuf eff m = CheckOk m' evs ->
  fstat_chrdev_spec k ok statbuf i m (Ok eff m' evs).
Proof. intros * H. eapply check_fstat_pinned_sound_ok. exact H. Qed.

Lemma check_fstat_chrdev_sound_unmodeled : forall ok k i statbuf eff m,
  check_fstat_chrdev ok k i statbuf eff m = CheckUnmodeled ->
  fstat_chrdev_spec k ok statbuf i m Unmodeled.
Proof. intros * H. eapply check_fstat_pinned_sound_unmodeled. exact H. Qed.

Lemma check_fstat_chrdev_complete_ok : forall ok k i statbuf eff m m' evs,
  fstat_chrdev_spec k ok statbuf i m (Ok eff m' evs) ->
  check_fstat_chrdev ok k i statbuf eff m = CheckOk m' evs.
Proof. intros * H. eapply check_fstat_pinned_complete_ok. exact H. Qed.

Lemma check_fstat_chrdev_complete_unmodeled : forall ok k i statbuf m eff,
  fstat_chrdev_spec k ok statbuf i m Unmodeled ->
  check_fstat_chrdev ok k i statbuf eff m = CheckUnmodeled.
Proof. intros * H. eapply check_fstat_pinned_complete_unmodeled. exact H. Qed.

(** A link the walk did not follow ([Stat.fstat_link_spec]): S_IFLNK,
    the body's length, under the link's own pin. *)
Definition check_fstat_link (k b : Fs.path) (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_fstat_pinned (IdLink k)
    (fun bs => stat_is_lnk bs && stat_lnk_size_ok (length (Fs.link_text b)) bs)%bool
    i statbuf eff m.

Lemma check_fstat_link_sound_ok : forall k b i statbuf eff m m' evs,
  check_fstat_link k b i statbuf eff m = CheckOk m' evs ->
  fstat_link_spec k b statbuf i m (Ok eff m' evs).
Proof. intros * H. eapply check_fstat_pinned_sound_ok. exact H. Qed.

Lemma check_fstat_link_sound_unmodeled : forall k b i statbuf eff m,
  check_fstat_link k b i statbuf eff m = CheckUnmodeled ->
  fstat_link_spec k b statbuf i m Unmodeled.
Proof. intros * H. eapply check_fstat_pinned_sound_unmodeled. exact H. Qed.

Lemma check_fstat_link_complete_ok : forall k b i statbuf eff m m' evs,
  fstat_link_spec k b statbuf i m (Ok eff m' evs) ->
  check_fstat_link k b i statbuf eff m = CheckOk m' evs.
Proof. intros * H. eapply check_fstat_pinned_complete_ok. exact H. Qed.

Lemma check_fstat_link_complete_unmodeled : forall k b i statbuf m eff,
  fstat_link_spec k b statbuf i m Unmodeled ->
  check_fstat_link k b i statbuf eff m = CheckUnmodeled.
Proof. intros * H. eapply check_fstat_pinned_complete_unmodeled. exact H. Qed.

(** The directory arm, branch for branch with [Stat.fstat_dir_spec]: the
    folder's pin ([State.IdDir]) checked against both predicates, and the
    delivery judged under [stat_dir_ok] with the rule the pin carries;
    the model left is [Stat.dir_pin_after]'s on a pinned folder, and a
    new pin carrying [Stat.dir_rule_after]'s rule on one with none. *)
Definition check_fstat_dir (k : Fs.path) (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb statbuf STAT_SIZE)
  then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => CheckUnmodeled
    | Some _ =>
        match statpin_lookup (m_statpins m) (IdDir k) with
        | Some sp =>
            if negb (stat_buf_wf (sp_bytes sp) && stat_is_dir (sp_bytes sp))%bool
            then CheckUnmodeled
            else check_fstat_deliver_gen
                   (stat_dir_ok (Fs.fs_dir_links (m_fs m) k) (sp_rule sp))
                   statbuf (Some (sp_bytes sp))
                   (fun bs => dir_pin_after k (Fs.fs_dir_links (m_fs m) k) sp bs m) eff
        | None =>
            check_fstat_deliver_gen
              (stat_dir_ok (Fs.fs_dir_links (m_fs m) k) None) statbuf None
              (fun bs => with_statpin (IdDir k)
                           (mkStatPin bs (dir_rule_after (Fs.fs_dir_links (m_fs m) k) None bs))
                           m) eff
        end
    end.

Lemma check_fstat_dir_sound_ok : forall k i statbuf eff m m' evs,
  check_fstat_dir k i statbuf eff m = CheckOk m' evs ->
  fstat_dir_spec k statbuf i m (Ok eff m' evs).
Proof.
  intros k i statbuf eff m m' evs H.
  unfold check_fstat_dir in H. unfold fstat_dir_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|discriminate].
    cbv iota.
    destruct (statpin_lookup (m_statpins m) (IdDir k)) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_dir (sp_bytes sp))%bool)
        eqn:Hb0; [discriminate|].
      cbv iota.
      apply check_fstat_deliver_gen_ok in H as (bs & -> & -> & HWF & HOK & HS & ->).
      specialize (HS _ eq_refl).
      unfold stat_dir_ok in HOK. apply andb_true_iff in HOK as [HDIR HNL].
      eapply bind_ok0; [apply (choose_ok _ bs); repeat split; eassumption|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + apply check_fstat_deliver_gen_ok in H as (bs & -> & -> & HWF & HOK & _ & ->).
      unfold stat_dir_ok in HOK. apply andb_true_iff in HOK as [HDIR HNL].
      eapply bind_ok0; [apply (choose_ok _ bs); repeat split; eassumption|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_fstat_dir_sound_unmodeled : forall k i statbuf eff m,
  check_fstat_dir k i statbuf eff m = CheckUnmodeled ->
  fstat_dir_spec k statbuf i m Unmodeled.
Proof.
  intros k i statbuf eff m H.
  unfold check_fstat_dir in H. unfold fstat_dir_spec.
  eapply bind_unmodeled2; [apply input_ok|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [cbv iota|cbv iota; apply unmodeled_intro].
    destruct (statpin_lookup (m_statpins m) (IdDir k)) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_dir (sp_bytes sp))%bool)
        eqn:Hb0; [cbv iota; apply unmodeled_intro|].
      now apply check_fstat_deliver_gen_no_unmodeled in H.
    + now apply check_fstat_deliver_gen_no_unmodeled in H.
Qed.

Lemma check_fstat_dir_complete_ok : forall k i statbuf eff m m' evs,
  fstat_dir_spec k statbuf i m (Ok eff m' evs) ->
  check_fstat_dir k i statbuf eff m = CheckOk m' evs.
Proof.
  intros k i statbuf eff m m' evs H.
  unfold fstat_dir_spec in H. unfold check_fstat_dir.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - sys_unfold; inv_ok; hall Ha; inv_ok.
    apply check_ret_only_ok_iff. now repeat split.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|sys_unfold; inv_ok; hall Ha; hall Hw; inv_ok].
    destruct (statpin_lookup (m_statpins m) (IdDir k)) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_dir (sp_bytes sp))%bool)
        eqn:Hb0;
        [sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok|].
      sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok.
      unfold check_fstat_deliver_gen, stat_dir_ok.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : stat_is_dir ?b = true,
        H4 : dir_nlink_ok _ _ ?b = true,
        H3 : stat_stable_eqb ?b _ = true |- _ =>
          rewrite H1, H2, H4; cbn [andb negb]; rewrite H3
      end.
      reflexivity.
    + sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; inv_ok.
      unfold check_fstat_deliver_gen, stat_dir_ok.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : stat_is_dir ?b = true,
        H4 : dir_nlink_ok _ _ ?b = true |- _ =>
          rewrite H1, H2, H4
      end.
      cbn [andb negb]. reflexivity.
Qed.

Lemma check_fstat_dir_complete_unmodeled : forall k i statbuf m eff,
  fstat_dir_spec k statbuf i m Unmodeled ->
  check_fstat_dir k i statbuf eff m = CheckUnmodeled.
Proof.
  intros k i statbuf m eff H.
  unfold fstat_dir_spec in H. unfold check_fstat_dir.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - exfalso. sys_unfold; inv_ok; hall Ha; inv_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|reflexivity].
    destruct (statpin_lookup (m_statpins m) (IdDir k)) as [sp|] eqn:Hp.
    + destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_dir (sp_bytes sp))%bool)
        eqn:Hb0; [reflexivity|].
      exfalso. sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok.
    + exfalso. sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; inv_ok.
Qed.

(** The two descriptor instances, and their lemmas by instantiation:
    a device descriptor reads the pin of the node at the device's own
    name ([Open.dev_at_home]). *)
Definition check_fstat_devnull (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_fstat_chrdev stat_devnull_ok devnull_path i statbuf eff m.

Definition check_fstat_urandom (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_fstat_chrdev stat_urandom_ok urandom_path i statbuf eff m.

Lemma check_fstat_devnull_sound_ok : forall i statbuf eff m m' evs,
  check_fstat_devnull i statbuf eff m = CheckOk m' evs ->
  fstat_devnull_spec statbuf i m (Ok eff m' evs).
Proof. intros. apply check_fstat_chrdev_sound_ok. exact H. Qed.

Lemma check_fstat_devnull_sound_unmodeled : forall i statbuf eff m,
  check_fstat_devnull i statbuf eff m = CheckUnmodeled ->
  fstat_devnull_spec statbuf i m Unmodeled.
Proof. intros. apply check_fstat_chrdev_sound_unmodeled with (eff := eff). exact H. Qed.

Lemma check_fstat_devnull_complete_ok : forall i statbuf eff m m' evs,
  fstat_devnull_spec statbuf i m (Ok eff m' evs) ->
  check_fstat_devnull i statbuf eff m = CheckOk m' evs.
Proof. intros. apply check_fstat_chrdev_complete_ok. exact H. Qed.

Lemma check_fstat_devnull_complete_unmodeled : forall i statbuf m eff,
  fstat_devnull_spec statbuf i m Unmodeled ->
  check_fstat_devnull i statbuf eff m = CheckUnmodeled.
Proof. intros. apply check_fstat_chrdev_complete_unmodeled. exact H. Qed.

Lemma check_fstat_urandom_sound_ok : forall i statbuf eff m m' evs,
  check_fstat_urandom i statbuf eff m = CheckOk m' evs ->
  fstat_urandom_spec statbuf i m (Ok eff m' evs).
Proof. intros. apply check_fstat_chrdev_sound_ok. exact H. Qed.

Lemma check_fstat_urandom_sound_unmodeled : forall i statbuf eff m,
  check_fstat_urandom i statbuf eff m = CheckUnmodeled ->
  fstat_urandom_spec statbuf i m Unmodeled.
Proof. intros. apply check_fstat_chrdev_sound_unmodeled with (eff := eff). exact H. Qed.

Lemma check_fstat_urandom_complete_ok : forall i statbuf eff m m' evs,
  fstat_urandom_spec statbuf i m (Ok eff m' evs) ->
  check_fstat_urandom i statbuf eff m = CheckOk m' evs.
Proof. intros. apply check_fstat_chrdev_complete_ok. exact H. Qed.

Lemma check_fstat_urandom_complete_unmodeled : forall i statbuf m eff,
  fstat_urandom_spec statbuf i m Unmodeled ->
  check_fstat_urandom i statbuf eff m = CheckUnmodeled.
Proof. intros. apply check_fstat_chrdev_complete_unmodeled. exact H. Qed.

(** [check_ret_only] on a bare errno arm, in the shape the proofs below
    apply it: the same [Local] helper [Checks.Sys.Fs.Open] carries. *)
Local Lemma check_ret_only_sound_ok : forall (i : SyscallInput) eff r m m' evs,
  check_ret_only eff r m [] = CheckOk m' evs ->
  ret_only r i m (Ok eff m' evs).
Proof.
  intros i eff r m m' evs H.
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  apply pure_ok.
Qed.

(** THE ENTRY DELIVERY, mirroring [Stat.stat_entry_spec] row for row:
    the inode's pin for a file, the key's for a folder, for a device
    node and for a link the walk did not follow. *)
Definition check_stat_entry (k : Fs.path) (e : Entry) (i : SyscallInput)
    (statbuf : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match e with
  | EFile ino => check_fstat_file i ino statbuf eff m
  | EDir => check_fstat_dir k i statbuf eff m
  | EDev DevNull => check_fstat_chrdev stat_devnull_ok k i statbuf eff m
  | EDev DevUrandom => check_fstat_chrdev stat_urandom_ok k i statbuf eff m
  | ELink b => check_fstat_link k b i statbuf eff m
  end.

Lemma check_stat_entry_sound_ok : forall k e i statbuf eff m m' evs,
  check_stat_entry k e i statbuf eff m = CheckOk m' evs ->
  stat_entry_spec k e statbuf i m (Ok eff m' evs).
Proof.
  intros k e i statbuf eff m m' evs H.
  unfold check_stat_entry in H. unfold stat_entry_spec.
  destruct e as [ino| |dk|lb]; cbv iota;
    [ now apply check_fstat_file_sound_ok
    | now apply check_fstat_dir_sound_ok
    | destruct dk; cbv iota; now apply check_fstat_chrdev_sound_ok
    | now apply check_fstat_link_sound_ok ].
Qed.

Lemma check_stat_entry_sound_unmodeled : forall k e i statbuf eff m,
  check_stat_entry k e i statbuf eff m = CheckUnmodeled ->
  stat_entry_spec k e statbuf i m Unmodeled.
Proof.
  intros k e i statbuf eff m H.
  unfold check_stat_entry in H. unfold stat_entry_spec.
  destruct e as [ino| |dk|lb]; cbv iota;
    [ eapply check_fstat_file_sound_unmodeled; exact H
    | eapply check_fstat_dir_sound_unmodeled; exact H
    | destruct dk; cbv iota; eapply check_fstat_chrdev_sound_unmodeled; exact H
    | eapply check_fstat_link_sound_unmodeled; exact H ].
Qed.

Lemma check_stat_entry_complete_ok : forall k e i statbuf eff m m' evs,
  stat_entry_spec k e statbuf i m (Ok eff m' evs) ->
  check_stat_entry k e i statbuf eff m = CheckOk m' evs.
Proof.
  intros k e i statbuf eff m m' evs H.
  unfold stat_entry_spec in H. unfold check_stat_entry.
  destruct e as [ino| |dk|lb]; cbv iota in H |- *;
    [ now apply check_fstat_file_complete_ok
    | now apply check_fstat_dir_complete_ok
    | destruct dk; cbv iota in H |- *; now apply check_fstat_chrdev_complete_ok
    | now apply check_fstat_link_complete_ok ].
Qed.

Lemma check_stat_entry_complete_unmodeled : forall k e i statbuf m eff,
  stat_entry_spec k e statbuf i m Unmodeled ->
  check_stat_entry k e i statbuf eff m = CheckUnmodeled.
Proof.
  intros k e i statbuf m eff H.
  unfold stat_entry_spec in H. unfold check_stat_entry.
  destruct e as [ino| |dk|lb]; cbv iota in H |- *;
    [ now apply check_fstat_file_complete_unmodeled
    | now apply check_fstat_dir_complete_unmodeled
    | destruct dk; cbv iota in H |- *; now apply check_fstat_chrdev_complete_unmodeled
    | now apply check_fstat_link_complete_unmodeled ].
Qed.

(** newfstatat: the path errnos, the two declines, and — new in R22 —
    the SUCCESS, one row per resolved entry kind.  Writing nothing is
    not reading nothing: each FAILING arm is
    [check_ret_only_copyins], which is [check_ret_only]'s empty-effect
    demand on everything BUT the copy-in list, plus an equality on that
    list; plain [check_ret_only] would insist the ledger be empty and so
    reject the truthful effect.  The range is the one
    [Open.check_openat] demands, because both syscalls run the same
    [getname_flags]; unlike openat's, no arm here copies in again after
    it, so the whole claimed list is that single range.

    THE SUCCESS ARM CARRIES THE SAME LEDGER, which is why it goes
    through [check_copyins_after] rather than through the delivery
    checker alone: the delivery judges a 128-byte write and an EMPTY
    copy-in list, and the wrapper then puts the pathname range on it. *)
Definition check_newfstatat_body (i : SyscallInput)
    (dirfd pathp statbuf flag : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | CstrOk p =>
      if path_eqb p [] then
        if negb (statat_empty_path flag) then check_ret_only eff (errno_ret ENOENT) m []
        else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
        else
          match Fs.fs_lookup (m_fs m) (m_cwd m) with
          | Some e => check_stat_entry (m_cwd m) e i statbuf eff m
          | None => CheckUnmodeled
          end
      else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
      else
        match Fs.resolve (statat_walk_mode flag) (m_fs m) (m_cwd m) p with
        | (Fs.RFound k e, _, _) => check_stat_entry k e i statbuf eff m
        | (Fs.RMissing _ _, _, _) => check_ret_only eff (errno_ret ENOENT) m []
        | (Fs.RNotDir _, _, _) => check_ret_only eff (errno_ret ENOTDIR) m []
        | (Fs.RAbsent _, _, _) => check_ret_only eff (errno_ret ENOENT) m []
        | (Fs.RLoop, _, _) => check_ret_only eff (errno_ret ELOOP) m []
        | (Fs.ROutside, _, _) => CheckUnmodeled
        | (Fs.RParent _ _, _, _) => CheckUnmodeled
        end
  end.

(** The NULL name under AT_EMPTY_PATH declines ([Stat.statat_null_name]).
    The walk's refusals are checked only on a call whose fetch reaches
    [getname_flags] ([Stat.statat_getname_runs]), as
    [Stat.newfstatat_core_spec] admits them, and [getname_flags]' own
    around the ledger on the same calls ([check_getname_refusals]), as
    [Stat.newfstatat_spec] admits them. *)
Definition check_newfstatat (i : SyscallInput) (dirfd pathp statbuf flag : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let fetched :=
    if negb (modeled_statat_flags flag) then CheckUnmodeled
    else if statat_null_name pathp flag then CheckUnmodeled
    else
      let reads := [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] in
      check_copyins_after reads eff
        (if statat_getname_runs i pathp flag then
           check_walk_refusals (statat_walk_mode flag) i pathp (clear_copyins eff) m
             (check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m)
         else check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m) in
  if statat_getname_runs i pathp flag then check_getname_refusals i pathp eff m fetched
  else fetched.

(** A DELIVERED [struct stat] NEVER CLAIMS A COPY-IN: each accepting
    branch is either a bare errno return or the one 128-byte write, and
    both leave the copy-in ledger empty.  [newfstatat]'s wrapper is what
    puts the pathname range on it, so the body must not have one
    already. *)
Local Lemma check_fstat_deliver_gen_no_copyin :
  forall ok statbuf held post eff m' evs,
  check_fstat_deliver_gen ok statbuf held post eff = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros ok statbuf held post eff m' evs H.
  apply check_fstat_deliver_gen_ok in H as (bs & -> & _). reflexivity.
Qed.

Local Lemma check_fstat_file_no_copyin : forall i ino statbuf eff m m' evs,
  check_fstat_file i ino statbuf eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros i ino statbuf eff m m' evs H. unfold check_fstat_file in H.
  destruct (negb (access_okb statbuf STAT_SIZE)).
  - apply check_ret_only_ok_iff in H as (-> & _ & _). reflexivity.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|]; [|discriminate].
    destruct (statpin_lookup (m_statpins m) (IdIno ino)) as [sp|];
      [destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_reg (sp_bytes sp))%bool);
        [discriminate|]|];
      eapply check_fstat_deliver_gen_no_copyin; exact H.
Qed.

Local Lemma check_fstat_dir_no_copyin : forall k i statbuf eff m m' evs,
  check_fstat_dir k i statbuf eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros k i statbuf eff m m' evs H. unfold check_fstat_dir in H.
  destruct (negb (access_okb statbuf STAT_SIZE)).
  - apply check_ret_only_ok_iff in H as (-> & _ & _). reflexivity.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|]; [|discriminate].
    destruct (statpin_lookup (m_statpins m) (IdDir k)) as [sp|];
      [destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_dir (sp_bytes sp))%bool);
        [discriminate|]|];
      eapply check_fstat_deliver_gen_no_copyin; exact H.
Qed.

Local Lemma check_fstat_pinned_no_copyin : forall id ok i statbuf eff m m' evs,
  check_fstat_pinned id ok i statbuf eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros id ok i statbuf eff m m' evs H. unfold check_fstat_pinned in H.
  destruct (negb (access_okb statbuf STAT_SIZE)).
  - apply check_ret_only_ok_iff in H as (-> & _ & _). reflexivity.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|]; [|discriminate].
    destruct (statpin_lookup (m_statpins m) id) as [sp|];
      [destruct (negb (stat_buf_wf (sp_bytes sp) && ok (sp_bytes sp))%bool);
        [discriminate|]|];
      eapply check_fstat_deliver_gen_no_copyin; exact H.
Qed.

Local Lemma check_fstat_chrdev_no_copyin : forall ok k i statbuf eff m m' evs,
  check_fstat_chrdev ok k i statbuf eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof. intros * H. eapply check_fstat_pinned_no_copyin. exact H. Qed.

Local Lemma check_fstat_link_no_copyin : forall k b i statbuf eff m m' evs,
  check_fstat_link k b i statbuf eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof. intros * H. eapply check_fstat_pinned_no_copyin. exact H. Qed.

Local Lemma check_stat_entry_no_copyin : forall k e i statbuf eff m m' evs,
  check_stat_entry k e i statbuf eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros k e i statbuf eff m m' evs H. unfold check_stat_entry in H.
  destruct e as [ino| |dk|lb]; cbv iota in H;
    [ eapply check_fstat_file_no_copyin; exact H
    | eapply check_fstat_dir_no_copyin; exact H
    | destruct dk; cbv iota in H; eapply check_fstat_chrdev_no_copyin; exact H
    | eapply check_fstat_link_no_copyin; exact H ].
Qed.

Local Lemma check_newfstatat_body_sound_ok :
  forall i dirfd pathp statbuf flag eff m m' evs,
  check_newfstatat_body i dirfd pathp statbuf flag eff m = CheckOk m' evs ->
  newfstatat_body_spec i m dirfd pathp statbuf flag i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp statbuf flag eff m m' evs H.
  unfold check_newfstatat_body in H. unfold newfstatat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota;
    [|now apply check_ret_only_sound_ok|now apply check_ret_only_sound_ok].
  destruct (path_eqb p []); cbv iota.
  - destruct (negb (statat_empty_path flag)); cbv iota;
      [now apply check_ret_only_sound_ok|].
    destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota; [discriminate|].
    destruct (Fs.fs_lookup (m_fs m) (m_cwd m)) as [e|]; cbv iota; [|discriminate].
    now apply check_stat_entry_sound_ok.
  - destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota; [discriminate|].
    destruct (Fs.resolve (statat_walk_mode flag) (m_fs m) (m_cwd m) p)
      as [[r lk] ts] eqn:Hr.
    cbv iota zeta.
    destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
      try (now apply check_ret_only_sound_ok); try discriminate.
    now apply check_stat_entry_sound_ok.
Qed.

Local Lemma check_newfstatat_body_sound_unmodeled :
  forall i dirfd pathp statbuf flag eff m,
  check_newfstatat_body i dirfd pathp statbuf flag eff m = CheckUnmodeled ->
  newfstatat_body_spec i m dirfd pathp statbuf flag i m Unmodeled.
Proof.
  intros i dirfd pathp statbuf flag eff m H.
  unfold check_newfstatat_body in H. unfold newfstatat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota;
    [|now apply check_ret_only_no_unmodeled in H
     |now apply check_ret_only_no_unmodeled in H].
  destruct (path_eqb p []); cbv iota.
  - destruct (negb (statat_empty_path flag)); cbv iota;
      [now apply check_ret_only_no_unmodeled in H|].
    destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota; [apply unmodeled_intro|].
    destruct (Fs.fs_lookup (m_fs m) (m_cwd m)) as [e|]; cbv iota;
      [|apply unmodeled_intro].
    eapply check_stat_entry_sound_unmodeled. exact H.
  - destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota;
      [apply unmodeled_intro|].
    destruct (Fs.resolve (statat_walk_mode flag) (m_fs m) (m_cwd m) p)
      as [[r lk] ts] eqn:Hr.
    cbv iota zeta.
    destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
      try (now apply check_ret_only_no_unmodeled in H);
      try apply unmodeled_intro.
    eapply check_stat_entry_sound_unmodeled. exact H.
Qed.

Local Lemma check_newfstatat_body_complete_ok :
  forall i dirfd pathp statbuf flag core m m' evs,
  newfstatat_body_spec i m dirfd pathp statbuf flag i m (Ok core m' evs) ->
  check_newfstatat_body i dirfd pathp statbuf flag core m = CheckOk m' evs
  /\ eff_copyins core = [].
Proof.
  intros i dirfd pathp statbuf flag core m m' evs H.
  unfold newfstatat_body_spec in H. unfold check_newfstatat_body.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    [|split; [apply check_ret_only_ok_iff|];
       sys_unfold; inv_ok; now repeat split
     |split; [apply check_ret_only_ok_iff|];
       sys_unfold; inv_ok; now repeat split].
  destruct (path_eqb p []); cbv iota in H |- *.
  - destruct (negb (statat_empty_path flag)); cbv iota in H |- *;
      [split; [apply check_ret_only_ok_iff|];
       sys_unfold; inv_ok; now repeat split|].
    destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
      [unfold unmodeled in H; inv_ok|].
    destruct (Fs.fs_lookup (m_fs m) (m_cwd m)) as [e|]; cbv iota in H |- *;
      [|unfold unmodeled in H; inv_ok].
    assert (Hc : check_stat_entry (m_cwd m) e i statbuf core m = CheckOk m' evs)
      by (now apply check_stat_entry_complete_ok).
    split; [exact Hc | eapply check_stat_entry_no_copyin; exact Hc].
  - destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
      [unfold unmodeled in H; inv_ok|].
    destruct (Fs.resolve (statat_walk_mode flag) (m_fs m) (m_cwd m) p)
      as [[r lk] ts] eqn:Hr.
    cbv iota zeta in H |- *.
    destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
      try (split; [apply check_ret_only_ok_iff|];
           sys_unfold; inv_ok; now repeat split);
      try (unfold unmodeled in H; inv_ok).
    assert (Hc : check_stat_entry k e i statbuf core m = CheckOk m' evs)
      by (now apply check_stat_entry_complete_ok).
    split; [exact Hc | eapply check_stat_entry_no_copyin; exact Hc].
Qed.

Local Lemma check_newfstatat_body_complete_unmodeled :
  forall i dirfd pathp statbuf flag m eff,
  newfstatat_body_spec i m dirfd pathp statbuf flag i m Unmodeled ->
  check_newfstatat_body i dirfd pathp statbuf flag eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp statbuf flag m eff H.
  unfold newfstatat_body_spec in H. unfold check_newfstatat_body.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    [|sys_unfold; inv_ok|sys_unfold; inv_ok].
  destruct (path_eqb p []); cbv iota in H |- *.
  - destruct (negb (statat_empty_path flag)); cbv iota in H |- *;
      [sys_unfold; inv_ok|].
    destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
      [reflexivity|].
    destruct (Fs.fs_lookup (m_fs m) (m_cwd m)) as [e|]; cbv iota in H |- *;
      [|reflexivity].
    now apply check_stat_entry_complete_unmodeled.
  - destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
      [reflexivity|].
    destruct (Fs.resolve (statat_walk_mode flag) (m_fs m) (m_cwd m) p)
      as [[r lk] ts] eqn:Hr.
    cbv iota zeta in H |- *.
    destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
      try (sys_unfold; inv_ok); try reflexivity.
    now apply check_stat_entry_complete_unmodeled.
Qed.

(** The body with [check_walk_refusals] around it, from the body's four
    and [Checks.Sys.Prelude]'s section lemmas. *)
Local Lemma check_newfstatat_walked_sound_ok :
  forall i dirfd pathp statbuf flag m eff m' evs,
  check_walk_refusals (statat_walk_mode flag) i pathp eff m
    (check_newfstatat_body i dirfd pathp statbuf flag eff m) = CheckOk m' evs ->
  walk_refusals (statat_walk_mode flag) pathp
    (newfstatat_body_spec i m dirfd pathp statbuf flag) i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp statbuf flag m.
  apply (check_walk_refusals_sound_ok (statat_walk_mode flag) _
           (fun e => check_newfstatat_body i dirfd pathp statbuf flag e m)).
  - intros. eapply check_newfstatat_body_sound_ok. eassumption.
  - intros. eapply check_newfstatat_body_sound_unmodeled. eassumption.
  - intros e m1 evs1 Hs.
    exact (proj1 (check_newfstatat_body_complete_ok _ _ _ _ flag _ _ _ _ Hs)).
  - intros. eapply check_newfstatat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_newfstatat_walked_sound_unmodeled :
  forall i dirfd pathp statbuf flag m eff,
  check_walk_refusals (statat_walk_mode flag) i pathp eff m
    (check_newfstatat_body i dirfd pathp statbuf flag eff m) = CheckUnmodeled ->
  walk_refusals (statat_walk_mode flag) pathp
    (newfstatat_body_spec i m dirfd pathp statbuf flag) i m Unmodeled.
Proof.
  intros i dirfd pathp statbuf flag m.
  apply (check_walk_refusals_sound_unmodeled (statat_walk_mode flag) _
           (fun e => check_newfstatat_body i dirfd pathp statbuf flag e m)).
  - intros. eapply check_newfstatat_body_sound_ok. eassumption.
  - intros. eapply check_newfstatat_body_sound_unmodeled. eassumption.
  - intros e m1 evs1 Hs.
    exact (proj1 (check_newfstatat_body_complete_ok _ _ _ _ flag _ _ _ _ Hs)).
  - intros. eapply check_newfstatat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_newfstatat_walked_complete_ok :
  forall i dirfd pathp statbuf flag core m m' evs,
  walk_refusals (statat_walk_mode flag) pathp
    (newfstatat_body_spec i m dirfd pathp statbuf flag) i m (Ok core m' evs) ->
  check_walk_refusals (statat_walk_mode flag) i pathp core m
    (check_newfstatat_body i dirfd pathp statbuf flag core m) = CheckOk m' evs
  /\ eff_copyins core = [].
Proof.
  intros i dirfd pathp statbuf flag core m m' evs H.
  assert (Hc : check_walk_refusals (statat_walk_mode flag) i pathp core m
                 (check_newfstatat_body i dirfd pathp statbuf flag core m)
               = CheckOk m' evs).
  { revert core m' evs H.
    apply (check_walk_refusals_complete_ok (statat_walk_mode flag) _
             (fun e => check_newfstatat_body i dirfd pathp statbuf flag e m)).
    - intros. eapply check_newfstatat_body_sound_ok. eassumption.
    - intros. eapply check_newfstatat_body_sound_unmodeled. eassumption.
    - intros e m1 evs1 Hs.
      exact (proj1 (check_newfstatat_body_complete_ok _ _ _ _ flag _ _ _ _ Hs)).
    - intros. eapply check_newfstatat_body_complete_unmodeled. eassumption. }
  split; [exact Hc|].
  eapply check_walk_refusals_copyins_nil; [|exact Hc].
  intros m1 evs1 Hb.
  exact (proj2 (check_newfstatat_body_complete_ok _ _ _ _ flag _ _ _ _
                  (check_newfstatat_body_sound_ok _ _ _ _ _ _ _ _ _ Hb))).
Qed.

Local Lemma check_newfstatat_walked_complete_unmodeled :
  forall i dirfd pathp statbuf flag m eff,
  walk_refusals (statat_walk_mode flag) pathp
    (newfstatat_body_spec i m dirfd pathp statbuf flag) i m Unmodeled ->
  check_walk_refusals (statat_walk_mode flag) i pathp eff m
    (check_newfstatat_body i dirfd pathp statbuf flag eff m) = CheckUnmodeled.
Proof.
  intros i dirfd pathp statbuf flag m.
  apply (check_walk_refusals_complete_unmodeled (statat_walk_mode flag) _
           (fun e => check_newfstatat_body i dirfd pathp statbuf flag e m)).
  - intros. eapply check_newfstatat_body_sound_ok. eassumption.
  - intros. eapply check_newfstatat_body_sound_unmodeled. eassumption.
  - intros e m1 evs1 Hs.
    exact (proj1 (check_newfstatat_body_complete_ok _ _ _ _ flag _ _ _ _ Hs)).
  - intros. eapply check_newfstatat_body_complete_unmodeled. eassumption.
Qed.

(** The call from the flag word on, under its pathname ledger: the part
    [getname_flags]' own refusals wrap where the fetch reaches it.  As
    for readlinkat above, the four are stated over [check_newfstatat]'s
    own expression, not over a name for it. *)
Local Lemma check_newfstatat_fetched_sound_ok :
  forall i dirfd pathp statbuf flag m eff m' evs,
  (if negb (modeled_statat_flags flag) then CheckUnmodeled
   else if statat_null_name pathp flag then CheckUnmodeled
   else
     check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
       (if statat_getname_runs i pathp flag then
          check_walk_refusals (statat_walk_mode flag) i pathp (clear_copyins eff) m
            (check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m)
        else check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m))
  = CheckOk m' evs ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (newfstatat_core_spec dirfd pathp statbuf flag) i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp statbuf flag m eff m' evs H.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl; [discriminate|].
  destruct (statat_null_name pathp flag) eqn:Hnull; [discriminate|].
  cbv iota zeta in H.
  apply check_copyins_after_ok_iff in H as (Hreads & Hchecked).
  apply record_copyins_clear_ok; [exact Hreads|].
  unfold newfstatat_core_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
  rewrite Hfl. cbv iota.
  rewrite Hnull. cbv iota.
  destruct (statat_getname_runs i pathp flag); cbv iota in Hchecked |- *.
  - eapply check_newfstatat_walked_sound_ok. exact Hchecked.
  - eapply check_newfstatat_body_sound_ok. exact Hchecked.
Qed.

Local Lemma check_newfstatat_fetched_sound_unmodeled :
  forall i dirfd pathp statbuf flag m eff,
  (if negb (modeled_statat_flags flag) then CheckUnmodeled
   else if statat_null_name pathp flag then CheckUnmodeled
   else
     check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
       (if statat_getname_runs i pathp flag then
          check_walk_refusals (statat_walk_mode flag) i pathp (clear_copyins eff) m
            (check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m)
        else check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m))
  = CheckUnmodeled ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (newfstatat_core_spec dirfd pathp statbuf flag) i m Unmodeled.
Proof.
  intros i dirfd pathp statbuf flag m eff H.
  apply record_copyins_unmodeled.
  unfold newfstatat_core_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl; cbv iota;
    [apply unmodeled_intro|].
  destruct (statat_null_name pathp flag) eqn:Hnull; cbv iota;
    [apply unmodeled_intro|].
  cbv iota zeta in H. apply check_copyins_after_unmodeled in H.
  destruct (statat_getname_runs i pathp flag); cbv iota in H |- *.
  - eapply check_newfstatat_walked_sound_unmodeled. exact H.
  - eapply check_newfstatat_body_sound_unmodeled. exact H.
Qed.

Local Lemma check_newfstatat_fetched_complete_ok :
  forall i dirfd pathp statbuf flag m eff m' evs,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (newfstatat_core_spec dirfd pathp statbuf flag) i m (Ok eff m' evs) ->
  (if negb (modeled_statat_flags flag) then CheckUnmodeled
   else if statat_null_name pathp flag then CheckUnmodeled
   else
     check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
       (if statat_getname_runs i pathp flag then
          check_walk_refusals (statat_walk_mode flag) i pathp (clear_copyins eff) m
            (check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m)
        else check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m))
  = CheckOk m' evs.
Proof.
  intros i dirfd pathp statbuf flag m eff m' evs H.
  apply record_copyins_ok_inv in H. destruct H as (core & H & ->).
  unfold newfstatat_core_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply bind_get_model_ok_inv in H. cbv beta iota in H.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl;
    hall Hfl; [unfold unmodeled in H; inv_ok|].
  destruct (statat_null_name pathp flag) eqn:Hnull;
    hall Hnull; [unfold unmodeled in H; inv_ok|].
  cbv iota zeta.
  apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)).
  destruct (statat_getname_runs i pathp flag); cbv iota in H |- *;
    [ apply check_newfstatat_walked_complete_ok with (flag := flag) in H
        as (Hchecked & Hcopyins)
    | apply check_newfstatat_body_complete_ok in H as (Hchecked & Hcopyins) ];
    (split;
     [ cbn [with_copyins eff_copyins]; rewrite Hcopyins, app_nil_r; reflexivity
     | destruct core as [ret ws zs us cs copyins];
       cbn in Hcopyins; subst copyins; exact Hchecked ]).
Qed.

Local Lemma check_newfstatat_fetched_complete_unmodeled :
  forall i dirfd pathp statbuf flag m eff,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (newfstatat_core_spec dirfd pathp statbuf flag) i m Unmodeled ->
  (if negb (modeled_statat_flags flag) then CheckUnmodeled
   else if statat_null_name pathp flag then CheckUnmodeled
   else
     check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
       (if statat_getname_runs i pathp flag then
          check_walk_refusals (statat_walk_mode flag) i pathp (clear_copyins eff) m
            (check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m)
        else check_newfstatat_body i dirfd pathp statbuf flag (clear_copyins eff) m))
  = CheckUnmodeled.
Proof.
  intros i dirfd pathp statbuf flag m eff H.
  apply record_copyins_unmodeled_inv in H.
  unfold newfstatat_core_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply bind_get_model_unmodeled_inv in H. cbv beta iota in H.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl; hall Hfl;
    [reflexivity|].
  destruct (statat_null_name pathp flag) eqn:Hnull; hall Hnull;
    [reflexivity|].
  cbv iota zeta. unfold check_copyins_after.
  destruct (statat_getname_runs i pathp flag); cbv iota in H |- *.
  - rewrite (check_newfstatat_walked_complete_unmodeled i dirfd pathp statbuf flag
               m (clear_copyins eff) H).
    reflexivity.
  - rewrite (check_newfstatat_body_complete_unmodeled i dirfd pathp statbuf flag
               m (clear_copyins eff) H).
    reflexivity.
Qed.

(** [check_newfstatat]'s outer test, split or built without touching
    the same test inside the fetched call, which the four above state
    as it stands. *)
Local Lemma check_if_cases : forall (b : bool) (x y r : check_result),
  (if b then x else y) = r -> (b = true /\ x = r) \/ (b = false /\ y = r).
Proof. intros [] x y r H; auto. Qed.

Local Lemma check_if_intro : forall (b : bool) (x y r : check_result),
  (b = true -> x = r) -> (b = false -> y = r) -> (if b then x else y) = r.
Proof. intros [] x y r Ht Hf; auto. Qed.

(** The four exports: the fetched call, with [getname_flags]' own
    refusals around it on a call whose fetch reaches [getname_flags]
    ([Checks.Sys.Prelude]'s section lemmas) and alone on any other. *)
Lemma check_newfstatat_sound_ok :
  forall i dirfd pathp statbuf flag eff m m' evs,
  check_newfstatat i dirfd pathp statbuf flag eff m = CheckOk m' evs ->
  newfstatat_spec dirfd pathp statbuf flag i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp statbuf flag eff m m' evs H.
  unfold check_newfstatat in H. cbv zeta in H.
  unfold newfstatat_spec. eapply bind_ok0; [apply input_ok|]. cbv beta.
  apply check_if_cases in H as [(Hr & H) | (Hr & H)]; rewrite Hr; cbv iota.
  - exact (check_getname_refusals_sound_ok pathp _ _ i m
             (check_newfstatat_fetched_sound_ok i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_sound_unmodeled i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_complete_ok i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_complete_unmodeled i dirfd pathp statbuf flag m)
             eff m' evs H).
  - exact (check_newfstatat_fetched_sound_ok i dirfd pathp statbuf flag m eff m' evs H).
Qed.

Lemma check_newfstatat_sound_unmodeled :
  forall i dirfd pathp statbuf flag eff m,
  check_newfstatat i dirfd pathp statbuf flag eff m = CheckUnmodeled ->
  newfstatat_spec dirfd pathp statbuf flag i m Unmodeled.
Proof.
  intros i dirfd pathp statbuf flag eff m H.
  unfold check_newfstatat in H. cbv zeta in H.
  unfold newfstatat_spec. eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  apply check_if_cases in H as [(Hr & H) | (Hr & H)]; rewrite Hr; cbv iota.
  - exact (check_getname_refusals_sound_unmodeled pathp _ _ i m
             (check_newfstatat_fetched_sound_ok i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_sound_unmodeled i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_complete_ok i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_complete_unmodeled i dirfd pathp statbuf flag m)
             eff H).
  - exact (check_newfstatat_fetched_sound_unmodeled i dirfd pathp statbuf flag m eff H).
Qed.

Lemma check_newfstatat_complete_ok :
  forall i dirfd pathp statbuf flag eff m m' evs,
  newfstatat_spec dirfd pathp statbuf flag i m (Ok eff m' evs) ->
  check_newfstatat i dirfd pathp statbuf flag eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp statbuf flag eff m m' evs H.
  unfold newfstatat_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  unfold check_newfstatat. cbv zeta.
  apply check_if_intro; intros Hr; rewrite Hr in H; cbv iota in H.
  - exact (check_getname_refusals_complete_ok pathp _ _ i m
             (check_newfstatat_fetched_sound_ok i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_sound_unmodeled i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_complete_ok i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_complete_unmodeled i dirfd pathp statbuf flag m)
             eff m' evs H).
  - exact (check_newfstatat_fetched_complete_ok i dirfd pathp statbuf flag m eff m' evs H).
Qed.

Lemma check_newfstatat_complete_unmodeled :
  forall i dirfd pathp statbuf flag m eff,
  newfstatat_spec dirfd pathp statbuf flag i m Unmodeled ->
  check_newfstatat i dirfd pathp statbuf flag eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp statbuf flag m eff H.
  unfold newfstatat_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  unfold check_newfstatat. cbv zeta.
  apply check_if_intro; intros Hr; rewrite Hr in H; cbv iota in H.
  - exact (check_getname_refusals_complete_unmodeled pathp _ _ i m
             (check_newfstatat_fetched_sound_ok i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_sound_unmodeled i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_complete_ok i dirfd pathp statbuf flag m)
             (check_newfstatat_fetched_complete_unmodeled i dirfd pathp statbuf flag m)
             eff H).
  - exact (check_newfstatat_fetched_complete_unmodeled i dirfd pathp statbuf flag m eff H).
Qed.

(** fstat: total over [FdEntry], answering on the closed descriptor's
    -EBADF, the four file kinds, which share one inode and so one
    answer, the directory, /dev/null and /dev/urandom.  The other six
    decline as a body; see [Stat.fstat_spec] for which of [struct
    stat]'s twenty members each would have to invent, and for why the
    match carries no wildcard. *)
Definition check_fstat (i : SyscallInput) (fd statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) => CheckUnmodeled
  | Some (FdFile ino _)  => check_fstat_file i ino statbuf eff m
  | Some (FdFileW ino _) => check_fstat_file i ino statbuf eff m
  | Some (FdFileA ino _) => check_fstat_file i ino statbuf eff m
  | Some (FdFileRW ino _) => check_fstat_file i ino statbuf eff m
  | Some (FdDir k)     => check_fstat_dir k i statbuf eff m
  | Some (FdSocket _)  => CheckUnmodeled
  | Some (FdStream _ _ _) => CheckUnmodeled
  | Some (FdDgram _)   => CheckUnmodeled
  | Some (FdEventfd _) => CheckUnmodeled
  | Some (FdPipe _ _)  => CheckUnmodeled
  | Some (FdDevNull _ _) => check_fstat_devnull i statbuf eff m
  | Some (FdUrandom _ _) => check_fstat_urandom i statbuf eff m
  end.

Lemma check_fstat_sound_ok : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs ->
  fstat_spec fd statbuf i m (Ok eff m' evs).
Proof.
  intros i fd statbuf eff m m' evs H.
  unfold check_fstat in H. unfold fstat_spec.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota in H |- *.
  2: { apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok. }
  destruct e as [ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam];
    cbv iota in H |- *; try discriminate.
  all: first [now apply check_fstat_file_sound_ok
             |now apply check_fstat_dir_sound_ok
             |now apply check_fstat_devnull_sound_ok
             |now apply check_fstat_urandom_sound_ok].
Qed.

Lemma check_fstat_sound_unmodeled : forall i fd statbuf eff m,
  check_fstat i fd statbuf eff m = CheckUnmodeled ->
  fstat_spec fd statbuf i m Unmodeled.
Proof.
  intros i fd statbuf eff m H.
  unfold check_fstat in H. unfold fstat_spec.
  eapply bind_unmodeled2; [apply get_model_ok|].
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv beta iota in H |- *;
    [|now apply check_ret_only_no_unmodeled in H].
  destruct e as [ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam];
    cbv iota in H |- *; try apply unmodeled_intro.
  all: first [eapply check_fstat_file_sound_unmodeled; exact H
             |eapply check_fstat_dir_sound_unmodeled; exact H
             |eapply check_fstat_devnull_sound_unmodeled; exact H
             |eapply check_fstat_urandom_sound_unmodeled; exact H].
Qed.

Lemma check_fstat_complete_ok : forall i fd statbuf eff m m' evs,
  fstat_spec fd statbuf i m (Ok eff m' evs) ->
  check_fstat i fd statbuf eff m = CheckOk m' evs.
Proof.
  intros i fd statbuf eff m m' evs H.
  unfold fstat_spec in H. unfold check_fstat.
  apply bind_get_model_ok_inv in H. cbv beta in H.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota in H |- *.
  2: { unfold pure in H. inversion H; clear H; subst.
       apply check_ret_only_ok_iff. now repeat split. }
  destruct e as [ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam];
    cbv iota in H |- *.
  all: first [now apply check_fstat_file_complete_ok
             |now apply check_fstat_dir_complete_ok
             |now apply check_fstat_devnull_complete_ok
             |now apply check_fstat_urandom_complete_ok
             |unfold unmodeled in H; discriminate].
Qed.

Lemma check_fstat_complete_unmodeled : forall i fd statbuf m eff,
  fstat_spec fd statbuf i m Unmodeled ->
  check_fstat i fd statbuf eff m = CheckUnmodeled.
Proof.
  intros i fd statbuf m eff H.
  unfold fstat_spec in H. unfold check_fstat.
  apply bind_get_model_unmodeled_inv in H. cbv beta in H.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota in H |- *.
  2: { unfold pure in H. discriminate. }
  destruct e as [ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam];
    cbv iota in H |- *; try reflexivity.
  all: first [eapply check_fstat_file_complete_unmodeled; exact H
             |eapply check_fstat_dir_complete_unmodeled; exact H
             |eapply check_fstat_devnull_complete_unmodeled; exact H
             |eapply check_fstat_urandom_complete_unmodeled; exact H].
Qed.
