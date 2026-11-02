(** * LinuxProcessSem.Checks.Sys.Fs.Readdir — the getdents64 (61) checker, and its proofs

    Mirrors [Sys/Fs/Readdir.v], which answers to Linux [fs/readdir.c]:
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
  Prelude.

(* -------------------------------------------------------------------------
   The /proc/self/fd listing
   ------------------------------------------------------------------------- *)

(** [Fs.Readdir.procfd_getdents_spec] as an acceptor.  The records are
    the effect's own writes: their addresses must be the ones the plan
    gives, and their bytes must pass [procfd_recs_ok], the predicate the
    spec chooses under. *)
Definition check_procfd_getdents (i : SyscallInput) (fd fl : word) (pos : option word)
    (dirent count : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match pos with
  | None => CheckUnmodeled
  | Some pw =>
      if negb (procfd_in_range (m_fds m) (bv_unsigned pw)) then CheckUnmodeled
      else
      let es := procfd_plan (m_fds m) (bv_unsigned pw) in
      let n := procfd_fit es (getdents64_ctx_count count) in
      let mpos := fun np : option word =>
        with_fds (fd_insert (m_fds m) fd (FdOpaque (OProcFdDir fl np))) m in
      match n, es with
      | O, [] => check_ret_only eff (Z_to_bv 64 0) (mpos None) []
      | O, e :: _ => check_ret_only eff (errno_ret EINVAL) (mpos (Some (Z_to_bv 64 (pfe_pos e)))) []
      | S _, [] => CheckUnmodeled
      | S _, e :: _ =>
          if negb (access_okb dirent (dirent64_reclen (length (pfe_name e))))
          then check_ret_only eff (errno_ret EFAULT) (mpos (Some (Z_to_bv 64 (pfe_pos e)))) []
          else
          let ws := firstn n es in
          let addrs := procfd_addrs dirent ws in
          if access_okb dirent (procfd_total ws) && procfd_writable (in_wmem i) addrs ws
          then
            match eff with
            | mkEffectU ret wr [] [] [] [] =>
                if bv_eqb ret (Z_to_bv 64 (procfd_total ws))
                   && writes_eqb wr (combine addrs (map snd wr))
                   && procfd_recs_ok (procfd_end_ok (m_fds m)) es n (map snd wr)
                then CheckOk (mpos (Some (Z_to_bv 64 (procfd_last_doff (map snd wr))))) []
                else CheckReject
            | _ => CheckReject
            end
          else CheckUnmodeled
      end
  end.

Local Lemma procfd_writes_eqb_refl : forall l, writes_eqb l l = true.
Proof. intros l. apply writes_eqb_eq. reflexivity. Qed.

Lemma procfd_recs_ok_length : forall f es n bss,
  procfd_recs_ok f es n bss = true -> length bss = n /\ (n <= length es)%nat.
Proof.
  intros f es n. revert es.
  induction n as [|n IH]; intros es bss H.
  - destruct bss; [cbn; split; [reflexivity|lia]|].
    destruct es; discriminate H.
  - destruct es as [|e es']; [destruct bss; discriminate H|].
    destruct bss as [|bs bss']; [discriminate H|].
    cbn [procfd_recs_ok] in H. apply andb_true_iff in H as [_ H].
    destruct (IH _ _ H) as [H1 H2]. cbn [length]. split; lia.
Qed.

Lemma procfd_addrs_length : forall d es, length (procfd_addrs d es) = length es.
Proof.
  intros d es. revert d. induction es as [|e es IH]; intros d; cbn; [reflexivity|].
  now rewrite IH.
Qed.

Lemma map_snd_combine_eq {A B} : forall (a : list A) (b : list B),
  length a = length b -> map snd (combine a b) = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in *; try discriminate; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

Lemma check_procfd_getdents_sound_ok : forall i fd fl pos dirent count eff m m' evs,
  check_procfd_getdents i fd fl pos dirent count eff m = CheckOk m' evs ->
  procfd_getdents_spec fd fl pos dirent count i m (Ok eff m' evs).
Proof.
  intros i fd fl pos dirent count eff m m' evs H.
  unfold check_procfd_getdents in H. unfold procfd_getdents_spec.
  destruct pos as [pw|]; [|discriminate H].
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  destruct (negb (procfd_in_range (m_fds m) (bv_unsigned pw))); [discriminate H|].
  destruct (procfd_fit (procfd_plan (m_fds m) (bv_unsigned pw)) (getdents64_ctx_count count))
    as [|n'] eqn:Hn;
  destruct (procfd_plan (m_fds m) (bv_unsigned pw)) as [|e es'] eqn:Hes;
  cbv beta iota zeta in H |- *.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [unfold set_fds; apply modify_ok|]. cbv beta.
    unfold ret_only. apply pure_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [unfold set_fds; apply modify_ok|]. cbv beta.
    unfold err_ret, ret_only. apply pure_ok.
  - discriminate H.
  - destruct (negb (access_okb dirent (dirent64_reclen (length (pfe_name e))))).
    + apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      eapply bind_ok0; [unfold set_fds; apply modify_ok|]. cbv beta.
      unfold err_ret, ret_only. apply pure_ok.
    + eapply bind_ok0; [apply input_ok|]. cbv beta zeta.
      match type of H with
      | context [if ?b then _ else CheckUnmodeled] => destruct b eqn:Hw; [|discriminate H]
      end.
      destruct eff as [ret wr zs us cs cis];
        destruct zs; [|discriminate H]; destruct us; [|discriminate H];
        destruct cs; [|discriminate H]; destruct cis; [|discriminate H].
      match type of H with
      | context [if ?b then CheckOk _ _ else CheckReject] => destruct b eqn:Hc; [|discriminate H]
      end.
      inversion H; clear H; subst.
      apply andb_true_iff in Hc as [Hc Hrecs]. apply andb_true_iff in Hc as [Hr Hwr].
      apply bv_eqb_eq in Hr; subst ret. apply writes_eqb_eq in Hwr.
      eapply bind_ok0; [apply (choose_ok _ (map snd wr)); exact Hrecs|]. cbv beta.
      eapply bind_ok0; [unfold set_fds; apply modify_ok|]. cbv beta.
      rewrite <- Hwr. apply pure_ok.
Qed.

Lemma check_procfd_getdents_sound_unmodeled : forall i fd fl pos dirent count eff m,
  check_procfd_getdents i fd fl pos dirent count eff m = CheckUnmodeled ->
  procfd_getdents_spec fd fl pos dirent count i m Unmodeled.
Proof.
  intros i fd fl pos dirent count eff m H.
  unfold check_procfd_getdents in H. unfold procfd_getdents_spec.
  destruct pos as [pw|]; [|apply unmodeled_intro].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
  destruct (negb (procfd_in_range (m_fds m) (bv_unsigned pw))); [apply unmodeled_intro|].
  destruct (procfd_fit (procfd_plan (m_fds m) (bv_unsigned pw)) (getdents64_ctx_count count))
    as [|n'] eqn:Hn;
  destruct (procfd_plan (m_fds m) (bv_unsigned pw)) as [|e es'] eqn:Hes;
  cbv beta iota zeta in H |- *;
    try (exfalso; now apply check_ret_only_no_unmodeled in H).
  - apply unmodeled_intro.
  - destruct (negb (access_okb dirent (dirent64_reclen (length (pfe_name e)))));
      [exfalso; now apply check_ret_only_no_unmodeled in H|].
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta zeta.
    match type of H with
    | context [if ?b then _ else CheckUnmodeled] => destruct b eqn:Hw; [|apply unmodeled_intro]
    end.
    exfalso.
    destruct eff as [ret wr zs us cs cis];
      destruct zs; [|discriminate H]; destruct us; [|discriminate H];
      destruct cs; [|discriminate H]; destruct cis; [|discriminate H].
    match type of H with
    | context [if ?b then CheckOk _ _ else CheckReject] => destruct b; discriminate H
    end.
Qed.

Local Ltac no_unmodeled_ok H := unfold unmodeled in H; discriminate H.

(** The accepting branch of [check_procfd_getdents], on the effect the
    spec builds: the records' bytes are what the checker reads back. *)
Lemma procfd_records_accept : forall (T : word) (A : list word) (bss : list (list byte))
    (f : Z -> bool) es n (mk : option word -> Model),
  length A = length bss ->
  procfd_recs_ok f es n bss = true ->
  match mkEffectU T (combine A bss) [] [] [] [] with
  | mkEffectU ret wr [] [] [] [] =>
      if bv_eqb ret T
         && writes_eqb wr (combine A (map snd wr))
         && procfd_recs_ok f es n (map snd wr)
      then CheckOk (mk (Some (Z_to_bv 64 (procfd_last_doff (map snd wr))))) []
      else CheckReject
  | _ => CheckReject
  end = CheckOk (mk (Some (Z_to_bv 64 (procfd_last_doff bss)))) [].
Proof.
  intros T A bss f es n mk Hlen Hrecs.
  cbn iota beta.
  rewrite (map_snd_combine_eq A bss Hlen), bv_eqb_refl, Hrecs, procfd_writes_eqb_refl.
  reflexivity.
Qed.

Lemma check_procfd_getdents_complete_ok : forall i fd fl pos dirent count eff m m' evs,
  procfd_getdents_spec fd fl pos dirent count i m (Ok eff m' evs) ->
  check_procfd_getdents i fd fl pos dirent count eff m = CheckOk m' evs.
Proof.
  intros i fd fl pos dirent count eff m m' evs H.
  unfold procfd_getdents_spec in H. unfold check_procfd_getdents.
  destruct pos as [pw|]; [|no_unmodeled_ok H].
  apply get_model_bind_ok_inv in H. cbv beta zeta in H.
  destruct (negb (procfd_in_range (m_fds m) (bv_unsigned pw))); [no_unmodeled_ok H|].
  destruct (procfd_fit (procfd_plan (m_fds m) (bv_unsigned pw)) (getdents64_ctx_count count))
    as [|n'] eqn:Hn;
  destruct (procfd_plan (m_fds m) (bv_unsigned pw)) as [|e es'] eqn:Hes;
  cbv beta iota zeta in H |- *.
  - sys_unfold. inv_ok. apply check_ret_only_ok_iff. auto.
  - sys_unfold. inv_ok. apply check_ret_only_ok_iff. auto.
  - no_unmodeled_ok H.
  - destruct (negb (access_okb dirent (dirent64_reclen (length (pfe_name e))))).
    + sys_unfold. inv_ok. apply check_ret_only_ok_iff. auto.
    + apply input_bind_ok_inv in H. cbv beta zeta in H.
      match goal with
      | |- context [if ?b then _ else CheckUnmodeled] => destruct b eqn:Hw; [|no_unmodeled_ok H]
      end.
      cbv beta iota in H.
      (* the records chosen, the position stored, the effect returned *)
      destruct H as (bss & m1 & evs1 & evs2 & Hch & Hk & Hevs).
      destruct Hch as (bss0 & Hrecs & Hch).
      injection Hch as -> -> ->.
      cbv beta in Hk.
      destruct Hk as (u & m2 & evs3 & evs4 & Hset & Hp & Hevs2).
      cbv beta in Hset. unfold set_fds, modify in Hset. injection Hset as -> -> ->.
      cbv beta in Hp. unfold pure in Hp. injection Hp as -> -> ->.
      subst evs evs2.
      cbv beta in Hrecs.
      pose proof (procfd_recs_ok_length _ _ _ _ Hrecs) as [Hl Hle].
      exact (procfd_records_accept
               (Z_to_bv 64 (procfd_total (firstn (S n') (e :: es'))))
               (procfd_addrs dirent (firstn (S n') (e :: es')))
               bss0 (procfd_end_ok (m_fds m)) (e :: es') (S n')
               (fun np => with_fds (fd_insert (m_fds m) fd (FdOpaque (OProcFdDir fl np))) m)
               ltac:(rewrite procfd_addrs_length, firstn_length_le; lia)
               Hrecs).
Qed.

Lemma check_procfd_getdents_complete_unmodeled : forall i fd fl pos dirent count eff m,
  procfd_getdents_spec fd fl pos dirent count i m Unmodeled ->
  check_procfd_getdents i fd fl pos dirent count eff m = CheckUnmodeled.
Proof.
  intros i fd fl pos dirent count eff m H.
  unfold procfd_getdents_spec in H. unfold check_procfd_getdents.
  destruct pos as [pw|]; [|reflexivity].
  apply get_model_bind_unmodeled_inv in H. cbv beta zeta in H.
  destruct (negb (procfd_in_range (m_fds m) (bv_unsigned pw))); [reflexivity|].
  destruct (procfd_fit (procfd_plan (m_fds m) (bv_unsigned pw)) (getdents64_ctx_count count))
    as [|n'] eqn:Hn;
  destruct (procfd_plan (m_fds m) (bv_unsigned pw)) as [|e es'] eqn:Hes;
  cbv beta iota zeta in H |- *;
    try reflexivity;
    try (exfalso; sys_unfold; inv_ok; fail).
  destruct (negb (access_okb dirent (dirent64_reclen (length (pfe_name e)))));
    [exfalso; sys_unfold; inv_ok|].
  apply input_bind_unmodeled_inv in H. cbv beta zeta in H.
  match goal with
  | |- context [if ?b then _ else CheckUnmodeled] => destruct b eqn:Hw; [|reflexivity]
  end.
  exfalso. cbv beta iota in H.
  destruct H as [Hc | (x & m1 & evs1 & Hc & Hk)].
  - destruct Hc as (y & _ & Hc). discriminate Hc.
  - cbv beta in Hk. destruct Hk as [Hs | (u & m2 & evs2 & Hs & Hp)].
    + unfold set_fds, modify in Hs. discriminate Hs.
    + cbv beta in Hp. unfold pure in Hp. discriminate Hp.
Qed.

(** The listing never answers -ENOENT: its returns are 0, -EINVAL,
    -EFAULT and a byte count below 2^31 ([SpuriousCfg] reads this). *)
Lemma dirent64_reclen_nonneg : forall nl, (0 <= dirent64_reclen nl)%Z.
Proof.
  intros nl. unfold dirent64_reclen.
  apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
Qed.

Lemma procfd_total_nonneg : forall es, (0 <= procfd_total es)%Z.
Proof.
  unfold procfd_total. induction es as [|e es IH]; cbn [fold_right]; [lia|].
  pose proof (dirent64_reclen_nonneg (length (pfe_name e))). lia.
Qed.

Lemma procfd_fit_total : forall es room,
  (procfd_total (firstn (procfd_fit es room) es) <= Z.max 0 room)%Z.
Proof.
  unfold procfd_total.
  induction es as [|e es IH]; intros room; cbn [procfd_fit firstn fold_right]; [lia|].
  destruct (dirent64_reclen (length (pfe_name e)) <=? room)%Z eqn:E;
    cbn [firstn fold_right]; [|lia].
  apply Z.leb_le in E.
  specialize (IH (room - dirent64_reclen (length (pfe_name e)))%Z). lia.
Qed.

Lemma sint32_lt : forall w, (sint32 w < 2 ^ 31)%Z.
Proof.
  intros w. unfold sint32. cbv zeta.
  destruct (bv_unsigned (abi_low32 w) <? 2 ^ 31)%Z eqn:E.
  - apply Z.ltb_lt in E. exact E.
  - unfold abi_low32.
    pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ 32) ltac:(lia)) as Hb.
    rewrite bv_unsigned_Z_to_bv_u64 by (unfold two_pow_64; lia).
    lia.
Qed.

Lemma procfd_ret_not_enoent : forall tot,
  (0 <= tot < 2 ^ 31)%Z -> bv_eqb (Z_to_bv 64 tot) (errno_ret ENOENT) = false.
Proof.
  intros tot Ht. destruct (bv_eqb _ _) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E.
  rewrite bv_unsigned_Z_to_bv_u64 in E by (unfold two_pow_64; lia).
  assert (bv_unsigned (errno_ret ENOENT) = 18446744073709551614%Z) as Hn
    by (vm_compute; reflexivity).
  lia.
Qed.

Lemma check_procfd_getdents_not_enoent : forall i fd fl pos dirent count eff m m' evs,
  check_procfd_getdents i fd fl pos dirent count eff m = CheckOk m' evs ->
  bv_eqb (eff_ret eff) (errno_ret ENOENT) = false.
Proof.
  intros i fd fl pos dirent count eff m m' evs H.
  unfold check_procfd_getdents in H.
  destruct pos as [pw|]; [|discriminate H].
  destruct (negb (procfd_in_range (m_fds m) (bv_unsigned pw))); [discriminate H|].
  destruct (procfd_fit (procfd_plan (m_fds m) (bv_unsigned pw)) (getdents64_ctx_count count))
    as [|n'] eqn:Hn;
  destruct (procfd_plan (m_fds m) (bv_unsigned pw)) as [|e es'] eqn:Hes;
  cbv beta iota zeta in H;
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _);
         vm_compute; reflexivity);
    try discriminate H.
  destruct (negb (access_okb dirent (dirent64_reclen (length (pfe_name e)))));
    [apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _);
     vm_compute; reflexivity|].
  match type of H with
  | context [if ?b then _ else CheckUnmodeled] => destruct b; [|discriminate H]
  end.
  destruct eff as [ret wr zs us cs cis];
    destruct zs; [|discriminate H]; destruct us; [|discriminate H];
    destruct cs; [|discriminate H]; destruct cis; [|discriminate H].
  match type of H with
  | context [if ?b then CheckOk _ _ else CheckReject] => destruct b eqn:Hc; [|discriminate H]
  end.
  apply andb_true_iff in Hc as [Hc _]. apply andb_true_iff in Hc as [Hr _].
  apply bv_eqb_eq in Hr. cbn [eff_ret]. rewrite Hr.
  apply procfd_ret_not_enoent.
  pose proof (procfd_fit_total (e :: es') (getdents64_ctx_count count)) as Ht.
  try rewrite Hes in Hn. rewrite Hn in Ht.
  pose proof (procfd_total_nonneg (firstn (S n') (e :: es'))).
  pose proof (sint32_lt count). unfold getdents64_ctx_count in Ht. lia.
Qed.

Lemma getdents64_opaque_not_enoent : forall i fd o dirent count m eff m' evs,
  getdents64_opaque_spec fd o dirent count i m (Ok eff m' evs) ->
  bv_eqb (eff_ret eff) (errno_ret ENOENT) = false.
Proof.
  intros i fd o dirent count m eff m' evs H.
  destruct o; cbn [getdents64_opaque_spec] in H; try (no_unmodeled_ok H).
  apply check_procfd_getdents_complete_ok in H.
  exact (check_procfd_getdents_not_enoent _ _ _ _ _ _ _ _ _ _ H).
Qed.

(** [getdents64] on an opaque descriptor: the /proc/self/fd listing, and
    a decline on every other kind ([Fs.Readdir.getdents64_opaque_spec]). *)
Definition check_getdents64_opaque (i : SyscallInput) (fd : word) (o : OpaqueFd)
    (dirent count : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match o with
  | OProcFdDir fl pos => check_procfd_getdents i fd fl pos dirent count eff m
  | OProcPath _ | OProcFile _ | OEventFd _ | ONsFile _ | OSignalFd _ _ => CheckUnmodeled
  end.

Lemma check_getdents64_opaque_sound_ok : forall i fd o dirent count eff m m' evs,
  check_getdents64_opaque i fd o dirent count eff m = CheckOk m' evs ->
  getdents64_opaque_spec fd o dirent count i m (Ok eff m' evs).
Proof.
  intros i fd o dirent count eff m m' evs H.
  destruct o; cbn [check_getdents64_opaque getdents64_opaque_spec] in *; try discriminate H.
  now apply check_procfd_getdents_sound_ok.
Qed.

Lemma check_getdents64_opaque_sound_unmodeled : forall i fd o dirent count eff m,
  check_getdents64_opaque i fd o dirent count eff m = CheckUnmodeled ->
  getdents64_opaque_spec fd o dirent count i m Unmodeled.
Proof.
  intros i fd o dirent count eff m H.
  destruct o; cbn [check_getdents64_opaque getdents64_opaque_spec] in *;
    try apply unmodeled_intro.
  now apply (check_procfd_getdents_sound_unmodeled i fd _ _ dirent count eff).
Qed.

Lemma check_getdents64_opaque_complete_ok : forall i fd o dirent count eff m m' evs,
  getdents64_opaque_spec fd o dirent count i m (Ok eff m' evs) ->
  check_getdents64_opaque i fd o dirent count eff m = CheckOk m' evs.
Proof.
  intros i fd o dirent count eff m m' evs H.
  destruct o; cbn [check_getdents64_opaque getdents64_opaque_spec] in *;
    try (unfold unmodeled in H; discriminate H).
  now apply check_procfd_getdents_complete_ok.
Qed.

Lemma check_getdents64_opaque_complete_unmodeled : forall i fd o dirent count eff m,
  getdents64_opaque_spec fd o dirent count i m Unmodeled ->
  check_getdents64_opaque i fd o dirent count eff m = CheckUnmodeled.
Proof.
  intros i fd o dirent count eff m H.
  destruct o; cbn [check_getdents64_opaque getdents64_opaque_spec] in *; try reflexivity.
  now apply check_procfd_getdents_complete_unmodeled.
Qed.

(** [getdents64] (61): -EBADF on a closed fd, -ENOTDIR on every fd that
    is not a directory, the /proc/self/fd listing on that directory
    ([check_procfd_getdents]), and on a [FdDir] either -EINVAL or the one
    injectable errno when the buffer cannot hold the smallest possible
    entry.  Every larger buffer on a [FdDir] is [CheckUnmodeled].
    Mirrors [Fs.Readdir.getdents64_spec] arm for arm — read that spec
    for why that listing is declined.

    The non-listing answers are a bare return with FIVE EMPTY LEDGERS:
    the kernel reaches [user_write_access_begin] only after the
    [reclen > ctx->count] test has failed the call, so nothing those arms
    admit writes, zeroes, unmaps or copies a byte.  A kernel that
    claimed a write alongside one of these returns is rejected on the
    ledger rather than on the return value. *)
Definition check_getdents64 (i : SyscallInput) (fd dirent count : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdFile _ _)  => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdFileW _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdFileA _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdFileRW _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdPipe _ _)  => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdSocket _)  => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdDevNull _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some FdUrandom => check_ret_only eff (errno_ret ENOTDIR) m []
  | Some (FdOpaque o) => check_getdents64_opaque i fd o dirent count eff m
  | Some FdDir =>
      if getdents64_no_room count then
        match eff with
        | mkEffectU ret [] [] [] [] [] =>
            if errno_ret_in getdents64_errnos ret then CheckOk m []
            else if bv_eqb ret (errno_ret EINVAL) then CheckOk m []
            else CheckReject
        | _ => CheckReject
        end
      else CheckUnmodeled
  end.

Lemma check_getdents64_sound_ok : forall i fd dirent count eff m m' evs,
  check_getdents64 i fd dirent count eff m = CheckOk m' evs ->
  getdents64_spec fd dirent count i m (Ok eff m' evs).
Proof.
  intros i fd dirent count eff m m' evs H.
  unfold check_getdents64 in H. unfold getdents64_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    try discriminate;
    (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
    (* the five -ENOTDIR arms and the -EBADF one are plain returns *)
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         apply pure_ok).
  (* the opaque kinds *)
  all: try (now apply check_getdents64_opaque_sound_ok).
  (* the directory arm *)
  destruct (getdents64_no_room count) eqn:Hroom; [|discriminate].
  destruct eff as [ret ws zs us cs cis]; destruct ws as [|w ws'];
    [destruct zs as [|z zs']|]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  destruct (errno_ret_in getdents64_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    apply pure_ok.
  - destruct (bv_eqb ret (errno_ret EINVAL)) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq; subst ret.
    apply alt_r. unfold err_ret, ret_only. apply pure_ok.
Qed.

(** The declines are the [FdDir] arm's roomy half — the listing the
    model cannot produce — and the opaque kinds' own.  Inside the
    small-buffer half every effect shape is either accepted or rejected,
    never declined, and so is every non-directory fd. *)
Lemma check_getdents64_sound_unmodeled : forall i fd dirent count eff m,
  check_getdents64 i fd dirent count eff m = CheckUnmodeled ->
  getdents64_spec fd dirent count i m Unmodeled.
Proof.
  intros i fd dirent count eff m H.
  unfold check_getdents64 in H. unfold getdents64_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    try (now apply check_ret_only_no_unmodeled in H);
    (* the opaque kinds *)
    try (eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota; srw Hfd;
         now apply (check_getdents64_opaque_sound_unmodeled i fd _ dirent count eff)).
  eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota; srw Hfd.
  destruct (getdents64_no_room count) eqn:Hroom; [|apply unmodeled_intro].
  exfalso.
  destruct eff as [ret ws zs us cs cis]; destruct ws; [destruct zs|];
    destruct us; destruct cs; destruct cis; try discriminate.
  destruct (errno_ret_in getdents64_errnos ret); [discriminate|].
  destruct (bv_eqb ret (errno_ret EINVAL)); discriminate.
Qed.

Lemma check_getdents64_complete_ok : forall i fd dirent count eff m m' evs,
  getdents64_spec fd dirent count i m (Ok eff m' evs) ->
  check_getdents64 i fd dirent count eff m = CheckOk m' evs.
Proof.
  intros i fd dirent count eff m m' evs H.
  unfold getdents64_spec in H. unfold check_getdents64.
  apply get_model_bind_ok_inv in H. cbv beta in H.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    cbv iota in H.
  (* the opaque kinds *)
  all: try (now apply check_getdents64_opaque_complete_ok).
  (* the directory arm *)
  all: try (destruct (getdents64_no_room count) eqn:Hroom; cbv iota in *;
            [|unfold unmodeled in H; discriminate H];
            unfold getdents64_errnos in *; sys_unfold; cbn [In] in *; inv_ok;
            try contradiction; vm_compute; reflexivity).
  (* the eight plain returns *)
  all: sys_unfold; inv_ok; cbn [check_ret_only]; rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_getdents64_complete_unmodeled : forall i fd dirent count m eff,
  getdents64_spec fd dirent count i m Unmodeled ->
  check_getdents64 i fd dirent count eff m = CheckUnmodeled.
Proof.
  intros i fd dirent count m eff H.
  unfold getdents64_spec in H. unfold check_getdents64.
  apply get_model_bind_unmodeled_inv in H. cbv beta in H.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    cbv iota in H.
  (* the opaque kinds *)
  all: try (now apply check_getdents64_opaque_complete_unmodeled).
  all: try (exfalso; sys_unfold; inv_ok; discriminate).
  destruct (getdents64_no_room count) eqn:Hroom; cbv iota in *;
    [|reflexivity].
  (* Neither arm of the [alt] can be [Unmodeled]: a [choose] bound to a
     [pure] admits only [Ok]. *)
  exfalso. sys_unfold. inv_ok.
Qed.
