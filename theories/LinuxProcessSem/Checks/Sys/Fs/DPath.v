(** * LinuxProcessSem.Checks.Sys.Fs.DPath — the getcwd (17) checker, and its proofs

    Mirrors [Sys/Fs/DPath.v], which answers to Linux [fs/d_path.c]: this
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

(** THE SHAPE OF EVERY getcwd ANSWER BUT THE SUCCESS: a bare return
    with five empty ledgers.  The kernel reaches its single
    [copy_to_user] only after the size comparison has passed, so an
    -ENOMEM, -ENAMETOOLONG, -ERANGE or -EFAULT writes, zeroes, unmaps
    and copies nothing, and a kernel that claimed a write alongside one
    of them is rejected on the LEDGER rather than on the return value.

    [det] is the branch's own deterministic errno; the injectable
    -ENOMEM is admitted beside it on every branch, because
    [__getname()] runs before all of them. *)
Definition check_getcwd_alt (det : Z) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if bv_eqb ret (errno_ret det) || errno_ret_in getcwd_errnos ret
      then CheckOk m []
      else CheckReject
  | _ => CheckReject
  end.

(** Closing a leaf of either completeness proof: the effect is a
    literal by then, so the checker computes on it. *)
Ltac getcwd_leaf :=
  cbn [getcwd_errnos In app] in *; inv_ok;
  unfold check_getcwd_alt;
  cbn [errno_ret_in existsb getcwd_errnos app];
  rewrite ?bv_eqb_refl, ?Bool.orb_true_r, ?Bool.orb_true_l;
  reflexivity.

Lemma check_getcwd_alt_sound_ok : forall det eff m m' evs i,
  check_getcwd_alt det eff m = CheckOk m' evs ->
  alt (e <- errno_from getcwd_errnos ;; err_ret e) (err_ret det)
      i m (Ok eff m' evs).
Proof.
  intros det eff m m' evs i H. unfold check_getcwd_alt in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws as [|w ws'];
    [destruct zs as [|z zs']|]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  destruct (bv_eqb ret (errno_ret det)) eqn:Heq; cbn [orb] in H.
  - inversion H; clear H; subst. apply bv_eqb_eq in Heq; subst ret.
    apply alt_r. unfold err_ret, ret_only. apply pure_ok.
  - destruct (errno_ret_in getcwd_errnos ret) eqn:He; [|discriminate].
    inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    unfold err_ret, ret_only. apply pure_ok.
Qed.

(** Neither arm of the [alt] can be [Unmodeled]: a [choose] bound to a
    [pure] admits only [Ok], and so does [err_ret]. *)
Lemma check_getcwd_alt_no_unmodeled : forall det i m,
  ~ alt (e <- errno_from getcwd_errnos ;; err_ret e) (err_ret det)
        i m Unmodeled.
Proof.
  intros det i m H. sys_unfold. destruct H as [H | H]; inv_ok.
Qed.

Lemma check_getcwd_alt_complete_ok : forall det eff m m' evs i,
  alt (e <- errno_from getcwd_errnos ;; err_ret e) (err_ret det)
      i m (Ok eff m' evs) ->
  check_getcwd_alt det eff m = CheckOk m' evs.
Proof.
  intros det eff m m' evs i H. sys_unfold.
  repeat (destruct H as [H | H]; inv_ok); try contradiction; getcwd_leaf.
Qed.

(** [getcwd] (17).  Mirrors [Fs.DPath.getcwd_spec] branch for branch —
    read that spec for why the working directory decides the answer
    now, for the premise the DECLARED directory carries, and for why
    [buf] is not consulted until the size test has passed.

    THE SUCCESS SHAPE is the path's bytes and one NUL delivered at
    [buf], with the length INCLUDING that NUL as the return value, and
    still no zero, unmap, copy or copy-in ledger entry.  The two
    branches inside it are told apart by the WRITE LEDGER rather than
    by the return value: the delivered string is never empty, so a
    success always carries one write entry and an injected -ENOMEM
    never does. *)
Definition check_getcwd (i : SyscallInput) (buf size : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let cwd := m_cwd m in
  let bs := getcwd_bytes cwd in
  let len := getcwd_len cwd in
  if Nat.ltb path_max len then check_getcwd_alt ENAMETOOLONG eff m
  else if (bv_unsigned size <? Z.of_nat len)%Z then
    check_getcwd_alt ERANGE eff m
  else if negb (access_okb buf (Z.of_nat len)) then
    check_getcwd_alt EFAULT eff m
  else
    match read_bytes_map (in_wmem i) buf (len_word bs) with
    | None => CheckUnmodeled
    | Some _ =>
        match eff with
        | mkEffectU ret [] [] [] [] [] =>
            if errno_ret_in getcwd_errnos ret then CheckOk m []
            else CheckReject
        | mkEffectU ret ws [] [] [] [] =>
            if bv_eqb ret (Z_to_bv 64 (Z.of_nat len))
               && writes_eqb ws (delivered_writes buf bs)
            then CheckOk m []
            else CheckReject
        | _ => CheckReject
        end
    end.

(** The delivered string is never empty — it ends in the terminating
    NUL whatever the working directory is — so the success always
    carries exactly one write-ledger entry. *)
Lemma getcwd_delivered_writes : forall buf cwd,
  delivered_writes buf (getcwd_bytes cwd) = [(buf, getcwd_bytes cwd)].
Proof.
  intros buf cwd. unfold delivered_writes, getcwd_bytes.
  destruct cwd as [|b r]; reflexivity.
Qed.

Lemma check_getcwd_sound_ok : forall i buf size eff m m' evs,
  check_getcwd i buf size eff m = CheckOk m' evs ->
  getcwd_spec buf size i m (Ok eff m' evs).
Proof.
  intros i buf size eff m m' evs H.
  unfold check_getcwd in H. unfold getcwd_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  destruct (Nat.ltb path_max (getcwd_len (m_cwd m))) eqn:Hl; cbv iota;
    [now apply check_getcwd_alt_sound_ok|].
  destruct (bv_unsigned size <? Z.of_nat (getcwd_len (m_cwd m)))%Z eqn:Hs;
    cbv iota; [now apply check_getcwd_alt_sound_ok|].
  destruct (negb (access_okb buf (Z.of_nat (getcwd_len (m_cwd m))))) eqn:Ha;
    cbv iota; [now apply check_getcwd_alt_sound_ok|].
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (getcwd_bytes (m_cwd m)))) as [ok|] eqn:Hr;
    cbv iota; [|discriminate].
  destruct eff as [ret ws zs us cs cis];
    destruct zs as [|z zs']; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?];
    destruct ws as [|w ws']; try discriminate.
  - (* no write: only the injected errno can claim it *)
    destruct (errno_ret_in getcwd_errnos ret) eqn:He; [|discriminate].
    (* the delivery always writes, so it cannot be this shape *)
    inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    unfold err_ret, ret_only. apply pure_ok.
  - (* one or more writes: only the delivery can claim it *)
    destruct (bv_eqb ret (Z_to_bv 64 (Z.of_nat (getcwd_len (m_cwd m)))))
      eqn:Hret; cbn [andb] in H; [|discriminate].
    destruct (writes_eqb (w :: ws')
                (delivered_writes buf (getcwd_bytes (m_cwd m)))) eqn:Hws;
      [|discriminate].
    inversion H; clear H; subst.
    apply bv_eqb_eq in Hret; subst ret.
    apply writes_eqb_eq in Hws. rewrite Hws.
    apply alt_r. apply pure_ok.
Qed.

Lemma check_getcwd_sound_unmodeled : forall i buf size eff m,
  check_getcwd i buf size eff m = CheckUnmodeled ->
  getcwd_spec buf size i m Unmodeled.
Proof.
  intros i buf size eff m H.
  unfold check_getcwd in H. unfold getcwd_spec.
  eapply bind_unmodeled2; [apply input_ok|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
  destruct (Nat.ltb path_max (getcwd_len (m_cwd m))) eqn:Hl; cbv iota;
    [exfalso; unfold check_getcwd_alt in H; destruct eff as [ret ws zs us cs cis];
     destruct ws; [destruct zs|]; destruct us; destruct cs; destruct cis;
     try discriminate;
     destruct (errno_ret_in getcwd_errnos ret); try discriminate;
     destruct (bv_eqb ret (errno_ret ENAMETOOLONG)); discriminate|].
  destruct (bv_unsigned size <? Z.of_nat (getcwd_len (m_cwd m)))%Z eqn:Hs;
    cbv iota;
    [exfalso; unfold check_getcwd_alt in H; destruct eff as [ret ws zs us cs cis];
     destruct ws; [destruct zs|]; destruct us; destruct cs; destruct cis;
     try discriminate;
     destruct (errno_ret_in getcwd_errnos ret); try discriminate;
     destruct (bv_eqb ret (errno_ret ERANGE)); discriminate|].
  destruct (negb (access_okb buf (Z.of_nat (getcwd_len (m_cwd m))))) eqn:Ha;
    cbv iota;
    [exfalso; unfold check_getcwd_alt in H; destruct eff as [ret ws zs us cs cis];
     destruct ws; [destruct zs|]; destruct us; destruct cs; destruct cis;
     try discriminate;
     destruct (errno_ret_in getcwd_errnos ret); try discriminate;
     destruct (bv_eqb ret (errno_ret EFAULT)); discriminate|].
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (getcwd_bytes (m_cwd m)))) as [ok|] eqn:Hr;
    cbv iota; [|apply unmodeled_intro].
  exfalso.
  destruct eff as [ret ws zs us cs cis];
    destruct zs; destruct us; destruct cs; destruct cis;
    destruct ws as [|w ws']; try discriminate.
  - destruct (errno_ret_in getcwd_errnos ret); discriminate.
  - destruct (bv_eqb ret (Z_to_bv 64 (Z.of_nat (getcwd_len (m_cwd m)))));
      cbn [andb] in H; try discriminate.
    destruct (writes_eqb (w :: ws')
                (delivered_writes buf (getcwd_bytes (m_cwd m)))); discriminate.
Qed.

Lemma check_getcwd_complete_ok : forall i buf size eff m m' evs,
  getcwd_spec buf size i m (Ok eff m' evs) ->
  check_getcwd i buf size eff m = CheckOk m' evs.
Proof.
  intros i buf size eff m m' evs H.
  unfold getcwd_spec in H. unfold check_getcwd. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (Nat.ltb path_max (getcwd_len (m_cwd m))) eqn:Hl; hall Hl.
  { inv_ok; getcwd_leaf. }
  destruct (bv_unsigned size <? Z.of_nat (getcwd_len (m_cwd m)))%Z eqn:Hs;
    hall Hs.
  { inv_ok; getcwd_leaf. }
  destruct (negb (access_okb buf (Z.of_nat (getcwd_len (m_cwd m))))) eqn:Ha;
    hall Ha.
  { inv_ok; getcwd_leaf. }
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (getcwd_bytes (m_cwd m)))) as [ok|] eqn:Hr;
    hall Hr; [|inv_ok].
  inv_ok.
  - (* the injected errno: an empty write ledger *)
    cbn [getcwd_errnos In app] in *; inv_ok.
    cbn [errno_ret_in existsb getcwd_errnos app].
    rewrite bv_eqb_refl, Bool.orb_true_l. reflexivity.
  - (* the delivery: one write entry, so the first pattern cannot fire *)
    cbn [app] in *. rewrite getcwd_delivered_writes.
    cbn [errno_ret_in existsb getcwd_errnos app].
    rewrite bv_eqb_refl, Bool.andb_true_l.
    rewrite (proj2 (writes_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma check_getcwd_complete_unmodeled : forall i buf size m eff,
  getcwd_spec buf size i m Unmodeled ->
  check_getcwd i buf size eff m = CheckUnmodeled.
Proof.
  intros i buf size m eff H.
  unfold getcwd_spec in H. unfold check_getcwd. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (Nat.ltb path_max (getcwd_len (m_cwd m))) eqn:Hl; hall Hl;
    [exfalso; inv_ok|].
  destruct (bv_unsigned size <? Z.of_nat (getcwd_len (m_cwd m)))%Z eqn:Hs;
    hall Hs; [exfalso; inv_ok|].
  destruct (negb (access_okb buf (Z.of_nat (getcwd_len (m_cwd m))))) eqn:Ha;
    hall Ha; [exfalso; inv_ok|].
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (getcwd_bytes (m_cwd m)))) as [ok|] eqn:Hr;
    hall Hr; [|reflexivity].
  exfalso. inv_ok.
Qed.
