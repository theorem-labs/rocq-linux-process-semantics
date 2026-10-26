(** * LinuxProcessSem.Checks.Sys.Kernel.Signal — the rt_sigaction (134), rt_sigprocmask (135) and sigaltstack (132) checkers, and their proofs

    Mirrors [Sys/Kernel/Signal.v], which answers to Linux
    [kernel/signal.c]: this file holds the checkers for the syscalls
    defined there, and no others.

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

(** sigaltstack: no arm writes user memory, so every admissible outcome
    is a bare return; the arms after the 24-byte copy of [uss] carry
    that copy in the ledger, and the arms before it, with the copy's own
    -EFAULT, carry none.  Exactly one outcome carries the model forward
    with the alternate-stack bit set, the install.  SS_DISABLE succeeds
    and does NOT set it: the kernel zeroes [ss_size] before the store, so
    the record stays in the shape the arms below can answer from.  The
    declining arms are the ones whose answer would need the user stack
    pointer, or the stored flags word (see [Signal.sigaltstack_spec]). *)
Definition check_sigaltstack (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if m_sigaltstack_installed m then CheckUnmodeled
  else if negb (w_is0 uoss) then CheckUnmodeled
  else if w_is0 uss then check_ret_only eff (Z_to_bv 64 0) m []
  else
    match sigaltstack_at (in_mem i) uss with
    | None => check_ret_only eff (errno_ret EFAULT) m []
    | Some bs =>
        if negb (ss_mode_ok (ss_flags_of bs))
        then check_ret_only_copyins [(uss, Z.to_nat SIGALTSTACK_BYTES)]
               eff (errno_ret EINVAL) m []
        else if ss_disabling (ss_flags_of bs)
        then check_ret_only_copyins [(uss, Z.to_nat SIGALTSTACK_BYTES)]
               eff (Z_to_bv 64 0) m []
        else if (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))%bool
        then CheckUnmodeled
        else if (bv_unsigned (ss_size_of bs) <? MINSIGSTKSZ)%Z
        then check_ret_only_copyins [(uss, Z.to_nat SIGALTSTACK_BYTES)]
               eff (errno_ret ENOMEM) m []
        else check_ret_only_copyins [(uss, Z.to_nat SIGALTSTACK_BYTES)]
               eff (Z_to_bv 64 0) (with_sigaltstack_installed m) []
    end.

Lemma check_sigaltstack_sound_ok : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs ->
  sigaltstack_spec uss uoss i m (Ok eff m' evs).
Proof.
  intros i uss uoss eff m m' evs H.
  unfold check_sigaltstack in H. unfold sigaltstack_spec.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (m_sigaltstack_installed m) eqn:Hw; cbv beta iota; [discriminate|].
  destruct (negb (w_is0 uoss)) eqn:Ho; cbv beta iota; [discriminate|].
  destruct (w_is0 uss) eqn:Hu; cbv beta iota.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (sigaltstack_at (in_mem i) uss) as [bs|] eqn:Hbs; cbv beta iota.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      apply pure_ok. }
  cbv beta iota zeta in H |- *.
  destruct (negb (ss_mode_ok (ss_flags_of bs))) eqn:Hmode; cbv beta iota.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
  destruct (ss_disabling (ss_flags_of bs)) eqn:Hdis; cbv beta iota.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
  destruct (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))%bool eqn:Hzero;
    cbv beta iota; [discriminate|].
  destruct (bv_unsigned (ss_size_of bs) <? MINSIGSTKSZ)%Z eqn:Hsz;
    cbv beta iota.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
  apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
  apply record_copyins_ok_empty; [reflexivity|].
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_sigaltstack_sound_unmodeled : forall i uss uoss eff m,
  check_sigaltstack i uss uoss eff m = CheckUnmodeled ->
  sigaltstack_spec uss uoss i m Unmodeled.
Proof.
  intros i uss uoss eff m H.
  unfold check_sigaltstack in H. unfold sigaltstack_spec.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (m_sigaltstack_installed m) eqn:Hw; cbv beta iota.
  { apply unmodeled_intro. }
  destruct (negb (w_is0 uoss)) eqn:Ho; cbv beta iota.
  { apply unmodeled_intro. }
  destruct (w_is0 uss) eqn:Hu; cbv beta iota.
  { now apply check_ret_only_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (sigaltstack_at (in_mem i) uss) as [bs|] eqn:Hbs; cbv beta iota.
  2:{ now apply check_ret_only_no_unmodeled in H. }
  apply record_copyins_unmodeled. cbv beta iota zeta in H |- *.
  destruct (negb (ss_mode_ok (ss_flags_of bs))) eqn:Hmode; cbv beta iota.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (ss_disabling (ss_flags_of bs)) eqn:Hdis; cbv beta iota.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))%bool eqn:Hzero;
    cbv beta iota.
  { apply unmodeled_intro. }
  destruct (bv_unsigned (ss_size_of bs) <? MINSIGSTKSZ)%Z eqn:Hsz;
    cbv beta iota; now apply check_ret_only_copyins_no_unmodeled in H.
Qed.

Lemma check_sigaltstack_complete_ok : forall i uss uoss eff m m' evs,
  sigaltstack_spec uss uoss i m (Ok eff m' evs) ->
  check_sigaltstack i uss uoss eff m = CheckOk m' evs.
Proof.
  intros i uss uoss eff m m' evs H.
  unfold sigaltstack_spec in H. unfold check_sigaltstack. sys_unfold.
  inv_ok.
  destruct (m_sigaltstack_installed m) eqn:Hw; cbv beta iota in *; [inv_ok|].
  destruct (negb (w_is0 uoss)) eqn:Ho; cbv beta iota in *; [inv_ok|].
  destruct (w_is0 uss) eqn:Hu; cbv beta iota in *.
  { inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
  inv_ok.
  destruct (sigaltstack_at (in_mem i) uss) as [bs|] eqn:Hbs;
    cbv beta iota in *.
  2:{ inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (negb (ss_mode_ok (ss_flags_of bs))) eqn:Hmode;
    cbv beta iota in *.
  { inv_ok. apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (ss_disabling (ss_flags_of bs)) eqn:Hdis; cbv beta iota in *.
  { inv_ok. apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))%bool eqn:Hzero;
    cbv beta iota in *; [inv_ok|].
  destruct (bv_unsigned (ss_size_of bs) <? MINSIGSTKSZ)%Z eqn:Hsz;
    cbv beta iota in *; inv_ok;
    apply check_ret_only_copyins_ok_iff; now repeat split.
Qed.

Lemma check_sigaltstack_complete_unmodeled : forall i uss uoss m eff,
  sigaltstack_spec uss uoss i m Unmodeled ->
  check_sigaltstack i uss uoss eff m = CheckUnmodeled.
Proof.
  intros i uss uoss m eff H.
  unfold sigaltstack_spec in H. unfold check_sigaltstack. sys_unfold.
  inv_ok.
  destruct (m_sigaltstack_installed m) eqn:Hw; cbv beta iota in *;
    [reflexivity|].
  destruct (negb (w_is0 uoss)) eqn:Ho; cbv beta iota in *; [reflexivity|].
  destruct (w_is0 uss) eqn:Hu; cbv beta iota in *; [inv_ok|].
  inv_ok.
  destruct (sigaltstack_at (in_mem i) uss) as [bs|] eqn:Hbs;
    cbv beta iota in *; [|inv_ok].
  destruct (negb (ss_mode_ok (ss_flags_of bs))) eqn:Hmode;
    cbv beta iota in *; [inv_ok|].
  destruct (ss_disabling (ss_flags_of bs)) eqn:Hdis; cbv beta iota in *;
    [inv_ok|].
  destruct (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))%bool eqn:Hzero;
    cbv beta iota in *; [reflexivity|].
  destruct (bv_unsigned (ss_size_of bs) <? MINSIGSTKSZ)%Z eqn:Hsz;
    cbv beta iota in *; inv_ok.
Qed.

(** rt_sigaction: every admissible outcome is a bare return.  The arms
    after the 24-byte copy of [act] carry that copy in the ledger; the
    arms before it, and the -EFAULT of the copy itself, carry none.  The
    declining arms are the ones whose answer would need a stored
    disposition (see [Signal.rt_sigaction_spec]). *)
Definition check_rt_sigaction (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (bv_eqb ss (Z_to_bv 64 8))
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (w_is0 oact) then CheckUnmodeled
  else if w_is0 act
  then (if sig_valid sig then check_ret_only eff (Z_to_bv 64 0) m []
        else check_ret_only eff (errno_ret EINVAL) m [])
  else
    match sigaction_flags (in_mem i) act with
    | None => check_ret_only eff (errno_ret EFAULT) m []
    | Some fl =>
        if negb (sig_valid sig)
        then check_ret_only_copyins [(act, 24%nat)] eff (errno_ret EINVAL) m []
        else if sig_kernel_only sig
        then check_ret_only_copyins [(act, 24%nat)] eff (errno_ret EINVAL) m []
        else if negb (sa_flags_ok fl) then CheckUnmodeled
        else if sigaction_accepted sig
        then check_ret_only_copyins [(act, 24%nat)] eff (Z_to_bv 64 0) m []
        else CheckUnmodeled
    end.

Lemma check_rt_sigaction_sound_ok : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs ->
  rt_sigaction_spec sig act oact ss i m (Ok eff m' evs).
Proof.
  intros i sig act oact ss eff m m' evs H.
  unfold check_rt_sigaction in H. unfold rt_sigaction_spec.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))) eqn:Hss; cbv beta iota.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (w_is0 oact)) eqn:Ho; cbv beta iota; [discriminate|].
  destruct (w_is0 act) eqn:Hact; cbv beta iota.
  { destruct (sig_valid sig) eqn:Hv; cbv beta iota;
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      apply pure_ok. }
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (sigaction_flags (in_mem i) act) as [fl|] eqn:Hfl; cbv beta iota.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      apply pure_ok. }
  destruct (negb (sig_valid sig)) eqn:Hv; cbv beta iota.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
  destruct (sig_kernel_only sig) eqn:Hk; cbv beta iota.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
  destruct (negb (sa_flags_ok fl)) eqn:Hfo; cbv beta iota; [discriminate|].
  destruct (sigaction_accepted sig) eqn:Ha; cbv beta iota; [|discriminate].
  apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
  apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
Qed.

Lemma check_rt_sigaction_sound_unmodeled : forall i sig act oact ss eff m,
  check_rt_sigaction i sig act oact ss eff m = CheckUnmodeled ->
  rt_sigaction_spec sig act oact ss i m Unmodeled.
Proof.
  intros i sig act oact ss eff m H.
  unfold check_rt_sigaction in H. unfold rt_sigaction_spec.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))) eqn:Hss; cbv beta iota.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (w_is0 oact)) eqn:Ho; cbv beta iota.
  { apply unmodeled_intro. }
  destruct (w_is0 act) eqn:Hact; cbv beta iota.
  { destruct (sig_valid sig) eqn:Hv; cbv beta iota;
      now apply check_ret_only_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (sigaction_flags (in_mem i) act) as [fl|] eqn:Hfl; cbv beta iota.
  2:{ now apply check_ret_only_no_unmodeled in H. }
  apply record_copyins_unmodeled.
  destruct (negb (sig_valid sig)) eqn:Hv; cbv beta iota.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (sig_kernel_only sig) eqn:Hk; cbv beta iota.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (negb (sa_flags_ok fl)) eqn:Hfo; cbv beta iota.
  { apply unmodeled_intro. }
  destruct (sigaction_accepted sig) eqn:Ha; cbv beta iota.
  - now apply check_ret_only_copyins_no_unmodeled in H.
  - apply unmodeled_intro.
Qed.

Lemma check_rt_sigaction_complete_ok : forall i sig act oact ss eff m m' evs,
  rt_sigaction_spec sig act oact ss i m (Ok eff m' evs) ->
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs.
Proof.
  intros i sig act oact ss eff m m' evs H.
  unfold rt_sigaction_spec in H. unfold check_rt_sigaction. sys_unfold.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))) eqn:Hss; cbv beta iota in *.
  { inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (negb (w_is0 oact)) eqn:Ho; cbv beta iota in *; [inv_ok|].
  destruct (w_is0 act) eqn:Hact; cbv beta iota in *.
  { destruct (sig_valid sig) eqn:Hv; cbv beta iota in *; inv_ok;
      cbn; rewrite bv_eqb_refl; reflexivity. }
  inv_ok.
  destruct (sigaction_flags (in_mem i) act) as [fl|] eqn:Hfl;
    cbv beta iota in *.
  2:{ inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (negb (sig_valid sig)) eqn:Hv; cbv beta iota in *.
  { inv_ok. apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (sig_kernel_only sig) eqn:Hk; cbv beta iota in *.
  { inv_ok. apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (negb (sa_flags_ok fl)) eqn:Hfo; cbv beta iota in *; [inv_ok|].
  destruct (sigaction_accepted sig) eqn:Ha; cbv beta iota in *; inv_ok.
  apply check_ret_only_copyins_ok_iff. now repeat split.
Qed.

Lemma check_rt_sigaction_complete_unmodeled : forall i sig act oact ss m eff,
  rt_sigaction_spec sig act oact ss i m Unmodeled ->
  check_rt_sigaction i sig act oact ss eff m = CheckUnmodeled.
Proof.
  intros i sig act oact ss m eff H.
  unfold rt_sigaction_spec in H. unfold check_rt_sigaction. sys_unfold.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))) eqn:Hss; cbv beta iota in *;
    [inv_ok|].
  destruct (negb (w_is0 oact)) eqn:Ho; cbv beta iota in *; [reflexivity|].
  destruct (w_is0 act) eqn:Hact; cbv beta iota in *.
  { destruct (sig_valid sig) eqn:Hv; cbv beta iota in *; inv_ok. }
  inv_ok.
  destruct (sigaction_flags (in_mem i) act) as [fl|] eqn:Hfl;
    cbv beta iota in *; [|inv_ok].
  destruct (negb (sig_valid sig)) eqn:Hv; cbv beta iota in *; [inv_ok|].
  destruct (sig_kernel_only sig) eqn:Hk; cbv beta iota in *; [inv_ok|].
  destruct (negb (sa_flags_ok fl)) eqn:Hfo; cbv beta iota in *;
    [reflexivity|].
  destruct (sigaction_accepted sig) eqn:Ha; cbv beta iota in *;
    [inv_ok|reflexivity].
Qed.

(** An effect that is exactly one write and nothing else, in the shape
    [check_ret_only] has for an effect that is nothing at all.  Local to
    this file because one syscall produces that shape; it moves to
    [Checks.Sys.Prelude] when a second one does. *)
Definition check_one_write (eff : SyscallEffect) (r a : word)
    (bs : list byte) (m' : Model) : check_result :=
  match eff with
  | mkEffectU ret ws [] [] [] [] =>
      if bv_eqb ret r && writes_eqb ws [(a, bs)]
      then CheckOk m' [] else CheckReject
  | _ => CheckReject
  end.

Lemma check_one_write_ok_iff : forall eff r a bs m1 m' evs,
  check_one_write eff r a bs m1 = CheckOk m' evs <->
  (eff = mkEffect r [(a, bs)] [] /\ m' = m1 /\ evs = []).
Proof.
  intros [ret ws zs us cs cin] r a bs m1 m' evs; cbn.
  destruct zs as [|z zs];
    [destruct us as [|u us];
      [destruct cs as [|c cs]; [destruct cin as [|d cin]|]|]|];
    try (split; [discriminate|intros (H1 & _ & _); discriminate H1]).
  destruct (bv_eqb ret r) eqn:E; cbn.
  - apply bv_eqb_eq in E; subst.
    destruct (writes_eqb ws [(a, bs)]) eqn:W.
    + apply writes_eqb_eq in W; subst.
      split; [intro H; inversion H; auto|intros (_ & -> & ->); reflexivity].
    + split; [discriminate|]. intros (H1 & _ & _). inversion H1; subst.
      now rewrite (proj2 (writes_eqb_eq _ _) eq_refl) in W.
  - split; [discriminate|]. intros (H1 & _ & _). inversion H1; subst.
    now rewrite bv_eqb_refl in E.
Qed.

(** The [oset] copy-out acceptor, mirroring [Kernel.Signal.write_oset]
    arm for arm and testing the same booleans in the same order —
    [State.access_okb] BEFORE the [in_wmem] walk, because the walk wraps
    at 2^64 and the range test does not.

    Both answering arms demand an empty copy-in ledger, which is what
    [write_oset] itself produces; the callers that run it under a
    [Syscall.record_copyins] use [check_write_oset_copyins] below. *)
Definition check_write_oset (i : SyscallInput) (oset old : word)
    (eff : SyscallEffect) (m' : Model) : check_result :=
  if negb (access_okb oset NSIG_BYTES)
  then check_ret_only eff (errno_ret EFAULT) m' []
  else
    match read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES) with
    | None => CheckUnmodeled
    | Some _ =>
        check_one_write eff (Z_to_bv 64 0) oset
          (Z_to_le_bytes (Z.to_nat NSIG_BYTES) (bv_unsigned old)) m'
    end.

(** The same, under a recorded copy-in ledger.  [check_ret_only_copyins]
    stands to [check_ret_only] exactly as this stands to
    [check_write_oset], and for the same reason: the ledger is attached
    outside the arm that produced the effect. *)
Definition check_write_oset_copyins (reads : list (word * nat))
    (i : SyscallInput) (oset old : word) (eff : SyscallEffect) (m' : Model)
    : check_result :=
  match check_write_oset i oset old (clear_copyins eff) m' with
  | CheckOk m'' evs =>
      if access_ranges_eqb (eff_copyins eff) reads
      then CheckOk m'' evs else CheckReject
  | result => result
  end.

Lemma check_write_oset_ok_iff : forall i oset old eff m1 m' evs,
  check_write_oset i oset old eff m1 = CheckOk m' evs <->
  (m' = m1 /\ evs = [] /\ eff_copyins eff = [] /\
   write_oset oset old i m1 (Ok eff m1 [])).
Proof.
  intros i oset old eff m1 m' evs.
  unfold check_write_oset, write_oset.
  destruct (negb (access_okb oset NSIG_BYTES)) eqn:Ha; cbv beta iota.
  { rewrite check_ret_only_ok_iff. split.
    - intros (-> & -> & ->).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      apply pure_ok.
    - intros (-> & -> & _ & H).
      unfold err_ret, ret_only, pure in H. inversion H; subst.
      split; [reflexivity|]. split; [reflexivity|]. reflexivity. }
  destruct (read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES)) eqn:Hw.
  - rewrite check_one_write_ok_iff. split.
    + intros (-> & -> & ->).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      eapply bind_ok0; [apply input_ok|]. cbv beta. rewrite Hw. apply pure_ok.
    + intros (-> & -> & _ & H).
      destruct H as (i' & m2 & evs1 & evs2 & Hi & Hk & Hev).
      unfold input in Hi. inversion Hi; subst. cbn in Hk.
      rewrite Hw in Hk. unfold pure in Hk. inversion Hk; subst.
      split; [reflexivity|]. split; [reflexivity|]. reflexivity.
  - split; [discriminate|]. intros (-> & -> & _ & H).
    destruct H as (i' & m2 & evs1 & evs2 & Hi & Hk & _).
    unfold input in Hi. inversion Hi; subst. cbn in Hk.
    rewrite Hw in Hk. unfold unmodeled in Hk. discriminate Hk.
Qed.

Lemma check_write_oset_no_ok_unmodeled : forall i oset old eff m1,
  check_write_oset i oset old eff m1 = CheckUnmodeled ->
  forall m, write_oset oset old i m Unmodeled.
Proof.
  intros i oset old eff m1 H m.
  unfold check_write_oset in H. unfold write_oset.
  destruct (negb (access_okb oset NSIG_BYTES)) eqn:Ha; cbv beta iota.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES)) eqn:Hw.
  - unfold check_one_write in H.
    destruct eff as [ret ws zs us cs cin];
      destruct zs, us, cs, cin; try discriminate;
      destruct (bv_eqb ret (Z_to_bv 64 0) && writes_eqb ws _); discriminate.
  - eapply bind_unmodeled2; [apply input_ok|]. cbv beta. rewrite Hw.
    apply unmodeled_intro.
Qed.

(** rt_sigprocmask's acceptor, mirroring
    [Kernel.Signal.rt_sigprocmask_spec].

    The arms that answer WITHOUT touching [oset] still use
    [check_ret_only], which demands all five effect lists be empty — so
    an effect claiming a write on the bad-size -EINVAL, or on the [nset]
    -EFAULT, is rejected rather than accepted as an inert errno.  That
    is what separates the two -EFAULTs this syscall can return: the one
    raised by [copy_from_user] writes nothing and RECORDS nothing, and
    the one raised by [copy_to_user] writes nothing and records the
    eight bytes it had already read. *)
Definition check_rt_sigprocmask (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let old := m_sigmask m in
    if w_is0 nset
    then (if w_is0 oset then check_ret_only eff (Z_to_bv 64 0) m []
          else check_write_oset i oset old eff m)
    else
      match sigset_at (in_mem i) nset with
      | None => check_ret_only eff (errno_ret EFAULT) m []
      | Some raw =>
          if negb (how_valid how)
          then check_ret_only_copyins [(nset, Z.to_nat NSIG_BYTES)]
                 eff (errno_ret EINVAL) m []
          else
            let m' := sigmask_deliver_model
                        (sigmask_apply how old (sigmask_strip raw)) m in
            if w_is0 oset
            then check_ret_only_copyins [(nset, Z.to_nat NSIG_BYTES)]
                   eff (Z_to_bv 64 0) m' []
            else check_write_oset_copyins [(nset, Z.to_nat NSIG_BYTES)]
                   i oset old eff m'
      end.

(** The two shapes [write_oset] can produce, accepted.  They are what
    the completeness proof's leaves reduce to, and naming them keeps
    that proof readable instead of six copies of the same [cbn]. *)
Lemma check_write_oset_efault : forall i oset old m,
  negb (access_okb oset NSIG_BYTES) = true ->
  check_write_oset i oset old (mkEffect (errno_ret EFAULT) [] []) m
  = CheckOk m [].
Proof.
  intros i oset old m Ha. unfold check_write_oset. rewrite Ha.
  apply check_ret_only_ok_iff. now repeat split.
Qed.

Lemma check_write_oset_stored : forall i oset old m bs,
  negb (access_okb oset NSIG_BYTES) = false ->
  read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES) = Some bs ->
  check_write_oset i oset old
    (mkEffect (Z_to_bv 64 0)
       [(oset, Z_to_le_bytes (Z.to_nat NSIG_BYTES) (bv_unsigned old))] []) m
  = CheckOk m [].
Proof.
  intros i oset old m bs Ha Hw. unfold check_write_oset. rewrite Ha, Hw.
  apply check_one_write_ok_iff. now repeat split.
Qed.

(** [check_write_oset_copyins] discharged from its two parts: the arm's
    own verdict and the ledger.  The same shape [check_ret_only_copyins]
    has, and it exists so the completeness proof never has to reduce
    through [clear_copyins] by hand. *)
Lemma check_write_oset_copyins_ok : forall reads i oset old eff m,
  check_write_oset i oset old (clear_copyins eff) m = CheckOk m [] ->
  eff_copyins eff = reads ->
  check_write_oset_copyins reads i oset old eff m = CheckOk m [].
Proof.
  intros reads i oset old eff m H Hc.
  unfold check_write_oset_copyins. rewrite H, Hc.
  now rewrite (proj2 (access_ranges_eqb_eq reads reads) eq_refl).
Qed.

Lemma check_rt_sigprocmask_sound_ok : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs ->
  rt_sigprocmask_spec how nset oset ss i m (Ok eff m' evs).
Proof.
  intros i how nset oset ss eff m m' evs H.
  unfold check_rt_sigprocmask in H. unfold rt_sigprocmask_spec.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss; cbv beta iota.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  cbv beta iota zeta in H.
  destruct (w_is0 nset) eqn:Hn; cbv beta iota.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota.
    - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      apply pure_ok.
    - apply check_write_oset_ok_iff in H.
      destruct H as (-> & -> & _ & Hspec). exact Hspec. }
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr; cbv beta iota.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      apply pure_ok. }
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|apply pure_ok]. }
  destruct (w_is0 oset) eqn:Ho; cbv beta iota.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|].
    eapply bind_ok0; [apply modify_ok|]. cbv beta. apply pure_ok. }
  unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset (m_sigmask m) (clear_copyins eff)
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m)
                               (sigmask_strip raw)) m))
    as [m2 evs2| |] eqn:Hcw; [|discriminate|discriminate].
  destruct (access_ranges_eqb (eff_copyins eff)
              [(nset, Z.to_nat NSIG_BYTES)]) eqn:Hled; [|discriminate].
  apply access_ranges_eqb_eq in Hled.
  apply check_write_oset_ok_iff in Hcw.
  destruct Hcw as (-> & -> & Hcin & Hspec). inversion H; subst m' evs.
  replace eff with (with_copyins [(nset, Z.to_nat NSIG_BYTES)]
                      (clear_copyins eff))
    by (unfold clear_copyins, with_copyins; destruct eff; cbn in Hled |- *;
        now rewrite Hled).
  apply record_copyins_ok_empty; [exact Hcin|].
  eapply bind_ok0; [apply modify_ok|]. cbv beta. exact Hspec.
Qed.

Lemma check_rt_sigprocmask_sound_unmodeled : forall i how nset oset ss eff m,
  check_rt_sigprocmask i how nset oset ss eff m = CheckUnmodeled ->
  rt_sigprocmask_spec how nset oset ss i m Unmodeled.
Proof.
  intros i how nset oset ss eff m H.
  unfold check_rt_sigprocmask in H. unfold rt_sigprocmask_spec.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss; cbv beta iota.
  { now apply check_ret_only_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
  cbv beta iota zeta in H.
  destruct (w_is0 nset) eqn:Hn; cbv beta iota.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota.
    - now apply check_ret_only_no_unmodeled in H.
    - eapply check_write_oset_no_ok_unmodeled; exact H. }
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr; cbv beta iota.
  2:{ now apply check_ret_only_no_unmodeled in H. }
  apply record_copyins_unmodeled.
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (w_is0 oset) eqn:Ho; cbv beta iota.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply modify_ok|]. cbv beta.
  unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset (m_sigmask m) (clear_copyins eff)
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m)
                               (sigmask_strip raw)) m))
    as [m2 evs2| |] eqn:Hcw.
  - destruct (access_ranges_eqb (eff_copyins eff)
                [(nset, Z.to_nat NSIG_BYTES)]); discriminate.
  - discriminate.
  - eapply check_write_oset_no_ok_unmodeled; exact Hcw.
Qed.

Lemma check_rt_sigprocmask_complete_ok : forall i how nset oset ss eff m m' evs,
  rt_sigprocmask_spec how nset oset ss i m (Ok eff m' evs) ->
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs.
Proof.
  intros i how nset oset ss eff m m' evs H.
  unfold rt_sigprocmask_spec in H. unfold check_rt_sigprocmask.
  unfold write_oset in H. sys_unfold.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss;
    cbv beta iota in *.
  { inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
  inv_ok. cbv beta iota zeta in *.
  destruct (w_is0 nset) eqn:Hn; cbv beta iota in *.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota in *.
    { inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
    destruct (negb (access_okb oset NSIG_BYTES)) eqn:Ha;
      cbv beta iota in *.
    { inv_ok. now apply check_write_oset_efault. }
    inv_ok.
    destruct (read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES))
      as [bs|] eqn:Hw; cbv beta iota in *; [|inv_ok].
    inv_ok. now apply (check_write_oset_stored _ _ _ _ bs). }
  inv_ok.
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr; cbv beta iota in *.
  2:{ inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta in *.
  { inv_ok. apply check_ret_only_copyins_ok_iff. now repeat split. }
  inv_ok.
  destruct (w_is0 oset) eqn:Ho; cbv beta iota in *.
  { inv_ok. apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (negb (access_okb oset NSIG_BYTES)) eqn:Ha;
    cbv beta iota in *.
  { inv_ok. apply check_write_oset_copyins_ok; [|reflexivity].
    unfold clear_copyins, with_copyins. cbn.
    now apply check_write_oset_efault. }
  inv_ok.
  destruct (read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES))
    as [bs|] eqn:Hw; cbv beta iota in *; [|inv_ok].
  inv_ok. apply check_write_oset_copyins_ok; [|reflexivity].
  unfold clear_copyins, with_copyins. cbn.
  now apply (check_write_oset_stored _ _ _ _ bs).
Qed.

Lemma check_rt_sigprocmask_complete_unmodeled : forall i how nset oset ss m eff,
  rt_sigprocmask_spec how nset oset ss i m Unmodeled ->
  check_rt_sigprocmask i how nset oset ss eff m = CheckUnmodeled.
Proof.
  intros i how nset oset ss m eff H.
  unfold rt_sigprocmask_spec in H. unfold check_rt_sigprocmask.
  unfold write_oset in H. sys_unfold.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss;
    cbv beta iota in *; [inv_ok|].
  inv_ok. cbv beta iota zeta in *.
  destruct (w_is0 nset) eqn:Hn; cbv beta iota in *.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota in *; [inv_ok|].
    destruct (negb (access_okb oset NSIG_BYTES)) eqn:Ha;
      cbv beta iota in *; [inv_ok|].
    inv_ok.
    destruct (read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES))
      as [bs|] eqn:Hw; cbv beta iota in *; [inv_ok|].
    unfold check_write_oset. rewrite Ha, Hw. reflexivity. }
  inv_ok.
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr;
    cbv beta iota in *; [|inv_ok].
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta in *; [inv_ok|].
  inv_ok.
  destruct (w_is0 oset) eqn:Ho; cbv beta iota in *; [inv_ok|].
  unfold check_write_oset_copyins.
  destruct (negb (access_okb oset NSIG_BYTES)) eqn:Ha;
    cbv beta iota in *; [inv_ok|].
  inv_ok.
  destruct (read_bytes_map (in_wmem i) oset (Z_to_bv 64 NSIG_BYTES))
    as [bs|] eqn:Hw; cbv beta iota in *; [inv_ok|].
  unfold check_write_oset. rewrite Ha, Hw. reflexivity.
Qed.

(** [Kernel.Signal.mask_launchable] carried across a whole run, which is
    what makes [Run.valid_sigmask] a property of every reachable state
    and not only of the entry one.  Its two halves are proved where the
    arithmetic lives; this is the step that says the checker has no
    other way to move the field.

    It matters because [oset] copies the mask out verbatim: a reachable
    state with SIGKILL or SIGSTOP set would put a trace in the model
    that Linux cannot produce, which is the second of the three
    priorities rather than the first. *)
Lemma check_rt_sigprocmask_keeps_mask_launchable :
  forall i how nset oset ss eff m m' evs,
  mask_launchable (m_sigmask m) ->
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs ->
  mask_launchable (m_sigmask m').
Proof.
  intros i how nset oset ss eff m m' evs Hm H.
  unfold check_rt_sigprocmask in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss;
    cbv beta iota zeta in H.
  { apply check_ret_only_ok_iff in H. destruct H as (_ & -> & _). exact Hm. }
  destruct (w_is0 nset) eqn:Hn; cbv beta iota in H.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
    - apply check_ret_only_ok_iff in H. destruct H as (_ & -> & _). exact Hm.
    - apply check_write_oset_ok_iff in H.
      destruct H as (-> & _ & _ & _). exact Hm. }
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr; cbv beta iota in H.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (_ & -> & _). exact Hm. }
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta in H.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & _).
    exact Hm. }
  assert (Hinst : mask_launchable
            (m_sigmask (sigmask_deliver_model
               (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m))).
  { rewrite m_sigmask_sigmask_deliver_model.
    apply sigmask_apply_launchable; [exact Hm | apply sigmask_strip_launchable]. }
  destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & _).
    exact Hinst. }
  unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset (m_sigmask m) (clear_copyins eff)
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m)
                               (sigmask_strip raw)) m))
    as [m2 evs2| |] eqn:Hcw; [|discriminate|discriminate].
  destruct (access_ranges_eqb (eff_copyins eff)
              [(nset, Z.to_nat NSIG_BYTES)]); [|discriminate].
  apply check_write_oset_ok_iff in Hcw. destruct Hcw as (-> & _ & _ & _).
  inversion H; subst. exact Hinst.
Qed.

(** The framing statement in the shape [Checks.VmMapsDisjoint]'s
    [check_syscall_preserves_vm_wf] cascade consumes, so the arm can be
    discharged there by naming this lemma and nothing else.

    IT IS STATED HERE RATHER THAN THERE because the arm CHANGES the
    model, so the cascade's generic [vm_frame2] cannot close it: that
    tactic reduces through the checker combinators it knows, and this
    checker's [check_write_oset] and [check_one_write] are not among
    them.  The proof needs [check_write_oset_ok_iff], which lives here.

    The arm does not hand back the very model it was given, but what
    the rest of the tree consumes is only the VM half, and that is
    true by construction — the model changes only inside
    [ProcState], through [State.with_sigmask] and, on the delivery
    branch, [State.with_killed] over it; both rebuild that record alone
    and carry every other subsystem across
    ([Kernel.Signal.m_vmmaps_sigmask_deliver_model]). *)
Lemma check_rt_sigprocmask_frame : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i how nset oset ss eff m m' evs H.
  unfold check_rt_sigprocmask in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss;
    cbv beta iota zeta in H.
  { apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (w_is0 nset) eqn:Hn; cbv beta iota in H.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
    - apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _).
    - apply check_write_oset_ok_iff in H. now destruct H as (-> & _ & _ & _). }
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr; cbv beta iota in H.
  2:{ apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta in H.
  { apply check_ret_only_copyins_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & _).
    now rewrite m_vmmaps_sigmask_deliver_model. }
  unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset (m_sigmask m) (clear_copyins eff)
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m)
                               (sigmask_strip raw)) m))
    as [m2 evs2| |] eqn:Hcw; [|discriminate|discriminate].
  destruct (access_ranges_eqb (eff_copyins eff)
              [(nset, Z.to_nat NSIG_BYTES)]); [|discriminate].
  apply check_write_oset_ok_iff in Hcw. destruct Hcw as (-> & _ & _ & _).
  inversion H; subst. now rewrite m_vmmaps_sigmask_deliver_model.
Qed.

(* =========================================================================
   tkill (130) and tgkill (131)
   ========================================================================= *)

(** The acceptor mirrors the spec's branches.  Two things are worth
    naming rather than reading off the code.

    THE EFFECT SHAPE IS EMPTY on every branch: neither call writes user
    memory, zeroes or unmaps anything, or copies anything in.  A claimed
    write is therefore a reject rather than a decline, so an effect
    that forges one fails.

    THE FATAL BRANCH STILL CLAIMS 0.  The syscall's own return value is
    what a kernel would have put in a0 had the process lived; the process
    does not, and [Run.sstep_killed] discards the effect.  Requiring the
    0 here rather than admitting anything keeps the acceptor total on the
    shape and costs nothing: no trace can distinguish the two. *)
Definition check_send_sigabrt (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if negb (bv_eqb ret (Z_to_bv 64 0)) then CheckReject
      else if sigabrt_blocked (m_sigmask m)
      then CheckOk (with_sigabrt_pending m) []
      else CheckOk (with_killed (Z_to_bv 64 SIGABRT) m) []
  | _ => CheckReject
  end.

Definition check_tkill_self (pid sig : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (m_abort_terminal m) then CheckUnmodeled
  else
    match m_tid m with
    | None => CheckUnmodeled
    | Some t =>
        if negb (bv_eqb pid t) then CheckUnmodeled
        else if negb (tkill_sig_valid sig)
        then check_ret_only eff (errno_ret EINVAL) m []
        else if bv_eqb sig (Z_to_bv 64 SIGABRT) then check_send_sigabrt eff m
        else CheckUnmodeled
    end.

Definition check_tkill (pid sig : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (m_abort_terminal m) then CheckUnmodeled
  else if negb (pid_positive pid)
  then check_ret_only eff (errno_ret EINVAL) m []
  else check_tkill_self pid sig eff m.

Definition check_tgkill (tgid pid sig : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (m_abort_terminal m) then CheckUnmodeled
  else if negb (pid_positive pid && pid_positive tgid)%bool
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    match m_tid m with
    | None => CheckUnmodeled
    | Some t =>
        if negb (bv_eqb pid t) then CheckUnmodeled
        else if negb (bv_eqb tgid t)
        then check_ret_only eff (errno_ret ESRCH) m []
        else check_tkill_self pid sig eff m
    end.

Lemma check_send_sigabrt_sound_ok : forall eff m m' evs i,
  check_send_sigabrt eff m = CheckOk m' evs -> send_sigabrt i m (Ok eff m' evs).
Proof.
  intros [ret ws zs us cs copyins] m m' evs i H.
  unfold check_send_sigabrt in H. unfold send_sigabrt.
  destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  destruct (negb (bv_eqb ret (Z_to_bv 64 0))) eqn:Hr; [discriminate|].
  apply Bool.negb_false_iff, bv_eqb_eq in Hr. subst ret.
  rewrite bind_get_model.
  destruct (sigabrt_blocked (m_sigmask m)) eqn:Hb; cbv beta iota;
    inversion H; clear H; subst;
    (eapply bind_ok0;
     [ unfold set_sigabrt_pending, set_killed; apply modify_ok
     | unfold ret_only; apply pure_ok ]).
Qed.

Lemma check_send_sigabrt_no_unmodeled : forall eff m,
  check_send_sigabrt eff m <> CheckUnmodeled.
Proof.
  intros [ret ws zs us cs copyins] m.
  unfold check_send_sigabrt.
  destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  destruct (negb (bv_eqb ret (Z_to_bv 64 0))); [discriminate|].
  destruct (sigabrt_blocked (m_sigmask m)); discriminate.
Qed.

Lemma check_send_sigabrt_complete_ok : forall eff m m' evs i,
  send_sigabrt i m (Ok eff m' evs) -> check_send_sigabrt eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H. unfold send_sigabrt in H.
  rewrite bind_get_model in H.
  unfold check_send_sigabrt.
  destruct (sigabrt_blocked (m_sigmask m)) eqn:Hb; cbv beta iota in H;
    sys_unfold; inv_ok; cbv beta iota;
    rewrite bv_eqb_refl; cbv beta iota; try rewrite Hb; reflexivity.
Qed.

Lemma check_send_sigabrt_complete_unmodeled : forall m i eff,
  send_sigabrt i m Unmodeled -> check_send_sigabrt eff m = CheckUnmodeled.
Proof.
  intros m i eff H. exfalso. unfold send_sigabrt in H.
  rewrite bind_get_model in H.
  destruct (sigabrt_blocked (m_sigmask m)); cbv beta iota in H;
    sys_unfold; inv_ok.
Qed.

Lemma check_tkill_self_sound_ok : forall pid sig eff m m' evs i,
  check_tkill_self pid sig eff m = CheckOk m' evs ->
  tkill_self pid sig i m (Ok eff m' evs).
Proof.
  intros pid sig eff m m' evs i H.
  unfold check_tkill_self in H. unfold tkill_self. rewrite bind_get_model.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *; [discriminate|].
  destruct (m_tid m) as [t|]; cbv beta iota in *; [|discriminate].
  destruct (negb (bv_eqb pid t)); cbv beta iota in *; [discriminate|].
  destruct (negb (tkill_sig_valid sig)); cbv beta iota in *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (bv_eqb sig (Z_to_bv 64 SIGABRT)); cbv beta iota in *;
    [| discriminate].
  exact (check_send_sigabrt_sound_ok _ _ _ _ i H).
Qed.

Lemma check_tkill_self_sound_unmodeled : forall pid sig eff m i,
  check_tkill_self pid sig eff m = CheckUnmodeled ->
  tkill_self pid sig i m Unmodeled.
Proof.
  intros pid sig eff m i H.
  unfold check_tkill_self in H. unfold tkill_self. rewrite bind_get_model.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *;
    [apply unmodeled_intro|].
  destruct (m_tid m) as [t|]; cbv beta iota in *; [|apply unmodeled_intro].
  destruct (negb (bv_eqb pid t)); cbv beta iota in *; [apply unmodeled_intro|].
  destruct (negb (tkill_sig_valid sig)); cbv beta iota in *.
  { exfalso. eapply check_ret_only_no_unmodeled. exact H. }
  destruct (bv_eqb sig (Z_to_bv 64 SIGABRT)); cbv beta iota in *;
    [| apply unmodeled_intro].
  exfalso. eapply check_send_sigabrt_no_unmodeled. exact H.
Qed.

Lemma check_tkill_self_complete_ok : forall pid sig eff m m' evs i,
  tkill_self pid sig i m (Ok eff m' evs) ->
  check_tkill_self pid sig eff m = CheckOk m' evs.
Proof.
  intros pid sig eff m m' evs i H.
  unfold tkill_self in H. rewrite bind_get_model in H.
  unfold check_tkill_self.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *;
    [sys_unfold; inv_ok|].
  destruct (m_tid m) as [t|]; cbv beta iota in *; [|sys_unfold; inv_ok].
  destruct (negb (bv_eqb pid t)); cbv beta iota in *; [sys_unfold; inv_ok|].
  destruct (negb (tkill_sig_valid sig)); cbv beta iota in *.
  { sys_unfold; inv_ok. cbv beta iota. rewrite ?bv_eqb_refl. reflexivity. }
  destruct (bv_eqb sig (Z_to_bv 64 SIGABRT)); cbv beta iota in *;
    [| sys_unfold; inv_ok].
  exact (check_send_sigabrt_complete_ok _ _ _ _ i H).
Qed.

Lemma check_tkill_self_complete_unmodeled : forall pid sig m i eff,
  tkill_self pid sig i m Unmodeled ->
  check_tkill_self pid sig eff m = CheckUnmodeled.
Proof.
  intros pid sig m i eff H.
  unfold tkill_self in H. rewrite bind_get_model in H.
  unfold check_tkill_self.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *; [reflexivity|].
  destruct (m_tid m) as [t|]; cbv beta iota in *; [|reflexivity].
  destruct (negb (bv_eqb pid t)); cbv beta iota in *; [reflexivity|].
  destruct (negb (tkill_sig_valid sig)); cbv beta iota in *.
  { exfalso. sys_unfold; inv_ok. }
  destruct (bv_eqb sig (Z_to_bv 64 SIGABRT)); cbv beta iota in *;
    [| reflexivity].
  exact (check_send_sigabrt_complete_unmodeled _ i eff H).
Qed.

Lemma check_tkill_sound_ok : forall pid sig eff m m' evs i,
  check_tkill pid sig eff m = CheckOk m' evs -> tkill_spec pid sig i m (Ok eff m' evs).
Proof.
  intros pid sig eff m m' evs i H.
  unfold check_tkill in H. unfold tkill_spec. rewrite bind_get_model.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *; [discriminate|].
  destruct (negb (pid_positive pid)); cbv beta iota in *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  exact (check_tkill_self_sound_ok _ _ _ _ _ _ i H).
Qed.

Lemma check_tkill_sound_unmodeled : forall pid sig eff m i,
  check_tkill pid sig eff m = CheckUnmodeled -> tkill_spec pid sig i m Unmodeled.
Proof.
  intros pid sig eff m i H.
  unfold check_tkill in H. unfold tkill_spec. rewrite bind_get_model.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *;
    [apply unmodeled_intro|].
  destruct (negb (pid_positive pid)); cbv beta iota in *.
  { exfalso. eapply check_ret_only_no_unmodeled. exact H. }
  exact (check_tkill_self_sound_unmodeled _ _ _ _ i H).
Qed.

Lemma check_tkill_complete_ok : forall pid sig eff m m' evs i,
  tkill_spec pid sig i m (Ok eff m' evs) -> check_tkill pid sig eff m = CheckOk m' evs.
Proof.
  intros pid sig eff m m' evs i H.
  unfold tkill_spec in H. rewrite bind_get_model in H. unfold check_tkill.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *;
    [sys_unfold; inv_ok|].
  destruct (negb (pid_positive pid)); cbv beta iota in *.
  { sys_unfold; inv_ok. cbv beta iota. rewrite ?bv_eqb_refl. reflexivity. }
  exact (check_tkill_self_complete_ok _ _ _ _ _ _ i H).
Qed.

Lemma check_tkill_complete_unmodeled : forall pid sig m i eff,
  tkill_spec pid sig i m Unmodeled -> check_tkill pid sig eff m = CheckUnmodeled.
Proof.
  intros pid sig m i eff H.
  unfold tkill_spec in H. rewrite bind_get_model in H. unfold check_tkill.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *; [reflexivity|].
  destruct (negb (pid_positive pid)); cbv beta iota in *.
  { exfalso. sys_unfold; inv_ok. }
  exact (check_tkill_self_complete_unmodeled _ _ _ i eff H).
Qed.

Lemma check_tgkill_sound_ok : forall tgid pid sig eff m m' evs i,
  check_tgkill tgid pid sig eff m = CheckOk m' evs ->
  tgkill_spec tgid pid sig i m (Ok eff m' evs).
Proof.
  intros tgid pid sig eff m m' evs i H.
  unfold check_tgkill in H. unfold tgkill_spec. rewrite bind_get_model.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *; [discriminate|].
  destruct (negb (pid_positive pid && pid_positive tgid)%bool);
    cbv beta iota in *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (m_tid m) as [t|]; cbv beta iota in *; [|discriminate].
  destruct (negb (bv_eqb pid t)); cbv beta iota in *; [discriminate|].
  destruct (negb (bv_eqb tgid t)); cbv beta iota in *.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  exact (check_tkill_self_sound_ok _ _ _ _ _ _ i H).
Qed.

Lemma check_tgkill_sound_unmodeled : forall tgid pid sig eff m i,
  check_tgkill tgid pid sig eff m = CheckUnmodeled ->
  tgkill_spec tgid pid sig i m Unmodeled.
Proof.
  intros tgid pid sig eff m i H.
  unfold check_tgkill in H. unfold tgkill_spec. rewrite bind_get_model.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *;
    [apply unmodeled_intro|].
  destruct (negb (pid_positive pid && pid_positive tgid)%bool);
    cbv beta iota in *.
  { exfalso. eapply check_ret_only_no_unmodeled. exact H. }
  destruct (m_tid m) as [t|]; cbv beta iota in *; [|apply unmodeled_intro].
  destruct (negb (bv_eqb pid t)); cbv beta iota in *; [apply unmodeled_intro|].
  destruct (negb (bv_eqb tgid t)); cbv beta iota in *.
  { exfalso. eapply check_ret_only_no_unmodeled. exact H. }
  exact (check_tkill_self_sound_unmodeled _ _ _ _ i H).
Qed.

Lemma check_tgkill_complete_ok : forall tgid pid sig eff m m' evs i,
  tgkill_spec tgid pid sig i m (Ok eff m' evs) ->
  check_tgkill tgid pid sig eff m = CheckOk m' evs.
Proof.
  intros tgid pid sig eff m m' evs i H.
  unfold tgkill_spec in H. rewrite bind_get_model in H. unfold check_tgkill.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *;
    [sys_unfold; inv_ok|].
  destruct (negb (pid_positive pid && pid_positive tgid)%bool);
    cbv beta iota in *.
  { sys_unfold; inv_ok. cbv beta iota. rewrite ?bv_eqb_refl. reflexivity. }
  destruct (m_tid m) as [t|]; cbv beta iota in *; [|sys_unfold; inv_ok].
  destruct (negb (bv_eqb pid t)); cbv beta iota in *; [sys_unfold; inv_ok|].
  destruct (negb (bv_eqb tgid t)); cbv beta iota in *.
  { sys_unfold; inv_ok. cbv beta iota. rewrite ?bv_eqb_refl. reflexivity. }
  exact (check_tkill_self_complete_ok _ _ _ _ _ _ i H).
Qed.

Lemma check_tgkill_complete_unmodeled : forall tgid pid sig m i eff,
  tgkill_spec tgid pid sig i m Unmodeled ->
  check_tgkill tgid pid sig eff m = CheckUnmodeled.
Proof.
  intros tgid pid sig m i eff H.
  unfold tgkill_spec in H. rewrite bind_get_model in H. unfold check_tgkill.
  destruct (negb (m_abort_terminal m)); cbv beta iota in *; [reflexivity|].
  destruct (negb (pid_positive pid && pid_positive tgid)%bool);
    cbv beta iota in *.
  { exfalso. sys_unfold; inv_ok. }
  destruct (m_tid m) as [t|]; cbv beta iota in *; [|reflexivity].
  destruct (negb (bv_eqb pid t)); cbv beta iota in *; [reflexivity|].
  destruct (negb (bv_eqb tgid t)); cbv beta iota in *.
  { exfalso. sys_unfold; inv_ok. }
  exact (check_tkill_self_complete_unmodeled _ _ _ i eff H).
Qed.

(** The framing statement [Checks.VmMapsDisjoint]'s cascade consumes.
    Both arms change the model on one branch each -- the pending bit and
    the kill -- and neither touches the address space: [State.with_killed]
    and [State.with_sigabrt_pending] rebuild [ProcState] alone. *)
Lemma check_tkill_frame : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros pid sig eff m m' evs H.
  unfold check_tkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _);
         reflexivity);
    inversion H; subst; autorewrite with model; reflexivity.
Qed.

Lemma check_tgkill_frame : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros tgid pid sig eff m m' evs H.
  unfold check_tgkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _);
         reflexivity);
    inversion H; subst; autorewrite with model; reflexivity.
Qed.
