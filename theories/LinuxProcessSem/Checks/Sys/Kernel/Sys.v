(** * LinuxProcessSem.Checks.Sys.Kernel.Sys — the getpid (172), gettid (178), setsid (157), uname (160), prlimit64 (261) checkers, and their proofs

    Mirrors [Sys/Kernel/Sys.v], which answers to Linux [kernel/sys.c]:
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
  Prelude Fs.ReadWrite Mm.Mmap Kernel.Fork.

(** getpid: the SAME check as [check_set_tid_address], because
    [Kernel.Sys.getpid_spec] is the same relation — see the argument there.
    Sharing the checker keeps the two calls from drifting apart in the
    executable model the way sharing the spec does in the relational
    one. *)

Definition check_getpid : SyscallEffect -> Model -> check_result :=
  check_set_tid_address.

(** gettid: the SAME check again, and for a shorter reason than
    [check_getpid]'s — [Kernel.Sys.gettid_spec] is
    [Fork.set_tid_address_spec] because the two syscalls return the same
    expression, with no thread-group-leader side condition in between
    (see the argument there). *)

Definition check_gettid : SyscallEffect -> Model -> check_result :=
  check_set_tid_address.

(** setsid: no writes.  -EPERM is always admissible — the model does
    not track what would make it fail, and a failure records nothing,
    because a kernel that refused one call can allow the next.  A
    session id is admissible only while no setsid has SUCCEEDED, and
    only in the tid envelope, agreeing with any tid already observed.
    The two are disjoint on the observed return for every [Model]:
    [errno_ret EPERM] is [-1] read unsigned, far above
    [PID_MAX_ENVELOPE].  See [Kernel.Sys.setsid_spec]. *)

Definition check_setsid (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if bv_eqb ret (errno_ret EPERM) then CheckOk m []
      else if m_setsid_succeeded m then CheckReject
      else if (0 <? bv_unsigned ret)%Z &&
              (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z &&
              (match m_tid m with None => true | Some t0 => bv_eqb ret t0 end)
      then CheckOk (with_setsid_succeeded (with_tid ret m)) []
      else CheckReject
  | _ => CheckReject
  end.

(** ioctl: a closed fd is -EBADF whatever the request; on an open one a
    terminal-only request answers -ENOTTY and any other request is
    unmodeled. *)

(** The READ arm's effect shape, split out so the fail-closed direction
    has something to point at: this answers [CheckOk] or [CheckReject]
    and NEVER [CheckUnmodeled], exactly as [check_getrandom_zero] does
    for its arm.  [bs0] is [m_rlimit_core]: [Some] once the limit is
    pinned, in which case the delivered bytes must be exactly it, and
    [None] before, in which case any well-formed pair is admissible and
    becomes the pin. *)

Definition check_rlim64_read (old_rlim : word) (bs0 : option (list byte))
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU r [(a, bs)] [] [] [] [] =>
      if negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a old_rlim)%bool
      then CheckReject
      else match bs0 with
           | Some b0 => if listN_eqb bs b0 then CheckOk m [] else CheckReject
           | None => if rlim64_wf bs then CheckOk (with_rlimit_core bs m) []
                     else CheckReject
           end
  | _ => CheckReject
  end.

(** prlimit64: [Kernel.Sys.prlimit64_spec] carries the argument — why only
    [RLIMIT_CORE], why only pid 0, and why exactly one of the two
    pointers may be non-NULL.  This mirrors its branch structure one for
    one.  The read's ledger entry is the 16 bytes of the [struct
    rlimit64] at [old_rlim]: once the limit is pinned it must be exactly
    the recorded bytes, and before it is pinned any well-formed pair is
    admissible and becomes the pin. *)

Definition check_prlimit64 (i : SyscallInput)
    (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (w_is0 pid) then CheckUnmodeled
  else if negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE) then CheckUnmodeled
  else if (w_is0 new_rlim && w_is0 old_rlim)%bool then CheckUnmodeled
  else if (negb (w_is0 new_rlim) && negb (w_is0 old_rlim))%bool then CheckUnmodeled
  else if w_is0 new_rlim then
    match copy_bytes_map (in_wmem i) old_rlim 16 with
    | None =>
        if negb (access_okb old_rlim 16)
        then check_ret_only eff (errno_ret EFAULT) m []
        else CheckUnmodeled
    | Some _ => check_rlim64_read old_rlim (m_rlimit_core m) eff m
    end
  else
    match m_rlimit_core m with
    | None => CheckUnmodeled
    | Some bs0 =>
        match copy_bytes_map (in_mem i) new_rlim 16 with
        | None =>
            if negb (access_okb new_rlim 16)
            then check_ret_only eff (errno_ret EFAULT) m []
            else CheckUnmodeled
        | Some nb =>
            if (bv_unsigned (rlim64_hard nb) <? bv_unsigned (rlim64_soft nb))%Z
            then check_ret_only_copyins [(new_rlim, 16%nat)]
                   eff (errno_ret EINVAL) m []
            else if negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0))
            then CheckUnmodeled
            else check_ret_only_copyins [(new_rlim, 16%nat)]
                   eff (Z_to_bv 64 0) (with_rlimit_core nb m) []
        end
    end.

(** uname: the copy-out arm, split out for the same reason
    [check_rlim64_read] is — it answers [CheckOk] or [CheckReject] and
    never [CheckUnmodeled], which is what the fail-closed direction
    points at.  [bs0] is [m_utsname]: [Some] once the name is pinned, in
    which case the delivered bytes must be exactly it, and [None] before,
    in which case any buffer inside [utsname_wf]'s envelope is admissible
    and becomes the pin. *)

Definition check_uname_copy (name : word) (bs0 : option (list byte))
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU r [(a, bs)] [] [] [] [] =>
      if negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a name)%bool
      then CheckReject
      else match bs0 with
           | Some b0 => if listN_eqb bs b0 then CheckOk m [] else CheckReject
           | None => if utsname_wf bs then CheckOk (with_utsname bs m) []
                     else CheckReject
           end
  | _ => CheckReject
  end.

(** uname: [Kernel.Sys.uname_spec] carries the argument — why the
    390-byte range is one gate rather than six, and why a range
    [access_ok] admits but memory does not wholly back is a decline
    rather than an -EFAULT.  This mirrors its branch structure one for
    one. *)

Definition check_uname (i : SyscallInput) (name : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb name NEW_UTSNAME_SIZE)
  then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE) with
    | None => CheckUnmodeled
    | Some _ => check_uname_copy name (m_utsname m) eff m
    end.

(** prctl: [Kernel.Sys.prctl_spec] carries the whole argument -- why
    only [PR_CAPBSET_READ], why its answer is the constant 1 rather than
    a choice, and why every other option declines.  This mirrors its
    three branches one for one.  TOTAL ON ITS OWN OPTION: once the
    option is [PR_CAPBSET_READ] this answers [CheckOk] or [CheckReject]
    and never [CheckUnmodeled], so the decline is a fact about the
    OPTION and about nothing else -- which is what makes
    [Checks.ProcessCreation]'s pin on [prctl_modeled_options] the whole
    story about what 167 declines. *)

Definition check_prctl (option_ arg2 : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if negb (Z.eqb (bv_unsigned option_) PR_CAPBSET_READ) then CheckUnmodeled
  else if (CAP_LAST_CAP <? bv_unsigned arg2)%Z
  then check_ret_only eff (errno_ret EINVAL) m []
  else check_ret_only eff (Z_to_bv 64 1) m [].

Lemma check_prctl_sound_ok : forall option_ arg2 eff m m' evs i,
  check_prctl option_ arg2 eff m = CheckOk m' evs ->
  prctl_spec option_ arg2 i m (Ok eff m' evs).
Proof.
  intros option_ arg2 eff m m' evs i H.
  unfold check_prctl in H. unfold prctl_spec.
  destruct (negb (Z.eqb (bv_unsigned option_) PR_CAPBSET_READ)); [discriminate|].
  destruct ((CAP_LAST_CAP <? bv_unsigned arg2)%Z);
    apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
    apply pure_ok.
Qed.

(** The option test is the ONLY thing that declines, so a [CheckUnmodeled]
    forces the same branch in the spec. *)
Lemma check_prctl_sound_unmodeled : forall option_ arg2 eff m i,
  check_prctl option_ arg2 eff m = CheckUnmodeled ->
  prctl_spec option_ arg2 i m Unmodeled.
Proof.
  intros option_ arg2 eff m i H.
  unfold check_prctl in H. unfold prctl_spec.
  destruct (negb (Z.eqb (bv_unsigned option_) PR_CAPBSET_READ));
    [apply unmodeled_intro|].
  destruct ((CAP_LAST_CAP <? bv_unsigned arg2)%Z);
    now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_prctl_complete_ok : forall option_ arg2 eff m m' evs i,
  prctl_spec option_ arg2 i m (Ok eff m' evs) ->
  check_prctl option_ arg2 eff m = CheckOk m' evs.
Proof.
  intros option_ arg2 eff m m' evs i H.
  unfold prctl_spec in H. unfold check_prctl.
  destruct (negb (Z.eqb (bv_unsigned option_) PR_CAPBSET_READ));
    [now inversion H|].
  destruct ((CAP_LAST_CAP <? bv_unsigned arg2)%Z);
    unfold err_ret, ret_only, pure in H; inversion H; subst;
    cbn; rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_prctl_complete_unmodeled : forall option_ arg2 m i eff,
  prctl_spec option_ arg2 i m Unmodeled ->
  check_prctl option_ arg2 eff m = CheckUnmodeled.
Proof.
  intros option_ arg2 m i eff H.
  unfold prctl_spec in H. unfold check_prctl.
  destruct (negb (Z.eqb (bv_unsigned option_) PR_CAPBSET_READ)); [reflexivity|].
  exfalso.
  destruct ((CAP_LAST_CAP <? bv_unsigned arg2)%Z);
    unfold err_ret, ret_only, pure in H; discriminate H.
Qed.

(* =========================================================================
   Dispatcher
   ========================================================================= *)

(** ftruncate: the negative length decided BEFORE the fd lookup, one
    -EINVAL for every fd kind that is not a writable regular file, and on
    a WRITABLE one — [FdFileW], [FdFileA] and [FdFileRW], which share a
    single arm because [do_ftruncate] reads only S_ISREG and FMODE_WRITE
    — a bare 0 with the file resized and THE OFFSET LEFT
    ALONE (see [Open.ftruncate_spec]).  The size guard is consulted only
    on that arm, as in the spec: a huge length on a channel or a
    directory is still the kernel's -EINVAL, not a decline. *)

(* ------------------------------------------------------------- getpid *)

(** [getpid_spec] and [check_getpid] are [set_tid_address_spec] and
    [check_set_tid_address].  The four obligations are therefore the
    set_tid_address ones, discharged by application rather than by a
    second copy of the proof. *)

Lemma check_getpid_sound_ok : forall eff m m' evs i,
  check_getpid eff m = CheckOk m' evs ->
  getpid_spec i m (Ok eff m' evs).
Proof. exact check_set_tid_address_sound_ok. Qed.

Lemma check_getpid_sound_unmodeled : forall eff m i,
  check_getpid eff m = CheckUnmodeled -> getpid_spec i m Unmodeled.
Proof. exact check_set_tid_address_sound_unmodeled. Qed.

Lemma check_getpid_complete_ok : forall eff m m' evs i,
  getpid_spec i m (Ok eff m' evs) -> check_getpid eff m = CheckOk m' evs.
Proof. exact check_set_tid_address_complete_ok. Qed.

Lemma check_getpid_complete_unmodeled : forall m i eff,
  getpid_spec i m Unmodeled -> check_getpid eff m = CheckUnmodeled.
Proof. exact check_set_tid_address_complete_unmodeled. Qed.

(* ------------------------------------------------------------- gettid *)

(** Same again: [gettid_spec] and [check_gettid] are
    [set_tid_address_spec] and [check_set_tid_address], so the four
    obligations are discharged by application rather than by a third
    copy of the proof. *)

Lemma check_gettid_sound_ok : forall eff m m' evs i,
  check_gettid eff m = CheckOk m' evs ->
  gettid_spec i m (Ok eff m' evs).
Proof. exact check_set_tid_address_sound_ok. Qed.

Lemma check_gettid_sound_unmodeled : forall eff m i,
  check_gettid eff m = CheckUnmodeled -> gettid_spec i m Unmodeled.
Proof. exact check_set_tid_address_sound_unmodeled. Qed.

Lemma check_gettid_complete_ok : forall eff m m' evs i,
  gettid_spec i m (Ok eff m' evs) -> check_gettid eff m = CheckOk m' evs.
Proof. exact check_set_tid_address_complete_ok. Qed.

Lemma check_gettid_complete_unmodeled : forall m i eff,
  gettid_spec i m Unmodeled -> check_gettid eff m = CheckUnmodeled.
Proof. exact check_set_tid_address_complete_unmodeled. Qed.

(* ------------------------------------------------------------- setsid *)

(** No session id can be mistaken for the -EPERM arm: [errno_ret EPERM]
    is [-1] read as an unsigned 64-bit register and every admissible id
    is below [PID_MAX_ENVELOPE].  This is what keeps [check_setsid] a
    function of the observed return rather than a choice, and it holds
    for every [Model], not merely every reachable one. *)
Lemma setsid_id_not_eperm : forall r : word,
  (bv_unsigned r < PID_MAX_ENVELOPE)%Z ->
  bv_eqb r (errno_ret EPERM) = false.
Proof.
  intros r H1. apply Bool.not_true_iff_false. intro Heq.
  apply bv_eqb_eq in Heq. subst r.
  change (bv_unsigned (errno_ret EPERM)) with 18446744073709551615%Z in H1.
  change PID_MAX_ENVELOPE with 4194304%Z in H1. lia.
Qed.

Lemma check_setsid_sound_ok : forall eff m m' evs i,
  check_setsid eff m = CheckOk m' evs -> setsid_spec i m (Ok eff m' evs).
Proof.
  intros [ret ws zs us cs copyins] m m' evs i H.
  unfold check_setsid in H. unfold setsid_spec.
  destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (bv_eqb ret (errno_ret EPERM)) eqn:Hp.
  { apply bv_eqb_eq in Hp. subst ret.
    destruct (m_setsid_succeeded m) eqn:Hs; cbv iota;
      inversion H; clear H; subst;
      [apply pure_ok | apply alt_l; apply pure_ok]. }
  destruct (m_setsid_succeeded m) eqn:Hs; [discriminate|]. cbv iota.
  destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z &&
            (match m_tid m with None => true | Some t0 => bv_eqb ret t0 end))
    eqn:Hvalid; [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in Hvalid as [Hrange Hpin].
  apply andb_true_iff in Hrange as [Hlo Hhi].
  apply Z.ltb_lt in Hlo. apply Z.ltb_lt in Hhi.
  apply alt_r.
  eapply bind_ok0.
  { apply (choose_ok _ ret). split; [lia|].
    destruct (m_tid m) as [t0|]; [apply bv_eqb_eq in Hpin; exact Hpin | exact I]. }
  eapply bind_ok0; [apply modify_ok|].
  eapply bind_ok0; [apply modify_ok|].
  apply pure_ok.
Qed.

(** setsid is TOTAL: every effect shape is accepted or rejected, never
    declined.  [Kernel.Sys.setsid_spec] has no [unmodeled] arm, and this
    is the checker half of saying so. *)
Lemma check_setsid_no_unmodeled : forall eff m,
  check_setsid eff m <> CheckUnmodeled.
Proof.
  intros [ret ws zs us cs copyins] m. unfold check_setsid.
  destruct ws;
    [destruct zs;
      [destruct us;
        [destruct cs;
          [destruct copyins;
            [destruct (bv_eqb ret (errno_ret EPERM));
              [|destruct (m_setsid_succeeded m);
                [|destruct ((0 <? bv_unsigned ret)%Z &&
                            (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z &&
                            (match m_tid m with
                             | None => true | Some t0 => bv_eqb ret t0 end))]]|]|]|]|]|];
    discriminate.
Qed.

Lemma check_setsid_sound_unmodeled : forall eff m i,
  check_setsid eff m = CheckUnmodeled -> setsid_spec i m Unmodeled.
Proof.
  intros eff m i H. exfalso. eapply check_setsid_no_unmodeled. exact H.
Qed.

Lemma check_setsid_complete_ok : forall eff m m' evs i,
  setsid_spec i m (Ok eff m' evs) -> check_setsid eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H.
  unfold setsid_spec in H. unfold check_setsid.
  destruct (m_setsid_succeeded m) eqn:Hs; sys_unfold; inv_ok;
    hall Hs; inv_ok.
  - cbn. rewrite bv_eqb_refl. reflexivity.
  - cbn. rewrite bv_eqb_refl. reflexivity.
  - cbn.
    match goal with
    | Hlo : (0 < bv_unsigned ?r)%Z, Hhi : (bv_unsigned ?r < PID_MAX_ENVELOPE)%Z |- _ =>
        rewrite (setsid_id_not_eperm r Hhi),
                (proj2 (Z.ltb_lt 0 (bv_unsigned r)) Hlo),
                (proj2 (Z.ltb_lt (bv_unsigned r) PID_MAX_ENVELOPE) Hhi)
    end.
    destruct (m_tid m) as [t0|] eqn:Htid; cbn.
    + match goal with
      | Hpin : _ = t0 |- _ => rewrite Hpin, bv_eqb_refl; reflexivity
      end.
    + reflexivity.
Qed.

Lemma check_setsid_complete_unmodeled : forall m i eff,
  setsid_spec i m Unmodeled -> check_setsid eff m = CheckUnmodeled.
Proof.
  intros m i eff H. exfalso.
  unfold setsid_spec in H.
  destruct (m_setsid_succeeded m) eqn:Hs; sys_unfold; inv_ok;
    hall Hs; inv_ok.
Qed.

(* ----------------------------------------------------------------- ioctl *)

(* ------------------------------------------------------------ dispatcher *)

(** Case on the dispatcher's syscall number, solving the matched arm with
    [tac] after peeling the [sysno]/[arg] readers. *)

Lemma check_rlim64_read_no_unmodeled : forall old_rlim bs0 eff m,
  check_rlim64_read old_rlim bs0 eff m <> CheckUnmodeled.
Proof.
  intros old_rlim bs0 [r ws zs us cs copyins] m. unfold check_rlim64_read.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a old_rlim)%bool);
    [discriminate|].
  destruct bs0 as [b0|];
    [destruct (listN_eqb bs b0)|destruct (rlim64_wf bs)]; discriminate.
Qed.

(** What a [CheckOk] out of the read arm tells you: the effect is a
    16-byte write of the limit at [old_rlim] returning 0, and either it
    repeated the pin or it created one. *)

Lemma check_rlim64_read_ok : forall old_rlim bs0 eff m m' evs,
  check_rlim64_read old_rlim bs0 eff m = CheckOk m' evs ->
  exists bs, eff = mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] []
             /\ evs = []
             /\ ((bs0 = Some bs /\ m' = m)
                 \/ (bs0 = None /\ rlim64_wf bs = true
                     /\ m' = with_rlimit_core bs m)).
Proof.
  intros old_rlim bs0 [r ws zs us cs copyins] m m' evs H.
  unfold check_rlim64_read in H.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a old_rlim)%bool) eqn:HG;
    [discriminate|].
  apply Bool.negb_false_iff in HG.
  apply andb_true_iff in HG as [HR HA].
  apply bv_eqb_eq in HR; subst r. apply bv_eqb_eq in HA; subst a.
  destruct bs0 as [b0|].
  - destruct (listN_eqb bs b0) eqn:HL; [|discriminate].
    apply listN_eqb_eq in HL; subst b0.
    inversion H; clear H; subst. exists bs. repeat split. now left.
  - destruct (rlim64_wf bs) eqn:HW; [|discriminate].
    inversion H; clear H; subst. exists bs. repeat split. right. now repeat split.
Qed.

(* ------------------------------------------------------------- uname *)

Lemma check_uname_copy_no_unmodeled : forall name bs0 eff m,
  check_uname_copy name bs0 eff m <> CheckUnmodeled.
Proof.
  intros name bs0 [r ws zs us cs copyins] m. unfold check_uname_copy.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a name)%bool);
    [discriminate|].
  destruct bs0 as [b0|];
    [destruct (listN_eqb bs b0)|destruct (utsname_wf bs)]; discriminate.
Qed.

(** What a [CheckOk] out of the copy arm tells you: the effect is one
    390-byte write of the utsname at [name] returning 0, and either it
    repeated the pin or it created one. *)

Lemma check_uname_copy_ok : forall name bs0 eff m m' evs,
  check_uname_copy name bs0 eff m = CheckOk m' evs ->
  exists bs, eff = mkEffect (Z_to_bv 64 0) [(name, bs)] []
             /\ evs = []
             /\ ((bs0 = Some bs /\ m' = m)
                 \/ (bs0 = None /\ utsname_wf bs = true
                     /\ m' = with_utsname bs m)).
Proof.
  intros name bs0 [r ws zs us cs copyins] m m' evs H.
  unfold check_uname_copy in H.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a name)%bool) eqn:HG;
    [discriminate|].
  apply Bool.negb_false_iff in HG.
  apply andb_true_iff in HG as [HR HA].
  apply bv_eqb_eq in HR; subst r. apply bv_eqb_eq in HA; subst a.
  destruct bs0 as [b0|].
  - destruct (listN_eqb bs b0) eqn:HL; [|discriminate].
    apply listN_eqb_eq in HL; subst b0.
    inversion H; clear H; subst. exists bs. repeat split. now left.
  - destruct (utsname_wf bs) eqn:HW; [|discriminate].
    inversion H; clear H; subst. exists bs. repeat split. right. now repeat split.
Qed.

Lemma check_uname_sound_ok : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs ->
  uname_spec name i m (Ok eff m' evs).
Proof.
  intros i name eff m m' evs H.
  unfold check_uname in H. unfold uname_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb name NEW_UTSNAME_SIZE)) eqn:Ho.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE))
      as [bs1|] eqn:Hw; [|discriminate].
    apply check_uname_copy_ok in H as (bs & -> & -> & [[Hm ->]|(Hm & HW & ->)]);
      rewrite Hm.
    + apply pure_ok.
    + eapply bind_ok0; [apply (choose_ok _ bs); exact HW|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_uname_sound_unmodeled : forall i name eff m,
  check_uname i name eff m = CheckUnmodeled -> uname_spec name i m Unmodeled.
Proof.
  intros i name eff m H.
  unfold check_uname in H. unfold uname_spec.
  eapply bind_unmodeled2; [apply input_ok|].
  eapply bind_unmodeled2; [apply get_model_ok|].
  destruct (negb (access_okb name NEW_UTSNAME_SIZE)) eqn:Ho.
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE))
      as [bs1|] eqn:Hw.
    + now apply check_uname_copy_no_unmodeled in H.
    + apply unmodeled_intro.
Qed.

Lemma check_uname_complete_ok : forall i name eff m m' evs,
  uname_spec name i m (Ok eff m' evs) ->
  check_uname i name eff m = CheckOk m' evs.
Proof.
  intros i name eff m m' evs H.
  unfold uname_spec in H. unfold check_uname.
  destruct (negb (access_okb name NEW_UTSNAME_SIZE)) eqn:Ho.
  - sys_unfold; inv_ok; hall Ho; inv_ok.
    apply check_ret_only_ok_iff. now repeat split.
  - destruct (read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE))
      as [bs1|] eqn:Hw;
      [|sys_unfold; inv_ok; hall Ho; hall Hw; inv_ok].
    destruct (m_utsname m) as [bs0|] eqn:Hm;
      sys_unfold; inv_ok; hall Ho; hall Hw; hall Hm; inv_ok;
      unfold check_uname_copy;
      rewrite !bv_eqb_refl; cbn [andb negb].
    + rewrite (proj2 (listN_eqb_eq bs0 bs0) eq_refl). reflexivity.
    + match goal with H : utsname_wf ?b = true |- _ => rewrite H end.
      reflexivity.
Qed.

Lemma check_uname_complete_unmodeled : forall i name m eff,
  uname_spec name i m Unmodeled -> check_uname i name eff m = CheckUnmodeled.
Proof.
  intros i name m eff H.
  unfold uname_spec in H. unfold check_uname.
  destruct (negb (access_okb name NEW_UTSNAME_SIZE)) eqn:Ho.
  - exfalso. sys_unfold; inv_ok; hall Ho; inv_ok.
  - destruct (read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE))
      as [bs1|] eqn:Hw; [exfalso|reflexivity].
    destruct (m_utsname m) as [bs0|] eqn:Hm;
      sys_unfold; inv_ok; hall Ho; hall Hw; hall Hm; inv_ok.
Qed.

Lemma check_prlimit64_sound_ok :
  forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs ->
  prlimit64_spec pid resource new_rlim old_rlim i m (Ok eff m' evs).
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H.
  unfold check_prlimit64 in H. unfold prlimit64_spec.
  destruct (negb (w_is0 pid)) eqn:Hp; [discriminate|]. cbv iota.
  destruct (negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE)) eqn:Hr;
    [discriminate|]. cbv iota.
  destruct (w_is0 new_rlim && w_is0 old_rlim)%bool eqn:Hb; [discriminate|].
  cbv iota.
  destruct (negb (w_is0 new_rlim) && negb (w_is0 old_rlim))%bool eqn:Hb2;
    [discriminate|]. cbv iota.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (w_is0 new_rlim) eqn:Hn.
  - destruct (copy_bytes_map (in_wmem i) old_rlim 16) as [bs1|]
      eqn:Hw.
    + apply check_rlim64_read_ok in H as (bs & -> & -> & [[Hm ->]|(Hm & HW & ->)]);
        rewrite Hm.
      * apply pure_ok.
      * eapply bind_ok0; [apply (choose_ok _ bs); exact HW|].
        eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + destruct (negb (access_okb old_rlim 16)) eqn:Ho;
        [|discriminate].
      apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
  - destruct (m_rlimit_core m) as [bs0|] eqn:Hm; [|discriminate].
    destruct (copy_bytes_map (in_mem i) new_rlim 16) as [nb|]
      eqn:Hw.
    + destruct ((bv_unsigned (rlim64_hard nb)
                 <? bv_unsigned (rlim64_soft nb))%Z) eqn:Hi.
      * apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
        apply record_copyins_ok. apply pure_ok.
      * destruct (negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0))) eqn:Hh;
          [discriminate|].
        apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
        apply record_copyins_ok.
        eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
    + destruct (negb (access_okb new_rlim 16)) eqn:Ho;
        [|discriminate].
      apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
Qed.

Lemma check_prlimit64_sound_unmodeled :
  forall i pid resource new_rlim old_rlim eff m,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckUnmodeled ->
  prlimit64_spec pid resource new_rlim old_rlim i m Unmodeled.
Proof.
  intros i pid resource new_rlim old_rlim eff m H.
  unfold check_prlimit64 in H. unfold prlimit64_spec.
  destruct (negb (w_is0 pid)) eqn:Hp.
  { cbv iota. apply unmodeled_intro. }
  cbv iota in H |- *.
  destruct (negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE)) eqn:Hr.
  { cbv iota. apply unmodeled_intro. }
  cbv iota in H |- *.
  destruct (w_is0 new_rlim && w_is0 old_rlim)%bool eqn:Hb.
  { cbv iota. apply unmodeled_intro. }
  cbv iota in H |- *.
  destruct (negb (w_is0 new_rlim) && negb (w_is0 old_rlim))%bool eqn:Hb2.
  { cbv iota. apply unmodeled_intro. }
  cbv iota in H |- *.
  eapply bind_unmodeled2; [apply input_ok|].
  eapply bind_unmodeled2; [apply get_model_ok|].
  destruct (w_is0 new_rlim) eqn:Hn.
  - destruct (copy_bytes_map (in_wmem i) old_rlim 16) as [bs1|]
      eqn:Hw.
    + now apply check_rlim64_read_no_unmodeled in H.
    + destruct (negb (access_okb old_rlim 16)) eqn:Ho.
      * now apply check_ret_only_no_unmodeled in H.
      * apply unmodeled_intro.
  - destruct (m_rlimit_core m) as [bs0|] eqn:Hm; [|apply unmodeled_intro].
    destruct (copy_bytes_map (in_mem i) new_rlim 16) as [nb|]
      eqn:Hw.
    + destruct ((bv_unsigned (rlim64_hard nb)
                 <? bv_unsigned (rlim64_soft nb))%Z) eqn:Hi.
      * now apply check_ret_only_copyins_no_unmodeled in H.
      * destruct (negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0))) eqn:Hh.
        { apply record_copyins_unmodeled. apply unmodeled_intro. }
        now apply check_ret_only_copyins_no_unmodeled in H.
    + destruct (negb (access_okb new_rlim 16)) eqn:Ho.
      * now apply check_ret_only_no_unmodeled in H.
      * apply unmodeled_intro.
Qed.

Lemma check_prlimit64_complete_ok :
  forall i pid resource new_rlim old_rlim eff m m' evs,
  prlimit64_spec pid resource new_rlim old_rlim i m (Ok eff m' evs) ->
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H.
  unfold prlimit64_spec in H. unfold check_prlimit64.
  destruct (negb (w_is0 pid)) eqn:Hp; [sys_unfold; inv_ok|]. cbv iota in H |- *.
  destruct (negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE)) eqn:Hr;
    [sys_unfold; inv_ok|]. cbv iota in H |- *.
  destruct (w_is0 new_rlim && w_is0 old_rlim)%bool eqn:Hb;
    [sys_unfold; inv_ok|]. cbv iota in H |- *.
  destruct (negb (w_is0 new_rlim) && negb (w_is0 old_rlim))%bool eqn:Hb2;
    [sys_unfold; inv_ok|]. cbv iota in H |- *.
  destruct (w_is0 new_rlim) eqn:Hn.
  - destruct (copy_bytes_map (in_wmem i) old_rlim 16) as [bs1|]
      eqn:Hw.
    + destruct (m_rlimit_core m) as [bs0|] eqn:Hm;
        sys_unfold; inv_ok; hall Hn; hall Hw; hall Hm; inv_ok;
        unfold check_rlim64_read;
        rewrite !bv_eqb_refl; cbn [andb negb].
      * rewrite (proj2 (listN_eqb_eq bs0 bs0) eq_refl). reflexivity.
      * match goal with H : rlim64_wf ?b = true |- _ => rewrite H end.
        reflexivity.
    + destruct (negb (access_okb old_rlim 16)) eqn:Ho;
        sys_unfold; inv_ok; hall Hn; hall Hw; hall Ho; inv_ok.
      apply check_ret_only_ok_iff. now repeat split.
  - destruct (m_rlimit_core m) as [bs0|] eqn:Hm;
      [|sys_unfold; inv_ok; hall Hn; hall Hm; inv_ok].
    destruct (copy_bytes_map (in_mem i) new_rlim 16) as [nb|]
      eqn:Hw.
    + destruct ((bv_unsigned (rlim64_hard nb)
                 <? bv_unsigned (rlim64_soft nb))%Z) eqn:Hi;
        [ sys_unfold; inv_ok; hall Hn; hall Hm; hall Hw; hall Hi; inv_ok;
          apply check_ret_only_copyins_ok_iff; now repeat split
        | ].
      destruct (negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0))) eqn:Hh;
        sys_unfold; inv_ok; hall Hn; hall Hm; hall Hw; hall Hi; hall Hh;
        inv_ok.
      apply check_ret_only_copyins_ok_iff. now repeat split.
    + destruct (negb (access_okb new_rlim 16)) eqn:Ho;
        sys_unfold; inv_ok; hall Hn; hall Hm; hall Hw; hall Ho; inv_ok.
      apply check_ret_only_ok_iff. now repeat split.
Qed.

Lemma check_prlimit64_complete_unmodeled :
  forall i pid resource new_rlim old_rlim m eff,
  prlimit64_spec pid resource new_rlim old_rlim i m Unmodeled ->
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckUnmodeled.
Proof.
  intros i pid resource new_rlim old_rlim m eff H.
  unfold prlimit64_spec in H. unfold check_prlimit64.
  destruct (negb (w_is0 pid)) eqn:Hp; [reflexivity|]. cbv iota in H |- *.
  destruct (negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE)) eqn:Hr;
    [reflexivity|]. cbv iota in H |- *.
  destruct (w_is0 new_rlim && w_is0 old_rlim)%bool eqn:Hb; [reflexivity|].
  cbv iota in H |- *.
  destruct (negb (w_is0 new_rlim) && negb (w_is0 old_rlim))%bool eqn:Hb2;
    [reflexivity|]. cbv iota in H |- *.
  destruct (w_is0 new_rlim) eqn:Hn.
  - destruct (copy_bytes_map (in_wmem i) old_rlim 16) as [bs1|]
      eqn:Hw.
    + exfalso. destruct (m_rlimit_core m) as [bs0|] eqn:Hm;
        sys_unfold; inv_ok; hall Hn; hall Hw; hall Hm; inv_ok.
    + destruct (negb (access_okb old_rlim 16)) eqn:Ho;
        [exfalso|reflexivity];
        sys_unfold; inv_ok; hall Hn; hall Hw; hall Ho; inv_ok.
  - destruct (m_rlimit_core m) as [bs0|] eqn:Hm; [|reflexivity].
    destruct (copy_bytes_map (in_mem i) new_rlim 16) as [nb|]
      eqn:Hw.
    + destruct ((bv_unsigned (rlim64_hard nb)
                 <? bv_unsigned (rlim64_soft nb))%Z) eqn:Hi;
        [ exfalso; sys_unfold; inv_ok; hall Hn; hall Hm; hall Hw; hall Hi;
          inv_ok | ].
      destruct (negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0))) eqn:Hh;
        [reflexivity|exfalso];
        sys_unfold; inv_ok; hall Hn; hall Hm; hall Hw; hall Hi; hall Hh;
        inv_ok.
    + destruct (negb (access_okb new_rlim 16)) eqn:Ho;
        [exfalso|reflexivity];
        sys_unfold; inv_ok; hall Hn; hall Hm; hall Hw; hall Ho; inv_ok.
Qed.

(* =========================================================================
   Credentials — getuid (174) / geteuid (175) / getgid (176) /
   getegid (177) / setuid (146) / setgid (144) / setresuid (147) /
   setresgid (149)
   ========================================================================= *)

(** A setter's success answer is 0, which is not an errno: the injected
    and the deterministic arm of its [alt] can never claim the same
    return. *)
Lemma errno_ret_in_setid_zero : forall b,
  errno_ret_in (setid_errnos b) (Z_to_bv 64 0) = false.
Proof. destruct b; reflexivity. Qed.

(** -EPERM is a verdict the setters reach from the credentials, never an
    environment failure the target may inject, so it is disjoint from the
    injectable set too. *)
Lemma errno_ret_in_setid_eperm : forall b,
  errno_ret_in (setid_errnos b) (errno_ret EPERM) = false.
Proof. destruct b; reflexivity. Qed.

(** [getuid] (174), [geteuid] (175), [getgid] (176), [getegid] (177):
    the stored id and nothing else.  TOTAL — there is no argument to
    reject and no allocation to fail, so this acceptor never declines
    (Linux v6.18.46, commit 1f99e9ab748f, kernel/sys.c,
    [SYSCALL_DEFINE0(getuid)] and its three siblings). *)
Definition check_getid (sel : Creds -> word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_ret_only eff (sel (m_creds m)) m [].

(** The shape every fallible id-setter branch shares: the observation is
    admissible if it is an injectable errno from [errs], which leaves the
    model alone, or the branch's own answer [r], which steps the model to
    [mR]. *)
Definition check_setid_result (errs : list Z) (r : word) (mR : Model)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in errs ret then CheckOk m []
      else if bv_eqb ret r then CheckOk mR [] else CheckReject
  | _ => CheckReject
  end.

(** [setuid] (146) and [setgid] (144), over the triple [get] reads and
    [put] writes; [user] is what admits -EAGAIN (Linux v6.18.46,
    commit 1f99e9ab748f, kernel/sys.c, [__sys_setuid] /
    [__sys_setgid]).  The tests are in the kernel's order: [(uid_t)-1]
    is -EINVAL before anything is
    allocated, then the privileged transition that moves all three ids,
    then the unprivileged one that moves only the effective id and
    answers -EPERM for any other target.  TOTAL — every branch answers,
    so this acceptor never declines. *)
Definition check_setid (get : Creds -> IdTriple) (put : IdTriple -> Creds -> Creds)
    (user : bool) (v : word) (eff : SyscallEffect) (m : Model) : check_result :=
  let c := m_creds m in
  let t := get c in
  if bv_eqb v ID_MINUS_ONE then check_ret_only eff (errno_ret EINVAL) m []
  else if creds_privileged c then
    check_setid_result (setid_errnos (andb user (negb (bv_eqb v (id_real t)))))
      (Z_to_bv 64 0) (with_creds (put (mkIdTriple v v v) c) m) eff m
  else if orb (bv_eqb v (id_real t)) (bv_eqb v (id_saved t)) then
    check_setid_result (setid_errnos false) (Z_to_bv 64 0)
      (with_creds (put (mkIdTriple (id_real t) v (id_saved t)) c) m) eff m
  else
    check_setid_result (setid_errnos false) (errno_ret EPERM) m eff m.

(** [setresuid] (147) and [setresgid] (149), the same way
    (Linux v6.18.46, commit 1f99e9ab748f, kernel/sys.c,
    [__sys_setresuid] / [__sys_setresgid]).  [(uid_t)-1] in a position
    means leave that id alone; a call that asks for nothing returns 0
    before any allocation;
    a call that would install an id the process does not already hold
    needs privilege, and is refused -EPERM before [prepare_creds], so
    that refusal can never answer -ENOMEM.  TOTAL for the same reason as
    [check_setid]. *)
Definition check_setresid (get : Creds -> IdTriple) (put : IdTriple -> Creds -> Creds)
    (user : bool) (r e s : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  let c := m_creds m in
  let t := get c in
  let pick (a : word) (cur : word) :=
    if bv_eqb a ID_MINUS_ONE then cur else a in
  let nr := pick r (id_real t) in
  let ne := pick e (id_eff t) in
  let ns := pick s (id_saved t) in
  if andb (andb (bv_eqb nr (id_real t)) (bv_eqb ne (id_eff t)))
          (bv_eqb ns (id_saved t)) then
    check_ret_only eff (Z_to_bv 64 0) m []
  else
    let is_old (x : word) :=
      orb (orb (bv_eqb x (id_real t)) (bv_eqb x (id_eff t))) (bv_eqb x (id_saved t)) in
    if andb (negb (andb (andb (is_old nr) (is_old ne)) (is_old ns)))
            (negb (creds_privileged c)) then
      check_ret_only eff (errno_ret EPERM) m []
    else
      check_setid_result (setid_errnos (andb user (negb (bv_eqb nr (id_real t)))))
        (Z_to_bv 64 0) (with_creds (put (mkIdTriple nr ne ns) c) m) eff m.

(** The [alt] every fallible credential-setter branch ends in: an
    injectable errno, or the branch's own deterministic arm [c2].  All
    this needs to know about [c2] is that it admits exactly [r] with the
    model at [mR]. *)
Lemma check_setid_result_sound_ok :
  forall errs r mR (c2 : Sys SyscallEffect) i eff m m' evs,
  c2 i m (Ok (mkEffect r [] []) mR []) ->
  check_setid_result errs r mR eff m = CheckOk m' evs ->
  alt (bind (errno_from errs) (fun e => err_ret e)) c2 i m (Ok eff m' evs).
Proof.
  intros errs r mR c2 i eff m m' evs Hc2 H.
  unfold check_setid_result in H.
  destruct eff as [ret ws zs us cs copyins].
  destruct ws as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (errno_ret_in errs ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
    apply pure_ok.
  - destruct (bv_eqb ret r) eqn:Hr; [|discriminate].
    apply bv_eqb_eq in Hr. inversion H; clear H; subst.
    apply alt_r. exact Hc2.
Qed.

(** Every branch of a credential setter answers, so this acceptor never
    declines. *)
Lemma check_setid_result_no_unmodeled : forall errs r mR eff m,
  check_setid_result errs r mR eff m <> CheckUnmodeled.
Proof.
  intros errs r mR eff m. unfold check_setid_result.
  destruct eff as [ret [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]]; try discriminate.
  destruct (errno_ret_in errs ret); [discriminate|].
  destruct (bv_eqb ret r); discriminate.
Qed.

(** Split the branch conditions of a credential setter — in the goal
    (the spec, for soundness; the acceptor, for completeness) and in
    every hypothesis at once.  [Sys.Kernel.Sys] and the acceptor make the
    same tests in the same order, so one split serves both sides. *)
Ltac creds_split :=
  repeat match goal with
         | |- context [ if ?b then _ else _ ] =>
             let E := fresh "Hb" in destruct b eqn:E; hall E
         end.

(** Every leaf of a credential setter answers, so the acceptor never
    reaches [CheckUnmodeled] and this direction is vacuous branch by
    branch. *)
Ltac creds_unmod_leaf :=
  match goal with
  | H : check_ret_only _ _ _ _ = CheckUnmodeled |- _ =>
      now apply check_ret_only_no_unmodeled in H
  | H : check_setid_result _ _ _ _ _ = CheckUnmodeled |- _ =>
      now apply check_setid_result_no_unmodeled in H
  end.

(** Close one leaf of a setter's soundness proof: either the branch is a
    single deterministic answer, or it is the injectable-errno [alt]
    whose right arm answers with, and possibly commits, new credentials. *)
Ltac creds_sound_leaf :=
  match goal with
  | H : check_ret_only _ _ _ _ = CheckOk _ _ |- _ =>
      apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
      apply pure_ok
  | H : check_setid_result _ _ _ _ _ = CheckOk _ _ |- _ =>
      eapply check_setid_result_sound_ok; [|exact H];
      first [ eapply bind_ok0; [apply modify_ok|]; apply pure_ok
            | apply pure_ok ]
  end.

(** The mirror image: a leaf of a setter's completeness proof, where the
    observation is already known and the acceptor has to be shown to
    accept it. *)
Ltac creds_complete_leaf :=
  try unfold check_setid_result; try unfold check_ret_only;
  cbv beta iota zeta;
  first
  [ match goal with
    | HIn : In ?e ?es |- _ => rewrite (errno_ret_in_intro es e HIn)
    end
  | rewrite errno_ret_in_setid_zero
  | rewrite errno_ret_in_setid_eperm
  | idtac ];
  cbv beta iota zeta; try rewrite bv_eqb_refl; reflexivity.

(* ---------------------------------------------- getuid/geteuid/getgid/getegid *)

Lemma check_getid_sound_ok : forall sel eff m m' evs i,
  check_getid sel eff m = CheckOk m' evs -> getid_spec sel i m (Ok eff m' evs).
Proof.
  intros sel eff m m' evs i H.
  unfold check_getid in H. unfold getid_spec.
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  eapply bind_ok0; [apply get_model_ok|]. apply pure_ok.
Qed.

(** The readers are total, so this direction is vacuous. *)
Lemma check_getid_sound_unmodeled : forall sel eff m i,
  check_getid sel eff m = CheckUnmodeled -> getid_spec sel i m Unmodeled.
Proof.
  intros sel eff m i H. unfold check_getid in H.
  now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_getid_complete_ok : forall sel eff m m' evs i,
  getid_spec sel i m (Ok eff m' evs) -> check_getid sel eff m = CheckOk m' evs.
Proof.
  intros sel eff m m' evs i H.
  unfold getid_spec in H. unfold check_getid. sys_unfold.
  cbv iota in H. inv_ok.
  cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

(** Vacuous for the same reason: the spec cannot decline either. *)
Lemma check_getid_complete_unmodeled : forall sel m i eff,
  getid_spec sel i m Unmodeled -> check_getid sel eff m = CheckUnmodeled.
Proof.
  intros sel m i eff H. unfold getid_spec in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

(* ------------------------------------------------------- setuid / setgid *)

Lemma check_setid_sound_ok : forall get put user v eff m m' evs i,
  check_setid get put user v eff m = CheckOk m' evs ->
  setid_spec get put user v i m (Ok eff m' evs).
Proof.
  intros get put user v eff m m' evs i H.
  unfold check_setid in H. unfold setid_spec.
  eapply bind_ok0; [apply get_model_ok|].
  cbv beta zeta in H |- *. creds_split; creds_sound_leaf.
Qed.

Lemma check_setid_sound_unmodeled : forall get put user v eff m i,
  check_setid get put user v eff m = CheckUnmodeled ->
  setid_spec get put user v i m Unmodeled.
Proof.
  intros get put user v eff m i H.
  unfold check_setid in H. unfold setid_spec.
  eapply bind_unmodeled2; [apply get_model_ok|].
  cbv beta zeta in H |- *. creds_split; creds_unmod_leaf.
Qed.

Lemma check_setid_complete_ok : forall get put user v eff m m' evs i,
  setid_spec get put user v i m (Ok eff m' evs) ->
  check_setid get put user v eff m = CheckOk m' evs.
Proof.
  intros get put user v eff m m' evs i H.
  unfold setid_spec in H. unfold check_setid. sys_unfold.
  cbv iota in H. inv_ok. creds_split; inv_ok; creds_complete_leaf.
Qed.

Lemma check_setid_complete_unmodeled : forall get put user v m i eff,
  setid_spec get put user v i m Unmodeled ->
  check_setid get put user v eff m = CheckUnmodeled.
Proof.
  intros get put user v m i eff H.
  unfold setid_spec in H. unfold check_setid. sys_unfold.
  cbv iota in H. inv_ok. creds_split; inv_ok.
Qed.

(* ------------------------------------------------- setresuid / setresgid *)

Lemma check_setresid_sound_ok : forall get put user r e s eff m m' evs i,
  check_setresid get put user r e s eff m = CheckOk m' evs ->
  setresid_spec get put user r e s i m (Ok eff m' evs).
Proof.
  intros get put user r e s eff m m' evs i H.
  unfold check_setresid in H. unfold setresid_spec.
  eapply bind_ok0; [apply get_model_ok|].
  cbv beta zeta in H |- *. creds_split; creds_sound_leaf.
Qed.

Lemma check_setresid_sound_unmodeled : forall get put user r e s eff m i,
  check_setresid get put user r e s eff m = CheckUnmodeled ->
  setresid_spec get put user r e s i m Unmodeled.
Proof.
  intros get put user r e s eff m i H.
  unfold check_setresid in H. unfold setresid_spec.
  eapply bind_unmodeled2; [apply get_model_ok|].
  cbv beta zeta in H |- *. creds_split; creds_unmod_leaf.
Qed.

Lemma check_setresid_complete_ok : forall get put user r e s eff m m' evs i,
  setresid_spec get put user r e s i m (Ok eff m' evs) ->
  check_setresid get put user r e s eff m = CheckOk m' evs.
Proof.
  intros get put user r e s eff m m' evs i H.
  unfold setresid_spec in H. unfold check_setresid. sys_unfold.
  cbv iota in H. inv_ok. creds_split; inv_ok; creds_complete_leaf.
Qed.

Lemma check_setresid_complete_unmodeled : forall get put user r e s m i eff,
  setresid_spec get put user r e s i m Unmodeled ->
  check_setresid get put user r e s eff m = CheckUnmodeled.
Proof.
  intros get put user r e s m i eff H.
  unfold setresid_spec in H. unfold check_setresid. sys_unfold.
  cbv iota in H. inv_ok. creds_split; inv_ok.
Qed.
