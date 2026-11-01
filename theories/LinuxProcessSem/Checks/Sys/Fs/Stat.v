(** * LinuxProcessSem.Checks.Sys.Fs.Stat — the readlinkat (78), newfstatat (79) and fstat (80) checkers, and their proofs

    Mirrors [Sys/Fs/Stat.v], which answers to Linux [fs/stat.c]: this
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

(** [Stat.readlinkat_spec] as an acceptor: the [bufsiz] gate with an
    empty ledger, then every answer past it carries the pathname range,
    exactly as [check_newfstatat]'s do. *)
Definition check_readlinkat (i : SyscallInput) (dirfd : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let pathp := in_arg i 1 in
  let reads := [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] in
  if (sint32 (in_arg i 3) <=? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
  else
    match read_cstr (in_mem i) pathp with
    | CstrTooLong => check_ret_only_copyins reads eff (errno_ret ENAMETOOLONG) m []
    | CstrFault => check_ret_only_copyins reads eff (errno_ret EFAULT) m []
    | CstrOk p =>
        if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
        else if path_eqb p [] then check_ret_only_copyins reads eff (errno_ret ENOENT) m []
        else if proc_path_b p then CheckUnmodeled
        else check_ret_only_copyins reads eff (errno_ret EINVAL) m []
    end.

Lemma check_readlinkat_sound_ok : forall i dirfd eff m m' evs,
  check_readlinkat i dirfd eff m = CheckOk m' evs ->
  readlinkat_spec dirfd i m (Ok eff m' evs).
Proof.
  intros i dirfd eff m m' evs H.
  unfold check_readlinkat in H. cbv zeta in H. unfold readlinkat_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct ((sint32 (in_arg i 3) <=? 0)%Z) eqn:Hb.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->). apply pure_ok. }
  destruct (read_cstr (in_mem i) (in_arg i 1)) as [p| |] eqn:Hp.
  2: { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
       apply record_copyins_ok_empty; [reflexivity|].
       unfold readlinkat_core_spec.
       eapply bind_ok0; [apply input_ok|]. cbv beta. srw Hp. apply pure_ok. }
  2: { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
       apply record_copyins_ok_empty; [reflexivity|].
       unfold readlinkat_core_spec.
       eapply bind_ok0; [apply input_ok|]. cbv beta. srw Hp. apply pure_ok. }
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; [discriminate|].
  destruct (path_eqb p []) eqn:Hpe.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|].
    unfold readlinkat_core_spec.
    eapply bind_ok0; [apply input_ok|]. cbv beta. srw Hp. srw Hd. srw Hpe.
    apply pure_ok. }
  destruct (proc_path_b p) eqn:Hpp; [discriminate|].
  apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
  apply record_copyins_ok_empty; [reflexivity|].
  unfold readlinkat_core_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta. srw Hp. srw Hd. srw Hpe. srw Hpp.
  apply pure_ok.
Qed.

Lemma check_readlinkat_sound_unmodeled : forall i dirfd eff m,
  check_readlinkat i dirfd eff m = CheckUnmodeled ->
  readlinkat_spec dirfd i m Unmodeled.
Proof.
  intros i dirfd eff m H.
  unfold check_readlinkat in H. cbv zeta in H. unfold readlinkat_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct ((sint32 (in_arg i 3) <=? 0)%Z) eqn:Hb;
    [now apply check_ret_only_no_unmodeled in H|].
  apply record_copyins_unmodeled.
  destruct (read_cstr (in_mem i) (in_arg i 1)) as [p| |] eqn:Hp;
    [| now apply check_ret_only_copyins_no_unmodeled in H
     | now apply check_ret_only_copyins_no_unmodeled in H ].
  unfold readlinkat_core_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta. srw Hp.
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; [apply unmodeled_intro|].
  destruct (path_eqb p []) eqn:Hpe;
    [now apply check_ret_only_copyins_no_unmodeled in H|].
  destruct (proc_path_b p) eqn:Hpp; [apply unmodeled_intro|].
  now apply check_ret_only_copyins_no_unmodeled in H.
Qed.

Lemma check_readlinkat_complete_ok : forall i dirfd eff m m' evs,
  readlinkat_spec dirfd i m (Ok eff m' evs) ->
  check_readlinkat i dirfd eff m = CheckOk m' evs.
Proof.
  intros i dirfd eff m m' evs H.
  unfold readlinkat_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  unfold check_readlinkat. cbv zeta.
  destruct ((sint32 (in_arg i 3) <=? 0)%Z) eqn:Hb; cbv iota in H.
  { sys_unfold. inv_ok.
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity. }
  apply record_copyins_ok_inv in H. destruct H as (core & H & ->).
  unfold readlinkat_core_spec in H.
  sys_unfold. cbv iota in H. inv_ok.
  destruct (read_cstr (in_mem i) (in_arg i 1)) as [p| |] eqn:Hp; hall Hp; inv_ok;
    try (cbn [eff_copyins with_copyins app];
         apply check_ret_only_copyins_refl).
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; hall Hd; inv_ok.
  destruct (path_eqb p []) eqn:Hpe; hall Hpe; inv_ok.
  { cbn [eff_copyins with_copyins app]. apply check_ret_only_copyins_refl. }
  destruct (proc_path_b p) eqn:Hpp; hall Hpp; inv_ok.
  cbn [eff_copyins with_copyins app]. apply check_ret_only_copyins_refl.
Qed.

Lemma check_readlinkat_complete_unmodeled : forall i dirfd m eff,
  readlinkat_spec dirfd i m Unmodeled ->
  check_readlinkat i dirfd eff m = CheckUnmodeled.
Proof.
  intros i dirfd m eff H.
  unfold readlinkat_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  unfold check_readlinkat. cbv zeta.
  destruct ((sint32 (in_arg i 3) <=? 0)%Z) eqn:Hb; cbv iota in H.
  { exfalso. sys_unfold. inv_ok. }
  apply record_copyins_unmodeled_inv in H.
  unfold readlinkat_core_spec in H. sys_unfold. cbv iota in H. inv_ok.
  destruct (read_cstr (in_mem i) (in_arg i 1)) as [p| |] eqn:Hp; hall Hp; inv_ok;
    try discriminate.
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; hall Hd; inv_ok;
    try discriminate; [reflexivity|].
  destruct (path_eqb p []) eqn:Hpe; hall Hpe; inv_ok; try discriminate.
  destruct (proc_path_b p) eqn:Hpp; hall Hpp; inv_ok; try discriminate.
  reflexivity.
Qed.

(** [Stat.newfstatat_proc_spec] as an acceptor, under the pathname
    ledger [reads] that [newfstatat_spec] puts on every answer.  An
    error-encoded return with nothing written is the spec's
    [Syscall.errno_any] ([check_newfstatat_proc_errno]); over a wholly
    writable [statbuf] a 0 with ONE write of 128 bytes at [statbuf] that
    [stat_proc_buf_ok] passes is the delivery.  A [statbuf] inside the
    address space but not wholly writable is declined, as the spec
    declines it. *)
Definition check_newfstatat_proc_errno (reads : list (word * nat))
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] ci =>
      if errno_any_b ret && access_ranges_eqb ci reads
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

Definition check_newfstatat_proc (i : SyscallInput) (reads : list (word * nat))
    (statbuf : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb statbuf STAT_SIZE)
  then check_newfstatat_proc_errno reads eff m
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => CheckUnmodeled
    | Some _ =>
        match eff with
        | mkEffectU ret [(a, bs)] [] [] [] ci =>
            if bv_eqb ret (Z_to_bv 64 0) && bv_eqb a statbuf
               && stat_proc_buf_ok bs && access_ranges_eqb ci reads
            then CheckOk m [] else CheckReject
        | _ => check_newfstatat_proc_errno reads eff m
        end
    end.

Lemma check_newfstatat_proc_errno_ok : forall reads eff m m' evs,
  check_newfstatat_proc_errno reads eff m = CheckOk m' evs ->
  eff_copyins eff = reads /\ m' = m /\ evs = [] /\
  exists e, ((1 <= e <= 4095)%Z /\ e <> EINTR) /\
            clear_copyins eff = mkEffect (errno_ret e) [] [].
Proof.
  intros reads [ret ws zs us cs ci] m m' evs H.
  unfold check_newfstatat_proc_errno in H.
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; cbv beta iota in H; try discriminate.
  destruct (errno_any_b ret) eqn:He; cbn [andb] in H; [|discriminate].
  destruct (access_ranges_eqb ci reads) eqn:Hci; [|discriminate].
  inversion H; clear H; subst.
  apply access_ranges_eqb_eq in Hci. subst ci.
  apply errno_any_b_errno in He. destruct He as (e & He & ->).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  exists e. split; [exact He|reflexivity].
Qed.

Lemma check_newfstatat_proc_errno_no_unmodeled : forall reads eff m,
  check_newfstatat_proc_errno reads eff m <> CheckUnmodeled.
Proof.
  intros reads [ret ws zs us cs ci] m. unfold check_newfstatat_proc_errno.
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; cbv beta iota; try discriminate.
  destruct (errno_any_b ret && access_ranges_eqb ci reads); discriminate.
Qed.

Lemma check_newfstatat_proc_sound_ok : forall i reads statbuf eff m m' evs,
  check_newfstatat_proc i reads statbuf eff m = CheckOk m' evs ->
  eff_copyins eff = reads /\
  newfstatat_proc_spec statbuf i m (Ok (clear_copyins eff) m' evs).
Proof.
  intros i reads statbuf eff m m' evs H.
  unfold check_newfstatat_proc in H. unfold newfstatat_proc_spec.
  assert (Herr : check_newfstatat_proc_errno reads eff m = CheckOk m' evs ->
                 eff_copyins eff = reads /\
                 bind errno_any (fun e => err_ret e) i m
                   (Ok (clear_copyins eff) m' evs)).
  { intro He. apply check_newfstatat_proc_errno_ok in He.
    destruct He as (Hci & -> & -> & e & He & Hc).
    split; [exact Hci|]. rewrite Hc.
    eapply bind_ok0; [unfold errno_any; apply (choose_ok _ e); exact He|].
    apply pure_ok. }
  destruct (negb (access_okb statbuf STAT_SIZE)).
  { destruct (Herr H) as (Hci & Hs). split; [exact Hci|].
    eapply bind_ok0; [apply input_ok|]. exact Hs. }
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|] eqn:Hw;
    [|discriminate].
  destruct eff as [ret ws zs us cs ci].
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?];
    try (destruct (Herr H) as (Hci & Hs); split; [exact Hci|];
         eapply bind_ok0; [apply input_ok|]; cbv beta; srw Hw;
         apply alt_l; exact Hs).
  cbv beta iota in H.
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a statbuf
            && stat_proc_buf_ok bs && access_ranges_eqb ci reads) eqn:Hb;
    [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in Hb as [Hb Hci]. apply andb_true_iff in Hb as [Hb Hok].
  apply andb_true_iff in Hb as [Hr Ha].
  apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. apply access_ranges_eqb_eq in Hci.
  subst ret a ci. split; [reflexivity|].
  eapply bind_ok0; [apply input_ok|]. cbv beta. srw Hw.
  apply alt_r. eapply bind_ok0; [apply (choose_ok _ bs); exact Hok|].
  apply pure_ok.
Qed.

Lemma check_newfstatat_proc_sound_unmodeled : forall i reads statbuf eff m,
  check_newfstatat_proc i reads statbuf eff m = CheckUnmodeled ->
  newfstatat_proc_spec statbuf i m Unmodeled.
Proof.
  intros i reads statbuf eff m H.
  unfold check_newfstatat_proc in H. unfold newfstatat_proc_spec.
  destruct (negb (access_okb statbuf STAT_SIZE)).
  { exfalso. exact (check_newfstatat_proc_errno_no_unmodeled _ _ _ H). }
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|];
    [|apply unmodeled_intro].
  exfalso.
  destruct eff as [ret ws zs us cs ci].
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; cbv beta iota in H;
    try exact (check_newfstatat_proc_errno_no_unmodeled _ _ _ H).
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a statbuf
            && stat_proc_buf_ok bs && access_ranges_eqb ci reads); discriminate.
Qed.

Lemma check_newfstatat_proc_complete_ok : forall i reads statbuf core m m' evs,
  newfstatat_proc_spec statbuf i m (Ok core m' evs) ->
  eff_copyins core = [] /\
  check_newfstatat_proc i reads statbuf (with_copyins reads core) m = CheckOk m' evs.
Proof.
  intros i reads statbuf core m m' evs H.
  unfold newfstatat_proc_spec, errno_any in H. unfold check_newfstatat_proc.
  sys_unfold. cbv beta iota in H. inv_ok.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha; hall Ha; inv_ok.
  { split; [reflexivity|].
    cbn [eff_copyins eff_ret eff_writes eff_zeros eff_unmaps eff_copies
         check_newfstatat_proc_errno].
    rewrite errno_any_b_ret by (intuition lia). rewrite access_ranges_eqb_refl.
    reflexivity. }
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|] eqn:Hw;
    hall Hw; inv_ok.
  - split; [reflexivity|].
    cbn [eff_copyins eff_ret eff_writes eff_zeros eff_unmaps eff_copies
         check_newfstatat_proc_errno].
    rewrite errno_any_b_ret by (intuition lia). rewrite access_ranges_eqb_refl.
    reflexivity.
  - split; [reflexivity|].
    cbn [eff_copyins eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
    rewrite !bv_eqb_refl, access_ranges_eqb_refl.
    match goal with H : stat_proc_buf_ok _ = true |- _ => rewrite H end.
    reflexivity.
Qed.

Lemma check_newfstatat_proc_complete_unmodeled : forall i reads statbuf eff m,
  newfstatat_proc_spec statbuf i m Unmodeled ->
  check_newfstatat_proc i reads statbuf eff m = CheckUnmodeled.
Proof.
  intros i reads statbuf eff m H.
  unfold newfstatat_proc_spec, errno_any in H. unfold check_newfstatat_proc.
  sys_unfold. cbv beta iota in H. inv_ok.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha; hall Ha; inv_ok.
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|] eqn:Hw;
    hall Hw; inv_ok.
  reflexivity.
Qed.

(** newfstatat: the FAILING side is modeled, and it writes nothing —
    a flag word outside {0, AT_SYMLINK_NOFOLLOW}, a dirfd other than
    AT_FDCWD, ".", and any path the file system holds all fail closed,
    because a successful call would have to deliver 128 bytes of
    metadata [Fs] does not carry (see [Stat.newfstatat_spec]).  The one
    arm that can deliver is a name relative to an O_PATH procfs
    descriptor, [check_newfstatat_proc] above.  Writing
    nothing is not reading nothing: each accepting arm is
    [check_ret_only_copyins], which is [check_ret_only]'s empty-effect
    demand on everything BUT the copy-in list, plus an equality on that
    list.  Plain [check_ret_only] would insist the ledger be empty and
    so reject the truthful effect.  The range is the one
    [Open.check_openat] demands, because both syscalls run the same
    [getname_flags]; unlike openat's, no arm here copies in again after
    it, so the whole claimed list is that single range. *)
Definition check_newfstatat (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let reads := [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] in
  if negb (modeled_statat_flags flag) then CheckUnmodeled
  else
    match read_cstr (in_mem i) pathp with
    | CstrTooLong => check_ret_only_copyins reads eff (errno_ret ENAMETOOLONG) m []
    | CstrFault => check_ret_only_copyins reads eff (errno_ret EFAULT) m []
    | CstrOk p =>
        if path_eqb p [] then check_ret_only_copyins reads eff (errno_ret ENOENT) m []
        else if negb (bv_eqb dirfd AT_FDCWD32) then
          (if newfstatat_proc_dir (m_fds m) dirfd p
           then check_newfstatat_proc i reads (in_arg i 2) eff m
           else CheckUnmodeled)
        else if path_eqb p dot_path then CheckUnmodeled
        else if proc_path_b p then CheckUnmodeled
        else
        match fs_lookup (m_fs m) p with
        | None => check_ret_only_copyins reads eff (errno_ret ENOENT) m []
        | Some _ => CheckUnmodeled
        end
    end.

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

Lemma check_newfstatat_sound_ok : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs ->
  newfstatat_spec dirfd pathp flag i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flag eff m m' evs H.
  unfold check_newfstatat in H. cbv zeta in H. unfold newfstatat_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl; [discriminate|].
  cbv iota in H.
  (* Every accepting arm returns an errno and the one pathname range, so
     the wrapper is stripped the same way on each: the core effect has an
     empty ledger, and [record_copyins_ok_empty] puts [reads] on it. *)
  destruct (read_cstr (in_mem i) pathp) as [p| |] eqn:Hp.
  2: { (* no NUL within PATH_MAX: a real -ENAMETOOLONG *)
    apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|].
    unfold newfstatat_core_spec.
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfl. srw Hp. apply pure_ok. }
  2: { (* unmapped byte before the NUL: a real -EFAULT, and the faulting
          byte's page is charged all the same *)
    apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|].
    unfold newfstatat_core_spec.
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfl. srw Hp. apply pure_ok. }
  destruct (path_eqb p []) eqn:Hpe.
  { (* empty pathname: -ENOENT *)
    apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|].
    unfold newfstatat_core_spec.
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfl. srw Hp. srw Hpe. apply pure_ok. }
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd.
  { (* relative to an O_PATH procfs descriptor: [check_newfstatat_proc] *)
    destruct (newfstatat_proc_dir (m_fds m) dirfd p) eqn:Hpd; cbv beta iota in H;
      [|discriminate].
    apply check_newfstatat_proc_sound_ok in H. destruct H as (Hci & H).
    apply record_copyins_clear_ok; [exact Hci|].
    unfold newfstatat_core_spec.
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfl. srw Hp. srw Hpe. srw Hd. srw Hpd. exact H. }
  destruct (path_eqb p dot_path) eqn:Hdot; [discriminate|].
  destruct (proc_path_b p) eqn:Hpp; [discriminate|].
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [discriminate|].
  (* the file is absent: -ENOENT *)
  apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
  apply record_copyins_ok_empty; [reflexivity|].
  unfold newfstatat_core_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
  srw Hfl. srw Hp. srw Hpe. srw Hd. srw Hdot. srw Hpp. srw Hfs.
  apply pure_ok.
Qed.

Lemma check_newfstatat_sound_unmodeled : forall i dirfd pathp flag eff m,
  check_newfstatat i dirfd pathp flag eff m = CheckUnmodeled ->
  newfstatat_spec dirfd pathp flag i m Unmodeled.
Proof.
  intros i dirfd pathp flag eff m H.
  unfold check_newfstatat in H. cbv zeta in H. unfold newfstatat_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  (* [record_copyins] carries a decline through untouched, so recording
     the pathname costs the declining arms nothing. *)
  apply record_copyins_unmodeled.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl.
  { unfold newfstatat_core_spec.
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfl. apply unmodeled_intro. }
  cbv iota in H.
  destruct (read_cstr (in_mem i) pathp) as [p| |] eqn:Hp;
    [| now apply check_ret_only_copyins_no_unmodeled in H
     | now apply check_ret_only_copyins_no_unmodeled in H ].
  destruct (path_eqb p []) eqn:Hpe.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd.
  { unfold newfstatat_core_spec.
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfl. srw Hp. srw Hpe. srw Hd.
    destruct (newfstatat_proc_dir (m_fds m) dirfd p) eqn:Hpd; cbv beta iota in H |- *;
      [|apply unmodeled_intro].
    exact (check_newfstatat_proc_sound_unmodeled _ _ _ _ _ H). }
  destruct (path_eqb p dot_path) eqn:Hdot.
  { unfold newfstatat_core_spec.
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfl. srw Hp. srw Hpe. srw Hd. srw Hdot. apply unmodeled_intro. }
  destruct (proc_path_b p) eqn:Hpp.
  { unfold newfstatat_core_spec.
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfl. srw Hp. srw Hpe. srw Hd. srw Hdot. srw Hpp. apply unmodeled_intro. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
    [|now apply check_ret_only_copyins_no_unmodeled in H].
  unfold newfstatat_core_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
  srw Hfl. srw Hp. srw Hpe. srw Hd. srw Hdot. srw Hpp. srw Hfs. apply unmodeled_intro.
Qed.

Lemma check_newfstatat_complete_ok : forall i dirfd pathp flag eff m m' evs,
  newfstatat_spec dirfd pathp flag i m (Ok eff m' evs) ->
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp flag eff m m' evs H.
  unfold newfstatat_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply record_copyins_ok_inv in H. destruct H as (core & H & ->).
  unfold newfstatat_core_spec in H. unfold check_newfstatat. cbv zeta.
  sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl; hall Hfl; inv_ok.
  destruct (read_cstr (in_mem i) pathp) as [p| |] eqn:Hp; hall Hp; inv_ok;
    try (cbn [eff_copyins with_copyins app];
         apply check_ret_only_copyins_refl).
  destruct (path_eqb p []) eqn:Hpe; hall Hpe; inv_ok.
  { cbn [eff_copyins with_copyins app]. apply check_ret_only_copyins_refl. }
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; hall Hd; inv_ok.
  { (* relative to an O_PATH procfs descriptor *)
    destruct (newfstatat_proc_dir (m_fds m) dirfd p) eqn:Hpd; hall Hpd; inv_ok.
    match goal with
    | Hs : newfstatat_proc_spec _ _ _ (Ok _ _ _) |- _ =>
        destruct (check_newfstatat_proc_complete_ok i
                    [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
                    _ _ _ _ _ Hs) as (Hci & Hc)
    end.
    rewrite Hci. exact Hc. }
  destruct (path_eqb p dot_path) eqn:Hdot; hall Hdot; inv_ok.
  destruct (proc_path_b p) eqn:Hpp; hall Hpp; inv_ok.
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok.
  cbn [eff_copyins with_copyins app]. apply check_ret_only_copyins_refl.
Qed.

Lemma check_newfstatat_complete_unmodeled : forall i dirfd pathp flag m eff,
  newfstatat_spec dirfd pathp flag i m Unmodeled ->
  check_newfstatat i dirfd pathp flag eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp flag m eff H.
  unfold newfstatat_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply record_copyins_unmodeled_inv in H.
  unfold newfstatat_core_spec in H. unfold check_newfstatat. cbv zeta.
  sys_unfold. cbv iota in H. inv_ok.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl; hall Hfl; inv_ok;
    try discriminate; [reflexivity|].
  destruct (read_cstr (in_mem i) pathp) as [p| |] eqn:Hp; hall Hp; inv_ok;
    try discriminate.
  destruct (path_eqb p []) eqn:Hpe; hall Hpe; inv_ok; try discriminate.
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; hall Hd; inv_ok;
    try discriminate.
  { destruct (newfstatat_proc_dir (m_fds m) dirfd p) eqn:Hpd; hall Hpd;
      [now apply check_newfstatat_proc_complete_unmodeled|reflexivity]. }
  destruct (path_eqb p dot_path) eqn:Hdot; hall Hdot; inv_ok;
    try discriminate; [reflexivity|].
  destruct (proc_path_b p) eqn:Hpp; hall Hpp; inv_ok;
    try discriminate; [reflexivity|].
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok;
    try discriminate; reflexivity.
Qed.

(** The delivering half of [Stat.fstat_file_spec], mirroring its
    [choose] arm for arm.  The effect must be ONE 128-byte write at
    [statbuf] returning 0 and nothing else — no zero range, no unmap, no
    symbolic copy, and an EMPTY copy-in ledger, because [fstat] takes
    its descriptor in a register and reads no user byte at all.  The
    bytes themselves are then judged by the two predicates the spec
    chooses under, plus the pin.

    THE PIN IS INSTALLED HERE on the branch that had none, exactly as
    [Checks.Sys.Kernel.Sys]'s [check_uname_copy] installs the UTS name:
    the bytes are the KERNEL's, so the model records what it was shown
    rather than reconstructing it. *)
Definition check_fstat_deliver_by (ok : list byte -> bool) (statbuf : word)
    (p : Fs.path) (pin : option (list byte)) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU r [(a, bs)] [] [] [] [] =>
      if negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf)%bool then CheckReject
      else if negb (stat_buf_wf bs && ok bs)%bool then CheckReject
      else match pin with
           | Some b0 => if stat_stable_eqb bs b0 then CheckOk m [] else CheckReject
           | None => CheckOk (with_statpin p bs m) []
           end
  | _ => CheckReject
  end.

(** The file arms' delivery: the predicate is the file's [st_size]
    implication.  [check_fstat_devnull] below instantiates the same
    acceptor with the device's assertions. *)
Definition check_fstat_deliver (statbuf : word) (n : nat) (p : Fs.path)
    (pin : option (list byte)) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_fstat_deliver_by (stat_size_ok n) statbuf p pin eff m.

(** The file arms of [Stat.fstat_spec], branch for branch with
    [Stat.fstat_file_spec]: an unlinked path and a partially writable
    destination decline, [access_ok]'s refusal is -EFAULT, and the rest
    is the delivery above. *)
Definition check_fstat_file (i : SyscallInput) (p : Fs.path) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fs_lookup (m_fs m) p with
  | None => CheckUnmodeled
  | Some data =>
      if negb (access_okb statbuf STAT_SIZE)
      then check_ret_only eff (errno_ret EFAULT) m []
      else
        match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
        | None => CheckUnmodeled
        | Some _ =>
            match statpin_lookup (m_statpins m) p with
            | Some b0 =>
                if negb (stat_buf_wf b0) then CheckUnmodeled
                else check_fstat_deliver statbuf (length data) p (Some b0) eff m
            | None => check_fstat_deliver statbuf (length data) p None eff m
            end
        end
  end.

Lemma check_fstat_deliver_by_no_unmodeled : forall ok statbuf p pin eff m,
  check_fstat_deliver_by ok statbuf p pin eff m <> CheckUnmodeled.
Proof.
  intros ok statbuf p pin [r ws zs us cs copyins] m.
  unfold check_fstat_deliver_by.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf)%bool);
    [discriminate|].
  destruct (negb (stat_buf_wf bs && ok bs)%bool); [discriminate|].
  destruct pin as [b0|]; [destruct (stat_stable_eqb bs b0)|]; discriminate.
Qed.

Lemma check_fstat_deliver_no_unmodeled : forall statbuf n p pin eff m,
  check_fstat_deliver statbuf n p pin eff m <> CheckUnmodeled.
Proof.
  intros statbuf n p pin [r ws zs us cs copyins] m.
  unfold check_fstat_deliver, check_fstat_deliver_by.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf)%bool);
    [discriminate|].
  destruct (negb (stat_buf_wf bs && stat_size_ok n bs)%bool); [discriminate|].
  destruct pin as [b0|]; [destruct (stat_stable_eqb bs b0)|]; discriminate.
Qed.

(** What a [CheckOk] out of the delivery arm tells you: the effect is
    one 128-byte write of a well-formed [struct stat] at [statbuf]
    returning 0, and either it repeated the file's pin or it created
    one. *)
Lemma check_fstat_deliver_by_ok : forall ok statbuf p pin eff m m' evs,
  check_fstat_deliver_by ok statbuf p pin eff m = CheckOk m' evs ->
  exists bs, eff = mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []
             /\ evs = []
             /\ stat_buf_wf bs = true
             /\ ok bs = true
             /\ ((exists b0, pin = Some b0 /\ stat_stable_eqb bs b0 = true /\ m' = m)
                 \/ (pin = None /\ m' = with_statpin p bs m)).
Proof.
  intros ok statbuf p pin [r ws zs us cs copyins] m m' evs H.
  unfold check_fstat_deliver_by in H.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf)%bool) eqn:HG;
    [discriminate|].
  apply Bool.negb_false_iff in HG. apply andb_true_iff in HG as [HR HA].
  apply bv_eqb_eq in HR; subst r. apply bv_eqb_eq in HA; subst a.
  destruct (negb (stat_buf_wf bs && ok bs)%bool) eqn:HW;
    [discriminate|].
  apply Bool.negb_false_iff in HW. apply andb_true_iff in HW as [HWF HSZ].
  exists bs. destruct pin as [b0|].
  - destruct (stat_stable_eqb bs b0) eqn:HS; [|discriminate].
    inversion H; clear H; subst.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HWF|].
    split; [exact HSZ|]. left. exists b0. now repeat split.
  - inversion H; clear H; subst.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HWF|].
    split; [exact HSZ|]. right. now split.
Qed.

Lemma check_fstat_deliver_ok : forall statbuf n p pin eff m m' evs,
  check_fstat_deliver statbuf n p pin eff m = CheckOk m' evs ->
  exists bs, eff = mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []
             /\ evs = []
             /\ stat_buf_wf bs = true
             /\ stat_size_ok n bs = true
             /\ ((exists b0, pin = Some b0 /\ stat_stable_eqb bs b0 = true /\ m' = m)
                 \/ (pin = None /\ m' = with_statpin p bs m)).
Proof.
  intros statbuf n p pin [r ws zs us cs copyins] m m' evs H.
  unfold check_fstat_deliver, check_fstat_deliver_by in H.
  destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (negb (bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf)%bool) eqn:HG;
    [discriminate|].
  apply Bool.negb_false_iff in HG. apply andb_true_iff in HG as [HR HA].
  apply bv_eqb_eq in HR; subst r. apply bv_eqb_eq in HA; subst a.
  destruct (negb (stat_buf_wf bs && stat_size_ok n bs)%bool) eqn:HW;
    [discriminate|].
  apply Bool.negb_false_iff in HW. apply andb_true_iff in HW as [HWF HSZ].
  exists bs. destruct pin as [b0|].
  - destruct (stat_stable_eqb bs b0) eqn:HS; [|discriminate].
    inversion H; clear H; subst.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HWF|].
    split; [exact HSZ|]. left. exists b0. now repeat split.
  - inversion H; clear H; subst.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HWF|].
    split; [exact HSZ|]. right. now split.
Qed.

Lemma check_fstat_file_sound_ok : forall i p statbuf eff m m' evs,
  check_fstat_file i p statbuf eff m = CheckOk m' evs ->
  fstat_file_spec p statbuf i m (Ok eff m' evs).
Proof.
  intros i p statbuf eff m m' evs H.
  unfold check_fstat_file in H. unfold fstat_file_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
  cbv iota.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|discriminate].
    cbv iota.
    destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp.
    + destruct (negb (stat_buf_wf b0)) eqn:Hb0; [discriminate|].
      cbv iota.
      apply check_fstat_deliver_ok in H
        as (bs & -> & -> & HWF & HSZ & [(b1 & Hpin & HS & ->)|(Hpin & ->)]);
        [|discriminate Hpin].
      inversion Hpin; clear Hpin; subst b1.
      eapply bind_ok0; [apply (choose_ok _ bs); repeat split; eassumption|].
      apply pure_ok.
    + apply check_fstat_deliver_ok in H
        as (bs & -> & -> & HWF & HSZ & [(b1 & Hpin & _ & _)|(_ & ->)]);
        [discriminate Hpin|].
      eapply bind_ok0; [apply (choose_ok _ bs); split; eassumption|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_fstat_file_sound_unmodeled : forall i p statbuf eff m,
  check_fstat_file i p statbuf eff m = CheckUnmodeled ->
  fstat_file_spec p statbuf i m Unmodeled.
Proof.
  intros i p statbuf eff m H.
  unfold check_fstat_file in H. unfold fstat_file_spec.
  eapply bind_unmodeled2; [apply input_ok|].
  eapply bind_unmodeled2; [apply get_model_ok|].
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
    [cbv iota|cbv iota; apply unmodeled_intro].
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [cbv iota|cbv iota; apply unmodeled_intro].
    destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp.
    + destruct (negb (stat_buf_wf b0)) eqn:Hb0;
        [cbv iota; apply unmodeled_intro|].
      now apply check_fstat_deliver_no_unmodeled in H.
    + now apply check_fstat_deliver_no_unmodeled in H.
Qed.

Lemma check_fstat_file_complete_ok : forall i p statbuf eff m m' evs,
  fstat_file_spec p statbuf i m (Ok eff m' evs) ->
  check_fstat_file i p statbuf eff m = CheckOk m' evs.
Proof.
  intros i p statbuf eff m m' evs H.
  unfold fstat_file_spec in H. unfold check_fstat_file.
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
    [|sys_unfold; inv_ok; hall Hfs; inv_ok].
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - sys_unfold; inv_ok; hall Hfs; hall Ha; inv_ok.
    apply check_ret_only_ok_iff. now repeat split.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|sys_unfold; inv_ok; hall Hfs; hall Ha; hall Hw; inv_ok].
    destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp.
    + destruct (negb (stat_buf_wf b0)) eqn:Hb0;
        [sys_unfold; inv_ok; hall Hfs; hall Ha; hall Hw; hall Hp; hall Hb0;
         inv_ok|].
      sys_unfold; inv_ok; hall Hfs; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok.
      unfold check_fstat_deliver, check_fstat_deliver_by.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : stat_size_ok _ ?b = true,
        H3 : stat_stable_eqb ?b _ = true |- _ =>
          rewrite H1, H2; cbn [andb negb]; rewrite H3
      end.
      reflexivity.
    + sys_unfold; inv_ok; hall Hfs; hall Ha; hall Hw; hall Hp; inv_ok.
      unfold check_fstat_deliver, check_fstat_deliver_by.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : stat_size_ok _ ?b = true |- _ =>
          rewrite H1, H2
      end.
      cbn [andb negb]. reflexivity.
Qed.

(** The character-device arm, branch for branch with
    [Stat.fstat_chrdev_spec]: no [fs_lookup], the pin checked against
    both predicates, and the delivery judged under the device's [ok].
    The null and random devices below are its two instances, as the
    spec's are. *)
Definition check_fstat_chrdev (ok : list byte -> bool) (p : Fs.path)
    (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb statbuf STAT_SIZE)
  then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => CheckUnmodeled
    | Some _ =>
        match statpin_lookup (m_statpins m) p with
        | Some b0 =>
            if negb (stat_buf_wf b0 && ok b0)%bool then CheckUnmodeled
            else check_fstat_deliver_by ok statbuf p
                   (Some b0) eff m
        | None => check_fstat_deliver_by ok statbuf p
                    None eff m
        end
    end.

Lemma check_fstat_chrdev_sound_ok : forall ok p i statbuf eff m m' evs,
  check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs ->
  fstat_chrdev_spec p ok statbuf i m (Ok eff m' evs).
Proof.
  intros ok p i statbuf eff m m' evs H.
  unfold check_fstat_chrdev in H. unfold fstat_chrdev_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|discriminate].
    cbv iota.
    destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp.
    + destruct (negb (stat_buf_wf b0 && ok b0)%bool) eqn:Hb0;
        [discriminate|].
      cbv iota.
      apply check_fstat_deliver_by_ok in H
        as (bs & -> & -> & HWF & HOK & [(b1 & Hpin & HS & ->)|(Hpin & ->)]);
        [|discriminate Hpin].
      inversion Hpin; clear Hpin; subst b1.
      eapply bind_ok0; [apply (choose_ok _ bs); repeat split; eassumption|].
      apply pure_ok.
    + apply check_fstat_deliver_by_ok in H
        as (bs & -> & -> & HWF & HOK & [(b1 & Hpin & _ & _)|(_ & ->)]);
        [discriminate Hpin|].
      eapply bind_ok0; [apply (choose_ok _ bs); split; eassumption|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_fstat_chrdev_sound_unmodeled : forall ok p i statbuf eff m,
  check_fstat_chrdev ok p i statbuf eff m = CheckUnmodeled ->
  fstat_chrdev_spec p ok statbuf i m Unmodeled.
Proof.
  intros ok p i statbuf eff m H.
  unfold check_fstat_chrdev in H. unfold fstat_chrdev_spec.
  eapply bind_unmodeled2; [apply input_ok|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [cbv iota|cbv iota; apply unmodeled_intro].
    destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp.
    + destruct (negb (stat_buf_wf b0 && ok b0)%bool) eqn:Hb0;
        [cbv iota; apply unmodeled_intro|].
      now apply check_fstat_deliver_by_no_unmodeled in H.
    + now apply check_fstat_deliver_by_no_unmodeled in H.
Qed.

Lemma check_fstat_chrdev_complete_ok : forall ok p i statbuf eff m m' evs,
  fstat_chrdev_spec p ok statbuf i m (Ok eff m' evs) ->
  check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs.
Proof.
  intros ok p i statbuf eff m m' evs H.
  unfold fstat_chrdev_spec in H. unfold check_fstat_chrdev.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - sys_unfold; inv_ok; hall Ha; inv_ok.
    apply check_ret_only_ok_iff. now repeat split.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|sys_unfold; inv_ok; hall Ha; hall Hw; inv_ok].
    destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp.
    + destruct (negb (stat_buf_wf b0 && ok b0)%bool) eqn:Hb0;
        [sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok|].
      sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok.
      unfold check_fstat_deliver_by.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : ok ?b = true,
        H3 : stat_stable_eqb ?b _ = true |- _ =>
          rewrite H1, H2; cbn [andb negb]; rewrite H3
      end.
      reflexivity.
    + sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; inv_ok.
      unfold check_fstat_deliver_by.
      rewrite !bv_eqb_refl; cbn [andb negb].
      match goal with
      | H1 : stat_buf_wf ?b = true, H2 : ok ?b = true |- _ =>
          rewrite H1, H2
      end.
      cbn [andb negb]. reflexivity.
Qed.

Lemma check_fstat_chrdev_complete_unmodeled : forall ok p i statbuf m eff,
  fstat_chrdev_spec p ok statbuf i m Unmodeled ->
  check_fstat_chrdev ok p i statbuf eff m = CheckUnmodeled.
Proof.
  intros ok p i statbuf m eff H.
  unfold fstat_chrdev_spec in H. unfold check_fstat_chrdev.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - exfalso. sys_unfold; inv_ok; hall Ha; inv_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|reflexivity].
    destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp.
    + destruct (negb (stat_buf_wf b0 && ok b0)%bool) eqn:Hb0;
        [reflexivity|].
      exfalso. sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; hall Hb0; inv_ok.
    + exfalso. sys_unfold; inv_ok; hall Ha; hall Hw; hall Hp; inv_ok.
Qed.

(** The two instances, and their lemmas by instantiation. *)
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

Lemma check_fstat_file_complete_unmodeled : forall i p statbuf m eff,
  fstat_file_spec p statbuf i m Unmodeled ->
  check_fstat_file i p statbuf eff m = CheckUnmodeled.
Proof.
  intros i p statbuf m eff H.
  unfold fstat_file_spec in H. unfold check_fstat_file.
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|reflexivity].
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha.
  - exfalso. sys_unfold; inv_ok; hall Hfs; hall Ha; inv_ok.
  - destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
      as [w|] eqn:Hw; [|reflexivity].
    destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp.
    + destruct (negb (stat_buf_wf b0)) eqn:Hb0; [reflexivity|].
      exfalso. sys_unfold; inv_ok; hall Hfs; hall Ha; hall Hw; hall Hp;
        hall Hb0; inv_ok.
    + exfalso. sys_unfold; inv_ok; hall Hfs; hall Ha; hall Hw; hall Hp; inv_ok.
Qed.

(** fstat: total over [FdEntry], answering on the closed descriptor's
    -EBADF, the four file kinds, which share one inode and so one
    answer, /dev/null and /dev/urandom.  The other five decline as a
    body; see [Stat.fstat_spec] for which of [struct stat]'s twenty
    members each would have to invent, and for why the match carries no
    wildcard. *)
Definition check_fstat (i : SyscallInput) (fd statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) => CheckUnmodeled
  | Some (FdFile p _)  => check_fstat_file i p statbuf eff m
  | Some (FdFileW p _) => check_fstat_file i p statbuf eff m
  | Some (FdFileA p _) => check_fstat_file i p statbuf eff m
  | Some (FdFileRW p _) => check_fstat_file i p statbuf eff m
  | Some FdDir         => CheckUnmodeled
  | Some (FdSocket _)  => CheckUnmodeled
  | Some (FdPipe _ _)  => CheckUnmodeled
  | Some (FdDevNull _ _) => check_fstat_devnull i statbuf eff m
  | Some FdUrandom => check_fstat_urandom i statbuf eff m
  | Some (FdOpaque _) => CheckUnmodeled
  end.

Lemma check_fstat_sound_ok : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs ->
  fstat_spec fd statbuf i m (Ok eff m' evs).
Proof.
  intros i fd statbuf eff m m' evs H.
  unfold check_fstat in H. unfold fstat_spec.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota;
    [destruct e; try discriminate;
     first [now apply check_fstat_file_sound_ok
           |now apply check_fstat_devnull_sound_ok
           |now apply check_fstat_urandom_sound_ok]|].
  apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
Qed.

Lemma check_fstat_sound_unmodeled : forall i fd statbuf eff m,
  check_fstat i fd statbuf eff m = CheckUnmodeled ->
  fstat_spec fd statbuf i m Unmodeled.
Proof.
  intros i fd statbuf eff m H.
  unfold check_fstat in H. unfold fstat_spec.
  eapply bind_unmodeled2; [apply get_model_ok|].
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv beta iota;
    [|now apply check_ret_only_no_unmodeled in H].
  destruct e; try apply unmodeled_intro;
    first [eapply check_fstat_file_sound_unmodeled; exact H
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
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota in H;
    [destruct e; try (now apply check_fstat_file_complete_ok);
       try (now apply check_fstat_devnull_complete_ok);
       try (now apply check_fstat_urandom_complete_ok);
       unfold unmodeled in H; discriminate|].
  unfold pure in H. inversion H; clear H; subst.
  apply check_ret_only_ok_iff. now repeat split.
Qed.

Lemma check_fstat_complete_unmodeled : forall i fd statbuf m eff,
  fstat_spec fd statbuf i m Unmodeled ->
  check_fstat i fd statbuf eff m = CheckUnmodeled.
Proof.
  intros i fd statbuf m eff H.
  unfold fstat_spec in H. unfold check_fstat.
  apply bind_get_model_unmodeled_inv in H. cbv beta in H.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota in H;
    [destruct e; try reflexivity;
       first [eapply check_fstat_file_complete_unmodeled; exact H
             |eapply check_fstat_devnull_complete_unmodeled; exact H
             |eapply check_fstat_urandom_complete_unmodeled; exact H]|].
  unfold pure in H. discriminate.
Qed.
