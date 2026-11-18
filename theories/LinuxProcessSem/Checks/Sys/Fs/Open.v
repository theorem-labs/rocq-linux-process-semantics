(** * LinuxProcessSem.Checks.Sys.Fs.Open — the openat (56), close (57), ftruncate (46) checkers, and their proofs

    Mirrors [Sys/Fs/Open.v], which answers to Linux [fs/open.c]: this
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
  Prelude Fs.ReadWrite.

Lemma alloc_fd_aux_le : forall fuel fds cand,
  (bv_unsigned cand + Z.of_nat fuel < two_pow_64)%Z ->
  (bv_unsigned (alloc_fd_aux fds cand fuel)
     <= bv_unsigned cand + Z.of_nat fuel)%Z.
Proof.
  induction fuel as [|f IH]; intros fds cand Hb; cbn [alloc_fd_aux].
  - lia.
  - destruct (fd_lookup fds cand).
    + assert (Hu : bv_unsigned (cand + 1) = (bv_unsigned cand + 1)%Z).
      { rewrite bv_add_unsigned.
        replace (bv_unsigned (1 : word)) with 1%Z by reflexivity.
        apply bv_wrap_small.
        unfold bv_modulus. change (Z.of_N 64) with 64%Z.
        pose proof (word_unsigned_range cand). unfold two_pow_64 in *. lia. }
      specialize (IH fds (cand + 1)). rewrite Hu in IH. lia.
    + pose proof (word_unsigned_range cand). lia.
Qed.

Lemma alloc_fd_le : forall fds, (bv_unsigned (alloc_fd fds) <= 4096)%Z.
Proof.
  intro fds. unfold alloc_fd.
  pose proof (alloc_fd_aux_le 4096 fds (Z_to_bv 64 0)) as H.
  rewrite Z_to_bv_small in H
    by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
  unfold two_pow_64 in H. lia.
Qed.

Lemma alloc_fd_not_error_b : forall fds, addr_is_error_b (alloc_fd fds) = false.
Proof.
  intro fds. pose proof (alloc_fd_le fds) as H.
  unfold addr_is_error_b, two_pow_64.
  apply Z.ltb_ge. lia.
Qed.

(** In particular an allocated fd never matches an injectable errno. *)

Lemma errno_ret_in_alloc_fd : forall es fds,
  errnos_ok es = true -> errno_ret_in es (alloc_fd fds) = false.
Proof.
  intros es fds Hok. apply errno_ret_in_fd; [exact Hok|].
  pose proof (alloc_fd_le fds). lia.
Qed.

(* =========================================================================
   Per-syscall checkers
   ========================================================================= *)

(** The shape every call that hands back a FRESH DESCRIPTOR admits:
    either an error-encoded return drawn from [es], or the lowest free fd
    ([State.alloc_fd]) with the model [mk] builds from it.  [openat],
    [socket] and [accept4] differ only in [es] and in [mk]. *)

Definition check_new_fd_result (es : list Z) (eff : SyscallEffect) (m : Model)
    (mk : word -> Model) : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in es ret then CheckOk m []
      else
        match fd_lookup (m_fds m) ret with
        | Some _ => CheckReject
        | None => if bv_eqb ret (alloc_fd (m_fds m)) then CheckOk (mk ret) []
                  else CheckReject
        end
  | _ => CheckReject
  end.

(** A fresh-descriptor result never declines: every shape it can see is
    either an injected errno, the allocated fd, or a rejection. *)

Lemma check_new_fd_result_no_unmodeled : forall es eff m mk,
  check_new_fd_result es eff m mk <> CheckUnmodeled.
Proof.
  intros es [ret ws zs us cs copyins] m mk. unfold check_new_fd_result.
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
  destruct (errno_ret_in es ret); [discriminate|].
  destruct (fd_lookup (m_fds m) ret); [discriminate|].
  destruct (bv_eqb ret (alloc_fd (m_fds m))); discriminate.
Qed.

Local Lemma check_new_fd_result_no_copyin : forall es eff m mk m' evs,
  check_new_fd_result es eff m mk = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros es [ret ws zs us cs cis] m mk m' evs H.
  unfold check_new_fd_result in H.
  destruct ws; destruct zs; destruct us; destruct cs; destruct cis;
    try discriminate; reflexivity.
Qed.

(** openat's instance: the effect must be (ret = [r], no writes, no
    zeros); step to [m'] emitting [evs]. *)

Definition check_open_result : SyscallEffect -> Model -> (word -> Model)
    -> check_result :=
  check_new_fd_result openat_errnos.

Local Lemma check_open_result_no_unmodeled : forall eff m mk,
  check_open_result eff m mk <> CheckUnmodeled.
Proof. intros eff m mk. apply check_new_fd_result_no_unmodeled. Qed.

(** The same acceptor written with the spec's OWN [mk], which is a
    [word -> Model -> Model] rather than the [word -> Model] the
    checker's shape wants.  Carrying the application inside is what
    keeps goal and lemma syntactically alike, so [apply] never has to
    solve [?mk fd m] — not a pattern in [m] — by higher-order
    unification. *)
Local Definition check_open_result_mk (eff : SyscallEffect) (m : Model)
    (mk : word -> Model -> Model) : check_result :=
  check_open_result eff m (fun fd => mk fd m).

Local Lemma check_open_result_mk_no_unmodeled : forall eff m mk,
  check_open_result_mk eff m mk <> CheckUnmodeled.
Proof. intros. apply check_new_fd_result_no_unmodeled. Qed.

(** The acceptor for [Open.create_wronly]: shared by the clobbering
    (O_TRUNC) and the exclusive (O_EXCL) write-create shapes, mirroring
    the one spec definition they share. *)

Definition check_create_wronly (fs' : Fs.Fs) (ino : Fs.ino) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdFileW ino (Z_to_bv 64 0)))
                 (with_fs fs' m)).

(** The acceptor for [Open.open_append].  One difference from the one
    above and no other: the fd kind is [State.FdFileA]. *)

Definition check_open_append (fs' : Fs.Fs) (ino : Fs.ino) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdFileA ino (Z_to_bv 64 0)))
                 (with_fs fs' m)).

(** The acceptor for [Open.open_rdwr].  The fd kind is
    [State.FdFileRW]. *)

Definition check_open_rdwr (fs' : Fs.Fs) (ino : Fs.ino) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdFileRW ino (Z_to_bv 64 0)))
                 (with_fs fs' m)).

Local Lemma check_open_result_sound_ok : forall i eff m mk m' evs,
  check_open_result eff m (fun fd => mk fd m) = CheckOk m' evs ->
  open_result_spec m mk i m (Ok eff m' evs).
Proof.
  intros i [ret ws zs us cs copyins] m mk m' evs H.
  unfold check_open_result, check_new_fd_result in H.
  destruct ws as [|w ws']; [destruct zs as [|z zs']|];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (errno_ret_in openat_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    unfold open_result_spec. apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    apply pure_ok.
  - destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
    destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq.
    unfold open_result_spec. apply alt_r. eapply bind_ok0.
    { apply (choose_ok _ ret). split; assumption. }
    cbv beta. eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Local Lemma check_create_wronly_sound_ok : forall i fs' ino eff m m' evs,
  check_create_wronly fs' ino eff m = CheckOk m' evs ->
  create_wronly fs' ino m i m (Ok eff m' evs).
Proof.
  intros i fs' ino [ret ws zs us cs copyins] m m' evs H.
  unfold check_create_wronly, check_open_result, check_new_fd_result in H.
  destruct ws as [|w ws']; [destruct zs as [|z zs']|];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (errno_ret_in openat_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    unfold create_wronly. apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    apply pure_ok.
  - destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
    destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq.
    unfold create_wronly. apply alt_r. eapply bind_ok0.
    { apply (choose_ok _ ret). split; assumption. }
    cbv beta. eapply bind_ok0; [apply modify_ok|].
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Local Lemma check_open_append_sound_ok : forall i fs' ino eff m m' evs,
  check_open_append fs' ino eff m = CheckOk m' evs ->
  open_append fs' ino m i m (Ok eff m' evs).
Proof.
  intros i fs' ino [ret ws zs us cs copyins] m m' evs H.
  unfold check_open_append, check_open_result, check_new_fd_result in H.
  destruct ws as [|w ws']; [destruct zs as [|z zs']|];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (errno_ret_in openat_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    unfold open_append. apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    apply pure_ok.
  - destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
    destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq.
    unfold open_append. apply alt_r. eapply bind_ok0.
    { apply (choose_ok _ ret). split; assumption. }
    cbv beta. eapply bind_ok0; [apply modify_ok|].
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Local Lemma check_open_rdwr_sound_ok : forall i fs' ino eff m m' evs,
  check_open_rdwr fs' ino eff m = CheckOk m' evs ->
  open_rdwr fs' ino m i m (Ok eff m' evs).
Proof.
  intros i fs' ino [ret ws zs us cs copyins] m m' evs H.
  unfold check_open_rdwr, check_open_result, check_new_fd_result in H.
  destruct ws as [|w ws']; [destruct zs as [|z zs']|];
    destruct us as [|? ?]; destruct cs as [|? ?];
    destruct copyins as [|? ?]; try discriminate.
  destruct (errno_ret_in openat_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    unfold open_rdwr. apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    apply pure_ok.
  - destruct (fd_lookup (m_fds m) ret) eqn:Hfr; [discriminate|].
    destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq.
    unfold open_rdwr. apply alt_r. eapply bind_ok0.
    { apply (choose_ok _ ret). split; assumption. }
    cbv beta. eapply bind_ok0; [apply modify_ok|].
    eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

(** Mirrors [Open.open_devnull] and [Open.open_urandom]: the decline of
    a device entry at a key other than the device's own name
    ([Open.dev_at_home]), then the shared success shape with the granted
    access mode on the entry. *)
Local Definition check_open_devnull (k : Fs.path) (rd wr : bool)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (dev_at_home k DevNull) then CheckUnmodeled
  else
    check_open_result_mk eff m
      (fun fd => with_fds (fd_insert (m_fds m) fd (FdDevNull rd wr))).

Local Definition check_open_urandom (k : Fs.path) (rd wr : bool)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (dev_at_home k DevUrandom) then CheckUnmodeled
  else
    check_open_result_mk eff m
      (fun fd => with_fds (fd_insert (m_fds m) fd (FdUrandom rd wr))).

(** THE ARMS, each a match on [Fs.resolve]'s outcome and mirroring the
    spec of the same name row for row.  Each declines "proc" and "sys"
    at the root ([Fs.ROutside]), the read and directory arms also the
    [O_CREAT] walk's end they never get ([Fs.RParent]), and the device
    rows a device entry away from its own name. *)
Local Definition check_openat_read (r : Fs.Resolved)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match r with
  | Fs.RFound k e =>
      match e with
      | EDir =>
          check_open_result_mk eff m
            (fun fd => with_fds (fd_insert (m_fds m) fd (FdDir k)))
      | EFile ino =>
          check_open_result_mk eff m
            (fun fd => with_fds (fd_insert (m_fds m) fd
                                   (FdFile ino (Z_to_bv 64 0))))
      | EDev DevNull => check_open_devnull k true false eff m
      | EDev DevUrandom => check_open_urandom k true false eff m
      | ELink _ => check_ret_only eff (errno_ret ELOOP) m []
      end
  | Fs.RMissing _ _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
  | Fs.ROutside => CheckUnmodeled
  | Fs.RParent _ _ => CheckUnmodeled
  end.

Local Definition check_openat_create (r : Fs.Resolved)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match r with
  | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
  | Fs.ROutside => CheckUnmodeled
  | Fs.RParent _ _ => check_ret_only eff (errno_ret EISDIR) m []
  | Fs.RMissing par nm =>
      check_create_wronly (create_file_fs (m_fs m) (Fs.child_key par nm))
        (create_file_ino (m_fs m)) eff m
  | Fs.RFound k e =>
      match e with
      | EDir => check_ret_only eff (errno_ret EISDIR) m []
      | EFile ino => check_create_wronly (Fs.fs_set_ino_data (m_fs m) ino []) ino eff m
      | EDev DevNull => check_open_devnull k false true eff m
      | EDev DevUrandom => check_open_urandom k false true eff m
      | ELink _ => check_ret_only eff (errno_ret ELOOP) m []
      end
  end.

Local Definition check_openat_excl (r : Fs.Resolved)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match r with
  | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
  | Fs.ROutside => CheckUnmodeled
  | Fs.RParent _ _ => check_ret_only eff (errno_ret EISDIR) m []
  | Fs.RMissing par nm =>
      check_create_wronly (create_file_fs (m_fs m) (Fs.child_key par nm))
        (create_file_ino (m_fs m)) eff m
  | Fs.RFound _ _ => check_ret_only eff (errno_ret EEXIST) m []
  end.

Local Definition check_openat_append (excl : bool) (r : Fs.Resolved)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match r with
  | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
  | Fs.ROutside => CheckUnmodeled
  | Fs.RParent _ _ => check_ret_only eff (errno_ret EISDIR) m []
  | Fs.RMissing par nm =>
      check_open_append (create_file_fs (m_fs m) (Fs.child_key par nm))
        (create_file_ino (m_fs m)) eff m
  | Fs.RFound k e =>
      if excl then check_ret_only eff (errno_ret EEXIST) m []
      else
        match e with
        | EDir => check_ret_only eff (errno_ret EISDIR) m []
        | EFile ino => check_open_append (m_fs m) ino eff m
        | EDev DevNull => check_open_devnull k false true eff m
        | EDev DevUrandom => check_open_urandom k false true eff m
        | ELink _ => check_ret_only eff (errno_ret ELOOP) m []
        end
  end.

Local Definition check_openat_rdwr (creat trunc : bool) (r : Fs.Resolved)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match r with
  | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
  | Fs.ROutside => CheckUnmodeled
  | Fs.RParent _ _ =>
      if creat then check_ret_only eff (errno_ret EISDIR) m [] else CheckUnmodeled
  | Fs.RMissing par nm =>
      if creat then
        check_open_rdwr (create_file_fs (m_fs m) (Fs.child_key par nm))
          (create_file_ino (m_fs m)) eff m
      else check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RFound k e =>
      match e with
      | EDir => check_ret_only eff (errno_ret EISDIR) m []
      | EFile ino =>
          check_open_rdwr (if trunc then Fs.fs_set_ino_data (m_fs m) ino []
                           else m_fs m) ino eff m
      | EDev DevNull => check_open_devnull k true true eff m
      | EDev DevUrandom => check_open_urandom k true true eff m
      | ELink _ => check_ret_only eff (errno_ret ELOOP) m []
      end
  end.

Local Definition check_openat_rdwr_excl (r : Fs.Resolved)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match r with
  | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
  | Fs.ROutside => CheckUnmodeled
  | Fs.RParent _ _ => check_ret_only eff (errno_ret EISDIR) m []
  | Fs.RMissing par nm =>
      check_open_rdwr (create_file_fs (m_fs m) (Fs.child_key par nm))
        (create_file_ino (m_fs m)) eff m
  | Fs.RFound _ _ => check_ret_only eff (errno_ret EEXIST) m []
  end.

Local Definition check_openat_dir (r : Fs.Resolved) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match r with
  | Fs.RFound k EDir =>
      check_open_result_mk eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd (FdDir k)))
  | Fs.RFound _ (EFile _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RFound _ (EDev _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RFound _ (ELink _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RMissing _ _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
  | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
  | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
  | Fs.ROutside => CheckUnmodeled
  | Fs.RParent _ _ => CheckUnmodeled
  end.

(** Mirrors [Open.openat_procfd_spec], branch for branch: the three
    words, then -ENOENT for a descriptor number nothing holds, then, on
    a regular file's descriptor, the reopen of its inode in one of three
    shapes, and the decline of every other kind at N.  Each reopen is
    [check_open_result]'s shape, whose errno alternatives are
    [openat_errnos]'. *)
Local Definition check_openat_procfd (n flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
  if negb (Z.eqb fl 0 || Z.eqb fl wr_create_flags
           || Z.eqb fl append_create_flags)%bool then CheckUnmodeled
  else
  match fd_lookup (m_fds m) n with
  | None => check_ret_only eff (errno_ret ENOENT) m []
  | Some (FdFile ino _) | Some (FdFileW ino _) | Some (FdFileA ino _)
  | Some (FdFileRW ino _) =>
      if Z.eqb fl 0 then
        check_open_result_mk eff m (fun fd => with_fds (fd_insert (m_fds m) fd
                                                  (FdFile ino (Z_to_bv 64 0))))
      else if Z.eqb fl wr_create_flags then
        check_create_wronly (Fs.fs_set_ino_data (m_fs m) ino []) ino eff m
      else check_open_append (m_fs m) ino eff m
  | Some (FdChannel _) | Some (FdDir _)
  | Some (FdSocket _) | Some (FdPipe _ _) | Some (FdDevNull _ _)
  | Some (FdUrandom _ _) | Some (FdStream _ _ _) | Some (FdEventfd _)
  | Some (FdDgram _) => CheckUnmodeled
  end.

(** Mirrors [Open.openat_resolved_spec]: "/proc/self/fd/N" ahead of the
    walk, then one resolution with the flag word's walk end
    ([Open.open_walk_mode]) and the ladder over the word's shape
    ([Open.open_shape]). *)
Local Definition check_openat_resolved (p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match proc_self_fd p with
  | Some n => check_openat_procfd n flags eff m
  | None =>
  match Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p with
  | (r, _, _) =>
      let fl := open_shape flags in
      if Z.eqb fl 0 then check_openat_read r eff m
      else if Z.eqb fl wr_create_flags then check_openat_create r eff m
      else if is_excl_create fl then check_openat_excl r eff m
      else if Z.eqb fl O_DIRECTORY then check_openat_dir r eff m
      else if Z.eqb fl append_create_flags then check_openat_append false r eff m
      else if rdwr_open_word fl then
        check_openat_rdwr (flag_set fl O_CREAT) (flag_set fl O_TRUNC) r eff m
      else if is_rdwr_excl_create fl then check_openat_rdwr_excl r eff m
      else if is_excl_append_create fl then check_openat_append true r eff m
      else CheckUnmodeled
  end
  end.

Local Definition check_openat_body (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match read_cstr (in_mem i) pathp with
    | CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
    | CstrFault => check_ret_only eff (errno_ret EFAULT) m []
    | CstrOk p =>
        if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
        else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
        else check_openat_resolved p flags eff m
  end.


(** The pathname copy-in is the prefix through the first NUL, the first
    faulting byte, or [PATH_MAX] — [State.cstr_access_len_aux].  That is
    the range the model records, not the one [getname()] loads:
    [strncpy_from_user] reads a word at a time and so runs to the end of
    the word holding the NUL, up to 7 bytes further, without moving the
    errno or the return (lib/strncpy_from_user.c, [do_strncpy_from_user];
    byte-identical v6.10 through v6.16 — the FILE is not, so the window
    belongs to the function).  Where the two agree, and the alignment argument
    that bounds the difference, are in
    bugs/openat-getname-word-at-a-time.md.  The open body performs no
    later copy-in, so clear the prefix while checking the result and
    require the complete claimed list to equal that one range.  Around
    that, [getname_flags]' own refusals ([check_getname_refusals]),
    which fail before the copy is done. *)
Definition check_openat (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_getname_refusals i pathp eff m
    (if negb (modeled_open_flags flags) then CheckUnmodeled
     else
       let reads := [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] in
       check_copyins_after reads eff
         (check_walk_refusals (open_walk_mode flags) i pathp (clear_copyins eff) m
            (check_openat_body i dirfd pathp flags (clear_copyins eff) m))).

Local Definition openat_nul_mem (a : word) : option byte :=
  if bv_eqb a 0x2000 then Some 102
  else if bv_eqb a 0x2001 then Some 0
  else None.

Example openat_copyin_includes_the_nul :
  cstr_access_len_aux openat_nul_mem 0x2000 path_max = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Definition check_close (fd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some _ => check_ret_only eff (Z_to_bv 64 0)
                (with_fds (fd_remove (m_fds m) fd) m) []
  end.

Local Lemma check_ret_only_sound_ok : forall i eff r m m' evs,
  check_ret_only eff r m [] = CheckOk m' evs ->
  ret_only r i m (Ok eff m' evs).
Proof.
  intros i eff r m m' evs H.
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  apply pure_ok.
Qed.

(** Eliminate only the branch index.  The caller captures its aligned spec
    and checker expressions once in [P], so elaboration never duplicates the
    large openat branch trees in an eliminator's arguments and conclusion. *)
Local Lemma refine_if (b : bool) (P : bool -> Prop) :
  P true -> P false -> P b.
Proof.
  intros Htrue Hfalse.
  refine (match b as b' return P b' with
          | true => Htrue | false => Hfalse end).
Qed.

Local Lemma refine_option {X : Type} (o : option X) (P : option X -> Prop) :
  (forall x, P (Some x)) -> P None -> P o.
Proof.
  intros Hsome Hnone.
  refine (match o as o' return P o' with
          | Some x => Hsome x | None => Hnone end).
Qed.

Local Lemma refine_cstr (r : cstr_result) (P : cstr_result -> Prop) :
  (forall p, P (CstrOk p)) -> P CstrTooLong -> P CstrFault -> P r.
Proof.
  intros Hok Htoo_long Hfault.
  refine (match r as r' return P r' with
          | CstrOk p => Hok p
          | CstrTooLong => Htoo_long
          | CstrFault => Hfault
          end).
Qed.

Local Lemma check_open_result_complete_ok : forall i eff m mk m' evs,
  open_result_spec m mk i m (Ok eff m' evs) ->
  check_open_result eff m (fun fd => mk fd m) = CheckOk m' evs /\
  eff_copyins eff = [].
Proof.
  intros i eff m mk m' evs H.
  unfold open_result_spec in H. unfold check_open_result, check_new_fd_result.
  sys_unfold. cbv iota in H. inv_ok.
  - split.
    + match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    + reflexivity.
  - split.
    + rewrite errno_ret_in_alloc_fd by reflexivity.
      match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
      rewrite bv_eqb_refl. reflexivity.
    + reflexivity.
Qed.

Local Lemma check_create_wronly_complete_ok : forall i fs' ino eff m m' evs,
  create_wronly fs' ino m i m (Ok eff m' evs) ->
  check_create_wronly fs' ino eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i fs' ino eff m m' evs H.
  unfold create_wronly in H.
  unfold check_create_wronly, check_open_result, check_new_fd_result.
  sys_unfold. cbv iota in H. inv_ok.
  - split.
    + match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    + reflexivity.
  - split.
    + rewrite errno_ret_in_alloc_fd by reflexivity.
      match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
      rewrite bv_eqb_refl. reflexivity.
    + reflexivity.
Qed.

Local Lemma check_open_append_complete_ok : forall i fs' ino eff m m' evs,
  open_append fs' ino m i m (Ok eff m' evs) ->
  check_open_append fs' ino eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i fs' ino eff m m' evs H.
  unfold open_append in H.
  unfold check_open_append, check_open_result, check_new_fd_result.
  sys_unfold. cbv iota in H. inv_ok.
  - split.
    + match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    + reflexivity.
  - split.
    + rewrite errno_ret_in_alloc_fd by reflexivity.
      match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
      rewrite bv_eqb_refl. reflexivity.
    + reflexivity.
Qed.

Local Lemma check_open_rdwr_complete_ok : forall i fs' ino eff m m' evs,
  open_rdwr fs' ino m i m (Ok eff m' evs) ->
  check_open_rdwr fs' ino eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i fs' ino eff m m' evs H.
  unfold open_rdwr in H.
  unfold check_open_rdwr, check_open_result, check_new_fd_result.
  sys_unfold. cbv iota in H. inv_ok.
  - split.
    + match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    + reflexivity.
  - split.
    + rewrite errno_ret_in_alloc_fd by reflexivity.
      match goal with H : fd_lookup _ _ = None |- _ => rewrite H end.
      rewrite bv_eqb_refl. reflexivity.
    + reflexivity.
Qed.

Local Lemma open_result_spec_no_unmodeled : forall m mk i,
  ~ open_result_spec m mk i m Unmodeled.
Proof.
  intros m mk i H. unfold open_result_spec in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

Local Lemma create_wronly_no_unmodeled : forall fs' ino m i,
  ~ create_wronly fs' ino m i m Unmodeled.
Proof.
  intros fs' ino m i H. unfold create_wronly in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

Local Lemma open_append_no_unmodeled : forall fs' ino m i,
  ~ open_append fs' ino m i m Unmodeled.
Proof.
  intros fs' ino m i H. unfold open_append in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

Local Lemma open_rdwr_no_unmodeled : forall fs' ino m i,
  ~ open_rdwr fs' ino m i m Unmodeled.
Proof.
  intros fs' ino m i H. unfold open_rdwr in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

Local Lemma check_open_rdwr_no_unmodeled : forall fs' ino eff m,
  check_open_rdwr fs' ino eff m <> CheckUnmodeled.
Proof.
  intros fs' ino eff m H. unfold check_open_rdwr in H.
  now apply check_open_result_no_unmodeled in H.
Qed.


(** The projections the arm proofs use: the check result alone, with the
    copy-in fact taken separately where it is wanted. *)
Local Lemma check_open_result_mk_complete_ok : forall i eff m mk m' evs,
  open_result_spec m mk i m (Ok eff m' evs) ->
  check_open_result_mk eff m mk = CheckOk m' evs.
Proof.
  intros. unfold check_open_result_mk.
  now apply check_open_result_complete_ok in H as (? & ?).
Qed.

Local Lemma check_open_result_mk_sound_ok : forall i eff m mk m' evs,
  check_open_result_mk eff m mk = CheckOk m' evs ->
  open_result_spec m mk i m (Ok eff m' evs).
Proof.
  intros. unfold check_open_result_mk in H.
  now apply check_open_result_sound_ok.
Qed.

Local Lemma check_open_result_mk_no_copyin : forall eff m mk m' evs,
  check_open_result_mk eff m mk = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros. unfold check_open_result_mk, check_open_result in H.
  eapply check_new_fd_result_no_copyin. exact H.
Qed.

Local Lemma check_create_wronly_complete_ok' : forall i fs' ino eff m m' evs,
  create_wronly fs' ino m i m (Ok eff m' evs) ->
  check_create_wronly fs' ino eff m = CheckOk m' evs.
Proof. intros. now apply check_create_wronly_complete_ok in H as (? & ?). Qed.

Local Lemma check_open_append_complete_ok' : forall i fs' ino eff m m' evs,
  open_append fs' ino m i m (Ok eff m' evs) ->
  check_open_append fs' ino eff m = CheckOk m' evs.
Proof. intros. now apply check_open_append_complete_ok in H as (? & ?). Qed.

Local Lemma check_open_rdwr_complete_ok' : forall i fs' ino eff m m' evs,
  open_rdwr fs' ino m i m (Ok eff m' evs) ->
  check_open_rdwr fs' ino eff m = CheckOk m' evs.
Proof. intros. now apply check_open_rdwr_complete_ok in H as (? & ?). Qed.

Local Lemma check_create_wronly_no_unmodeled : forall fs' ino eff m,
  check_create_wronly fs' ino eff m <> CheckUnmodeled.
Proof. intros. apply check_new_fd_result_no_unmodeled. Qed.

Local Lemma check_open_append_no_unmodeled : forall fs' ino eff m,
  check_open_append fs' ino eff m <> CheckUnmodeled.
Proof. intros. apply check_new_fd_result_no_unmodeled. Qed.

Local Lemma ret_only_no_unmodeled : forall r i m,
  ~ ret_only r i m Unmodeled.
Proof. intros r i m H. unfold ret_only, pure in H. discriminate H. Qed.

(** Closing a leaf that is a bare errno return: the four moves each
    direction needs, found by shape rather than by hypothesis name. *)
Local Ltac op_ret_ok :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckOk _ _ |- _ =>
      apply check_ret_only_ok_iff in Hx; destruct Hx as (-> & -> & ->);
      unfold err_ret, ret_only; apply pure_ok
  end.
Local Ltac op_ret_nu :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckUnmodeled |- _ =>
      now apply check_ret_only_no_unmodeled in Hx
  end.
Local Ltac op_ret_co :=
  unfold err_ret, ret_only, pure in *; inv_ok;
  apply check_ret_only_ok_iff; now repeat split.
Local Ltac op_ret_cnil :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckOk _ _ |- _ =>
      apply check_ret_only_ok_iff in Hx; destruct Hx as (-> & _ & _);
      reflexivity
  end.

(** The device rows are [open_result_spec] under a different name,
    behind the device-at-home test, so one lemma per direction covers
    both. *)
Local Lemma check_open_devnull_sound_ok : forall i k rd wr eff m m' evs,
  check_open_devnull k rd wr eff m = CheckOk m' evs ->
  open_devnull k m rd wr i m (Ok eff m' evs).
Proof.
  intros i k rd wr eff m m' evs H. unfold check_open_devnull in H.
  unfold open_devnull. destruct (negb (dev_at_home k DevNull)); [discriminate|].
  eapply check_open_result_mk_sound_ok; exact H.
Qed.

Local Lemma check_open_urandom_sound_ok : forall i k rd wr eff m m' evs,
  check_open_urandom k rd wr eff m = CheckOk m' evs ->
  open_urandom k m rd wr i m (Ok eff m' evs).
Proof.
  intros i k rd wr eff m m' evs H. unfold check_open_urandom in H.
  unfold open_urandom. destruct (negb (dev_at_home k DevUrandom)); [discriminate|].
  eapply check_open_result_mk_sound_ok; exact H.
Qed.

Local Lemma check_open_devnull_sound_unmodeled : forall i k rd wr eff m,
  check_open_devnull k rd wr eff m = CheckUnmodeled ->
  open_devnull k m rd wr i m Unmodeled.
Proof.
  intros i k rd wr eff m H. unfold check_open_devnull in H.
  unfold open_devnull. destruct (negb (dev_at_home k DevNull));
    [apply unmodeled_intro|].
  exfalso. eapply check_open_result_mk_no_unmodeled; exact H.
Qed.

Local Lemma check_open_urandom_sound_unmodeled : forall i k rd wr eff m,
  check_open_urandom k rd wr eff m = CheckUnmodeled ->
  open_urandom k m rd wr i m Unmodeled.
Proof.
  intros i k rd wr eff m H. unfold check_open_urandom in H.
  unfold open_urandom. destruct (negb (dev_at_home k DevUrandom));
    [apply unmodeled_intro|].
  exfalso. eapply check_open_result_mk_no_unmodeled; exact H.
Qed.

Local Lemma check_open_devnull_complete_ok : forall i k rd wr eff m m' evs,
  open_devnull k m rd wr i m (Ok eff m' evs) ->
  check_open_devnull k rd wr eff m = CheckOk m' evs.
Proof.
  intros i k rd wr eff m m' evs H. unfold open_devnull in H.
  unfold check_open_devnull. destruct (negb (dev_at_home k DevNull));
    [unfold unmodeled in H; inv_ok|].
  eapply check_open_result_mk_complete_ok; exact H.
Qed.

Local Lemma check_open_urandom_complete_ok : forall i k rd wr eff m m' evs,
  open_urandom k m rd wr i m (Ok eff m' evs) ->
  check_open_urandom k rd wr eff m = CheckOk m' evs.
Proof.
  intros i k rd wr eff m m' evs H. unfold open_urandom in H.
  unfold check_open_urandom. destruct (negb (dev_at_home k DevUrandom));
    [unfold unmodeled in H; inv_ok|].
  eapply check_open_result_mk_complete_ok; exact H.
Qed.

Local Lemma check_open_devnull_complete_unmodeled : forall i k rd wr eff m,
  open_devnull k m rd wr i m Unmodeled ->
  check_open_devnull k rd wr eff m = CheckUnmodeled.
Proof.
  intros i k rd wr eff m H. unfold open_devnull in H.
  unfold check_open_devnull. destruct (negb (dev_at_home k DevNull));
    [reflexivity|].
  exfalso. eapply open_result_spec_no_unmodeled; exact H.
Qed.

Local Lemma check_open_urandom_complete_unmodeled : forall i k rd wr eff m,
  open_urandom k m rd wr i m Unmodeled ->
  check_open_urandom k rd wr eff m = CheckUnmodeled.
Proof.
  intros i k rd wr eff m H. unfold open_urandom in H.
  unfold check_open_urandom. destruct (negb (dev_at_home k DevUrandom));
    [reflexivity|].
  exfalso. eapply open_result_spec_no_unmodeled; exact H.
Qed.

Local Lemma check_open_devnull_no_copyin : forall k rd wr eff m m' evs,
  check_open_devnull k rd wr eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros k rd wr eff m m' evs H. unfold check_open_devnull in H.
  destruct (negb (dev_at_home k DevNull)); [discriminate|].
  eapply check_open_result_mk_no_copyin; exact H.
Qed.

Local Lemma check_open_urandom_no_copyin : forall k rd wr eff m m' evs,
  check_open_urandom k rd wr eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros k rd wr eff m m' evs H. unfold check_open_urandom in H.
  destruct (negb (dev_at_home k DevUrandom)); [discriminate|].
  eapply check_open_result_mk_no_copyin; exact H.
Qed.

(** The device cell of an arm, in each direction: the kind switch, then
    the lemma for the device it names. *)
Local Ltac dev_sound_ok :=
  first [eapply check_open_devnull_sound_ok; eassumption
        |eapply check_open_urandom_sound_ok; eassumption].
Local Ltac dev_sound_nu :=
  first [eapply check_open_devnull_sound_unmodeled; eassumption
        |eapply check_open_urandom_sound_unmodeled; eassumption].
Local Ltac dev_complete_ok :=
  first [eapply check_open_devnull_complete_ok; eassumption
        |eapply check_open_urandom_complete_ok; eassumption].
Local Ltac dev_complete_nu :=
  first [eapply check_open_devnull_complete_unmodeled; eassumption
        |eapply check_open_urandom_complete_unmodeled; eassumption].
Local Ltac dev_cnil :=
  first [eapply check_open_devnull_no_copyin; eassumption
        |eapply check_open_urandom_no_copyin; eassumption].

(* ------------------------------------------------------------ the arms *)

(** Every arm splits on the outcome, the entry and the device kind, and
    each leaf closes by the lemma for its acceptor, one per direction. *)
Local Ltac arm_sound_ok :=
  first [ op_ret_ok
        | eapply check_open_result_mk_sound_ok; eassumption
        | eapply check_create_wronly_sound_ok; eassumption
        | eapply check_open_append_sound_ok; eassumption
        | eapply check_open_rdwr_sound_ok; eassumption
        | dev_sound_ok
        | discriminate ].
Local Ltac arm_sound_nu :=
  first [ op_ret_nu
        | apply unmodeled_intro
        | exfalso; eapply check_open_result_mk_no_unmodeled; eassumption
        | exfalso; eapply check_create_wronly_no_unmodeled; eassumption
        | exfalso; eapply check_open_append_no_unmodeled; eassumption
        | exfalso; eapply check_open_rdwr_no_unmodeled; eassumption
        | dev_sound_nu ].
Local Ltac arm_complete_ok :=
  first [ op_ret_co
        | eapply check_open_result_mk_complete_ok; eassumption
        | eapply check_create_wronly_complete_ok'; eassumption
        | eapply check_open_append_complete_ok'; eassumption
        | eapply check_open_rdwr_complete_ok'; eassumption
        | dev_complete_ok
        | unfold unmodeled in *; inv_ok ].
Local Ltac arm_complete_nu :=
  first [ reflexivity
        | sys_unfold; inv_ok; fail
        | exfalso; eapply open_result_spec_no_unmodeled; eassumption
        | exfalso; eapply create_wronly_no_unmodeled; eassumption
        | exfalso; eapply open_append_no_unmodeled; eassumption
        | exfalso; eapply open_rdwr_no_unmodeled; eassumption
        | dev_complete_nu ].

Local Lemma check_openat_read_sound_ok : forall i r eff m m' evs,
  check_openat_read r eff m = CheckOk m' evs ->
  openat_read_spec r m i m (Ok eff m' evs).
Proof.
  intros i r eff m m' evs H. unfold check_openat_read, openat_read_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_ok.
Qed.

Local Lemma check_openat_read_sound_unmodeled : forall i r eff m,
  check_openat_read r eff m = CheckUnmodeled ->
  openat_read_spec r m i m Unmodeled.
Proof.
  intros i r eff m H. unfold check_openat_read, openat_read_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_nu.
Qed.

Local Lemma check_openat_read_complete_ok : forall i r eff m m' evs,
  openat_read_spec r m i m (Ok eff m' evs) ->
  check_openat_read r eff m = CheckOk m' evs.
Proof.
  intros i r eff m m' evs H. unfold check_openat_read, openat_read_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_ok.
Qed.

Local Lemma check_openat_read_complete_unmodeled : forall i r m eff,
  openat_read_spec r m i m Unmodeled ->
  check_openat_read r eff m = CheckUnmodeled.
Proof.
  intros i r m eff H. unfold check_openat_read, openat_read_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_nu.
Qed.

Local Lemma check_openat_create_sound_ok : forall i r eff m m' evs,
  check_openat_create r eff m = CheckOk m' evs ->
  openat_create_spec r m i m (Ok eff m' evs).
Proof.
  intros i r eff m m' evs H. unfold check_openat_create, openat_create_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_ok.
Qed.

Local Lemma check_openat_create_sound_unmodeled : forall i r eff m,
  check_openat_create r eff m = CheckUnmodeled ->
  openat_create_spec r m i m Unmodeled.
Proof.
  intros i r eff m H. unfold check_openat_create, openat_create_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_nu.
Qed.

Local Lemma check_openat_create_complete_ok : forall i r eff m m' evs,
  openat_create_spec r m i m (Ok eff m' evs) ->
  check_openat_create r eff m = CheckOk m' evs.
Proof.
  intros i r eff m m' evs H. unfold check_openat_create, openat_create_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_ok.
Qed.

Local Lemma check_openat_create_complete_unmodeled : forall i r m eff,
  openat_create_spec r m i m Unmodeled ->
  check_openat_create r eff m = CheckUnmodeled.
Proof.
  intros i r m eff H. unfold check_openat_create, openat_create_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_nu.
Qed.

Local Lemma check_openat_excl_sound_ok : forall i r eff m m' evs,
  check_openat_excl r eff m = CheckOk m' evs ->
  openat_excl_spec r m i m (Ok eff m' evs).
Proof.
  intros i r eff m m' evs H. unfold check_openat_excl, openat_excl_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_ok.
Qed.

Local Lemma check_openat_excl_sound_unmodeled : forall i r eff m,
  check_openat_excl r eff m = CheckUnmodeled ->
  openat_excl_spec r m i m Unmodeled.
Proof.
  intros i r eff m H. unfold check_openat_excl, openat_excl_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_nu.
Qed.

Local Lemma check_openat_excl_complete_ok : forall i r eff m m' evs,
  openat_excl_spec r m i m (Ok eff m' evs) ->
  check_openat_excl r eff m = CheckOk m' evs.
Proof.
  intros i r eff m m' evs H. unfold check_openat_excl, openat_excl_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_ok.
Qed.

Local Lemma check_openat_excl_complete_unmodeled : forall i r m eff,
  openat_excl_spec r m i m Unmodeled ->
  check_openat_excl r eff m = CheckUnmodeled.
Proof.
  intros i r m eff H. unfold check_openat_excl, openat_excl_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_nu.
Qed.

Local Lemma check_openat_append_sound_ok : forall i excl r eff m m' evs,
  check_openat_append excl r eff m = CheckOk m' evs ->
  openat_append_spec excl r m i m (Ok eff m' evs).
Proof.
  intros i excl r eff m m' evs H. unfold check_openat_append, openat_append_spec in *.
  destruct excl; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_ok.
Qed.

Local Lemma check_openat_append_sound_unmodeled : forall i excl r eff m,
  check_openat_append excl r eff m = CheckUnmodeled ->
  openat_append_spec excl r m i m Unmodeled.
Proof.
  intros i excl r eff m H. unfold check_openat_append, openat_append_spec in *.
  destruct excl; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_nu.
Qed.

Local Lemma check_openat_append_complete_ok : forall i excl r eff m m' evs,
  openat_append_spec excl r m i m (Ok eff m' evs) ->
  check_openat_append excl r eff m = CheckOk m' evs.
Proof.
  intros i excl r eff m m' evs H. unfold check_openat_append, openat_append_spec in *.
  destruct excl; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_ok.
Qed.

Local Lemma check_openat_append_complete_unmodeled : forall i excl r m eff,
  openat_append_spec excl r m i m Unmodeled ->
  check_openat_append excl r eff m = CheckUnmodeled.
Proof.
  intros i excl r m eff H. unfold check_openat_append, openat_append_spec in *.
  destruct excl; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_nu.
Qed.

Local Lemma check_openat_rdwr_sound_ok : forall i creat trunc r eff m m' evs,
  check_openat_rdwr creat trunc r eff m = CheckOk m' evs ->
  openat_rdwr_spec creat trunc r m i m (Ok eff m' evs).
Proof.
  intros i creat trunc r eff m m' evs H. unfold check_openat_rdwr, openat_rdwr_spec in *.
  destruct creat; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_ok.
Qed.

Local Lemma check_openat_rdwr_sound_unmodeled : forall i creat trunc r eff m,
  check_openat_rdwr creat trunc r eff m = CheckUnmodeled ->
  openat_rdwr_spec creat trunc r m i m Unmodeled.
Proof.
  intros i creat trunc r eff m H. unfold check_openat_rdwr, openat_rdwr_spec in *.
  destruct creat; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_nu.
Qed.

Local Lemma check_openat_rdwr_complete_ok : forall i creat trunc r eff m m' evs,
  openat_rdwr_spec creat trunc r m i m (Ok eff m' evs) ->
  check_openat_rdwr creat trunc r eff m = CheckOk m' evs.
Proof.
  intros i creat trunc r eff m m' evs H. unfold check_openat_rdwr, openat_rdwr_spec in *.
  destruct creat; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_ok.
Qed.

Local Lemma check_openat_rdwr_complete_unmodeled : forall i creat trunc r m eff,
  openat_rdwr_spec creat trunc r m i m Unmodeled ->
  check_openat_rdwr creat trunc r eff m = CheckUnmodeled.
Proof.
  intros i creat trunc r m eff H. unfold check_openat_rdwr, openat_rdwr_spec in *.
  destruct creat; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_nu.
Qed.

Local Lemma check_openat_rdwr_excl_sound_ok : forall i r eff m m' evs,
  check_openat_rdwr_excl r eff m = CheckOk m' evs ->
  openat_rdwr_excl_spec r m i m (Ok eff m' evs).
Proof.
  intros i r eff m m' evs H. unfold check_openat_rdwr_excl, openat_rdwr_excl_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_ok.
Qed.

Local Lemma check_openat_rdwr_excl_sound_unmodeled : forall i r eff m,
  check_openat_rdwr_excl r eff m = CheckUnmodeled ->
  openat_rdwr_excl_spec r m i m Unmodeled.
Proof.
  intros i r eff m H. unfold check_openat_rdwr_excl, openat_rdwr_excl_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_nu.
Qed.

Local Lemma check_openat_rdwr_excl_complete_ok : forall i r eff m m' evs,
  openat_rdwr_excl_spec r m i m (Ok eff m' evs) ->
  check_openat_rdwr_excl r eff m = CheckOk m' evs.
Proof.
  intros i r eff m m' evs H. unfold check_openat_rdwr_excl, openat_rdwr_excl_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_ok.
Qed.

Local Lemma check_openat_rdwr_excl_complete_unmodeled : forall i r m eff,
  openat_rdwr_excl_spec r m i m Unmodeled ->
  check_openat_rdwr_excl r eff m = CheckUnmodeled.
Proof.
  intros i r m eff H. unfold check_openat_rdwr_excl, openat_rdwr_excl_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_nu.
Qed.

Local Lemma check_openat_dir_sound_ok : forall i r eff m m' evs,
  check_openat_dir r eff m = CheckOk m' evs ->
  openat_dir_spec r m i m (Ok eff m' evs).
Proof.
  intros i r eff m m' evs H. unfold check_openat_dir, openat_dir_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_ok.
Qed.

Local Lemma check_openat_dir_sound_unmodeled : forall i r eff m,
  check_openat_dir r eff m = CheckUnmodeled ->
  openat_dir_spec r m i m Unmodeled.
Proof.
  intros i r eff m H. unfold check_openat_dir, openat_dir_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_sound_nu.
Qed.

Local Lemma check_openat_dir_complete_ok : forall i r eff m m' evs,
  openat_dir_spec r m i m (Ok eff m' evs) ->
  check_openat_dir r eff m = CheckOk m' evs.
Proof.
  intros i r eff m m' evs H. unfold check_openat_dir, openat_dir_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_ok.
Qed.

Local Lemma check_openat_dir_complete_unmodeled : forall i r m eff,
  openat_dir_spec r m i m Unmodeled ->
  check_openat_dir r eff m = CheckUnmodeled.
Proof.
  intros i r m eff H. unfold check_openat_dir, openat_dir_spec in *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (destruct e as [ino| |dk|lb]; cbv iota in H |- *;
         try (destruct dk; cbv iota in H |- *)); arm_complete_nu.
Qed.

(* --------------------------------------------- the dispatcher and wrapper *)

Local Ltac openat_ladder fl Hh tac :=
  destruct (Z.eqb (open_shape fl) 0); cbv iota in Hh |- *; [tac|];
  destruct (Z.eqb (open_shape fl) wr_create_flags); cbv iota in Hh |- *; [tac|];
  destruct (is_excl_create (open_shape fl)); cbv iota in Hh |- *; [tac|];
  destruct (Z.eqb (open_shape fl) O_DIRECTORY); cbv iota in Hh |- *; [tac|];
  destruct (Z.eqb (open_shape fl) append_create_flags); cbv iota in Hh |- *; [tac|];
  destruct (rdwr_open_word (open_shape fl)); cbv iota in Hh |- *; [tac|];
  destruct (is_rdwr_excl_create (open_shape fl)); cbv iota in Hh |- *; [tac|];
  destruct (is_excl_append_create (open_shape fl)); cbv iota in Hh |- *; [tac|].

Local Lemma check_openat_procfd_sound_ok : forall i n flags eff m m' evs,
  check_openat_procfd n flags eff m = CheckOk m' evs ->
  openat_procfd_spec n flags m i m (Ok eff m' evs).
Proof.
  intros i n flags eff m m' evs H.
  unfold check_openat_procfd, openat_procfd_spec in *. cbv zeta in *.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       wr_create_flags
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       append_create_flags)%bool); [discriminate|].
  destruct (fd_lookup (m_fds m) n)
    as [[ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam]|];
    try discriminate; try op_ret_ok.
  all: destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [eapply check_open_result_mk_sound_ok; exact H|];
    destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) wr_create_flags);
    [eapply check_create_wronly_sound_ok; exact H
    |eapply check_open_append_sound_ok; exact H].
Qed.

Local Lemma check_openat_procfd_sound_unmodeled : forall i n flags eff m,
  check_openat_procfd n flags eff m = CheckUnmodeled ->
  openat_procfd_spec n flags m i m Unmodeled.
Proof.
  intros i n flags eff m H.
  unfold check_openat_procfd, openat_procfd_spec in *. cbv zeta in *.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       wr_create_flags
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       append_create_flags)%bool); [apply unmodeled_intro|].
  destruct (fd_lookup (m_fds m) n)
    as [[ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam]|];
    try apply unmodeled_intro.
  all: exfalso;
    first [ now apply check_ret_only_no_unmodeled in H
          | destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
            [eapply check_open_result_mk_no_unmodeled; exact H|];
            destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                        wr_create_flags);
            [eapply check_create_wronly_no_unmodeled; exact H
            |eapply check_open_append_no_unmodeled; exact H] ].
Qed.

Local Lemma check_openat_procfd_complete_ok : forall i n flags eff m m' evs,
  openat_procfd_spec n flags m i m (Ok eff m' evs) ->
  check_openat_procfd n flags eff m = CheckOk m' evs.
Proof.
  intros i n flags eff m m' evs.
  unfold openat_procfd_spec, check_openat_procfd. cbv zeta.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       wr_create_flags
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       append_create_flags)%bool);
    [unfold unmodeled; intro Hu; discriminate Hu|].
  destruct (fd_lookup (m_fds m) n)
    as [[ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam]|];
    try (unfold unmodeled; intro Hu; discriminate Hu).
  all: intro H;
    first [ op_ret_co
          | destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
            [eapply check_open_result_mk_complete_ok; exact H|];
            destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                        wr_create_flags);
            [eapply check_create_wronly_complete_ok'; exact H
            |eapply check_open_append_complete_ok'; exact H] ].
Qed.

Local Lemma check_openat_procfd_complete_unmodeled : forall i n flags eff m,
  openat_procfd_spec n flags m i m Unmodeled ->
  check_openat_procfd n flags eff m = CheckUnmodeled.
Proof.
  intros i n flags eff m.
  unfold openat_procfd_spec, check_openat_procfd. cbv zeta.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       wr_create_flags
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       append_create_flags)%bool); [reflexivity|].
  destruct (fd_lookup (m_fds m) n)
    as [[ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam]|];
    try (intros _; reflexivity).
  all: intro H; exfalso;
    first [ exact (ret_only_no_unmodeled (errno_ret ENOENT) i m H)
          | destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
            [exact (open_result_spec_no_unmodeled _ _ i H)|];
            destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                        wr_create_flags);
            [exact (create_wronly_no_unmodeled _ _ _ _ H)
            |exact (open_append_no_unmodeled _ _ _ _ H)] ].
Qed.

Local Lemma check_openat_resolved_sound_ok : forall i p flags eff m m' evs,
  check_openat_resolved p flags eff m = CheckOk m' evs ->
  openat_resolved_spec p flags m i m (Ok eff m' evs).
Proof.
  intros i p flags eff m m' evs H.
  unfold check_openat_resolved, openat_resolved_spec in *.
  destruct (proc_self_fd p) as [n|];
    [now apply check_openat_procfd_sound_ok|].
  destruct (Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  openat_ladder flags H ltac:(first [now apply check_openat_read_sound_ok
                            |now apply check_openat_create_sound_ok
                            |now apply check_openat_excl_sound_ok
                            |now apply check_openat_dir_sound_ok
                            |now apply check_openat_append_sound_ok
                            |now apply check_openat_rdwr_sound_ok
                            |now apply check_openat_rdwr_excl_sound_ok]).
  discriminate.
Qed.

Local Lemma check_openat_resolved_sound_unmodeled : forall i p flags eff m,
  check_openat_resolved p flags eff m = CheckUnmodeled ->
  openat_resolved_spec p flags m i m Unmodeled.
Proof.
  intros i p flags eff m H.
  unfold check_openat_resolved, openat_resolved_spec in *.
  destruct (proc_self_fd p) as [n|];
    [eapply check_openat_procfd_sound_unmodeled; exact H|].
  destruct (Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  openat_ladder flags H
    ltac:(first [eapply check_openat_read_sound_unmodeled; exact H
                |eapply check_openat_create_sound_unmodeled; exact H
                |eapply check_openat_excl_sound_unmodeled; exact H
                |eapply check_openat_dir_sound_unmodeled; exact H
                |eapply check_openat_append_sound_unmodeled; exact H
                |eapply check_openat_rdwr_sound_unmodeled; exact H
                |eapply check_openat_rdwr_excl_sound_unmodeled; exact H]).
  apply unmodeled_intro.
Qed.

Local Lemma check_openat_resolved_complete_ok : forall i p flags eff m m' evs,
  openat_resolved_spec p flags m i m (Ok eff m' evs) ->
  check_openat_resolved p flags eff m = CheckOk m' evs.
Proof.
  intros i p flags eff m m' evs H.
  unfold check_openat_resolved, openat_resolved_spec in *.
  destruct (proc_self_fd p) as [n|];
    [eapply check_openat_procfd_complete_ok; exact H|].
  destruct (Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  openat_ladder flags H
    ltac:(first [eapply check_openat_read_complete_ok; exact H
                |eapply check_openat_create_complete_ok; exact H
                |eapply check_openat_excl_complete_ok; exact H
                |eapply check_openat_dir_complete_ok; exact H
                |eapply check_openat_append_complete_ok; exact H
                |eapply check_openat_rdwr_complete_ok; exact H
                |eapply check_openat_rdwr_excl_complete_ok; exact H]).
  unfold unmodeled in H. inv_ok.
Qed.

Local Lemma check_openat_resolved_complete_unmodeled : forall i p flags m eff,
  openat_resolved_spec p flags m i m Unmodeled ->
  check_openat_resolved p flags eff m = CheckUnmodeled.
Proof.
  intros i p flags m eff H.
  unfold check_openat_resolved, openat_resolved_spec in *.
  destruct (proc_self_fd p) as [n|];
    [eapply check_openat_procfd_complete_unmodeled; exact H|].
  destruct (Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H |- *.
  openat_ladder flags H
    ltac:(first [eapply check_openat_read_complete_unmodeled; exact H
                |eapply check_openat_create_complete_unmodeled; exact H
                |eapply check_openat_excl_complete_unmodeled; exact H
                |eapply check_openat_dir_complete_unmodeled; exact H
                |eapply check_openat_append_complete_unmodeled; exact H
                |eapply check_openat_rdwr_complete_unmodeled; exact H
                |eapply check_openat_rdwr_excl_complete_unmodeled; exact H]).
  reflexivity.
Qed.

(** No arm of the body claims a copy-in of its own: each returns either
    through [check_ret_only], which forces every ledger empty, or
    through [check_new_fd_result], which matches six empty lists.  That
    is what lets the wrapper equate the WHOLE claimed ledger with the one
    pathname range rather than with a prefix of it. *)
Local Ltac op_nfd_cnil :=
  match goal with
  | Hx : check_new_fd_result _ _ _ _ = CheckOk _ _ |- _ =>
      eapply check_new_fd_result_no_copyin; exact Hx
  end.

Local Ltac arm_cnil :=
  first [ op_ret_cnil
        | eapply check_open_result_mk_no_copyin; eassumption
        | unfold check_create_wronly, check_open_result in *; op_nfd_cnil
        | unfold check_open_append, check_open_result in *; op_nfd_cnil
        | unfold check_open_rdwr, check_open_result in *; op_nfd_cnil
        | dev_cnil
        | discriminate ].

Local Lemma check_openat_read_no_copyin : forall r eff m m' evs,
  check_openat_read r eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros r eff m m' evs H. unfold check_openat_read in H.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try (destruct e as [ino| |dk|lb]; cbv iota in H;
         try (destruct dk; cbv iota in H)); arm_cnil.
Qed.

Local Lemma check_openat_create_no_copyin : forall r eff m m' evs,
  check_openat_create r eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros r eff m m' evs H. unfold check_openat_create in H.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try (destruct e as [ino| |dk|lb]; cbv iota in H;
         try (destruct dk; cbv iota in H)); arm_cnil.
Qed.

Local Lemma check_openat_excl_no_copyin : forall r eff m m' evs,
  check_openat_excl r eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros r eff m m' evs H. unfold check_openat_excl in H.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try (destruct e as [ino| |dk|lb]; cbv iota in H;
         try (destruct dk; cbv iota in H)); arm_cnil.
Qed.

Local Lemma check_openat_append_no_copyin : forall excl r eff m m' evs,
  check_openat_append excl r eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros excl r eff m m' evs H. unfold check_openat_append in H.
  destruct excl; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try (destruct e as [ino| |dk|lb]; cbv iota in H;
         try (destruct dk; cbv iota in H)); arm_cnil.
Qed.

Local Lemma check_openat_rdwr_no_copyin : forall creat trunc r eff m m' evs,
  check_openat_rdwr creat trunc r eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros creat trunc r eff m m' evs H. unfold check_openat_rdwr in H.
  destruct creat; destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try (destruct e as [ino| |dk|lb]; cbv iota in H;
         try (destruct dk; cbv iota in H)); arm_cnil.
Qed.

Local Lemma check_openat_rdwr_excl_no_copyin : forall r eff m m' evs,
  check_openat_rdwr_excl r eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros r eff m m' evs H. unfold check_openat_rdwr_excl in H.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try (destruct e as [ino| |dk|lb]; cbv iota in H;
         try (destruct dk; cbv iota in H)); arm_cnil.
Qed.

Local Lemma check_openat_dir_no_copyin : forall r eff m m' evs,
  check_openat_dir r eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros r eff m m' evs H. unfold check_openat_dir in H.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try (destruct e as [ino| |dk|lb]; cbv iota in H;
         try (destruct dk; cbv iota in H)); arm_cnil.
Qed.

Local Lemma check_openat_procfd_no_copyin : forall n flags eff m m' evs,
  check_openat_procfd n flags eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros n flags eff m m' evs H. unfold check_openat_procfd in H. cbv zeta in H.
  destruct (negb (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       wr_create_flags
                  || Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       append_create_flags)%bool); [discriminate|].
  destruct (fd_lookup (m_fds m) n)
    as [[ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam]|];
    try discriminate; try op_ret_cnil.
  all: destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [eapply check_open_result_mk_no_copyin; exact H|];
    destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                wr_create_flags);
    [unfold check_create_wronly, check_open_result in H; op_nfd_cnil
    |unfold check_open_append, check_open_result in H; op_nfd_cnil].
Qed.

Local Lemma check_openat_resolved_no_copyin : forall p flags eff m m' evs,
  check_openat_resolved p flags eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros p flags eff m m' evs H. unfold check_openat_resolved in H.
  destruct (proc_self_fd p) as [n|];
    [eapply check_openat_procfd_no_copyin; exact H|].
  destruct (Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p) as [[r lk] ts] eqn:Hr.
  cbv iota zeta in H.
  destruct (Z.eqb (open_shape flags) 0);
    cbv iota in H; [eapply check_openat_read_no_copyin; exact H|].
  destruct (Z.eqb (open_shape flags) wr_create_flags); cbv iota in H;
    [eapply check_openat_create_no_copyin; exact H|].
  destruct (is_excl_create (open_shape flags));
    cbv iota in H; [eapply check_openat_excl_no_copyin; exact H|].
  destruct (Z.eqb (open_shape flags) O_DIRECTORY);
    cbv iota in H; [eapply check_openat_dir_no_copyin; exact H|].
  destruct (Z.eqb (open_shape flags) append_create_flags); cbv iota in H;
    [eapply check_openat_append_no_copyin; exact H|].
  destruct (rdwr_open_word (open_shape flags));
    cbv iota in H; [eapply check_openat_rdwr_no_copyin; exact H|].
  destruct (is_rdwr_excl_create (open_shape flags));
    cbv iota in H; [eapply check_openat_rdwr_excl_no_copyin; exact H|].
  destruct (is_excl_append_create (open_shape flags));
    cbv iota in H; [eapply check_openat_append_no_copyin; exact H|].
  discriminate.
Qed.

Local Lemma check_openat_body_sound_ok : forall i dirfd pathp flags eff m m' evs,
  check_openat_body i dirfd pathp flags eff m = CheckOk m' evs ->
  openat_body_spec i m dirfd pathp flags i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_openat_body, openat_body_spec in *.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try op_ret_ok.
  destruct (path_eqb p []); cbv iota in H |- *; [op_ret_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [discriminate|].
  eapply check_openat_resolved_sound_ok; exact H.
Qed.

Local Lemma check_openat_body_sound_unmodeled : forall i dirfd pathp flags eff m,
  check_openat_body i dirfd pathp flags eff m = CheckUnmodeled ->
  openat_body_spec i m dirfd pathp flags i m Unmodeled.
Proof.
  intros i dirfd pathp flags eff m H.
  unfold check_openat_body, openat_body_spec in *.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try op_ret_nu.
  destruct (path_eqb p []); cbv iota in H |- *; [op_ret_nu|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [apply unmodeled_intro|].
  eapply check_openat_resolved_sound_unmodeled. exact H.
Qed.

Local Lemma check_openat_body_complete_ok : forall i dirfd pathp flags eff m m' evs,
  openat_body_spec i m dirfd pathp flags i m (Ok eff m' evs) ->
  check_openat_body i dirfd pathp flags eff m = CheckOk m' evs
  /\ eff_copyins eff = [].
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_openat_body, openat_body_spec in *.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try (split; [op_ret_co
                |unfold err_ret, ret_only, pure in *; inv_ok; reflexivity]).
  destruct (path_eqb p []); cbv iota in H |- *;
    [split; [op_ret_co
            |unfold err_ret, ret_only, pure in *; inv_ok; reflexivity]|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [unfold unmodeled in H; inv_ok|].
  assert (Hc : check_openat_resolved p flags eff m = CheckOk m' evs)
    by (eapply check_openat_resolved_complete_ok; exact H).
  split; [exact Hc | eapply check_openat_resolved_no_copyin; exact Hc].
Qed.

Local Lemma check_openat_body_complete_unmodeled : forall i dirfd pathp flags m eff,
  openat_body_spec i m dirfd pathp flags i m Unmodeled ->
  check_openat_body i dirfd pathp flags eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  unfold check_openat_body, openat_body_spec in *.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail).
  destruct (path_eqb p []); cbv iota in H |- *; [sys_unfold; inv_ok; fail|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [reflexivity|].
  eapply check_openat_resolved_complete_unmodeled. exact H.
Qed.

Local Lemma openat_core_ok_inv : forall i dirfd pathp flags eff m m' evs,
  openat_core_spec dirfd pathp flags i m (Ok eff m' evs) ->
  negb (modeled_open_flags flags) = false /\
  walk_refusals (open_walk_mode flags) pathp (openat_body_spec i m dirfd pathp flags)
    i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold openat_core_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  unfold bind, get_model in H. cbv beta iota in H.
  destruct H as (model & m1 & evs1 & evs2 & Hget & Hbody & Hevs).
  inversion Hget; clear Hget; subst.
  destruct (negb (modeled_open_flags flags)) eqn:Hflags.
  - unfold unmodeled in Hbody. discriminate Hbody.
  - split; [reflexivity|exact Hbody].
Qed.

Local Lemma openat_core_unmodeled_inv : forall i dirfd pathp flags m,
  openat_core_spec dirfd pathp flags i m Unmodeled ->
  negb (modeled_open_flags flags) = true \/
  (negb (modeled_open_flags flags) = false /\
   walk_refusals (open_walk_mode flags) pathp (openat_body_spec i m dirfd pathp flags)
     i m Unmodeled).
Proof.
  intros i dirfd pathp flags m H. unfold openat_core_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  unfold bind, get_model in H. cbv beta iota in H.
  destruct H as [Hget | (model & m1 & evs1 & Hget & Hbody)].
  - discriminate Hget.
  - inversion Hget; clear Hget; subst.
    destruct (negb (modeled_open_flags flags)) eqn:Hflags.
    + left. reflexivity.
    + right. split; [reflexivity|exact Hbody].
Qed.

(** The body with [check_walk_refusals] around it, from the body's four
    and [Checks.Sys.Prelude]'s section lemmas. *)
Local Lemma check_openat_body_ok_copyins_nil :
    forall i dirfd pathp flags eff m m' evs,
  check_openat_body i dirfd pathp flags eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  exact (proj2 (check_openat_body_complete_ok _ _ _ _ _ _ _ _
                  (check_openat_body_sound_ok _ _ _ _ _ _ _ _ H))).
Qed.

Local Lemma check_openat_walked_sound_ok : forall i dirfd pathp flags m eff m' evs,
  check_walk_refusals (open_walk_mode flags) i pathp eff m
    (check_openat_body i dirfd pathp flags eff m) = CheckOk m' evs ->
  walk_refusals (open_walk_mode flags) pathp (openat_body_spec i m dirfd pathp flags)
    i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags m.
  apply (check_walk_refusals_sound_ok (open_walk_mode flags) _
           (fun e => check_openat_body i dirfd pathp flags e m)).
  - intros. eapply check_openat_body_sound_ok. eassumption.
  - intros. eapply check_openat_body_sound_unmodeled. eassumption.
  - intros e m1 evs1 Hs. exact (proj1 (check_openat_body_complete_ok _ _ _ _ _ _ _ _ Hs)).
  - intros. eapply check_openat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_openat_walked_sound_unmodeled : forall i dirfd pathp flags m eff,
  check_walk_refusals (open_walk_mode flags) i pathp eff m
    (check_openat_body i dirfd pathp flags eff m) = CheckUnmodeled ->
  walk_refusals (open_walk_mode flags) pathp (openat_body_spec i m dirfd pathp flags)
    i m Unmodeled.
Proof.
  intros i dirfd pathp flags m.
  apply (check_walk_refusals_sound_unmodeled (open_walk_mode flags) _
           (fun e => check_openat_body i dirfd pathp flags e m)).
  - intros. eapply check_openat_body_sound_ok. eassumption.
  - intros. eapply check_openat_body_sound_unmodeled. eassumption.
  - intros e m1 evs1 Hs. exact (proj1 (check_openat_body_complete_ok _ _ _ _ _ _ _ _ Hs)).
  - intros. eapply check_openat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_openat_walked_complete_ok : forall i dirfd pathp flags m eff m' evs,
  walk_refusals (open_walk_mode flags) pathp (openat_body_spec i m dirfd pathp flags)
    i m (Ok eff m' evs) ->
  check_walk_refusals (open_walk_mode flags) i pathp eff m
    (check_openat_body i dirfd pathp flags eff m)
    = CheckOk m' evs
  /\ eff_copyins eff = [].
Proof.
  intros i dirfd pathp flags m eff m' evs H.
  assert (Hc : check_walk_refusals (open_walk_mode flags) i pathp eff m
                 (check_openat_body i dirfd pathp flags eff m) = CheckOk m' evs).
  { revert eff m' evs H.
    apply (check_walk_refusals_complete_ok (open_walk_mode flags) _
             (fun e => check_openat_body i dirfd pathp flags e m)).
    - intros. eapply check_openat_body_sound_ok. eassumption.
    - intros. eapply check_openat_body_sound_unmodeled. eassumption.
    - intros e m1 evs1 Hs. exact (proj1 (check_openat_body_complete_ok _ _ _ _ _ _ _ _ Hs)).
    - intros. eapply check_openat_body_complete_unmodeled. eassumption. }
  split; [exact Hc|].
  eapply check_walk_refusals_copyins_nil; [|exact Hc].
  intros. eapply check_openat_body_ok_copyins_nil. eassumption.
Qed.

Local Lemma check_openat_walked_complete_unmodeled : forall i dirfd pathp flags m eff,
  walk_refusals (open_walk_mode flags) pathp (openat_body_spec i m dirfd pathp flags)
    i m Unmodeled ->
  check_walk_refusals (open_walk_mode flags) i pathp eff m
    (check_openat_body i dirfd pathp flags eff m)
    = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m.
  apply (check_walk_refusals_complete_unmodeled (open_walk_mode flags) _
           (fun e => check_openat_body i dirfd pathp flags e m)).
  - intros. eapply check_openat_body_sound_ok. eassumption.
  - intros. eapply check_openat_body_sound_unmodeled. eassumption.
  - intros e m1 evs1 Hs. exact (proj1 (check_openat_body_complete_ok _ _ _ _ _ _ _ _ Hs)).
  - intros. eapply check_openat_body_complete_unmodeled. eassumption.
Qed.

(** The call from the flag word on, under its pathname ledger: the part
    [getname_flags]' own refusals wrap.  The four are stated over
    [check_openat]'s own expression, not over a name for it: a name
    the kernel has to unfold against that expression costs minutes per
    [Qed]. *)
Local Lemma check_openat_fetched_sound_ok : forall i dirfd pathp flags m eff m' evs,
  (if negb (modeled_open_flags flags) then CheckUnmodeled
   else
     check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
       (check_walk_refusals (open_walk_mode flags) i pathp (clear_copyins eff) m
          (check_openat_body i dirfd pathp flags (clear_copyins eff) m)))
  = CheckOk m' evs ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (openat_core_spec dirfd pathp flags) i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags m eff m' evs H.
  destruct (negb (modeled_open_flags flags)) eqn:Hfl; [discriminate|].
  cbv iota zeta in H.
  apply check_copyins_after_ok_iff in H as (Hreads & Hchecked).
  apply record_copyins_clear_ok; [exact Hreads|].
  unfold openat_core_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
  rewrite Hfl. cbv iota.
  now apply check_openat_walked_sound_ok.
Qed.

Local Lemma check_openat_fetched_sound_unmodeled : forall i dirfd pathp flags m eff,
  (if negb (modeled_open_flags flags) then CheckUnmodeled
   else
     check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
       (check_walk_refusals (open_walk_mode flags) i pathp (clear_copyins eff) m
          (check_openat_body i dirfd pathp flags (clear_copyins eff) m)))
  = CheckUnmodeled ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (openat_core_spec dirfd pathp flags) i m Unmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  apply record_copyins_unmodeled. unfold openat_core_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
  destruct (negb (modeled_open_flags flags)) eqn:Hfl; cbv iota;
    [apply unmodeled_intro|].
  cbv iota zeta in H. apply check_copyins_after_unmodeled in H.
  eapply check_openat_walked_sound_unmodeled. exact H.
Qed.

Local Lemma check_openat_fetched_complete_ok : forall i dirfd pathp flags m eff m' evs,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (openat_core_spec dirfd pathp flags) i m (Ok eff m' evs) ->
  (if negb (modeled_open_flags flags) then CheckUnmodeled
   else
     check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
       (check_walk_refusals (open_walk_mode flags) i pathp (clear_copyins eff) m
          (check_openat_body i dirfd pathp flags (clear_copyins eff) m)))
  = CheckOk m' evs.
Proof.
  intros i dirfd pathp flags m eff m' evs H.
  apply record_copyins_ok_inv in H.
  destruct H as (core & Hcore & ->).
  apply openat_core_ok_inv in Hcore.
  destruct Hcore as (Hflags & Hbody).
  apply check_openat_walked_complete_ok in Hbody.
  destruct Hbody as (Hchecked & Hcopyins).
  rewrite Hflags. cbv iota zeta.
  apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
  - cbn [with_copyins eff_copyins]. rewrite Hcopyins, app_nil_r. reflexivity.
  - destruct core as [ret ws zs us cs copyins].
    cbn in Hcopyins. subst copyins.
    exact Hchecked.
Qed.

Local Lemma check_openat_fetched_complete_unmodeled : forall i dirfd pathp flags m eff,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (openat_core_spec dirfd pathp flags) i m Unmodeled ->
  (if negb (modeled_open_flags flags) then CheckUnmodeled
   else
     check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
       (check_walk_refusals (open_walk_mode flags) i pathp (clear_copyins eff) m
          (check_openat_body i dirfd pathp flags (clear_copyins eff) m)))
  = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  apply record_copyins_unmodeled_inv in H.
  apply openat_core_unmodeled_inv in H.
  destruct H as [Hflags | (Hflags & Hbody)].
  - rewrite Hflags. reflexivity.
  - apply check_openat_walked_complete_unmodeled
      with (eff := clear_copyins eff) in Hbody.
    rewrite Hflags. cbv iota zeta.
    unfold check_copyins_after. rewrite Hbody. reflexivity.
Qed.

(** [check_openat] unfolded, as an equation.  The two soundness
    exports rewrite their hypothesis with it: handing the kernel the
    hypothesis itself where its unfolded type is expected costs it
    minutes per [Qed]. *)
Local Lemma check_openat_eq : forall i dirfd pathp flags eff m,
  check_openat i dirfd pathp flags eff m
  = check_getname_refusals i pathp eff m
      (if negb (modeled_open_flags flags) then CheckUnmodeled
       else
         check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
           (check_walk_refusals (open_walk_mode flags) i pathp (clear_copyins eff) m
              (check_openat_body i dirfd pathp flags (clear_copyins eff) m))).
Proof. intros. unfold check_openat. cbv zeta. reflexivity. Qed.

(** The four exports: the fetched call with [getname_flags]' own
    refusals around it ([Checks.Sys.Prelude]'s section lemmas). *)
Lemma check_openat_sound_ok : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs ->
  openat_spec dirfd pathp flags i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  rewrite check_openat_eq in H.
  unfold openat_spec. eapply bind_ok0; [apply input_ok|]. cbv beta.
  exact (check_getname_refusals_sound_ok pathp _ _ i m
           (check_openat_fetched_sound_ok i dirfd pathp flags m)
           (check_openat_fetched_sound_unmodeled i dirfd pathp flags m)
           (check_openat_fetched_complete_ok i dirfd pathp flags m)
           (check_openat_fetched_complete_unmodeled i dirfd pathp flags m)
           eff m' evs H).
Qed.

Lemma check_openat_sound_unmodeled : forall i dirfd pathp flags eff m,
  check_openat i dirfd pathp flags eff m = CheckUnmodeled ->
  openat_spec dirfd pathp flags i m Unmodeled.
Proof.
  intros i dirfd pathp flags eff m H.
  rewrite check_openat_eq in H.
  unfold openat_spec. eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  exact (check_getname_refusals_sound_unmodeled pathp _ _ i m
           (check_openat_fetched_sound_ok i dirfd pathp flags m)
           (check_openat_fetched_sound_unmodeled i dirfd pathp flags m)
           (check_openat_fetched_complete_ok i dirfd pathp flags m)
           (check_openat_fetched_complete_unmodeled i dirfd pathp flags m)
           eff H).
Qed.

Lemma check_openat_complete_ok : forall i dirfd pathp flags eff m m' evs,
  openat_spec dirfd pathp flags i m (Ok eff m' evs) ->
  check_openat i dirfd pathp flags eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold openat_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  unfold check_openat. cbv zeta.
  exact (check_getname_refusals_complete_ok pathp _ _ i m
           (check_openat_fetched_sound_ok i dirfd pathp flags m)
           (check_openat_fetched_sound_unmodeled i dirfd pathp flags m)
           (check_openat_fetched_complete_ok i dirfd pathp flags m)
           (check_openat_fetched_complete_unmodeled i dirfd pathp flags m)
           eff m' evs H).
Qed.

Lemma check_openat_complete_unmodeled : forall i dirfd pathp flags m eff,
  openat_spec dirfd pathp flags i m Unmodeled ->
  check_openat i dirfd pathp flags eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  unfold openat_spec in H. apply input_bind_unmodeled_inv in H. cbv beta in H.
  unfold check_openat. cbv zeta.
  exact (check_getname_refusals_complete_unmodeled pathp _ _ i m
           (check_openat_fetched_sound_ok i dirfd pathp flags m)
           (check_openat_fetched_sound_unmodeled i dirfd pathp flags m)
           (check_openat_fetched_complete_ok i dirfd pathp flags m)
           (check_openat_fetched_complete_unmodeled i dirfd pathp flags m)
           eff H).
Qed.

(* ----------------------------------------------------------------- close *)

Lemma check_close_sound_ok : forall fd eff m m' evs i,
  check_close fd eff m = CheckOk m' evs ->
  close_spec fd i m (Ok eff m' evs).
Proof.
  intros fd eff m m' evs i H.
  unfold check_close in H. unfold close_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd;
    apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
    (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd.
  - eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
  - apply pure_ok.
Qed.

Lemma check_close_sound_unmodeled : forall fd eff m i,
  check_close fd eff m = CheckUnmodeled -> close_spec fd i m Unmodeled.
Proof.
  intros fd eff m i H. unfold check_close in H.
  destruct (fd_lookup (m_fds m) fd); now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_close_complete_ok : forall fd eff m m' evs i,
  close_spec fd i m (Ok eff m' evs) -> check_close fd eff m = CheckOk m' evs.
Proof.
  intros fd eff m m' evs i H.
  unfold close_spec in H. unfold check_close. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_close_complete_unmodeled : forall fd m i eff,
  close_spec fd i m Unmodeled -> check_close fd eff m = CheckUnmodeled.
Proof.
  intros fd m i eff H.
  unfold close_spec in H. sys_unfold. cbv iota in H. inv_ok.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; hall Hfd; inv_ok;
    discriminate.
Qed.

(* ----------------------------------------------------------------- lseek *)

Definition check_ftruncate (fd len : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if (bv_signed len <? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
  else
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdSocket _) => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdStream _ _ _) => check_ret_only eff (errno_ret EINVAL) m []  (* S_ISSOCK too *)
  | Some (FdDgram _) => check_ret_only eff (errno_ret EINVAL) m []  (* and a datagram socket *)
  | Some (FdEventfd _) => check_ret_only eff (errno_ret EINVAL) m []  (* no type bits: not S_ISREG *)
  | Some (FdPipe _ _) => check_ret_only eff (errno_ret EINVAL) m []  (* S_IFIFO, not S_ISREG *)
  | Some (FdDevNull _ _) => check_ret_only eff (errno_ret EINVAL) m []  (* S_IFCHR, not S_ISREG *)
  | Some (FdUrandom _ _) => check_ret_only eff (errno_ret EINVAL) m []  (* S_IFCHR again *)
  | Some (FdFile _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdDir _) => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdFileA ino _) | Some (FdFileW ino _) | Some (FdFileRW ino _) =>
      (* the writable kinds: the inode's contents, offsets kept *)
      if negb (modeled_truncate_gap (Fs.fs_ino_data (m_fs m) ino) len) then CheckUnmodeled
      else
        check_ret_only eff (Z_to_bv 64 0)
          (with_fs (Fs.fs_set_ino_data (m_fs m) ino
                      (file_truncate (Fs.fs_ino_data (m_fs m) ino) len)) m) []
  end.

Lemma check_ftruncate_sound_ok : forall fd len eff m m' evs i,
  check_ftruncate fd len eff m = CheckOk m' evs ->
  ftruncate_spec fd len i m (Ok eff m' evs).
Proof.
  intros fd len eff m m' evs i H.
  unfold check_ftruncate in H. unfold ftruncate_spec.
  destruct ((bv_signed len <? 0)%Z) eqn:Hneg.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (fd_lookup (m_fds m) fd) as [[ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|id side st|ctx|fam]|] eqn:Hfd;
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
         apply pure_ok).
  (* the writable arms: the grow bound, then the inode's contents *)
  all: destruct (negb (modeled_truncate_gap (Fs.fs_ino_data (m_fs m) ino) len)) eqn:Hgap;
    [discriminate|].
  all: apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->).
  all: eapply bind_ok0; [apply get_model_ok|]; cbv beta iota; srw Hfd;
       srw Hgap; eapply bind_ok0; [apply modify_ok|]; apply pure_ok.
Qed.

Lemma check_ftruncate_sound_unmodeled : forall fd len eff m i,
  check_ftruncate fd len eff m = CheckUnmodeled ->
  ftruncate_spec fd len i m Unmodeled.
Proof.
  intros fd len eff m i H.
  unfold check_ftruncate in H. unfold ftruncate_spec.
  destruct ((bv_signed len <? 0)%Z) eqn:Hneg.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (fd_lookup (m_fds m) fd) as [[ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|id side st|ctx|fam]|] eqn:Hfd;
    try (now apply check_ret_only_no_unmodeled in H).
  (* every destruct precedes the bind: the spec's test sits under
     [get_model]'s binder, so it is only rewritable once [get_model_ok]
     has instantiated it *)
  all: destruct (negb (modeled_truncate_gap (Fs.fs_ino_data (m_fs m) ino) len)) eqn:Hgap;
       [ eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
         srw Hfd; srw Hgap; apply unmodeled_intro
       | now apply check_ret_only_no_unmodeled in H ].
Qed.

Lemma check_ftruncate_complete_ok : forall fd len eff m m' evs i,
  ftruncate_spec fd len i m (Ok eff m' evs) ->
  check_ftruncate fd len eff m = CheckOk m' evs.
Proof.
  intros fd len eff m m' evs i H.
  unfold ftruncate_spec in H. unfold check_ftruncate. sys_unfold.
  cbv iota in H. inv_ok.
  destruct ((bv_signed len <? 0)%Z) eqn:Hneg; hall Hneg; inv_ok;
    try (destruct (fd_lookup (m_fds m) fd) as [[ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|id side st|ctx|fam]|] eqn:Hfd;
         hall Hfd; inv_ok);
    try (destruct (negb (modeled_truncate_gap (Fs.fs_ino_data (m_fs m) ino) len)) eqn:Hgap;
         hall Hgap; inv_ok);
    cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_ftruncate_complete_unmodeled : forall fd len m i eff,
  ftruncate_spec fd len i m Unmodeled ->
  check_ftruncate fd len eff m = CheckUnmodeled.
Proof.
  intros fd len m i eff H.
  unfold ftruncate_spec in H. unfold check_ftruncate. sys_unfold.
  cbv iota in H. inv_ok.
  destruct ((bv_signed len <? 0)%Z) eqn:Hneg; hall Hneg; inv_ok;
    try (destruct (fd_lookup (m_fds m) fd) as [[ch|ino cur|ino cur|ino cur|ino cur|k|sk|pid pw|rd wr|urd uwr|id side st|ctx|fam]|] eqn:Hfd;
         hall Hfd; inv_ok);
    try (destruct (negb (modeled_truncate_gap (Fs.fs_ino_data (m_fs m) ino) len)) eqn:Hgap;
         hall Hgap; inv_ok);
    first [reflexivity | discriminate].
Qed.

(* ============================================================ faccessat (48)

   The acceptor for the arm of [Fs.Open.faccessat_spec] that can succeed:
   either 0 or an injectable errno, with NO state change either way — the
   two alternatives write the same model, which is what makes this
   syscall a pure observation — and FIVE EMPTY LEDGERS, since faccessat
   writes, zeroes, unmaps and copies out nothing, and the pathname
   copy-in is cleared by the wrapper before the body sees the effect.
   So only a forged ledger reaches the other half of the claim. *)
Definition check_access_exists (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in faccessat_errnos ret || bv_eqb ret (Z_to_bv 64 0)
      then CheckOk m []
      else CheckReject
  | _ => CheckReject
  end.

Local Definition check_faccessat_body (md : Fs.WalkMode) (i : SyscallInput)
    (dirfd pathp : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | CstrOk p =>
      if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
      else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
      else
        let '(r, _, _) := Fs.resolve md (m_fs m) (m_cwd m) p in
        match r with
        | Fs.RFound _ _ => check_access_exists eff m
        | Fs.RMissing _ _ => check_ret_only eff (errno_ret ENOENT) m []
        | Fs.RNotDir _ => check_ret_only eff (errno_ret ENOTDIR) m []
        | Fs.RAbsent _ => check_ret_only eff (errno_ret ENOENT) m []
        | Fs.RLoop => check_ret_only eff (errno_ret ELOOP) m []
        | Fs.ROutside => CheckUnmodeled
        | Fs.RParent _ _ => CheckUnmodeled
        end
  end.

(** The pathname copy-in, as [check_openat] and
    [Checks.Sys.Fs.Namei.check_unlinkat] check it: decide the body
    against the effect with the ledger cleared, then require the claimed
    ledger to be exactly that one range.  Both mode arms are outside the
    wrapper, mirroring the spec — the kernel decides the mode before
    [user_path_at], so an honest -EINVAL carries no copy-in at all.
    [getname_flags]' own refusals stand around the ledger
    ([check_getname_refusals]), behind the mode arms. *)
Definition check_faccessat (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (modeled_access_mode mode)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (access_mode_f_ok mode) then CheckUnmodeled
  else
    let reads := [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] in
    check_getname_refusals i pathp eff m
      (check_copyins_after reads eff
         (check_walk_refusals (Fs.WalkFull true false) i pathp (clear_copyins eff) m
            (check_faccessat_body (Fs.WalkFull true false) i dirfd pathp
               (clear_copyins eff) m))).

(** Read the input and the model, the two steps [faccessat_spec] takes
    before the mode test. *)
Ltac fa_open :=
  eapply bind_ok0; [apply input_ok|]; cbv beta;
  eapply bind_ok0; [apply get_model_ok|]; cbv beta iota.

Ltac fa_open_u :=
  eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
  eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota.

(** 0 is not an injectable errno, so [access_exists_spec]'s two
    alternatives never both have to be justified by the same return —
    though either would do, since both leave the model alone. *)
Lemma errno_ret_in_faccessat_zero :
  errno_ret_in faccessat_errnos (Z_to_bv 64 0) = false.
Proof.
  apply errno_ret_in_fd; [reflexivity|].
  rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia). lia.
Qed.

Local Lemma check_access_exists_sound_ok : forall i eff m m' evs,
  check_access_exists eff m = CheckOk m' evs ->
  access_exists_spec i m (Ok eff m' evs).
Proof.
  intros i eff m m' evs H. unfold check_access_exists in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws as [|w ws'];
    [destruct zs as [|z zs']|]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  unfold access_exists_spec.
  destruct (errno_ret_in faccessat_errnos ret) eqn:He; cbn in H.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    apply pure_ok.
  - destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq; subst ret.
    apply alt_r. apply pure_ok.
Qed.

Local Lemma check_access_exists_no_unmodeled : forall eff m,
  check_access_exists eff m = CheckUnmodeled -> False.
Proof.
  intros eff m H. unfold check_access_exists in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws; [destruct zs|];
    destruct us; destruct cs; destruct cis; try discriminate.
  destruct (errno_ret_in faccessat_errnos ret); cbn in H; [discriminate|].
  destruct (bv_eqb ret (Z_to_bv 64 0)); discriminate.
Qed.

Local Lemma check_access_exists_complete_ok : forall i eff m m' evs,
  access_exists_spec i m (Ok eff m' evs) ->
  check_access_exists eff m = CheckOk m' evs.
Proof.
  intros i eff m m' evs H. unfold access_exists_spec in H. sys_unfold.
  inv_ok.
  - (* the injectable failure *)
    unfold check_access_exists.
    match goal with
    | |- context [errno_ret_in ?es (errno_ret ?e)] =>
        rewrite (errno_ret_in_intro es e) by assumption
    end.
    reflexivity.
  - (* the plain 0 *)
    unfold check_access_exists.
    rewrite errno_ret_in_faccessat_zero, bv_eqb_refl. reflexivity.
Qed.

Local Lemma check_access_exists_ok_copyins_nil : forall eff m m' evs,
  check_access_exists eff m = CheckOk m' evs -> eff_copyins eff = [].
Proof.
  intros eff m m' evs H. unfold check_access_exists in H.
  destruct eff as [ret ws zs us cs cis]; destruct ws; [destruct zs|];
    destruct us; destruct cs; destruct cis; try discriminate; reflexivity.
Qed.

(** The deterministic arms, from either side: [err_ret] is [pure] of a
    bare-return effect, so one inversion settles the outcome and
    [check_ret_only] then reduces. *)
Ltac fa_det :=
  match goal with
  | H : err_ret _ _ _ (Ok _ _ _) |- _ =>
      unfold err_ret, ret_only, pure in H; inversion H; subst;
      cbn; rewrite ?bv_eqb_refl; reflexivity
  end.

Ltac fa_det_u :=
  match goal with
  | H : err_ret _ _ _ Unmodeled |- _ =>
      unfold err_ret, ret_only, pure in H; discriminate H
  end.

Ltac fa_unmod_h :=
  match goal with
  | H : unmodeled _ _ (Ok _ _ _) |- _ => unfold unmodeled in H; discriminate H
  end.

Local Lemma access_exists_no_unmodeled : forall i m,
  access_exists_spec i m Unmodeled -> False.
Proof.
  intros i m H. unfold access_exists_spec in H. sys_unfold. inv_ok.
Qed.

Local Ltac fa_ret_ok :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckOk _ _ |- _ =>
      apply check_ret_only_ok_iff in Hx; destruct Hx as (-> & -> & ->);
      unfold err_ret, ret_only; apply pure_ok
  end.
Local Ltac fa_ret_nu :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckUnmodeled |- _ =>
      now apply check_ret_only_no_unmodeled in Hx
  end.
Local Ltac fa_ret_co :=
  unfold err_ret, ret_only, pure in *; inv_ok;
  apply check_ret_only_ok_iff; now repeat split.
Local Ltac fa_ret_cnil :=
  match goal with
  | Hx : check_ret_only _ _ _ _ = CheckOk _ _ |- _ =>
      apply check_ret_only_ok_iff in Hx; destruct Hx as (-> & _ & _);
      reflexivity
  end.

Local Lemma check_faccessat_body_sound_ok : forall md i dirfd pathp eff m m' evs,
  check_faccessat_body md i dirfd pathp eff m = CheckOk m' evs ->
  faccessat_body_spec md dirfd pathp i m i m (Ok eff m' evs).
Proof.
  intros md i dirfd pathp eff m m' evs H.
  unfold check_faccessat_body in H. unfold faccessat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try fa_ret_ok.
  destruct (path_eqb p []); cbv iota in H |- *; [fa_ret_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [discriminate|].
  destruct (Fs.resolve md (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try fa_ret_ok; try discriminate.
  now apply check_access_exists_sound_ok.
Qed.

Local Lemma check_faccessat_body_sound_unmodeled : forall md i dirfd pathp eff m,
  check_faccessat_body md i dirfd pathp eff m = CheckUnmodeled ->
  faccessat_body_spec md dirfd pathp i m i m Unmodeled.
Proof.
  intros md i dirfd pathp eff m H.
  unfold check_faccessat_body in H. unfold faccessat_body_spec.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try fa_ret_nu.
  destruct (path_eqb p []); cbv iota in H |- *; [fa_ret_nu|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [apply unmodeled_intro|].
  destruct (Fs.resolve md (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try fa_ret_nu; try apply unmodeled_intro.
  exfalso. eapply check_access_exists_no_unmodeled. exact H.
Qed.

Local Lemma check_faccessat_body_complete_ok :
    forall md i dirfd pathp eff m m' evs,
  faccessat_body_spec md dirfd pathp i m i m (Ok eff m' evs) ->
  check_faccessat_body md i dirfd pathp eff m = CheckOk m' evs.
Proof.
  intros md i dirfd pathp eff m m' evs H.
  unfold faccessat_body_spec in H. unfold check_faccessat_body.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try fa_ret_co.
  destruct (path_eqb p []); cbv iota in H |- *; [fa_ret_co|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [unfold unmodeled in H; inv_ok|].
  destruct (Fs.resolve md (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try fa_ret_co; try (unfold unmodeled in H; inv_ok; fail).
  eapply check_access_exists_complete_ok. exact H.
Qed.

Local Lemma check_faccessat_body_complete_unmodeled :
    forall md i dirfd pathp m eff,
  faccessat_body_spec md dirfd pathp i m i m Unmodeled ->
  check_faccessat_body md i dirfd pathp eff m = CheckUnmodeled.
Proof.
  intros md i dirfd pathp m eff H.
  unfold faccessat_body_spec in H. unfold check_faccessat_body.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail).
  destruct (path_eqb p []); cbv iota in H |- *; [sys_unfold; inv_ok; fail|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H |- *;
    [reflexivity|].
  destruct (Fs.resolve md (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta in H |- *.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H |- *;
    try (sys_unfold; inv_ok; fail); try reflexivity.
  exfalso. eapply access_exists_no_unmodeled. exact H.
Qed.

Local Lemma check_faccessat_body_ok_copyins_nil :
    forall md i dirfd pathp eff m m' evs,
  check_faccessat_body md i dirfd pathp eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros md i dirfd pathp eff m m' evs H.
  unfold check_faccessat_body in H.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota in H;
    try fa_ret_cnil.
  destruct (path_eqb p []); cbv iota in H; [fa_ret_cnil|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota in H; [discriminate|].
  destruct (Fs.resolve md (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta in H.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota in H;
    try fa_ret_cnil; try discriminate.
  eapply check_access_exists_ok_copyins_nil. exact H.
Qed.

(** The body with [check_walk_refusals] around it, from the body's four
    and [Checks.Sys.Prelude]'s section lemmas; [faccessat] and
    [faccessat2] share it, each with its own walk end [md]. *)
Local Lemma check_faccessat_walked_sound_ok : forall md i dirfd pathp m eff m' evs,
  check_walk_refusals md i pathp eff m (check_faccessat_body md i dirfd pathp eff m)
    = CheckOk m' evs ->
  walk_refusals md pathp (faccessat_body_spec md dirfd pathp i m) i m (Ok eff m' evs).
Proof.
  intros md i dirfd pathp m.
  apply (check_walk_refusals_sound_ok md _
           (fun e => check_faccessat_body md i dirfd pathp e m)).
  - intros. eapply check_faccessat_body_sound_ok. eassumption.
  - intros. eapply check_faccessat_body_sound_unmodeled. eassumption.
  - intros. eapply check_faccessat_body_complete_ok. eassumption.
  - intros. eapply check_faccessat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_faccessat_walked_sound_unmodeled : forall md i dirfd pathp m eff,
  check_walk_refusals md i pathp eff m (check_faccessat_body md i dirfd pathp eff m)
    = CheckUnmodeled ->
  walk_refusals md pathp (faccessat_body_spec md dirfd pathp i m) i m Unmodeled.
Proof.
  intros md i dirfd pathp m.
  apply (check_walk_refusals_sound_unmodeled md _
           (fun e => check_faccessat_body md i dirfd pathp e m)).
  - intros. eapply check_faccessat_body_sound_ok. eassumption.
  - intros. eapply check_faccessat_body_sound_unmodeled. eassumption.
  - intros. eapply check_faccessat_body_complete_ok. eassumption.
  - intros. eapply check_faccessat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_faccessat_walked_complete_ok : forall md i dirfd pathp m eff m' evs,
  walk_refusals md pathp (faccessat_body_spec md dirfd pathp i m) i m (Ok eff m' evs) ->
  check_walk_refusals md i pathp eff m (check_faccessat_body md i dirfd pathp eff m)
    = CheckOk m' evs.
Proof.
  intros md i dirfd pathp m.
  apply (check_walk_refusals_complete_ok md _
           (fun e => check_faccessat_body md i dirfd pathp e m)).
  - intros. eapply check_faccessat_body_sound_ok. eassumption.
  - intros. eapply check_faccessat_body_sound_unmodeled. eassumption.
  - intros. eapply check_faccessat_body_complete_ok. eassumption.
  - intros. eapply check_faccessat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_faccessat_walked_complete_unmodeled : forall md i dirfd pathp m eff,
  walk_refusals md pathp (faccessat_body_spec md dirfd pathp i m) i m Unmodeled ->
  check_walk_refusals md i pathp eff m (check_faccessat_body md i dirfd pathp eff m)
    = CheckUnmodeled.
Proof.
  intros md i dirfd pathp m.
  apply (check_walk_refusals_complete_unmodeled md _
           (fun e => check_faccessat_body md i dirfd pathp e m)).
  - intros. eapply check_faccessat_body_sound_ok. eassumption.
  - intros. eapply check_faccessat_body_sound_unmodeled. eassumption.
  - intros. eapply check_faccessat_body_complete_ok. eassumption.
  - intros. eapply check_faccessat_body_complete_unmodeled. eassumption.
Qed.

Local Lemma check_faccessat_walked_ok_copyins_nil :
    forall md i dirfd pathp eff m m' evs,
  check_walk_refusals md i pathp eff m (check_faccessat_body md i dirfd pathp eff m)
    = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros md i dirfd pathp eff m m' evs H.
  eapply check_walk_refusals_copyins_nil; [|exact H].
  intros. eapply check_faccessat_body_ok_copyins_nil. eassumption.
Qed.

(** The walked body under its pathname ledger, for either walk mode:
    the part [getname_flags]' own refusals wrap in both calls, stated
    over the checkers' own expression as openat's four are. *)
Local Lemma check_faccessat_fetched_sound_ok : forall md i dirfd pathp m eff m' evs,
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals md i pathp (clear_copyins eff) m
       (check_faccessat_body md i dirfd pathp (clear_copyins eff) m))
  = CheckOk m' evs ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals md pathp (faccessat_body_spec md dirfd pathp i m))
    i m (Ok eff m' evs).
Proof.
  intros md i dirfd pathp m eff m' evs H.
  apply check_copyins_after_ok_iff in H. destruct H as (Hreads & Hbody).
  apply record_copyins_clear_ok; [exact Hreads|].
  now apply check_faccessat_walked_sound_ok.
Qed.

Local Lemma check_faccessat_fetched_sound_unmodeled : forall md i dirfd pathp m eff,
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals md i pathp (clear_copyins eff) m
       (check_faccessat_body md i dirfd pathp (clear_copyins eff) m))
  = CheckUnmodeled ->
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals md pathp (faccessat_body_spec md dirfd pathp i m))
    i m Unmodeled.
Proof.
  intros md i dirfd pathp m eff H.
  apply check_copyins_after_unmodeled in H.
  apply record_copyins_unmodeled.
  eapply check_faccessat_walked_sound_unmodeled. exact H.
Qed.

Local Lemma check_faccessat_fetched_complete_ok : forall md i dirfd pathp m eff m' evs,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals md pathp (faccessat_body_spec md dirfd pathp i m))
    i m (Ok eff m' evs) ->
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals md i pathp (clear_copyins eff) m
       (check_faccessat_body md i dirfd pathp (clear_copyins eff) m))
  = CheckOk m' evs.
Proof.
  intros md i dirfd pathp m eff m' evs H.
  apply record_copyins_ok_inv in H.
  destruct H as (core & Hcore & ->).
  apply check_faccessat_walked_complete_ok in Hcore.
  pose proof (check_faccessat_walked_ok_copyins_nil _ _ _ _ _ _ _ _ Hcore) as Hnil.
  apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
  - cbn [with_copyins eff_copyins]. rewrite Hnil, app_nil_r. reflexivity.
  - destruct core as [ret ws zs us cs copyins].
    cbn in Hnil. subst copyins. exact Hcore.
Qed.

Local Lemma check_faccessat_fetched_complete_unmodeled : forall md i dirfd pathp m eff,
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (walk_refusals md pathp (faccessat_body_spec md dirfd pathp i m))
    i m Unmodeled ->
  check_copyins_after [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] eff
    (check_walk_refusals md i pathp (clear_copyins eff) m
       (check_faccessat_body md i dirfd pathp (clear_copyins eff) m))
  = CheckUnmodeled.
Proof.
  intros md i dirfd pathp m eff H.
  apply record_copyins_unmodeled_inv in H.
  unfold check_copyins_after.
  rewrite (check_faccessat_walked_complete_unmodeled md
             i dirfd pathp m (clear_copyins eff) H). reflexivity.
Qed.

Lemma check_faccessat_sound_ok : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs ->
  faccessat_spec dirfd pathp mode i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold check_faccessat in H. unfold faccessat_spec.
  destruct (negb (modeled_access_mode mode)) eqn:Hmo; cbv iota in H.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    fa_open. apply pure_ok. }
  destruct (negb (access_mode_f_ok mode)) eqn:Hfok; cbv iota in H;
    [discriminate|].
  cbv zeta in H. fa_open.
  exact (check_getname_refusals_sound_ok pathp _ _ i m
           (check_faccessat_fetched_sound_ok (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_sound_unmodeled (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_complete_ok (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_complete_unmodeled (Fs.WalkFull true false) i dirfd pathp m)
           eff m' evs H).
Qed.

Lemma check_faccessat_sound_unmodeled : forall i dirfd pathp mode eff m,
  check_faccessat i dirfd pathp mode eff m = CheckUnmodeled ->
  faccessat_spec dirfd pathp mode i m Unmodeled.
Proof.
  intros i dirfd pathp mode eff m H.
  unfold check_faccessat in H. unfold faccessat_spec.
  destruct (negb (modeled_access_mode mode)) eqn:Hmo; cbv iota in H;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (negb (access_mode_f_ok mode)) eqn:Hfok; cbv iota in H.
  { fa_open_u. apply unmodeled_intro. }
  cbv zeta in H. fa_open_u.
  exact (check_getname_refusals_sound_unmodeled pathp _ _ i m
           (check_faccessat_fetched_sound_ok (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_sound_unmodeled (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_complete_ok (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_complete_unmodeled (Fs.WalkFull true false) i dirfd pathp m)
           eff H).
Qed.

Lemma check_faccessat_complete_ok : forall i dirfd pathp mode eff m m' evs,
  faccessat_spec dirfd pathp mode i m (Ok eff m' evs) ->
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold faccessat_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta iota in H.
  unfold check_faccessat.
  destruct (negb (modeled_access_mode mode)) eqn:Hmo.
  { cbv iota in H. unfold err_ret, ret_only, pure in H. inversion H; subst.
    cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (negb (access_mode_f_ok mode)) eqn:Hfok; cbv iota in H;
    [fa_unmod_h|].
  cbv zeta.
  exact (check_getname_refusals_complete_ok pathp _ _ i m
           (check_faccessat_fetched_sound_ok (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_sound_unmodeled (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_complete_ok (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_complete_unmodeled (Fs.WalkFull true false) i dirfd pathp m)
           eff m' evs H).
Qed.

Lemma check_faccessat_complete_unmodeled : forall i dirfd pathp mode m eff,
  faccessat_spec dirfd pathp mode i m Unmodeled ->
  check_faccessat i dirfd pathp mode eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp mode m eff H.
  unfold faccessat_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply get_model_bind_unmodeled_inv in H. cbv beta iota in H.
  unfold check_faccessat.
  destruct (negb (modeled_access_mode mode)) eqn:Hmo.
  { cbv iota in H. unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (negb (access_mode_f_ok mode)) eqn:Hfok; cbv iota in H;
    [reflexivity|].
  cbv zeta.
  exact (check_getname_refusals_complete_unmodeled pathp _ _ i m
           (check_faccessat_fetched_sound_ok (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_sound_unmodeled (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_complete_ok (Fs.WalkFull true false) i dirfd pathp m)
           (check_faccessat_fetched_complete_unmodeled (Fs.WalkFull true false) i dirfd pathp m)
           eff H).
Qed.

(* =========================================================== faccessat2 (439)

   The same body, under a wrapper with one more test.  [do_faccessat] is
   the shared function, so the acceptor differs from [check_faccessat]
   only in the two flag arms: the kernel's own -EINVAL for a bit outside
   the three it accepts, and the decline for AT_EMPTY_PATH.  Both sit
   outside the copy-in wrapper, mirroring the spec — neither reaches
   [user_path_at], so neither carries a ledger. *)
Definition check_faccessat2 (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (modeled_access_mode mode)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (valid_access_flags flags)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (modeled_access_flags flags) then CheckUnmodeled
  else if negb (access_mode_f_ok mode) then CheckUnmodeled
  else
    let reads := [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)] in
    check_getname_refusals i pathp eff m
      (check_copyins_after reads eff
         (check_walk_refusals (access_walk_mode flags) i pathp (clear_copyins eff) m
            (check_faccessat_body (access_walk_mode flags) i dirfd pathp
               (clear_copyins eff) m))).

Lemma check_faccessat2_sound_ok :
    forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs ->
  faccessat2_spec dirfd pathp mode flags i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold check_faccessat2 in H. unfold faccessat2_spec.
  destruct (negb (modeled_access_mode mode)) eqn:Hmo; cbv iota in H.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    fa_open. apply pure_ok. }
  destruct (negb (valid_access_flags flags)) eqn:Hfl; cbv iota in H.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    fa_open. apply pure_ok. }
  destruct (negb (modeled_access_flags flags)) eqn:Hmf; cbv iota in H;
    [discriminate|].
  destruct (negb (access_mode_f_ok mode)) eqn:Hfok; cbv iota in H;
    [discriminate|].
  cbv zeta in H. fa_open.
  exact (check_getname_refusals_sound_ok pathp _ _ i m
           (check_faccessat_fetched_sound_ok (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_sound_unmodeled (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_complete_ok (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_complete_unmodeled (access_walk_mode flags) i dirfd pathp m)
           eff m' evs H).
Qed.

Lemma check_faccessat2_sound_unmodeled :
    forall i dirfd pathp mode flags eff m,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckUnmodeled ->
  faccessat2_spec dirfd pathp mode flags i m Unmodeled.
Proof.
  intros i dirfd pathp mode flags eff m H.
  unfold check_faccessat2 in H. unfold faccessat2_spec.
  destruct (negb (modeled_access_mode mode)) eqn:Hmo; cbv iota in H;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (negb (valid_access_flags flags)) eqn:Hfl; cbv iota in H;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (negb (modeled_access_flags flags)) eqn:Hmf; cbv iota in H.
  { fa_open_u. apply unmodeled_intro. }
  destruct (negb (access_mode_f_ok mode)) eqn:Hfok; cbv iota in H.
  { fa_open_u. apply unmodeled_intro. }
  cbv zeta in H. fa_open_u.
  exact (check_getname_refusals_sound_unmodeled pathp _ _ i m
           (check_faccessat_fetched_sound_ok (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_sound_unmodeled (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_complete_ok (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_complete_unmodeled (access_walk_mode flags) i dirfd pathp m)
           eff H).
Qed.

Lemma check_faccessat2_complete_ok :
    forall i dirfd pathp mode flags eff m m' evs,
  faccessat2_spec dirfd pathp mode flags i m (Ok eff m' evs) ->
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold faccessat2_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta iota in H.
  unfold check_faccessat2.
  destruct (negb (modeled_access_mode mode)) eqn:Hmo.
  { cbv iota in H. unfold err_ret, ret_only, pure in H. inversion H; subst.
    cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (negb (valid_access_flags flags)) eqn:Hfl.
  { cbv iota in H. unfold err_ret, ret_only, pure in H. inversion H; subst.
    cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (negb (modeled_access_flags flags)) eqn:Hmf; cbv iota in H;
    [fa_unmod_h|].
  destruct (negb (access_mode_f_ok mode)) eqn:Hfok; cbv iota in H;
    [fa_unmod_h|].
  cbv zeta.
  exact (check_getname_refusals_complete_ok pathp _ _ i m
           (check_faccessat_fetched_sound_ok (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_sound_unmodeled (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_complete_ok (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_complete_unmodeled (access_walk_mode flags) i dirfd pathp m)
           eff m' evs H).
Qed.

Lemma check_faccessat2_complete_unmodeled :
    forall i dirfd pathp mode flags m eff,
  faccessat2_spec dirfd pathp mode flags i m Unmodeled ->
  check_faccessat2 i dirfd pathp mode flags eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp mode flags m eff H.
  unfold faccessat2_spec in H.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply get_model_bind_unmodeled_inv in H. cbv beta iota in H.
  unfold check_faccessat2.
  destruct (negb (modeled_access_mode mode)) eqn:Hmo.
  { cbv iota in H. unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (negb (valid_access_flags flags)) eqn:Hfl.
  { cbv iota in H. unfold err_ret, ret_only, pure in H. discriminate H. }
  destruct (negb (modeled_access_flags flags)) eqn:Hmf; cbv iota in H;
    [reflexivity|].
  destruct (negb (access_mode_f_ok mode)) eqn:Hfok; cbv iota in H;
    [reflexivity|].
  cbv zeta.
  exact (check_getname_refusals_complete_unmodeled pathp _ _ i m
           (check_faccessat_fetched_sound_ok (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_sound_unmodeled (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_complete_ok (access_walk_mode flags) i dirfd pathp m)
           (check_faccessat_fetched_complete_unmodeled (access_walk_mode flags) i dirfd pathp m)
           eff H).
Qed.
