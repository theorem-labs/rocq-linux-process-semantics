(** * LinuxProcessSem.Checks.Sys.Fs.Open — the openat (56), close (57), ftruncate (46) checkers, and their proofs

    Mirrors [Sys/Fs/Open.v], which answers to Linux [fs/open.c]: this
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

(** openat's instance: the effect must be (ret = [r], no writes, no
    zeros); step to [m'] emitting [evs]. *)

Definition check_open_result : SyscallEffect -> Model -> (word -> Model)
    -> check_result :=
  check_new_fd_result openat_errnos.

(** The acceptor for [Open.create_wronly]: shared by the clobbering
    (O_TRUNC) and the exclusive (O_EXCL) write-create shapes, mirroring
    the one spec definition they share. *)

Definition check_create_wronly (p : path) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdFileW p (Z_to_bv 64 0)))
                 (with_fs (fs_set (m_fs m) p []) m)).

(** The acceptor for [Open.open_append].  Two differences from the one
    above and no others: the fd kind is [State.FdFileA], and the file
    system change is [Open.append_open_fs], which leaves an existing
    file's bytes alone. *)

Definition check_open_append (p : path) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdFileA p (Z_to_bv 64 0)))
                 (with_fs (append_open_fs (m_fs m) p) m)).

(** The acceptor for [Open.open_rdwr].  The fd kind is
    [State.FdFileRW]; the file-system change is whatever the arm
    computed, so it is a parameter here as it is there. *)

Definition check_open_rdwr (p : path) (fs' : Fs.Fs) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdFileRW p (Z_to_bv 64 0)))
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

Local Lemma check_create_wronly_sound_ok : forall i p eff m m' evs,
  check_create_wronly p eff m = CheckOk m' evs ->
  create_wronly p m i m (Ok eff m' evs).
Proof.
  intros i p [ret ws zs us cs copyins] m m' evs H.
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

Local Lemma check_open_append_sound_ok : forall i p eff m m' evs,
  check_open_append p eff m = CheckOk m' evs ->
  open_append p m i m (Ok eff m' evs).
Proof.
  intros i p [ret ws zs us cs copyins] m m' evs H.
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

Local Lemma check_open_rdwr_sound_ok : forall i p fs' eff m m' evs,
  check_open_rdwr p fs' eff m = CheckOk m' evs ->
  open_rdwr p fs' m i m (Ok eff m' evs).
Proof.
  intros i p fs' [ret ws zs us cs copyins] m m' evs H.
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

Local Definition check_openat_read (p : path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p then
      check_open_result eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m)
  else
    match fs_lookup (m_fs m) p with
    | None => check_ret_only eff (errno_ret ENOENT) m []
    | Some _ => check_open_result eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd
                               (FdFile p (Z_to_bv 64 0))) m)
    end.

Local Definition check_openat_create (p : path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EISDIR) m []
  else check_create_wronly p eff m.

Local Definition check_openat_append (p : path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EISDIR) m []
  else check_open_append p eff m.

Local Definition check_openat_rdwr (creat trunc : bool) (p : path)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EISDIR) m []
  else
    match fs_lookup (m_fs m) p with
    | None =>
        if creat then check_open_rdwr p (fs_set (m_fs m) p []) eff m
        else check_ret_only eff (errno_ret ENOENT) m []
    | Some _ =>
        check_open_rdwr p (if trunc then fs_set (m_fs m) p [] else m_fs m) eff m
    end.

Local Definition check_openat_rdwr_excl (p : path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EEXIST) m []
  else
    match fs_lookup (m_fs m) p with
    | Some _ => check_ret_only eff (errno_ret EEXIST) m []
    | None => check_open_rdwr p (fs_set (m_fs m) p []) eff m
    end.

Local Definition check_openat_excl (p : path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EEXIST) m []
  else match fs_lookup (m_fs m) p with
       | Some _ => check_ret_only eff (errno_ret EEXIST) m []
       | None => check_create_wronly p eff m
       end.

(** The only openat arm that can DECLINE: [Open.openat_dir_spec] says
    why the two path guards it takes are free here and are not available
    to the other three. *)
Local Definition check_openat_dir (p : path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p then
      check_open_result eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m)
  else if Nat.ltb NAME_MAX (length p) then CheckUnmodeled
  else if fs_under (m_fs m) p then CheckUnmodeled
  else
    match fs_lookup (m_fs m) p with
    | None => check_ret_only eff (errno_ret ENOENT) m []
    | Some _ => check_ret_only eff (errno_ret ENOTDIR) m []
    end.

(** Mirrors [Open.openat_localtime_spec]: -ENOENT for the one absolute
    path the maintainer has declared absent from the image, fail-closed
    with O_CREAT or when the image holds the key or a key under it.
    That definition carries the assumption and its scope. *)
Local Definition check_openat_localtime (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match fs_lookup (m_fs m) localtime_path with
  | Some _ => CheckUnmodeled
  | None =>
      if fs_under (m_fs m) localtime_path then CheckUnmodeled
      else if flag_set (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_CREAT
      then CheckUnmodeled
      else check_ret_only eff (errno_ret ENOENT) m []
  end.

(** Mirrors [Open.open_devnull]: the shared success shape with the
    granted access mode on the entry. *)
Local Definition check_open_devnull (rd wr : bool) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdDevNull rd wr)) m).

(** Mirrors [Open.openat_devnull_spec], word for word; that definition
    carries the assumption and the kernel path. *)
Local Definition check_openat_devnull (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match fs_lookup (m_fs m) devnull_path with
  | Some _ => CheckUnmodeled
  | None =>
      if fs_under (m_fs m) devnull_path then CheckUnmodeled
      else
      let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
      if Z.eqb fl 0 then check_open_devnull true false eff m
      else if Z.eqb fl wr_create_flags then check_open_devnull false true eff m
      else if is_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
      else if Z.eqb fl O_DIRECTORY then check_ret_only eff (errno_ret ENOTDIR) m []
      else if Z.eqb fl append_create_flags then check_open_devnull false true eff m
      else if rdwr_open_word fl then check_open_devnull true true eff m
      else if is_rdwr_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
      else CheckUnmodeled
  end.

(** Mirrors [Open.open_urandom]: the shared success shape with the
    read-only entry. *)
Local Definition check_open_urandom (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd FdUrandom) m).

(** Mirrors [Open.openat_urandom_spec], word for word; that definition
    carries the assumption, the kernel path and the declined write
    words. *)
Local Definition check_openat_urandom (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match fs_lookup (m_fs m) urandom_path with
  | Some _ => CheckUnmodeled
  | None =>
      if fs_under (m_fs m) urandom_path then CheckUnmodeled
      else
      let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
      if Z.eqb fl 0 then check_open_urandom eff m
      else if is_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
      else if Z.eqb fl O_DIRECTORY then check_ret_only eff (errno_ret ENOTDIR) m []
      else if is_rdwr_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
      else CheckUnmodeled
  end.

(** Mirrors [Open.openat_tmp_spec]; that definition carries the premise,
    the three shapes and the reason each decline is a decline. *)
Local Definition check_openat_tmp (n p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if Nat.ltb NAME_MAX (length n) then CheckUnmodeled
  else
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
  if Z.eqb fl 0 then
    (if fs_under (m_fs m) p then CheckUnmodeled
     else match fs_lookup (m_fs m) p with
          | None => CheckUnmodeled
          | Some _ => check_openat_read p eff m
          end)
  else if Z.eqb fl wr_create_flags then check_openat_create p eff m
  else CheckUnmodeled.

(** Mirrors [Open.openat_sep_spec]: the separator-bearing pathnames
    that are answered, ahead of the decline. *)
Local Definition check_openat_sep (p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if path_eqb p localtime_path then check_openat_localtime flags eff m
  else if path_eqb p devnull_path then check_openat_devnull flags eff m
  else if path_eqb p urandom_path then check_openat_urandom flags eff m
  else match tmp_name p with
       | Some n => check_openat_tmp n p flags eff m
       | None => CheckUnmodeled
       end.

(** Mirrors [Open.openat_resolved_spec]'s leading guard: a pathname
    with a separator in it is declined before any flag is looked at,
    unless [check_openat_sep] answers it.  See that definition for why,
    and for why ".." is an arm instead. *)
Local Definition check_openat_resolved (p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if path_has_slash p then check_openat_sep p flags eff m else
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
  if Z.eqb fl 0 then check_openat_read p eff m
  else if Z.eqb fl wr_create_flags then check_openat_create p eff m
  else if is_excl_create fl then check_openat_excl p eff m
  else if Z.eqb fl O_DIRECTORY then check_openat_dir p eff m
  else if Z.eqb fl append_create_flags then check_openat_append p eff m
  else if rdwr_open_word fl then
    check_openat_rdwr (flag_set fl O_CREAT) (flag_set fl O_TRUNC) p eff m
  else if is_rdwr_excl_create fl then check_openat_rdwr_excl p eff m
  else CheckUnmodeled.

Local Definition check_openat_body (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match user_read_cstr i m pathp with
    | UOk CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
    | UFault | UOk CstrFault => check_ret_only eff (errno_ret EFAULT) m []
    | USpecial => CheckUnmodeled
    | UOk (CstrOk p) =>
        if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
        else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
        else check_openat_resolved p flags eff m
  end.




(** The pathname copy-in is the prefix through the first NUL, the first
    faulting byte, or [PATH_MAX] — [State.user_cstr_access_len].  That is
    the range the model records, not the one [getname()] loads:
    [strncpy_from_user] reads a word at a time and so runs to the end of
    the word holding the NUL, up to 7 bytes further, without moving the
    errno or the return (lib/strncpy_from_user.c, [do_strncpy_from_user];
    byte-identical v6.10 through v6.16 — the FILE is not, so the window
    belongs to the function).  The open body performs no
    later copy-in, so clear the prefix while checking the result and
    require the complete claimed list to equal that one range. *)
Definition check_openat (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (modeled_open_flags flags) then CheckUnmodeled
  else
    let reads := [(pathp, user_cstr_access_len i m pathp)] in
    check_copyins_after reads eff
      (check_openat_body i dirfd pathp flags (clear_copyins eff) m).

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

Local Lemma refine_ucstr (r : UserRead cstr_result)
    (P : UserRead cstr_result -> Prop) :
  (forall p, P (UOk (CstrOk p))) -> P (UOk CstrTooLong) ->
  P (UOk CstrFault) -> P UFault -> P USpecial -> P r.
Proof.
  intros Hok Htoo_long Hcfault Hfault Hspecial.
  refine (match r as r' return P r' with
          | UOk (CstrOk p) => Hok p
          | UOk CstrTooLong => Htoo_long
          | UOk CstrFault => Hcfault
          | UFault => Hfault
          | USpecial => Hspecial
          end).
Qed.

Local Lemma check_openat_read_sound_ok : forall i p eff m m' evs,
  check_openat_read p eff m = CheckOk m' evs ->
  openat_read_spec p m i m (Ok eff m' evs).
Proof.
  intros i p eff m m' evs H.
  unfold check_openat_read, openat_read_spec in *.
  destruct (path_is_dirref p).
  - change (open_result_spec m
      (fun fd => with_fds (fd_insert (m_fds m) fd FdDir))
      i m (Ok eff m' evs)).
    now apply check_open_result_sound_ok.
  - destruct (fs_lookup (m_fs m) p).
    + change (open_result_spec m
        (fun fd => with_fds (fd_insert (m_fds m) fd
          (FdFile p (Z_to_bv 64 0)))) i m (Ok eff m' evs)).
      now apply check_open_result_sound_ok.
    + now apply check_ret_only_sound_ok.
Qed.

Local Lemma check_openat_create_sound_ok : forall i p eff m m' evs,
  check_openat_create p eff m = CheckOk m' evs ->
  openat_create_spec p m i m (Ok eff m' evs).
Proof.
  intros i p eff m m' evs H.
  unfold check_openat_create, openat_create_spec in *.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_sound_ok.
  - now apply check_create_wronly_sound_ok.
Qed.

Local Lemma check_openat_excl_sound_ok : forall i p eff m m' evs,
  check_openat_excl p eff m = CheckOk m' evs ->
  openat_excl_spec p m i m (Ok eff m' evs).
Proof.
  intros i p eff m m' evs H.
  unfold check_openat_excl, openat_excl_spec in *.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_sound_ok.
  - destruct (fs_lookup (m_fs m) p).
    + now apply check_ret_only_sound_ok.
    + now apply check_create_wronly_sound_ok.
Qed.

Local Lemma check_openat_dir_sound_ok : forall i p eff m m' evs,
  check_openat_dir p eff m = CheckOk m' evs ->
  openat_dir_spec p m i m (Ok eff m' evs).
Proof.
  intros i p eff m m' evs H.
  unfold check_openat_dir, openat_dir_spec in *.
  destruct (path_is_dirref p).
  - change (open_result_spec m
      (fun fd => with_fds (fd_insert (m_fds m) fd FdDir))
      i m (Ok eff m' evs)).
    now apply check_open_result_sound_ok.
  - destruct (Nat.ltb NAME_MAX (length p)); [discriminate|].
    destruct (fs_under (m_fs m) p); [discriminate|].
    destruct (fs_lookup (m_fs m) p); now apply check_ret_only_sound_ok.
Qed.

Local Lemma check_openat_append_sound_ok : forall i p eff m m' evs,
  check_openat_append p eff m = CheckOk m' evs ->
  openat_append_spec p m i m (Ok eff m' evs).
Proof.
  intros i p eff m m' evs H.
  unfold check_openat_append, openat_append_spec in *.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_sound_ok.
  - now apply check_open_append_sound_ok.
Qed.

Local Lemma check_openat_rdwr_sound_ok : forall i creat trunc p eff m m' evs,
  check_openat_rdwr creat trunc p eff m = CheckOk m' evs ->
  openat_rdwr_spec creat trunc p m i m (Ok eff m' evs).
Proof.
  intros i creat trunc p eff m m' evs H.
  unfold check_openat_rdwr, openat_rdwr_spec in *.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_sound_ok.
  - destruct (fs_lookup (m_fs m) p).
    + now apply check_open_rdwr_sound_ok.
    + destruct creat.
      * now apply check_open_rdwr_sound_ok.
      * now apply check_ret_only_sound_ok.
Qed.

Local Lemma check_openat_rdwr_excl_sound_ok : forall i p eff m m' evs,
  check_openat_rdwr_excl p eff m = CheckOk m' evs ->
  openat_rdwr_excl_spec p m i m (Ok eff m' evs).
Proof.
  intros i p eff m m' evs H.
  unfold check_openat_rdwr_excl, openat_rdwr_excl_spec in *.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_sound_ok.
  - destruct (fs_lookup (m_fs m) p).
    + now apply check_ret_only_sound_ok.
    + now apply check_open_rdwr_sound_ok.
Qed.

Local Lemma check_openat_localtime_sound_ok : forall i flags eff m m' evs,
  check_openat_localtime flags eff m = CheckOk m' evs ->
  openat_localtime_spec flags m i m (Ok eff m' evs).
Proof.
  intros i flags eff m m' evs H.
  unfold check_openat_localtime, openat_localtime_spec in *.
  destruct (fs_lookup (m_fs m) localtime_path); [discriminate|].
  destruct (fs_under (m_fs m) localtime_path); [discriminate|].
  destruct (flag_set (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_CREAT);
    [discriminate|].
  now apply check_ret_only_sound_ok.
Qed.

Local Lemma check_open_devnull_sound_ok : forall i rd wr eff m m' evs,
  check_open_devnull rd wr eff m = CheckOk m' evs ->
  open_devnull m rd wr i m (Ok eff m' evs).
Proof.
  intros i rd wr eff m m' evs H.
  unfold check_open_devnull, open_devnull in *.
  now apply check_open_result_sound_ok.
Qed.

Local Lemma check_openat_devnull_sound_ok : forall i flags eff m m' evs,
  check_openat_devnull flags eff m = CheckOk m' evs ->
  openat_devnull_spec flags m i m (Ok eff m' evs).
Proof.
  intros i flags eff m m' evs H.
  unfold check_openat_devnull, openat_devnull_spec in *. cbv zeta in *.
  destruct (fs_lookup (m_fs m) devnull_path); [discriminate|].
  destruct (fs_under (m_fs m) devnull_path); [discriminate|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [now apply check_open_devnull_sound_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags);
    [now apply check_open_devnull_sound_ok|].
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [now apply check_ret_only_sound_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY);
    [now apply check_ret_only_sound_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              append_create_flags);
    [now apply check_open_devnull_sound_ok|].
  destruct (rdwr_open_word (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [now apply check_open_devnull_sound_ok|].
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [now apply check_ret_only_sound_ok|].
  discriminate.
Qed.

Local Lemma check_open_urandom_sound_ok : forall i eff m m' evs,
  check_open_urandom eff m = CheckOk m' evs ->
  open_urandom m i m (Ok eff m' evs).
Proof.
  intros i eff m m' evs H.
  unfold check_open_urandom, open_urandom in *.
  now apply check_open_result_sound_ok.
Qed.

Local Lemma check_openat_urandom_sound_ok : forall i flags eff m m' evs,
  check_openat_urandom flags eff m = CheckOk m' evs ->
  openat_urandom_spec flags m i m (Ok eff m' evs).
Proof.
  intros i flags eff m m' evs H.
  unfold check_openat_urandom, openat_urandom_spec in *. cbv zeta in *.
  destruct (fs_lookup (m_fs m) urandom_path); [discriminate|].
  destruct (fs_under (m_fs m) urandom_path); [discriminate|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [now apply check_open_urandom_sound_ok|].
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [now apply check_ret_only_sound_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY);
    [now apply check_ret_only_sound_ok|].
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [now apply check_ret_only_sound_ok|].
  discriminate.
Qed.

Local Lemma check_openat_tmp_sound_ok : forall i n p flags eff m m' evs,
  check_openat_tmp n p flags eff m = CheckOk m' evs ->
  openat_tmp_spec n p flags m i m (Ok eff m' evs).
Proof.
  intros i n p flags eff m m' evs H.
  unfold check_openat_tmp, openat_tmp_spec in *. cbv zeta in *.
  destruct (Nat.ltb NAME_MAX (length n)); [discriminate|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
  { destruct (fs_under (m_fs m) p); [discriminate|].
    destruct (fs_lookup (m_fs m) p) as [data|]; [|discriminate].
    now apply check_openat_read_sound_ok. }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags); [|discriminate].
  now apply check_openat_create_sound_ok.
Qed.

Local Lemma check_openat_sep_sound_ok : forall i p flags eff m m' evs,
  check_openat_sep p flags eff m = CheckOk m' evs ->
  openat_sep_spec p flags m i m (Ok eff m' evs).
Proof.
  intros i p flags eff m m' evs H.
  unfold check_openat_sep, openat_sep_spec in *.
  destruct (path_eqb p localtime_path);
    [now apply check_openat_localtime_sound_ok|].
  destruct (path_eqb p devnull_path);
    [now apply check_openat_devnull_sound_ok|].
  destruct (path_eqb p urandom_path);
    [now apply check_openat_urandom_sound_ok|].
  destruct (tmp_name p) as [n|];
    [now apply check_openat_tmp_sound_ok|discriminate].
Qed.

Local Lemma check_openat_resolved_sound_ok : forall i p flags eff m m' evs,
  check_openat_resolved p flags (clear_copyins eff) m = CheckOk m' evs ->
  openat_resolved_spec p flags m i m (Ok (clear_copyins eff) m' evs).
Proof.
  intros i p flags eff m m' evs H.
  unfold check_openat_resolved, openat_resolved_spec in *.
  destruct (path_has_slash p); [now apply check_openat_sep_sound_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
  - now apply check_openat_read_sound_ok.
  - destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
      wr_create_flags).
    + now apply check_openat_create_sound_ok.
    + destruct (is_excl_create
        (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
      * now apply check_openat_excl_sound_ok.
      * destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
          O_DIRECTORY).
        -- now apply check_openat_dir_sound_ok.
        -- destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
               append_create_flags).
           ++ now apply check_openat_append_sound_ok.
           ++ destruct (rdwr_open_word
                  (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
              ** now apply check_openat_rdwr_sound_ok.
              ** destruct (is_rdwr_excl_create
                     (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
                 --- now apply check_openat_rdwr_excl_sound_ok.
                 --- discriminate.
Qed.

Local Lemma check_openat_body_spec_sound_ok :
  forall i dirfd pathp flags eff m m' evs,
  check_openat_body i dirfd pathp flags (clear_copyins eff) m = CheckOk m' evs ->
  openat_body_spec i m dirfd pathp flags i m
    (Ok (clear_copyins eff) m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_openat_body, openat_body_spec in H |- *.
  destruct (user_read_cstr i m pathp) as [[p| |]| |].
  - destruct (path_eqb p []).
    + now apply check_ret_only_sound_ok.
    + destruct (negb (bv_eqb dirfd AT_FDCWD32)); [discriminate|].
      now apply check_openat_resolved_sound_ok.
  - now apply check_ret_only_sound_ok.
  - now apply check_ret_only_sound_ok.
  - now apply check_ret_only_sound_ok.
  - discriminate.
Qed.

Local Lemma check_openat_body_sound_ok : forall i dirfd pathp flags eff m m' evs,
  negb (modeled_open_flags flags) = false ->
  check_openat_body i dirfd pathp flags (clear_copyins eff) m = CheckOk m' evs ->
  openat_core_spec dirfd pathp flags i m (Ok (clear_copyins eff) m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs Hfl H.
  unfold openat_core_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
  rewrite Hfl. cbv iota.
  now apply check_openat_body_spec_sound_ok.
Qed.


Lemma check_openat_sound_ok : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs ->
  openat_spec dirfd pathp flags i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_openat in H.
  destruct (negb (modeled_open_flags flags)) eqn:Hfl; [discriminate|].
  cbv iota in H.
  apply check_copyins_after_ok_iff in H.
  destruct H as (Hreads & Hchecked).
  pose proof (check_openat_body_sound_ok i dirfd pathp flags eff
    m m' evs Hfl Hchecked) as Hcore.
  unfold openat_spec. eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  now apply record_copyins_clear_ok.
Qed.

Local Lemma check_open_result_no_unmodeled : forall eff m mk,
  check_open_result eff m mk <> CheckUnmodeled.
Proof. intros eff m mk. apply check_new_fd_result_no_unmodeled. Qed.

Local Lemma check_openat_read_no_unmodeled : forall p eff m,
  check_openat_read p eff m <> CheckUnmodeled.
Proof.
  intros p eff m H. unfold check_openat_read in H.
  destruct (path_is_dirref p).
  - now apply check_open_result_no_unmodeled in H.
  - destruct (fs_lookup (m_fs m) p).
    + now apply check_open_result_no_unmodeled in H.
    + now apply check_ret_only_no_unmodeled in H.
Qed.

Local Lemma check_openat_create_no_unmodeled : forall p eff m,
  check_openat_create p eff m <> CheckUnmodeled.
Proof.
  intros p eff m H. unfold check_openat_create in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_no_unmodeled in H.
  - unfold check_create_wronly in H.
    now apply check_open_result_no_unmodeled in H.
Qed.

Local Lemma check_openat_excl_no_unmodeled : forall p eff m,
  check_openat_excl p eff m <> CheckUnmodeled.
Proof.
  intros p eff m H. unfold check_openat_excl in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (fs_lookup (m_fs m) p).
    + now apply check_ret_only_no_unmodeled in H.
    + unfold check_create_wronly in H.
      now apply check_open_result_no_unmodeled in H.
Qed.

(** Unlike its three neighbours this checker CAN decline, so the
    dispatcher's unmodeled-soundness proof gets a lemma here rather than
    an [exfalso]. *)
Local Lemma check_openat_dir_sound_unmodeled : forall i p eff m,
  check_openat_dir p eff m = CheckUnmodeled ->
  openat_dir_spec p m i m Unmodeled.
Proof.
  intros i p eff m H.
  unfold check_openat_dir, openat_dir_spec in *.
  destruct (path_is_dirref p).
  - exfalso. now apply check_open_result_no_unmodeled in H.
  - destruct (Nat.ltb NAME_MAX (length p)); [apply unmodeled_intro|].
    destruct (fs_under (m_fs m) p); [apply unmodeled_intro|].
    destruct (fs_lookup (m_fs m) p); exfalso;
      now apply check_ret_only_no_unmodeled in H.
Qed.

Local Lemma check_openat_append_no_unmodeled : forall p eff m,
  check_openat_append p eff m <> CheckUnmodeled.
Proof.
  intros p eff m H. unfold check_openat_append in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_no_unmodeled in H.
  - unfold check_open_append in H.
    now apply check_open_result_no_unmodeled in H.
Qed.

Local Lemma check_open_rdwr_no_unmodeled : forall p fs' eff m,
  check_open_rdwr p fs' eff m <> CheckUnmodeled.
Proof.
  intros p fs' eff m H. unfold check_open_rdwr in H.
  now apply check_open_result_no_unmodeled in H.
Qed.

Local Lemma check_openat_rdwr_no_unmodeled : forall creat trunc p eff m,
  check_openat_rdwr creat trunc p eff m <> CheckUnmodeled.
Proof.
  intros creat trunc p eff m H. unfold check_openat_rdwr in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (fs_lookup (m_fs m) p).
    + now apply check_open_rdwr_no_unmodeled in H.
    + destruct creat.
      * now apply check_open_rdwr_no_unmodeled in H.
      * now apply check_ret_only_no_unmodeled in H.
Qed.

Local Lemma check_openat_rdwr_excl_no_unmodeled : forall p eff m,
  check_openat_rdwr_excl p eff m <> CheckUnmodeled.
Proof.
  intros p eff m H. unfold check_openat_rdwr_excl in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - now apply check_ret_only_no_unmodeled in H.
  - destruct (fs_lookup (m_fs m) p).
    + now apply check_ret_only_no_unmodeled in H.
    + now apply check_open_rdwr_no_unmodeled in H.
Qed.

Local Lemma check_openat_localtime_sound_unmodeled : forall i flags eff m,
  check_openat_localtime flags eff m = CheckUnmodeled ->
  openat_localtime_spec flags m i m Unmodeled.
Proof.
  intros i flags eff m H.
  unfold check_openat_localtime, openat_localtime_spec in *.
  destruct (fs_lookup (m_fs m) localtime_path); [apply unmodeled_intro|].
  destruct (fs_under (m_fs m) localtime_path); [apply unmodeled_intro|].
  destruct (flag_set (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_CREAT);
    [apply unmodeled_intro|].
  exfalso. now apply check_ret_only_no_unmodeled in H.
Qed.

Local Lemma check_openat_devnull_sound_unmodeled : forall i flags eff m,
  check_openat_devnull flags eff m = CheckUnmodeled ->
  openat_devnull_spec flags m i m Unmodeled.
Proof.
  intros i flags eff m H.
  unfold check_openat_devnull, openat_devnull_spec, check_open_devnull in *.
  cbv zeta in *.
  destruct (fs_lookup (m_fs m) devnull_path); [apply unmodeled_intro|].
  destruct (fs_under (m_fs m) devnull_path); [apply unmodeled_intro|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [exfalso; now apply check_open_result_no_unmodeled in H|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags);
    [exfalso; now apply check_open_result_no_unmodeled in H|].
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [exfalso; now apply check_ret_only_no_unmodeled in H|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY);
    [exfalso; now apply check_ret_only_no_unmodeled in H|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              append_create_flags);
    [exfalso; now apply check_open_result_no_unmodeled in H|].
  destruct (rdwr_open_word (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [exfalso; now apply check_open_result_no_unmodeled in H|].
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [exfalso; now apply check_ret_only_no_unmodeled in H|].
  apply unmodeled_intro.
Qed.

Local Lemma check_openat_urandom_sound_unmodeled : forall i flags eff m,
  check_openat_urandom flags eff m = CheckUnmodeled ->
  openat_urandom_spec flags m i m Unmodeled.
Proof.
  intros i flags eff m H.
  unfold check_openat_urandom, openat_urandom_spec, check_open_urandom in *.
  cbv zeta in *.
  destruct (fs_lookup (m_fs m) urandom_path); [apply unmodeled_intro|].
  destruct (fs_under (m_fs m) urandom_path); [apply unmodeled_intro|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [exfalso; now apply check_open_result_no_unmodeled in H|].
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [exfalso; now apply check_ret_only_no_unmodeled in H|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY);
    [exfalso; now apply check_ret_only_no_unmodeled in H|].
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [exfalso; now apply check_ret_only_no_unmodeled in H|].
  apply unmodeled_intro.
Qed.

Local Lemma check_openat_tmp_sound_unmodeled : forall i n p flags eff m,
  check_openat_tmp n p flags eff m = CheckUnmodeled ->
  openat_tmp_spec n p flags m i m Unmodeled.
Proof.
  intros i n p flags eff m H.
  unfold check_openat_tmp, openat_tmp_spec in *. cbv zeta in *.
  destruct (Nat.ltb NAME_MAX (length n)); [apply unmodeled_intro|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
  { destruct (fs_under (m_fs m) p); [apply unmodeled_intro|].
    destruct (fs_lookup (m_fs m) p) as [data|]; [|apply unmodeled_intro].
    exfalso. now apply check_openat_read_no_unmodeled in H. }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags); [|apply unmodeled_intro].
  exfalso. now apply check_openat_create_no_unmodeled in H.
Qed.

Local Lemma check_openat_sep_sound_unmodeled : forall i p flags eff m,
  check_openat_sep p flags eff m = CheckUnmodeled ->
  openat_sep_spec p flags m i m Unmodeled.
Proof.
  intros i p flags eff m H.
  unfold check_openat_sep, openat_sep_spec in *.
  destruct (path_eqb p localtime_path);
    [exact (check_openat_localtime_sound_unmodeled i flags eff m H)|].
  destruct (path_eqb p devnull_path);
    [exact (check_openat_devnull_sound_unmodeled i flags eff m H)|].
  destruct (path_eqb p urandom_path);
    [exact (check_openat_urandom_sound_unmodeled i flags eff m H)|].
  destruct (tmp_name p) as [n|];
    [exact (check_openat_tmp_sound_unmodeled i n p flags eff m H)
    |apply unmodeled_intro].
Qed.

Local Lemma check_openat_resolved_sound_unmodeled : forall i p flags eff m,
  check_openat_resolved p flags eff m = CheckUnmodeled ->
  openat_resolved_spec p flags m i m Unmodeled.
Proof.
  intros i p flags eff m H.
  unfold check_openat_resolved, openat_resolved_spec in *.
  destruct (path_has_slash p);
    [exact (check_openat_sep_sound_unmodeled i p flags eff m H)|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
  - exfalso. now apply check_openat_read_no_unmodeled in H.
  - destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
      wr_create_flags).
    + exfalso. now apply check_openat_create_no_unmodeled in H.
    + destruct (is_excl_create
        (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
      * exfalso. now apply check_openat_excl_no_unmodeled in H.
      * destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
          O_DIRECTORY).
        -- exact (check_openat_dir_sound_unmodeled i p eff m H).
        -- destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
               append_create_flags).
           ++ exfalso. now apply check_openat_append_no_unmodeled in H.
           ++ destruct (rdwr_open_word
                  (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
              ** exfalso. now apply check_openat_rdwr_no_unmodeled in H.
              ** destruct (is_rdwr_excl_create
                     (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
                 --- exfalso. now apply check_openat_rdwr_excl_no_unmodeled in H.
                 --- apply unmodeled_intro.
Qed.

Local Lemma check_openat_body_spec_sound_unmodeled :
  forall i dirfd pathp flags eff m,
  check_openat_body i dirfd pathp flags eff m = CheckUnmodeled ->
  openat_body_spec i m dirfd pathp flags i m Unmodeled.
Proof.
  intros i dirfd pathp flags eff m H.
  unfold check_openat_body, openat_body_spec in *.
  destruct (user_read_cstr i m pathp) as [[p| |]| |].
  - destruct (path_eqb p []).
    + exfalso. now apply check_ret_only_no_unmodeled in H.
    + destruct (negb (bv_eqb dirfd AT_FDCWD32)).
      * apply unmodeled_intro.
      * exact (check_openat_resolved_sound_unmodeled i p flags eff m H).
  - exfalso. now apply check_ret_only_no_unmodeled in H.
  - exfalso. now apply check_ret_only_no_unmodeled in H.
  - exfalso. now apply check_ret_only_no_unmodeled in H.
  - apply unmodeled_intro.
Qed.

Local Lemma check_openat_body_sound_unmodeled :
  forall i dirfd pathp flags eff m,
  negb (modeled_open_flags flags) = false ->
  check_openat_body i dirfd pathp flags eff m = CheckUnmodeled ->
  openat_core_spec dirfd pathp flags i m Unmodeled.
Proof.
  intros i dirfd pathp flags eff m Hfl H.
  unfold openat_core_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
  rewrite Hfl. cbv iota.
  exact (check_openat_body_spec_sound_unmodeled
    i dirfd pathp flags eff m H).
Qed.

Lemma check_openat_sound_unmodeled : forall i dirfd pathp flags eff m,
  check_openat i dirfd pathp flags eff m = CheckUnmodeled ->
  openat_spec dirfd pathp flags i m Unmodeled.
Proof.
  intros i dirfd pathp flags eff m H.
  unfold check_openat in H.
  destruct (negb (modeled_open_flags flags)) eqn:Hfl.
  - unfold openat_spec. eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
    apply record_copyins_unmodeled. unfold openat_core_spec.
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    rewrite Hfl. apply unmodeled_intro.
  - cbv iota in H. apply check_copyins_after_unmodeled in H.
    unfold openat_spec. eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
    apply record_copyins_unmodeled.
    exact (check_openat_body_sound_unmodeled i dirfd pathp flags
      (clear_copyins eff) m Hfl H).
Qed.

Local Definition completes_ok (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : list event)
    (spec : Sys SyscallEffect) (check : check_result) : Prop :=
  spec i m (Ok eff m' evs) ->
  check = CheckOk m' evs /\ eff_copyins eff = [].

Local Lemma check_ret_only_complete_ok : forall i eff r m m' evs,
  ret_only r i m (Ok eff m' evs) ->
  check_ret_only eff r m [] = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i eff r m m' evs H.
  unfold ret_only, pure in H. inversion H; clear H; subst.
  split; [cbn; rewrite bv_eqb_refl; reflexivity|reflexivity].
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

Local Lemma check_create_wronly_complete_ok : forall i p eff m m' evs,
  create_wronly p m i m (Ok eff m' evs) ->
  check_create_wronly p eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p eff m m' evs H.
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

Local Lemma check_open_append_complete_ok : forall i p eff m m' evs,
  open_append p m i m (Ok eff m' evs) ->
  check_open_append p eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p eff m m' evs H.
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

Local Lemma check_open_rdwr_complete_ok : forall i p fs' eff m m' evs,
  open_rdwr p fs' m i m (Ok eff m' evs) ->
  check_open_rdwr p fs' eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p fs' eff m m' evs H.
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

Local Lemma check_openat_read_complete_ok : forall i p eff m m' evs,
  openat_read_spec p m i m (Ok eff m' evs) ->
  check_openat_read p eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p eff m m' evs.
  unfold openat_read_spec, check_openat_read.
  refine (refine_if (path_is_dirref p)
    (fun b => completes_ok i m eff m' evs
      (if b then
         alt (e <- errno_from openat_errnos ;; err_ret e)
             (fd <- lowest_fd (m_fds m) ;;
              set_fds (fd_insert (m_fds m) fd FdDir) ;;
              ret_only fd)
       else match fs_lookup (m_fs m) p with
            | None => err_ret ENOENT
            | Some _ =>
                alt (e <- errno_from openat_errnos ;; err_ret e)
                    (fd <- lowest_fd (m_fds m) ;;
                     set_fds (fd_insert (m_fds m) fd
                       (FdFile p (Z_to_bv 64 0))) ;;
                     ret_only fd)
            end)
      (if b then check_open_result eff m
         (fun fd => with_fds (fd_insert (m_fds m) fd FdDir) m)
       else match fs_lookup (m_fs m) p with
            | None => check_ret_only eff (errno_ret ENOENT) m []
            | Some _ => check_open_result eff m
                (fun fd => with_fds (fd_insert (m_fds m) fd
                  (FdFile p (Z_to_bv 64 0))) m)
            end)) _ _).
  - unfold completes_ok.
    apply check_open_result_complete_ok.
  - refine (refine_option (fs_lookup (m_fs m) p)
      (fun o => completes_ok i m eff m' evs
        (match o with
         | Some _ => alt (e <- errno_from openat_errnos ;; err_ret e)
             (fd <- lowest_fd (m_fds m) ;;
              set_fds (fd_insert (m_fds m) fd
                (FdFile p (Z_to_bv 64 0))) ;;
              ret_only fd)
         | None => err_ret ENOENT
         end)
        (match o with
         | Some _ => check_open_result eff m
             (fun fd => with_fds (fd_insert (m_fds m) fd
               (FdFile p (Z_to_bv 64 0))) m)
         | None => check_ret_only eff (errno_ret ENOENT) m []
         end)) _ _).
    + intro data. unfold completes_ok.
      apply check_open_result_complete_ok.
    + unfold completes_ok. apply check_ret_only_complete_ok.
Qed.

Local Lemma check_openat_create_complete_ok : forall i p eff m m' evs,
  openat_create_spec p m i m (Ok eff m' evs) ->
  check_openat_create p eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p eff m m' evs.
  unfold openat_create_spec, check_openat_create.
  refine (refine_if (path_is_dirref p || fs_under (m_fs m) p)
    (fun b => completes_ok i m eff m' evs
      (if b then err_ret EISDIR else create_wronly p m)
      (if b then check_ret_only eff (errno_ret EISDIR) m []
       else check_create_wronly p eff m)) _ _).
  - unfold completes_ok. apply check_ret_only_complete_ok.
  - unfold completes_ok. apply check_create_wronly_complete_ok.
Qed.

Local Lemma check_openat_excl_complete_ok : forall i p eff m m' evs,
  openat_excl_spec p m i m (Ok eff m' evs) ->
  check_openat_excl p eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p eff m m' evs.
  unfold openat_excl_spec, check_openat_excl.
  refine (refine_if (path_is_dirref p || fs_under (m_fs m) p)
    (fun b => completes_ok i m eff m' evs
      (if b then err_ret EEXIST
       else match fs_lookup (m_fs m) p with
            | Some _ => err_ret EEXIST | None => create_wronly p m end)
      (if b then check_ret_only eff (errno_ret EEXIST) m []
       else match fs_lookup (m_fs m) p with
            | Some _ => check_ret_only eff (errno_ret EEXIST) m []
            | None => check_create_wronly p eff m end)) _ _).
  - unfold completes_ok. apply check_ret_only_complete_ok.
  - refine (refine_option (fs_lookup (m_fs m) p)
      (fun o => completes_ok i m eff m' evs
        (match o with Some _ => err_ret EEXIST | None => create_wronly p m end)
        (match o with
         | Some _ => check_ret_only eff (errno_ret EEXIST) m []
         | None => check_create_wronly p eff m
         end)) _ _).
    + intro data. unfold completes_ok. apply check_ret_only_complete_ok.
    + unfold completes_ok. apply check_create_wronly_complete_ok.
Qed.

Local Lemma check_openat_dir_complete_ok : forall i p eff m m' evs,
  openat_dir_spec p m i m (Ok eff m' evs) ->
  check_openat_dir p eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p eff m m' evs.
  unfold openat_dir_spec, check_openat_dir.
  destruct (path_is_dirref p).
  - apply check_open_result_complete_ok.
  - destruct (Nat.ltb NAME_MAX (length p));
      [unfold unmodeled; intro Hu; discriminate Hu|].
    destruct (fs_under (m_fs m) p);
      [unfold unmodeled; intro Hu; discriminate Hu|].
    destruct (fs_lookup (m_fs m) p); apply check_ret_only_complete_ok.
Qed.

Local Lemma check_openat_append_complete_ok : forall i p eff m m' evs,
  openat_append_spec p m i m (Ok eff m' evs) ->
  check_openat_append p eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p eff m m' evs.
  unfold openat_append_spec, check_openat_append.
  refine (refine_if (path_is_dirref p || fs_under (m_fs m) p)
    (fun b => completes_ok i m eff m' evs
      (if b then err_ret EISDIR else open_append p m)
      (if b then check_ret_only eff (errno_ret EISDIR) m []
       else check_open_append p eff m)) _ _).
  - unfold completes_ok. apply check_ret_only_complete_ok.
  - unfold completes_ok. apply check_open_append_complete_ok.
Qed.

Local Lemma check_openat_rdwr_complete_ok : forall i creat trunc p eff m m' evs,
  openat_rdwr_spec creat trunc p m i m (Ok eff m' evs) ->
  check_openat_rdwr creat trunc p eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i creat trunc p eff m m' evs.
  unfold openat_rdwr_spec, check_openat_rdwr.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - apply check_ret_only_complete_ok.
  - destruct (fs_lookup (m_fs m) p).
    + apply check_open_rdwr_complete_ok.
    + destruct creat.
      * apply check_open_rdwr_complete_ok.
      * apply check_ret_only_complete_ok.
Qed.

Local Lemma check_openat_rdwr_excl_complete_ok : forall i p eff m m' evs,
  openat_rdwr_excl_spec p m i m (Ok eff m' evs) ->
  check_openat_rdwr_excl p eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p eff m m' evs.
  unfold openat_rdwr_excl_spec, check_openat_rdwr_excl.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - apply check_ret_only_complete_ok.
  - destruct (fs_lookup (m_fs m) p).
    + apply check_ret_only_complete_ok.
    + apply check_open_rdwr_complete_ok.
Qed.

Local Lemma check_openat_localtime_complete_ok : forall i flags eff m m' evs,
  openat_localtime_spec flags m i m (Ok eff m' evs) ->
  check_openat_localtime flags eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i flags eff m m' evs.
  unfold openat_localtime_spec, check_openat_localtime.
  destruct (fs_lookup (m_fs m) localtime_path);
    [unfold unmodeled; intro Hu; discriminate Hu|].
  destruct (fs_under (m_fs m) localtime_path);
    [unfold unmodeled; intro Hu; discriminate Hu|].
  destruct (flag_set (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_CREAT);
    [unfold unmodeled; intro Hu; discriminate Hu|].
  apply check_ret_only_complete_ok.
Qed.

Local Lemma check_open_devnull_complete_ok : forall i rd wr eff m m' evs,
  open_devnull m rd wr i m (Ok eff m' evs) ->
  check_open_devnull rd wr eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i rd wr eff m m' evs.
  unfold open_devnull, check_open_devnull.
  apply check_open_result_complete_ok.
Qed.

Local Lemma check_openat_devnull_complete_ok : forall i flags eff m m' evs,
  openat_devnull_spec flags m i m (Ok eff m' evs) ->
  check_openat_devnull flags eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i flags eff m m' evs.
  unfold openat_devnull_spec, check_openat_devnull. cbv zeta.
  destruct (fs_lookup (m_fs m) devnull_path);
    [unfold unmodeled; intro Hu; discriminate Hu|].
  destruct (fs_under (m_fs m) devnull_path);
    [unfold unmodeled; intro Hu; discriminate Hu|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [apply check_open_devnull_complete_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags);
    [apply check_open_devnull_complete_ok|].
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [apply check_ret_only_complete_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY);
    [apply check_ret_only_complete_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              append_create_flags);
    [apply check_open_devnull_complete_ok|].
  destruct (rdwr_open_word (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [apply check_open_devnull_complete_ok|].
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [apply check_ret_only_complete_ok|].
  unfold unmodeled. intro Hu. discriminate Hu.
Qed.

Local Lemma check_open_urandom_complete_ok : forall i eff m m' evs,
  open_urandom m i m (Ok eff m' evs) ->
  check_open_urandom eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i eff m m' evs.
  unfold open_urandom, check_open_urandom.
  apply check_open_result_complete_ok.
Qed.

Local Lemma check_openat_urandom_complete_ok : forall i flags eff m m' evs,
  openat_urandom_spec flags m i m (Ok eff m' evs) ->
  check_openat_urandom flags eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i flags eff m m' evs.
  unfold openat_urandom_spec, check_openat_urandom. cbv zeta.
  destruct (fs_lookup (m_fs m) urandom_path);
    [unfold unmodeled; intro Hu; discriminate Hu|].
  destruct (fs_under (m_fs m) urandom_path);
    [unfold unmodeled; intro Hu; discriminate Hu|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [apply check_open_urandom_complete_ok|].
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [apply check_ret_only_complete_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY);
    [apply check_ret_only_complete_ok|].
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [apply check_ret_only_complete_ok|].
  unfold unmodeled. intro Hu. discriminate Hu.
Qed.

Local Lemma check_openat_tmp_complete_ok : forall i n p flags eff m m' evs,
  openat_tmp_spec n p flags m i m (Ok eff m' evs) ->
  check_openat_tmp n p flags eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i n p flags eff m m' evs.
  unfold openat_tmp_spec, check_openat_tmp. cbv zeta.
  destruct (Nat.ltb NAME_MAX (length n));
    [unfold unmodeled; intro Hu; discriminate Hu|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
  { destruct (fs_under (m_fs m) p);
      [unfold unmodeled; intro Hu; discriminate Hu|].
    destruct (fs_lookup (m_fs m) p) as [data|];
      [apply check_openat_read_complete_ok
      |unfold unmodeled; intro Hu; discriminate Hu]. }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags);
    [apply check_openat_create_complete_ok
    |unfold unmodeled; intro Hu; discriminate Hu].
Qed.

Local Lemma check_openat_sep_complete_ok : forall i p flags eff m m' evs,
  openat_sep_spec p flags m i m (Ok eff m' evs) ->
  check_openat_sep p flags eff m = CheckOk m' evs /\ eff_copyins eff = [].
Proof.
  intros i p flags eff m m' evs.
  unfold openat_sep_spec, check_openat_sep.
  destruct (path_eqb p localtime_path);
    [apply check_openat_localtime_complete_ok|].
  destruct (path_eqb p devnull_path);
    [apply check_openat_devnull_complete_ok|].
  destruct (path_eqb p urandom_path);
    [apply check_openat_urandom_complete_ok|].
  destruct (tmp_name p) as [n|];
    [apply check_openat_tmp_complete_ok
    |unfold unmodeled; intro Hu; discriminate Hu].
Qed.

Local Lemma check_openat_resolved_complete_ok : forall i p flags eff m m' evs,
  openat_resolved_spec p flags m i m (Ok eff m' evs) ->
  check_openat_resolved p flags eff m = CheckOk m' evs /\
  eff_copyins eff = [].
Proof.
  intros i p flags eff m m' evs.
  unfold openat_resolved_spec, check_openat_resolved. cbv zeta.
  destruct (path_has_slash p); [apply check_openat_sep_complete_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [apply check_openat_read_complete_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags);
    [apply check_openat_create_complete_ok|].
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [apply check_openat_excl_complete_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY);
    [apply check_openat_dir_complete_ok|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              append_create_flags);
    [apply check_openat_append_complete_ok|].
  destruct (rdwr_open_word (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [apply check_openat_rdwr_complete_ok|].
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [apply check_openat_rdwr_excl_complete_ok|].
  unfold unmodeled. intros H. discriminate H.
Qed.

Local Lemma check_openat_body_complete_ok : forall i dirfd pathp flags eff m m' evs,
  openat_body_spec i m dirfd pathp flags i m (Ok eff m' evs) ->
  check_openat_body i dirfd pathp flags eff m = CheckOk m' evs /\
  eff_copyins eff = [].
Proof.
  intros i dirfd pathp flags eff m m' evs.
  unfold openat_body_spec, check_openat_body.
  refine (refine_ucstr (user_read_cstr i m pathp)
    (fun r => completes_ok i m eff m' evs
      (match r with
       | UOk CstrTooLong => err_ret ENAMETOOLONG
       | UFault | UOk CstrFault => err_ret EFAULT
       | USpecial => unmodeled
       | UOk (CstrOk p) =>
           if path_eqb p [] then err_ret ENOENT
           else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
           else openat_resolved_spec p flags m
       end)
      (match r with
       | UOk CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
       | UFault | UOk CstrFault => check_ret_only eff (errno_ret EFAULT) m []
       | USpecial => CheckUnmodeled
       | UOk (CstrOk p) =>
           if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
           else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
           else check_openat_resolved p flags eff m
       end)) _ _ _ _ _).
  - intro p.
    refine (refine_if (path_eqb p [])
      (fun b => completes_ok i m eff m' evs
        (if b then err_ret ENOENT
         else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
         else openat_resolved_spec p flags m)
        (if b then check_ret_only eff (errno_ret ENOENT) m []
         else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
         else check_openat_resolved p flags eff m)) _ _).
    + unfold completes_ok. apply check_ret_only_complete_ok.
    + refine (refine_if (negb (bv_eqb dirfd AT_FDCWD32))
        (fun b => completes_ok i m eff m' evs
          (if b then unmodeled else openat_resolved_spec p flags m)
          (if b then CheckUnmodeled else check_openat_resolved p flags eff m))
        _ _).
      * unfold completes_ok, unmodeled. intros H. discriminate H.
      * unfold completes_ok. apply check_openat_resolved_complete_ok.
  - unfold completes_ok. apply check_ret_only_complete_ok.
  - unfold completes_ok. apply check_ret_only_complete_ok.
  - unfold completes_ok. apply check_ret_only_complete_ok.
  - unfold completes_ok, unmodeled. intros H. discriminate H.
Qed.



Local Lemma openat_core_ok_inv : forall i dirfd pathp flags eff m m' evs,
  openat_core_spec dirfd pathp flags i m (Ok eff m' evs) ->
  negb (modeled_open_flags flags) = false /\
  openat_body_spec i m dirfd pathp flags i m (Ok eff m' evs).
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

Lemma check_openat_complete_ok : forall i dirfd pathp flags eff m m' evs,
  openat_spec dirfd pathp flags i m (Ok eff m' evs) ->
  check_openat i dirfd pathp flags eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold openat_spec in H.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta in H.
  apply record_copyins_ok_inv in H.
  destruct H as (core & Hcore & ->).
  apply openat_core_ok_inv in Hcore.
  destruct Hcore as (Hflags & Hbody).
  apply check_openat_body_complete_ok in Hbody.
  destruct Hbody as (Hchecked & Hcopyins).
  unfold check_openat. rewrite Hflags. cbv iota.
  apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
  - cbn [with_copyins eff_copyins]. rewrite Hcopyins, app_nil_r. reflexivity.
  - destruct core as [ret ws zs us cs copyins].
    cbn in Hcopyins. subst copyins.
    exact Hchecked.
Qed.

Local Definition completes_unmodeled (i : SyscallInput) (m : Model)
    (spec : Sys SyscallEffect) (check : check_result) : Prop :=
  spec i m Unmodeled -> check = CheckUnmodeled.

Local Lemma ret_only_no_unmodeled : forall r i m,
  ~ ret_only r i m Unmodeled.
Proof. intros r i m H. unfold ret_only, pure in H. discriminate H. Qed.

Local Lemma open_result_spec_no_unmodeled : forall m mk i,
  ~ open_result_spec m mk i m Unmodeled.
Proof.
  intros m mk i H. unfold open_result_spec in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

Local Lemma create_wronly_no_unmodeled : forall p m i,
  ~ create_wronly p m i m Unmodeled.
Proof.
  intros p m i H. unfold create_wronly in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

Local Lemma openat_read_spec_no_unmodeled : forall p m i,
  ~ openat_read_spec p m i m Unmodeled.
Proof.
  intros p m i H. unfold openat_read_spec in H.
  destruct (path_is_dirref p).
  - exact (open_result_spec_no_unmodeled m
      (fun fd => with_fds (fd_insert (m_fds m) fd FdDir)) i H).
  - destruct (fs_lookup (m_fs m) p).
    + exact (open_result_spec_no_unmodeled m
        (fun fd => with_fds (fd_insert (m_fds m) fd
          (FdFile p (Z_to_bv 64 0)))) i H).
    + exact (ret_only_no_unmodeled (errno_ret ENOENT) i m H).
Qed.

Local Lemma openat_create_spec_no_unmodeled : forall p m i,
  ~ openat_create_spec p m i m Unmodeled.
Proof.
  intros p m i H. unfold openat_create_spec in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - exact (ret_only_no_unmodeled (errno_ret EISDIR) i m H).
  - exact (create_wronly_no_unmodeled p m i H).
Qed.

Local Lemma openat_excl_spec_no_unmodeled : forall p m i,
  ~ openat_excl_spec p m i m Unmodeled.
Proof.
  intros p m i H. unfold openat_excl_spec in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - exact (ret_only_no_unmodeled (errno_ret EEXIST) i m H).
  - destruct (fs_lookup (m_fs m) p).
    + exact (ret_only_no_unmodeled (errno_ret EEXIST) i m H).
    + exact (create_wronly_no_unmodeled p m i H).
Qed.

Local Lemma check_openat_dir_complete_unmodeled : forall i p eff m,
  openat_dir_spec p m i m Unmodeled ->
  check_openat_dir p eff m = CheckUnmodeled.
Proof.
  intros i p eff m.
  unfold openat_dir_spec, check_openat_dir.
  destruct (path_is_dirref p).
  - intro H. exfalso.
    exact (open_result_spec_no_unmodeled m
      (fun fd => with_fds (fd_insert (m_fds m) fd FdDir)) i H).
  - destruct (Nat.ltb NAME_MAX (length p)); [reflexivity|].
    destruct (fs_under (m_fs m) p); [reflexivity|].
    destruct (fs_lookup (m_fs m) p); intro H; exfalso;
      [exact (ret_only_no_unmodeled (errno_ret ENOTDIR) i m H)
      |exact (ret_only_no_unmodeled (errno_ret ENOENT) i m H)].
Qed.

Local Lemma open_append_no_unmodeled : forall p m i,
  ~ open_append p m i m Unmodeled.
Proof.
  intros p m i H. unfold open_append in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

Local Lemma openat_append_spec_no_unmodeled : forall p m i,
  ~ openat_append_spec p m i m Unmodeled.
Proof.
  intros p m i H. unfold openat_append_spec in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - exact (ret_only_no_unmodeled (errno_ret EISDIR) i m H).
  - exact (open_append_no_unmodeled p m i H).
Qed.

Local Lemma open_rdwr_no_unmodeled : forall p fs' m i,
  ~ open_rdwr p fs' m i m Unmodeled.
Proof.
  intros p fs' m i H. unfold open_rdwr in H. sys_unfold.
  cbv iota in H. inv_ok.
Qed.

Local Lemma openat_rdwr_spec_no_unmodeled : forall creat trunc p m i,
  ~ openat_rdwr_spec creat trunc p m i m Unmodeled.
Proof.
  intros creat trunc p m i H. unfold openat_rdwr_spec in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - exact (ret_only_no_unmodeled (errno_ret EISDIR) i m H).
  - destruct (fs_lookup (m_fs m) p).
    + exact (open_rdwr_no_unmodeled p _ m i H).
    + destruct creat.
      * exact (open_rdwr_no_unmodeled p _ m i H).
      * exact (ret_only_no_unmodeled (errno_ret ENOENT) i m H).
Qed.

Local Lemma openat_rdwr_excl_spec_no_unmodeled : forall p m i,
  ~ openat_rdwr_excl_spec p m i m Unmodeled.
Proof.
  intros p m i H. unfold openat_rdwr_excl_spec in H.
  destruct (path_is_dirref p || fs_under (m_fs m) p).
  - exact (ret_only_no_unmodeled (errno_ret EEXIST) i m H).
  - destruct (fs_lookup (m_fs m) p).
    + exact (ret_only_no_unmodeled (errno_ret EEXIST) i m H).
    + exact (open_rdwr_no_unmodeled p _ m i H).
Qed.

Local Lemma check_openat_localtime_complete_unmodeled : forall i flags eff m,
  openat_localtime_spec flags m i m Unmodeled ->
  check_openat_localtime flags eff m = CheckUnmodeled.
Proof.
  intros i flags eff m.
  unfold openat_localtime_spec, check_openat_localtime.
  destruct (fs_lookup (m_fs m) localtime_path); [reflexivity|].
  destruct (fs_under (m_fs m) localtime_path); [reflexivity|].
  destruct (flag_set (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_CREAT);
    [reflexivity|].
  intro H. exfalso. exact (ret_only_no_unmodeled (errno_ret ENOENT) i m H).
Qed.

Local Lemma open_devnull_no_unmodeled : forall rd wr m i,
  ~ open_devnull m rd wr i m Unmodeled.
Proof.
  intros rd wr m i H. unfold open_devnull in H.
  exact (open_result_spec_no_unmodeled m _ i H).
Qed.

Local Lemma check_openat_devnull_complete_unmodeled : forall i flags eff m,
  openat_devnull_spec flags m i m Unmodeled ->
  check_openat_devnull flags eff m = CheckUnmodeled.
Proof.
  intros i flags eff m.
  unfold openat_devnull_spec, check_openat_devnull. cbv zeta.
  destruct (fs_lookup (m_fs m) devnull_path); [reflexivity|].
  destruct (fs_under (m_fs m) devnull_path); [reflexivity|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [intro H; exfalso; exact (open_devnull_no_unmodeled _ _ m i H)|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags);
    [intro H; exfalso; exact (open_devnull_no_unmodeled _ _ m i H)|].
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [intro H; exfalso; exact (ret_only_no_unmodeled (errno_ret EEXIST) i m H)|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY);
    [intro H; exfalso; exact (ret_only_no_unmodeled (errno_ret ENOTDIR) i m H)|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              append_create_flags);
    [intro H; exfalso; exact (open_devnull_no_unmodeled _ _ m i H)|].
  destruct (rdwr_open_word (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [intro H; exfalso; exact (open_devnull_no_unmodeled _ _ m i H)|].
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [intro H; exfalso; exact (ret_only_no_unmodeled (errno_ret EEXIST) i m H)|].
  unfold unmodeled. intros _. reflexivity.
Qed.

Local Lemma open_urandom_no_unmodeled : forall m i,
  ~ open_urandom m i m Unmodeled.
Proof.
  intros m i H. unfold open_urandom in H.
  exact (open_result_spec_no_unmodeled m _ i H).
Qed.

Local Lemma check_openat_urandom_complete_unmodeled : forall i flags eff m,
  openat_urandom_spec flags m i m Unmodeled ->
  check_openat_urandom flags eff m = CheckUnmodeled.
Proof.
  intros i flags eff m.
  unfold openat_urandom_spec, check_openat_urandom. cbv zeta.
  destruct (fs_lookup (m_fs m) urandom_path); [reflexivity|].
  destruct (fs_under (m_fs m) urandom_path); [reflexivity|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0);
    [intro H; exfalso; exact (open_urandom_no_unmodeled m i H)|].
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [intro H; exfalso; exact (ret_only_no_unmodeled (errno_ret EEXIST) i m H)|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY);
    [intro H; exfalso; exact (ret_only_no_unmodeled (errno_ret ENOTDIR) i m H)|].
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags));
    [intro H; exfalso; exact (ret_only_no_unmodeled (errno_ret EEXIST) i m H)|].
  unfold unmodeled. intros _. reflexivity.
Qed.

Local Lemma check_openat_tmp_complete_unmodeled : forall i n p flags eff m,
  openat_tmp_spec n p flags m i m Unmodeled ->
  check_openat_tmp n p flags eff m = CheckUnmodeled.
Proof.
  intros i n p flags eff m.
  unfold openat_tmp_spec, check_openat_tmp. cbv zeta.
  destruct (Nat.ltb NAME_MAX (length n)); [reflexivity|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
  { destruct (fs_under (m_fs m) p); [reflexivity|].
    destruct (fs_lookup (m_fs m) p) as [data|]; [|reflexivity].
    intro H. exfalso. exact (openat_read_spec_no_unmodeled p m i H). }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags); [|reflexivity].
  intro H. exfalso. exact (openat_create_spec_no_unmodeled p m i H).
Qed.

Local Lemma check_openat_sep_complete_unmodeled : forall i p flags eff m,
  openat_sep_spec p flags m i m Unmodeled ->
  check_openat_sep p flags eff m = CheckUnmodeled.
Proof.
  intros i p flags eff m.
  unfold openat_sep_spec, check_openat_sep.
  destruct (path_eqb p localtime_path);
    [apply check_openat_localtime_complete_unmodeled|].
  destruct (path_eqb p devnull_path);
    [apply check_openat_devnull_complete_unmodeled|].
  destruct (path_eqb p urandom_path);
    [apply check_openat_urandom_complete_unmodeled|].
  destruct (tmp_name p) as [n|];
    [apply check_openat_tmp_complete_unmodeled|reflexivity].
Qed.

Local Lemma check_openat_resolved_complete_unmodeled :
    forall i p flags eff m,
  openat_resolved_spec p flags m i m Unmodeled ->
  check_openat_resolved p flags eff m = CheckUnmodeled.
Proof.
  intros i p flags eff m.
  unfold openat_resolved_spec, check_openat_resolved. cbv zeta.
  destruct (path_has_slash p); [apply check_openat_sep_complete_unmodeled|].
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
  { intro H. exfalso. exact (openat_read_spec_no_unmodeled p m i H). }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              wr_create_flags).
  { intro H. exfalso. exact (openat_create_spec_no_unmodeled p m i H). }
  destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
  { intro H. exfalso. exact (openat_excl_spec_no_unmodeled p m i H). }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_DIRECTORY).
  { apply check_openat_dir_complete_unmodeled. }
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
              append_create_flags).
  { intro H. exfalso. exact (openat_append_spec_no_unmodeled p m i H). }
  destruct (rdwr_open_word (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
  { intro H. exfalso. exact (openat_rdwr_spec_no_unmodeled _ _ p m i H). }
  destruct (is_rdwr_excl_create
              (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
  { intro H. exfalso. exact (openat_rdwr_excl_spec_no_unmodeled p m i H). }
  unfold unmodeled. intros _. reflexivity.
Qed.

Local Lemma check_openat_body_spec_complete_unmodeled :
    forall i dirfd pathp flags eff m,
  openat_body_spec i m dirfd pathp flags i m Unmodeled ->
  check_openat_body i dirfd pathp flags eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags eff m.
  unfold openat_body_spec, check_openat_body.
  refine (refine_ucstr (user_read_cstr i m pathp)
    (fun r => completes_unmodeled i m
      (match r with
       | UOk CstrTooLong => err_ret ENAMETOOLONG
       | UFault | UOk CstrFault => err_ret EFAULT
       | USpecial => unmodeled
       | UOk (CstrOk p) =>
           if path_eqb p [] then err_ret ENOENT
           else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
           else openat_resolved_spec p flags m
       end)
      (match r with
       | UOk CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
       | UFault | UOk CstrFault => check_ret_only eff (errno_ret EFAULT) m []
       | USpecial => CheckUnmodeled
       | UOk (CstrOk p) =>
           if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
           else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
           else check_openat_resolved p flags eff m
       end)) _ _ _ _ _).
  - intro p.
    refine (refine_if (path_eqb p [])
      (fun b => completes_unmodeled i m
        (if b then err_ret ENOENT
         else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
         else openat_resolved_spec p flags m)
        (if b then check_ret_only eff (errno_ret ENOENT) m []
         else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
         else check_openat_resolved p flags eff m)) _ _).
    + unfold completes_unmodeled. intro H.
      exfalso. exact (ret_only_no_unmodeled (errno_ret ENOENT) i m H).
    + refine (refine_if (negb (bv_eqb dirfd AT_FDCWD32))
        (fun b => completes_unmodeled i m
          (if b then unmodeled else openat_resolved_spec p flags m)
          (if b then CheckUnmodeled else check_openat_resolved p flags eff m))
        _ _).
      * unfold completes_unmodeled, unmodeled. intros _. reflexivity.
      * unfold completes_unmodeled.
        apply check_openat_resolved_complete_unmodeled.
  - unfold completes_unmodeled. intro H.
    exfalso. exact (ret_only_no_unmodeled (errno_ret ENAMETOOLONG) i m H).
  - unfold completes_unmodeled. intro H.
    exfalso. exact (ret_only_no_unmodeled (errno_ret EFAULT) i m H).
  - unfold completes_unmodeled. intro H.
    exfalso. exact (ret_only_no_unmodeled (errno_ret EFAULT) i m H).
  - unfold completes_unmodeled, unmodeled. intros _. reflexivity.
Qed.



Local Lemma openat_core_unmodeled_inv : forall i dirfd pathp flags m,
  openat_core_spec dirfd pathp flags i m Unmodeled ->
  negb (modeled_open_flags flags) = true \/
  (negb (modeled_open_flags flags) = false /\
   openat_body_spec i m dirfd pathp flags i m Unmodeled).
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

Lemma check_openat_complete_unmodeled : forall i dirfd pathp flags m eff,
  openat_spec dirfd pathp flags i m Unmodeled ->
  check_openat i dirfd pathp flags eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp flags m eff H.
  unfold openat_spec in H. apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply get_model_bind_unmodeled_inv in H. cbv beta in H.
  apply record_copyins_unmodeled_inv in H.
  apply openat_core_unmodeled_inv in H.
  destruct H as [Hflags | (Hflags & Hbody)].
  - unfold check_openat. rewrite Hflags. reflexivity.
  - apply check_openat_body_spec_complete_unmodeled
      with (eff := clear_copyins eff) in Hbody.
    unfold check_openat. rewrite Hflags. cbv iota. rewrite Hbody. reflexivity.
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
  | Some (FdPipe _ _) => check_ret_only eff (errno_ret EINVAL) m []  (* S_IFIFO, not S_ISREG *)
  | Some (FdDevNull _ _) => check_ret_only eff (errno_ret EINVAL) m []  (* S_IFCHR, not S_ISREG *)
  | Some FdUrandom => check_ret_only eff (errno_ret EINVAL) m []  (* S_IFCHR again *)
  | Some (FdFile _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | Some FdDir => check_ret_only eff (errno_ret EINVAL) m []
  | Some (FdFileW p _) | Some (FdFileRW p _) =>
      match fs_lookup (m_fs m) p with
      | None => CheckUnmodeled
      | Some data =>
          if negb (modeled_truncate_gap data len) then CheckUnmodeled
          else
            check_ret_only eff (Z_to_bv 64 0)
              (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) []
      end
  | Some (FdFileA p _) =>
      match fs_lookup (m_fs m) p with
      | None => CheckUnmodeled
      | Some data =>
          if negb (modeled_truncate_gap data len) then CheckUnmodeled
          else
            check_ret_only eff (Z_to_bv 64 0)
              (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) []
      end
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
  destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| ]|] eqn:Hfd;
    try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
         (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota; srw Hfd;
         apply pure_ok).
  (* the two writable-file arms are the only ones that change the model *)
  all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; [|discriminate].
  all: destruct (negb (modeled_truncate_gap data len)) eqn:Hgap; [discriminate|].
  all: apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->).
  all: eapply bind_ok0; [apply get_model_ok|]; cbv beta iota; srw Hfd; srw Hfs;
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
  destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| ]|] eqn:Hfd;
    try (now apply check_ret_only_no_unmodeled in H).
  (* every destruct precedes the bind: the spec's [fs_lookup] sits under
     [get_model]'s binder, so it is only rewritable once [get_model_ok]
     has instantiated it *)
  all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
       [ destruct (negb (modeled_truncate_gap data len)) eqn:Hgap;
         [ eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
           srw Hfd; srw Hfs; srw Hgap; apply unmodeled_intro
         | now apply check_ret_only_no_unmodeled in H ]
       | eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
         srw Hfd; srw Hfs; apply unmodeled_intro ].
Qed.

Lemma check_ftruncate_complete_ok : forall fd len eff m m' evs i,
  ftruncate_spec fd len i m (Ok eff m' evs) ->
  check_ftruncate fd len eff m = CheckOk m' evs.
Proof.
  intros fd len eff m m' evs i H.
  unfold ftruncate_spec in H. unfold check_ftruncate. sys_unfold.
  cbv iota in H. inv_ok.
  destruct ((bv_signed len <? 0)%Z) eqn:Hneg; hall Hneg; inv_ok;
    try (destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| ]|] eqn:Hfd;
         hall Hfd; inv_ok);
    try (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok);
    try (destruct (negb (modeled_truncate_gap data len)) eqn:Hgap; hall Hgap;
         inv_ok);
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
    try (destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| ]|] eqn:Hfd;
         hall Hfd; inv_ok);
    try (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; hall Hfs; inv_ok);
    try (destruct (negb (modeled_truncate_gap data len)) eqn:Hgap; hall Hgap;
         inv_ok);
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

Local Definition check_faccessat_body (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match user_read_cstr i m pathp with
  | UOk CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | UFault | UOk CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | USpecial => CheckUnmodeled
  | UOk (CstrOk p) =>
      if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
      else if negb (bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
      else if path_eqb p dot_path then check_access_exists eff m
      else if path_eqb p dotdot_path then check_access_exists eff m
      else if path_has_slash p then CheckUnmodeled
      else if Nat.ltb NAME_MAX (length p) then CheckUnmodeled
      else if fs_under (m_fs m) p then CheckUnmodeled
      else
      match fs_lookup (m_fs m) p with
      | None => check_ret_only eff (errno_ret ENOENT) m []
      | Some _ => check_access_exists eff m
      end
  end.

(** The pathname copy-in, as [check_openat] and
    [Checks.Sys.Fs.Namei.check_unlinkat] check it: decide the body
    against the effect with the ledger cleared, then require the claimed
    ledger to be exactly that one range.  Both mode arms are outside the
    wrapper, mirroring the spec — the kernel decides the mode before
    [user_path_at], so an honest -EINVAL carries no copy-in at all. *)
Definition check_faccessat (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (modeled_access_mode mode)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (access_mode_f_ok mode) then CheckUnmodeled
  else
    let reads := [(pathp, user_cstr_access_len i m pathp)] in
    check_copyins_after reads eff
      (check_faccessat_body i dirfd pathp (clear_copyins eff) m).

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

Local Lemma check_faccessat_body_sound_ok : forall i dirfd pathp eff m m' evs,
  check_faccessat_body i dirfd pathp eff m = CheckOk m' evs ->
  faccessat_body_spec dirfd pathp i m i m (Ok eff m' evs).
Proof.
  intros i dirfd pathp eff m m' evs H.
  unfold check_faccessat_body in H. unfold faccessat_body_spec.
  destruct (user_read_cstr i m pathp) as [[p| |]| |] eqn:Hp.
  2-4: apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
       apply pure_ok.
  2: discriminate.
  destruct (path_eqb p []) eqn:Hpe.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; [discriminate|].
  destruct (path_eqb p dot_path) eqn:Hdot.
  { now apply check_access_exists_sound_ok. }
  destruct (path_eqb p dotdot_path) eqn:Hdd.
  { now apply check_access_exists_sound_ok. }
  destruct (path_has_slash p) eqn:Hsl; [discriminate|].
  destruct (Nat.ltb NAME_MAX (length p)) eqn:Hnm; [discriminate|].
  destruct (fs_under (m_fs m) p) eqn:Hun; [discriminate|].
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
  2: { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
       apply pure_ok. }
  now apply check_access_exists_sound_ok.
Qed.

Local Lemma check_faccessat_body_sound_unmodeled : forall i dirfd pathp eff m,
  check_faccessat_body i dirfd pathp eff m = CheckUnmodeled ->
  faccessat_body_spec dirfd pathp i m i m Unmodeled.
Proof.
  intros i dirfd pathp eff m H.
  unfold check_faccessat_body in H. unfold faccessat_body_spec.
  destruct (user_read_cstr i m pathp) as [[p| |]| |] eqn:Hp;
    [|now apply check_ret_only_no_unmodeled in H
     |now apply check_ret_only_no_unmodeled in H
     |now apply check_ret_only_no_unmodeled in H
     |apply unmodeled_intro].
  destruct (path_eqb p []) eqn:Hpe;
    [now apply check_ret_only_no_unmodeled in H|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; [apply unmodeled_intro|].
  destruct (path_eqb p dot_path) eqn:Hdot.
  { exfalso. now apply check_access_exists_no_unmodeled in H. }
  destruct (path_eqb p dotdot_path) eqn:Hdd.
  { exfalso. now apply check_access_exists_no_unmodeled in H. }
  destruct (path_has_slash p) eqn:Hsl; [apply unmodeled_intro|].
  destruct (Nat.ltb NAME_MAX (length p)) eqn:Hnm; [apply unmodeled_intro|].
  destruct (fs_under (m_fs m) p) eqn:Hun; [apply unmodeled_intro|].
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
    [|now apply check_ret_only_no_unmodeled in H].
  exfalso. now apply check_access_exists_no_unmodeled in H.
Qed.

Local Lemma check_faccessat_body_complete_ok :
    forall i dirfd pathp eff m m' evs,
  faccessat_body_spec dirfd pathp i m i m (Ok eff m' evs) ->
  check_faccessat_body i dirfd pathp eff m = CheckOk m' evs.
Proof.
  intros i dirfd pathp eff m m' evs H.
  unfold faccessat_body_spec in H. unfold check_faccessat_body.
  destruct (user_read_cstr i m pathp) as [[p| |]| |] eqn:Hp;
    [|fa_det|fa_det|fa_det|fa_unmod_h].
  destruct (path_eqb p []) eqn:Hpe; [fa_det|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; [fa_unmod_h|].
  destruct (path_eqb p dot_path) eqn:Hdot;
    [now apply check_access_exists_complete_ok in H|].
  destruct (path_eqb p dotdot_path) eqn:Hdd;
    [now apply check_access_exists_complete_ok in H|].
  destruct (path_has_slash p) eqn:Hsl; [fa_unmod_h|].
  destruct (Nat.ltb NAME_MAX (length p)) eqn:Hnm; [fa_unmod_h|].
  destruct (fs_under (m_fs m) p) eqn:Hun; [fa_unmod_h|].
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
    [now apply check_access_exists_complete_ok in H|fa_det].
Qed.

Local Lemma check_faccessat_body_complete_unmodeled :
    forall i dirfd pathp m eff,
  faccessat_body_spec dirfd pathp i m i m Unmodeled ->
  check_faccessat_body i dirfd pathp eff m = CheckUnmodeled.
Proof.
  intros i dirfd pathp m eff H.
  unfold faccessat_body_spec in H. unfold check_faccessat_body.
  destruct (user_read_cstr i m pathp) as [[p| |]| |] eqn:Hp;
    [|fa_det_u|fa_det_u|fa_det_u|reflexivity].
  destruct (path_eqb p []) eqn:Hpe; [fa_det_u|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; [reflexivity|].
  destruct (path_eqb p dot_path) eqn:Hdot;
    [exfalso; now apply access_exists_no_unmodeled in H|].
  destruct (path_eqb p dotdot_path) eqn:Hdd;
    [exfalso; now apply access_exists_no_unmodeled in H|].
  destruct (path_has_slash p) eqn:Hsl; [reflexivity|].
  destruct (Nat.ltb NAME_MAX (length p)) eqn:Hnm; [reflexivity|].
  destruct (fs_under (m_fs m) p) eqn:Hun; [reflexivity|].
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
    [exfalso; now apply access_exists_no_unmodeled in H|fa_det_u].
Qed.

(** No arm of the body claims a copy-in of its own: each returns either
    through [check_ret_only], which forces every ledger empty, or
    through [check_access_exists], which matches six empty lists.  That
    is what lets the wrapper equate the WHOLE claimed ledger with the one
    pathname range rather than with a prefix of it. *)
Local Lemma check_faccessat_body_ok_copyins_nil :
    forall i dirfd pathp eff m m' evs,
  check_faccessat_body i dirfd pathp eff m = CheckOk m' evs ->
  eff_copyins eff = [].
Proof.
  intros i dirfd pathp eff m m' evs H.
  unfold check_faccessat_body in H.
  destruct (user_read_cstr i m pathp) as [[p| |]| |];
    [ | apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity
      | apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity
      | apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity
      | discriminate ].
  destruct (path_eqb p []);
    [apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); [discriminate|].
  destruct (path_eqb p dot_path);
    [now apply check_access_exists_ok_copyins_nil in H|].
  destruct (path_eqb p dotdot_path);
    [now apply check_access_exists_ok_copyins_nil in H|].
  destruct (path_has_slash p); [discriminate|].
  destruct (Nat.ltb NAME_MAX (length p)); [discriminate|].
  destruct (fs_under (m_fs m) p); [discriminate|].
  destruct (fs_lookup (m_fs m) p) as [data|];
    [now apply check_access_exists_ok_copyins_nil in H
    |apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _); reflexivity].
Qed.

(* ------------------------------------------------------- the four exports *)

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
  cbv zeta in H. apply check_copyins_after_ok_iff in H.
  destruct H as (Hreads & Hbody).
  fa_open. apply record_copyins_clear_ok; [exact Hreads|].
  now apply check_faccessat_body_sound_ok.
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
  cbv zeta in H. apply check_copyins_after_unmodeled in H.
  fa_open_u. apply record_copyins_unmodeled.
  eapply check_faccessat_body_sound_unmodeled. exact H.
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
  apply record_copyins_ok_inv in H.
  destruct H as (core & Hcore & ->).
  apply check_faccessat_body_complete_ok in Hcore.
  pose proof (check_faccessat_body_ok_copyins_nil _ _ _ _ _ _ _ Hcore) as Hnil.
  cbv zeta. apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
  - cbn [with_copyins eff_copyins]. rewrite Hnil, app_nil_r. reflexivity.
  - destruct core as [ret ws zs us cs copyins].
    cbn in Hnil. subst copyins. exact Hcore.
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
  apply record_copyins_unmodeled_inv in H.
  cbv zeta. unfold check_copyins_after.
  rewrite (check_faccessat_body_complete_unmodeled i dirfd pathp m
             (clear_copyins eff) H). reflexivity.
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
    let reads := [(pathp, user_cstr_access_len i m pathp)] in
    check_copyins_after reads eff
      (check_faccessat_body i dirfd pathp (clear_copyins eff) m).

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
  cbv zeta in H. apply check_copyins_after_ok_iff in H.
  destruct H as (Hreads & Hbody).
  fa_open. apply record_copyins_clear_ok; [exact Hreads|].
  now apply check_faccessat_body_sound_ok.
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
  cbv zeta in H. apply check_copyins_after_unmodeled in H.
  fa_open_u. apply record_copyins_unmodeled.
  eapply check_faccessat_body_sound_unmodeled. exact H.
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
  apply record_copyins_ok_inv in H.
  destruct H as (core & Hcore & ->).
  apply check_faccessat_body_complete_ok in Hcore.
  pose proof (check_faccessat_body_ok_copyins_nil _ _ _ _ _ _ _ Hcore) as Hnil.
  cbv zeta. apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
  - cbn [with_copyins eff_copyins]. rewrite Hnil, app_nil_r. reflexivity.
  - destruct core as [ret ws zs us cs copyins].
    cbn in Hnil. subst copyins. exact Hcore.
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
  apply record_copyins_unmodeled_inv in H.
  cbv zeta. unfold check_copyins_after.
  rewrite (check_faccessat_body_complete_unmodeled i dirfd pathp m
             (clear_copyins eff) H). reflexivity.
Qed.
