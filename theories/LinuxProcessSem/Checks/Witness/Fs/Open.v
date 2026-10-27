(** * LinuxProcessSem.Checks.Witness.Fs.Open — the openat (56), close (57), ftruncate (46) witnesses, and their proofs

    Mirrors [Sys/Fs/Open.v], which answers to Linux [fs/open.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude Fs.ReadWrite.

Local Definition openat_core_witness (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if negb (modeled_open_flags flags) then Unmodeled  (* unmodeled flag combination *)
  else match user_read_cstr i m pathp with
       | UOk CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m  (* over-long path *)
       | UFault | UOk CstrFault =>
           ret_outcome (errno_ret EFAULT) m                         (* unreadable path *)
       | USpecial => Unmodeled                                      (* vDSO pair *)
       | UOk (CstrOk p) =>
           if path_eqb p [] then ret_outcome (errno_ret ENOENT) m  (* empty pathname *)
           else if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled         (* unmodeled dirfd *)
           (* a pathname with a separator, declined before any flag is
              looked at — see [Open.openat_resolved_spec]'s guard —
              except the one [Open.openat_sep_spec] answers *)
           else if path_has_slash p then
             if path_eqb p localtime_path then
               match fs_lookup (m_fs m) localtime_path with
               | Some _ => Unmodeled
               | None =>
                   if fs_under (m_fs m) localtime_path then Unmodeled
                   else if flag_set (Z.ldiff (bv_unsigned flags)
                                       open_ignored_flags) O_CREAT
                   then Unmodeled
                   else ret_outcome (errno_ret ENOENT) m
               end
             else if path_eqb p devnull_path then
               match fs_lookup (m_fs m) devnull_path with
               | Some _ => Unmodeled
               | None =>
                   if fs_under (m_fs m) devnull_path then Unmodeled
                   else
                   let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
                   if Z.eqb fl 0 then ret_outcome (errno_ret witness_errno) m
                   else if Z.eqb fl wr_create_flags then
                     ret_outcome (errno_ret witness_errno) m
                   else if is_excl_create fl then ret_outcome (errno_ret EEXIST) m
                   else if Z.eqb fl O_DIRECTORY then ret_outcome (errno_ret ENOTDIR) m
                   else if Z.eqb fl append_create_flags then
                     ret_outcome (errno_ret witness_errno) m
                   else if rdwr_open_word fl then ret_outcome (errno_ret witness_errno) m
                   else if is_rdwr_excl_create fl then ret_outcome (errno_ret EEXIST) m
                   else Unmodeled
               end
             else if path_eqb p urandom_path then
               match fs_lookup (m_fs m) urandom_path with
               | Some _ => Unmodeled
               | None =>
                   if fs_under (m_fs m) urandom_path then Unmodeled
                   else
                   let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
                   if Z.eqb fl 0 then ret_outcome (errno_ret witness_errno) m
                   else if is_excl_create fl then ret_outcome (errno_ret EEXIST) m
                   else if Z.eqb fl O_DIRECTORY then ret_outcome (errno_ret ENOTDIR) m
                   else if is_rdwr_excl_create fl then ret_outcome (errno_ret EEXIST) m
                   else Unmodeled
               end
             else match tmp_name p with
                  | Some n =>
                      if Nat.ltb NAME_MAX (length n) then Unmodeled
                      else
                      let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
                      if Z.eqb fl 0 then
                        (if fs_under (m_fs m) p then Unmodeled
                         else match fs_lookup (m_fs m) p with
                              | None => Unmodeled
                              | Some _ => ret_outcome (errno_ret witness_errno) m
                              end)
                      else if Z.eqb fl wr_create_flags then
                        (if path_is_dirref p || fs_under (m_fs m) p
                         then ret_outcome (errno_ret EISDIR) m
                         else ret_outcome (errno_ret witness_errno) m)
                      else Unmodeled
                  | None => Unmodeled
                  end
           else
           let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
           if Z.eqb fl 0 then
             if path_is_dirref p then
               ret_outcome (errno_ret witness_errno) m  (* "."/".." : env-failure branch *)
             else
             match fs_lookup (m_fs m) p with
             | None => ret_outcome (errno_ret ENOENT) m
             | Some _ => ret_outcome (errno_ret witness_errno) m
             end
           else if Z.eqb fl wr_create_flags then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EISDIR) m        (* "."/".." or an implied directory : deterministic -EISDIR *)
             else
             ret_outcome (errno_ret witness_errno) m
           else if is_excl_create fl then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EEXIST) m        (* "."/".." or an implied directory : deterministic -EEXIST *)
             else
             match fs_lookup (m_fs m) p with
             | Some _ => ret_outcome (errno_ret EEXIST) m  (* exists: deterministic -EEXIST *)
             | None => ret_outcome (errno_ret witness_errno) m  (* env-failure branch *)
             end
           else if Z.eqb fl O_DIRECTORY then
             (* the one arm with declines of its own: the witness follows
                them, since [Unmodeled] is the outcome the spec exhibits
                there *)
             if path_is_dirref p then
               ret_outcome (errno_ret witness_errno) m  (* "."/".." : env-failure branch *)
             else if Nat.ltb NAME_MAX (length p) then Unmodeled
             else if fs_under (m_fs m) p then Unmodeled
             else
             match fs_lookup (m_fs m) p with
             | None => ret_outcome (errno_ret ENOENT) m
             | Some _ => ret_outcome (errno_ret ENOTDIR) m
             end
           else if Z.eqb fl append_create_flags then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EISDIR) m        (* "."/".." or an implied directory : deterministic -EISDIR *)
             else
             ret_outcome (errno_ret witness_errno) m   (* env-failure branch *)
           else if rdwr_open_word fl then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EISDIR) m        (* "."/".." or an implied directory : deterministic -EISDIR *)
             else
             match fs_lookup (m_fs m) p with
             | None =>
                 if flag_set fl O_CREAT
                 then ret_outcome (errno_ret witness_errno) m  (* env-failure branch *)
                 else ret_outcome (errno_ret ENOENT) m         (* deterministic -ENOENT *)
             | Some _ => ret_outcome (errno_ret witness_errno) m
             end
           else if is_rdwr_excl_create fl then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EEXIST) m        (* "."/".." or an implied directory : deterministic -EEXIST *)
             else
             match fs_lookup (m_fs m) p with
             | Some _ => ret_outcome (errno_ret EEXIST) m
             | None => ret_outcome (errno_ret witness_errno) m
             end
           else Unmodeled   (* unreachable: [modeled_open_flags flags] holds here *)
       end.

Definition openat_witness (dirfd pathp flags : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  outcome_copyins
    [(pathp, user_cstr_access_len i m pathp)]
    (openat_core_witness dirfd pathp flags i m).

Local Lemma openat_core_witness_ok : forall dirfd pathp flags i m,
  openat_core_spec dirfd pathp flags i m
    (openat_core_witness dirfd pathp flags i m).
Proof.
  intros. unfold openat_core_spec, openat_core_witness.
  unfold create_wronly, open_append, open_rdwr.
  destruct (negb (modeled_open_flags flags)) eqn:Hfl.
  - (* unmodeled flags: declined BEFORE the pathname is fetched *)
    eapply bind_step; [apply input_ok|].
    cbv beta. eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta. apply unmodeled_intro.
  - eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
    unfold openat_body_spec.
    destruct (user_read_cstr i m pathp) as [[p| |]| |] eqn:Hp.
    2-4: apply pure_ok.
    2: apply unmodeled_intro.
    destruct (path_eqb p []) eqn:Hpe.
    { apply pure_ok. }
    destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd.
    { apply unmodeled_intro. }
    unfold openat_resolved_spec.
    destruct (path_has_slash p) eqn:Huw.
    { unfold openat_sep_spec, openat_localtime_spec, openat_devnull_spec,
        open_devnull, openat_urandom_spec, open_urandom, open_result_spec.
      cbv zeta.
      destruct (path_eqb p localtime_path).
      { destruct (fs_lookup (m_fs m) localtime_path); [apply unmodeled_intro|].
        destruct (fs_under (m_fs m) localtime_path); [apply unmodeled_intro|].
        destruct (flag_set (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                    O_CREAT); [apply unmodeled_intro|].
        apply pure_ok. }
      destruct (path_eqb p devnull_path).
      2:{ destruct (path_eqb p urandom_path).
          2:{ destruct (tmp_name p) as [n|]; [|apply unmodeled_intro].
              unfold openat_tmp_spec, openat_read_spec, openat_create_spec.
              cbv zeta.
              destruct (Nat.ltb NAME_MAX (length n)); [apply unmodeled_intro|].
              destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
              { destruct (fs_under (m_fs m) p); [apply unmodeled_intro|].
                destruct (fs_lookup (m_fs m) p); [|apply unmodeled_intro].
                destruct (path_is_dirref p);
                  (apply alt_l; eapply bind_step;
                   [apply errno_head_witness|apply pure_ok]). }
              destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                          wr_create_flags); [|apply unmodeled_intro].
              destruct (path_is_dirref p || fs_under (m_fs m) p).
              { apply pure_ok. }
              apply alt_l. eapply bind_step; [apply errno_head_witness|].
              apply pure_ok. }
          destruct (fs_lookup (m_fs m) urandom_path); [apply unmodeled_intro|].
          destruct (fs_under (m_fs m) urandom_path); [apply unmodeled_intro|].
          destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
          { apply alt_l. eapply bind_step; [apply errno_head_witness|].
            apply pure_ok. }
          destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
          { apply pure_ok. }
          destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                      O_DIRECTORY).
          { apply pure_ok. }
          destruct (is_rdwr_excl_create
                      (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
          { apply pure_ok. }
          apply unmodeled_intro. }
      destruct (fs_lookup (m_fs m) devnull_path); [apply unmodeled_intro|].
      destruct (fs_under (m_fs m) devnull_path); [apply unmodeled_intro|].
      destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0).
      { apply alt_l. eapply bind_step; [apply errno_head_witness|].
        apply pure_ok. }
      destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                  wr_create_flags).
      { apply alt_l. eapply bind_step; [apply errno_head_witness|].
        apply pure_ok. }
      destruct (is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
      { apply pure_ok. }
      destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                  O_DIRECTORY).
      { apply pure_ok. }
      destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                  append_create_flags).
      { apply alt_l. eapply bind_step; [apply errno_head_witness|].
        apply pure_ok. }
      destruct (rdwr_open_word (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
      { apply alt_l. eapply bind_step; [apply errno_head_witness|].
        apply pure_ok. }
      destruct (is_rdwr_excl_create
                  (Z.ldiff (bv_unsigned flags) open_ignored_flags)).
      { apply pure_ok. }
      apply unmodeled_intro. }
    unfold openat_read_spec, openat_create_spec, openat_excl_spec,
      openat_dir_spec, openat_append_spec, openat_rdwr_spec,
      openat_rdwr_excl_spec, open_result_spec.
    destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags) 0) eqn:Hf0.
    + destruct (path_is_dirref p) eqn:Hdot.
      { apply alt_l. eapply bind_step; [apply errno_head_witness|].
        apply pure_ok. }
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
      * apply alt_l. eapply bind_step; [apply errno_head_witness|].
        apply pure_ok.
      * apply pure_ok.
    + destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                  wr_create_flags) eqn:Hfw.
      * destruct (path_is_dirref p || fs_under (m_fs m) p) eqn:Hdot.
        { apply pure_ok. }
        apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
      * destruct (is_excl_create
                    (Z.ldiff (bv_unsigned flags) open_ignored_flags)) eqn:Hfx.
        -- destruct (path_is_dirref p || fs_under (m_fs m) p) eqn:Hdot.
           { apply pure_ok. }
           destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
           { apply pure_ok. }
           apply alt_l. eapply bind_step; [apply errno_head_witness|].
           apply pure_ok.
        -- destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                       O_DIRECTORY) eqn:Hfd.
           ++ destruct (path_is_dirref p) eqn:Hdot.
              { apply alt_l. eapply bind_step; [apply errno_head_witness|].
                apply pure_ok. }
              destruct (Nat.ltb NAME_MAX (length p)) eqn:Hnm.
              { apply unmodeled_intro. }
              destruct (fs_under (m_fs m) p) eqn:Hun.
              { apply unmodeled_intro. }
              destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
                apply pure_ok.
           ++ destruct (Z.eqb (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                          append_create_flags) eqn:Hfa.
              ** destruct (path_is_dirref p || fs_under (m_fs m) p) eqn:Hdot.
                 { apply pure_ok. }
                 apply alt_l. eapply bind_step; [apply errno_head_witness|].
                 apply pure_ok.
              ** destruct (rdwr_open_word
                             (Z.ldiff (bv_unsigned flags) open_ignored_flags))
                     eqn:Hfrw.
                 { destruct (path_is_dirref p || fs_under (m_fs m) p) eqn:Hdot.
                   { apply pure_ok. }
                   destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
                   { apply alt_l. eapply bind_step; [apply errno_head_witness|].
                     apply pure_ok. }
                   destruct (flag_set
                               (Z.ldiff (bv_unsigned flags) open_ignored_flags)
                               O_CREAT) eqn:Hcr.
                   { apply alt_l. eapply bind_step; [apply errno_head_witness|].
                     apply pure_ok. }
                   apply pure_ok. }
                 destruct (is_rdwr_excl_create
                             (Z.ldiff (bv_unsigned flags) open_ignored_flags))
                     eqn:Hfrx.
                 { destruct (path_is_dirref p || fs_under (m_fs m) p) eqn:Hdot.
                   { apply pure_ok. }
                   destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
                   { apply pure_ok. }
                   apply alt_l. eapply bind_step; [apply errno_head_witness|].
                   apply pure_ok. }
                 apply unmodeled_intro.
Qed.

Lemma openat_witness_ok : forall dirfd pathp flags i m,
  openat_spec dirfd pathp flags i m (openat_witness dirfd pathp flags i m).
Proof.
  intros. unfold openat_spec, openat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  apply record_copyins_outcome.
  apply openat_core_witness_ok.
Qed.

(* =========================================================================
   close (57) — deterministic: remove the fd or -EBADF
   ========================================================================= *)

Definition close_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some _ => ret_outcome (Z_to_bv 64 0) (with_fds (fd_remove (m_fds m) fd) m)
  end.

Lemma close_witness_ok : forall fd i m, close_spec fd i m (close_witness fd m).
Proof.
  intros. unfold close_spec, close_witness.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
Qed.

(* =========================================================================
   lseek (62) — deterministic: reposition the file offset, or the
   errno for a channel / bad fd / invalid destination
   ========================================================================= *)

Definition ftruncate_witness (fd len : word) (m : Model)
    : outcome SyscallEffect :=
  if (bv_signed len <? 0)%Z then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) => ret_outcome (errno_ret EINVAL) m
  | Some (FdSocket _) => ret_outcome (errno_ret EINVAL) m  (* S_ISSOCK, not S_ISREG *)
  | Some (FdPipe _ _) => ret_outcome (errno_ret EINVAL) m  (* S_IFIFO, not S_ISREG *)
  | Some (FdDevNull _ _) => ret_outcome (errno_ret EINVAL) m  (* S_IFCHR, not S_ISREG *)
  | Some FdUrandom => ret_outcome (errno_ret EINVAL) m  (* S_IFCHR again *)
  | Some (FdFile _ _) => ret_outcome (errno_ret EINVAL) m
  | Some FdDir => ret_outcome (errno_ret EINVAL) m
  | Some (FdFileW p _) | Some (FdFileRW p _) =>
      match fs_lookup (m_fs m) p with
      | None => Unmodeled
      | Some data =>
          if negb (modeled_truncate_gap data len) then Unmodeled
          else ret_outcome (Z_to_bv 64 0)
                 (with_fs (fs_set (m_fs m) p (file_truncate data len)) m)
      end
  | Some (FdFileA p _) =>
      (* a writable regular file too: see [Open.ftruncate_spec] *)
      match fs_lookup (m_fs m) p with
      | None => Unmodeled
      | Some data =>
          if negb (modeled_truncate_gap data len) then Unmodeled
          else ret_outcome (Z_to_bv 64 0)
                 (with_fs (fs_set (m_fs m) p (file_truncate data len)) m)
      end
  end.

Lemma ftruncate_witness_ok : forall fd len i m,
  ftruncate_spec fd len i m (ftruncate_witness fd len m).
Proof.
  intros. unfold ftruncate_spec, ftruncate_witness.
  destruct ((bv_signed len <? 0)%Z) eqn:Hneg; [apply pure_ok|].
  destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| ]|] eqn:Hfd;
    try (eapply bind_step; [apply get_model_ok|];
         cbv beta iota; srw Hfd; apply pure_ok).
  all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
       [ destruct (negb (modeled_truncate_gap data len)) eqn:Hgap;
         [ eapply bind_step; [apply get_model_ok|];
           cbv beta iota; srw Hfd; srw Hfs; srw Hgap; apply unmodeled_intro
         | eapply bind_step; [apply get_model_ok|];
           cbv beta iota; srw Hfd; srw Hfs; srw Hgap;
           eapply bind_step; [apply modify_ok|]; apply pure_ok ]
       | eapply bind_step; [apply get_model_ok|];
         cbv beta iota; srw Hfd; srw Hfs; apply unmodeled_intro ].
Qed.

(** faccessat witness: the deterministic errno arms, the fail-closed
    [Unmodeled], or — where the path resolves — plain SUCCESS.  That is
    the [alt]'s RIGHT branch, unlike the openat and unlinkat witnesses
    which take the injectable-errno branch to avoid building a new model
    state.  Nothing has to be built here: faccessat changes no state, so
    both alternatives return the same model and the success one is the
    outcome a real run actually produces. *)
Local Definition faccessat_body_witness (dirfd pathp : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match user_read_cstr i m pathp with
  | UOk CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | UFault | UOk CstrFault => ret_outcome (errno_ret EFAULT) m
  | USpecial => Unmodeled
  | UOk (CstrOk p) =>
      if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
      else if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled
      else if path_eqb p dot_path then ret_outcome (Z_to_bv 64 0) m
      else if path_eqb p dotdot_path then ret_outcome (Z_to_bv 64 0) m
      else if path_has_slash p then Unmodeled
      else if Nat.ltb NAME_MAX (length p) then Unmodeled
      else if fs_under (m_fs m) p then Unmodeled
      else
      match fs_lookup (m_fs m) p with
      | None => ret_outcome (errno_ret ENOENT) m
      | Some _ => ret_outcome (Z_to_bv 64 0) m
      end
  end.

(** Both mode arms carry no copy-in — the kernel decides the mode before
    [user_path_at] — and every other arm carries the one pathname range
    [Fs.Open.faccessat_spec] records. *)
Definition faccessat_witness (dirfd pathp mode : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (modeled_access_mode mode) then ret_outcome (errno_ret EINVAL) m
  else if negb (access_mode_f_ok mode) then Unmodeled
  else
    outcome_copyins [(pathp, user_cstr_access_len i m pathp)]
      (faccessat_body_witness dirfd pathp i m).

Local Lemma faccessat_body_witness_ok : forall dirfd pathp i m,
  faccessat_body_spec dirfd pathp i m i m
    (faccessat_body_witness dirfd pathp i m).
Proof.
  intros. unfold faccessat_body_spec, faccessat_body_witness.
  destruct (user_read_cstr i m pathp) as [[p| |]| |];
    [|apply pure_ok|apply pure_ok|apply pure_ok|apply unmodeled_intro].
  destruct (path_eqb p []); [apply pure_ok|].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); [apply unmodeled_intro|].
  destruct (path_eqb p dot_path);
    [unfold access_exists_spec; apply alt_r; apply pure_ok|].
  destruct (path_eqb p dotdot_path);
    [unfold access_exists_spec; apply alt_r; apply pure_ok|].
  destruct (path_has_slash p); [apply unmodeled_intro|].
  destruct (Nat.ltb NAME_MAX (length p)); [apply unmodeled_intro|].
  destruct (fs_under (m_fs m) p); [apply unmodeled_intro|].
  destruct (fs_lookup (m_fs m) p) as [data|]; [|apply pure_ok].
  unfold access_exists_spec. apply alt_r. apply pure_ok.
Qed.

Lemma faccessat_witness_ok : forall dirfd pathp mode i m,
  faccessat_spec dirfd pathp mode i m (faccessat_witness dirfd pathp mode i m).
Proof.
  intros. unfold faccessat_spec, faccessat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota.
  destruct (negb (modeled_access_mode mode)); [apply pure_ok|].
  destruct (negb (access_mode_f_ok mode)); [apply unmodeled_intro|].
  apply record_copyins_outcome. apply faccessat_body_witness_ok.
Qed.

(** faccessat2's witness is faccessat's, under one more -EINVAL and one
    more decline: [do_faccessat] is the shared body, so past the flag
    word there is nothing new to build. *)
Definition faccessat2_witness (dirfd pathp mode flags : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (modeled_access_mode mode) then ret_outcome (errno_ret EINVAL) m
  else if negb (valid_access_flags flags) then ret_outcome (errno_ret EINVAL) m
  else if negb (modeled_access_flags flags) then Unmodeled
  else if negb (access_mode_f_ok mode) then Unmodeled
  else
    outcome_copyins [(pathp, user_cstr_access_len i m pathp)]
      (faccessat_body_witness dirfd pathp i m).

Lemma faccessat2_witness_ok : forall dirfd pathp mode flags i m,
  faccessat2_spec dirfd pathp mode flags i m
    (faccessat2_witness dirfd pathp mode flags i m).
Proof.
  intros. unfold faccessat2_spec, faccessat2_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota.
  destruct (negb (modeled_access_mode mode)); [apply pure_ok|].
  destruct (negb (valid_access_flags flags)); [apply pure_ok|].
  destruct (negb (modeled_access_flags flags)); [apply unmodeled_intro|].
  destruct (negb (access_mode_f_ok mode)); [apply unmodeled_intro|].
  apply record_copyins_outcome. apply faccessat_body_witness_ok.
Qed.
