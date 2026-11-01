(** * LinuxProcessSem.Checks.Witness.Fs.Stat — the readlinkat (78), newfstatat (79) and fstat (80) witnesses, and their proofs

    Mirrors [Sys/Fs/Stat.v], which answers to Linux [fs/stat.c]: this
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
  Prelude.

(** readlinkat: [Stat.readlinkat_spec] read straight off — every arm is
    deterministic. *)
Definition readlinkat_core_witness (dirfd pathp : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | CstrFault => ret_outcome (errno_ret EFAULT) m
  | CstrOk p =>
      if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled
      else if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
      else if path_eqb p dot_path || path_eqb p dotdot_path
      then ret_outcome (errno_ret EINVAL) m
      else
        match statat_cwd_path m p with
        | None => Unmodeled
        | Some q =>
            match fs_lookup (m_fs m) q with
            | None => ret_outcome (errno_ret ENOENT) m
            | Some _ => ret_outcome (errno_ret EINVAL) m
            end
        end
  end.

Definition readlinkat_witness (dirfd : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if (sint32 (in_arg i 3) <=? 0)%Z then ret_outcome (errno_ret EINVAL) m
  else outcome_copyins
         [(in_arg i 1, cstr_access_len_aux (in_mem i) (in_arg i 1) path_max)]
         (readlinkat_core_witness dirfd (in_arg i 1) i m).

Local Lemma readlinkat_core_witness_ok : forall dirfd pathp i m,
  readlinkat_core_spec dirfd pathp i m (readlinkat_core_witness dirfd pathp i m).
Proof.
  intros. unfold readlinkat_core_spec, readlinkat_core_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv beta iota;
    [|apply pure_ok|apply pure_ok].
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv beta iota; [apply unmodeled_intro|].
  destruct (path_eqb p []); cbv beta iota; [apply pure_ok|].
  destruct (path_eqb p dot_path || path_eqb p dotdot_path); cbv beta iota; [apply pure_ok|].
  destruct (statat_cwd_path m p) as [q|]; cbv beta iota; [|apply unmodeled_intro].
  destruct (fs_lookup (m_fs m) q); cbv beta iota; apply pure_ok.
Qed.

Lemma readlinkat_witness_ok : forall dirfd i m,
  readlinkat_spec dirfd i m (readlinkat_witness dirfd i m).
Proof.
  intros. unfold readlinkat_spec, readlinkat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct ((sint32 (in_arg i 3) <=? 0)%Z); cbv beta iota.
  - unfold err_ret, ret_only, ret_outcome. apply pure_ok.
  - apply record_copyins_outcome. apply readlinkat_core_witness_ok.
Qed.

(** newfstatat: a path errno (-ENAMETOOLONG / -EFAULT / -ENOENT) or
    [Unmodeled], and on a name relative to an O_PATH procfs descriptor
    the errno alternative of [Stat.newfstatat_proc_spec] (its
    [Syscall.errno_any] admits -ENOMEM) wherever that spec answers.
    Every other arm is deterministic. *)
Definition newfstatat_core_witness (dirfd pathp flag : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (modeled_statat_flags flag) then Unmodeled   (* unmodeled flag word *)
  else match read_cstr (in_mem i) pathp with
       | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m  (* over-long path *)
       | CstrFault => ret_outcome (errno_ret EFAULT) m          (* unreadable path *)
       | CstrOk p =>
           if path_eqb p [] then ret_outcome (errno_ret ENOENT) m  (* empty pathname *)
           else if negb (bv_eqb dirfd AT_FDCWD32) then
             (if newfstatat_proc_dir (m_fds m) dirfd p then
                (if negb (access_okb (in_arg i 2) STAT_SIZE)
                 then ret_outcome (errno_ret ENOMEM) m
                 else match read_bytes_map (in_wmem i) (in_arg i 2)
                              (Z_to_bv 64 STAT_SIZE) with
                      | None => Unmodeled                     (* partly writable buffer *)
                      | Some _ => ret_outcome (errno_ret ENOMEM) m
                      end)
              else Unmodeled)                                   (* unmodeled dirfd *)
           else if path_eqb p dot_path then Unmodeled              (* directory metadata *)
           else
             match statat_cwd_path m p with
             | None => Unmodeled
             | Some q =>
                 match fs_lookup (m_fs m) q with
                 | None => ret_outcome (errno_ret ENOENT) m
                 | Some _ => Unmodeled
                 end
             end
       end.

(** The pathname bytes [newfstatat_spec] records ride along on every
    outcome, exactly as [openat_witness] carries [openat]'s. *)
Definition newfstatat_witness (dirfd pathp flag : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  outcome_copyins
    [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (newfstatat_core_witness dirfd pathp flag i m).

Local Lemma newfstatat_core_witness_ok : forall dirfd pathp flag i m,
  newfstatat_core_spec dirfd pathp flag i m
    (newfstatat_core_witness dirfd pathp flag i m).
Proof.
  intros. unfold newfstatat_core_spec, newfstatat_core_witness.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl.
  - eapply bind_step; [apply input_ok|].
    cbv beta. eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta. apply unmodeled_intro.
  - destruct (read_cstr (in_mem i) pathp) as [p| |] eqn:Hp.
    2: { eapply bind_step; [apply input_ok|].
         cbv beta. eapply bind_step; [apply get_model_ok|].
         cbv beta iota zeta; srw Hp. apply pure_ok. }
    2: { eapply bind_step; [apply input_ok|].
         cbv beta. eapply bind_step; [apply get_model_ok|].
         cbv beta iota zeta; srw Hp. apply pure_ok. }
    destruct (path_eqb p []) eqn:Hpe.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hp; srw Hpe. apply pure_ok. }
    destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hp; srw Hpe.
      destruct (newfstatat_proc_dir (m_fds m) dirfd p) eqn:Hpd; cbv beta iota;
        [|apply unmodeled_intro].
      unfold newfstatat_proc_spec.
      eapply bind_step; [apply input_ok|]. cbv beta.
      destruct (negb (access_okb (in_arg i 2) STAT_SIZE)); cbv beta iota.
      { eapply bind_step;
          [unfold errno_any; apply (choose_ok _ ENOMEM); cbv beta; unfold ENOMEM, EINTR; lia|].
        apply pure_ok. }
      destruct (read_bytes_map (in_wmem i) (in_arg i 2) (Z_to_bv 64 STAT_SIZE));
        cbv beta iota; [|apply unmodeled_intro].
      apply alt_l.
      eapply bind_step;
        [unfold errno_any; apply (choose_ok _ ENOMEM); cbv beta; unfold ENOMEM, EINTR; lia|].
      apply pure_ok. }
    destruct (path_eqb p dot_path) eqn:Hdot.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hp; srw Hpe; srw Hdot.
      apply unmodeled_intro. }
    destruct (statat_cwd_path m p) as [q|] eqn:Hcp.
    2: { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hp; srw Hpe; srw Hdot; srw Hcp.
      apply unmodeled_intro. }
    destruct (fs_lookup (m_fs m) q) as [data|] eqn:Hfs.
    + eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hp; srw Hpe; srw Hdot; srw Hcp; srw Hfs.
      apply unmodeled_intro.
    + eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hp; srw Hpe; srw Hdot; srw Hcp; srw Hfs.
      apply pure_ok.
Qed.

(** ONE [struct stat] INSIDE [Uapi.stat_buf_wf]'s ENVELOPE, and the
    smallest that is: 128 bytes, zero everywhere except [st_mode], which
    is a bare S_IFREG.  It is the SEED the witnesses below patch a
    length into, never an answer the spec prefers — [Stat.fstat_file_spec]
    chooses over the whole envelope, and progress needs one member of
    that set named, not the likeliest one.  A real [struct stat] has a
    nonzero device, inode and block size; nothing here claims otherwise.

    S_IFREG rather than one of the six other types on purpose: it is the
    arm whose [st_size] obligation actually bites, so the witness
    exercises [Uapi.stat_size_ok]'s interesting half rather than
    discharging it vacuously. *)
Definition stat_witness_base : list byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 S_IFREG ++ Z_to_le_bytes 108 0.

Lemma stat_witness_base_wf : stat_buf_wf stat_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_witness_base_length : length stat_witness_base = 128%nat.
Proof. vm_compute. reflexivity. Qed.

(** The buffer each file arm's witness delivers: the seed above with the
    file's current length written into [st_size] on the branch that has
    no pin, and THE PIN ITSELF with the same patch on the branch that
    has one — because there the stable members are not the witness's to
    pick. *)
Definition fstat_witness_buf (n : nat) (pin : option (list byte)) : list byte :=
  match pin with
  | Some b0 => stat_set_size n b0
  | None => stat_set_size n stat_witness_base
  end.

(** fstat's file arms, mirroring [Stat.fstat_file_spec] branch for
    branch.  Deterministic even where the spec chooses: a witness names
    one admissible outcome, and these are the [choose]s resolved to
    [fstat_witness_buf]. *)
Definition fstat_file_witness (p : Fs.path) (statbuf : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match fs_lookup (m_fs m) p with
  | None => Unmodeled                          (* unlinked under an open fd *)
  | Some data =>
      if negb (access_okb statbuf STAT_SIZE) then ret_outcome (errno_ret EFAULT) m
      else
        match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
        | None => Unmodeled                    (* a partial [copy_to_user] *)
        | Some _ =>
            match statpin_lookup (m_statpins m) p with
            | Some b0 =>
                if negb (stat_buf_wf b0) then Unmodeled
                else Ok (mkEffect (Z_to_bv 64 0)
                          [(statbuf, fstat_witness_buf (length data) (Some b0))] [])
                        m []
            | None =>
                let bs := fstat_witness_buf (length data) None in
                Ok (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
                   (with_statpin p bs m) []
            end
        end
  end.

Lemma fstat_file_witness_ok : forall p statbuf i m,
  fstat_file_spec p statbuf i m (fstat_file_witness p statbuf i m).
Proof.
  intros p statbuf i m.
  unfold fstat_file_spec, fstat_file_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs; cbv iota;
    [|apply unmodeled_intro].
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha; cbv iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
    as [w|] eqn:Hw; cbv iota; [|apply unmodeled_intro].
  destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp; cbv iota.
  - destruct (negb (stat_buf_wf b0)) eqn:Hb0; cbv iota; [apply unmodeled_intro|].
    apply Bool.negb_false_iff in Hb0.
    pose proof (stat_buf_wf_length b0 Hb0) as Hlen.
    unfold fstat_witness_buf.
    eapply bind_step;
      [apply (choose_ok _ (stat_set_size (length data) b0)); repeat split|].
    + now apply stat_set_size_wf.
    + now apply stat_set_size_size_ok.
    + now apply stat_set_size_stable.
    + apply pure_ok.
  - unfold fstat_witness_buf.
    eapply bind_step;
      [apply (choose_ok _ (stat_set_size (length data) stat_witness_base));
       split|].
    + apply stat_set_size_wf, stat_witness_base_wf.
    + apply stat_set_size_size_ok, stat_witness_base_length.
    + eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

(** THE /dev/null SEED: [stat_witness_base] with the device's four
    members set — S_IFCHR, [st_rdev] 1:3, and the zero [st_size] and
    [st_blocks] the seed already carries — so that it satisfies
    [Uapi.stat_devnull_ok] outright.  Zero everywhere else, for the
    reason the file seed is.  [stat_urandom_witness_base] is the same
    seed with the random device's number. *)
Definition stat_chrdev_witness_base (rdev : Z) : list byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 S_IFCHR ++ Z_to_le_bytes 12 0
  ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 88 0.

Definition stat_devnull_witness_base : list byte :=
  stat_chrdev_witness_base DEVNULL_RDEV.

Definition stat_urandom_witness_base : list byte :=
  stat_chrdev_witness_base URANDOM_RDEV.

Lemma stat_devnull_witness_base_wf : stat_buf_wf stat_devnull_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_devnull_witness_base_ok :
  stat_devnull_ok stat_devnull_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_urandom_witness_base_wf : stat_buf_wf stat_urandom_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_urandom_witness_base_ok :
  stat_urandom_ok stat_urandom_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

(** fstat's character-device arm, mirroring [Stat.fstat_chrdev_spec]
    branch for branch, with the seed [base] delivered on the unpinned
    branch.  On the pinned branch the witness delivers THE PIN ITSELF:
    the spec has just checked it against both predicates, and the
    stable comparison is reflexive — there is no [st_size] to patch,
    because the device's is asserted to be 0 already. *)
Definition fstat_chrdev_witness (p : Fs.path) (ok : list byte -> bool)
    (base : list byte) (statbuf : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (access_okb statbuf STAT_SIZE) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => Unmodeled                    (* a partial [copy_to_user] *)
    | Some _ =>
        match statpin_lookup (m_statpins m) p with
        | Some b0 =>
            if negb (stat_buf_wf b0 && ok b0)%bool then Unmodeled
            else Ok (mkEffect (Z_to_bv 64 0) [(statbuf, b0)] []) m []
        | None =>
            Ok (mkEffect (Z_to_bv 64 0) [(statbuf, base)] [])
               (with_statpin p base m) []
        end
    end.

Lemma fstat_chrdev_witness_ok : forall p ok base,
  stat_buf_wf base = true -> ok base = true ->
  forall statbuf i m,
  fstat_chrdev_spec p ok statbuf i m (fstat_chrdev_witness p ok base statbuf i m).
Proof.
  intros p ok base Hwf Hok statbuf i m.
  unfold fstat_chrdev_spec, fstat_chrdev_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha; cbv iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
    as [w|] eqn:Hw; cbv iota; [|apply unmodeled_intro].
  destruct (statpin_lookup (m_statpins m) p) as [b0|] eqn:Hp; cbv iota.
  - destruct (negb (stat_buf_wf b0 && ok b0)%bool) eqn:Hb0; cbv iota;
      [apply unmodeled_intro|].
    apply Bool.negb_false_iff in Hb0. apply andb_true_iff in Hb0 as [HWF HOK].
    eapply bind_step;
      [apply (choose_ok _ b0); repeat split;
       [exact HWF | exact HOK | apply stat_stable_eqb_refl]|].
    apply pure_ok.
  - eapply bind_step;
      [apply (choose_ok _ base); split; [exact Hwf | exact Hok]|].
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

Definition fstat_devnull_witness (statbuf : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  fstat_chrdev_witness devnull_path stat_devnull_ok stat_devnull_witness_base
    statbuf i m.

Lemma fstat_devnull_witness_ok : forall statbuf i m,
  fstat_devnull_spec statbuf i m (fstat_devnull_witness statbuf i m).
Proof.
  intros. apply fstat_chrdev_witness_ok;
    [apply stat_devnull_witness_base_wf | apply stat_devnull_witness_base_ok].
Qed.

Definition fstat_urandom_witness (statbuf : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  fstat_chrdev_witness urandom_path stat_urandom_ok stat_urandom_witness_base
    statbuf i m.

Lemma fstat_urandom_witness_ok : forall statbuf i m,
  fstat_urandom_spec statbuf i m (fstat_urandom_witness statbuf i m).
Proof.
  intros. apply fstat_chrdev_witness_ok;
    [apply stat_urandom_witness_base_wf | apply stat_urandom_witness_base_ok].
Qed.

(** fstat (80) — -EBADF on a descriptor the process does not hold, a
    delivered [struct stat] on the four file kinds and on the two device
    kinds, and [Unmodeled] on the other five. *)
Definition fstat_witness (fd statbuf : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m   (* [vfs_fstat] resolves the fd first *)
  | Some (FdChannel _) => Unmodeled           (* struct stat: see [Stat.fstat_spec] *)
  | Some (FdFile p _)  => fstat_file_witness p statbuf i m
  | Some (FdFileW p _) => fstat_file_witness p statbuf i m
  | Some (FdFileA p _) => fstat_file_witness p statbuf i m
  | Some (FdFileRW p _) => fstat_file_witness p statbuf i m
  | Some FdDir         => Unmodeled
  | Some (FdSocket _)  => Unmodeled
  | Some (FdPipe _ _)  => Unmodeled
  | Some (FdDevNull _ _) => fstat_devnull_witness statbuf i m
  | Some FdUrandom => fstat_urandom_witness statbuf i m
  | Some (FdOpaque _) => Unmodeled
  end.

Lemma fstat_witness_ok : forall fd statbuf i m,
  fstat_spec fd statbuf i m (fstat_witness fd statbuf i m).
Proof.
  intros. unfold fstat_spec, fstat_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota;
    [destruct e; cbv iota;
       first [apply unmodeled_intro | apply fstat_file_witness_ok
             | apply fstat_devnull_witness_ok
             | apply fstat_urandom_witness_ok]
    |unfold ret_outcome; apply pure_ok].
Qed.

Lemma newfstatat_witness_ok : forall dirfd pathp flag i m,
  newfstatat_spec dirfd pathp flag i m (newfstatat_witness dirfd pathp flag i m).
Proof.
  intros. unfold newfstatat_spec, newfstatat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  apply record_copyins_outcome. apply newfstatat_core_witness_ok.
Qed.
