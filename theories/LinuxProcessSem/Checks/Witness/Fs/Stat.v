(** * LinuxProcessSem.Checks.Witness.Fs.Stat — the readlinkat (78), newfstatat (79) and fstat (80) witnesses, and their proofs

    Mirrors [Sys/Fs/Stat.v], which answers to Linux [fs/stat.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

(** The copy of a found link's body: the whole count delivered. *)
Local Definition readlink_copy_witness (i : SyscallInput) (b : path)
    (buf bufsiz : word) (m : Model) : outcome SyscallEffect :=
  let n := readlink_count b bufsiz in
  if readlink_copy_faults buf n then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_wmem i) buf (Z_to_bv 64 (Z.of_nat n)) with
    | None => Unmodeled
    | Some _ =>
        Ok (mkEffect (Z_to_bv 64 (Z.of_nat n))
              (delivered_writes buf (firstn n (Fs.link_text b))) []) m []
    end.

Local Lemma readlink_copy_witness_ok : forall i b buf bufsiz m,
  readlink_copy_spec i b buf bufsiz i m (readlink_copy_witness i b buf bufsiz m).
Proof.
  intros. unfold readlink_copy_spec, readlink_copy_witness. cbv zeta.
  destruct (readlink_copy_faults buf (readlink_count b bufsiz)); cbv iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  destruct (read_bytes_map (in_wmem i) buf
              (Z_to_bv 64 (Z.of_nat (readlink_count b bufsiz)))); cbv iota;
    [apply pure_ok|apply unmodeled_intro].
Qed.

Local Definition readlinkat_body_witness (i : SyscallInput)
    (dirfd pathp buf bufsiz : word) (m : Model) : outcome SyscallEffect :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | CstrFault => ret_outcome (errno_ret EFAULT) m
  | CstrOk p =>
      if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled
      else if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
      else
        let '(r, _, _) := Fs.resolve (Fs.WalkFull false false) (m_fs m) (m_cwd m) p in
        match r with
        | Fs.RFound _ (ELink b) => readlink_copy_witness i b buf bufsiz m
        | Fs.RFound _ _ => ret_outcome (errno_ret EINVAL) m
        | Fs.RMissing _ _ => ret_outcome (errno_ret ENOENT) m
        | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
        | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
        | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
        | Fs.ROutside => Unmodeled
        | Fs.RParent _ _ => Unmodeled
        end
  end.

Definition readlinkat_witness (dirfd pathp buf bufsiz : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if (sint32 bufsiz <=? 0)%Z then ret_outcome (errno_ret EINVAL) m
  else
    outcome_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
      (readlinkat_body_witness i dirfd pathp buf bufsiz m).

Lemma readlinkat_witness_ok : forall dirfd pathp buf bufsiz i m,
  readlinkat_spec dirfd pathp buf bufsiz i m
    (readlinkat_witness dirfd pathp buf bufsiz i m).
Proof.
  intros. unfold readlinkat_spec, readlinkat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct ((sint32 bufsiz <=? 0)%Z); cbv iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  apply getname_refusals_intro.
  apply record_copyins_outcome. apply walk_refusals_intro.
  unfold readlinkat_body_spec.
  unfold readlinkat_body_witness.
  destruct (read_cstr (in_mem i) pathp) as [p| |]; cbv iota;
    try (unfold err_ret, ret_only, ret_outcome; apply pure_ok).
  destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota;
    [apply unmodeled_intro|].
  destruct (path_eqb p []); cbv iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  destruct (Fs.resolve (Fs.WalkFull false false) (m_fs m) (m_cwd m) p) as [[r lk] ts];
    cbv iota beta zeta.
  destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
    try (unfold err_ret, ret_only, ret_outcome; apply pure_ok);
    try apply unmodeled_intro.
  destruct e as [ino| |dk|lb]; cbv iota;
    try (unfold err_ret, ret_only, ret_outcome; apply pure_ok).
  apply readlink_copy_witness_ok.
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

(** The buffer each file arm's witness delivers: the seed above, or THE
    PIN ITSELF on the branch that has one -- because there the stable
    members are not the witness's to pick -- with the file's current
    length written into [st_size] and its link count into [st_nlink]. *)
Definition fstat_witness_buf (n nl : nat) (pin : option (list byte)) : list byte :=
  match pin with
  | Some b0 => stat_set_nlink nl (stat_set_size n b0)
  | None => stat_set_nlink nl (stat_set_size n stat_witness_base)
  end.

(** The file seed is S_IFREG, and the head [Uapi.stat_set_size] and
    [Uapi.stat_set_nlink] leave alone keeps it so. *)
Lemma stat_witness_base_reg : stat_is_reg stat_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_set_size_reg : forall n bs,
  (48 <= length bs)%nat -> stat_is_reg (stat_set_size n bs) = stat_is_reg bs.
Proof.
  intros n bs Hlen. unfold stat_is_reg, stat_ifmt.
  rewrite (stat_field_le_head ST_MODE_OFF 4 (stat_set_size n bs) bs);
    [reflexivity | unfold ST_MODE_OFF; lia | apply stat_set_size_head; exact Hlen].
Qed.

(** Everything [Stat.fstat_file_spec]'s [choose] asks of a delivery
    built over a well-formed S_IFREG buffer [b]. *)
Lemma fstat_witness_buf_ok : forall n nl b,
  stat_buf_wf b = true -> stat_is_reg b = true ->
  stat_buf_wf (stat_set_nlink nl (stat_set_size n b)) = true
  /\ stat_is_reg (stat_set_nlink nl (stat_set_size n b)) = true
  /\ stat_size_ok n (stat_set_nlink nl (stat_set_size n b)) = true
  /\ stat_nlink_ok nl (stat_set_nlink nl (stat_set_size n b)) = true
  /\ stat_stable_eqb (stat_set_nlink nl (stat_set_size n b)) b = true.
Proof.
  intros n nl b Hwf Hreg.
  pose proof (stat_buf_wf_length b Hwf) as Hlen.
  assert (Hlen' : length (stat_set_size n b) = 128%nat)
    by now apply stat_set_size_length.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - apply stat_set_nlink_wf, stat_set_size_wf, Hwf.
  - rewrite stat_set_nlink_reg by lia. rewrite stat_set_size_reg by lia. exact Hreg.
  - rewrite stat_set_nlink_size_ok by lia. now apply stat_set_size_size_ok.
  - apply stat_set_nlink_nlink_ok. lia.
  - eapply stat_stable_eqb_trans; [apply stat_set_nlink_stable; exact Hlen'|].
    now apply stat_set_size_stable.
Qed.

(** fstat's file arms, mirroring [Stat.fstat_file_spec] branch for
    branch.  Deterministic even where the spec chooses: a witness names
    one admissible outcome, and these are the [choose]s resolved to
    [fstat_witness_buf].  On the pinned branch the model is
    [Stat.file_pin_after]'s, which is the same model: the buffer
    repeats the pin's mode. *)
Definition fstat_file_witness (ino : Fs.ino) (statbuf : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  let n := length (Fs.fs_ino_data (m_fs m) ino) in
  let nl := Fs.fs_ino_nlink (m_fs m) ino in
  if negb (access_okb statbuf STAT_SIZE) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => Unmodeled                    (* a partial [copy_to_user] *)
    | Some _ =>
        match statpin_lookup (m_statpins m) (IdIno ino) with
        | Some sp =>
            if negb (stat_buf_wf (sp_bytes sp) && stat_is_reg (sp_bytes sp))%bool
            then Unmodeled
            else
              let bs := fstat_witness_buf n nl (Some (sp_bytes sp)) in
              Ok (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
                 (file_pin_after ino sp bs m) []
        | None =>
            let bs := fstat_witness_buf n nl None in
            Ok (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
               (with_statpin (IdIno ino) (mkStatPin bs None) m) []
        end
    end.

Lemma fstat_file_witness_ok : forall ino statbuf i m,
  fstat_file_spec ino statbuf i m (fstat_file_witness ino statbuf i m).
Proof.
  intros ino statbuf i m.
  unfold fstat_file_spec, fstat_file_witness. cbv zeta.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha; cbv iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
    as [w|] eqn:Hw; cbv iota; [|apply unmodeled_intro].
  destruct (statpin_lookup (m_statpins m) (IdIno ino)) as [sp|] eqn:Hp; cbv iota.
  - destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_reg (sp_bytes sp))%bool)
      eqn:Hb0; cbv iota; [apply unmodeled_intro|].
    apply Bool.negb_false_iff in Hb0. apply andb_true_iff in Hb0 as [Hb0 HREG].
    unfold fstat_witness_buf.
    destruct (fstat_witness_buf_ok (length (Fs.fs_ino_data (m_fs m) ino))
                (Fs.fs_ino_nlink (m_fs m) ino) (sp_bytes sp) Hb0 HREG)
      as (H1 & H2 & H3 & H4 & H5).
    eapply bind_step;
      [apply (choose_ok _ (stat_set_nlink (Fs.fs_ino_nlink (m_fs m) ino)
                             (stat_set_size (length (Fs.fs_ino_data (m_fs m) ino))
                                (sp_bytes sp))));
       exact (conj H1 (conj H2 (conj H3 (conj H4 H5))))|].
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - unfold fstat_witness_buf.
    destruct (fstat_witness_buf_ok (length (Fs.fs_ino_data (m_fs m) ino))
                (Fs.fs_ino_nlink (m_fs m) ino) stat_witness_base
                stat_witness_base_wf stat_witness_base_reg)
      as (H1 & H2 & H3 & H4 & _).
    eapply bind_step;
      [apply (choose_ok _ (stat_set_nlink (Fs.fs_ino_nlink (m_fs m) ino)
                             (stat_set_size (length (Fs.fs_ino_data (m_fs m) ino))
                                stat_witness_base)));
       exact (conj H1 (conj H2 (conj H3 H4)))|].
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
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

(** The pinned-identity arm, mirroring [Stat.fstat_pinned_spec] branch
    for branch, with the seed [base] delivered on the unpinned branch.
    On the pinned branch the witness delivers THE PIN ITSELF: the spec
    has just checked it against both predicates, and the link-count and
    stable comparisons are reflexive -- there is no [st_size] to patch,
    because the device's is asserted to be 0 already and a link's was
    written into its seed when the pin was made. *)
Definition fstat_pinned_witness (id : StatId) (ok : list byte -> bool)
    (base : list byte) (statbuf : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (access_okb statbuf STAT_SIZE) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => Unmodeled                    (* a partial [copy_to_user] *)
    | Some _ =>
        match statpin_lookup (m_statpins m) id with
        | Some sp =>
            if negb (stat_buf_wf (sp_bytes sp) && ok (sp_bytes sp))%bool then Unmodeled
            else Ok (mkEffect (Z_to_bv 64 0) [(statbuf, sp_bytes sp)] []) m []
        | None =>
            Ok (mkEffect (Z_to_bv 64 0) [(statbuf, base)] [])
               (with_statpin id (mkStatPin base None) m) []
        end
    end.

Lemma fstat_pinned_witness_ok : forall id ok base,
  stat_buf_wf base = true -> ok base = true ->
  forall statbuf i m,
  fstat_pinned_spec id ok statbuf i m (fstat_pinned_witness id ok base statbuf i m).
Proof.
  intros id ok base Hwf Hok statbuf i m.
  unfold fstat_pinned_spec, fstat_pinned_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha; cbv iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
    as [w|] eqn:Hw; cbv iota; [|apply unmodeled_intro].
  destruct (statpin_lookup (m_statpins m) id) as [sp|] eqn:Hp; cbv iota.
  - destruct (negb (stat_buf_wf (sp_bytes sp) && ok (sp_bytes sp))%bool) eqn:Hb0;
      cbv iota; [apply unmodeled_intro|].
    apply Bool.negb_false_iff in Hb0. apply andb_true_iff in Hb0 as [HWF HOK].
    eapply bind_step;
      [apply (choose_ok _ (sp_bytes sp));
       exact (conj HWF (conj HOK (conj (stat_pin_held_refl _ _)
                                       (stat_stable_eqb_refl _))))|].
    apply pure_ok.
  - eapply bind_step;
      [apply (choose_ok _ base); exact (conj Hwf Hok)|].
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

(** A device node: its key's pin ([Stat.fstat_chrdev_spec]). *)
Definition fstat_chrdev_witness (k : Fs.path) (ok : list byte -> bool)
    (base : list byte) (statbuf : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  fstat_pinned_witness (IdDev k) ok base statbuf i m.

Lemma fstat_chrdev_witness_ok : forall k ok base,
  stat_buf_wf base = true -> ok base = true ->
  forall statbuf i m,
  fstat_chrdev_spec k ok statbuf i m (fstat_chrdev_witness k ok base statbuf i m).
Proof.
  intros. unfold fstat_chrdev_spec, fstat_chrdev_witness.
  now apply fstat_pinned_witness_ok.
Qed.

(** THE LINK SEED: [stat_witness_base] with S_IFLNK in place of S_IFREG,
    and the body's length patched into [st_size] by [stat_set_size]. *)
Definition stat_lnk_witness_base : list byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 S_IFLNK ++ Z_to_le_bytes 108 0.

Lemma stat_lnk_witness_base_wf : stat_buf_wf stat_lnk_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_lnk_witness_base_lnk : stat_is_lnk stat_lnk_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_lnk_witness_base_length : length stat_lnk_witness_base = 128%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_set_size_lnk : forall n bs,
  (48 <= length bs)%nat -> stat_is_lnk (stat_set_size n bs) = stat_is_lnk bs.
Proof.
  intros n bs Hlen. unfold stat_is_lnk, stat_ifmt.
  rewrite (stat_field_le_head ST_MODE_OFF 4 (stat_set_size n bs) bs);
    [reflexivity | unfold ST_MODE_OFF; lia | apply stat_set_size_head; exact Hlen].
Qed.

(** A link the walk did not follow: the link seed with the body's
    length ([Stat.fstat_link_spec]). *)
Definition fstat_link_witness (k b : Fs.path) (statbuf : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  fstat_pinned_witness (IdLink k)
    (fun bs => stat_is_lnk bs && stat_lnk_size_ok (length (Fs.link_text b)) bs)%bool
    (stat_set_size (length (Fs.link_text b)) stat_lnk_witness_base) statbuf i m.

Lemma fstat_link_witness_ok : forall k b statbuf i m,
  fstat_link_spec k b statbuf i m (fstat_link_witness k b statbuf i m).
Proof.
  intros k b statbuf i m. unfold fstat_link_spec, fstat_link_witness.
  apply fstat_pinned_witness_ok.
  - apply stat_set_size_wf, stat_lnk_witness_base_wf.
  - rewrite stat_set_size_lnk by (rewrite stat_lnk_witness_base_length; lia).
    rewrite stat_lnk_witness_base_lnk. cbn [andb].
    apply stat_set_size_lnk_size_ok, stat_lnk_witness_base_length.
Qed.

(** THE DIRECTORY SEED: [stat_witness_base] with S_IFDIR in place of
    S_IFREG, and zero everywhere else.  A real directory reports a
    nonzero device, inode and block size; the seed is one member of the
    envelope the spec chooses over, not the likeliest one. *)
Definition stat_dir_witness_base : list byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 S_IFDIR ++ Z_to_le_bytes 108 0.

Lemma stat_dir_witness_base_wf : stat_buf_wf stat_dir_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_dir_witness_base_is_dir : stat_is_dir stat_dir_witness_base = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stat_dir_witness_base_length : length stat_dir_witness_base = 128%nat.
Proof. vm_compute. reflexivity. Qed.

(** The link count a directory witness writes: the rule the pin holds,
    or the counting rule where none is chosen yet -- either satisfies
    [Stat.dir_nlink_ok], which accepts both counts until the first stat
    that tells them apart. *)
Definition dir_witness_nlink (d : Fs.DirLinks) (r : option DirRule) : nat :=
  match r with
  | Some r => dir_rule_count d r
  | None => Fs.dl_counting d
  end.

Lemma dir_witness_nlink_ok : forall d r bs,
  (20 <= length bs)%nat ->
  dir_nlink_ok d r (stat_set_nlink (dir_witness_nlink d r) bs) = true.
Proof.
  intros d r bs Hlen. unfold dir_nlink_ok, dir_witness_nlink.
  destruct r as [r|].
  - now apply stat_set_nlink_nlink_ok.
  - rewrite stat_set_nlink_nlink_ok by exact Hlen. reflexivity.
Qed.

(** fstat's directory arm, mirroring [Stat.fstat_dir_spec] branch for
    branch.  On the pinned branch it delivers THE PIN ITSELF with the
    link count the pin's rule gives: the spec has just checked the pin
    against both predicates, and neither [Uapi.stat_stable_eqb] nor the
    [st_blocks] [Stat.stat_pin_held] holds reads [st_nlink]. *)
Definition fstat_dir_witness (k : Fs.path) (statbuf : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  let d := Fs.fs_dir_links (m_fs m) k in
  if negb (access_okb statbuf STAT_SIZE) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => Unmodeled                    (* a partial [copy_to_user] *)
    | Some _ =>
        match statpin_lookup (m_statpins m) (IdDir k) with
        | Some sp =>
            if negb (stat_buf_wf (sp_bytes sp) && stat_is_dir (sp_bytes sp))%bool
            then Unmodeled
            else
              let bs := stat_set_nlink (dir_witness_nlink d (sp_rule sp)) (sp_bytes sp) in
              Ok (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
                 (dir_pin_after k d sp bs m) []
        | None =>
            let bs := stat_set_nlink (Fs.dl_counting d) stat_dir_witness_base in
            Ok (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
               (with_statpin (IdDir k) (mkStatPin bs (dir_rule_after d None bs)) m) []
        end
    end.

Lemma fstat_dir_witness_ok : forall k statbuf i m,
  fstat_dir_spec k statbuf i m (fstat_dir_witness k statbuf i m).
Proof.
  intros k statbuf i m. unfold fstat_dir_spec, fstat_dir_witness. cbv zeta.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb statbuf STAT_SIZE)) eqn:Ha; cbv iota;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE))
    as [w|] eqn:Hw; cbv iota; [|apply unmodeled_intro].
  destruct (statpin_lookup (m_statpins m) (IdDir k)) as [sp|] eqn:Hp; cbv iota.
  - destruct (negb (stat_buf_wf (sp_bytes sp) && stat_is_dir (sp_bytes sp))%bool)
      eqn:Hb0; cbv iota; [apply unmodeled_intro|].
    apply Bool.negb_false_iff in Hb0. apply andb_true_iff in Hb0 as [HWF HOK].
    pose proof (stat_buf_wf_length _ HWF) as Hlen.
    eapply bind_step;
      [apply (choose_ok _ (stat_set_nlink
                             (dir_witness_nlink (Fs.fs_dir_links (m_fs m) k) (sp_rule sp))
                             (sp_bytes sp)));
       refine (conj _ (conj _ (conj _ (conj _ _))))|].
    + now apply stat_set_nlink_wf.
    + rewrite stat_set_nlink_dir by lia. exact HOK.
    + apply dir_witness_nlink_ok. lia.
    + cbn [stat_pin_held]. apply stat_set_nlink_field_eqb; [unfold ST_BLOCKS_OFF; lia | lia].
    + now apply stat_set_nlink_stable.
    + eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - eapply bind_step;
      [apply (choose_ok _ (stat_set_nlink (Fs.dl_counting (Fs.fs_dir_links (m_fs m) k))
                             stat_dir_witness_base));
       refine (conj _ (conj _ _))|].
    + apply stat_set_nlink_wf, stat_dir_witness_base_wf.
    + rewrite stat_set_nlink_dir by (rewrite stat_dir_witness_base_length; lia).
      apply stat_dir_witness_base_is_dir.
    + change (Fs.dl_counting (Fs.fs_dir_links (m_fs m) k))
        with (dir_witness_nlink (Fs.fs_dir_links (m_fs m) k) None).
      apply dir_witness_nlink_ok. rewrite stat_dir_witness_base_length. lia.
    + eapply bind_step; [apply modify_ok|]. apply pure_ok.
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
    delivered [struct stat] on the four file kinds, the directory and
    the two device kinds, and [Unmodeled] on the other six. *)
Definition fstat_witness (fd statbuf : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m   (* [vfs_fstat] resolves the fd first *)
  | Some (FdChannel _) => Unmodeled           (* struct stat: see [Stat.fstat_spec] *)
  | Some (FdFile p _)  => fstat_file_witness p statbuf i m
  | Some (FdFileW p _) => fstat_file_witness p statbuf i m
  | Some (FdFileA p _) => fstat_file_witness p statbuf i m
  | Some (FdFileRW p _) => fstat_file_witness p statbuf i m
  | Some (FdDir k)     => fstat_dir_witness k statbuf i m
  | Some (FdSocket _)  => Unmodeled
  | Some (FdStream _ _ _) => Unmodeled
  | Some (FdDgram _)   => Unmodeled
  | Some (FdEventfd _) => Unmodeled
  | Some (FdPipe _ _)  => Unmodeled
  | Some (FdDevNull _ _) => fstat_devnull_witness statbuf i m
  | Some (FdUrandom _ _) => fstat_urandom_witness statbuf i m
  end.

Lemma fstat_witness_ok : forall fd statbuf i m,
  fstat_spec fd statbuf i m (fstat_witness fd statbuf i m).
Proof.
  intros. unfold fstat_spec, fstat_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota;
    [|unfold ret_outcome; apply pure_ok].
  destruct e as [ch|p cur|p cur|p cur|p cur|k|sk|pid pw|rd wr|urd uwr|sid side st|ctx|fam];
    cbv iota.
  all: first [apply unmodeled_intro | apply fstat_file_witness_ok
             | apply fstat_dir_witness_ok
             | apply fstat_devnull_witness_ok
             | apply fstat_urandom_witness_ok].
Qed.

(** newfstatat (79): the path errnos, the declines, and — new in R22 —
    the SUCCESS, one row per resolved entry kind.  Deterministic even
    where the spec chooses: a witness names one admissible outcome, and
    these are the [choose]s resolved to the seeds above. *)
Definition stat_entry_witness (k : Fs.path) (e : Entry) (statbuf : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match e with
  | EFile ino => fstat_file_witness ino statbuf i m
  | EDir => fstat_dir_witness k statbuf i m
  | EDev DevNull =>
      fstat_chrdev_witness k stat_devnull_ok stat_devnull_witness_base statbuf i m
  | EDev DevUrandom =>
      fstat_chrdev_witness k stat_urandom_ok stat_urandom_witness_base statbuf i m
  | ELink b => fstat_link_witness k b statbuf i m
  end.

Lemma stat_entry_witness_ok : forall k e statbuf i m,
  stat_entry_spec k e statbuf i m (stat_entry_witness k e statbuf i m).
Proof.
  intros k e statbuf i m. unfold stat_entry_spec, stat_entry_witness.
  destruct e as [ino| |dk|body]; cbv iota.
  - apply fstat_file_witness_ok.
  - apply fstat_dir_witness_ok.
  - destruct dk; cbv iota.
    + apply fstat_chrdev_witness_ok;
        [apply stat_devnull_witness_base_wf|apply stat_devnull_witness_base_ok].
    + apply fstat_chrdev_witness_ok;
        [apply stat_urandom_witness_base_wf|apply stat_urandom_witness_base_ok].
  - apply fstat_link_witness_ok.
Qed.

Definition newfstatat_core_witness (dirfd pathp statbuf flag : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (modeled_statat_flags flag) then Unmodeled   (* unmodeled flag word *)
  else if statat_null_name pathp flag then Unmodeled   (* NULL under AT_EMPTY_PATH *)
  else match read_cstr (in_mem i) pathp with
       | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m  (* over-long path *)
       | CstrFault => ret_outcome (errno_ret EFAULT) m          (* unreadable path *)
       | CstrOk p =>
           if path_eqb p [] then
             if negb (statat_empty_path flag) then ret_outcome (errno_ret ENOENT) m
             else if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled
             else
               match Fs.fs_lookup (m_fs m) (m_cwd m) with
               | Some e => stat_entry_witness (m_cwd m) e statbuf i m
               | None => Unmodeled
               end
           else if negb (bv_eqb dirfd AT_FDCWD32) then Unmodeled   (* unmodeled dirfd *)
           else
             let '(r, _, _) := Fs.resolve (statat_walk_mode flag) (m_fs m) (m_cwd m) p in
             match r with
             | Fs.RFound k e => stat_entry_witness k e statbuf i m
             | Fs.RMissing _ _ => ret_outcome (errno_ret ENOENT) m
             | Fs.RNotDir _ => ret_outcome (errno_ret ENOTDIR) m
             | Fs.RAbsent _ => ret_outcome (errno_ret ENOENT) m
             | Fs.RLoop => ret_outcome (errno_ret ELOOP) m
             | Fs.ROutside => Unmodeled
             | Fs.RParent _ _ => Unmodeled
             end
       end.

(** The pathname bytes [newfstatat_spec] records ride along on every
    outcome, exactly as [openat_witness] carries [openat]'s. *)
Definition newfstatat_witness (dirfd pathp statbuf flag : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  outcome_copyins
    [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (newfstatat_core_witness dirfd pathp statbuf flag i m).

Local Lemma newfstatat_core_witness_ok : forall dirfd pathp statbuf flag i m,
  newfstatat_core_spec dirfd pathp statbuf flag i m
    (newfstatat_core_witness dirfd pathp statbuf flag i m).
Proof.
  intros. unfold newfstatat_core_spec, newfstatat_core_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (modeled_statat_flags flag)) eqn:Hfl; cbv iota;
    [apply unmodeled_intro|].
  destruct (statat_null_name pathp flag); cbv iota;
    [apply unmodeled_intro|].
  destruct (statat_getname_runs i pathp flag); cbv iota;
    [apply walk_refusals_intro|].
  all: unfold newfstatat_body_spec.
  all: destruct (read_cstr (in_mem i) pathp) as [p| |] eqn:Hp; cbv iota;
    [|unfold ret_outcome; apply pure_ok|unfold ret_outcome; apply pure_ok].
  all: destruct (path_eqb p []) eqn:Hpe; cbv iota.
  1,3: destruct (negb (statat_empty_path flag)); cbv iota;
      [unfold ret_outcome; apply pure_ok|];
    destruct (negb (bv_eqb dirfd AT_FDCWD32)); cbv iota; [apply unmodeled_intro|];
    destruct (Fs.fs_lookup (m_fs m) (m_cwd m)) as [e|]; cbv iota;
      [apply stat_entry_witness_ok|apply unmodeled_intro].
  all: destruct (negb (bv_eqb dirfd AT_FDCWD32)) eqn:Hd; cbv iota;
      [apply unmodeled_intro|].
  all: destruct (Fs.resolve (statat_walk_mode flag) (m_fs m) (m_cwd m) p)
      as [[r lk] ts] eqn:Hr.
  all: cbv iota zeta.
  all: destruct r as [k e|par nm|q|q| | |dr nm']; cbv iota;
      try (unfold ret_outcome; apply pure_ok); try apply unmodeled_intro.
  all: apply stat_entry_witness_ok.
Qed.

Lemma newfstatat_witness_ok : forall dirfd pathp statbuf flag i m,
  newfstatat_spec dirfd pathp statbuf flag i m
    (newfstatat_witness dirfd pathp statbuf flag i m).
Proof.
  intros. unfold newfstatat_spec, newfstatat_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (statat_getname_runs i pathp flag); cbv iota;
    try apply getname_refusals_intro;
    apply record_copyins_outcome; apply newfstatat_core_witness_ok.
Qed.
