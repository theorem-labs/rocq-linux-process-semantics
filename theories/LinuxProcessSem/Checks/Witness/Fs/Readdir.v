(** * LinuxProcessSem.Checks.Witness.Fs.Readdir — the getdents64 (61) witness, and its proof

    Mirrors [Sys/Fs/Readdir.v], which answers to Linux [fs/readdir.c]:
    this file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.

(* -------------------------------------------------------------------------
   The /proc/self/fd listing
   ------------------------------------------------------------------------- *)

(** One record with [d_ino] 1, the given [d_off] bytes, [d_reclen], the
    [d_type] the entry's kind gives first, the name and its NUL.  [d_ino]
    is the environment's; no record Linux writes has 0 ([get_next_ino],
    fs/inode.c, read at v6.18.44; identical at v6.18.46). *)
Definition procfd_rec_bytes (e : procfd_ent) (doff : list byte) : list byte :=
  Z_to_le_bytes 8 1 ++ doff
  ++ Z_to_le_bytes 2 (dirent64_reclen (length (pfe_name e)))
  ++ [Z_to_bv 8 (if pfe_isfd e then DT_LNK else DT_DIR)]
  ++ pfe_name e ++ [Z_to_bv 8 0].

(** The witness's records: each [d_off] the next entry's position, and
    the end value [eend] after the last entry of the plan. *)
Fixpoint procfd_witness_bss (eend : Z) (es : list procfd_ent) (n : nat)
    : list (list byte) :=
  match n, es with
  | S n', e :: r =>
      let doff := match r with
                  | e' :: _ => Z_to_le_bytes 8 (pfe_pos e')
                  | [] => Z_to_le_bytes 8 eend
                  end in
      procfd_rec_bytes e doff :: procfd_witness_bss eend r n'
  | _, _ => []
  end.

Lemma procfd_rec_bytes_ok : forall e (doff_ok : list byte -> bool) d,
  length d = 8%nat -> doff_ok d = true ->
  dirent64_rec_ok e doff_ok (procfd_rec_bytes e d) = true.
Proof.
  intros e doff_ok d Hd Hok.
  do 8 (destruct d as [|? d]; [discriminate Hd|]). destruct d; [|discriminate Hd].
  unfold dirent64_rec_ok, procfd_rec_bytes. cbv zeta.
  destruct (pfe_isfd e) eqn:Hfd; generalize (pfe_name e) as nm; intros nm;
    rewrite !andb_true_iff; repeat split.
  all: try (apply Nat.eqb_eq; rewrite !length_app, !length_Z_to_le_bytes;
            cbn [length]; lia).
  all: try exact Hok.
  all: try (apply path_eqb_eq; reflexivity).
  all: try (apply path_eqb_eq;
            transitivity (firstn (length nm) (nm ++ [Z_to_bv 8 0])); [reflexivity|];
            rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn];
            apply app_nil_r).
  all: try (transitivity (Z.eqb (bv_unsigned (nth (length nm) (nm ++ [Z_to_bv 8 0])
                                              (Z_to_bv 8 1))) 0); [reflexivity|];
            rewrite nth_middle; reflexivity).
  all: reflexivity.
Qed.

Lemma procfd_witness_bss_ok : forall end_ok eend es n,
  end_ok (bytes_le_to_Z (Z_to_le_bytes 8 eend)) = true ->
  (n <= length es)%nat ->
  procfd_recs_ok end_ok es n (procfd_witness_bss eend es n) = true.
Proof.
  intros end_ok eend es n Hend. revert es.
  induction n as [|n IH]; intros es Hle; [destruct es; reflexivity|].
  destruct es as [|e r]; [cbn in Hle; lia|].
  destruct r as [|e' r'];
    cbn [procfd_witness_bss procfd_recs_ok]; apply andb_true_intro; split.
  - apply procfd_rec_bytes_ok; [apply length_Z_to_le_bytes | exact Hend].
  - destruct n; [reflexivity|]. cbn in Hle. lia.
  - apply procfd_rec_bytes_ok; [apply length_Z_to_le_bytes | apply path_eqb_refl].
  - exact (IH (e' :: r') ltac:(cbn [length] in Hle |- *; lia)).
Qed.

Lemma procfd_fit_le : forall es room, (procfd_fit es room <= length es)%nat.
Proof.
  induction es as [|e es IH]; intros room; cbn [procfd_fit length]; [lia|].
  destruct (dirent64_reclen (length (pfe_name e)) <=? room)%Z; [|lia].
  pose proof (IH (room - dirent64_reclen (length (pfe_name e)))%Z). lia.
Qed.

Lemma procfd_end_witness_ok : forall fds,
  forallb (fun kv => (bv_unsigned (fst kv) <? 2 ^ 31)%Z) fds = true ->
  procfd_end_ok fds (bytes_le_to_Z (Z_to_le_bytes 8 (2 ^ 31 + 2))) = true.
Proof.
  intros fds H.
  replace (bytes_le_to_Z (Z_to_le_bytes 8 (2 ^ 31 + 2))) with (2 ^ 31 + 2)%Z
    by (vm_compute; reflexivity).
  unfold procfd_end_ok. apply andb_true_intro; split; [reflexivity|].
  rewrite forallb_forall in H |- *. intros kv Hin. specialize (H kv Hin).
  apply Z.ltb_lt in H. apply Z.ltb_lt. lia.
Qed.

(** The listing's witness: the one answer the plan gives, with the
    records [procfd_witness_bss] builds (end value 2^31 + 2). *)
Definition procfd_getdents_witness (fd fl : word) (pos : option word)
    (dirent count : word) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match pos with
  | None => Unmodeled
  | Some pw =>
      if negb (procfd_in_range (m_fds m) (bv_unsigned pw)) then Unmodeled
      else
      let es := procfd_plan (m_fds m) (bv_unsigned pw) in
      let n := procfd_fit es (getdents64_ctx_count count) in
      let mpos := fun np : option word =>
        with_fds (fd_insert (m_fds m) fd (FdOpaque (OProcFdDir fl np))) m in
      match n, es with
      | O, [] => ret_outcome (Z_to_bv 64 0) (mpos None)
      | O, e :: _ => ret_outcome (errno_ret EINVAL) (mpos (Some (Z_to_bv 64 (pfe_pos e))))
      | S _, [] => Unmodeled
      | S _, e :: _ =>
          if negb (access_okb dirent (dirent64_reclen (length (pfe_name e))))
          then ret_outcome (errno_ret EFAULT) (mpos (Some (Z_to_bv 64 (pfe_pos e))))
          else
          let ws := firstn n es in
          let addrs := procfd_addrs dirent ws in
          if access_okb dirent (procfd_total ws) && procfd_writable (in_wmem i) addrs ws
          then
            let bss := procfd_witness_bss (2 ^ 31 + 2) es n in
            Ok (mkEffect (Z_to_bv 64 (procfd_total ws)) (combine addrs bss) [])
               (mpos (Some (Z_to_bv 64 (procfd_last_doff bss)))) []
          else Unmodeled
      end
  end.

Lemma procfd_getdents_witness_ok : forall fd fl pos dirent count i m,
  procfd_getdents_spec fd fl pos dirent count i m
    (procfd_getdents_witness fd fl pos dirent count i m).
Proof.
  intros fd fl pos dirent count i m.
  unfold procfd_getdents_spec, procfd_getdents_witness.
  destruct pos as [pw|]; [|apply unmodeled_intro].
  eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
  destruct (procfd_in_range (m_fds m) (bv_unsigned pw)) eqn:Hr;
    cbn [negb]; [|apply unmodeled_intro].
  destruct (procfd_fit (procfd_plan (m_fds m) (bv_unsigned pw)) (getdents64_ctx_count count))
    as [|n'] eqn:Hn;
  destruct (procfd_plan (m_fds m) (bv_unsigned pw)) as [|e es'] eqn:Hes;
  cbv beta iota zeta.
  - eapply bind_step; [unfold set_fds; apply modify_ok|]. cbv beta.
    unfold ret_only, ret_outcome. apply pure_ok.
  - eapply bind_step; [unfold set_fds; apply modify_ok|]. cbv beta.
    unfold err_ret, ret_only, ret_outcome. apply pure_ok.
  - apply unmodeled_intro.
  - destruct (negb (access_okb dirent (dirent64_reclen (length (pfe_name e))))).
    + eapply bind_step; [unfold set_fds; apply modify_ok|]. cbv beta.
      unfold err_ret, ret_only, ret_outcome. apply pure_ok.
    + eapply bind_step; [apply input_ok|]. cbv beta zeta.
      match goal with
      | |- context [if ?b then _ else Unmodeled] => destruct b eqn:Hw; [|apply unmodeled_intro]
      end.
      eapply bind_step.
      { apply choose_ok. apply procfd_witness_bss_ok.
        - apply procfd_end_witness_ok.
          unfold procfd_in_range in Hr. apply andb_true_iff in Hr as [_ Hr]. exact Hr.
        - pose proof (procfd_fit_le (e :: es') (getdents64_ctx_count count)) as Hle.
          rewrite Hn in Hle. exact Hle. }
      cbv beta.
      eapply bind_step; [unfold set_fds; apply modify_ok|]. cbv beta.
      apply pure_ok.
Qed.

(** [getdents64] on an opaque descriptor: the listing's witness, or the
    decline the spec gives every other kind. *)
Definition getdents64_opaque_witness (fd : word) (o : OpaqueFd) (dirent count : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match o with
  | OProcFdDir fl pos => procfd_getdents_witness fd fl pos dirent count i m
  | OProcPath _ | OProcFile _ | OEventFd _ | ONsFile _ | OSignalFd _ _ => Unmodeled
  end.

Lemma getdents64_opaque_witness_ok : forall fd o dirent count i m,
  getdents64_opaque_spec fd o dirent count i m (getdents64_opaque_witness fd o dirent count i m).
Proof.
  intros fd o dirent count i m.
  destruct o; cbn [getdents64_opaque_spec getdents64_opaque_witness];
    try apply unmodeled_intro.
  apply procfd_getdents_witness_ok.
Qed.

(** On the directory arm the witness takes -EINVAL rather than the
    injected -ENOENT: it is the answer the model actually derives from
    [count], while a directory removed out from under the fd is a
    condition no modeled state decides.  Above the small-buffer band,
    failing closed is itself the admissible outcome. *)
Definition getdents64_witness (fd dirent count : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdFile _ _)  => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdFileW _ _) => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdFileA _ _) => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdFileRW _ _) => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdPipe _ _)  => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdSocket _)  => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdDevNull _ _) => ret_outcome (errno_ret ENOTDIR) m
  | Some FdUrandom => ret_outcome (errno_ret ENOTDIR) m
  | Some (FdOpaque o) => getdents64_opaque_witness fd o dirent count i m
  | Some FdDir =>
      if getdents64_no_room count
      then ret_outcome (errno_ret EINVAL) m
      else Unmodeled
  end.

Lemma getdents64_witness_ok : forall fd dirent count i m,
  getdents64_spec fd dirent count i m (getdents64_witness fd dirent count i m).
Proof.
  intros fd dirent count i m. unfold getdents64_spec, getdents64_witness.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; [destruct e|];
    (eapply bind_step; [apply get_model_ok|]);
    cbv beta iota zeta; srw Hfd; try solve [apply pure_ok | apply unmodeled_intro].
  all: try (apply getdents64_opaque_witness_ok).
  destruct (getdents64_no_room count) eqn:Hroom; [|apply unmodeled_intro].
  apply alt_r. unfold err_ret, ret_only, ret_outcome. apply pure_ok.
Qed.
