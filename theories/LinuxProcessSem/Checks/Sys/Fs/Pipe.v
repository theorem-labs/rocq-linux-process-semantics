(** * LinuxProcessSem.Checks.Sys.Fs.Pipe — the pipe2 (59) checker, and its proofs

    Mirrors [Sys/Fs/Pipe.v], which answers to Linux [fs/pipe.c]: this
    file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad RiscvSemantics Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Uaccess Fs.ReadWrite.

(** Abbreviations for the two descriptors [pipe2] hands out and the model
    it leaves behind, so the acceptor's success test and the proofs below
    talk about the same terms. *)
Definition pipe2_fdr (m : Model) : word := alloc_fd (m_fds m).

Definition pipe2_fds1 (m : Model) (id : word) : list (word * FdEntry) :=
  fd_insert (m_fds m) (pipe2_fdr m) (FdPipe id false).

Definition pipe2_fdw (m : Model) (id : word) : word :=
  alloc_fd (pipe2_fds1 m id).

Definition pipe2_model (m : Model) (id : word) : Model :=
  with_pipes (pipe_insert (m_pipes m) id ([], 0%Z))
    (with_fds (fd_insert (pipe2_fds1 m id) (pipe2_fdw m id) (FdPipe id true)) m).

(** [Specs.pipe2_spec] as an acceptor.  Two admissible shapes on the
    branches that can succeed — the injected environment errno, and the
    single 8-byte copy-out — so the effect's own write list is what
    picks between them. *)
Definition check_pipe2 (i : SyscallInput) (fildes flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags) pipe2_flags_mask) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (Z.eqb (Z.ldiff (bv_unsigned flags) pipe2_ignored_flags) 0)
  then CheckUnmodeled
  else
  let id := pipe_new_id (m_pipes m) in
  match pipe_lookup (m_pipes m) id with
  | Some _ => CheckUnmodeled
  | None =>
      if negb (access_okb fildes 8)
      then (* [access_ok] refuses the range: -EFAULT with nothing installed.
              Mirrors [Fs.Pipe.pipe2_spec]'s guard of the same name; the
              argument is there. *)
        match eff with
        | mkEffectU ret [] [] [] [] [] =>
            if errno_ret_in (EFAULT :: pipe2_errnos) ret
            then CheckOk m [] else CheckReject
        | _ => CheckReject
        end
      else
      match read_bytes_map (in_wmem i) fildes (Z_to_bv 64 8) with
      | Some _ =>
          match eff with
          | mkEffectU ret [] [] [] [] [] =>
              if errno_ret_in pipe2_errnos ret then CheckOk m [] else CheckReject
          | mkEffectU ret [(a, bs)] [] [] [] [] =>
              match fd_lookup (m_fds m) (pipe2_fdr m) with
              | Some _ => CheckReject   (* no free read-end fd: only the errno stands *)
              | None =>
                  match fd_lookup (pipe2_fds1 m id) (pipe2_fdw m id) with
                  | Some _ => CheckReject   (* no free write-end fd *)
                  | None =>
                      if bv_eqb ret (Z_to_bv 64 0) && bv_eqb a fildes
                         && listN_eqb bs (pipe_fd_bytes (pipe2_fdr m)
                                            (pipe2_fdw m id))
                      then CheckOk (pipe2_model m id) []
                      else CheckReject
                  end
              end
          | _ => CheckReject
          end
      | None =>
          match read_bytes_map (in_wmem i) fildes (Z_to_bv 64 1) with
          | None =>
              match eff with
              | mkEffectU ret [] [] [] [] [] =>
                  if errno_ret_in (EFAULT :: pipe2_errnos) ret
                  then CheckOk m [] else CheckReject
              | _ => CheckReject
              end
          | Some _ => CheckUnmodeled   (* partially writable destination *)
          end
      end
  end.

Lemma check_pipe2_sound_ok : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs ->
  pipe2_spec fildes flags i m (Ok eff m' evs).
Proof.
  intros i fildes flags eff m m' evs H.
  unfold check_pipe2 in H. unfold pipe2_spec.
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_flags_mask =? 0)%Z)
    eqn:Hbad.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|].
    rewrite ?Hbad; cbv beta iota zeta. apply pure_ok. }
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_ignored_flags =? 0)%Z)
    eqn:Hnz; [discriminate|].
  destruct (pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m))) as [st|] eqn:Hid;
    [discriminate|].
  destruct (negb (access_okb fildes 8)) eqn:Hak.
  { (* [access_ok] refuses the range: -EFAULT, or one of the injected
       errnos alongside it, with nothing installed *)
    destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
    destruct (errno_ret_in (EFAULT :: pipe2_errnos) ret) eqn:He; [|discriminate].
    inversion H; clear H; subst.
    apply errno_ret_in_true in He as (e & Hin & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|].
    rewrite ?Hbad, ?Hnz, ?Hid, ?Hak; cbv beta iota zeta.
    destruct Hin as [<-|Hin].
    - apply alt_r. apply pure_ok.
    - apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact Hin|].
      apply pure_ok. }
  destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 8)) as [w8|] eqn:H8.
  - destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
      destruct us as [|? ?]; destruct cs as [|? ?];
      destruct copyins as [|? ?]; try discriminate.
    { (* the injected environment errno *)
      destruct (errno_ret_in pipe2_errnos ret) eqn:He; [|discriminate].
      inversion H; clear H; subst.
      apply errno_ret_in_true in He as (e & Hin & ->).
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|].
      rewrite ?Hbad, ?Hnz, ?Hid, ?H8; cbv beta iota zeta.
      apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact Hin|]. apply pure_ok. }
    { (* the copy-out of two fresh descriptors *)
      destruct (fd_lookup (m_fds m) (pipe2_fdr m)) as [x|] eqn:Hfr;
        [discriminate|].
      destruct (fd_lookup (pipe2_fds1 m (pipe_new_id (m_pipes m)))
                  (pipe2_fdw m (pipe_new_id (m_pipes m)))) as [y|] eqn:Hfw;
        [discriminate|].
      destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a fildes
                && listN_eqb bs (pipe_fd_bytes (pipe2_fdr m)
                                   (pipe2_fdw m (pipe_new_id (m_pipes m)))))
        eqn:Hg; [|discriminate].
      inversion H; clear H; subst m' evs.
      apply andb_true_iff in Hg as [Hg Hbs].
      apply andb_true_iff in Hg as [Hret Ha].
      apply bv_eqb_eq in Hret; subst ret. apply bv_eqb_eq in Ha; subst a.
      apply listN_eqb_eq in Hbs; subst bs.
      eapply bind_ok0; [apply input_ok|]. cbv beta.
      eapply bind_ok0; [apply get_model_ok|].
      rewrite ?Hbad, ?Hnz, ?Hid, ?H8; cbv beta iota zeta.
      apply alt_r.
      eapply bind_ok0.
      { apply (choose_ok _ (pipe2_fdr m)).
        split; [exact Hfr|reflexivity]. }
      cbv beta.
      eapply bind_ok0.
      { apply (choose_ok _ (pipe2_fdw m (pipe_new_id (m_pipes m)))).
        split; [exact Hfw|reflexivity]. }
      cbv beta.
      eapply bind_ok0; [apply modify_ok|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok. }
  - destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 1)) as [w1|] eqn:H1;
      [discriminate|].
    destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
    destruct (errno_ret_in (EFAULT :: pipe2_errnos) ret) eqn:He; [|discriminate].
    inversion H; clear H; subst.
    apply errno_ret_in_true in He as (e & Hin & ->).
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    eapply bind_ok0; [apply get_model_ok|].
    rewrite ?Hbad, ?Hnz, ?Hid, ?H8, ?H1; cbv beta iota zeta.
    destruct Hin as [<-|Hin].
    + apply alt_r. apply pure_ok.
    + apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact Hin|]. apply pure_ok.
Qed.

Lemma check_pipe2_sound_unmodeled : forall i fildes flags eff m,
  check_pipe2 i fildes flags eff m = CheckUnmodeled ->
  pipe2_spec fildes flags i m Unmodeled.
Proof.
  intros i fildes flags eff m H.
  unfold check_pipe2 in H. unfold pipe2_spec.
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_flags_mask =? 0)%Z)
    eqn:Hbad.
  { now apply check_ret_only_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|].
  rewrite ?Hbad; cbv beta iota zeta.
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_ignored_flags =? 0)%Z)
    eqn:Hnz; [apply unmodeled_intro|].
  destruct (pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m))) as [st|] eqn:Hid;
    [apply unmodeled_intro|].
  destruct (negb (access_okb fildes 8)) eqn:Hak.
  { exfalso. destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
    destruct (errno_ret_in (EFAULT :: pipe2_errnos) ret); discriminate. }
  destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 8)) as [w8|] eqn:H8.
  - exfalso. destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|[a bs] [|? ?]]; destruct zs as [|? ?];
      destruct us as [|? ?]; destruct cs as [|? ?];
      destruct copyins as [|? ?]; try discriminate.
    + destruct (errno_ret_in pipe2_errnos ret); discriminate.
    + destruct (fd_lookup (m_fds m) (pipe2_fdr m)); [discriminate|].
      destruct (fd_lookup (pipe2_fds1 m (pipe_new_id (m_pipes m)))
                  (pipe2_fdw m (pipe_new_id (m_pipes m)))); [discriminate|].
      destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a fildes
                && listN_eqb bs (pipe_fd_bytes (pipe2_fdr m)
                                   (pipe2_fdw m (pipe_new_id (m_pipes m)))));
        discriminate.
  - destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 1)) as [w1|] eqn:H1.
    + apply unmodeled_intro.
    + exfalso. destruct eff as [ret ws zs us cs copyins].
      destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
      destruct (errno_ret_in (EFAULT :: pipe2_errnos) ret); discriminate.
Qed.

Lemma check_pipe2_complete_ok : forall i fildes flags eff m m' evs,
  pipe2_spec fildes flags i m (Ok eff m' evs) ->
  check_pipe2 i fildes flags eff m = CheckOk m' evs.
Proof.
  intros i fildes flags eff m m' evs H.
  unfold pipe2_spec in H. unfold check_pipe2. sys_unfold.
  cbv beta iota zeta in H |- *.
  (* each branch is focused, because [inv_ok] splits the injected-errno
     membership into one goal per errno and [all:] must not reach past
     the branch that produced them *)
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_flags_mask =? 0)%Z)
    eqn:Hbad.
  { hall Hbad; inv_ok. cbn; rewrite bv_eqb_refl; reflexivity. }
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_ignored_flags =? 0)%Z)
    eqn:Hnz.
  { hall Hbad; hall Hnz; inv_ok; try discriminate. }
  destruct (pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m))) as [st|] eqn:Hid.
  { hall Hbad; hall Hnz; inv_ok; hall Hid; inv_ok; try discriminate. }
  destruct (negb (access_okb fildes 8)) eqn:Hak.
  { hall Hbad; hall Hnz; inv_ok; hall Hid; hall Hak; inv_ok.
    (* -EFAULT, or one of the injected errnos alongside it *)
    all: cbv beta iota; erewrite errno_ret_in_intro by (cbn in *; tauto);
         reflexivity. }
  destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 8)) as [w8|] eqn:H8.
  { hall Hbad; hall Hnz; inv_ok; hall Hid; hall H8; inv_ok.
    (* the injected environment errno, once per member of [pipe2_errnos] *)
    all: try (cbv beta iota;
              erewrite errno_ret_in_intro by (cbn in *; tauto); reflexivity).
    (* what is left is the copy-out of two fresh descriptors *)
    unfold pipe2_model, pipe2_fdw, pipe2_fds1, pipe2_fdr. cbv beta iota.
    destruct (fd_lookup (m_fds m) (alloc_fd (m_fds m))) eqn:Hfr;
      [exfalso; congruence|]. cbv beta iota.
    destruct (fd_lookup
                (fd_insert (m_fds m) (alloc_fd (m_fds m))
                   (FdPipe (pipe_new_id (m_pipes m)) false))
                (alloc_fd
                   (fd_insert (m_fds m) (alloc_fd (m_fds m))
                      (FdPipe (pipe_new_id (m_pipes m)) false)))) eqn:Hfw;
      [exfalso; congruence|]. cbv beta iota.
    rewrite !bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl).
    reflexivity. }
  destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 1)) as [w1|] eqn:H1.
  { hall Hbad; hall Hnz; inv_ok; hall Hid; hall H8; hall H1; inv_ok;
    try discriminate. }
  hall Hbad; hall Hnz; inv_ok; hall Hid; hall H8; hall H1; inv_ok.
  (* -EFAULT, or one of the injected errnos alongside it *)
  all: cbv beta iota; erewrite errno_ret_in_intro by (cbn in *; tauto);
       reflexivity.
Qed.

Lemma check_pipe2_complete_unmodeled : forall i fildes flags m eff,
  pipe2_spec fildes flags i m Unmodeled ->
  check_pipe2 i fildes flags eff m = CheckUnmodeled.
Proof.
  intros i fildes flags m eff H.
  unfold pipe2_spec in H. unfold check_pipe2. sys_unfold.
  cbv beta iota zeta in H |- *.
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_flags_mask =? 0)%Z)
    eqn:Hbad.
  { hall Hbad; inv_ok; try discriminate. }
  destruct (negb (Z.ldiff (bv_unsigned flags) pipe2_ignored_flags =? 0)%Z)
    eqn:Hnz; [reflexivity|].
  destruct (pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m))) as [st|] eqn:Hid;
    [reflexivity|].
  destruct (negb (access_okb fildes 8)) eqn:Hak.
  { hall Hbad; hall Hnz; inv_ok; hall Hid; hall Hak; inv_ok; try discriminate. }
  destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 8)) as [w8|] eqn:H8.
  { hall Hbad; hall Hnz; inv_ok; hall Hid; hall H8; inv_ok; try discriminate. }
  destruct (read_bytes_map (in_wmem i) fildes (Z_to_bv 64 1)) as [w1|] eqn:H1;
    [reflexivity|].
  hall Hbad; hall Hnz; inv_ok; hall Hid; hall H8; hall H1; inv_ok;
    try discriminate.
Qed.
