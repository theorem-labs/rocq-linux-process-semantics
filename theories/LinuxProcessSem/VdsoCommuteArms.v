(** * LinuxProcessSem.VdsoCommuteArms — the vDSO frame, one specification at a time

    [VdsoCommute.v] proves that [State.with_vdso] frames every combinator a
    specification is built from.  [Monad.Sys] is a relational monad, so that
    does not close the question for a specification: the walk has to visit
    each one.  This file is that walk, in [Sys.SyscallTable.spec_table]'s
    order, and [VdsoCommuteSys.v] assembles it.

    85 lemmas for 93 arms: [getid_spec] answers four numbers,
    [setid_spec], [setresid_spec], [fsync_spec], [exit_spec] and
    [accept4_spec] two each.  A repeated arm costs nothing here; it is
    applied twice at the dispatcher.

    A new arm in [spec_table] with no lemma here fails
    [VdsoCommuteSys.v]'s assembly, not this file, which is where the
    omission is visible.

    PURE ADDITION: this file changes no existing statement. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs.
From LinuxProcessSemantics Require Import LinuxProcessSem.Vdso.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  State Monad Specs VdsoCommute.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* ---- fs/d_path.c ---- *)
Lemma vc_getcwd_spec : forall buf size, vdso_commutes (getcwd_spec buf size).
Proof. intros; unfold getcwd_spec; vdso_walk. Qed.

(* ---- fs/eventfd.c ---- *)
Lemma vc_eventfd2_spec : forall flags, vdso_commutes (eventfd2_spec flags).
Proof. intros; unfold eventfd2_spec; vdso_walk. Qed.

(* ---- fs/eventpoll.c ---- *)
Lemma vc_epoll_create1_spec : forall flags,
  vdso_commutes (epoll_create1_spec flags).
Proof. intros; unfold epoll_create1_spec; vdso_walk. Qed.

Lemma vc_epoll_ctl_spec : forall epfd op tfd event,
  vdso_commutes (epoll_ctl_spec epfd op tfd event).
Proof. intros; unfold epoll_ctl_spec; vdso_walk. Qed.

Lemma vc_epoll_pwait_spec : forall epfd events maxevents sigmask sigsetsize,
  vdso_commutes (epoll_pwait_spec epfd events maxevents sigmask sigsetsize).
Proof. intros; unfold epoll_pwait_spec; vdso_walk. Qed.

(* ---- fs/file.c ---- *)
Lemma vc_dup_spec : forall oldfd, vdso_commutes (dup_spec oldfd).
Proof. intros; unfold dup_spec; vdso_walk. Qed.

Lemma vc_dup3_spec : forall oldfd newfd flags,
  vdso_commutes (dup3_spec oldfd newfd flags).
Proof. intros; unfold dup3_spec; vdso_walk. Qed.

(* ---- fs/fcntl.c ---- *)
Lemma vc_fcntl_spec : forall fd cmd a, vdso_commutes (fcntl_spec fd cmd a).
Proof. intros; unfold fcntl_spec; vdso_walk. Qed.

(* ---- fs/ioctl.c ---- *)
Lemma vc_ioctl_spec : forall fd req, vdso_commutes (ioctl_spec fd req).
Proof. intros; unfold ioctl_spec; vdso_walk. Qed.

(* ---- fs/locks.c ---- *)
Lemma vc_flock_spec : forall fd cmd, vdso_commutes (flock_spec fd cmd).
Proof. intros; unfold flock_spec; vdso_walk. Qed.

(* ---- the walk's own refusals ---- *)

(** [Sys.Fs.Namei.walk_refusals] reads the arm it wraps NEGATIVELY: a
    refusal stands where the arm neither declines nor gives that errno
    itself.  The two-program walk relates an arm at two running models
    whose draws need not agree, and a negative premise does not travel
    that way.  At ONE model it does: the reverse direction is the forward
    one at the model's own draw ([with_vdso_same]).  So an arm that wraps
    its walk is proved at one model ([vdso_at]), and the body under the
    wrapper is walked as before. *)
Definition vdso_at (P : SyscallInput -> Model -> Sys SyscallEffect) : Prop :=
  forall v i m o, P i m i m o ->
    P i (with_vdso v m) i (with_vdso v m) (outcome_with_vdso v o).

Local Lemma bind_input_iff {A} (k : SyscallInput -> Sys A) : forall i m o,
  bind input k i m o <-> k i i m o.
Proof.
  intros i m o. unfold bind, input. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3).
    injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists i, m, [], evs. split; [reflexivity|].
    split; [exact H | reflexivity].
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|].
    injection H1 as -> -> ->. exact H2.
  - intros H. right. exists i, m, []. split; [reflexivity | exact H].
Qed.

Local Lemma reads_iff (P : SyscallInput -> Model -> Sys SyscallEffect) :
  forall i m o, (i0 <- input ;; m0 <- get_model ;; P i0 m0) i m o <-> P i m i m o.
Proof.
  intros i m o.
  rewrite (bind_input_iff (fun i0 => m0 <- get_model ;; P i0 m0)).
  exact (bind_get_model (fun m0 => P i m0) i m o).
Qed.

Lemma vdso_commutes_of_at : forall P, vdso_at P ->
  vdso_commutes (i <- input ;; m <- get_model ;; P i m).
Proof.
  intros P HP v i m o H.
  apply (proj1 (reads_iff P i m o)) in H.
  apply (proj2 (reads_iff P i (with_vdso v m) (outcome_with_vdso v o))).
  exact (HP v i m o H).
Qed.

Lemma vdso_at_of_commutes : forall P,
  vdso_commutes (i <- input ;; m <- get_model ;; P i m) -> vdso_at P.
Proof.
  intros P HP v i m o H.
  apply (proj2 (reads_iff P i m o)) in H.
  exact (proj1 (reads_iff P i (with_vdso v m) (outcome_with_vdso v o)) (HP v i m o H)).
Qed.

Lemma vdso_at_walk_refusals : forall md (pathp : word) P, vdso_at P ->
  vdso_at (fun i m => walk_refusals md pathp (P i m)).
Proof.
  intros md pathp P HP v i m o [H | (Hnu & es & e & Hw & Hin & -> & Hnot)].
  - left. exact (HP v i m o H).
  - right. split.
    + intro Hu. apply Hnu.
      pose proof (HP (m_vdso m) i (with_vdso v m) Unmodeled Hu) as H'.
      rewrite with_vdso_idem, with_vdso_same in H'. exact H'.
    + exists es, e. split; [exact Hw|]. split; [exact Hin|]. split; [reflexivity|].
      intros m1 evs1 Hs. apply (Hnot (with_vdso (m_vdso m) m1) evs1).
      pose proof (HP (m_vdso m) i (with_vdso v m) _ Hs) as H'.
      rewrite with_vdso_idem, with_vdso_same in H'. exact H'.
Qed.

(** [Sys.Fs.Namei.getname_refusals] reads the arm it wraps negatively
    too, and is proved the same way: at one model, and, for an arm whose
    wrapper stands outside its own model read, as a frame of its own
    ([vc_getname_refusals]). *)
Lemma vdso_at_getname_refusals :
  forall (lead : list (word * nat)) (pathp : word) P, vdso_at P ->
  vdso_at (fun i m => getname_refusals lead pathp (P i m)).
Proof.
  intros lead pathp P HP v i m o [H | (Hnu & reads & e & Hr & Hin & -> & Hnot)].
  - left. exact (HP v i m o H).
  - right. split.
    + intro Hu. apply Hnu.
      pose proof (HP (m_vdso m) i (with_vdso v m) Unmodeled Hu) as H'.
      rewrite with_vdso_idem, with_vdso_same in H'. exact H'.
    + exists reads, e. split; [exact Hr|]. split; [exact Hin|]. split; [reflexivity|].
      intros m1 evs1 Hs. apply (Hnot (with_vdso (m_vdso m) m1) evs1).
      pose proof (HP (m_vdso m) i (with_vdso v m) _ Hs) as H'.
      rewrite with_vdso_idem, with_vdso_same in H'. exact H'.
Qed.

Lemma vc_getname_refusals :
  forall (lead : list (word * nat)) (pathp : word) (c : Sys SyscallEffect),
  vdso_commutes c -> vdso_commutes (getname_refusals lead pathp c).
Proof.
  intros lead pathp c Hc v i m o [H | (Hnu & reads & e & Hr & Hin & -> & Hnot)].
  - left. exact (Hc v i m o H).
  - right. split.
    + intro Hu. apply Hnu.
      pose proof (Hc (m_vdso m) i (with_vdso v m) Unmodeled Hu) as H'.
      rewrite with_vdso_idem, with_vdso_same in H'. exact H'.
    + exists reads, e. split; [exact Hr|]. split; [exact Hin|]. split; [reflexivity|].
      intros m1 evs1 Hs. apply (Hnot (with_vdso (m_vdso m) m1) evs1).
      pose proof (Hc (m_vdso m) i (with_vdso v m) _ Hs) as H'.
      rewrite with_vdso_idem, with_vdso_same in H'. exact H'.
Qed.

Lemma vdso_at_record_copyins : forall (L : SyscallInput -> list (word * nat)) P,
  vdso_at P -> vdso_at (fun i m => record_copyins (L i) (P i m)).
Proof.
  intros L P HP v i m o H. unfold record_copyins, bind, pure in *.
  destruct o as [y m2 evs|].
  - destruct H as (x & m1 & evs1 & evs2 & Hx & Hy & ->).
    injection Hy as -> -> ->.
    exists x, (with_vdso v m1), evs1, []. split; [exact (HP v i m _ Hx)|].
    split; reflexivity.
  - destruct H as [H | (x & m1 & evs1 & Hx & Hy)];
      [left; exact (HP v i m Unmodeled H) | discriminate Hy].
Qed.

Lemma vdso_at_if : forall (b : bool) P Q, vdso_at P -> vdso_at Q ->
  vdso_at (fun i m => if b then P i m else Q i m).
Proof. intros b P Q HP HQ. destruct b; assumption. Qed.

(** The same for a test on the input alone, which both sides read
    unchanged: [Stat.statat_getname_runs] in [newfstatat_core_spec]. *)
Lemma vdso_at_if_input : forall (b : SyscallInput -> bool) P Q,
  vdso_at P -> vdso_at Q ->
  vdso_at (fun i m => if b i then P i m else Q i m).
Proof. intros b P Q HP HQ v i m o. destruct (b i); [apply HP|apply HQ]. Qed.

Lemma vdso_at_const : forall c, vdso_commutes c -> vdso_at (fun _ _ => c).
Proof. intros c Hc v i m o H. exact (Hc v i m o H). Qed.

(** The same for a test on the input and the descriptor table, which
    [State.with_vdso] carries across: [Fs.Open.openat_core_spec]'s test
    for a table with no free slot. *)
Lemma vdso_at_if_fds : forall (b : SyscallInput -> list (word * FdEntry) -> bool) P Q,
  vdso_at P -> vdso_at Q ->
  vdso_at (fun i m => if b i (m_fds m) then P i m else Q i m).
Proof.
  intros b P Q HP HQ v i m o H. cbv beta in H |- *.
  change (m_fds (with_vdso v m)) with (m_fds m).
  destruct (b i (m_fds m)); [exact (HP v i m o H) | exact (HQ v i m o H)].
Qed.

(** What [get_unused_fd_flags] answers on a table with no free slot
    ([Fs.File.unused_fd_none_spec]) reads the soft limit and the table,
    both of which [State.with_vdso] carries across. *)
Lemma vdso_at_unused_fd_none : vdso_at (fun _ m => unused_fd_none_spec m).
Proof.
  intros v i m o H. cbv beta in H |- *. unfold unused_fd_none_spec in *.
  change (m_nofile (with_vdso v m)) with (m_nofile m).
  change (m_fds (with_vdso v m)) with (m_fds m).
  destruct (bv_unsigned (m_nofile m) <=? bv_unsigned (alloc_fd (m_fds m)) + 1)%Z.
  - exact (vc_err_ret EMFILE v i m o H).
  - exact (vc_unmodeled v i m o H).
Qed.

(** The arm at one model: its gates, its ledger, [getname_refusals] and
    [walk_refusals], then the body walked as a specification of its own. *)
Ltac vdso_at_walk :=
  apply vdso_commutes_of_at;
  repeat first
    [ apply vdso_at_getname_refusals
    | apply vdso_at_walk_refusals
    | apply vdso_at_record_copyins
    | apply vdso_at_if
    | apply vdso_at_if_input
    | (apply vdso_at_const; solve [vdso_walk]) ];
  apply vdso_at_of_commutes; vdso_walk.

(* ---- fs/namei.c ---- *)
Lemma vc_mkdirat_spec : forall dirfd pathp,
  vdso_commutes (mkdirat_spec dirfd pathp).
Proof. intros; unfold mkdirat_spec; vdso_at_walk. Qed.

Lemma vc_unlinkat_spec : forall dirfd pathp flags,
  vdso_commutes (unlinkat_spec dirfd pathp flags).
Proof. intros; unfold unlinkat_spec; vdso_at_walk. Qed.

(* ---- fs/open.c ---- *)
Lemma vc_ftruncate_spec : forall fd len, vdso_commutes (ftruncate_spec fd len).
Proof. intros; unfold ftruncate_spec; vdso_walk. Qed.

Lemma vc_faccessat_spec : forall dirfd pathp mode,
  vdso_commutes (faccessat_spec dirfd pathp mode).
Proof. intros; unfold faccessat_spec; vdso_at_walk. Qed.

Lemma vc_faccessat2_spec : forall dirfd pathp mode flags,
  vdso_commutes (faccessat2_spec dirfd pathp mode flags).
Proof. intros; unfold faccessat2_spec; vdso_at_walk. Qed.

Lemma vc_openat_spec : forall dirfd pathp flags,
  vdso_commutes (openat_spec dirfd pathp flags).
Proof.
  intros.
  assert (Hc : vdso_commutes (openat_core_spec dirfd pathp flags)).
  { unfold openat_core_spec. apply vdso_commutes_of_at.
    apply vdso_at_if; [apply vdso_at_const; solve [vdso_walk] |].
    apply (vdso_at_if_fds (fun i fds => openat_name_fetched i pathp && lowest_fd_none fds)).
    - apply vdso_at_unused_fd_none.
    - apply vdso_at_walk_refusals. apply vdso_at_of_commutes. vdso_walk. }
  unfold openat_spec. apply vc_bind; [vdso_walk | intros x; cbv beta].
  apply vc_getname_refusals. vdso_walk.
Qed.

Lemma vc_close_spec : forall fd, vdso_commutes (close_spec fd).
Proof. intros; unfold close_spec; vdso_walk. Qed.

(* ---- fs/pipe.c ---- *)
Lemma vc_pipe2_spec : forall fildes flags,
  vdso_commutes (pipe2_spec fildes flags).
Proof. intros; unfold pipe2_spec; vdso_walk. Qed.

(* ---- fs/readdir.c ---- *)
Lemma vc_getdents64_spec : forall fd count,
  vdso_commutes (getdents64_spec fd count).
Proof. intros; unfold getdents64_spec; vdso_walk. Qed.

(* ---- fs/read_write.c ---- *)
Lemma vc_lseek_spec : forall fd off whence,
  vdso_commutes (lseek_spec fd off whence).
Proof. intros; unfold lseek_spec; vdso_walk. Qed.

Lemma vc_read_spec : forall fd buf count, vdso_commutes (read_spec fd buf count).
Proof. intros; unfold read_spec; vdso_walk. Qed.

(* -------------------------------------------------------------------------
   The write family's TRANSFORMERS

   [Sys.Fs.ReadWrite.write_file_tail] is handed the file-extension step as an
   [option (Sys SyscallEffect -> Sys SyscallEffect)], chosen by a lookup, so
   the walk meets a function it cannot look inside: destructing the option
   leaves an opaque [u] and the walk stops there.  What the four producers
   actually yield is [fun k => set_* … ;; k] or the identity, and these
   lemmas say so, once each.  [vc_write_file_tail] then closes the tail for
   every arm that uses it.
   ------------------------------------------------------------------------- *)

Lemma vc_tr_write_fault_extend : forall fs p off u,
  write_fault_extend fs p off = Some u -> vdso_commutes_tr u.
Proof.
  intros fs p off u H. unfold write_fault_extend in H. cbv zeta in H.
  destruct (negb (modeled_zero_fill (bv_unsigned off) (fs_ino_data fs p)));
    [discriminate H|].
  injection H as <-. intros c Hc. vdso_walk.
Qed.

Lemma vc_tr_write_fault_keep : vdso_commutes_tr write_fault_keep.
Proof. intros c Hc. exact Hc. Qed.

(** The tail every file write arm shares. *)
Lemma vc_write_file_tail : forall mp buf count fault place,
  (forall u, fault = Some u -> vdso_commutes_tr u) ->
  (forall bs u, place bs = Some u -> vdso_commutes_tr u) ->
  vdso_commutes (write_file_tail mp buf count fault place).
Proof.
  intros mp buf count fault place Hf Hp. unfold write_file_tail.
  destruct (negb (w_is0 count) &&
            Nat.eqb (length (write_source mp buf count)) 0)%bool.
  - destruct fault as [u|] eqn:E.
    + exact (Hf u eq_refl _ (vc_err_ret EFAULT)).
    + apply vc_unmodeled.
  - assert (Hd : vdso_commutes
      match place (write_source mp buf count) with
      | None => unmodeled
      | Some upd => upd (write_ledger buf count (write_source mp buf count))
      end).
    { destruct (place (write_source mp buf count)) as [u|] eqn:E.
      - apply (Hp _ u E). unfold write_ledger. vdso_walk.
      - apply vc_unmodeled. }
    destruct (w_is0 count); [| exact Hd].
    unfold access_ok_zero. vdso_walk.
Qed.

(** The vectored twin of [write_file_tail].  Same two transformer
    arguments, one more decline ([writev_buf_gap]) and the import in
    front. *)
Lemma vc_writev_file_arm : forall mp iov iovcnt off fault place,
  (forall u, fault = Some u -> vdso_commutes_tr u) ->
  (forall bs u, place bs = Some u -> vdso_commutes_tr u) ->
  vdso_commutes (writev_file_arm mp iov iovcnt off fault place).
Proof.
  intros mp iov iovcnt off fault place Hf Hp. unfold writev_file_arm.
  apply vc_record_copyins.
  destruct (import_iovecs mp iov (iovcnt32 iovcnt)) as [iovs0 | |];
    [| apply vc_err_ret | apply vc_err_ret].
  cbn zeta.
  destruct (Z.eqb (iovs_total (cap_iovecs iovs0)) 0); [apply vc_ret_only|].
  destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)));
    [apply vc_err_ret|].
  destruct (Nat.eqb (length (writev_gathered mp iovs0)) 0).
  - destruct fault as [u|] eqn:E.
    + exact (Hf u eq_refl _ (vc_err_ret EFAULT)).
    + unfold writev_buf_gap; vdso_walk.
  - destruct (place (writev_gathered mp iovs0)) as [u|] eqn:E.
    + destruct (addr_is_error_b (len_word (writev_gathered mp iovs0)));
        [unfold writev_buf_gap; vdso_walk|].
      apply (Hp _ u E). unfold writev_ledger. vdso_walk.
    + unfold writev_buf_gap; vdso_walk.
Qed.

(** A transformer handed over by a lookup, from the equation the lookup
    satisfies.  The named producers above are the three the write arms pass
    by name; the [place] argument is as often an inline [match] on the file
    system, so this opens whatever the equation's left-hand side is until a
    [Some] shows through and then walks the transformer it found.  Every
    one of them is [fun k => set_* … ;; k] or the identity. *)
Ltac tr_from_eq :=
  match goal with
  | H : _ = Some ?u |- vdso_commutes_tr ?u =>
      (* Open the left-hand side until each branch is [None] (discharged)
         or [Some …].  [injection] is OUTSIDE the loop: it consumes [H],
         and a loop that then names [H] again is an anomaly, not a
         failure. *)
      repeat first
        [ discriminate H
        | match type of H with
          | ?f _ = _ => progress unfold f in H
          | ?f _ _ = _ => progress unfold f in H
          | ?f _ _ _ = _ => progress unfold f in H
          | ?f _ _ _ _ = _ => progress unfold f in H
          | ?f _ _ _ _ _ = _ => progress unfold f in H
          | context [if ?b then _ else _] => destruct b
          | context [match ?x with _ => _ end] => destruct x
          end ];
      injection H as <-;
      let c := fresh "c" in let Hc := fresh "Hc" in
      intros c Hc; vdso_walk
  end.

(** The walk, with the write family's tail added to it.  [rw_step] is tried
    FIRST: [vdso_step]'s last resort unfolds the head constant, which would
    open [write_file_tail] and destruct its option without keeping the
    equation, leaving an opaque transformer and no way back. *)
Ltac rw_step :=
  match goal with
  | |- vdso_commutes (write_file_tail _ _ _ _ _) =>
      apply vc_write_file_tail; intros; cbn beta zeta in *
  | |- vdso_commutes (writev_file_arm _ _ _ _ _ _) =>
      apply vc_writev_file_arm; intros; cbn beta zeta in *
  | H : write_fault_extend _ _ _ = Some ?u |- vdso_commutes_tr ?u =>
      exact (vc_tr_write_fault_extend _ _ _ _ H)
  | |- vdso_commutes_tr _ => tr_from_eq
  (** [pwrite64]'s arms INLINE the tail rather than calling
      [write_file_tail], so the walk meets the option itself.  Keep the
      equation — [vdso_step]'s plain [destruct] throws it away and leaves an
      opaque transformer with nothing to identify it by — and then read the
      transformer off it. *)
  | H : _ = Some ?u |- vdso_commutes (?u _) =>
      let T := fresh "Htr" in
      assert (T : vdso_commutes_tr u) by tr_from_eq; apply T
  | |- vdso_commutes (match ?x with _ => _ end) => destruct x eqn:?
  end.

Ltac rw_walk := intros; repeat (cbn beta zeta iota; first [rw_step | vdso_step]).

(** FROM HERE, the plain walk is the wider one.  The transformer steps are
    not specific to the write arms — any specification that chooses a
    continuation by a lookup meets the same shape — and carrying two tactic
    names through the rest of the table would say they are two kinds of
    walk when they are one.

    This goes through [VdsoCommute.v]'s declared hook rather than
    redefining [vdso_walk]: a redefinition cannot be [Local], so it would
    change what [vdso_walk] means for every later importer, and an importer
    of this file would see a different walk from one that imported only
    [VdsoCommute].  The hook is the one name whose purpose is to be
    redefined. *)
Ltac vdso_extra_step ::= rw_step.

Lemma vc_write_spec : forall fd buf count,
  vdso_commutes (write_spec fd buf count).
Proof. intros; unfold write_spec; rw_walk. Qed.

Lemma vc_readv_spec : forall fd iov iovcnt,
  vdso_commutes (readv_spec fd iov iovcnt).
Proof. intros; unfold readv_spec; vdso_walk. Qed.

Lemma vc_writev_spec : forall fd iov iovcnt,
  vdso_commutes (writev_spec fd iov iovcnt).
Proof. intros; unfold writev_spec; rw_walk. Qed.

Lemma vc_pread64_spec : forall fd buf count pos,
  vdso_commutes (pread64_spec fd buf count pos).
Proof. intros; unfold pread64_spec; rw_walk. Qed.

Lemma vc_pwrite64_spec : forall fd buf count pos,
  vdso_commutes (pwrite64_spec fd buf count pos).
Proof. intros; unfold pwrite64_spec; rw_walk. Qed.

Lemma vc_pwritev2_spec : forall fd iov iovcnt pos_l pos_h flags,
  vdso_commutes (pwritev2_spec fd iov iovcnt pos_l pos_h flags).
Proof. intros; unfold pwritev2_spec; rw_walk. Qed.

(* ---- fs/select.c ---- *)
Lemma vc_pselect6_spec : forall n32 inp outp exp tsp sig,
  vdso_commutes (pselect6_spec n32 inp outp exp tsp sig).
Proof. intros; unfold pselect6_spec; vdso_walk. Qed.

Lemma vc_ppoll_spec : forall ufds nfds tsp sig sigsetsize,
  vdso_commutes (ppoll_spec ufds nfds tsp sig sigsetsize).
Proof. intros; unfold ppoll_spec; vdso_walk. Qed.

(* ---- fs/stat.c ---- *)
Lemma vc_readlinkat_spec : forall dirfd pathp buf bufsiz,
  vdso_commutes (readlinkat_spec dirfd pathp buf bufsiz).
Proof. intros; unfold readlinkat_spec; vdso_at_walk. Qed.

Lemma vc_newfstatat_spec : forall dirfd pathp statbuf flag,
  vdso_commutes (newfstatat_spec dirfd pathp statbuf flag).
Proof.
  intros.
  assert (Hc : vdso_commutes (newfstatat_core_spec dirfd pathp statbuf flag))
    by (unfold newfstatat_core_spec; vdso_at_walk).
  unfold newfstatat_spec. apply vc_bind; [vdso_walk | intros x; cbv beta].
  destruct (statat_getname_runs x pathp flag); [apply vc_getname_refusals|];
    vdso_walk.
Qed.

Lemma vc_fstat_spec : forall fd statbuf, vdso_commutes (fstat_spec fd statbuf).
Proof. intros; unfold fstat_spec; vdso_walk. Qed.

(* ---- fs/sync.c ---- *)
Lemma vc_fsync_spec : forall fd, vdso_commutes (fsync_spec fd).
Proof. intros; unfold fsync_spec; vdso_walk. Qed.

(* ---- fs/timerfd.c ---- *)
Lemma vc_timerfd_create_spec : forall clkid flags,
  vdso_commutes (timerfd_create_spec clkid flags).
Proof. intros; unfold timerfd_create_spec; vdso_walk. Qed.

(* ---- kernel/exit.c ---- *)
Lemma vc_exit_spec : forall code, vdso_commutes (exit_spec code).
Proof. intros; unfold exit_spec; vdso_walk. Qed.

Lemma vc_wait4_spec : forall upid stat_addr options rusage,
  vdso_commutes (wait4_spec upid stat_addr options rusage).
Proof. intros; unfold wait4_spec; vdso_walk. Qed.

(* ---- kernel/fork.c ---- *)
Lemma vc_set_tid_address_spec : vdso_commutes set_tid_address_spec.
Proof. intros; unfold set_tid_address_spec; vdso_walk. Qed.

Lemma vc_clone_spec : forall flags, vdso_commutes (clone_spec flags).
Proof. intros; unfold clone_spec; vdso_walk. Qed.

Lemma vc_clone3_spec : forall uargs size,
  vdso_commutes (clone3_spec uargs size).
Proof. intros; unfold clone3_spec; vdso_walk. Qed.

(* ---- kernel/futex/syscalls.c ---- *)
Lemma vc_futex_spec : forall uaddr op val utime,
  vdso_commutes (futex_spec uaddr op val utime).
Proof. intros; unfold futex_spec; vdso_walk. Qed.

Lemma vc_set_robust_list_spec : forall len,
  vdso_commutes (set_robust_list_spec len).
Proof. intros; unfold set_robust_list_spec; vdso_walk. Qed.

(* ---- kernel/time/hrtimer.c ---- *)
Lemma vc_nanosleep_spec : forall rqtp rmtp,
  vdso_commutes (nanosleep_spec rqtp rmtp).
Proof. intros; unfold nanosleep_spec; vdso_walk. Qed.

(* ---- kernel/time/posix-timers.c ---- *)
Lemma vc_clock_gettime_spec : forall clkid tp,
  vdso_commutes (clock_gettime_spec clkid tp).
Proof. intros; unfold clock_gettime_spec; vdso_walk. Qed.

Lemma vc_clock_getres_spec : forall clkid tp,
  vdso_commutes (clock_getres_spec clkid tp).
Proof. intros; unfold clock_getres_spec; vdso_walk. Qed.

(* ---- kernel/time/time.c ---- *)
Lemma vc_gettimeofday_spec : forall tv tz,
  vdso_commutes (gettimeofday_spec tv tz).
Proof. intros; unfold gettimeofday_spec; vdso_walk. Qed.

(* ---- kernel/sched/syscalls.c ---- *)
Lemma vc_sched_setscheduler_spec : forall pid policy param,
  vdso_commutes (sched_setscheduler_spec pid policy param).
Proof. intros; unfold sched_setscheduler_spec; vdso_walk. Qed.

Lemma vc_sched_getaffinity_spec : forall len,
  vdso_commutes (sched_getaffinity_spec len).
Proof. intros; unfold sched_getaffinity_spec; vdso_walk. Qed.

Lemma vc_sched_yield_spec : vdso_commutes sched_yield_spec.
Proof. intros; unfold sched_yield_spec; vdso_walk. Qed.

(* ---- kernel/signal.c ---- *)
Lemma vc_tkill_spec : forall pid sig, vdso_commutes (tkill_spec pid sig).
Proof. intros; unfold tkill_spec; vdso_walk. Qed.

Lemma vc_tgkill_spec : forall tgid pid sig,
  vdso_commutes (tgkill_spec tgid pid sig).
Proof. intros; unfold tgkill_spec; vdso_walk. Qed.

Lemma vc_sigaltstack_spec : forall uss uoss,
  vdso_commutes (sigaltstack_spec uss uoss).
Proof. intros; unfold sigaltstack_spec; vdso_walk. Qed.

Lemma vc_rt_sigaction_spec : forall sig act oact ss,
  vdso_commutes (rt_sigaction_spec sig act oact ss).
Proof. intros; unfold rt_sigaction_spec; vdso_walk. Qed.

Lemma vc_rt_sigprocmask_spec : forall how nset oset ss,
  vdso_commutes (rt_sigprocmask_spec how nset oset ss).
Proof. intros; unfold rt_sigprocmask_spec; vdso_walk. Qed.

(* ---- kernel/groups.c ---- *)
Lemma vc_getgroups_spec : forall gidsetsize,
  vdso_commutes (getgroups_spec gidsetsize).
Proof. intros; unfold getgroups_spec; vdso_walk. Qed.

Lemma vc_setgroups_spec : vdso_commutes setgroups_spec.
Proof. intros; unfold setgroups_spec; vdso_walk. Qed.

(* ---- kernel/sys.c ---- *)
Lemma vc_setid_spec : forall get put user v,
  vdso_commutes (setid_spec get put user v).
Proof. intros; unfold setid_spec; vdso_walk. Qed.

Lemma vc_setresid_spec : forall get put user r e s,
  vdso_commutes (setresid_spec get put user r e s).
Proof. intros; unfold setresid_spec; vdso_walk. Qed.

Lemma vc_setsid_spec : vdso_commutes setsid_spec.
Proof. intros; unfold setsid_spec; vdso_walk. Qed.

Lemma vc_uname_spec : forall name, vdso_commutes (uname_spec name).
Proof. intros; unfold uname_spec; vdso_walk. Qed.

Lemma vc_prctl_spec : forall option_ arg2,
  vdso_commutes (prctl_spec option_ arg2).
Proof. intros; unfold prctl_spec; vdso_walk. Qed.

Lemma vc_getpid_spec : vdso_commutes getpid_spec.
Proof. intros; unfold getpid_spec; vdso_walk. Qed.

Lemma vc_getid_spec : forall sel, vdso_commutes (getid_spec sel).
Proof. intros; unfold getid_spec; vdso_walk. Qed.

Lemma vc_gettid_spec : vdso_commutes gettid_spec.
Proof. intros; unfold gettid_spec; vdso_walk. Qed.

Lemma vc_prlimit64_spec : forall pid resource new_rlim old_rlim,
  vdso_commutes (prlimit64_spec pid resource new_rlim old_rlim).
Proof. intros; unfold prlimit64_spec; vdso_walk. Qed.

(* ---- net/socket.c ---- *)
Lemma vc_socket_spec : forall domain type protocol,
  vdso_commutes (socket_spec domain type protocol).
Proof. intros; unfold socket_spec; vdso_walk. Qed.

Lemma vc_socketpair_spec : forall family type protocol sv,
  vdso_commutes (socketpair_spec family type protocol sv).
Proof. intros; unfold socketpair_spec; vdso_walk. Qed.

Lemma vc_bind_spec : forall fd addrp addrlen,
  vdso_commutes (bind_spec fd addrp addrlen).
Proof. intros; unfold bind_spec; vdso_walk. Qed.

Lemma vc_listen_spec : forall fd backlog, vdso_commutes (listen_spec fd backlog).
Proof. intros; unfold listen_spec; vdso_walk. Qed.

Lemma vc_accept4_spec : forall fd addrp addrlenp flags,
  vdso_commutes (accept4_spec fd addrp addrlenp flags).
Proof. intros; unfold accept4_spec; vdso_walk. Qed.

Lemma vc_connect_spec : forall fd addrp addrlen,
  vdso_commutes (connect_spec fd addrp addrlen).
Proof. intros; unfold connect_spec; vdso_walk. Qed.

Lemma vc_getsockname_spec : forall fd, vdso_commutes (getsockname_spec fd).
Proof. intros; unfold getsockname_spec; vdso_walk. Qed.

Lemma vc_getpeername_spec : forall fd, vdso_commutes (getpeername_spec fd).
Proof. intros; unfold getpeername_spec; vdso_walk. Qed.

Lemma vc_sendto_spec : forall fd buf count flags addrp addrlen,
  vdso_commutes (sendto_spec fd buf count flags addrp addrlen).
Proof. intros; unfold sendto_spec; vdso_walk. Qed.

Lemma vc_recvfrom_spec : forall fd buf size,
  vdso_commutes (recvfrom_spec fd buf size).
Proof. intros; unfold recvfrom_spec; vdso_walk. Qed.

Lemma vc_setsockopt_spec : forall fd level optlen,
  vdso_commutes (setsockopt_spec fd level optlen).
Proof. intros; unfold setsockopt_spec; vdso_walk. Qed.

Lemma vc_getsockopt_spec : forall fd level optlenp,
  vdso_commutes (getsockopt_spec fd level optlenp).
Proof. intros; unfold getsockopt_spec; vdso_walk. Qed.

Lemma vc_shutdown_spec : forall fd how, vdso_commutes (shutdown_spec fd how).
Proof. intros; unfold shutdown_spec; vdso_walk. Qed.

Lemma vc_sendmsg_spec : forall fd msgp flags,
  vdso_commutes (sendmsg_spec fd msgp flags).
Proof. intros; unfold sendmsg_spec; vdso_walk. Qed.

Lemma vc_recvmsg_spec : forall fd flags, vdso_commutes (recvmsg_spec fd flags).
Proof. intros; unfold recvmsg_spec; vdso_walk. Qed.

(* ---- mm/mmap.c ----

   THE MEMORY ARMS CAPTURE THE MODEL.  [brk_spec] reads it, computes the
   next one from what it read, and installs that with a [modify] that
   discards the model it is applied at, so the continuation is not
   indifferent to the wrapper and [vdso_walk]'s [get_model] rule does not
   apply.  [vdso_walk_dep] is the same walk with both programs in hand.

   The model they build is not a single setter either: it forgets a LIST of
   ranges, which is a fold and so needs an induction rather than a
   conversion.  These two lemmas are that induction, and the walk's model
   equations are rewritten with them. *)

Lemma forget_vm_ranges_with_vdso : forall rs v m,
  forget_vm_ranges rs (with_vdso v m) = with_vdso v (forget_vm_ranges rs m).
Proof.
  induction rs as [|[a n] rs IH]; intros v m; [reflexivity|].
  cbn [forget_vm_ranges].
  rewrite vm_forget_range_with_vdso, IH. reflexivity.
Qed.

Lemma with_brk_next_with_vdso : forall v m req r,
  with_brk_next (with_vdso v m) req r = with_vdso v (with_brk_next m req r).
Proof.
  intros v m req r. unfold with_brk_next. cbn zeta.
  change (m_vmmaps (with_vdso v m)) with (m_vmmaps m).
  rewrite with_vmmaps_with_vdso, forget_vm_ranges_with_vdso. reflexivity.
Qed.

(** The memory constructions, through [VdsoCommute.v]'s other declared
    hook.  [vdso_model_eq] consults it before it starts unfolding, so a
    fold whose frame is an induction is rewritten rather than unfolded
    past. *)
Ltac vdso_extra_eq ::=
  rewrite ?with_brk_next_with_vdso, ?forget_vm_ranges_with_vdso.

Lemma vc_brk_spec : forall req, vdso_commutes (brk_spec req).
Proof. intros; unfold brk_spec; vdso_walk_dep. Qed.

Lemma vc_munmap_spec : forall addr len, vdso_commutes (munmap_spec addr len).
Proof. intros; unfold munmap_spec; vdso_walk. Qed.

(** [mmap_spec] chooses against a budget TEST taken at the model it read,
    so under the wrapper the test is at the wrapped model.  The test reads
    the backing ledgers and the limit and nothing else, so the two are the
    same boolean — by conversion, but not as the same term, and the walk's
    [choose] rule wants one term.  Stated, and added to the unwrapping step
    so the walk meets a single predicate. *)
Lemma with_mmap_backing_with_vdso : forall flags a n v m,
  with_mmap_backing flags a n (with_vdso v m)
  = with_vdso v (with_mmap_backing flags a n m).
Proof. intros flags a n v m; vdso_model_eq. Qed.

Lemma with_mmap_replacement_with_vdso : forall flags a n v m,
  with_mmap_replacement flags a n (with_vdso v m)
  = with_vdso v (with_mmap_replacement flags a n m).
Proof.
  intros flags a n v m. unfold with_mmap_replacement.
  rewrite vm_forget_range_with_vdso, with_mmap_backing_with_vdso.
  reflexivity.
Qed.

Lemma mmap_fixed_rw_budget_ok_with_vdso : forall flags v m addr n,
  mmap_fixed_rw_budget_ok flags (with_vdso v m) addr n
  = mmap_fixed_rw_budget_ok flags m addr n.
Proof.
  intros flags v m addr n. unfold mmap_fixed_rw_budget_ok.
  change (m_vmmaps (with_vdso v m)) with (m_vmmaps m).
  rewrite with_vmmaps_with_vdso, with_mmap_replacement_with_vdso.
  reflexivity.
Qed.

Lemma mmap_fixed_rw_span_budget_ok_with_vdso : forall flags v m addr n,
  mmap_fixed_rw_span_budget_ok flags (with_vdso v m) addr n
  = mmap_fixed_rw_span_budget_ok flags m addr n.
Proof.
  intros flags v m addr n. unfold mmap_fixed_rw_span_budget_ok.
  change (m_vmmaps (with_vdso v m)) with (m_vmmaps m).
  rewrite with_vmmaps_with_vdso, with_mmap_replacement_with_vdso.
  reflexivity.
Qed.

(** The budget gates join the same hook.  They are NOT conversions — the
    gate rebuilds a whole post-state through [with_mmap_replacement], which
    goes through the [forget_vm_ranges] fold — so [vdso_unwrap] cannot
    reach them with [change] and consults the hook instead. *)
Ltac vdso_extra_eq ::=
  rewrite ?with_brk_next_with_vdso, ?forget_vm_ranges_with_vdso,
          ?mmap_fixed_rw_budget_ok_with_vdso,
          ?mmap_fixed_rw_span_budget_ok_with_vdso.

Lemma vc_mmap_spec : forall addr len prot flags fd off,
  vdso_commutes (mmap_spec addr len prot flags fd off).
Proof. intros; unfold mmap_spec; vdso_walk. Qed.

(* ---- mm/mremap.c ---- *)
Lemma vc_mremap_spec : forall old old_size new_size flags,
  vdso_commutes (mremap_spec old old_size new_size flags).
Proof. intros; unfold mremap_spec; vdso_walk. Qed.

(* ---- mm/mprotect.c ---- *)
Lemma vc_mprotect_spec : forall addr len prot,
  vdso_commutes (mprotect_spec addr len prot).
Proof. intros; unfold mprotect_spec; vdso_walk. Qed.

(* ---- mm/madvise.c ---- *)
Lemma vc_madvise_spec : forall addr len advice,
  vdso_commutes (madvise_spec addr len advice).
Proof. intros; unfold madvise_spec; vdso_walk. Qed.

(* ---- drivers/char/random.c ---- *)
Lemma vc_getrandom_spec : forall buf buflen flags,
  vdso_commutes (getrandom_spec buf buflen flags).
Proof. intros; unfold getrandom_spec; vdso_walk. Qed.
