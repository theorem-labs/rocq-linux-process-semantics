(** * LinuxProcessSem.Checks.NsFileFree — no arm of the spec table makes an [ONsFile]

    Not part of the trusted specification: a theorem ABOUT it.

    [State.stream_end] and [State.pipe_end_live] look for the live ends
    of a stream pair or a pipe in the descriptor table, and they skip
    every [FdOpaque] entry.  For an [State.ONsFile] entry that skip is
    right only on a condition [State.ONsFile]'s doc states: the
    namespace and mount model never makes one on an end of a pipe or of
    a stream pair the table tracks.  If one did, that end would still
    have a reference after its tracked descriptor closed, and the peer
    would not see the end close (net/unix/af_unix.c [unix_release_sock]
    and fs/pipe.c [pipe_release] run only at the last reference; read at
    v6.18.44; identical at v6.18.46).

    THIS FILE PROVES THE CONDITION FOR EVERY RUN, as an invariant over
    the arms that can make an [ONsFile] -- and in this model there are
    none.  The namespace and mount model (its arms and its child start
    relation) is not part of it, so the case analysis is over every arm
    of [Checks.Sys.Dispatch.checked_table]:

    - [check_syscall_ns_post]: no arm of the table adds an [ONsFile]
      handle to the descriptor table; every handle the post-model holds,
      the model before the call held ([ns_kept]);
    - [ns_frame_holds]: the same for [Specs.syscall_spec], through
      [Checks.ExecutableSpecs.check_syscall_ok_iff];
    - [star_ns_kept]: the same for any execution ([Run.star]): the
      instruction step, the vDSO call and the materialization keep the
      descriptor table ([Run.mi_account_step_model_frame],
      [State.materialize_model_accesses_frame]);
    - [run_ns_free]: a run from [Run.init_config] starts with the three
      standard channels only, so EVERY model it reaches holds no
      [ONsFile] at all, and [run_opaque_entries_not_ns] says what
      [State.stream_end] and [State.pipe_end_live] need: no [FdOpaque]
      entry they skip is one.

    THE SHAPE IS [Checks.KillFree]'s.  Each arm gets a [_nf] lemma that
    unfolds its checker as that file's [_kf] lemma does, splits every
    branch with [kf_step], and closes each with [nf_close], which follows
    an [ONsFile] entry of the post-table back to the table before the
    call through the table operations the arms use ([fd_insert] of a
    kind that is not [ONsFile], or of an entry copied from the table;
    [fd_remove]; [close_range_fds]; [anon_update]; [share_eventfds];
    [ppoll_record]; the /tmp unlink's conversion).  An arm added to the
    dispatcher without a [_nf] lemma fails [checked_table_ns_post] by
    name.

    WHEN THE NAMESPACE AND MOUNT MODEL LANDS, its arms that make an
    [ONsFile] each owe the condition above for the handle they make, and
    its child start relation owes it for the table it starts from; this
    file's frame stays as it is, since it says the spec table's arms add
    no handle whatever table they start from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint KillFree.
Import ListNotations.
Open Scope bv_scope.

(* -------------------------------------------------------------------------
   The invariant
   ------------------------------------------------------------------------- *)

(** Some entry of [fds] is an [ONsFile] under handle [h]. *)
Definition ns_handle_in (fds : list (word * FdEntry)) (h : N) : Prop :=
  exists fd, In (fd, FdOpaque (ONsFile h)) fds.

(** No new handle: every [ONsFile] handle [fds'] holds, [fds] held. *)
Definition ns_kept (fds fds' : list (word * FdEntry)) : Prop :=
  forall h, ns_handle_in fds' h -> ns_handle_in fds h.

(** No [ONsFile] at all. *)
Definition ns_free (fds : list (word * FdEntry)) : Prop :=
  forall h, ~ ns_handle_in fds h.

(** What one checker outcome owes. *)
Definition ns_post (m m' : Model) : Prop := ns_kept (m_fds m) (m_fds m').

Lemma ns_kept_refl : forall fds, ns_kept fds fds.
Proof. intros fds h H. exact H. Qed.

Lemma ns_kept_trans : forall a b c, ns_kept a b -> ns_kept b c -> ns_kept a c.
Proof. intros a b c Hab Hbc h H. exact (Hab h (Hbc h H)). Qed.

Lemma ns_free_kept : forall a b, ns_free a -> ns_kept a b -> ns_free b.
Proof. intros a b Ha Hab h H. exact (Ha h (Hab h H)). Qed.

Lemma ns_kept_fd_eq : forall m1 m2, m_fd m2 = m_fd m1 -> ns_kept (m_fds m1) (m_fds m2).
Proof. intros m1 m2 E. unfold m_fds. rewrite E. apply ns_kept_refl. Qed.

(* -------------------------------------------------------------------------
   The table operations the arms use
   ------------------------------------------------------------------------- *)

Lemma fd_lookup_In : forall fds k e, fd_lookup fds k = Some e -> In (k, e) fds.
Proof.
  induction fds as [|[k0 e0] r IH]; intros k e H; cbn [fd_lookup] in H;
    [discriminate H|].
  destruct (bv_eqb k0 k) eqn:E; cbv beta iota in H.
  - injection H as <-. apply bv_eqb_eq in E. subst k0. left. reflexivity.
  - right. exact (IH _ _ H).
Qed.

Lemma ns_in_fd_insert : forall fds k e fd h,
  In (fd, FdOpaque (ONsFile h)) (fd_insert fds k e) ->
  e = FdOpaque (ONsFile h) \/ In (fd, FdOpaque (ONsFile h)) fds.
Proof.
  intros fds k e fd h H. unfold fd_insert in H. destruct H as [H|H].
  - left. injection H as _ He. exact He.
  - right. apply filter_In in H. exact (proj1 H).
Qed.

Lemma ns_in_filter : forall (f : word * FdEntry -> bool) fds p,
  In p (List.filter f fds) -> In p fds.
Proof. intros f fds p H. apply filter_In in H. exact (proj1 H). Qed.

Lemma ns_in_fd_remove : forall fds k p, In p (fd_remove fds k) -> In p fds.
Proof. intros fds k p H. exact (ns_in_filter _ _ _ H). Qed.

Lemma ns_in_close_range_fds : forall lo hi fds p,
  In p (close_range_fds lo hi fds) -> In p fds.
Proof. intros lo hi fds p H. exact (ns_in_filter _ _ _ H). Qed.

(** An entry function that never turns another kind into an [ONsFile]. *)
Ltac nf_entry_inv H :=
  repeat (cbv beta iota in H;
          match type of H with
          | context [if ?b then _ else _] => destruct b
          | context [match ?x with _ => _ end] => destruct x
          end);
  first [ exact H | discriminate H ].

Lemma anon_entry_update_ns : forall id g e h,
  anon_entry_update id g e = FdOpaque (ONsFile h) -> e = FdOpaque (ONsFile h).
Proof. intros id g e h H. unfold anon_entry_update in H. destruct e; nf_entry_inv H. Qed.

Lemma eventfd_shared_entry_ns : forall e h,
  eventfd_shared_entry e = FdOpaque (ONsFile h) -> e = FdOpaque (ONsFile h).
Proof. intros e h H. unfold eventfd_shared_entry in H. destruct e; nf_entry_inv H. Qed.

Lemma forfeit_entry_ns : forall e h,
  forfeit_entry e = FdOpaque (ONsFile h) -> e = FdOpaque (ONsFile h).
Proof. intros e h H. unfold forfeit_entry in H. destruct e; nf_entry_inv H. Qed.

Lemma unlink_open_entry_ns : forall c id data pin e h,
  unlink_open_entry c id data pin e = FdOpaque (ONsFile h) -> e = FdOpaque (ONsFile h).
Proof.
  intros c id data pin e h H. unfold unlink_open_entry in H. destruct e; nf_entry_inv H.
Qed.

Lemma ppoll_record_entry_ns : forall fds und sel k e h,
  ppoll_record_entry fds und sel k e = FdOpaque (ONsFile h) -> e = FdOpaque (ONsFile h).
Proof.
  intros fds und sel k e h H. unfold ppoll_record_entry in H. destruct e; nf_entry_inv H.
Qed.

Lemma ns_in_anon_update : forall fds id g fd h,
  In (fd, FdOpaque (ONsFile h)) (anon_update fds id g) ->
  In (fd, FdOpaque (ONsFile h)) fds.
Proof.
  intros fds id g fd h H. unfold anon_update in H. apply in_map_iff in H.
  destruct H as ([k e] & Heq & Hin). cbn [fst snd] in Heq.
  injection Heq as -> He. apply anon_entry_update_ns in He. subst e. exact Hin.
Qed.

Lemma ns_in_unlink_map : forall c id data pin fds fd h,
  In (fd, FdOpaque (ONsFile h))
     (map (fun q : word * FdEntry => (fst q, unlink_open_entry c id data pin (snd q))) fds) ->
  In (fd, FdOpaque (ONsFile h)) fds.
Proof.
  intros c id data pin fds fd h H. apply in_map_iff in H.
  destruct H as ([k e] & Heq & Hin). cbn [fst snd] in Heq.
  injection Heq as -> He. apply unlink_open_entry_ns in He. subst e. exact Hin.
Qed.

Lemma ns_in_ppoll_record : forall fds und sel fd h,
  In (fd, FdOpaque (ONsFile h)) (ppoll_record fds und sel) ->
  In (fd, FdOpaque (ONsFile h)) fds.
Proof.
  intros fds und sel fd h H. unfold ppoll_record in H. apply in_map_iff in H.
  destruct H as ([k e] & Heq & Hin). cbn [fst snd] in Heq.
  injection Heq as -> He. apply ppoll_record_entry_ns in He. subst e. exact Hin.
Qed.

Lemma ns_in_share_eventfds : forall fds fd h,
  In (fd, FdOpaque (ONsFile h)) (share_eventfds fds) ->
  In (fd, FdOpaque (ONsFile h)) fds.
Proof.
  induction fds as [|[k e] r IH]; intros fd h H; cbn [share_eventfds] in H;
    [exact H|].
  destruct H as [H|H].
  - injection H as -> He. apply eventfd_shared_entry_ns in He. subst e.
    left. reflexivity.
  - right. exact (IH _ _ H).
Qed.

(** The caller's table after a successful clone also forfeits its live
    inherited offsets ([forfeit_inherited], under [share_eventfds]); an
    [ONsFile] passes through it unchanged too. *)
Lemma ns_in_forfeit_inherited : forall fds fd h,
  In (fd, FdOpaque (ONsFile h)) (forfeit_inherited fds) ->
  In (fd, FdOpaque (ONsFile h)) fds.
Proof.
  intros fds fd h H. unfold forfeit_inherited in H.
  apply in_map_iff in H as ([k e] & He & Hin). cbn [fst snd] in He.
  injection He as -> He. apply forfeit_entry_ns in He. subst e. exact Hin.
Qed.

Lemma ns_in_anon_place_fds : forall fds fd0 id af bs fds' fd h,
  anon_place_fds fds fd0 id af bs = Some fds' ->
  In (fd, FdOpaque (ONsFile h)) fds' -> In (fd, FdOpaque (ONsFile h)) fds.
Proof.
  intros fds fd0 id af bs fds' fd h E H. unfold anon_place_fds in E. cbv zeta in E.
  repeat (match type of E with context [if ?b then _ else _] => destruct b end;
          cbv beta iota in E);
  first [ discriminate E | injection E as <- ];
  unfold anon_write_back in H; apply ns_in_fd_insert in H;
  (destruct H as [H|H];
   [ discriminate H | exact (ns_in_anon_update _ _ _ _ _ H) ]).
Qed.

(** [dup3]'s table ([File.dup3_fds]): a copy of a kind
    [File.dup_modeled_entry] copies, or a move of a regular file that
    leaves an [OAlias] behind.  Neither installs an [ONsFile]: no opaque
    object is copied or moved. *)
Lemma ns_in_dup3_fds : forall o n e fds fds' fd h,
  dup3_fds o n e fds = Some fds' ->
  In (fd, FdOpaque (ONsFile h)) fds' -> In (fd, FdOpaque (ONsFile h)) fds.
Proof.
  intros o n e fds fds' fd h E H. unfold dup3_fds in E.
  destruct (dup_modeled_entry e) eqn:Hd.
  - injection E as <-. apply ns_in_fd_insert in H. destruct H as [He|H]; [|exact H].
    subst e. cbn in Hd. discriminate Hd.
  - destruct (dup3_moves_entry e) eqn:Hm; [|discriminate E].
    injection E as <-. apply ns_in_fd_insert in H. destruct H as [He|H]; [discriminate He|].
    apply ns_in_fd_insert in H. destruct H as [He|H]; [|exact H].
    subst e. cbn in Hm. discriminate Hm.
Qed.

(* -------------------------------------------------------------------------
   The descriptor table of a post-model
   ------------------------------------------------------------------------- *)

Lemma m_fds_forget_vm_ranges_nf : forall rs m,
  m_fds (forget_vm_ranges rs m) = m_fds m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma m_fds_with_brk_next_nf : forall m req r, m_fds (with_brk_next m req r) = m_fds m.
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  rewrite m_fds_forget_vm_ranges_nf. reflexivity.
Qed.

Lemma m_fds_with_mmap_backing_nf : forall flags a n m,
  m_fds (with_mmap_backing flags a n m) = m_fds m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma m_fds_with_mmap_replacement_nf : forall flags a n m,
  m_fds (with_mmap_replacement flags a n m) = m_fds m.
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  rewrite m_fds_with_mmap_backing_nf. reflexivity.
Qed.

Lemma m_fds_raise_sigpipe_nf : forall m, m_fds (raise_sigpipe m) = m_fds m.
Proof.
  intros m. unfold raise_sigpipe.
  repeat (match goal with |- context [if ?b then _ else _] => destruct b end;
          cbv beta iota);
  reflexivity.
Qed.

Lemma m_fds_sigmask_deliver_model_nf : forall new m,
  m_fds (sigmask_deliver_model new m) = m_fds m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  repeat (match goal with |- context [if ?b then _ else _] => destruct b end;
          cbv beta iota);
  reflexivity.
Qed.

Lemma m_fds_with_accepted_nf : forall v m, m_fds (with_accepted v m) = v.
Proof. reflexivity. Qed.
Lemma m_fds_with_children_nf : forall m, m_fds (with_children m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_child_nf : forall pid m, m_fds (with_child pid m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_pdeath_signal_nf : forall v m, m_fds (with_pdeath_signal v m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_sigpipe_install_nf : forall a m,
  m_fds (with_sigpipe_install a m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_sigpipe_default_nf : forall v m,
  m_fds (with_sigpipe_default v m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_sigpipe_terminal_nf : forall v m,
  m_fds (with_sigpipe_terminal v m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_sigpipe_pending_nf : forall m, m_fds (with_sigpipe_pending m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_vdso_bump_nf : forall m, m_fds (with_vdso_bump m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_vm_backing_nf : forall lz mt m, m_fds (with_vm_backing lz mt m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_mmap_destroyed_nf : forall a n h' m,
  m_fds (with_mmap_destroyed a n h' m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_with_sigchld_dfl_nf : forall b m,
  m_fds (with_sigchld_dfl b m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_sigchld_install_model_nf : forall m,
  m_fds (sigchld_install_model m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_fds_open_cloexec_model_nf : forall flags r m,
  m_fds (open_cloexec_model flags r m) = m_fds m.
Proof.
  intros flags r m. unfold open_cloexec_model.
  destruct (addr_is_error_b r); [reflexivity|].
  destruct (fd_lookup (m_fds m) r); reflexivity.
Qed.

Create HintDb nf_fds.
#[local] Hint Rewrite m_fds_with_fds m_fds_with_vmmaps m_fds_with_stdin
  m_fds_with_urandom m_fds_with_fs m_fds_with_halted m_fds_with_tid
  m_fds_with_rlimit_core m_fds_with_clock m_fds_with_setsid_succeeded
  m_fds_with_pipes m_fds_with_creds m_fds_with_net m_fds_with_abort_terminal
  m_fds_with_killed m_fds_with_nofile m_fds_with_sigabrt_pending
  m_fds_with_sigaltstack_installed m_fds_with_sigmask m_fds_with_statpin
  m_fds_with_utsname
  m_fds_forget_vm_ranges_nf m_fds_with_brk_next_nf m_fds_with_mmap_backing_nf
  m_fds_with_mmap_replacement_nf m_fds_raise_sigpipe_nf
  m_fds_sigmask_deliver_model_nf m_fds_with_accepted_nf m_fds_with_children_nf
  m_fds_with_child_nf
  m_fds_with_pdeath_signal_nf m_fds_with_sigpipe_install_nf
  m_fds_with_sigpipe_default_nf m_fds_with_sigpipe_terminal_nf
  m_fds_with_sigpipe_pending_nf m_fds_with_vdso_bump_nf m_fds_with_vm_backing_nf
  m_fds_with_mmap_destroyed_nf m_fds_with_sigchld_dfl_nf
  m_fds_sigchld_install_model_nf m_fds_with_cloexec m_fds_open_cloexec_model_nf : nf_fds.

(* -------------------------------------------------------------------------
   The tactic
   ------------------------------------------------------------------------- *)

(** The post-models that are named functions of the model before the
    call, unfolded to the table operations above. *)
Ltac nf_norm Hin :=
  cbv beta iota zeta delta [unlink_open_model ppoll_rec Open.procfd_reopen_model
    Open.procfd_trunc_model pipe2_model pipe2_fds1 clone_child_made
    stream_reset_seen anon_write_back anon_set_data] in Hin;
  autorewrite with nf_fds in Hin.

(** A new entry: a kind that is not [ONsFile]; an entry copied from the
    table before the call; or an opaque object the arm's premise says is
    not an [ONsFile]. *)
Ltac nf_fresh He :=
  first
  [ discriminate He
  | (subst; eexists; eapply fd_lookup_In; eassumption)
  | (let He' := fresh "He" in
     injection He as He'; subst; eexists; eapply fd_lookup_In; eassumption)
  | (let He' := fresh "He" in
     injection He as He';
     match goal with Hno : forall h, ?o <> ONsFile h |- _ => destruct (Hno _ He') end) ].

Ltac nf_chase Hin :=
  repeat
    match type of Hin with
    | In _ (fd_insert _ _ _) =>
        apply ns_in_fd_insert in Hin; destruct Hin as [Hin|Hin]; [nf_fresh Hin|]
    | In _ (fd_remove _ _) => apply ns_in_fd_remove in Hin
    | In _ (close_range_fds _ _ _) => apply ns_in_close_range_fds in Hin
    | In _ (anon_update _ _ _) => apply ns_in_anon_update in Hin
    | In _ (share_eventfds _) => apply ns_in_share_eventfds in Hin
    | In _ (forfeit_inherited _) => apply ns_in_forfeit_inherited in Hin
    | In _ (ppoll_record _ _ _) => apply ns_in_ppoll_record in Hin
    | In _ (map _ _) => apply ns_in_unlink_map in Hin
    | In _ ?v =>
        is_var v;
        match goal with
        | E : anon_place_fds _ _ _ _ _ = Some v |- _ =>
            apply (ns_in_anon_place_fds _ _ _ _ _ _ _ _ E) in Hin
        | E : dup3_fds _ _ _ _ = Some v |- _ =>
            apply (ns_in_dup3_fds _ _ _ _ _ _ _ E) in Hin
        end
    | In _ _ =>
        (* a table chosen by a case the outcome did not split (shutdown's
           peer lookup): split it *)
        match type of Hin with
        | context [match ?x with _ => _ end] => destruct x; cbv beta iota in Hin
        end
    end.

Ltac nf_close :=
  unfold ns_post, ns_kept;
  let h := fresh "h" in let fd := fresh "fd" in let Hin := fresh "Hin" in
  intros h [fd Hin]; nf_norm Hin; nf_chase Hin; exists fd; exact Hin.

Ltac nf_finish := nf_close.

(** The atomic sub-checkers [kf_step] does not open, as [kf_done] has
    them in [Checks.KillFree]. *)
Lemma check_efault_or_nf : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros fb eff m m' evs H. unfold check_efault_or in H.
  repeat kf_step H; nf_finish.
Qed.

Lemma check_sigpipe_write_nf : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros eff m m' evs H. unfold check_sigpipe_write in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_ok_iff in H. destruct H as (_ & -> & _). nf_finish.
Qed.

Lemma check_sigpipe_writev_nf : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros reads eff m m' evs H. unfold check_sigpipe_writev in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & _). nf_finish.
Qed.

Ltac nf_stream_base H :=
  first
  [ (eapply check_efault_or_nf in H; exact H)
  | (eapply check_sigpipe_write_nf in H; exact H) ].

Lemma check_stream_read_empty_nf : forall fd id side st nonblock eff m m' evs,
  check_stream_read_empty fd id side st nonblock eff m = CheckOk m' evs ->
  ns_post m m'.
Proof.
  intros fd id side st nonblock eff m m' evs H.
  unfold check_stream_read_empty, check_stream_read_reset in H. cbv beta iota zeta in H.
  repeat (kf_step H || nf_stream_base H); nf_finish.
Qed.

Lemma check_stream_read_nf :
  forall fd id side st nonblock buf count i eff m m' evs,
  check_stream_read fd id side st nonblock buf count i eff m = CheckOk m' evs ->
  ns_post m m'.
Proof.
  intros fd id side st nonblock buf count i eff m m' evs H.
  unfold check_stream_read, check_stream_read_empty, check_stream_read_reset in H.
  cbv beta iota zeta in H.
  repeat (kf_step H || nf_stream_base H); nf_finish.
Qed.

Lemma check_stream_send_nf :
  forall id side st nonblock nosignal n src ledger eff m m' evs,
  check_stream_send id side st nonblock nosignal n src ledger eff m = CheckOk m' evs ->
  ns_post m m'.
Proof.
  intros id side st nonblock nosignal n src ledger eff m m' evs H.
  unfold check_stream_send in H. cbv beta iota zeta in H.
  repeat (kf_step H || nf_stream_base H); nf_finish.
Qed.

Lemma check_stream_write_nf :
  forall id side st nonblock nosignal buf count i eff m m' evs,
  check_stream_write id side st nonblock nosignal buf count i eff m = CheckOk m' evs ->
  ns_post m m'.
Proof.
  intros id side st nonblock nosignal buf count i eff m m' evs H.
  unfold check_stream_write in H. exact (check_stream_send_nf _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Ltac nf_stream H :=
  first
  [ (eapply check_stream_read_nf in H; exact H)
  | (eapply check_stream_read_empty_nf in H; exact H)
  | (eapply check_stream_write_nf in H; exact H)
  | (eapply check_stream_send_nf in H; exact H) ].

(** The new-descriptor answer: the model it installs is [mk fd], and the
    premise asks that one to owe [ns_post]. *)
Lemma check_open_result_nf : forall eff m mk m' evs,
  check_open_result eff m mk = CheckOk m' evs ->
  (forall fd, ns_post m (mk fd)) -> ns_post m m'.
Proof.
  intros eff m mk m' evs H Hmk.
  unfold check_open_result, check_new_fd_result in H.
  repeat kf_step H.
  all: first [ apply Hmk | nf_finish ].
Qed.

Lemma check_readv_imported_nf : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd r iovs0 eff m m' evs H.
  unfold check_readv_imported in H. cbv beta iota zeta in H.
  repeat (kf_step H
          || (eapply check_efault_or_nf in H; exact H)
          || nf_stream H
          || elim (check_readv_gap_frame _ _ H));
  nf_finish.
Qed.

Ltac nf_done H :=
  first
  [ (eapply check_efault_or_nf in H; exact H)
  | (eapply check_sigpipe_write_nf in H; exact H)
  | (eapply check_sigpipe_writev_nf in H; exact H)
  | elim (check_readv_gap_frame _ _ H)
  | nf_stream H
  | (eapply check_readv_imported_nf in H; exact H)
  | (refine (check_open_result_nf _ _ _ _ _ H _);
     let fd := fresh "fd" in intros fd; cbv beta; nf_finish) ].

Ltac nf_use L H := (eapply L in H; exact H).

Ltac nf_frame H :=
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H); nf_finish.

(* -------------------------------------------------------------------------
   The arms
   ------------------------------------------------------------------------- *)

Lemma check_tkill_nf : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros pid sig eff m m' evs H.
  unfold check_tkill, check_tkill_self, check_send_sigabrt in H. nf_frame H.
Qed.

Lemma check_tgkill_nf : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros tgid pid sig eff m m' evs H.
  unfold check_tgkill, check_tkill_self, check_send_sigabrt in H. nf_frame H.
Qed.

Lemma check_rt_sigprocmask_nf : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i how nset oset ss eff m m' evs H. unfold check_rt_sigprocmask in H. nf_frame H.
Qed.

Lemma check_rt_sigaction_sigpipe_nf : forall i act oact eff m m' evs,
  check_rt_sigaction_sigpipe i act oact eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i act oact eff m m' evs H.
  unfold check_rt_sigaction_sigpipe in H. cbv zeta in H.
  destruct (w_is0 act); cbv beta iota in H.
  { apply check_sigpipe_oact_write_model in H. subst m'. nf_finish. }
  destruct (sigaction_struct (in_mem i) act) as [bs|]; cbv beta iota in H.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (_ & -> & _). nf_finish. }
  destruct (negb (Z.eqb (sigaction_field bs 0) SIG_DFL
                  || Z.eqb (sigaction_field bs 0) SIG_IGN)%bool);
    cbv beta iota in H; [discriminate|].
  destruct (Z.eqb (sigaction_field bs 0) SIG_DFL
            && sigpipe_hidden_pending_possible m)%bool;
    cbv beta iota in H; [discriminate|].
  apply check_copyins_after_ok_iff in H. destruct H as (_ & H).
  apply check_sigpipe_oact_write_model in H. subst m'. nf_finish.
Qed.

Lemma check_rt_sigaction_nf : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i sig act oact ss eff m m' evs H.
  unfold check_rt_sigaction in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))); cbv beta iota in H; [nf_frame H|].
  destruct (Z.eqb (bv_unsigned sig) SIGPIPE); cbv beta iota in H.
  { exact (check_rt_sigaction_sigpipe_nf _ _ _ _ _ _ _ H). }
  nf_frame H.
Qed.

Lemma check_brk_nf : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H. unfold check_brk in H. nf_frame H.
Qed.

Lemma check_mmap_nf : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H.
  unfold check_mmap, check_mmap_fixed_overflow in H. nf_frame H.
Qed.

Lemma check_munmap_nf : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H. unfold check_munmap in H. nf_frame H.
Qed.

Lemma check_mremap_nf : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H.
  unfold check_mremap in H. nf_frame H.
Qed.

Lemma check_mprotect_nf : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H.
  unfold check_mprotect in H. nf_frame H.
Qed.

Lemma check_madvise_nf : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H.
  unfold check_madvise in H. nf_frame H.
Qed.

(** Read's and write's helpers, one lemma each, as in [Checks.KillFree]. *)

Lemma nf_read_urandom : forall i buf count eff m m' evs,
  check_read_urandom i buf count eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i buf count eff m m' evs H. unfold check_read_urandom in H. nf_frame H. Qed.

Lemma nf_socket_pending_error : forall e fd peer ch buf count i eff m m' evs,
  check_socket_pending_error e fd peer ch buf count i eff m = CheckOk m' evs ->
  ns_post m m'.
Proof.
  intros e fd peer ch buf count i eff m m' evs H.
  unfold check_socket_pending_error, check_access_ok_zero in H. nf_frame H.
Qed.

Lemma nf_read_proc : forall i buf count eff m m' evs,
  check_read_proc i buf count eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i buf count eff m m' evs H.
  unfold check_read_proc, check_read_proc_bare in H. nf_frame H.
Qed.

Lemma nf_eventfd_read : forall fd ctx buf count i eff m m' evs,
  check_eventfd_read fd ctx buf count i eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros fd ctx buf count i eff m m' evs H. unfold check_eventfd_read in H. nf_frame H.
Qed.

Lemma nf_eventfd_write : forall fd ctx buf count i eff m m' evs,
  check_eventfd_write fd ctx buf count i eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros fd ctx buf count i eff m m' evs H. unfold check_eventfd_write in H. nf_frame H.
Qed.

Lemma nf_write_fault_extend : forall reads m p off eff m' evs,
  check_write_fault_extend reads m p off eff = CheckOk m' evs -> ns_post m m'.
Proof.
  intros reads m p off eff m' evs H. unfold check_write_fault_extend in H. nf_frame H.
Qed.

Lemma nf_anon_fault_extend : forall reads m id data dst eff m' evs,
  check_anon_fault_extend reads m id data dst eff = CheckOk m' evs -> ns_post m m'.
Proof.
  intros reads m id data dst eff m' evs H. unfold check_anon_fault_extend in H. nf_frame H.
Qed.

Lemma nf_anon_write_fault : forall reads m id af eff m' evs,
  check_anon_write_fault reads m id af eff = CheckOk m' evs -> ns_post m m'.
Proof.
  intros reads m id af eff m' evs H. unfold check_anon_write_fault in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_anon_fault_extend H); nf_finish.
Qed.

Lemma check_read_nf : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_read, check_read_file_data, check_access_ok_zero in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H
          || (apply check_read_opaque_keeps in H; destruct H as [-> ->])
          || nf_use nf_read_urandom H || nf_use nf_socket_pending_error H
          || nf_use nf_read_proc H || nf_use nf_eventfd_read H);
  nf_finish.
Qed.

Lemma check_write_nf : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_write, check_access_ok_zero in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H
          || (apply check_write_opaque_keeps in H; destruct H as [-> ->])
          || nf_use nf_write_fault_extend H || nf_use nf_eventfd_write H
          || nf_use nf_anon_write_fault H);
  nf_finish.
Qed.

Lemma check_pread64_nf : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd buf count pos eff m m' evs H. unfold check_pread64 in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_read_urandom H); nf_finish.
Qed.

Lemma check_pwrite64_nf : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd buf count pos eff m m' evs H. unfold check_pwrite64 in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H
          || nf_use nf_write_fault_extend H || nf_use nf_anon_fault_extend H);
  nf_finish.
Qed.

Lemma check_readv_nf : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i fd iov iovcnt eff m m' evs H. unfold check_readv in H. nf_frame H. Qed.

Lemma check_writev_nf : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd iov iovcnt eff m m' evs H. unfold check_writev in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H
          || nf_use nf_write_fault_extend H || nf_use nf_anon_write_fault H);
  nf_finish.
Qed.

Lemma check_pwritev2_nf :
  forall i fd iov iovcnt pos_l pos_h flags eff m m' evs,
  check_pwritev2 i fd iov iovcnt pos_l pos_h flags eff m = CheckOk m' evs ->
  ns_post m m'.
Proof.
  intros i fd iov iovcnt pos_l pos_h flags eff m m' evs H. unfold check_pwritev2 in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_anon_fault_extend H); nf_finish.
Qed.

(** Openat's sub-checkers, one lemma each, as in [Checks.KillFree]. *)

Lemma nf_open_wronly : forall p eff m m' evs,
  check_create_wronly p eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros p eff m m' evs H. unfold check_create_wronly in H. nf_frame H. Qed.

Lemma nf_open_append : forall p eff m m' evs,
  check_open_append p eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros p eff m m' evs H. unfold check_open_append in H. nf_frame H. Qed.

Lemma nf_open_rdwr : forall p fs' eff m m' evs,
  check_open_rdwr p fs' eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros p fs' eff m m' evs H. unfold check_open_rdwr in H. nf_frame H. Qed.

Lemma nf_openat_read : forall p eff m m' evs,
  Open.check_openat_read p eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros p eff m m' evs H. unfold Open.check_openat_read in H. nf_frame H. Qed.

Lemma nf_openat_create : forall p eff m m' evs,
  Open.check_openat_create p eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros p eff m m' evs H. unfold Open.check_openat_create in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_open_wronly H); nf_finish.
Qed.

Lemma nf_openat_excl : forall p eff m m' evs,
  Open.check_openat_excl p eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros p eff m m' evs H. unfold Open.check_openat_excl in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_open_wronly H); nf_finish.
Qed.

Lemma nf_openat_append : forall excl p eff m m' evs,
  Open.check_openat_append excl p eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros excl p eff m m' evs H. unfold Open.check_openat_append in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_open_append H); nf_finish.
Qed.

Lemma nf_openat_rdwr : forall creat trunc p eff m m' evs,
  Open.check_openat_rdwr creat trunc p eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros creat trunc p eff m m' evs H. unfold Open.check_openat_rdwr in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_open_rdwr H); nf_finish.
Qed.

Lemma nf_openat_rdwr_excl : forall p eff m m' evs,
  Open.check_openat_rdwr_excl p eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros p eff m m' evs H. unfold Open.check_openat_rdwr_excl in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_open_rdwr H); nf_finish.
Qed.

Lemma nf_openat_dir : forall p eff m m' evs,
  Open.check_openat_dir p eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros p eff m m' evs H. unfold Open.check_openat_dir in H. nf_frame H. Qed.

Lemma nf_openat_localtime : forall flags eff m m' evs,
  Open.check_openat_localtime flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros flags eff m m' evs H. unfold Open.check_openat_localtime in H. nf_frame H.
Qed.

Lemma nf_open_devnull : forall rd wr eff m m' evs,
  Open.check_open_devnull rd wr eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros rd wr eff m m' evs H. unfold Open.check_open_devnull in H. nf_frame H. Qed.

Lemma nf_openat_devnull : forall flags eff m m' evs,
  Open.check_openat_devnull flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros flags eff m m' evs H. unfold Open.check_openat_devnull in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_open_devnull H); nf_finish.
Qed.

Lemma nf_open_urandom : forall eff m m' evs,
  Open.check_open_urandom eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros eff m m' evs H. unfold Open.check_open_urandom in H. nf_frame H. Qed.

Lemma nf_openat_urandom : forall flags eff m m' evs,
  Open.check_openat_urandom flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros flags eff m m' evs H. unfold Open.check_openat_urandom in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_open_urandom H); nf_finish.
Qed.

Lemma nf_openat_tmp : forall n p flags eff m m' evs,
  Open.check_openat_tmp n p flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros n p flags eff m m' evs H. unfold Open.check_openat_tmp in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_openat_read H
          || nf_use nf_openat_create H || nf_use nf_openat_rdwr_excl H);
  nf_finish.
Qed.

Lemma nf_openat_sep : forall p flags eff m m' evs,
  Open.check_openat_sep p flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros p flags eff m m' evs H. unfold Open.check_openat_sep in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_openat_localtime H
          || nf_use nf_openat_devnull H || nf_use nf_openat_urandom H
          || nf_use nf_openat_tmp H);
  nf_finish.
Qed.

Lemma nf_openat_resolved : forall p flags eff m m' evs,
  Open.check_openat_resolved p flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros p flags eff m m' evs H. unfold Open.check_openat_resolved in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_openat_sep H
          || nf_use nf_openat_read H || nf_use nf_openat_create H
          || nf_use nf_openat_excl H || nf_use nf_openat_dir H
          || nf_use nf_openat_append H || nf_use nf_openat_rdwr H
          || nf_use nf_openat_rdwr_excl H);
  nf_finish.
Qed.

(** The procfs open's answer installs [FdOpaque o]; its two callers pass
    [OProcPath] and [OProcFile], never an [ONsFile]. *)
Lemma nf_proc_open_result : forall o eff m m' evs,
  Open.check_proc_open_result o eff m = CheckOk m' evs ->
  (forall h, o <> ONsFile h) -> ns_post m m'.
Proof.
  intros o eff m m' evs H Hno. unfold Open.check_proc_open_result in H. nf_frame H.
Qed.

(** The "/proc/self/fd/N" reopen: a new [FdAnon] beside the agreeing
    one, never an [ONsFile] (the opaque kinds at N decline). *)
Lemma nf_openat_procfd : forall n flags eff m m' evs,
  Open.check_openat_procfd n flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros n flags eff m m' evs H. unfold Open.check_openat_procfd in H. nf_frame H.
Qed.

Lemma nf_openat_proc : forall c flags eff m m' evs,
  Open.check_openat_proc c flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros c flags eff m m' evs H. unfold Open.check_openat_proc in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H
          || (eapply nf_proc_open_result in H;
              first [ exact H
                    | (let h' := fresh "h" in let Ho := fresh "Ho" in
                       intros h' Ho; discriminate Ho) ])
          || nf_use nf_openat_procfd H);
  nf_finish.
Qed.

Lemma nf_openat_body : forall i dirfd pathp flags eff m m' evs,
  Open.check_openat_body i dirfd pathp flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H. unfold Open.check_openat_body in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_openat_proc H
          || nf_use nf_openat_resolved H);
  nf_finish.
Qed.

Lemma check_openat_table_nf : forall i dirfd pathp flags eff m m' evs,
  check_openat_table i dirfd pathp flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H. unfold check_openat_table in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_openat_body H); nf_finish.
Qed.

(** The close-on-exec step after the table writes [State.m_cloexec]
    alone ([Open.open_cloexec_model]). *)
Lemma check_openat_nf : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H. unfold check_openat in H.
  destruct (check_openat_table i dirfd pathp flags eff m) as [m0 evs0| |] eqn:E;
    try discriminate H.
  injection H as <- <-. apply check_openat_table_nf in E.
  unfold ns_post in *. rewrite m_fds_open_cloexec_model_nf. exact E.
Qed.

Lemma check_close_nf : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros fd eff m m' evs H. unfold check_close in H. nf_frame H. Qed.

Lemma check_lseek_nf : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros fd off whence eff m m' evs H. unfold check_lseek in H. nf_frame H. Qed.

Lemma check_ftruncate_nf : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros fd len eff m m' evs H. unfold check_ftruncate in H. nf_frame H. Qed.

Lemma check_ioctl_nf : forall i fd req eff m m' evs,
  check_ioctl i fd req eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd req eff m m' evs H.
  unfold check_ioctl, check_siocgifindex, check_ifreq_writeback in H. nf_frame H.
Qed.

Lemma check_readlinkat_nf : forall i dirfd eff m m' evs,
  check_readlinkat i dirfd eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i dirfd eff m m' evs H. unfold check_readlinkat in H. nf_frame H. Qed.

Lemma check_wait4_nf : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H. unfold check_wait4 in H.
  nf_frame H.
Qed.

Lemma check_fsync_nf : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros fd eff m m' evs H. unfold check_fsync in H. nf_frame H. Qed.

Lemma check_getdents64_nf : forall i fd dirent count eff m m' evs,
  check_getdents64 i fd dirent count eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd dirent count eff m m' evs H.
  unfold check_getdents64, check_getdents64_opaque, check_procfd_getdents in H.
  nf_frame H.
Qed.

Lemma check_flock_nf : forall fd cmd eff m m' evs,
  check_flock fd cmd eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros fd cmd eff m m' evs H. unfold check_flock in H. nf_frame H. Qed.

Lemma check_exit_nf : forall code eff m m' evs,
  check_exit code eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros code eff m m' evs H. unfold check_exit in H. nf_frame H. Qed.

Lemma check_set_tid_address_nf : forall eff m m' evs,
  check_set_tid_address eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros eff m m' evs H. unfold check_set_tid_address in H. nf_frame H. Qed.

Lemma check_getpid_nf : forall eff m m' evs,
  check_getpid eff m = CheckOk m' evs -> ns_post m m'.
Proof. exact check_set_tid_address_nf. Qed.

Lemma check_gettid_nf : forall eff m m' evs,
  check_gettid eff m = CheckOk m' evs -> ns_post m m'.
Proof. exact check_set_tid_address_nf. Qed.

Lemma check_setsid_nf : forall eff m m' evs,
  check_setsid eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros eff m m' evs H. unfold check_setsid in H. nf_frame H. Qed.

Lemma check_uname_nf : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i name eff m m' evs H. unfold check_uname, check_uname_copy in H. nf_frame H.
Qed.

Lemma check_prctl_nf : forall i option_ arg2 eff m m' evs,
  check_prctl i option_ arg2 eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i option_ arg2 eff m m' evs H. unfold check_prctl, check_ret_writes in H.
  nf_frame H.
Qed.

Lemma check_getppid_nf : forall eff m m' evs,
  check_getppid eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros eff m m' evs H. unfold check_getppid in H. nf_frame H. Qed.

Lemma check_getsid_nf : forall pid eff m m' evs,
  check_getsid pid eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros pid eff m m' evs H. unfold check_getsid, check_pid_choice in H. nf_frame H.
Qed.

Lemma check_getresid_nf : forall i get rp ep sp eff m m' evs,
  check_getresid i get rp ep sp eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i get rp ep sp eff m m' evs H. unfold check_getresid, check_ret_writes in H.
  nf_frame H.
Qed.

Lemma check_capget_nf : forall i header dataptr eff m m' evs,
  check_capget i header dataptr eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i header dataptr eff m m' evs H. unfold check_capget, check_capget_copy in H.
  nf_frame H.
Qed.

Lemma check_capset_nf : forall i header data eff m m' evs,
  check_capset i header data eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i header data eff m m' evs H. unfold check_capset in H. nf_frame H. Qed.

Lemma check_close_range_nf : forall fd max_fd flags eff m m' evs,
  check_close_range fd max_fd flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros fd max_fd flags eff m m' evs H. unfold check_close_range in H. nf_frame H.
Qed.

Lemma check_prlimit64_nf : forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs ->
  ns_post m m'.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H.
  unfold check_prlimit64, check_rlim64_read in H. nf_frame H.
Qed.

Lemma check_getrandom_nf : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i buf cap flags eff m m' evs H.
  unfold check_getrandom, check_getrandom_zero in H. nf_frame H.
Qed.

Lemma check_gettimeofday_nf : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i tv tz eff m m' evs H. unfold check_gettimeofday in H. nf_frame H. Qed.

Lemma check_clock_gettime_nf : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i clkid tp eff m m' evs H. unfold check_clock_gettime in H. nf_frame H. Qed.

Lemma check_clock_getres_nf : forall i clkid tp eff m m' evs,
  check_clock_getres i clkid tp eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_getres, check_clock_getres_result in H. nf_frame H.
Qed.

Lemma check_nanosleep_nf : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i rqtp rmtp eff m m' evs H. unfold check_nanosleep in H. nf_frame H. Qed.

(** dup and dup3 copy an entry they found in the table, so a copy is
    never a new handle ([nf_fresh]'s second alternative). *)
Lemma check_dup_nf : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros oldfd eff m m' evs H. unfold check_dup, check_dup_result in H. nf_frame H.
Qed.

Lemma check_dup3_nf : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros oldfd newfd flags eff m m' evs H. unfold check_dup3 in H. nf_frame H.
Qed.

Lemma check_unlinkat_nf : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat, Namei.check_unlinkat_body, Namei.check_unlinkat_tmp,
    Namei.check_unlink_found, check_unlink_result,
    Namei.check_unlink_open_tmp, check_unlink_open_result, check_unlink_type_result in H.
  nf_frame H.
Qed.

Lemma check_faccessat_nf : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  nf_frame H.
Qed.

Lemma check_faccessat2_nf : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  nf_frame H.
Qed.

Lemma check_pselect6_nf : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold check_pselect6, check_pselect_answer in H. nf_frame H.
Qed.

Lemma check_ppoll_nf : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll, check_pselect_answer in H. nf_frame H.
Qed.

(** Fstat's and newfstatat's helpers, one lemma each, as in
    [Checks.KillFree]. *)

Lemma nf_fstat_deliver_by : forall ok statbuf p pin eff m m' evs,
  check_fstat_deliver_by ok statbuf p pin eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros ok statbuf p pin eff m m' evs H. unfold check_fstat_deliver_by in H. nf_frame H.
Qed.

Lemma nf_fstat_deliver : forall statbuf n p pin eff m m' evs,
  check_fstat_deliver statbuf n p pin eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros statbuf n p pin eff m m' evs H. unfold check_fstat_deliver in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_fstat_deliver_by H); nf_finish.
Qed.

Lemma nf_fstat_file : forall i p statbuf eff m m' evs,
  check_fstat_file i p statbuf eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i p statbuf eff m m' evs H. unfold check_fstat_file in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_fstat_deliver H
          || nf_use nf_fstat_deliver_by H);
  nf_finish.
Qed.

Lemma nf_fstat_chrdev : forall ok p i statbuf eff m m' evs,
  check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros ok p i statbuf eff m m' evs H. unfold check_fstat_chrdev in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_fstat_deliver H
          || nf_use nf_fstat_deliver_by H);
  nf_finish.
Qed.

Lemma nf_fstat_devnull : forall i statbuf eff m m' evs,
  check_fstat_devnull i statbuf eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i statbuf eff m m' evs H. unfold check_fstat_devnull in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_fstat_chrdev H); nf_finish.
Qed.

Lemma nf_fstat_urandom : forall i statbuf eff m m' evs,
  check_fstat_urandom i statbuf eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i statbuf eff m m' evs H. unfold check_fstat_urandom in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_fstat_chrdev H); nf_finish.
Qed.

Lemma nf_fstat_anon_deliver : forall statbuf id n pin eff m m' evs,
  check_fstat_anon_deliver statbuf id n pin eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros statbuf id n pin eff m m' evs H. unfold check_fstat_anon_deliver in H.
  nf_frame H.
Qed.

Lemma nf_fstat_anon : forall i id af statbuf eff m m' evs,
  check_fstat_anon i id af statbuf eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i id af statbuf eff m m' evs H. unfold check_fstat_anon in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_fstat_anon_deliver H); nf_finish.
Qed.

Lemma nf_newfstatat_proc_errno : forall reads eff m m' evs,
  check_newfstatat_proc_errno reads eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros reads eff m m' evs H. unfold check_newfstatat_proc_errno in H. nf_frame H.
Qed.

Lemma nf_newfstatat_proc : forall i reads statbuf eff m m' evs,
  check_newfstatat_proc i reads statbuf eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i reads statbuf eff m m' evs H. unfold check_newfstatat_proc in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_newfstatat_proc_errno H); nf_finish.
Qed.

Lemma check_newfstatat_nf : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i dirfd pathp flag eff m m' evs H. unfold check_newfstatat, check_newfstatat_proc, check_newfstatat_proc_errno in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H || nf_use nf_newfstatat_proc H
          || nf_use nf_newfstatat_proc_errno H);
  nf_finish.
Qed.

Lemma check_fstat_nf : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd statbuf eff m m' evs H. unfold check_fstat in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || nf_done H
          || (apply check_fstat_opaque_keeps in H; destruct H as [-> ->])
          || nf_use nf_fstat_file H
          || nf_use nf_fstat_devnull H || nf_use nf_fstat_urandom H
          || nf_use nf_fstat_anon H);
  nf_finish.
Qed.

Lemma check_getid_nf : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros sel eff m m' evs H. unfold check_getid in H. nf_frame H. Qed.

Lemma check_setid_nf : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros get put user v eff m m' evs H. unfold check_setid, check_setid_result in H.
  nf_frame H.
Qed.

Lemma check_setresid_nf : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros get put user r e sv eff m m' evs H.
  unfold check_setresid, check_setid_result in H. nf_frame H.
Qed.

Lemma check_getgroups_nf : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros gidsetsize eff m m' evs H. unfold check_getgroups in H. nf_frame H. Qed.

Lemma check_setgroups_nf : forall i eff m m' evs,
  check_setgroups i eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i eff m m' evs H. unfold check_setgroups in H. nf_frame H. Qed.

Lemma check_socket_nf : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros domain type protocol eff m m' evs H.
  unfold check_socket, check_new_fd_result, check_errno_or_list in H. nf_frame H.
Qed.

Lemma check_bind_nf : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_bind, check_errno_or_success in H. nf_frame H.
Qed.

Lemma check_listen_nf : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros fd backlog eff m m' evs H.
  unfold check_listen, check_errno_or_success, check_errno_only in H. nf_frame H.
Qed.

Lemma check_accept4_nf : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H.
  unfold check_accept4, check_new_fd_result, check_errno_or_success, check_errno_only,
    check_errno_or_list in H.
  nf_frame H.
Qed.

Lemma check_fcntl_nf : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros fd cmd arg eff m m' evs H. unfold check_fcntl in H. nf_frame H. Qed.

Lemma check_sched_setscheduler_nf : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i pid policy param eff m m' evs H. unfold check_sched_setscheduler in H.
  nf_frame H.
Qed.

Lemma check_sched_getaffinity_nf : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros len eff m m' evs H. unfold check_sched_getaffinity in H. nf_frame H. Qed.

Lemma check_sched_yield_nf : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros eff m m' evs H. unfold check_sched_yield in H. nf_frame H. Qed.

Lemma check_sigaltstack_nf : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i uss uoss eff m m' evs H. unfold check_sigaltstack in H. nf_frame H. Qed.

Lemma check_futex_nf : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i uaddr op val utime eff m m' evs H.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  nf_frame H.
Qed.

Lemma check_set_robust_list_nf : forall len eff m m' evs,
  check_set_robust_list len eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros len eff m m' evs H. unfold check_set_robust_list in H. nf_frame H. Qed.

(** A successful clone shares the eventfds ([share_eventfds]); an
    [ONsFile] passes through it unchanged.  A host refuser's errno
    ([check_clone_ok_inv], [check_clone3_ok_inv]) and the argument
    checks' -EINVAL ([check_clone_einval], [check_clone3_einval]) leave
    the model as it was. *)
Lemma check_clone_nf : forall i flags eff m m' evs,
  check_clone i flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i flags eff m m' evs H.
  destruct (check_clone_ok_inv _ _ _ _ _ _ H)
    as [(-> & _ & _)|[(e & He & _)|[(e & He & _)|[He|He]]]];
    [ exact (ns_kept_refl _)
    | clear H;
      unfold check_clone_resolve, check_clone_answer, check_clone_ns_resolve,
        check_clone_ns_answer, check_clone_einval, check_clone_ns_refused in He;
      nf_frame He .. ].
Qed.

Lemma check_clone3_nf : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i uargs size eff m m' evs H.
  destruct (check_clone3_ok_inv _ _ _ _ _ _ _ H)
    as [(-> & _ & _)|[(reads & He)|[(reads & en & _ & He)|(e & He & _)]]];
    [ exact (ns_kept_refl _)
    | clear H;
      unfold check_clone3_resolve, check_clone_resolve, check_clone_answer in He;
      nf_frame He .. ].
Qed.

Lemma check_getsockname_nf : forall i fd eff m m' evs,
  check_getsockname i fd eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd eff m m' evs H.
  unfold check_getsockname, check_getsockname_core, check_stream_getname,
    check_ret_writes_copyins in H.
  nf_frame H.
Qed.

Lemma check_getpeername_nf : forall i fd eff m m' evs,
  check_getpeername i fd eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd eff m m' evs H.
  unfold check_getpeername, check_getpeername_core, check_stream_getname,
    check_ret_writes_copyins in H.
  nf_frame H.
Qed.

Lemma check_setsockopt_nf : forall i fd level optlen eff m m' evs,
  check_setsockopt i fd level optlen eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd level optlen eff m m' evs H.
  unfold check_setsockopt, check_setsockopt_core, check_stream_setsockopt, check_seqpacket_setsockopt in H.
  nf_frame H.
Qed.

Lemma check_getsockopt_nf : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd level optlenp eff m m' evs H.
  unfold check_getsockopt, check_getsockopt_core, check_stream_getsockopt,
    check_ret_writes_copyins in H.
  nf_frame H.
Qed.

Lemma check_shutdown_nf : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros fd how eff m m' evs H.
  unfold check_shutdown, check_shutdown_core, check_stream_shutdown in H. nf_frame H.
Qed.

Lemma check_sendto_nf : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd buf count flags addrp eff m m' evs H.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H. nf_frame H.
Qed.

Lemma check_sendmsg_nf : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd msgp flags eff m m' evs H.
  unfold check_sendmsg, check_send_on_socket in H. nf_frame H.
Qed.

Lemma check_socketpair_nf : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i family type protocol sv eff m m' evs H.
  unfold check_socketpair, check_socketpair_unix, check_socketpair_seqpacket_written,
    check_socketpair_unix_written, check_socketpair_written, check_socketpair_faulted,
    check_errno_only in H.
  cbv zeta in H.
  nf_frame H.
Qed.

Lemma check_recvfrom_nf : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd buf size eff m m' evs H.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H. nf_frame H.
Qed.

Lemma check_recvmsg_nf : forall i fd flags eff m m' evs,
  check_recvmsg i fd flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fd flags eff m m' evs H.
  unfold check_recvmsg, check_seqpacket_recvmsg, check_recvmsg_eof_writes,
    check_ret_writes_copyins, check_recv_fd_answer in H.
  nf_frame H.
Qed.

Lemma check_connect_nf : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros i fd addrp addrlen eff m m' evs H. unfold check_connect in H. nf_frame H. Qed.

Lemma check_timerfd_create_nf : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros clkid flags eff m m' evs H. unfold check_timerfd_create in H. nf_frame H.
Qed.

Lemma check_eventfd2_nf : forall i flags eff m m' evs,
  check_eventfd2 i flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i flags eff m m' evs H. unfold check_eventfd2, check_new_fd_result in H.
  nf_frame H.
Qed.

Lemma check_pipe2_nf : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i fildes flags eff m m' evs H. unfold check_pipe2, pipe2_model in H. nf_frame H.
Qed.

Lemma check_getcwd_nf : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros size eff m m' evs H. unfold check_getcwd in H. nf_frame H. Qed.

Lemma check_epoll_create1_nf : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> ns_post m m'.
Proof. intros flags32 eff m m' evs H. unfold check_epoll_create1 in H. nf_frame H. Qed.

Lemma check_epoll_ctl_nf : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i epfd op32 tfd event eff m m' evs H. unfold check_epoll_ctl in H. nf_frame H.
Qed.

Lemma check_epoll_pwait_nf :
  forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs ->
  ns_post m m'.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H.
  unfold check_epoll_pwait in H. nf_frame H.
Qed.

(** The three arms procstate-migration adds beside C1's: [kill] (its
    self-kill rebuilds [ProcState] alone), [setns] and [signalfd4] (a new
    descriptor that is not an [ONsFile]). *)
Lemma check_kill_nf : forall pid sig eff m m' evs,
  check_kill pid sig eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros pid sig eff m m' evs H.
  unfold check_kill, check_kill_self in H. nf_frame H.
Qed.

Lemma check_setns_nf : forall fd eff m m' evs,
  check_setns fd eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros fd eff m m' evs H. unfold check_setns in H. nf_frame H.
Qed.

Lemma check_signalfd4_nf : forall i ufd mask sizemask flags eff m m' evs,
  check_signalfd4 i ufd mask sizemask flags eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i ufd mask sizemask flags eff m m' evs H.
  unfold check_signalfd4, check_new_fd_result in H. nf_frame H.
Qed.

(* -------------------------------------------------------------------------
   The table, the dispatcher, the spec
   ------------------------------------------------------------------------- *)

Definition arm_ns_post (c : CheckedArm) : Prop :=
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs -> ns_post m m'.

(** Every arm discharges it.  As in [Checks.KillFree], the last
    alternative names the lemma an uncovered arm needs. *)
Lemma checked_table_ns_post : Forall arm_ns_post checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_ns_post).
  all: unfold arm_ns_post; intros i eff m m' evs H;
       autorewrite with arm_unfold in H.
  all: first
    [ fail
    | eapply check_brk_nf; eassumption
    | eapply check_mmap_nf; eassumption
    | eapply check_munmap_nf; eassumption
    | eapply check_mremap_nf; eassumption
    | eapply check_mprotect_nf; eassumption
    | eapply check_madvise_nf; eassumption
    | eapply check_read_nf; eassumption
    | eapply check_write_nf; eassumption
    | eapply check_pread64_nf; eassumption
    | eapply check_pwrite64_nf; eassumption
    | eapply check_readv_nf; eassumption
    | eapply check_writev_nf; eassumption
    | eapply check_pwritev2_nf; eassumption
    | eapply check_openat_nf; eassumption
    | eapply check_close_nf; eassumption
    | eapply check_lseek_nf; eassumption
    | eapply check_ftruncate_nf; eassumption
    | eapply check_ioctl_nf; eassumption
    | eapply check_readlinkat_nf; eassumption
    | eapply check_wait4_nf; eassumption
    | eapply check_fsync_nf; eassumption
    | eapply check_getdents64_nf; eassumption
    | eapply check_flock_nf; eassumption
    | eapply check_exit_nf; eassumption
    | eapply check_set_tid_address_nf; eassumption
    | eapply check_getpid_nf; eassumption
    | eapply check_gettid_nf; eassumption
    | eapply check_setsid_nf; eassumption
    | eapply check_uname_nf; eassumption
    | eapply check_prctl_nf; eassumption
    | eapply check_prlimit64_nf; eassumption
    | eapply check_getrandom_nf; eassumption
    | eapply check_gettimeofday_nf; eassumption
    | eapply check_clock_gettime_nf; eassumption
    | eapply check_clock_getres_nf; eassumption
    | eapply check_nanosleep_nf; eassumption
    | eapply check_dup_nf; eassumption
    | eapply check_dup3_nf; eassumption
    | eapply check_unlinkat_nf; eassumption
    | eapply check_faccessat_nf; eassumption
    | eapply check_faccessat2_nf; eassumption
    | eapply check_pselect6_nf; eassumption
    | eapply check_ppoll_nf; eassumption
    | eapply check_newfstatat_nf; eassumption
    | eapply check_fstat_nf; eassumption
    | eapply check_getid_nf; eassumption
    | eapply check_setid_nf; eassumption
    | eapply check_setresid_nf; eassumption
    | eapply check_getgroups_nf; eassumption
    | eapply check_setgroups_nf; eassumption
    | eapply check_socket_nf; eassumption
    | eapply check_bind_nf; eassumption
    | eapply check_listen_nf; eassumption
    | eapply check_accept4_nf; eassumption
    | eapply check_fcntl_nf; eassumption
    | eapply check_sched_setscheduler_nf; eassumption
    | eapply check_sched_getaffinity_nf; eassumption
    | eapply check_sched_yield_nf; eassumption
    | eapply check_sigaltstack_nf; eassumption
    | eapply check_rt_sigaction_nf; eassumption
    | eapply check_tkill_nf; eassumption
    | eapply check_kill_nf; eassumption
    | eapply check_tgkill_nf; eassumption
    | eapply check_rt_sigprocmask_nf; eassumption
    | eapply check_futex_nf; eassumption
    | eapply check_set_robust_list_nf; eassumption
    | eapply check_clone_nf; eassumption
    | eapply check_clone3_nf; eassumption
    | eapply check_getsockname_nf; eassumption
    | eapply check_getpeername_nf; eassumption
    | eapply check_setsockopt_nf; eassumption
    | eapply check_getsockopt_nf; eassumption
    | eapply check_shutdown_nf; eassumption
    | eapply check_sendto_nf; eassumption
    | eapply check_sendmsg_nf; eassumption
    | eapply check_socketpair_nf; eassumption
    | eapply check_recvfrom_nf; eassumption
    | eapply check_recvmsg_nf; eassumption
    | eapply check_connect_nf; eassumption
    | eapply check_timerfd_create_nf; eassumption
    | eapply check_eventfd2_nf; eassumption
    | eapply check_pipe2_nf; eassumption
    | eapply check_getcwd_nf; eassumption
    | eapply check_epoll_create1_nf; eassumption
    | eapply check_epoll_ctl_nf; eassumption
    | eapply check_epoll_pwait_nf; eassumption
    | eapply check_getppid_nf; eassumption
    | eapply check_getsid_nf; eassumption
    | eapply check_getresid_nf; eassumption
    | eapply check_capget_nf; eassumption
    | eapply check_capset_nf; eassumption
    | eapply check_close_range_nf; eassumption
    | eapply check_setns_nf; eassumption
    | eapply check_signalfd4_nf; eassumption
    | fail 1 "checked_table_ns_post has no case for this dispatcher arm: give the new checker a *_nf lemma and add it to the list above" ].
Qed.

Theorem check_syscall_ns_post : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs -> ns_post m m'.
Proof.
  intros i eff m m' evs H. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_ns_post as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H).
Qed.

(** THE FRAME, for the spec: no outcome of [Specs.syscall_spec] adds an
    [ONsFile] handle to the table. *)
Definition ns_frame : Prop :=
  forall i m eff m' evs,
    syscall_spec i m (Ok eff m' evs) -> ns_kept (m_fds m) (m_fds m').

Theorem ns_frame_holds : ns_frame.
Proof.
  intros i m eff m' evs Hs. apply check_syscall_ok_iff in Hs.
  exact (check_syscall_ns_post _ _ _ _ _ Hs).
Qed.

(* -------------------------------------------------------------------------
   The consequences for runs
   ------------------------------------------------------------------------- *)

(** One step: the instruction step and the materialization keep the
    descriptor table ([m_fd]), and every outcome a step consumes is
    [ns_frame]'s. *)
Lemma sstep_ns_kept : forall segs ms model evs c',
  sstep segs (mkCfg ms model) evs (SNext c') ->
  ns_kept (m_fds model) (m_fds (cfg_model c')).
Proof.
  intros segs ms model evs c' Hstep.
  inversion Hstep; subst; cbn [cfg_model].
  all: first
    [ match goal with
      | Ha : _ = RiscvSemantics.MachineOk (_, _) |- _ =>
          apply mi_account_step_model_frame in Ha; destruct Ha as (Hfd & _);
          apply ns_kept_fd_eq; exact Hfd
      end
    | match goal with
      | Hs : syscall_spec _ _ (Ok _ ?m1 _),
        Hm : materialize_model_accesses ?m1 _ = Some _ |- _ =>
          apply materialize_model_accesses_frame in Hm; destruct Hm as (Hfd & _);
          eapply ns_kept_trans; [exact (ns_frame_holds _ _ _ _ _ Hs) |];
          apply ns_kept_fd_eq; exact Hfd
      end
    | match goal with
      | Hs : syscall_spec _ _ (Ok _ _ _) |- _ => exact (ns_frame_holds _ _ _ _ _ Hs)
      end ].
Qed.

Lemma star_ns_kept : forall segs c tr c',
  star segs c tr c' -> ns_kept (m_fds (cfg_model c)) (m_fds (cfg_model c')).
Proof.
  intros segs c tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr c3 Hstep Hstar IH].
  - apply ns_kept_refl.
  - destruct c1 as [ms model].
    exact (ns_kept_trans _ _ _ (sstep_ns_kept _ _ _ _ _ Hstep) IH).
Qed.

(** A launch holds the three standard channels and the descriptors it
    inherits ([State.inherited_table]), none of them a namespace file. *)
Lemma init_config_ns_free : forall segs pc ph sp brk0 mbase rnd lim inp,
  ns_free (m_fds (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))).
Proof.
  intros segs pc ph sp brk0 mbase rnd lim inp h [fd Hin].
  change (In (fd, FdOpaque (ONsFile h))
            ([(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
              (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
              (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))]
             ++ inherited_table (in_inherited_fds inp))) in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - repeat (destruct Hin as [Hin|Hin]; [discriminate Hin|]).
    exact Hin.
  - unfold inherited_table in Hin. apply in_map_iff in Hin.
    destruct Hin as (kv & Heq & _). discriminate Heq.
Qed.

(** EVERY MODEL A RUN REACHES HOLDS NO [ONsFile]. *)
Theorem run_ns_free : forall segs pc ph sp brk0 mbase rnd lim inp tr c,
  star segs (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c ->
  ns_free (m_fds (cfg_model c)).
Proof.
  intros segs pc ph sp brk0 mbase rnd lim inp tr c Hstar.
  exact (ns_free_kept _ _ (init_config_ns_free segs pc ph sp brk0 mbase rnd lim inp)
           (star_ns_kept _ _ _ _ Hstar)).
Qed.

(** The same under any [Run.SpuriousCfg]. *)
Corollary run_scfg_ns_free : forall segs cfg pc ph sp brk0 mbase rnd lim inp tr c,
  star_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c ->
  ns_free (m_fds (cfg_model c)).
Proof.
  intros segs cfg pc ph sp brk0 mbase rnd lim inp tr c H.
  exact (run_ns_free _ _ _ _ _ _ _ _ _ _ _ (star_cfg_sub _ _ _ _ _ H)).
Qed.

(** WHAT [State.stream_end] AND [State.pipe_end_live] NEED, at every
    model a run reaches: no [FdOpaque] entry they skip is an [ONsFile],
    so none is a second reference to an end the table tracks. *)
Corollary run_opaque_entries_not_ns :
  forall segs pc ph sp brk0 mbase rnd lim inp tr c fd o,
  star segs (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c ->
  In (fd, FdOpaque o) (m_fds (cfg_model c)) ->
  forall h, o <> ONsFile h.
Proof.
  intros segs pc ph sp brk0 mbase rnd lim inp tr c fd o Hstar Hin h ->.
  exact (run_ns_free _ _ _ _ _ _ _ _ _ _ _ Hstar h (ex_intro _ fd Hin)).
Qed.
