(** * LinuxProcessSem.Checks.CloexecKeys — every known close-on-exec bit names an open descriptor

    Not part of the trusted specification: QA on [State.m_cloexec] across
    the released dispatcher, in the sense of [Checks.Examples]'s header.

    [cloexec_keys_open m] says every key of the close-on-exec map is an
    open descriptor of the table.  It is what makes a map of KNOWN bits
    sound: a creating arm that installs a descriptor at a FREE number and
    records no bit leaves that descriptor without a key, so
    [Fs.Fcntl.fcntl_spec]'s [F_GETFD] admits both answers there instead of
    a stale bit of an earlier descriptor.

    - [cloexec_keys_open_init_model]: true at launch.
    - [checked_table_ck]: preserved by every [CheckOk] of every arm of
      [Checks.Sys.Dispatch.checked_table], one lemma per arm, failing BY
      NAME for an arm added without one.  Most arms keep the map and only
      grow the table's domain ([fd_rel]); the six that write the map
      ([fcntl], [dup], [dup3], [close], [close_range], [openat]) have
      their own lemma.
    - [syscall_spec_cloexec_keys]: the same for every [Ok] answer of the
      released spec.
    - The namespace layer's three table writers ([Ns.Files.install],
      [Ns.Files.close_fn], [Ns.Net.socket_arm]) are not in
      [checked_table]; [ns_install_keys], [ns_close_keys] and
      [ns_socket_keys] cover them.  Every other namespace arm either
      leaves the released model's table alone or answers through the
      released arm, which [checked_table_ck] covers. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Signal Fork.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint ProcsPrivateFrame.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel Require Import Signal Fork.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Ext Arm Files Net.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

Definition cloexec_keys_open (m : Model) : Prop :=
  forall n b, In (n, b) (m_cloexec m) -> fd_lookup (m_fds m) n <> None.

(* =========================================================================
   The table and the map, as lists
   ========================================================================= *)

(** A filter that keeps every entry at [n] leaves [n]'s lookup alone. *)
Lemma fd_lookup_filter_keep : forall (g : word * FdEntry -> bool) fds n,
  (forall e, g (n, e) = true) ->
  fd_lookup (List.filter g fds) n = fd_lookup fds n.
Proof.
  intros g fds n Hg.
  induction fds as [|[k e] r IH]; [reflexivity|].
  cbn [List.filter].
  destruct (g (k, e)) eqn:Eg; cbn [fd_lookup].
  - destruct (bv_eqb k n); [reflexivity|exact IH].
  - rewrite IH. destruct (bv_eqb k n) eqn:E; [|reflexivity].
    apply bv_eqb_eq in E. subst k. rewrite Hg in Eg. discriminate Eg.
Qed.

Lemma fd_lookup_insert_same : forall fds k e, fd_lookup (fd_insert fds k e) k = Some e.
Proof. intros. unfold fd_insert. cbn [fd_lookup]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma fd_lookup_insert_keep : forall fds k e n,
  fd_lookup fds n <> None -> fd_lookup (fd_insert fds k e) n <> None.
Proof.
  intros fds k e n Hn. unfold fd_insert. cbn [fd_lookup].
  destruct (bv_eqb k n) eqn:E; [discriminate|].
  rewrite fd_lookup_filter_keep; [exact Hn|].
  intros e'. cbn [fst]. destruct (bv_eqb n k) eqn:E'; [|reflexivity].
  apply bv_eqb_eq in E'. subst n. rewrite bv_eqb_refl in E. discriminate E.
Qed.

(** The table only GROWS its domain. *)
Definition fds_grow (fds fds' : list (word * FdEntry)) : Prop :=
  forall n, fd_lookup fds n <> None -> fd_lookup fds' n <> None.

Lemma fds_grow_of_eq : forall a b, a = b -> fds_grow a b.
Proof. intros a b -> n H. exact H. Qed.

Lemma fds_grow_insert : forall a b k e, fds_grow a b -> fds_grow a (fd_insert b k e).
Proof. intros a b k e H n Hn. apply fd_lookup_insert_keep. exact (H n Hn). Qed.

Lemma fds_grow_forfeit : forall fds, fds_grow fds (forfeit_inherited fds).
Proof.
  intros fds n Hn. rewrite fd_lookup_forfeit_inherited.
  destruct (fd_lookup fds n); [discriminate|contradiction].
Qed.

(** A map that keeps every key keeps the domain: [State.anon_update],
    [State.anon_set_data], the /tmp unlink's conversion
    ([Checks.Sys.Fs.Namei.unlink_open_model]), [ppoll_record] and
    [Kernel.Fork.forfeit_inherited] are all of this shape. *)
Lemma fd_lookup_map_key : forall (g : word * FdEntry -> word * FdEntry),
  (forall p, fst (g p) = fst p) ->
  forall b n, fd_lookup b n <> None -> fd_lookup (map g b) n <> None.
Proof.
  intros g Hg b. induction b as [|[k e] r IH]; intros n H; [exfalso; apply H; reflexivity|].
  cbn [map]. pose proof (Hg (k, e)) as Hk. destruct (g (k, e)) as [k' e'].
  cbn [fst] in Hk. subst k'. cbn [fd_lookup] in H |- *.
  destruct (bv_eqb k n); [discriminate|exact (IH n H)].
Qed.

Lemma fds_grow_map_key : forall a b (g : word * FdEntry -> word * FdEntry),
  (forall p, fst (g p) = fst p) -> fds_grow a b -> fds_grow a (map g b).
Proof. intros a b g Hg H n Hn. exact (fd_lookup_map_key g Hg b n (H n Hn)). Qed.

(** A successful clone's eventfd conversion rewrites entries in place
    ([Kernel.Fork.share_eventfds]). *)
Lemma fd_lookup_share_eventfds_keep : forall b n,
  fd_lookup b n <> None -> fd_lookup (share_eventfds b) n <> None.
Proof.
  induction b as [|[k e] r IH]; intros n H; cbn [share_eventfds fd_lookup] in *;
    [exact H|].
  destruct (bv_eqb k n); [discriminate|exact (IH n H)].
Qed.

Lemma fds_grow_share_eventfds : forall a b, fds_grow a b -> fds_grow a (share_eventfds b).
Proof. intros a b H n Hn. exact (fd_lookup_share_eventfds_keep b n (H n Hn)). Qed.

(** A write through an unnamed file's descriptor: the contents to every
    descriptor of the file and the offset to this one
    ([State.anon_write_back]), whatever [anon_place_fds] decides. *)
Lemma fds_grow_anon_place_fds : forall a fds fd id af bs fds',
  anon_place_fds fds fd id af bs = Some fds' -> fds_grow a fds -> fds_grow a fds'.
Proof.
  intros a fds fd id af bs fds' E H. unfold anon_place_fds in E. cbv zeta in E.
  repeat (match type of E with context [if ?b then _ else _] => destruct b end;
          cbv beta iota in E);
  first [ discriminate E | injection E as <- ];
  unfold anon_write_back, anon_set_data, anon_update;
  (apply fds_grow_insert; apply fds_grow_map_key;
   [ intros [? ?]; reflexivity | exact H ]).
Qed.

(** What an arm that does not write the map owes: the map is the old
    one and the table's domain only grows. *)
Definition fd_rel (m m' : Model) : Prop :=
  m_cloexec m' = m_cloexec m /\ fds_grow (m_fds m) (m_fds m').

Lemma fd_rel_of_fd : forall m m', m_fd m' = m_fd m -> fd_rel m m'.
Proof.
  intros m m' E. unfold fd_rel, m_cloexec, m_fds. rewrite E.
  split; [reflexivity | apply fds_grow_of_eq; reflexivity].
Qed.

Lemma ck_of_fd_rel : forall m m', fd_rel m m' -> cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros m m' [Hc Hg] Hk n b Hin. rewrite Hc in Hin. exact (Hg n (Hk n b Hin)).
Qed.

(* =========================================================================
   The writers of the map
   ========================================================================= *)

(** [F_SETFD], and [openat]'s bit: a key written at an open descriptor. *)
Lemma ck_set_open : forall m k b,
  cloexec_keys_open m -> fd_lookup (m_fds m) k <> None ->
  cloexec_keys_open (with_cloexec (cloexec_set (m_cloexec m) k b) m).
Proof.
  intros m k b Hk Hkk n b' Hin.
  rewrite m_cloexec_with_cloexec in Hin. rewrite m_fds_with_cloexec.
  unfold cloexec_set in Hin. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. exact Hkk.
  - unfold cloexec_forget in Hin. apply filter_In in Hin as [Hin _].
    exact (Hk _ _ Hin).
Qed.

(** [dup] and [dup3]: a descriptor installed and its key written. *)
Lemma ck_insert_set : forall m k b e,
  cloexec_keys_open m ->
  cloexec_keys_open (with_cloexec (cloexec_set (m_cloexec m) k b)
                       (with_fds (fd_insert (m_fds m) k e) m)).
Proof.
  intros m k b e Hk n b' Hin.
  rewrite m_cloexec_with_cloexec in Hin. rewrite m_fds_with_cloexec, m_fds_with_fds.
  unfold cloexec_set in Hin. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. rewrite fd_lookup_insert_same. discriminate.
  - unfold cloexec_forget in Hin. apply filter_In in Hin as [Hin _].
    apply fd_lookup_insert_keep. exact (Hk _ _ Hin).
Qed.

(** [dup3]'s MOVE: two descriptors installed, the alias at [k2] and the
    file at [k], and [k]'s key written. *)
Lemma ck_dup3_move : forall m k k2 b e e2,
  cloexec_keys_open m ->
  cloexec_keys_open (with_cloexec (cloexec_set (m_cloexec m) k b)
                       (with_fds (fd_insert (fd_insert (m_fds m) k e) k2 e2) m)).
Proof.
  intros m k k2 b e e2 Hk n b' Hin.
  rewrite m_cloexec_with_cloexec in Hin. rewrite m_fds_with_cloexec, m_fds_with_fds.
  unfold cloexec_set in Hin. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. apply fd_lookup_insert_keep.
    rewrite fd_lookup_insert_same. discriminate.
  - unfold cloexec_forget in Hin. apply filter_In in Hin as [Hin _].
    apply fd_lookup_insert_keep. apply fd_lookup_insert_keep. exact (Hk _ _ Hin).
Qed.

(** Every table [File.dup3_fds] answers: a copy or a move. *)
Lemma ck_dup3_fds : forall oldfd newfd e m fds' b,
  dup3_fds oldfd newfd e (m_fds m) = Some fds' ->
  cloexec_keys_open m ->
  cloexec_keys_open (with_cloexec (cloexec_set (m_cloexec m) newfd b)
                       (with_fds fds' m)).
Proof.
  intros oldfd newfd e m fds' b H Hk. unfold dup3_fds in H.
  destruct (dup_modeled_entry e).
  - injection H as <-. apply ck_insert_set. exact Hk.
  - destruct (dup3_moves_entry e); [|discriminate H].
    injection H as <-. apply ck_dup3_move. exact Hk.
Qed.

(** The namespace layer's install: a descriptor installed and its key in
    the released map forgotten. *)
Lemma ck_insert_forget : forall m k e,
  cloexec_keys_open m ->
  cloexec_keys_open (with_cloexec (cloexec_forget (m_cloexec m) k)
                       (with_fds (fd_insert (m_fds m) k e) m)).
Proof.
  intros m k e Hk n b Hin.
  rewrite m_cloexec_with_cloexec in Hin. rewrite m_fds_with_cloexec, m_fds_with_fds.
  unfold cloexec_forget in Hin. apply filter_In in Hin as [Hin _].
  apply fd_lookup_insert_keep. exact (Hk _ _ Hin).
Qed.

(** [close]: the descriptor and its key go together. *)
Lemma ck_close : forall m k,
  cloexec_keys_open m ->
  cloexec_keys_open (with_cloexec (cloexec_forget (m_cloexec m) k)
                       (with_fds (fd_remove (m_fds m) k) m)).
Proof.
  intros m k Hk n b Hin.
  rewrite m_cloexec_with_cloexec in Hin. rewrite m_fds_with_cloexec, m_fds_with_fds.
  unfold cloexec_forget in Hin. apply filter_In in Hin as [Hin Hg].
  unfold fd_remove. rewrite fd_lookup_filter_keep; [exact (Hk _ _ Hin)|].
  intros e. exact Hg.
Qed.

(** [close_range]: the descriptors of the range and their keys go
    together, and every other key stays with its descriptor. *)
Lemma ck_close_range : forall m lo hi,
  cloexec_keys_open m ->
  cloexec_keys_open (with_cloexec (close_range_cloexec lo hi (m_cloexec m))
                       (with_fds (close_range_fds lo hi (m_fds m)) m)).
Proof.
  intros m lo hi Hk n b Hin.
  rewrite m_cloexec_with_cloexec in Hin. rewrite m_fds_with_cloexec, m_fds_with_fds.
  unfold close_range_cloexec in Hin. apply filter_In in Hin as [Hin Hg].
  unfold close_range_fds. rewrite fd_lookup_filter_keep; [exact (Hk _ _ Hin)|].
  intros e. exact Hg.
Qed.

(* =========================================================================
   The launch
   ========================================================================= *)

Lemma fd_lookup_member_open : forall fds n e,
  In (n, e) fds -> fd_lookup fds n <> None.
Proof.
  intros fds. induction fds as [|[k e] r IH]; intros n ent Hin.
  - contradiction.
  - cbn [fd_lookup]. destruct Hin as [H|Hin].
    + inversion H; subst. rewrite bv_eqb_refl. discriminate.
    + destruct (bv_eqb k n); [discriminate|exact (IH n ent Hin)].
Qed.

Lemma cloexec_keys_open_init_model : forall reserved brk0 mbase sp lim inp,
  cloexec_keys_open (init_model reserved brk0 mbase sp lim inp).
Proof.
  intros reserved brk0 mbase sp lim inp n b Hin.
  rewrite m_fds_init_model.
  rewrite m_cloexec_init_model in Hin. unfold launch_cloexec in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct Hin as [H|[H|[H|[]]]]; inversion H; subst;
      intro Hc; vm_compute in Hc; discriminate Hc.
  - apply in_map_iff in Hin as ([k bytes] & Heq & Hmem).
    cbn [fst] in Heq. injection Heq as Hn Hb. subst n b.
    apply (fd_lookup_member_open _ k
      (FdOpaque (OInherited (Some (bytes, Z_to_bv 64 0))))).
    apply in_or_app. right. unfold inherited_table.
    apply in_map_iff. exists (k, bytes). split; [reflexivity|exact Hmem].
Qed.

(* =========================================================================
   The arms that keep the map: the walk
   ========================================================================= *)

(** The memory-management wrappers of [Sys.Mm] that branch or recurse,
    and the signal delivery: each keeps [State.m_fd] whole. *)
Lemma m_fd_forget_vm_ranges : forall rs m, m_fd (forget_vm_ranges rs m) = m_fd m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma m_fd_with_brk_next : forall m req r, m_fd (with_brk_next m req r) = m_fd m.
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  rewrite m_fd_forget_vm_ranges. reflexivity.
Qed.

Lemma m_fd_with_mmap_backing : forall flags a n m,
  m_fd (with_mmap_backing flags a n m) = m_fd m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma m_fd_with_mmap_replacement : forall flags a n m,
  m_fd (with_mmap_replacement flags a n m) = m_fd m.
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  rewrite m_fd_with_mmap_backing. reflexivity.
Qed.

Lemma m_fd_sigmask_deliver_model : forall new m,
  m_fd (sigmask_deliver_model new m) = m_fd m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

(** A leaf keeps the fd state whole, inserts a descriptor, rewrites
    entries in place (a key-keeping map: the unnamed file's contents, the
    /tmp unlink's conversion, ppoll's readiness record, the inherited
    offsets a clone forfeits; or the clone's eventfd conversion), or
    installs the table an unnamed-file write placed. *)
Ltac fr_grow :=
  repeat (first
    [ apply fds_grow_insert
    | apply fds_grow_share_eventfds
    | (apply fds_grow_map_key; [intros [? ?]; reflexivity|])
    | match goal with
      | E : anon_place_fds _ _ _ _ _ = Some _ |- _ =>
          apply (fds_grow_anon_place_fds _ _ _ _ _ _ _ E)
      end ]);
  first [apply fds_grow_of_eq; reflexivity | apply fds_grow_forfeit].

Ltac fr_leaf :=
  cbv beta;
  first
  [ apply fd_rel_of_fd; reflexivity
  | apply fd_rel_of_fd;
    rewrite ?m_fd_with_mmap_backing, ?m_fd_with_mmap_replacement,
      ?m_fd_with_brk_next, ?m_fd_forget_vm_ranges, ?m_fd_sigmask_deliver_model;
    reflexivity
  | split; [reflexivity | fr_grow] ].

Lemma check_efault_or_fr : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros fb eff m m' evs H. unfold check_efault_or in H. repeat vm_step H; fr_leaf.
Qed.

Lemma check_sigpipe_write_fr : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros eff m m' evs H. unfold check_sigpipe_write in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); fr_leaf.
Qed.

Lemma check_sigpipe_writev_fr : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros reads eff m m' evs H. unfold check_sigpipe_writev in H.
  destruct (sigpipe_declines m); cbv iota in H; [discriminate H|].
  apply check_ret_only_copyins_model in H; subst.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m), (sigpipe_blocked (m_sigmask m)); fr_leaf.
Qed.

Lemma check_readv_gap_fr : forall m' evs, check_readv_gap = CheckOk m' evs -> False.
Proof. intros m' evs H. unfold check_readv_gap in H. discriminate. Qed.

Lemma check_open_result_fr : forall eff m mk m' evs,
  (forall fd, fd_rel m (mk fd)) ->
  check_open_result eff m mk = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_open_result, check_new_fd_result in H.
  repeat vm_step H; first [apply Hmk | fr_leaf].
Qed.

Lemma check_write_open_result_fr : forall eff m mk m' evs,
  (forall fd, fd_rel m (mk fd)) ->
  check_write_open_result eff m mk = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_write_open_result, check_new_fd_result in H.
  repeat vm_step H; first [apply Hmk | fr_leaf].
Qed.

Lemma check_write_open_create_result_fr : forall eff m mk m' evs,
  (forall fd, fd_rel m (mk fd)) ->
  check_write_open_create_result eff m mk = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_write_open_create_result, check_new_fd_result in H.
  repeat vm_step H; first [apply Hmk | fr_leaf].
Qed.

Ltac fr_done H :=
  first
  [ apply check_efault_or_fr in H; exact H
  | apply check_sigpipe_write_fr in H; exact H
  | apply check_sigpipe_writev_fr in H; exact H
  | elim (check_readv_gap_fr _ _ H)
  | (eapply check_open_result_fr in H; [exact H | intros; fr_leaf])
  | (eapply check_write_open_result_fr in H; [exact H | intros; fr_leaf])
  | (eapply check_write_open_create_result_fr in H; [exact H | intros; fr_leaf]) ].

Ltac fr_frame2 H :=
  repeat (vm_step H || fr_done H); fr_leaf.

(** C1'S SUB-CHECKERS, ONE LEMMA EACH, as [Checks.KillFree] has them: a
    stream-pair end's read and send, the /proc/sys file, the eventfd, the
    unnamed file's two write helpers and the "/proc/self/fd/N" reopen.
    Each rewrites entries in place or installs one descriptor, and none
    writes the close-on-exec map. *)
Lemma fr_stream_read_empty : forall fd id side st nonblock eff m m' evs,
  check_stream_read_empty fd id side st nonblock eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros fd id side st nonblock eff m m' evs H.
  unfold check_stream_read_empty, check_stream_read_reset in H. cbv beta iota zeta in H.
  fr_frame2 H.
Qed.

Lemma fr_stream_read :
  forall fd id side st nonblock buf count i eff m m' evs,
  check_stream_read fd id side st nonblock buf count i eff m = CheckOk m' evs ->
  fd_rel m m'.
Proof.
  intros fd id side st nonblock buf count i eff m m' evs H.
  unfold check_stream_read, check_stream_read_empty, check_stream_read_reset in H.
  cbv beta iota zeta in H. fr_frame2 H.
Qed.

Lemma fr_stream_send :
  forall id side st nonblock nosignal n src ledger eff m m' evs,
  check_stream_send id side st nonblock nosignal n src ledger eff m = CheckOk m' evs ->
  fd_rel m m'.
Proof.
  intros id side st nonblock nosignal n src ledger eff m m' evs H.
  unfold check_stream_send in H. cbv beta iota zeta in H. fr_frame2 H.
Qed.

Lemma fr_stream_write :
  forall id side st nonblock nosignal buf count i eff m m' evs,
  check_stream_write id side st nonblock nosignal buf count i eff m = CheckOk m' evs ->
  fd_rel m m'.
Proof.
  intros id side st nonblock nosignal buf count i eff m m' evs H.
  unfold check_stream_write in H. exact (fr_stream_send _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Ltac fr_stream H :=
  first
  [ exact (fr_stream_read _ _ _ _ _ _ _ _ _ _ _ _ H)
  | exact (fr_stream_read_empty _ _ _ _ _ _ _ _ _ H)
  | exact (fr_stream_write _ _ _ _ _ _ _ _ _ _ _ _ H)
  | exact (fr_stream_send _ _ _ _ _ _ _ _ _ _ _ _ H) ].

Lemma fr_read_proc : forall i buf count eff m m' evs,
  check_read_proc i buf count eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i buf count eff m m' evs H.
  unfold check_read_proc, check_read_proc_bare in H. cbv beta iota zeta in H.
  fr_frame2 H.
Qed.

Lemma fr_eventfd_read : forall fd ctx buf count i eff m m' evs,
  check_eventfd_read fd ctx buf count i eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros fd ctx buf count i eff m m' evs H. unfold check_eventfd_read in H.
  cbv beta iota zeta in H. fr_frame2 H.
Qed.

Lemma fr_eventfd_write : forall fd ctx buf count i eff m m' evs,
  check_eventfd_write fd ctx buf count i eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros fd ctx buf count i eff m m' evs H. unfold check_eventfd_write in H.
  cbv beta iota zeta in H. fr_frame2 H.
Qed.

Lemma fr_anon_fault_extend : forall reads m id data dst eff m' evs,
  check_anon_fault_extend reads m id data dst eff = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros reads m id data dst eff m' evs H. unfold check_anon_fault_extend in H.
  cbv beta iota zeta in H. fr_frame2 H.
Qed.

Lemma fr_anon_write_fault : forall reads m id af eff m' evs,
  check_anon_write_fault reads m id af eff = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros reads m id af eff m' evs H. unfold check_anon_write_fault in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H || (eapply fr_anon_fault_extend in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_procfd : forall n flags eff m m' evs,
  Open.check_openat_procfd n flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros n flags eff m m' evs H. unfold Open.check_openat_procfd in H.
  cbv beta iota zeta in H. fr_frame2 H.
Qed.

(** OPENAT AND READ'S AND WRITE'S HELPERS, ONE LEMMA PER SUB-CHECKER, as
    [VmMapsDisjoint] and [KillFree] prove them: each proves its own step
    and closes the sub-checkers it calls with their lemmas, so no proof
    unfolds the whole openat tree. *)
Lemma fr_open_wronly : forall p eff m m' evs,
  check_create_wronly p eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p eff m m' evs H. unfold check_create_wronly in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_open_append : forall p eff m m' evs,
  check_open_append p eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p eff m m' evs H. unfold check_open_append in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_open_rdwr : forall p fs' eff m m' evs,
  check_open_rdwr p fs' eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p fs' eff m m' evs H. unfold check_open_rdwr in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_openat_read : forall p eff m m' evs,
  Open.check_openat_read p eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p eff m m' evs H. unfold Open.check_openat_read in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_openat_create : forall p eff m m' evs,
  Open.check_openat_create p eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p eff m m' evs H. unfold Open.check_openat_create in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_open_wronly in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_excl : forall p eff m m' evs,
  Open.check_openat_excl p eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p eff m m' evs H. unfold Open.check_openat_excl in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_open_wronly in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_append : forall excl p eff m m' evs,
  Open.check_openat_append excl p eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros excl p eff m m' evs H. unfold Open.check_openat_append in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_open_append in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_rdwr : forall creat trunc p eff m m' evs,
  Open.check_openat_rdwr creat trunc p eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros creat trunc p eff m m' evs H. unfold Open.check_openat_rdwr in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_open_rdwr in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_rdwr_excl : forall p eff m m' evs,
  Open.check_openat_rdwr_excl p eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p eff m m' evs H. unfold Open.check_openat_rdwr_excl in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_open_rdwr in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_dir : forall p eff m m' evs,
  Open.check_openat_dir p eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p eff m m' evs H. unfold Open.check_openat_dir in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_openat_localtime : forall flags eff m m' evs,
  Open.check_openat_localtime flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros flags eff m m' evs H. unfold Open.check_openat_localtime in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_open_devnull : forall rd wr eff m m' evs,
  Open.check_open_devnull rd wr eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros rd wr eff m m' evs H. unfold Open.check_open_devnull in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_openat_devnull : forall flags eff m m' evs,
  Open.check_openat_devnull flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros flags eff m m' evs H. unfold Open.check_openat_devnull in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_open_devnull in H; exact H));
  fr_leaf.
Qed.

Lemma fr_open_urandom : forall eff m m' evs,
  Open.check_open_urandom eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros eff m m' evs H. unfold Open.check_open_urandom in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_openat_urandom : forall flags eff m m' evs,
  Open.check_openat_urandom flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros flags eff m m' evs H. unfold Open.check_openat_urandom in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_open_urandom in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_tmp : forall n p flags eff m m' evs,
  Open.check_openat_tmp n p flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros n p flags eff m m' evs H. unfold Open.check_openat_tmp in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_openat_read in H; exact H)
          || (eapply fr_openat_create in H; exact H)
          || (eapply fr_openat_rdwr_excl in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_sep : forall p flags eff m m' evs,
  Open.check_openat_sep p flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p flags eff m m' evs H. unfold Open.check_openat_sep in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_openat_localtime in H; exact H)
          || (eapply fr_openat_devnull in H; exact H)
          || (eapply fr_openat_urandom in H; exact H)
          || (eapply fr_openat_tmp in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_resolved : forall p flags eff m m' evs,
  Open.check_openat_resolved p flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros p flags eff m m' evs H. unfold Open.check_openat_resolved in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_openat_sep in H; exact H)
          || (eapply fr_openat_read in H; exact H)
          || (eapply fr_openat_create in H; exact H)
          || (eapply fr_openat_excl in H; exact H)
          || (eapply fr_openat_dir in H; exact H)
          || (eapply fr_openat_append in H; exact H)
          || (eapply fr_openat_rdwr in H; exact H)
          || (eapply fr_openat_rdwr_excl in H; exact H));
  fr_leaf.
Qed.

Lemma fr_proc_open_result : forall o eff m m' evs,
  Open.check_proc_open_result o eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros o eff m m' evs H. unfold Open.check_proc_open_result in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_openat_proc : forall c flags eff m m' evs,
  Open.check_openat_proc c flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros c flags eff m m' evs H. unfold Open.check_openat_proc in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_proc_open_result in H; exact H)
          || (eapply fr_openat_procfd in H; exact H));
  fr_leaf.
Qed.

Lemma fr_openat_body : forall i dirfd pathp flags eff m m' evs,
  Open.check_openat_body i dirfd pathp flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H. unfold Open.check_openat_body in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_openat_proc in H; exact H)
          || (eapply fr_openat_resolved in H; exact H));
  fr_leaf.
Qed.

Lemma fr_read_urandom : forall i buf count eff m m' evs,
  check_read_urandom i buf count eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i buf count eff m m' evs H. unfold check_read_urandom, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_socket_pending_error : forall e fd peer ch buf count i eff m m' evs,
  check_socket_pending_error e fd peer ch buf count i eff m = CheckOk m' evs ->
  fd_rel m m'.
Proof.
  intros e fd peer ch buf count i eff m m' evs H.
  unfold check_socket_pending_error, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_write_fault_extend : forall reads m p off eff m' evs,
  check_write_fault_extend reads m p off eff = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros reads m p off eff m' evs H.
  unfold check_write_fault_extend, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_newfstatat_proc_errno : forall reads eff m m' evs,
  check_newfstatat_proc_errno reads eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros reads eff m m' evs H. unfold check_newfstatat_proc_errno in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H);
  fr_leaf.
Qed.

Lemma fr_newfstatat_proc : forall i reads statbuf eff m m' evs,
  check_newfstatat_proc i reads statbuf eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i reads statbuf eff m m' evs H. unfold check_newfstatat_proc in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_newfstatat_proc_errno in H; exact H));
  fr_leaf.
Qed.

(** [check_read_opaque] keeps the model whole.  A live inherited entry
    instead uses [check_read_file_data], which replaces its table entry
    without changing the close-on-exec map or losing a descriptor key. *)
Lemma check_read_fr : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_read, check_read_file_data, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H || fr_stream H
          || (apply check_read_opaque_keeps in H; destruct H as [-> ->])
          || (eapply fr_read_urandom in H; exact H)
          || (eapply fr_socket_pending_error in H; exact H)
          || (eapply fr_read_proc in H; exact H)
          || (eapply fr_eventfd_read in H; exact H));
  fr_leaf.
Qed.

Lemma check_write_fr : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_write, check_access_ok_zero in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H || fr_stream H
          || (apply check_write_opaque_keeps in H; destruct H as [-> ->])
          || (eapply fr_write_fault_extend in H; exact H)
          || (eapply fr_eventfd_write in H; exact H)
          || (eapply fr_anon_write_fault in H; exact H));
  fr_leaf.
Qed.

Lemma check_pread64_fr : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pread64 in H. cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H || (eapply fr_read_urandom in H; exact H));
  fr_leaf.
Qed.

Lemma check_pwrite64_fr : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pwrite64 in H. cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H
          || (eapply fr_write_fault_extend in H; exact H)
          || (eapply fr_anon_fault_extend in H; exact H));
  fr_leaf.
Qed.

Lemma check_openat_table_fr : forall i dirfd pathp flags eff m m' evs,
  check_openat_table i dirfd pathp flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_openat_table in H. cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H || (eapply fr_openat_body in H; exact H));
  fr_leaf.
Qed.

Lemma check_lseek_fr : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros fd off whence eff m m' evs H. unfold check_lseek in H. fr_frame2 H. Qed.

Lemma check_getcwd_fr : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros size eff m m' evs H. unfold check_getcwd in H. fr_frame2 H. Qed.

Lemma check_getrandom_fr : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i buf cap flags eff m m' evs H.
  unfold check_getrandom, check_getrandom_zero in H. fr_frame2 H.
Qed.

Lemma check_readlinkat_fr : forall i dirfd eff m m' evs,
  check_readlinkat i dirfd eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i dirfd eff m m' evs H. unfold check_readlinkat in H. cbv zeta in H.
  fr_frame2 H.
Qed.

Lemma check_exit_fr : forall code eff m m' evs,
  check_exit code eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros code eff m m' evs H. unfold check_exit in H. fr_frame2 H. Qed.

Lemma check_set_tid_address_fr : forall eff m m' evs,
  check_set_tid_address eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros eff m m' evs H. unfold check_set_tid_address in H. fr_frame2 H. Qed.

Lemma check_ioctl_fr : forall i fd req eff m m' evs,
  check_ioctl i fd req eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd req eff m m' evs H.
  unfold check_ioctl, check_siocgifindex, check_ifreq_writeback in H. fr_frame2 H.
Qed.

Lemma check_writev_fr : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_writev in H. cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H || fr_stream H
          || (eapply fr_write_fault_extend in H; exact H)
          || (eapply fr_anon_write_fault in H; exact H));
  fr_leaf.
Qed.

(** pwritev2 (287) writes an unnamed file's contents into every
    descriptor of it ([State.anon_set_data]) and nothing else. *)
Lemma check_pwritev2_fr :
  forall i fd iov iovcnt pos_l pos_h flags eff m m' evs,
  check_pwritev2 i fd iov iovcnt pos_l pos_h flags eff m = CheckOk m' evs ->
  fd_rel m m'.
Proof.
  intros i fd iov iovcnt pos_l pos_h flags eff m m' evs H.
  unfold check_pwritev2 in H. cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H || fr_stream H
          || (eapply fr_anon_fault_extend in H; exact H));
  fr_leaf.
Qed.

Lemma check_readv_imported_fr : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd r iovs0 eff m m' evs H. unfold check_readv_imported in H.
  cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H || fr_stream H); fr_leaf.
Qed.

Lemma check_readv_fr : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_readv in H.
  repeat (vm_step H || fr_done H
          || (apply check_readv_imported_fr in H; exact H));
  fr_leaf.
Qed.

Lemma check_wait4_fr : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H.
  unfold check_wait4 in H.
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | _ => first
                 [ discriminate H
                 | match type of H with
                   | context [match ?x with _ => _ end] => destruct x eqn:?
                   | context [if ?b then _ else _] => destruct b eqn:?
                   end ]
          end).
  all: injection H as <- _.
  all: fr_leaf.
Qed.

Lemma check_epoll_create1_fr : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros flags32 eff m m' evs H. unfold check_epoll_create1 in H. fr_frame2 H. Qed.

Lemma check_epoll_ctl_fr : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i epfd op32 tfd event eff m m' evs H. unfold check_epoll_ctl in H. fr_frame2 H.
Qed.

Lemma check_epoll_pwait_fr :
  forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H.
  unfold check_epoll_pwait in H. fr_frame2 H.
Qed.

Lemma check_fsync_fr : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros fd eff m m' evs H. unfold check_fsync in H. fr_frame2 H. Qed.

Lemma check_getdents64_fr : forall i fd dirent count eff m m' evs,
  check_getdents64 i fd dirent count eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd dirent count eff m m' evs H.
  unfold check_getdents64, check_getdents64_opaque, check_procfd_getdents in H.
  cbv zeta in H. fr_frame2 H.
Qed.

Lemma check_flock_fr : forall fd cmd eff m m' evs,
  check_flock fd cmd eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros fd cmd eff m m' evs H. unfold check_flock in H. fr_frame2 H. Qed.

Lemma check_timerfd_create_fr : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros clkid flags eff m m' evs H. unfold check_timerfd_create in H. fr_frame2 H.
Qed.

Lemma check_eventfd2_fr : forall i flags eff m m' evs,
  check_eventfd2 i flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i flags eff m m' evs H. unfold check_eventfd2, check_new_fd_result in H.
  fr_frame2 H.
Qed.

Lemma check_signalfd4_fr : forall i ufd mask sizemask flags eff m m' evs,
  check_signalfd4 i ufd mask sizemask flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i ufd mask sizemask flags eff m m' evs H.
  unfold check_signalfd4, check_new_fd_result in H. fr_frame2 H.
Qed.

Lemma check_uname_fr : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i name eff m m' evs H. unfold check_uname, check_uname_copy in H. fr_frame2 H.
Qed.

Lemma check_prlimit64_fr :
  forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs ->
  fd_rel m m'.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H.
  unfold check_prlimit64, check_rlim64_read in H. fr_frame2 H.
Qed.

Lemma check_capget_fr : forall i header dataptr eff m m' evs,
  check_capget i header dataptr eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i header dataptr eff m m' evs H.
  unfold check_capget, check_capget_copy in H. fr_frame2 H.
Qed.

Lemma check_capset_fr : forall i header data eff m m' evs,
  check_capset i header data eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros i header data eff m m' evs H. unfold check_capset in H. fr_frame2 H. Qed.

Lemma check_ftruncate_fr : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros fd len eff m m' evs H. unfold check_ftruncate in H. fr_frame2 H. Qed.

Lemma check_getpid_fr : forall eff m m' evs,
  check_getpid eff m = CheckOk m' evs -> fd_rel m m'.
Proof. exact check_set_tid_address_fr. Qed.

Lemma check_gettid_fr : forall eff m m' evs,
  check_gettid eff m = CheckOk m' evs -> fd_rel m m'.
Proof. exact check_set_tid_address_fr. Qed.

Lemma check_getppid_fr : forall eff m m' evs,
  check_getppid eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros eff m m' evs H. unfold check_getppid in H. fr_frame2 H. Qed.

Lemma check_setsid_fr : forall eff m m' evs,
  check_setsid eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros eff m m' evs H. unfold check_setsid in H. fr_frame2 H. Qed.

Lemma check_getsid_fr : forall pid eff m m' evs,
  check_getsid pid eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros pid eff m m' evs H. unfold check_getsid, check_pid_choice in H. fr_frame2 H.
Qed.

Lemma check_prctl_fr : forall i option_ arg2 eff m m' evs,
  check_prctl i option_ arg2 eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i option_ arg2 eff m m' evs H.
  unfold check_prctl, check_ret_writes in H. fr_frame2 H.
Qed.

Lemma check_gettimeofday_fr : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros i tv tz eff m m' evs H. unfold check_gettimeofday in H. fr_frame2 H. Qed.

Lemma check_clock_gettime_fr : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i clkid tp eff m m' evs H. unfold check_clock_gettime in H. fr_frame2 H.
Qed.

Lemma check_clock_getres_fr : forall i clkid tp eff m m' evs,
  check_clock_getres i clkid tp eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_getres, check_clock_getres_result in H. fr_frame2 H.
Qed.

Lemma check_nanosleep_fr : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros i rqtp rmtp eff m m' evs H. unfold check_nanosleep in H. fr_frame2 H. Qed.

Lemma check_unlinkat_fr : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat, Namei.check_unlinkat_body, Namei.check_unlinkat_tmp,
    Namei.check_unlink_found, check_unlink_result,
    Namei.check_unlink_open_tmp, check_unlink_open_result, check_unlink_type_result in H.
  fr_frame2 H.
Qed.

Lemma check_faccessat_fr : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  fr_frame2 H.
Qed.

Lemma check_faccessat2_fr : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  fr_frame2 H.
Qed.

Lemma check_pselect6_fr : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H. unfold check_pselect6 in H.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [pa|];
    cbv beta iota in H; [|discriminate H].
  apply check_pselect_answer_model in H. subst m'. fr_leaf.
Qed.

Lemma check_ppoll_fr : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H. unfold check_ppoll in H.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [pa|];
    cbv beta iota in H; [|discriminate H].
  apply check_pselect_answer_model in H. subst m'. fr_leaf.
Qed.

Lemma check_newfstatat_fr : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i dirfd pathp flag eff m m' evs H.
  unfold check_newfstatat in H. cbv beta iota zeta in H.
  repeat (vm_step H || fr_done H || (eapply fr_newfstatat_proc in H; exact H));
  fr_leaf.
Qed.

Lemma check_fstat_file_fr : forall i p statbuf eff m m' evs,
  check_fstat_file i p statbuf eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i p statbuf eff m m' evs H.
  unfold check_fstat_file in H.
  destruct (fs_lookup (m_fs m) p) as [data|]; [|discriminate].
  destruct (negb (access_okb statbuf STAT_SIZE)); [fr_frame2 H|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|];
    [|discriminate].
  assert (Hdel : exists pin,
             check_fstat_deliver statbuf (length data) p pin eff m
             = CheckOk m' evs).
  { destruct (statpin_lookup (m_statpins m) p) as [b0|]; [|eauto].
    destruct (negb (stat_buf_wf b0)); [discriminate|eauto]. }
  destruct Hdel as (pin & Hd).
  apply check_fstat_deliver_ok in Hd
    as (bs & _ & _ & _ & _ & [(b1 & _ & _ & ->)|(_ & ->)]); fr_leaf.
Qed.

Lemma check_fstat_chrdev_fr : forall ok p i statbuf eff m m' evs,
  check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros ok p i statbuf eff m m' evs H.
  unfold check_fstat_chrdev in H.
  destruct (negb (access_okb statbuf STAT_SIZE)); [fr_frame2 H|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|];
    [|discriminate].
  assert (Hdel : exists pin,
             check_fstat_deliver_by ok statbuf p pin eff m
             = CheckOk m' evs).
  { destruct (statpin_lookup (m_statpins m) p) as [b0|]; [|eauto].
    destruct (negb (stat_buf_wf b0 && ok b0)%bool); [discriminate|eauto]. }
  destruct Hdel as (pin & Hd).
  apply check_fstat_deliver_by_ok in Hd
    as (bs & _ & _ & _ & _ & [(b1 & _ & _ & ->)|(_ & ->)]); fr_leaf.
Qed.

Lemma check_fstat_devnull_fr : forall i statbuf eff m m' evs,
  check_fstat_devnull i statbuf eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros. eapply check_fstat_chrdev_fr. exact H. Qed.

Lemma check_fstat_urandom_fr : forall i statbuf eff m m' evs,
  check_fstat_urandom i statbuf eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros. eapply check_fstat_chrdev_fr. exact H. Qed.

Lemma check_fstat_opaque_fr : forall i o statbuf eff m m' evs,
  check_fstat_opaque i o statbuf eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i o statbuf eff m m' evs H.
  unfold check_fstat_opaque, check_fstat_procfd_dir in H. fr_frame2 H.
Qed.

(** An unnamed file's fstat writes its pin into every descriptor of it
    ([State.anon_update]) and the statbuf. *)
Lemma check_fstat_anon_fr : forall i id af statbuf eff m m' evs,
  check_fstat_anon i id af statbuf eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i id af statbuf eff m m' evs H.
  unfold check_fstat_anon, check_fstat_anon_deliver in H. cbv beta iota zeta in H.
  fr_frame2 H.
Qed.

Lemma check_fstat_fr : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd statbuf eff m m' evs H. unfold check_fstat in H.
  destruct (fd_lookup (m_fds m) fd) as [e|]; [|fr_frame2 H].
  destruct e; try discriminate;
    try (match type of H with
         | context [negb (anon_agree ?f ?a ?b)] =>
             destruct (negb (anon_agree f a b)); cbv iota in H; [discriminate H|]
         end);
    first [eapply check_fstat_file_fr; exact H
          |eapply check_fstat_devnull_fr; exact H
          |eapply check_fstat_urandom_fr; exact H
          |eapply check_fstat_anon_fr; exact H
          |eapply check_fstat_opaque_fr; exact H].
Qed.

Lemma check_getid_fr : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros sel eff m m' evs H. unfold check_getid in H. fr_frame2 H. Qed.

Lemma check_getresid_fr : forall i get rp ep sp eff m m' evs,
  check_getresid i get rp ep sp eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i get rp ep sp eff m m' evs H.
  unfold check_getresid, check_ret_writes in H. fr_frame2 H.
Qed.

Lemma check_setid_fr : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros get put user v eff m m' evs H.
  unfold check_setid, check_setid_result in H. fr_frame2 H.
Qed.

Lemma check_setresid_fr : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros get put user r e sv eff m m' evs H.
  unfold check_setresid, check_setid_result in H. fr_frame2 H.
Qed.

Lemma check_getgroups_fr : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros gidsetsize eff m m' evs H. unfold check_getgroups in H. fr_frame2 H.
Qed.

Lemma check_setgroups_fr : forall i eff m m' evs,
  check_setgroups i eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros i eff m m' evs H. unfold check_setgroups in H. fr_frame2 H. Qed.

Lemma check_socket_fr : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros domain type protocol eff m m' evs H.
  unfold check_socket, check_new_fd_result, check_errno_or_list in H. fr_frame2 H.
Qed.

Lemma check_bind_fr : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_bind, check_errno_or_success in H. fr_frame2 H.
Qed.

Lemma check_listen_fr : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros fd backlog eff m m' evs H.
  unfold check_listen, check_errno_or_success, check_errno_only in H. fr_frame2 H.
Qed.

Lemma check_connect_fr : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros i fd addrp addrlen eff m m' evs H. unfold check_connect in H. fr_frame2 H. Qed.

Lemma check_accept4_fr : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H.
  unfold check_accept4, check_new_fd_result, check_errno_or_success,
    check_errno_only, check_errno_or_list in H. fr_frame2 H.
Qed.

Lemma check_sched_setscheduler_fr : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i pid policy param eff m m' evs H. unfold check_sched_setscheduler in H.
  fr_frame2 H.
Qed.

Lemma check_sched_getaffinity_fr : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros len eff m m' evs H. unfold check_sched_getaffinity in H. fr_frame2 H. Qed.

Lemma check_sched_yield_fr : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros eff m m' evs H. unfold check_sched_yield in H. fr_frame2 H. Qed.

Lemma check_sigaltstack_fr : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros i uss uoss eff m m' evs H. unfold check_sigaltstack in H. fr_frame2 H. Qed.

(** The SIGPIPE arm answers at the model it was handed or installs one
    SIGPIPE action ([State.with_sigpipe_install]), which rebuilds
    [ProcState] alone: [Checks.Sys.Kernel.Signal.check_rt_sigaction_sigpipe_model]. *)
Lemma check_rt_sigaction_fr : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i sig act oact ss eff m m' evs H. unfold check_rt_sigaction in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 8))); cbv beta iota in H; [fr_frame2 H|].
  destruct (Z.eqb (bv_unsigned sig) SIGPIPE); cbv beta iota in H.
  { apply check_rt_sigaction_sigpipe_model in H as [-> | [a ->]]; fr_leaf. }
  fr_frame2 H.
Qed.

Lemma check_getsockname_fr : forall i fd eff m m' evs,
  check_getsockname i fd eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd eff m m' evs H.
  unfold check_getsockname, check_getsockname_core, check_stream_getname,
    check_ret_writes_copyins in H. cbv zeta in H.
  fr_frame2 H.
Qed.

Lemma check_getpeername_fr : forall i fd eff m m' evs,
  check_getpeername i fd eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd eff m m' evs H.
  unfold check_getpeername, check_getpeername_core, check_stream_getname,
    check_ret_writes_copyins in H. cbv zeta in H.
  fr_frame2 H.
Qed.

(** [setsockopt]: the SO_PASSCRED store on an AF_UNIX SEQPACKET end
    rewrites that end's entry in place; every other answer keeps the
    fd state. *)
Lemma check_setsockopt_fr : forall i fd level optlen eff m m' evs,
  check_setsockopt i fd level optlen eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd level optlen eff m m' evs H.
  unfold check_setsockopt, check_seqpacket_setsockopt, check_setsockopt_core,
    check_stream_setsockopt in H.
  cbv zeta in H.
  fr_frame2 H.
Qed.

Lemma check_getsockopt_fr : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd level optlenp eff m m' evs H.
  unfold check_getsockopt, check_getsockopt_core, check_stream_getsockopt,
    check_ret_writes_copyins in H.
  cbv zeta in H.
  fr_frame2 H.
Qed.

(** [shutdown] on a stream end rewrites that end and its peer, if the
    pair still has one, in place ([Socket.check_stream_shutdown]): the
    peer lookup is a [match] in the post-model, split here. *)
Lemma check_shutdown_fr : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros fd how eff m m' evs H.
  unfold check_shutdown, check_shutdown_core, check_stream_shutdown in H. cbv zeta in H.
  repeat (vm_step H || fr_done H);
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
  fr_leaf.
Qed.

Lemma check_send_on_socket_fr :
  forall pre acc fd sk total bs eff m m' evs,
  check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros pre acc fd sk total bs eff m m' evs H. unfold check_send_on_socket in H.
  fr_frame2 H.
Qed.

Lemma check_recv_fd_answer_fr : forall fds fd eff m m' evs,
  check_recv_fd_answer fds fd eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros fds fd eff m m' evs H. unfold check_recv_fd_answer in H. fr_frame2 H.
Qed.

(** [socketpair]: an AF_UNIX SEQPACKET pair inserts its two ends; every
    other answer keeps the fd state. *)
Lemma check_socketpair_fr : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i family type protocol sv eff m m' evs H.
  unfold check_socketpair, check_socketpair_unix, check_socketpair_seqpacket_written,
    check_socketpair_unix_written, check_socketpair_written, check_socketpair_faulted,
    check_errno_only in H.
  cbv zeta in H.
  fr_frame2 H.
Qed.

Lemma check_recvfrom_fr : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd buf size eff m m' evs H.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H.
  repeat (vm_step H || fr_done H || fr_stream H); fr_leaf.
Qed.

Lemma check_recvmsg_fr : forall i fd flags eff m m' evs,
  check_recvmsg i fd flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd flags eff m m' evs H.
  unfold check_recvmsg, check_seqpacket_recvmsg, check_recvmsg_eof_writes,
    check_ret_writes_copyins, check_recv_fd_answer in H.
  fr_frame2 H.
Qed.

Lemma check_sendto_fr : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd buf count flags addrp eff m m' evs H.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H.
  repeat (vm_step H || fr_done H || fr_stream H); fr_leaf.
Qed.

Lemma check_sendmsg_fr : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fd msgp flags eff m m' evs H.
  unfold check_sendmsg, check_send_on_socket in H. fr_frame2 H.
Qed.

Lemma check_pipe2_fr : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i fildes flags eff m m' evs H.
  unfold check_pipe2, pipe2_model in H. fr_frame2 H.
Qed.

Lemma check_futex_fr : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i uaddr op val utime eff m m' evs H.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  fr_frame2 H.
Qed.

Lemma check_set_robust_list_fr : forall len eff m m' evs,
  check_set_robust_list len eff m = CheckOk m' evs -> fd_rel m m'.
Proof. intros len eff m m' evs H. unfold check_set_robust_list in H. fr_frame2 H. Qed.

(** Split [H] on every [if] and [match] to a leaf, as [MmStepFrame] does. *)
Local Ltac mm_walk H :=
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | _ => match type of H with
                 | context [match ?x with _ => _ end] => destruct x
                 end
          end);
  try discriminate H.

Local Ltac mm_leaf H := injection H as <- <-; fr_leaf.

Lemma check_brk_fr : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H.
  unfold check_brk in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mmap_fr : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H.
  (* [check_ret_only] goes last, so the one inside
     [check_mmap_fixed_overflow] (the -ENOMEM answer) is opened too, as
     [MmStepFrame.check_mmap_mm_frame] does. *)
  unfold check_mmap, check_mmap_fixed_overflow, check_ret_only in H.
  mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mremap_fr : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H.
  unfold check_mremap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_munmap_fr : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H.
  unfold check_munmap, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_mprotect_fr : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H.
  unfold check_mprotect, check_ret_only in H. mm_walk H. all: mm_leaf H.
Qed.

Lemma check_madvise_fr : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H.
  unfold check_madvise in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; fr_leaf|].
  dif H; [discriminate|].
  dif H; [apply check_ret_only_model in H; subst m'; fr_leaf|].
  dif H; [apply check_ret_only_model in H; subst m'; fr_leaf|].
  dif H; [|discriminate].
  destruct ws, us, cs, ci; try discriminate.
  dif H; [|discriminate]. injection H as <- <-. fr_leaf.
Qed.

Lemma check_rt_sigprocmask_fr : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i how nset oset ss eff m m' evs H.
  unfold check_rt_sigprocmask in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss;
    cbv beta iota zeta in H.
  { apply check_ret_only_ok_iff in H. destruct H as (_ & -> & _). fr_leaf. }
  destruct (w_is0 nset) eqn:Hn; cbv beta iota in H.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
    - apply check_ret_only_ok_iff in H. destruct H as (_ & -> & _). fr_leaf.
    - apply check_write_oset_ok_iff in H. destruct H as (-> & _ & _ & _). fr_leaf. }
  destruct (sigset_at (in_mem i) nset) as [raw|] eqn:Hr; cbv beta iota in H.
  2:{ apply check_ret_only_ok_iff in H. destruct H as (_ & -> & _). fr_leaf. }
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta in H.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & _). fr_leaf. }
  destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & _).
    apply fd_rel_of_fd. apply m_fd_sigmask_deliver_model. }
  unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset (m_sigmask m) (clear_copyins eff)
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m)
                               (sigmask_strip raw)) m))
    as [m2 evs2| |] eqn:Hcw; [|discriminate|discriminate].
  destruct (access_ranges_eqb (eff_copyins eff)
              [(nset, Z.to_nat NSIG_BYTES)]); [|discriminate].
  apply check_write_oset_ok_iff in Hcw. destruct Hcw as (-> & _ & _ & _).
  inversion H; subst. apply fd_rel_of_fd. apply m_fd_sigmask_deliver_model.
Qed.

Lemma check_tkill_fr : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros pid sig eff m m' evs H.
  unfold check_tkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _); fr_leaf);
    inversion H; subst; fr_leaf.
Qed.

Lemma check_tgkill_fr : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros tgid pid sig eff m m' evs H.
  unfold check_tgkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _); fr_leaf);
    inversion H; subst; fr_leaf.
Qed.

(** [kill] of the caller's own pid: an errno, a 0 with no change, or the
    death by SIGKILL ([State.with_killed]), each keeping [State.m_fd]. *)
Lemma check_kill_fr : forall pid sig eff m m' evs,
  check_kill pid sig eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros pid sig eff m m' evs H.
  unfold check_kill, check_kill_self in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _); fr_leaf.
Qed.

(** The released setns arm answers errnos without changing the model. *)
Lemma check_setns_fr : forall fd eff m m' evs,
  check_setns fd eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros fd eff m m' evs H. unfold check_setns in H. fr_frame2 H.
Qed.

(** The clone arms: the model as it was, or the child recorded over the
    model the caller keeps ([Checks.Sys.Kernel.Fork.check_clone_shape]). *)
Lemma check_clone_fr : forall i flags eff m m' evs,
  check_clone i flags eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i flags eff m m' evs H.
  destruct (check_clone_shape _ _ _ _ _ _ H) as (_ & [(-> & _) | (-> & _)]); fr_leaf.
Qed.

Lemma check_clone3_fr : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs -> fd_rel m m'.
Proof.
  intros i uargs size eff m m' evs H.
  destruct (check_clone3_shape _ _ _ _ _ _ _ H) as (_ & [(-> & _) | (-> & _)]); fr_leaf.
Qed.

(* =========================================================================
   The arms that write the map
   ========================================================================= *)

Lemma check_fcntl_ck : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros fd cmd arg eff m m' evs H Hk. unfold check_fcntl in H.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv beta iota in H.
  - destruct (bv_eqb cmd F_SETFD); cbv beta iota in H.
    + apply check_ret_only_model in H. subst m'.
      apply ck_set_open; [exact Hk | rewrite Hfd; discriminate].
    + repeat vm_step H;
        first [exact Hk | apply (ck_of_fd_rel m); [fr_leaf | exact Hk]].
  - apply check_ret_only_model in H. subst m'. exact Hk.
Qed.

Lemma check_dup_ck : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros oldfd eff m m' evs H Hk. unfold check_dup, check_dup_result in H.
  repeat vm_step H.
  all: cbv beta; first [exact Hk | apply ck_insert_set; exact Hk].
Qed.

Lemma check_dup3_ck : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros oldfd newfd flags eff m m' evs H Hk. unfold check_dup3 in H.
  repeat vm_step H.
  all: first [exact Hk | eapply ck_dup3_fds; eassumption].
Qed.

Lemma check_close_ck : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros fd eff m m' evs H Hk. unfold check_close in H.
  repeat vm_step H.
  all: first [exact Hk | apply ck_close; exact Hk].
Qed.

Lemma check_close_range_ck : forall fd max_fd flags eff m m' evs,
  check_close_range fd max_fd flags eff m = CheckOk m' evs ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros fd max_fd flags eff m m' evs H Hk. unfold check_close_range in H.
  repeat vm_step H.
  all: first [exact Hk | apply ck_close_range; exact Hk].
Qed.

(** [openat]: the table step keeps the map and grows the table; the bit
    is then written at the returned descriptor only where the table holds
    it ([Open.open_cloexec_model]). *)
Lemma check_openat_ck : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros i dirfd pathp flags eff m m' evs H Hk. unfold check_openat in H.
  destruct (check_openat_table i dirfd pathp flags eff m) as [m0 evs0| |] eqn:E;
    try discriminate H.
  injection H as <- <-.
  pose proof (ck_of_fd_rel _ _ (check_openat_table_fr _ _ _ _ _ _ _ _ E) Hk) as Hk0.
  unfold open_cloexec_model.
  destruct (addr_is_error_b (eff_ret eff)); [exact Hk0|].
  destruct (fd_lookup (m_fds m0) (eff_ret eff)) eqn:Ef; [|exact Hk0].
  apply ck_set_open; [exact Hk0 | rewrite Ef; discriminate].
Qed.

(* =========================================================================
   Every arm
   ========================================================================= *)

Definition arm_ck (c : CheckedArm) : Prop :=
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs ->
    cloexec_keys_open m -> cloexec_keys_open m'.

Lemma checked_table_ck : Forall arm_ck checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_ck).
  all: unfold arm_ck; intros i eff m m' evs H Hk; autorewrite with arm_unfold in H.
  all: first
    [ eapply check_fcntl_ck; eassumption
    | eapply check_dup_ck; eassumption
    | eapply check_dup3_ck; eassumption
    | eapply check_close_ck; eassumption
    | eapply check_close_range_ck; eassumption
    | eapply check_openat_ck; eassumption
    | apply (ck_of_fd_rel m m'); [|exact Hk];
      first
      [   eapply check_read_fr; eassumption
        | eapply check_brk_fr; eassumption
        | eapply check_munmap_fr; eassumption
        | eapply check_mremap_fr; eassumption
        | eapply check_mmap_fr; eassumption
        | eapply check_mprotect_fr; eassumption
        | eapply check_write_fr; eassumption
        | eapply check_pread64_fr; eassumption
        | eapply check_pwrite64_fr; eassumption
        | eapply check_lseek_fr; eassumption
        | eapply check_getcwd_fr; eassumption
        | eapply check_getrandom_fr; eassumption
        | eapply check_readlinkat_fr; eassumption
        | eapply check_exit_fr; eassumption
        | eapply check_set_tid_address_fr; eassumption
        | eapply check_ioctl_fr; eassumption
        | eapply check_writev_fr; eassumption
        | eapply check_pwritev2_fr; eassumption
        | eapply check_readv_imported_fr; eassumption
        | eapply check_readv_fr; eassumption
        | eapply check_epoll_create1_fr; eassumption
        | eapply check_epoll_ctl_fr; eassumption
        | eapply check_epoll_pwait_fr; eassumption
        | eapply check_fsync_fr; eassumption
        | eapply check_getdents64_fr; eassumption
        | eapply check_flock_fr; eassumption
        | eapply check_timerfd_create_fr; eassumption
        | eapply check_eventfd2_fr; eassumption
        | eapply check_signalfd4_fr; eassumption
        | eapply check_uname_fr; eassumption
        | eapply check_prlimit64_fr; eassumption
        | eapply check_capget_fr; eassumption
        | eapply check_capset_fr; eassumption
        | eapply check_ftruncate_fr; eassumption
        | eapply check_getpid_fr; eassumption
        | eapply check_gettid_fr; eassumption
        | eapply check_getppid_fr; eassumption
        | eapply check_setsid_fr; eassumption
        | eapply check_getsid_fr; eassumption
        | eapply check_prctl_fr; eassumption
        | eapply check_gettimeofday_fr; eassumption
        | eapply check_clock_gettime_fr; eassumption
        | eapply check_clock_getres_fr; eassumption
        | eapply check_nanosleep_fr; eassumption
        | eapply check_unlinkat_fr; eassumption
        | eapply check_faccessat_fr; eassumption
        | eapply check_faccessat2_fr; eassumption
        | eapply check_pselect6_fr; eassumption
        | eapply check_ppoll_fr; eassumption
        | eapply check_newfstatat_fr; eassumption
        | eapply check_fstat_file_fr; eassumption
        | eapply check_fstat_chrdev_fr; eassumption
        | eapply check_fstat_devnull_fr; eassumption
        | eapply check_fstat_urandom_fr; eassumption
        | eapply check_fstat_fr; eassumption
        | eapply check_getid_fr; eassumption
        | eapply check_getresid_fr; eassumption
        | eapply check_setid_fr; eassumption
        | eapply check_setresid_fr; eassumption
        | eapply check_getgroups_fr; eassumption
        | eapply check_setgroups_fr; eassumption
        | eapply check_socket_fr; eassumption
        | eapply check_bind_fr; eassumption
        | eapply check_listen_fr; eassumption
        | eapply check_connect_fr; eassumption
        | eapply check_accept4_fr; eassumption
        | eapply check_sched_setscheduler_fr; eassumption
        | eapply check_sched_getaffinity_fr; eassumption
        | eapply check_sched_yield_fr; eassumption
        | eapply check_sigaltstack_fr; eassumption
        | eapply check_rt_sigaction_fr; eassumption
        | eapply check_getsockname_fr; eassumption
        | eapply check_getpeername_fr; eassumption
        | eapply check_setsockopt_fr; eassumption
        | eapply check_getsockopt_fr; eassumption
        | eapply check_shutdown_fr; eassumption
        | eapply check_send_on_socket_fr; eassumption
        | eapply check_recv_fd_answer_fr; eassumption
        | eapply check_socketpair_fr; eassumption
        | eapply check_recvfrom_fr; eassumption
        | eapply check_recvmsg_fr; eassumption
        | eapply check_sendto_fr; eassumption
        | eapply check_sendmsg_fr; eassumption
        | eapply check_pipe2_fr; eassumption
        | eapply check_futex_fr; eassumption
        | eapply check_set_robust_list_fr; eassumption
        | eapply check_setns_fr; eassumption
        | eapply check_madvise_fr; eassumption
        | eapply check_rt_sigprocmask_fr; eassumption
        | eapply check_tkill_fr; eassumption
        | eapply check_tgkill_fr; eassumption
        | eapply check_kill_fr; eassumption
        | eapply check_wait4_fr; eassumption
        | eapply check_clone_fr; eassumption
        | eapply check_clone3_fr; eassumption
      ]
    | fail 1 "checked_table_ck has no case for this arm: give its checker a *_fr lemma (it keeps the close-on-exec map and grows the table) or a *_ck one (it writes the map), and add it to the list above" ].
Qed.

(** THE SPEC FACT: every [Ok] answer of the released spec keeps every
    known close-on-exec bit on an open descriptor. *)
Theorem syscall_spec_cloexec_keys : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros i m eff m' evs H Hk. apply check_syscall_ok_iff in H.
  unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_ck as Hall. rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H Hk).
Qed.

(* =========================================================================
   The namespace layer's table writers
   ========================================================================= *)

(** [Ns.Files.install]: the descriptor installed, the released map's key
    for it forgotten. *)
Lemma ns_install_keys : forall reads m ctx st fd k fl cl eff m' ctx' st' evs,
  Files.install reads m ctx st fd k fl cl = Ext.EOk eff m' ctx' st' evs ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros reads m ctx st fd k fl cl eff m' ctx' st' evs H Hk.
  unfold Files.install, Files.ans in H. cbv zeta in H.
  inversion H; subst. apply ck_insert_forget. exact Hk.
Qed.

(** [Ns.Files.close_fn]: the descriptor and its released key go
    together. *)
Lemma ns_close_keys : forall i m ctx st eff m' ctx' st' evs,
  Files.close_fn i m ctx st = Some (Ext.EOk eff m' ctx' st' evs) ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros i m ctx st eff m' ctx' st' evs H Hk.
  unfold Files.close_fn in H. cbv zeta in H.
  match type of H with
  | context [match ?x with _ => _ end] => destruct x as [[h f]|]
  end; [|discriminate H].
  inversion H; subst. apply ck_close. exact Hk.
Qed.

(** [Ns.Net.socket_arm]: an errno leaves the model alone; a socket is
    installed with the released key for it forgotten. *)
Lemma ns_socket_keys : forall i m ctx st eff m' ctx' st' evs,
  Net.socket_arm i m ctx st (Ext.EOk eff m' ctx' st' evs) ->
  cloexec_keys_open m -> cloexec_keys_open m'.
Proof.
  intros i m ctx st eff m' ctx' st' evs H Hk.
  unfold Net.socket_arm in H. cbv zeta in H.
  repeat match type of H with
         | context [if ?b then _ else _] => destruct b
         | context [match ?x with _ => _ end] => destruct x
         end.
  all: repeat match type of H with
              | _ \/ _ => destruct H as [H|H]
              | exists _, _ => destruct H as [? H]
              | _ /\ _ => destruct H as [_ H]
              end.
  all: try (unfold Arm.ns_errno, Arm.ns_ret in H); try discriminate H.
  all: inversion H; subst; first [exact Hk | apply ck_insert_forget; exact Hk].
Qed.
