(** * LinuxProcessSem.Ns.Mount — operations on a mount tree

    Pure functions from a table of mounts to a new table or a Linux errno.
    They decide what the mount tree alone decides; an arm that answers a
    system call adds what the rest of the system decides (open writers for
    EBUSY, the caller's capabilities for EPERM, path lookup for the target).

    Linux 6.18.44 sources:
    - the subtree a recursive operation reaches: [copy_tree] and
      [mount_setattr_prepare] walk [next_mnt] over the subtree,
      fs/namespace.c;
    - [mount_setattr] with and without AT_RECURSIVE: [do_mount_setattr],
      [mount_setattr_prepare], [can_change_locked_flags], fs/namespace.c;
      the whole subtree changes or none of it;
    - a bind: [__do_loopback] refuses an unbindable source with EINVAL
      (fs/namespace.c:2954-2971); [copy_tree] skips an unbindable submount
      with its subtree, or fails with EPERM when that submount is also
      MNT_LOCKED (fs/namespace.c:2157-2230, skip at 2181-2190); a copy keeps
      the source's flags and locks ([clone_mnt]) and is not unbindable, since
      [clone_mnt] does not copy [mnt_t_flags]; with neither CL_SLAVE nor
      CL_PRIVATE a copy joins the source's peer group and keeps its master;
    - a detaching unmount: [can_umount] refuses a mount that is MNT_LOCKED
      with EINVAL; [umount_tree] removes the subtree;
    - a propagation change with or without MS_REC: [do_change_type] over the
      subtree in pre-order, [change_mnt_propagation] and [do_make_slave] on
      each mount (fs/pnode.c): MS_PRIVATE leaves peer group and master;
      MS_SLAVE leaves the peer group and becomes a slave of it when it had
      another member, else keeps its old master;
    - [pivot_root] (SYSCALL_DEFINE2(pivot_root), fs/namespace.c): its checks
      on the three mounts in kernel order, then the new root takes the old
      root's place, the old root goes on put_old, and MNT_LOCKED moves from
      the old root to the new one.  The checks on dentries ([d_unlinked],
      [path_mounted]) belong to the arm that resolves the paths. *)

From Stdlib Require Import List PArith ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables.
Import ListNotations.

Inductive MResult :=
  | MOk  (t : list Mount)
  | MErr (e : Z).

Definition find_mount (T : list Mount) (i : positive) : option Mount :=
  find (fun m => Pos.eqb (mnt_id m) i) T.

Definition is_child_of (p : positive) (m : Mount) : bool :=
  match mnt_parent m with
  | Some q => Pos.eqb q p
  | None => false
  end.

Definition mem (i : positive) (l : list positive) : bool := existsb (Pos.eqb i) l.

(** The ids of the subtree rooted at [r]: [r], then each child's subtree in
    table order.  The fuel is the table's length, which bounds the depth of
    any tree the table holds. *)
Fixpoint subtree_fuel (fuel : nat) (T : list Mount) (r : positive) : list positive :=
  match fuel with
  | O => [r]
  | Datatypes.S f =>
      r :: flat_map (fun m => subtree_fuel f T (mnt_id m)) (List.filter (is_child_of r) T)
  end.

Definition subtree (T : list Mount) (r : positive) : list positive :=
  subtree_fuel (length T) T r.

(* =========================================================================
   mount_setattr
   ========================================================================= *)

Record AttrChange := mkAttr {
  at_set : MountFlags;
  at_clr : MountFlags
}.

Definition flags_or (a b : MountFlags) : MountFlags :=
  mkMountFlags (mf_ro a || mf_ro b) (mf_nosuid a || mf_nosuid b)
               (mf_nodev a || mf_nodev b) (mf_noexec a || mf_noexec b).

Definition flags_clear (a c : MountFlags) : MountFlags :=
  mkMountFlags (mf_ro a && negb (mf_ro c)) (mf_nosuid a && negb (mf_nosuid c))
               (mf_nodev a && negb (mf_nodev c)) (mf_noexec a && negb (mf_noexec c)).

(** The new flags: the cleared ones off, then the set ones on. *)
Definition apply_attr (ch : AttrChange) (f : MountFlags) : MountFlags :=
  flags_or (flags_clear f (at_clr ch)) (at_set ch).

(** [can_change_locked_flags]: a flag that is locked on the mount may not be
    cleared.  Setting it again is always allowed. *)
Definition clears_locked (ch : AttrChange) (m : Mount) : bool :=
  (mf_ro (mnt_lock_flags m) && mf_ro (at_clr ch))
  || (mf_nosuid (mnt_lock_flags m) && mf_nosuid (at_clr ch))
  || (mf_nodev (mnt_lock_flags m) && mf_nodev (at_clr ch))
  || (mf_noexec (mnt_lock_flags m) && mf_noexec (at_clr ch)).

Definition with_flags (m : Mount) (f : MountFlags) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m)
          (mnt_sb m) f (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          (mnt_peer m) (mnt_master m).

Definition setattr_targets (T : list Mount) (r : positive) (recursive : bool) : list positive :=
  if recursive then subtree T r else [r].

Definition mount_setattr (T : list Mount) (r : positive) (recursive : bool) (ch : AttrChange)
    : MResult :=
  match find_mount T r with
  | None => MErr EINVAL
  | Some _ =>
      if existsb (fun m => mem (mnt_id m) (setattr_targets T r recursive) && clears_locked ch m) T
      then MErr EPERM
      else MOk (map (fun m => if mem (mnt_id m) (setattr_targets T r recursive)
                              then with_flags m (apply_attr ch (mnt_flags m))
                              else m) T)
  end.

(** Each flag that [b] has, [a] has too. *)
Definition flags_implies (b a : MountFlags) : bool :=
  implb (mf_ro b) (mf_ro a) && implb (mf_nosuid b) (mf_nosuid a)
  && implb (mf_nodev b) (mf_nodev a) && implb (mf_noexec b) (mf_noexec a).

Lemma flags_or_implies : forall a b, flags_implies b (flags_or a b) = true.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  destruct a1, a2, a3, a4, b1, b2, b3, b4; reflexivity.
Qed.

Lemma mnt_flags_with_flags : forall m f, mnt_flags (with_flags m f) = f.
Proof. reflexivity. Qed.

(** Every mount the change reaches ends with every flag the change sets. *)
Theorem mount_setattr_sets : forall T r rec ch T',
  mount_setattr T r rec ch = MOk T' ->
  forall m', In m' T' -> mem (mnt_id m') (setattr_targets T r rec) = true ->
  flags_implies (at_set ch) (mnt_flags m') = true.
Proof.
  intros T r rec ch T'. unfold mount_setattr.
  destruct (find_mount T r) as [m0|]; [|intros Hc; discriminate Hc].
  destruct (existsb _ T) eqn:Hlock; [intros Hc; discriminate Hc|].
  intros H. injection H as HT. subst T'.
  intros m' Hin.
  apply in_map_iff in Hin. destruct Hin as [m [Heq _]]. subst m'.
  cbv beta.
  destruct (mem (mnt_id m) (setattr_targets T r rec)) eqn:E; cbv iota.
  - intros _. rewrite mnt_flags_with_flags. unfold apply_attr. apply flags_or_implies.
  - intros Ht. rewrite E in Ht. discriminate Ht.
Qed.

(** A mount the change does not reach is left exactly as it was. *)
Theorem mount_setattr_frame : forall T r rec ch T',
  mount_setattr T r rec ch = MOk T' ->
  forall m, In m T -> mem (mnt_id m) (setattr_targets T r rec) = false -> In m T'.
Proof.
  intros T r rec ch T'. unfold mount_setattr.
  destruct (find_mount T r) as [m0|]; [|intros Hc; discriminate Hc].
  destruct (existsb _ T) eqn:Hlock; [intros Hc; discriminate Hc|].
  intros H. injection H as HT. subst T'.
  intros m Hm Hout. apply in_map_iff. exists m. split; [|exact Hm].
  cbv beta. rewrite Hout. reflexivity.
Qed.

(** A change refused for a lock changes nothing: the result names no table. *)
Theorem mount_setattr_locked : forall T r rec ch m,
  find_mount T r <> None ->
  In m T -> mem (mnt_id m) (setattr_targets T r rec) = true -> clears_locked ch m = true ->
  mount_setattr T r rec ch = MErr EPERM.
Proof.
  intros T r rec ch m Hf Hm Ht Hl. unfold mount_setattr.
  destruct (find_mount T r) as [m0|]; [|exfalso; exact (Hf eq_refl)].
  replace (existsb (fun m1 => mem (mnt_id m1) (setattr_targets T r rec) && clears_locked ch m1) T)
    with true; [reflexivity|].
  symmetry. apply existsb_exists. exists m. split; [exact Hm|].
  cbv beta. rewrite Ht, Hl. reflexivity.
Qed.

(* =========================================================================
   Bind
   ========================================================================= *)

Definition max_mount_id (T : list Mount) : positive :=
  fold_left (fun acc m => Pos.max acc (mnt_id m)) T 1%positive.

(** The mounts a recursive bind copies, in order: the source, then each
    child's copies, skipping an unbindable child with its subtree.  [None]
    when an unbindable child is also locked: the bind fails with EPERM. *)
Fixpoint copyable_fuel (fuel : nat) (T : list Mount) (m : Mount) {struct fuel}
    : option (list Mount) :=
  match fuel with
  | O => Some [m]
  | Datatypes.S f =>
      option_map (fun rest => m :: rest)
        (fold_right
           (fun k acc =>
              match acc with
              | None => None
              | Some rest =>
                  if mnt_unbindable k
                  then (if mnt_locked k then None else Some rest)
                  else match copyable_fuel f T k with
                       | None => None
                       | Some sub => Some (sub ++ rest)
                       end
              end)
           (Some []) (List.filter (is_child_of (mnt_id m)) T))
  end.

Fixpoint index_of (i : positive) (l : list Mount) : option nat :=
  match l with
  | [] => None
  | m :: r => if Pos.eqb (mnt_id m) i then Some O else option_map Datatypes.S (index_of i r)
  end.

(** The [k]-th copy.  The copy of the source sits on the target mount at the
    target dentry; any other copy sits on the copy of its parent, at its own
    mount point. *)
Definition copy_of (base : positive) (srcs : list Mount) (src tgt tgt_dentry ns : positive)
    (k : nat) (m : Mount) : Mount :=
  mkMount (base + Pos.of_succ_nat k)%positive ns
          (if Pos.eqb (mnt_id m) src then Some tgt
           else match mnt_parent m with
                | Some p => match index_of p srcs with
                            | Some j => Some (base + Pos.of_succ_nat j)%positive
                            | None => Some tgt
                            end
                | None => Some tgt
                end)
          (if Pos.eqb (mnt_id m) src then tgt_dentry else mnt_mountpoint m)
          (mnt_root m) (mnt_sb m) (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) false
          (mnt_peer m) (mnt_master m).

Definition copies (base : positive) (srcs : list Mount) (src tgt tgt_dentry ns : positive)
    : list Mount :=
  map (fun p => copy_of base srcs src tgt tgt_dentry ns (fst p) (snd p))
      (combine (seq 0 (length srcs)) srcs).

Definition bind_mount (T : list Mount) (src : positive) (recursive : bool)
    (tgt tgt_dentry : positive) : MResult :=
  match find_mount T src, find_mount T tgt with
  | Some s, Some t =>
      if mnt_unbindable s then MErr EINVAL
      else match (if recursive then copyable_fuel (length T) T s else Some [s]) with
           | None => MErr EPERM
           | Some l => MOk (T ++ copies (max_mount_id T) l src tgt tgt_dentry (mnt_ns t))
           end
  | _, _ => MErr EINVAL
  end.

(** No copy a bind makes is unbindable. *)
Theorem copies_not_unbindable : forall base l src tgt d ns c,
  In c (copies base l src tgt d ns) -> mnt_unbindable c = false.
Proof.
  intros base l src tgt d ns c Hin. unfold copies in Hin.
  apply in_map_iff in Hin. destruct Hin as [[k m] [Heq _]]. subst c. reflexivity.
Qed.

(** Every copy carries the flags, the locks and MNT_LOCKED of a mount it
    was copied from. *)
Theorem copies_keep_flags : forall base l src tgt d ns c,
  In c (copies base l src tgt d ns) ->
  exists m, In m l /\ mnt_flags c = mnt_flags m /\ mnt_lock_flags c = mnt_lock_flags m
            /\ mnt_locked c = mnt_locked m.
Proof.
  intros base l src tgt d ns c Hin. unfold copies in Hin.
  apply in_map_iff in Hin. destruct Hin as [[k m] [Heq Hk]]. subst c.
  exists m. split; [eapply in_combine_r; exact Hk|].
  split; [reflexivity|]. split; reflexivity.
Qed.

(** A successful bind keeps every mount the table had, and adds copies. *)
Theorem bind_mount_extends : forall T src rec tgt d T',
  bind_mount T src rec tgt d = MOk T' ->
  exists l ns, T' = T ++ copies (max_mount_id T) l src tgt d ns.
Proof.
  intros T src rec tgt d T'. unfold bind_mount.
  destruct (find_mount T src) as [s|]; [|intros Hc; discriminate Hc].
  destruct (find_mount T tgt) as [t|]; [|intros Hc; discriminate Hc].
  destruct (mnt_unbindable s); [intros Hc; discriminate Hc|].
  destruct (if rec then copyable_fuel (length T) T s else Some [s]) as [l|];
    [|intros Hc; discriminate Hc].
  intros H. injection H as HT. subst T'. exists l, (mnt_ns t). reflexivity.
Qed.

(* =========================================================================
   Detaching unmount
   ========================================================================= *)

Definition umount_detach (T : list Mount) (i : positive) : MResult :=
  match find_mount T i with
  | None => MErr EINVAL
  | Some m =>
      if mnt_locked m then MErr EINVAL
      else MOk (List.filter (fun x => negb (mem (mnt_id x) (subtree T i))) T)
  end.

(** After a detaching unmount no mount of the subtree is in the table. *)
Theorem umount_detach_removes : forall T i T',
  umount_detach T i = MOk T' -> forall m, In m T' -> mem (mnt_id m) (subtree T i) = false.
Proof.
  intros T i T'. unfold umount_detach.
  destruct (find_mount T i) as [m0|]; [|intros Hc; discriminate Hc].
  destruct (mnt_locked m0); [intros Hc; discriminate Hc|].
  intros H. injection H as HT. subst T'.
  intros m Hm. apply filter_In in Hm. destruct Hm as [_ Hneg].
  cbv beta in Hneg. apply negb_true_iff in Hneg. exact Hneg.
Qed.

(* =========================================================================
   Propagation changes
   =========================================================================

   A mount's peer group is [mnt_peer] ([mnt_group_id] while MNT_SHARED);
   a slave's master is the peer group it receives from.  The kernel's
   [mnt_master] names one member of that group, and [transfer_propagation]
   moves a slave to another member whenever its master leaves the group, so
   the group is what a slave receives from.  MS_SHARED and MS_UNBINDABLE
   are not modelled here. *)

Inductive PropChange := PropPrivate | PropSlave.

Definition with_prop (m : Mount) (peer master : option positive) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m)
          (mnt_sb m) (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          peer master.

(** MS_PRIVATE: no peer group, no master, and the unbindable mark cleared. *)
Definition made_private (m : Mount) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m)
          (mnt_sb m) (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) false None None.

(** Another mount of the table is in peer group [g]. *)
Definition has_other_peer (t : list Mount) (m : Mount) (g : positive) : bool :=
  existsb (fun x => negb (Pos.eqb (mnt_id x) (mnt_id m))
                    && match mnt_peer x with Some h => Pos.eqb h g | None => false end) t.

(** What [m] receives from once it leaves its peer group: the group, through
    [next_peer], when the group has another member; else [m]'s own master. *)
Definition passed_master (t : list Mount) (m : Mount) : option positive :=
  match mnt_peer m with
  | Some g => if has_other_peer t m g then Some g else mnt_master m
  | None => mnt_master m
  end.

(** The peer group [m] ends by leaving it: the group [m] is the only member
    of. *)
Definition ended_group (t : list Mount) (m : Mount) : option positive :=
  match mnt_peer m with
  | Some g => if has_other_peer t m g then None else Some g
  | None => None
  end.

Definition slave_of (g : option positive) (x : Mount) : bool :=
  match g, mnt_master x with
  | Some a, Some b => Pos.eqb a b
  | _, _ => false
  end.

(** [change_mnt_propagation] of mount [m] in table [t], seen at mount [x]:
    [m] leaves its peer group and becomes a slave or private; a slave of a
    group [m] ends passes to [m]'s old master. *)
Definition change_mount (k : PropChange) (t : list Mount) (m x : Mount) : Mount :=
  if Pos.eqb (mnt_id x) (mnt_id m) then
    match k with
    | PropSlave => with_prop x None (passed_master t m)
    | PropPrivate => made_private x
    end
  else if slave_of (ended_group t m) x then with_prop x (mnt_peer x) (mnt_master m)
  else x.

Definition change_one (k : PropChange) (t : list Mount) (i : positive) : list Mount :=
  match find_mount t i with
  | None => t
  | Some m => map (change_mount k t m) t
  end.

(** The mounts change one at a time, in pre-order, each one against the
    table the earlier ones left, as [do_change_type]'s loop over
    [next_mnt] does; siblings come in table order.  The checks before the
    loop (the path is the root of its mount; the caller is CAP_SYS_ADMIN
    over the mount's namespace) belong to the arm. *)
Definition change_propagation (T : list Mount) (r : positive) (recursive : bool) (k : PropChange)
    : MResult :=
  match find_mount T r with
  | None => MErr EINVAL
  | Some _ => MOk (fold_left (change_one k) (setattr_targets T r recursive) T)
  end.

Lemma mnt_id_change_mount : forall k t m x, mnt_id (change_mount k t m x) = mnt_id x.
Proof.
  intros k t m x. unfold change_mount.
  destruct (Pos.eqb (mnt_id x) (mnt_id m));
    [destruct k | destruct (slave_of (ended_group t m) x)]; reflexivity.
Qed.

(** The mount a change names ends in no peer group; a change to private also
    leaves it with no master and not unbindable. *)
Lemma change_one_named : forall k t i m',
  In m' (change_one k t i) -> mnt_id m' = i ->
  mnt_peer m' = None
  /\ (k = PropPrivate -> mnt_master m' = None /\ mnt_unbindable m' = false).
Proof.
  intros k t i m' Hin Hid. unfold change_one in Hin.
  destruct (find_mount t i) as [m|] eqn:Hf; cbv beta iota in Hin.
  - apply in_map_iff in Hin. destruct Hin as [x [Hx Hxt]].
    unfold find_mount in Hf. apply find_some in Hf. destruct Hf as [_ Hmi].
    cbv beta in Hmi. apply Pos.eqb_eq in Hmi.
    assert (Hxi : mnt_id x = mnt_id m).
    { rewrite <- Hx in Hid. rewrite mnt_id_change_mount in Hid. congruence. }
    rewrite <- Hx. unfold change_mount. rewrite Hxi, Pos.eqb_refl.
    destruct k; (split; [reflexivity|]); intros Hk; first [discriminate Hk | split; reflexivity].
  - exfalso. unfold find_mount in Hf. pose proof (find_none _ _ Hf m' Hin) as Hn.
    cbv beta in Hn. rewrite Hid, Pos.eqb_refl in Hn. discriminate Hn.
Qed.

(** Any other mount keeps its id and peer group, and a mount with no master
    is left as it was. *)
Lemma change_one_other : forall k t i m',
  In m' (change_one k t i) -> mnt_id m' <> i ->
  exists x, In x t /\ mnt_id x = mnt_id m' /\ mnt_peer m' = mnt_peer x
            /\ (mnt_master x = None -> m' = x).
Proof.
  intros k t i m' Hin Hne. unfold change_one in Hin.
  destruct (find_mount t i) as [m|] eqn:Hf; cbv beta iota in Hin.
  - apply in_map_iff in Hin. destruct Hin as [x [Hx Hxt]].
    unfold find_mount in Hf. apply find_some in Hf. destruct Hf as [_ Hmi].
    cbv beta in Hmi. apply Pos.eqb_eq in Hmi.
    exists x. split; [exact Hxt|].
    assert (Hxid : mnt_id x = mnt_id m').
    { rewrite <- Hx. rewrite mnt_id_change_mount. reflexivity. }
    split; [exact Hxid|].
    rewrite <- Hx. unfold change_mount.
    destruct (Pos.eqb_spec (mnt_id x) (mnt_id m)) as [E|E].
    + exfalso. apply Hne. congruence.
    + split.
      * destruct (slave_of (ended_group t m) x); reflexivity.
      * intros Hx0. unfold slave_of. rewrite Hx0.
        destruct (ended_group t m); reflexivity.
  - exists m'. split; [exact Hin|]. split; [reflexivity|]. split; [reflexivity|].
    intros _. reflexivity.
Qed.

(** A property every mount of [done] has survives a [change_one] that names
    [i], for [i] and the mounts of [done] alike, so it holds after the whole
    loop for every mount the loop named. *)
Lemma fold_change_inv : forall (P : Mount -> Prop) k,
  (forall t i done, (forall m, In m t -> In (mnt_id m) done -> P m) ->
     forall m', In m' (change_one k t i) -> In (mnt_id m') (i :: done) -> P m') ->
  forall targets t done, (forall m, In m t -> In (mnt_id m) done -> P m) ->
  forall m', In m' (fold_left (change_one k) targets t) -> In (mnt_id m') (targets ++ done) -> P m'.
Proof.
  intros P k Hstep targets. induction targets as [|i rest IH]; intros t done Hinv m' Hin Hid.
  - exact (Hinv m' Hin Hid).
  - apply (IH (change_one k t i) (i :: done)).
    + intros m Hm Hmd. exact (Hstep t i done Hinv m Hm Hmd).
    + exact Hin.
    + change (In (mnt_id m') (i :: (rest ++ done))) in Hid.
      apply in_inv in Hid. destruct Hid as [Hi|Hr].
      * apply in_or_app. right. rewrite <- Hi. apply in_eq.
      * apply in_app_or in Hr. destruct Hr as [Hr|Hd].
        -- apply in_or_app. left. exact Hr.
        -- apply in_or_app. right. apply in_cons. exact Hd.
Qed.

Lemma change_one_peer : forall k t i done,
  (forall m, In m t -> In (mnt_id m) done -> mnt_peer m = None) ->
  forall m', In m' (change_one k t i) -> In (mnt_id m') (i :: done) -> mnt_peer m' = None.
Proof.
  intros k t i done Hinv m' Hin Hid.
  destruct (Pos.eq_dec (mnt_id m') i) as [E|E].
  - exact (proj1 (change_one_named k t i m' Hin E)).
  - destruct (change_one_other k t i m' Hin E) as [x [Hxt [Hxid [Hp _]]]].
    rewrite Hp. apply (Hinv x Hxt). rewrite Hxid.
    apply in_inv in Hid. destruct Hid as [Hi|Hd]; [congruence | exact Hd].
Qed.

Lemma change_one_master_private : forall t i done,
  (forall m, In m t -> In (mnt_id m) done -> mnt_master m = None) ->
  forall m', In m' (change_one PropPrivate t i) -> In (mnt_id m') (i :: done) ->
  mnt_master m' = None.
Proof.
  intros t i done Hinv m' Hin Hid.
  destruct (Pos.eq_dec (mnt_id m') i) as [E|E].
  - exact (proj1 (proj2 (change_one_named PropPrivate t i m' Hin E) eq_refl)).
  - destruct (change_one_other PropPrivate t i m' Hin E) as [x [Hxt [Hxid [_ Hkeep]]]].
    assert (Hd : In (mnt_id x) done).
    { rewrite Hxid. apply in_inv in Hid. destruct Hid as [Hi|Hd]; [congruence | exact Hd]. }
    pose proof (Hinv x Hxt Hd) as Hx0.
    rewrite (Hkeep Hx0). exact Hx0.
Qed.

(** After a propagation change of either kind, every mount it reached is in
    no peer group, so no later mount or unmount under it propagates. *)
Theorem change_propagation_unshared : forall T r rec k T',
  change_propagation T r rec k = MOk T' ->
  forall m', In m' T' -> In (mnt_id m') (setattr_targets T r rec) -> mnt_peer m' = None.
Proof.
  intros T r rec k T'. unfold change_propagation.
  destruct (find_mount T r) as [m0|]; [|intros Hc; discriminate Hc].
  intros H. injection H as HT. subst T'.
  intros m' Hin Hid.
  apply (fold_change_inv (fun m => mnt_peer m = None) k (change_one_peer k)
           (setattr_targets T r rec) T [] (fun m _ Hd => False_ind _ Hd) m' Hin).
  rewrite app_nil_r. exact Hid.
Qed.

(** After a change to private, every mount it reached is also no slave, so
    it receives nothing either. *)
Theorem change_propagation_private : forall T r rec T',
  change_propagation T r rec PropPrivate = MOk T' ->
  forall m', In m' T' -> In (mnt_id m') (setattr_targets T r rec) -> mnt_master m' = None.
Proof.
  intros T r rec T'. unfold change_propagation.
  destruct (find_mount T r) as [m0|]; [|intros Hc; discriminate Hc].
  intros H. injection H as HT. subst T'.
  intros m' Hin Hid.
  apply (fold_change_inv (fun m => mnt_master m = None) PropPrivate change_one_master_private
           (setattr_targets T r rec) T [] (fun m _ Hd => False_ind _ Hd) m' Hin).
  rewrite app_nil_r. exact Hid.
Qed.

(* =========================================================================
   pivot_root
   ========================================================================= *)

(** What the path walk found, which the kernel checks between its checks on
    the mounts: the new root's dentry is unlinked ([d_unlinked]); the task's
    root is the root of its mount, and so is the new root
    ([path_mounted]). *)
Record PivotPaths := mkPivotPaths {
  pp_new_unlinked : bool;
  pp_root_mounted : bool;
  pp_new_mounted  : bool
}.

(** A mount's parent, or the mount itself when it has none, as [mnt_parent]
    is in the kernel. *)
Definition parent_or_self (m : Mount) : positive :=
  match mnt_parent m with Some p => p | None => mnt_id m end.

Definition is_shared (T : list Mount) (i : positive) : bool :=
  match find_mount T i with
  | Some m => match mnt_peer m with Some _ => true | None => false end
  | None => false
  end.

(** The move: the new root [nr] takes the old root's parent and mount point
    ([rp], [rmp]); the old root [rt] goes on put_old, dentry [d] of mount
    [old]; MNT_LOCKED moves from the old root ([rlocked]) to the new one. *)
Definition pivot_effect (T : list Mount) (rt nr old d rp rmp : positive) (rlocked : bool)
    : list Mount :=
  map (fun m =>
         if Pos.eqb (mnt_id m) nr then
           mkMount (mnt_id m) (mnt_ns m) (Some rp) rmp (mnt_root m) (mnt_sb m)
                   (mnt_flags m) (mnt_lock_flags m) (mnt_locked m || rlocked)
                   (mnt_unbindable m) (mnt_peer m) (mnt_master m)
         else if Pos.eqb (mnt_id m) rt then
           mkMount (mnt_id m) (mnt_ns m) (Some old) d (mnt_root m) (mnt_sb m)
                   (mnt_flags m) (mnt_lock_flags m) false
                   (mnt_unbindable m) (mnt_peer m) (mnt_master m)
         else m) T.

(** [pivot_root] in the caller's mount namespace [ns], with the caller's
    root on mount [rt], the new root on mount [nr], and put_old at dentry
    [d] of mount [old] (the top of the mount stack there, as [LOCK_MOUNT]
    finds it).  The checks run in the kernel's order, the path checks of
    [pp] among them: a shared put_old mount, parent of the new root or
    parent of the root (EINVAL); the root or new root outside [ns] (EINVAL);
    a locked new root (EINVAL); an unlinked new root (ENOENT); the new root
    or the put_old mount being the root mount (EBUSY); the root not the
    root of its mount, or with no parent; the new root likewise; put_old
    not under the new root; the new root not under the root (each EINVAL).
    The arm adds what comes before (CAP_SYS_ADMIN, the two lookups, the LSM
    hook) and after: [chroot_fs_refs] moves every task's root and working
    directory that are the old root to the new root. *)
Definition pivot_root (T : list Mount) (ns rt nr old d : positive) (pp : PivotPaths)
    : MResult :=
  match find_mount T rt, find_mount T nr, find_mount T old with
  | Some r, Some n, Some _ =>
      if is_shared T old || is_shared T (parent_or_self n) || is_shared T (parent_or_self r)
      then MErr EINVAL
      else if negb (Pos.eqb (mnt_ns r) ns) || negb (Pos.eqb (mnt_ns n) ns) then MErr EINVAL
      else if mnt_locked n then MErr EINVAL
      else if pp_new_unlinked pp then MErr ENOENT
      else if Pos.eqb nr rt || Pos.eqb old rt then MErr EBUSY
      else if negb (pp_root_mounted pp) then MErr EINVAL
      else match mnt_parent r with
           | None => MErr EINVAL
           | Some rp =>
               if negb (pp_new_mounted pp) then MErr EINVAL
               else match mnt_parent n with
                    | None => MErr EINVAL
                    | Some _ =>
                        if negb (mem old (subtree T nr)) then MErr EINVAL
                        else if negb (mem nr (subtree T rt)) then MErr EINVAL
                        else MOk (pivot_effect T rt nr old d rp (mnt_mountpoint r)
                                               (mnt_locked r))
                    end
           end
  | _, _, _ => MErr EINVAL
  end.

(** A pivot that succeeds is the move of [pivot_effect], with the root's
    parent and mount point, and a new root that is not the root. *)
Theorem pivot_root_effect : forall T ns rt nr old d pp T',
  pivot_root T ns rt nr old d pp = MOk T' ->
  exists r rp, find_mount T rt = Some r /\ mnt_parent r = Some rp /\ nr <> rt
               /\ T' = pivot_effect T rt nr old d rp (mnt_mountpoint r) (mnt_locked r).
Proof.
  intros T ns rt nr old d pp T'. unfold pivot_root.
  destruct (find_mount T rt) as [r|] eqn:Hr; [|intros Hc; discriminate Hc].
  destruct (find_mount T nr) as [n|]; [|intros Hc; discriminate Hc].
  destruct (find_mount T old) as [o|]; [|intros Hc; discriminate Hc].
  cbv beta iota.
  destruct (is_shared T old || is_shared T (parent_or_self n) || is_shared T (parent_or_self r));
    [intros Hc; discriminate Hc|].
  destruct (negb (Pos.eqb (mnt_ns r) ns) || negb (Pos.eqb (mnt_ns n) ns));
    [intros Hc; discriminate Hc|].
  destruct (mnt_locked n); [intros Hc; discriminate Hc|].
  destruct (pp_new_unlinked pp); [intros Hc; discriminate Hc|].
  destruct (Pos.eqb_spec nr rt) as [Eb|Eb]; [intros Hc; discriminate Hc|].
  destruct (Pos.eqb old rt); [intros Hc; discriminate Hc|].
  destruct (negb (pp_root_mounted pp)); [intros Hc; discriminate Hc|].
  destruct (mnt_parent r) as [rp|] eqn:Hrp; [|intros Hc; discriminate Hc].
  destruct (negb (pp_new_mounted pp)); [intros Hc; discriminate Hc|].
  destruct (mnt_parent n) as [np|]; [|intros Hc; discriminate Hc].
  destruct (negb (mem old (subtree T nr))); [intros Hc; discriminate Hc|].
  destruct (negb (mem nr (subtree T rt))); [intros Hc; discriminate Hc|].
  intros H. injection H as HT. subst T'.
  exists r, rp. split; [first [reflexivity | exact Hr]|].
  split; [exact Hrp|]. split; [exact Eb | reflexivity].
Qed.

(** A mount other than the two that move is left as it was. *)
Theorem pivot_effect_frame : forall T rt nr old d rp rmp rl m,
  In m T -> mnt_id m <> nr -> mnt_id m <> rt -> In m (pivot_effect T rt nr old d rp rmp rl).
Proof.
  intros T rt nr old d rp rmp rl m Hm Hn Hr. unfold pivot_effect.
  apply in_map_iff. exists m. split; [|exact Hm]. cbv beta.
  destruct (Pos.eqb_spec (mnt_id m) nr) as [E|E]; [contradiction|].
  destruct (Pos.eqb_spec (mnt_id m) rt) as [E2|E2]; [contradiction|].
  reflexivity.
Qed.

(** The new root takes the old root's parent and mount point. *)
Theorem pivot_effect_new_root : forall T rt nr old d rp rmp rl n,
  In n T -> mnt_id n = nr ->
  exists m', In m' (pivot_effect T rt nr old d rp rmp rl)
             /\ mnt_id m' = nr /\ mnt_parent m' = Some rp /\ mnt_mountpoint m' = rmp.
Proof.
  intros T rt nr old d rp rmp rl n Hn Hid.
  exists (mkMount (mnt_id n) (mnt_ns n) (Some rp) rmp (mnt_root n) (mnt_sb n)
                  (mnt_flags n) (mnt_lock_flags n) (mnt_locked n || rl)
                  (mnt_unbindable n) (mnt_peer n) (mnt_master n)).
  split; [|split; [exact Hid | split; reflexivity]].
  unfold pivot_effect. apply in_map_iff. exists n. split; [|exact Hn]. cbv beta.
  rewrite Hid, Pos.eqb_refl. reflexivity.
Qed.

(** The old root goes on put_old and is no longer MNT_LOCKED. *)
Theorem pivot_effect_old_root : forall T rt nr old d rp rmp rl r,
  In r T -> mnt_id r = rt -> rt <> nr ->
  exists m', In m' (pivot_effect T rt nr old d rp rmp rl)
             /\ mnt_id m' = rt /\ mnt_parent m' = Some old /\ mnt_mountpoint m' = d
             /\ mnt_locked m' = false.
Proof.
  intros T rt nr old d rp rmp rl r Hr Hid Hne.
  exists (mkMount (mnt_id r) (mnt_ns r) (Some old) d (mnt_root r) (mnt_sb r)
                  (mnt_flags r) (mnt_lock_flags r) false
                  (mnt_unbindable r) (mnt_peer r) (mnt_master r)).
  split; [|split; [exact Hid | split; [reflexivity | split; reflexivity]]].
  unfold pivot_effect. apply in_map_iff. exists r. split; [|exact Hr]. cbv beta.
  apply Pos.eqb_neq in Hne.
  rewrite Hid, Hne, Pos.eqb_refl. reflexivity.
Qed.
