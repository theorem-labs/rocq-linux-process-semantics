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
      [clone_mnt] does not copy [mnt_t_flags];
    - a detaching unmount: [can_umount] refuses a mount that is MNT_LOCKED
      with EINVAL; [umount_tree] removes the subtree. *)

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
          (mnt_sb m) f (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m).

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
  destruct (find_mount T r) as [m0|] eqn:Ef; [|exfalso; exact (Hf Ef)].
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
          (mnt_root m) (mnt_sb m) (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) false.

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
