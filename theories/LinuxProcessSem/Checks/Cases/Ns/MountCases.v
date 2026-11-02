(** * LinuxProcessSem.Checks.Cases.Ns.MountCases — the mount tree on small trees

    Each example runs one operation of [Ns.Mount] on a tree of four mounts
    and states its exact result: which mounts a recursive operation reaches,
    which flags change, which mounts a recursive bind copies, how
    [pivot_root] moves the mounts, and the errno a refused operation gives.
    Mount 1 is the namespace root, mount 2 sits on mount 1, mounts 3 and 4
    sit on mount 2, and mount 4 is unbindable.  No mount is shared or a
    slave unless an example says so. *)

From Stdlib Require Import List PArith ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount.
Import ListNotations.
Open Scope positive_scope.

Definition no_flags : MountFlags := mkMountFlags false false false false.
Definition ro_only : MountFlags := mkMountFlags true false false false.

Definition mnt (i : positive) (p : option positive) (unbindable : bool) : Mount :=
  mkMount i 1 p 10 20 30 no_flags no_flags false unbindable None None.

Definition tree : list Mount :=
  [mnt 1 None false; mnt 2 (Some 1) false; mnt 3 (Some 2) false; mnt 4 (Some 2) true].

(** The subtree of a mount: the mount, then its children's subtrees. *)
Example subtree_of_2 : subtree tree 2 = [2; 3; 4] := eq_refl.
Example subtree_of_3 : subtree tree 3 = [3] := eq_refl.

Definition set_ro : AttrChange := mkAttr ro_only no_flags.

Definition ro_bits (r : MResult) : list bool :=
  match r with
  | MOk t => map (fun m => mf_ro (mnt_flags m)) t
  | MErr _ => []
  end.

(** A recursive change reaches the whole subtree and nothing else. *)
Example setattr_recursive_sets_subtree :
  ro_bits (mount_setattr tree 2 true set_ro) = [false; true; true; true] := eq_refl.

(** Without the recursive flag only the named mount changes. *)
Example setattr_single_sets_one :
  ro_bits (mount_setattr tree 2 false set_ro) = [false; true; false; false] := eq_refl.

(** Clearing a flag that is locked on the mount is refused with EPERM. *)
Definition locked_ro (i : positive) (p : option positive) : Mount :=
  mkMount i 1 p 10 20 30 ro_only ro_only false false None None.

Definition tree_locked : list Mount := [mnt 1 None false; locked_ro 2 (Some 1)].

Example setattr_clear_locked_refused :
  mount_setattr tree_locked 2 false (mkAttr no_flags ro_only) = MErr 1%Z := eq_refl.

(** Setting a locked flag again is allowed. *)
Example setattr_set_locked_allowed :
  ro_bits (mount_setattr tree_locked 2 false set_ro) = [false; true] := eq_refl.

Example setattr_missing_mount : mount_setattr tree 9 false set_ro = MErr 22%Z := eq_refl.

Definition ids (r : MResult) : list positive :=
  match r with MOk t => map mnt_id t | MErr _ => [] end.

(** The decided answer of a bind; [MErr 0] stands for "not decided" and no
    example below expects it. *)
Definition bound (r : option MResult) : MResult :=
  match r with Some x => x | None => MErr 0%Z end.

Definition copied (n : nat) (r : option MResult) : list Mount :=
  match bound r with MOk t => skipn n t | MErr _ => [] end.

(** A bind of a whole mount: the source path is the mount's root (dentry
    20), so every child is under it, and no path check fails. *)
Definition whole : BindPaths := mkBindPaths 20 (fun _ => true) false false false.

(** Binds run in mount namespace 1 with room for 100 mounts. *)
Definition bind (T : list Mount) (src : positive) (bp : BindPaths) (rec : bool)
    (tgt d : positive) : option MResult :=
  bind_mount T 1 100 src bp rec tgt d.

(** A recursive bind of mount 2 onto mount 1 at dentry 7 copies mounts 2 and
    3 as new mounts 5 and 6, and skips the unbindable mount 4. *)
Example bind_skips_unbindable :
  ids (bound (bind tree 2 whole true 1 7)) = [1; 2; 3; 4; 5; 6] := eq_refl.

(** The copy of the bound mount sits on the target at the target dentry; the
    copy of its child sits on that copy, at the child's own mount point. *)
Example bind_relinks_parents :
  map mnt_parent (copied 4 (bind tree 2 whole true 1 7)) = [Some 1; Some 5] := eq_refl.

Example bind_sets_mountpoints :
  map mnt_mountpoint (copied 4 (bind tree 2 whole true 1 7)) = [7; 10] := eq_refl.

Example bind_copies_are_bindable :
  map mnt_unbindable (copied 4 (bind tree 2 whole true 1 7)) = [false; false] := eq_refl.

(** A bind that is not recursive copies the one mount. *)
Example bind_nonrecursive_one_copy :
  ids (bound (bind tree 2 whole false 1 7)) = [1; 2; 3; 4; 5] := eq_refl.

(** A bind of a directory inside a mount copies only the child mounts whose
    mount point is under that directory: mount 5 sits at dentry 11, which is
    under the source dentry 50, and mount 3 at dentry 10, which is not.  The
    copy of the source has the source dentry as its root. *)
Definition tree_sub : list Mount :=
  [mnt 1 None false; mnt 2 (Some 1) false; mnt 3 (Some 2) false;
   mkMount 5 1 (Some 2) 11 20 30 no_flags no_flags false false None None].

Definition sub : BindPaths := mkBindPaths 50 (fun d => Pos.eqb d 11) false false false.

Example bind_subdir_copies_below :
  ids (bound (bind tree_sub 2 sub true 1 7)) = [1; 2; 3; 5; 6; 7] := eq_refl.

Example bind_subdir_root :
  map mnt_root (copied 4 (bind tree_sub 2 sub true 1 7)) = [50; 20] := eq_refl.

(** The copy of the source is not MNT_LOCKED ([clone_mnt] clears it); a copy
    of a locked child is ([copy_tree] sets it again). *)
Definition tree_lk : list Mount :=
  [mnt 1 None false;
   mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags true false None None;
   mkMount 3 1 (Some 2) 10 20 30 no_flags no_flags true false None None].

Example bind_locks_children_only :
  map mnt_locked (copied 3 (bind tree_lk 2 whole true 1 7)) = [false; true] := eq_refl.

(** A bind that is not recursive is refused with EINVAL when a locked child
    sits under the source path, and allowed when none does. *)
Example bind_nonrecursive_locked_child :
  bind tree_lk 2 whole false 1 7 = Some (MErr 22%Z) := eq_refl.

Example bind_nonrecursive_locked_child_elsewhere :
  ids (bound (bind tree_lk 2 (mkBindPaths 50 (fun _ => false) false false false) false 1 7))
  = [1; 2; 3; 4] := eq_refl.

(** A recursive bind that meets an unbindable mount that is also locked is
    refused with EPERM. *)
Definition tree_lub : list Mount :=
  [mnt 1 None false; mnt 2 (Some 1) false;
   mkMount 3 1 (Some 2) 10 20 30 no_flags no_flags true true None None].

Example bind_locked_unbindable_refused :
  bind tree_lub 2 whole true 1 7 = Some (MErr 1%Z) := eq_refl.

(** An unbindable source is refused with EINVAL. *)
Example bind_unbindable_source_refused :
  bind tree 4 whole true 1 7 = Some (MErr 22%Z) := eq_refl.

(** A copy of a shared mount joins its peer group. *)
Definition tree_shared : list Mount :=
  [mnt 1 None false; mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags false false (Some 8) None].

Example bind_copy_joins_peer_group :
  map mnt_peer (copied 2 (bind tree_shared 2 whole false 1 7)) = [Some 8] := eq_refl.

(** Mount 9 is in another mount namespace.  A target there is refused with
    EINVAL ([do_loopback]'s [check_mnt]); a source there is not decided by
    the tree ([may_copy_tree] also accepts an nsfs or pidfs dentry and a
    mount of an anonymous namespace), unless an earlier check refuses it:
    a source dentry that would make a namespace loop. *)
Definition tree_ns : list Mount :=
  tree ++ [mkMount 9 2 None 10 20 30 no_flags no_flags false false None None].

Example bind_target_other_ns : bind tree_ns 2 whole true 9 7 = Some (MErr 22%Z) := eq_refl.

Example bind_source_other_ns_undecided : bind tree_ns 9 whole true 1 7 = None := eq_refl.

Example bind_ns_loop_first :
  bind tree_ns 9 (mkBindPaths 20 (fun _ => true) true false false) true 1 7
  = Some (MErr 22%Z) := eq_refl.

(** At the graft: a source on a superblock with SB_NOUSER is refused with
    EINVAL, a directory onto a non-directory or back with ENOTDIR, and both
    come after the copy, so a copy that fails with EPERM fails first. *)
Example bind_nouser : bind tree 2 (mkBindPaths 20 (fun _ => true) false true false) true 1 7
  = Some (MErr 22%Z) := eq_refl.

Example bind_dir_mismatch : bind tree 2 (mkBindPaths 20 (fun _ => true) false false true) true 1 7
  = Some (MErr 20%Z) := eq_refl.

Example bind_eperm_before_nouser :
  bind tree_lub 2 (mkBindPaths 20 (fun _ => true) false true false) true 1 7
  = Some (MErr 1%Z) := eq_refl.

(** [count_mounts]: the namespace holds 4 mounts and a recursive bind of
    mount 2 adds 2, so a limit of 5 refuses it with ENOSPC and a limit of 6
    allows it. *)
Example bind_mount_max_refused : bind_mount tree 1 5 2 whole true 1 7 = Some (MErr 28%Z)
  := eq_refl.

Example bind_mount_max_allowed :
  ids (bound (bind_mount tree 1 6 2 whole true 1 7)) = [1; 2; 3; 4; 5; 6] := eq_refl.

(** A shared target propagates the new mounts to its peers and slaves
    ([attach_recursive_mnt]), which the tree does not decide; the limit is
    checked first. *)
Example bind_shared_target_undecided : bind tree_shared 1 whole false 2 7 = None := eq_refl.

Example bind_shared_target_limit_first :
  bind_mount tree_shared 1 2 1 whole false 2 7 = Some (MErr 28%Z) := eq_refl.

(** A detaching unmount removes the whole subtree. *)
Example umount_detaches_subtree : ids (umount_detach tree 2) = [1] := eq_refl.

Example umount_locked_refused :
  umount_detach [mnt 1 None false; mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags true false None None] 2
  = MErr 22%Z := eq_refl.

(** The namespace root cannot be detached. *)
Example umount_root_refused : umount_detach tree 1 = MErr 22%Z := eq_refl.

(** A shared or slave parent requires UMOUNT_PROPAGATE, which this local
    tree operation declines. *)
Definition tree_with_shared_parent : list Mount :=
  [mkMount 1 1 None 10 20 30 no_flags no_flags false false (Some 8) None;
   mnt 2 (Some 1) false].
Example umount_shared_parent_declines :
  umount_propagates tree_with_shared_parent (mnt 2 (Some 1) false) = true := eq_refl.

(** Propagation changes reach the subtree with the recursive flag.  A shared
    mount made a slave leaves its peer group; it becomes a slave of that
    group when the group has another member (mount 4 is a peer of mount 2),
    and otherwise keeps its old master, here none (mount 3 is alone in group
    9).  A mount made private has neither. *)
Definition tree_prop : list Mount :=
  [mnt 1 None false;
   mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags false false (Some 8) None;
   mkMount 3 1 (Some 2) 10 20 30 no_flags no_flags false false (Some 9) None;
   mkMount 4 1 (Some 1) 10 20 30 no_flags no_flags false false (Some 8) None].

Definition peers_masters (r : MResult) : list (option positive * option positive) :=
  match r with MOk t => map (fun m => (mnt_peer m, mnt_master m)) t | MErr _ => [] end.

Example make_slave_recursive :
  peers_masters (change_propagation tree_prop 2 true PropSlave)
  = [(None, None); (None, Some 8); (None, None); (Some 8, None)] := eq_refl.

Example make_private_single :
  peers_masters (change_propagation tree_prop 2 false PropPrivate)
  = [(None, None); (None, None); (Some 9, None); (Some 8, None)] := eq_refl.

(** A mount that leaves a peer group it was the only member of ends the
    group, and the group's slaves pass to that mount's old master
    ([transfer_propagation]): mount 3, alone in group 9, is a slave of group
    7, and mount 5 is a slave of group 9. *)
Definition tree_transfer : list Mount :=
  [mnt 1 None false;
   mkMount 3 1 (Some 1) 10 20 30 no_flags no_flags false false (Some 9) (Some 7);
   mkMount 5 1 (Some 1) 10 20 30 no_flags no_flags false false None (Some 9)].

Example private_transfers_slaves :
  peers_masters (change_propagation tree_transfer 3 false PropPrivate)
  = [(None, None); (None, None); (None, Some 7)] := eq_refl.

Example slave_alone_keeps_old_master :
  peers_masters (change_propagation tree_transfer 3 false PropSlave)
  = [(None, None); (None, Some 7); (None, Some 7)] := eq_refl.

(** While the group has another member its slaves stay with it.  Made
    slaves one after another, the last member ends the group and every
    slave of it, the earlier members too, is left with no master. *)
Definition tree_group : list Mount :=
  [mnt 1 None false;
   mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags false false (Some 8) None;
   mkMount 4 1 (Some 1) 10 20 30 no_flags no_flags false false (Some 8) None;
   mkMount 5 1 (Some 1) 10 20 30 no_flags no_flags false false None (Some 8)].

Example private_member_leaves_slaves :
  peers_masters (change_propagation tree_group 2 false PropPrivate)
  = [(None, None); (None, None); (Some 8, None); (None, Some 8)] := eq_refl.

Example slave_whole_group_ends_propagation :
  peers_masters (change_propagation tree_group 1 true PropSlave)
  = [(None, None); (None, None); (None, None); (None, None)] := eq_refl.

(** A change to private clears the unbindable mark; a change to slave keeps
    it. *)
Definition unbindable_bits (r : MResult) : list bool :=
  match r with MOk t => map mnt_unbindable t | MErr _ => [] end.

Example private_clears_unbindable :
  unbindable_bits (change_propagation tree 4 false PropPrivate)
  = [false; false; false; false] := eq_refl.

Example slave_keeps_unbindable :
  unbindable_bits (change_propagation tree 4 false PropSlave)
  = [false; false; false; true] := eq_refl.

(** [pivot_root]: mount 3 sits on the task's root mount 2 and becomes the
    new root; the old root goes on put_old, dentry 40 of mount 3.  [plain]
    says what the path walk found: the new root's dentry is linked, and the
    task's root and the new root are each the root of their mount. *)
Definition plain : PivotPaths := mkPivotPaths false true true.

Definition parents (r : MResult) : list (option positive) :=
  match r with MOk t => map mnt_parent t | MErr _ => [] end.

Definition mountpoints (r : MResult) : list positive :=
  match r with MOk t => map mnt_mountpoint t | MErr _ => [] end.

Example pivot_moves_new_root_up :
  parents (pivot_root tree 1 2 3 3 40 plain) = [None; Some 3; Some 1; Some 2] := eq_refl.

Example pivot_sets_mountpoints :
  mountpoints (pivot_root tree 1 2 3 3 40 plain) = [10; 40; 10; 10] := eq_refl.

(** The new root being the old root is refused with EBUSY. *)
Example pivot_same_mount_busy : pivot_root tree 1 2 2 2 40 plain = MErr 16%Z := eq_refl.

(** put_old outside the new root is refused with EINVAL. *)
Example pivot_put_old_outside : pivot_root tree 1 2 3 4 40 plain = MErr 22%Z := eq_refl.

(** The absolute root, which has no parent, cannot be pivoted away. *)
Example pivot_absolute_root : pivot_root tree 1 1 2 2 40 plain = MErr 22%Z := eq_refl.

(** A locked new root is refused with EINVAL. *)
Definition tree_locked_new : list Mount :=
  [mnt 1 None false; mnt 2 (Some 1) false;
   mkMount 3 1 (Some 2) 10 20 30 no_flags no_flags true false None None].

Example pivot_locked_new_root :
  pivot_root tree_locked_new 1 2 3 3 40 plain = MErr 22%Z := eq_refl.

(** A locked old root passes its lock to the new root. *)
Definition tree_locked_root : list Mount :=
  [mnt 1 None false;
   mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags true false None None;
   mnt 3 (Some 2) false].

Example pivot_moves_lock :
  match pivot_root tree_locked_root 1 2 3 3 40 plain with
  | MOk t => map mnt_locked t
  | MErr _ => []
  end = [false; false; true] := eq_refl.

(** A shared mount where the pivot attaches or detaches is refused: here the
    parent of the task's root. *)
Definition tree_shared_parent : list Mount :=
  [mkMount 1 1 None 10 20 30 no_flags no_flags false false (Some 8) None;
   mnt 2 (Some 1) false; mnt 3 (Some 2) false].

Example pivot_shared_parent_refused :
  pivot_root tree_shared_parent 1 2 3 3 40 plain = MErr 22%Z := eq_refl.

(** A root with no parent counts as its own parent: when it is shared, the
    shared check refuses the call before the EBUSY check. *)
Example pivot_shared_absolute_root :
  pivot_root tree_shared_parent 1 1 1 2 40 plain = MErr 22%Z := eq_refl.

(** A mount of another namespace is refused with EINVAL. *)
Example pivot_other_namespace : pivot_root tree 5 2 3 3 40 plain = MErr 22%Z := eq_refl.

(** The checks on the paths run between the kernel's checks on the mounts:
    an unlinked new root gives ENOENT after the lock check and before the
    EBUSY check; a task root or new root that is not the root of its mount
    gives EINVAL after the EBUSY check. *)
Example pivot_unlinked_before_busy :
  pivot_root tree 1 2 2 2 40 (mkPivotPaths true true true) = MErr 2%Z := eq_refl.

Example pivot_locked_before_unlinked :
  pivot_root tree_locked_new 1 2 3 3 40 (mkPivotPaths true true true) = MErr 22%Z := eq_refl.

Example pivot_root_not_mount_root :
  pivot_root tree 1 2 3 3 40 (mkPivotPaths false false true) = MErr 22%Z := eq_refl.

Example pivot_busy_before_not_mount_root :
  pivot_root tree 1 2 2 2 40 (mkPivotPaths false false false) = MErr 16%Z := eq_refl.

Example pivot_new_not_mount_root :
  pivot_root tree 1 2 3 3 40 (mkPivotPaths false true false) = MErr 22%Z := eq_refl.

(** [copy_mnt_ns]: a new mount namespace copies every mount of the old
    one, in pre-order, unbindable ones included and none of the copies
    unbindable.  Mount 2 is read-only, mount 3 unbindable, mount 4 shared
    in group 8. *)
Definition tree_ns_copy : list Mount :=
  [mnt 1 None false;
   mkMount 2 1 (Some 1) 10 20 30 ro_only no_flags false false None None;
   mnt 3 (Some 2) true;
   mkMount 4 1 (Some 1) 11 20 30 no_flags no_flags false false (Some 8) None].

Definition copied_part (r : list Mount * (positive -> positive)) : list Mount := skipn 4 (fst r).

Example ns_copy_ids : map mnt_id (copied_part (copy_mnt_ns tree_ns_copy 1 2 true)) = [5; 6; 7; 8]
  := eq_refl.
Example ns_copy_parents :
  map mnt_parent (copied_part (copy_mnt_ns tree_ns_copy 1 2 true)) = [None; Some 5; Some 6; Some 5]
  := eq_refl.
Example ns_copy_namespace :
  map mnt_ns (copied_part (copy_mnt_ns tree_ns_copy 1 2 true)) = [2; 2; 2; 2] := eq_refl.
Example ns_copy_not_unbindable :
  map mnt_unbindable (copied_part (copy_mnt_ns tree_ns_copy 1 2 true)) = [false; false; false; false]
  := eq_refl.

(** Into another user namespace: the copies are slaves of the originals'
    peer groups, every copy but the root is MNT_LOCKED, and each flag a
    copy carries is locked ([lock_mnt_tree]). *)
Example ns_copy_slave :
  map (fun m => (mnt_peer m, mnt_master m)) (copied_part (copy_mnt_ns tree_ns_copy 1 2 true))
  = [(None, None); (None, None); (None, None); (None, Some 8)] := eq_refl.
Example ns_copy_locked :
  map mnt_locked (copied_part (copy_mnt_ns tree_ns_copy 1 2 true)) = [false; true; true; true]
  := eq_refl.
Example ns_copy_locks_flags :
  map (fun m => mf_ro (mnt_lock_flags m)) (copied_part (copy_mnt_ns tree_ns_copy 1 2 true))
  = [false; true; false; false] := eq_refl.

(** In the same user namespace: the copies join the originals' peer
    groups and nothing is locked. *)
Example ns_copy_peers :
  map (fun m => (mnt_peer m, mnt_master m)) (copied_part (copy_mnt_ns tree_ns_copy 1 2 false))
  = [(None, None); (None, None); (None, None); (Some 8, None)] := eq_refl.
Example ns_copy_unlocked :
  map mnt_locked (copied_part (copy_mnt_ns tree_ns_copy 1 2 false)) = [false; false; false; false]
  := eq_refl.

(** A task's root and cwd move to the copies of their mounts. *)
Example ns_copy_maps_mounts :
  map (snd (copy_mnt_ns tree_ns_copy 1 2 true)) [1; 2; 3; 4; 9] = [5; 6; 7; 8; 9] := eq_refl.
