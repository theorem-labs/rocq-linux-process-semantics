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

Definition copied (r : MResult) : list Mount :=
  match r with MOk t => skipn 4 t | MErr _ => [] end.

(** A recursive bind of mount 2 onto mount 1 at dentry 7 copies mounts 2 and
    3 as new mounts 5 and 6, and skips the unbindable mount 4. *)
Example bind_skips_unbindable :
  ids (bind_mount tree 2 true 1 7) = [1; 2; 3; 4; 5; 6] := eq_refl.

(** The copy of the bound mount sits on the target at the target dentry; the
    copy of its child sits on that copy, at the child's own mount point. *)
Example bind_relinks_parents :
  map mnt_parent (copied (bind_mount tree 2 true 1 7)) = [Some 1; Some 5] := eq_refl.

Example bind_sets_mountpoints :
  map mnt_mountpoint (copied (bind_mount tree 2 true 1 7)) = [7; 10] := eq_refl.

Example bind_copies_are_bindable :
  map mnt_unbindable (copied (bind_mount tree 2 true 1 7)) = [false; false] := eq_refl.

(** A bind that is not recursive copies the one mount. *)
Example bind_nonrecursive_one_copy :
  ids (bind_mount tree 2 false 1 7) = [1; 2; 3; 4; 5] := eq_refl.

(** A recursive bind that meets an unbindable mount that is also locked is
    refused with EPERM. *)
Definition tree_lub : list Mount :=
  [mnt 1 None false; mnt 2 (Some 1) false;
   mkMount 3 1 (Some 2) 10 20 30 no_flags no_flags true true None None].

Example bind_locked_unbindable_refused :
  bind_mount tree_lub 2 true 1 7 = MErr 1%Z := eq_refl.

(** An unbindable source is refused with EINVAL. *)
Example bind_unbindable_source_refused :
  bind_mount tree 4 true 1 7 = MErr 22%Z := eq_refl.

(** A copy of a shared mount joins its peer group. *)
Definition tree_shared : list Mount :=
  [mnt 1 None false; mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags false false (Some 8) None].

Example bind_copy_joins_peer_group :
  map mnt_peer (copied (bind_mount (tree_shared ++ [mnt 3 (Some 1) false; mnt 4 (Some 1) false])
                                   2 false 1 7))
  = [Some 8] := eq_refl.

(** A detaching unmount removes the whole subtree. *)
Example umount_detaches_subtree : ids (umount_detach tree 2) = [1] := eq_refl.

Example umount_locked_refused :
  umount_detach [mnt 1 None false; mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags true false None None] 2
  = MErr 22%Z := eq_refl.

(** Propagation changes reach the subtree with the recursive flag: a shared
    mount made a slave leaves its peer group and has it as its master; a
    mount made private has neither. *)
Definition tree_prop : list Mount :=
  [mnt 1 None false;
   mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags false false (Some 8) None;
   mkMount 3 1 (Some 2) 10 20 30 no_flags no_flags false false (Some 9) None].

Definition peers_masters (r : MResult) : list (option positive * option positive) :=
  match r with MOk t => map (fun m => (mnt_peer m, mnt_master m)) t | MErr _ => [] end.

Example make_slave_recursive :
  peers_masters (change_propagation tree_prop 2 true PropSlave)
  = [(None, None); (None, Some 8); (None, Some 9)] := eq_refl.

Example make_private_single :
  peers_masters (change_propagation tree_prop 2 false PropPrivate)
  = [(None, None); (None, None); (Some 9, None)] := eq_refl.

(** [pivot_root]: mount 3 sits on the task's root mount 2 and becomes the
    new root; the old root goes on put_old, dentry 40 of mount 3. *)
Definition parents (r : MResult) : list (option positive) :=
  match r with MOk t => map mnt_parent t | MErr _ => [] end.

Definition mountpoints (r : MResult) : list positive :=
  match r with MOk t => map mnt_mountpoint t | MErr _ => [] end.

Example pivot_moves_new_root_up :
  parents (pivot_root tree 1 2 3 3 40) = [None; Some 3; Some 1; Some 2] := eq_refl.

Example pivot_sets_mountpoints :
  mountpoints (pivot_root tree 1 2 3 3 40) = [10; 40; 10; 10] := eq_refl.

(** The new root being the old root is refused with EBUSY. *)
Example pivot_same_mount_busy : pivot_root tree 1 2 2 2 40 = MErr 16%Z := eq_refl.

(** put_old outside the new root is refused with EINVAL. *)
Example pivot_put_old_outside : pivot_root tree 1 2 3 4 40 = MErr 22%Z := eq_refl.

(** The absolute root, which has no parent, cannot be pivoted away. *)
Example pivot_absolute_root : pivot_root tree 1 1 2 2 40 = MErr 22%Z := eq_refl.

(** A locked new root is refused with EINVAL. *)
Definition tree_locked_new : list Mount :=
  [mnt 1 None false; mnt 2 (Some 1) false;
   mkMount 3 1 (Some 2) 10 20 30 no_flags no_flags true false None None].

Example pivot_locked_new_root : pivot_root tree_locked_new 1 2 3 3 40 = MErr 22%Z := eq_refl.

(** A locked old root passes its lock to the new root. *)
Definition tree_locked_root : list Mount :=
  [mnt 1 None false;
   mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags true false None None;
   mnt 3 (Some 2) false].

Example pivot_moves_lock :
  match pivot_root tree_locked_root 1 2 3 3 40 with
  | MOk t => map mnt_locked t
  | MErr _ => []
  end = [false; false; true] := eq_refl.

(** A shared mount where the pivot attaches or detaches is refused. *)
Example pivot_shared_parent_refused :
  pivot_root tree_prop 1 2 3 3 40 = MErr 22%Z := eq_refl.

(** A mount of another namespace is refused with EINVAL. *)
Example pivot_other_namespace : pivot_root tree 5 2 3 3 40 = MErr 22%Z := eq_refl.
