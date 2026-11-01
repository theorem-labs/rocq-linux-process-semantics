(** * LinuxProcessSem.Checks.Cases.Ns.MountCases — the mount tree on small trees

    Each example runs one operation of [Ns.Mount] on a tree of four mounts
    and states its exact result: which mounts a recursive operation reaches,
    which flags change, which mounts a recursive bind copies, and the errno a
    refused operation gives.  Mount 1 is the namespace root, mount 2 sits on
    mount 1, mounts 3 and 4 sit on mount 2, and mount 4 is unbindable. *)

From Stdlib Require Import List PArith ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount.
Import ListNotations.
Open Scope positive_scope.

Definition no_flags : MountFlags := mkMountFlags false false false false.
Definition ro_only : MountFlags := mkMountFlags true false false false.

Definition mnt (i : positive) (p : option positive) (unbindable : bool) : Mount :=
  mkMount i 1 p 10 20 30 no_flags no_flags false unbindable.

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
  mkMount i 1 p 10 20 30 ro_only ro_only false false.

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
   mkMount 3 1 (Some 2) 10 20 30 no_flags no_flags true true].

Example bind_locked_unbindable_refused :
  bind_mount tree_lub 2 true 1 7 = MErr 1%Z := eq_refl.

(** An unbindable source is refused with EINVAL. *)
Example bind_unbindable_source_refused :
  bind_mount tree 4 true 1 7 = MErr 22%Z := eq_refl.

(** A detaching unmount removes the whole subtree. *)
Example umount_detaches_subtree : ids (umount_detach tree 2) = [1] := eq_refl.

Example umount_locked_refused :
  umount_detach [mnt 1 None false; mkMount 2 1 (Some 1) 10 20 30 no_flags no_flags true false] 2
  = MErr 22%Z := eq_refl.
