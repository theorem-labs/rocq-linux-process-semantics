(** * LinuxProcessSem.Checks.Cases.Ns.UsernsCases — user namespaces and id maps

    Each example runs one operation of [Ns.Userns] and states its exact
    result: an id mapped through one extent, the extent rules a map write
    must pass, and the namespace a creation makes or the errno it gives. *)

From Stdlib Require Import List PArith ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Userns.
Import ListNotations.
Open Scope Z_scope.

Example map_one_extent : map_id [mkExtent 0 1000 1] 0 = Some 1000 := eq_refl.
Example map_outside_extent : map_id [mkExtent 0 1000 1] 1 = None := eq_refl.
Example map_second_extent : map_id [mkExtent 0 1000 1; mkExtent 5 2000 3] 6 = Some 2001 := eq_refl.

Example extents_ok_one : map_extents_ok [mkExtent 0 1000 1] = true := eq_refl.
Example extents_overlap_first_refused :
  map_extents_ok [mkExtent 0 1000 2; mkExtent 1 2000 1] = false := eq_refl.
Example extents_overlap_lower_refused :
  map_extents_ok [mkExtent 0 1000 2; mkExtent 5 1001 1] = false := eq_refl.
Example extents_zero_count_refused : map_extents_ok [mkExtent 0 1000 0] = false := eq_refl.
Example extents_empty_refused : map_extents_ok [] = false := eq_refl.

Definition full : list IdExtent := [mkExtent 0 0 4294967295].

Definition root_ns : UserNs := mkUserNs 1%positive None 0%nat 0 (Some full) (Some full) true.

Definition level_of (r : NsResult (positive * list UserNs)) : option nat :=
  match r with
  | NsOk (i, u) => option_map uns_level (find_userns u i)
  | NsErr _ => None
  end.

(** A new user namespace is one level below its parent and has no maps yet. *)
Example create_child_level : level_of (create_user_ns [root_ns] 1%positive 1000) = Some 1%nat := eq_refl.

Example create_child_unmapped :
  match create_user_ns [root_ns] 1%positive 1000 with
  | NsOk (i, u) => option_map uns_uid_map (find_userns u i)
  | NsErr _ => None
  end = Some None := eq_refl.

(** A parent at level 33 can have no child: ENOSPC. *)
Definition deep : UserNs := mkUserNs 1%positive None 33%nat 0 None None true.
Example create_too_deep : create_user_ns [deep] 1%positive 1000 = NsErr 28 := eq_refl.

(** A parent at level 32 still can. *)
Definition level32 : UserNs := mkUserNs 1%positive None 32%nat 0 None None true.
Example create_at_level_32 : level_of (create_user_ns [level32] 1%positive 1000) = Some 33%nat := eq_refl.

Example create_missing_parent : create_user_ns [root_ns] 2%positive 1000 = NsErr 22 := eq_refl.

(** A child copies the parent's setgroups state. *)
Definition denied : UserNs := mkUserNs 1%positive None 0%nat 0 None None false.
Example create_inherits_setgroups_deny :
  match create_user_ns [denied] 1%positive 1000 with
  | NsOk (i, u) => option_map uns_setgroups_allowed (find_userns u i)
  | NsErr _ => None
  end = Some false := eq_refl.
