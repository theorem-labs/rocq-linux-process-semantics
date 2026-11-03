(** * LinuxProcessSem.Checks.Cases.Ns.UmountPropCases — MNT_DETACH unmounts that propagate

    The world of [PropagateCases]: mount namespace 1 has its root mount 1,
    /tmp (mount 2, peer group 7) and /src (mount 3); mount namespace 2 has
    its root mount 5 and a peer of /tmp (mount 6, group 7).  Each example
    runs [umount2(path, MNT_DETACH)] by a task of namespace 1 with
    CAP_SYS_ADMIN, by computation, and states which mounts stay, where
    they sit, and which group each slave receives from (Linux v6.18.46:
    [umount_tree] with UMOUNT_PROPAGATE, fs/namespace.c:1771-1838, from
    do_umount, 1948-1950; [propagate_mount_unlock], [propagate_umount],
    fs/pnode.c:466-687; [bulk_make_private], fs/pnode.c:126-175). *)

From Stdlib Require Import ZArith List Bool NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import
  Tables Ext Arm Mount Propagation Userns Walk MountArms.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Ns Require MountArmsCases PropagateCases.
Import ListNotations.

Open Scope Z_scope.

Definition p_mnt : list Z := [47; 109; 110; 116].              (* /mnt *)
Definition p_mnt_d : list Z := [47; 109; 110; 116; 47; 100].   (* /mnt/d *)

Open Scope positive_scope.

Definition mt := PropagateCases.mt.
Definition shared := PropagateCases.shared.
Definition slave := PropagateCases.slave.
Definition world := PropagateCases.world.
Definition m1 := PropagateCases.m1.
Definition m2 := PropagateCases.m2.
Definition m3 := PropagateCases.m3.
Definition m5 := PropagateCases.m5.
Definition m6 := PropagateCases.m6.

(** [umount2(path, MNT_DETACH)]. *)
Definition umount_out (st : NsState) (path : list Z) : ext_outcome :=
  umount2_fn (MountArmsCases.umount_input path MNT_DETACH) MountArmsCases.base_model
             MountArmsCases.c_admin st.

Definition ids_of (o : ext_outcome) : option (list positive) :=
  option_map (map mnt_id) (MountArmsCases.mounts_of o).

(** Mount [i]'s master group in the state after the call. *)
Definition master_of (i : positive) (s : NsState) : list (positive * option positive) :=
  map (fun x => (mnt_id x, mnt_master x)) (List.filter (fun x => Pos.eqb (mnt_id x) i) (ns_mounts s)).

(** A bind of /src onto /tmp/d puts mount 7 there and its secondary 8 on
    mount 6, both in group 8 ([PropagateCases.bind_onto_shared]).
    Unmounting /tmp/d removes mount 7 and, at the same place on mount 6,
    the receiver of its parent, the secondary 8 ([gather_candidates],
    fs/pnode.c:505-531).  Group 8 ends: its ring goes and its key is not
    given again. *)
Definition after_bind : NsState :=
  match PropagateCases.state_of (PropagateCases.bind_out PropagateCases.st_a PropagateCases.bind_flags) with
  | Some s => s
  | None => PropagateCases.st_a
  end.

Example umount_takes_secondary :
  PropagateCases.places (umount_out after_bind PropagateCases.p_td)
  = Some [(1, 1, None, 1, None, None); (2, 1, Some 1, 2, Some 7, None);
          (3, 1, Some 1, 3, None, None); (5, 2, None, 1, None, None);
          (6, 2, Some 5, 2, Some 7, None)]
  /\ option_map (fun s => (pl_find 8 (pl_rings (ns_prop s)), pl_next_group (ns_prop s), prop_okb s))
                (PropagateCases.state_of (umount_out after_bind PropagateCases.p_td))
     = Some (None, 9, true).
Proof. split; vm_compute; reflexivity. Qed.

(** Mount 7 on /tmp/d and mount 8 at the same place on mount 6, the peer of
    /tmp.  Mount 9 sits on mount 8 at its directory c, not on its root, so
    removing mount 8 would shift mount 9: mount 8 stays (non-shifting,
    [trim_one], fs/pnode.c:575-589), and only mount 7 goes. *)
Definition x7 : Mount := mt 7 1 (Some 2) 21 30 3.
Definition x8 : Mount := mt 8 2 (Some 6) 21 30 3.
Definition st_k : NsState := world [m1; m2; m3; m5; m6; x7; x8; mt 9 2 (Some 8) 31 40 4] 1.

Example candidate_with_child_stays :
  ids_of (umount_out st_k PropagateCases.p_td) = Some [1; 2; 3; 5; 6; 8; 9].
Proof. vm_compute. reflexivity. Qed.

(** Mount 9 sits on the root of mount 8 instead: mount 8 goes too, and
    mount 9 moves down to where mount 8 sat, on mount 6 at dentry 21
    ([reparent], fs/pnode.c:631-643, from 679-683). *)
Definition st_l : NsState := world [m1; m2; m3; m5; m6; x7; x8; mt 9 2 (Some 8) 30 40 4] 1.

Example overmount_moves_down :
  option_map (map (fun x => (mnt_id x, mnt_parent x, mnt_mountpoint x)))
             (MountArmsCases.mounts_of (umount_out st_l PropagateCases.p_td))
  = Some [(1, None, 1); (2, Some 1, 2); (3, Some 1, 3); (5, None, 1); (6, Some 5, 2);
          (9, Some 6, 21)].
Proof. vm_compute. reflexivity. Qed.

(** Mount 8 is MNT_LOCKED.  [propagate_mount_unlock] clears it before
    anything is decided (fs/pnode.c:466-479, from fs/namespace.c:1776-1777),
    so mount 8 goes with mount 7; with mount 9 inside it, mount 8 stays, and
    stays unlocked. *)
Definition x8l : Mount := mnt_with_locked x8 true.
Definition st_m : NsState := world [m1; m2; m3; m5; m6; x7; x8l] 1.
Definition st_n : NsState := world [m1; m2; m3; m5; m6; x7; x8l; mt 9 2 (Some 8) 31 40 4] 1.

Example unlock_before_decision :
  ids_of (umount_out st_m PropagateCases.p_td) = Some [1; 2; 3; 5; 6]
  /\ option_map (map (fun x => (mnt_id x, mnt_locked x)))
                (MountArmsCases.mounts_of (umount_out st_n PropagateCases.p_td))
     = Some [(1, false); (2, false); (3, false); (5, false); (6, false); (8, false); (9, false)].
Proof. split; vm_compute; reflexivity. Qed.

(** /mnt is mount 7, shared in group 9 with mount 8 in namespace 2; its
    parent, the root mount 1, is neither shared nor a slave.  Mount 10 sits
    on mount 7 at its directory c, and mount 11 at the same place on mount
    8.  The unmount gathers candidates for every mount of the subtree, so
    mount 11, at mount 10's place on a receiver of mount 10's parent, goes
    too (fs/pnode.c:505-531).  [Mount.umount_detach], the answer before the
    unmount propagated for such a parent, keeps mount 11.  When mount 11 is
    MNT_LOCKED it stays: its parent 8 stays, so removing it would reveal
    what it covers ([handle_locked], fs/pnode.c:597-616), and nothing
    unlocks it (it is not at mount 7's place). *)
Definition y7 : Mount := shared 9 (mt 7 1 (Some 1) 4 30 3).
Definition y8 : Mount := shared 9 (mt 8 2 (Some 5) 4 30 3).
Definition y10 : Mount := mt 10 1 (Some 7) 31 40 4.
Definition y11 : Mount := mt 11 2 (Some 8) 31 40 4.
Definition st_o : NsState := world [m1; m2; m3; m5; m6; y7; y8; y10; y11] 1.
Definition st_p : NsState := world [m1; m2; m3; m5; m6; y7; y8; y10; mnt_with_locked y11 true] 1.

Example inner_peer_child_goes :
  ids_of (umount_out st_o p_mnt) = Some [1; 2; 3; 5; 6; 8]
  /\ match umount_detach (ns_mounts st_o) 7 with MOk T => map mnt_id T | MErr _ => [] end
     = [1; 2; 3; 5; 6; 8; 11].
Proof. split; vm_compute; reflexivity. Qed.

Example locked_candidate_stays :
  ids_of (umount_out st_p p_mnt) = Some [1; 2; 3; 5; 6; 8; 11].
Proof. vm_compute. reflexivity. Qed.

(** Mount 10, in namespace 2, is a slave of group 9, on the slave list of
    mount 7.  Unmounting /mnt removes mount 7; group 9 keeps mount 8, so
    mount 10 stays a slave of group 9, now on mount 8's list
    ([trace_transfers], fs/pnode.c:129-134, 144-145; [transfer_propagation],
    74-88).  The order data forgets the lists of group 9's members, and
    the one possible list of mount 8 is still known. *)
Definition s10 : Mount := slave 9 (mt 10 2 (Some 5) 3 40 4).
Definition st_q : NsState :=
  with_ns_prop (world [m1; m2; m3; m5; m6; y7; y8; s10] 1)
               (pl_with_slaves empty_prop [(7, [10]); (8, [])]).

Example slave_keeps_group :
  option_map (fun s => (master_of 10 s, pl_slaves (ns_prop s), slave_list s 8, prop_okb s))
             (PropagateCases.state_of (umount_out st_q p_mnt))
  = Some ([(10, Some 9)], [], Some [10], true).
Proof. vm_compute. reflexivity. Qed.

(** Mount 7 is the only member of group 9 and a slave of group 7; mount 10
    is a slave of group 9.  Unmounting /mnt ends group 9, and mount 10
    becomes a slave of group 7, the master group of the dead group
    ([trace_transfers], fs/pnode.c:135-139, 144-145; [bulk_make_private],
    162-175).  [Mount.umount_detach] left it a slave of the dead group.
    With no master above group 9, mount 10 receives from nothing. *)
Definition st_r : NsState := world [m1; m2; m3; m5; m6; slave 7 y7; s10] 1.
Definition st_s : NsState := world [m1; m2; m3; m5; m6; y7; s10] 1.

Example slave_of_last_member :
  option_map (fun s => (master_of 10 s, pl_next_group (ns_prop s), prop_okb s))
             (PropagateCases.state_of (umount_out st_r p_mnt))
  = Some ([(10, Some 7)], 10, true)
  /\ match umount_detach (ns_mounts st_r) 7 with MOk T => map (fun x => (mnt_id x, mnt_master x))
                                                              (List.filter (fun x => Pos.eqb (mnt_id x) 10) T)
                                             | MErr _ => [] end
     = [(10, Some 9)]
  /\ option_map (master_of 10) (PropagateCases.state_of (umount_out st_s p_mnt)) = Some [(10, None)].
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(** The two answers above changed for states the model could reach before
    the unmount propagated.  A launch's tables are a parameter
    ([ProcsIface.sh_nsstate]), and a mount's peer group and master group
    are launch values ([Tables.mnt_peer], [Tables.mnt_master]) that no
    premise restricts, so a start state can hold shared mounts and slaves,
    as [st_o] and [st_r] do under the default launch (no open group, every
    rule of [prop_ok]).  On both, the arm then answered (the parent of /mnt
    is neither shared nor a slave, so [Mount.umount_propagates] did not
    stop it) with [Mount.umount_detach]'s table, the old answers stated
    in [inner_peer_child_goes] and [slave_of_last_member]. *)
Example old_arm_answered :
  (env_open_groups (ns_env st_o), prop_okb st_o, umount_propagates (ns_mounts st_o) y7)
  = ([], true, false)
  /\ (env_open_groups (ns_env st_r), prop_okb st_r, umount_propagates (ns_mounts st_r) (slave 7 y7))
     = ([], true, false).
Proof. split; vm_compute; reflexivity. Qed.

(** /mnt/d is mount 7 on mount 4, a slave of group 7 that is not shared:
    mount 4 has no peer and no slave, so no other mount goes
    (fs/pnode.c:177-212).  Before, the arm had no answer for a parent that
    is a slave ([Mount.umount_propagates]). *)
Definition st_u : NsState :=
  world [m1; m2; m3; slave 7 (mt 4 1 (Some 1) 4 20 2); m5; m6; mt 7 1 (Some 4) 21 30 3] 1.

Example slave_parent :
  ids_of (umount_out st_u p_mnt_d) = Some [1; 2; 3; 4; 5; 6]
  /\ umount_propagates (ns_mounts st_u) (mt 7 1 (Some 4) 21 30 3) = true.
Proof. split; vm_compute; reflexivity. Qed.

(** Mount 10, in group 9, sits inside the tree of /mnt.  With group 9 open
    the host can mount or unmount on mount 10 at any time, so the unmount
    has no answer ([umount_detach_prop]); with no open group it removes
    mounts 7 and 10. *)
Definition st_t : NsState :=
  world [m1; m2; m3; m5; m6; mt 7 1 (Some 1) 4 30 3; shared 9 (mt 10 1 (Some 7) 31 40 4)] 1.

Example umount_tree_holds_open_group :
  ids_of (umount_out st_t p_mnt) = Some [1; 2; 3; 5; 6]
  /\ umount_out (with_open_groups st_t [9]) p_mnt = EUnmodeled.
Proof. split; vm_compute; reflexivity. Qed.
