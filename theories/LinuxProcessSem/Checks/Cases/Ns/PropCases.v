(** * LinuxProcessSem.Checks.Cases.Ns.PropCases — the order data of propagation

    [Ns.Propagation.prop_okb] holds of the start state of every case of the
    namespace model; each of its rules refuses a state that breaks it; and
    [Ns.Propagation.open_reach] names the mounts an open peer group reaches. *)

From Stdlib Require Import List PArith ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount Propagation.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Ns Require
  CloneCases FilesCases FsOpsCases MountArmsCases MountCases MountinfoCases NetCases
  NewMountCases SpecCases TaskCases UserArmsCases UtsCases WalkCases.
Import ListNotations.
Open Scope positive_scope.

(** The start states of the existing cases.  Each has no order data, so
    these check rules 3 and 4 on their mount tables. *)
Example clone_states :
  forallb prop_okb [CloneCases.host; CloneCases.host_rootfs; CloneCases.inside; CloneCases.deep]
  = true.
Proof. vm_compute. reflexivity. Qed.

Example files_states :
  forallb prop_okb [FilesCases.W; FilesCases.W_user_sys; FilesCases.W_dir3; FilesCases.W_fd5]
  = true.
Proof. vm_compute. reflexivity. Qed.

Example fsops_states :
  forallb prop_okb
    [FsOpsCases.base_state; FsOpsCases.existing_ro_state; FsOpsCases.proc_state;
     FsOpsCases.map_state []; FsOpsCases.sys_state; FsOpsCases.file_state;
     FsOpsCases.unlink_state 511 0 0 [];
     FsOpsCases.unlink_state 511 1000 1002
       [MountCases.mnt 2 (Some 1) false];
     FsOpsCases.edge_state; FsOpsCases.sys_open_state; FsOpsCases.sysw;
     FsOpsCases.opened_state]
  = true.
Proof. vm_compute. reflexivity. Qed.

Example mount_arms_states :
  forallb prop_okb
    [MountArmsCases.state false false []; MountArmsCases.state true false [];
     MountArmsCases.state false true []]
  = true.
Proof. vm_compute. reflexivity. Qed.

Example mountinfo_state : prop_okb MountinfoCases.st = true.
Proof. vm_compute. reflexivity. Qed.

Example net_states :
  forallb prop_okb [NetCases.rcv_state; NetCases.snd_state; NetCases.up_state] = true.
Proof. vm_compute. reflexivity. Qed.

Example new_mount_states :
  forallb prop_okb
    [NewMountCases.world true false; NewMountCases.world false false;
     NewMountCases.world true true; NewMountCases.at_limit]
  = true.
Proof. vm_compute. reflexivity. Qed.

Example spec_states :
  forallb prop_okb [SpecCases.world true; SpecCases.one_mount; SpecCases.rootfs_world] = true.
Proof. vm_compute. reflexivity. Qed.

Example task_state : prop_okb TaskCases.U = true.
Proof. vm_compute. reflexivity. Qed.

Example user_arms_states :
  forallb prop_okb [UserArmsCases.w_room; UserArmsCases.w_full] = true.
Proof. vm_compute. reflexivity. Qed.

Example uts_states :
  forallb prop_okb
    [UtsCases.host; UtsCases.c_st; UtsCases.inside; UtsCases.two_mntns; UtsCases.st1]
  = true.
Proof. vm_compute. reflexivity. Qed.

Example walk_states :
  forallb prop_okb
    [WalkCases.world; WalkCases.chain_world 40; WalkCases.cap_world 1000;
     WalkCases.empty_link_world; WalkCases.absent_world]
  = true.
Proof. vm_compute. reflexivity. Qed.

(** The mount trees of [MountCases], shared and slave mounts among them. *)
Example mount_trees :
  forallb (fun T => prop_okb (with_mounts empty_nsstate T))
    [MountCases.tree; MountCases.tree_locked; MountCases.tree_sub; MountCases.tree_lk;
     MountCases.tree_lub; MountCases.tree_shared; MountCases.tree_ns;
     MountCases.tree_with_shared_parent; MountCases.tree_prop; MountCases.tree_transfer;
     MountCases.tree_group; MountCases.tree_locked_new; MountCases.tree_locked_root;
     MountCases.tree_shared_parent; MountCases.tree_ns_copy]
  = true.
Proof. vm_compute. reflexivity. Qed.

(** A small tree with order data: mount 1 is the root; mounts 2 and 3 are
    peers in group 8, ring order 3 then 2; mounts 4 and 5 are slaves of
    group 8 with master mount 2, slave list 5 then 4. *)
Definition m (i : positive) (p : option positive) : Mount := MountCases.mnt i p false.

Definition shared8 (i : positive) : Mount := mnt_with_peer (m i (Some 1)) (Some 8).
Definition slave8 (i : positive) : Mount := mnt_with_master (m i (Some 1)) (Some 8).

Definition group_tree : list Mount := [m 1 None; shared8 2; shared8 3; slave8 4; slave8 5].

Definition links : PropLinks :=
  pl_with_slaves (pl_with_rings empty_prop [(8, [3; 2])]) [(2, [5; 4])].

Definition ordered : NsState := with_ns_prop (with_mounts empty_nsstate group_tree) links.

Example ordered_ok : prop_okb ordered = true.
Proof. vm_compute. reflexivity. Qed.

(** Rule 1: a ring entry that misses a member, lists a mount of another
    group, repeats a member, or a second entry for the group. *)
Example ring_misses_member :
  prop_okb (with_ns_prop ordered (pl_with_rings links [(8, [3])])) = false.
Proof. vm_compute. reflexivity. Qed.

Example ring_lists_stranger :
  prop_okb (with_ns_prop ordered (pl_with_rings links [(8, [3; 2; 4])])) = false.
Proof. vm_compute. reflexivity. Qed.

Example ring_repeats :
  prop_okb (with_ns_prop ordered (pl_with_rings links [(8, [3; 2; 3])])) = false.
Proof. vm_compute. reflexivity. Qed.

Example ring_twice :
  prop_okb (with_ns_prop ordered (pl_with_rings links [(8, [3; 2]); (8, [2; 3])])) = false.
Proof. vm_compute. reflexivity. Qed.

(** Rule 2: a slave list of a mount that is not shared, of a slave of
    another group, or a mount in two lists. *)
Example slaves_of_private :
  prop_okb (with_ns_prop ordered (pl_with_slaves links [(4, [5])])) = false.
Proof. vm_compute. reflexivity. Qed.

Example slaves_not_slaves :
  prop_okb (with_ns_prop ordered (pl_with_slaves links [(2, [3])])) = false.
Proof. vm_compute. reflexivity. Qed.

Example slave_in_two_lists :
  prop_okb (with_ns_prop ordered (pl_with_slaves links [(2, [5; 4]); (3, [4])])) = false.
Proof. vm_compute. reflexivity. Qed.

(** Rule 3: two mounts in one group with different masters. *)
Example two_masters :
  prop_okb (with_mounts empty_nsstate
              [m 1 None; mnt_with_master (shared8 2) (Some 7); shared8 3])
  = false.
Proof. vm_compute. reflexivity. Qed.

(** Rule 4: a mount that is a slave of its own group. *)
Example own_master :
  prop_okb (with_mounts empty_nsstate [m 1 None; mnt_with_master (shared8 2) (Some 8)]) = false.
Proof. vm_compute. reflexivity. Qed.

(** Rule 5: an open group has no ring entry. *)
Example open_ring :
  prop_okb (with_open_groups ordered [8]) = false
  /\ prop_okb (with_open_groups (with_ns_prop ordered (pl_with_rings links [])) [8]) = true.
Proof. split; vm_compute; reflexivity. Qed.

(** With group 8 open, its members, its slaves and a slave of a slave
    receive host events; the root does not.  With no open group, nothing
    does. *)
Definition chain_tree : list Mount :=
  group_tree ++ [mnt_with_master (mnt_with_peer (m 6 (Some 1)) (Some 9)) (Some 8);
                 mnt_with_master (m 7 (Some 1)) (Some 9)].

Definition open8 : NsState := with_open_groups (with_mounts empty_nsstate chain_tree) [8].

Example open_reaches :
  map (open_reach open8) chain_tree = [false; true; true; true; true; true; true]
  /\ map (open_reach (with_mounts empty_nsstate chain_tree)) chain_tree
     = [false; false; false; false; false; false; false].
Proof. split; vm_compute; reflexivity. Qed.

(* =========================================================================
   Propagation types: change_mnt_propagation (fs/pnode.c:93-124)
   ========================================================================= *)

Definition flat (T : list Mount) : NsState := with_mounts empty_nsstate T.
Definition peers_of (st : NsState) : list (option positive) := map mnt_peer (ns_mounts st).
Definition masters_of (st : NsState) : list (option positive) := map mnt_master (ns_mounts st).
Definition unbindable_of (st : NsState) : list bool := map mnt_unbindable (ns_mounts st).

(** MS_SHARED on a private mount: a new group (fs/namespace.c:2454-2456),
    whose key is above every key in use, and no later group gets it. *)
Example shared_new_group :
  peers_of (change_type PShared (flat MountCases.tree) 3 false) = [None; None; Some 2; None]
  /\ pl_next_group (ns_prop (change_type PShared (flat MountCases.tree) 3 false)) = 3.
Proof. split; vm_compute; reflexivity. Qed.

(** MS_SHARED with MS_REC on the three mounts of a subtree: three groups
    (fs/namespace.c:2453); the unbindable mount 4 is no longer unbindable
    (T_SHARED_MASK, fs/pnode.h:35-36). *)
Example shared_recursive :
  peers_of (change_type PShared (flat MountCases.tree) 2 true) = [None; Some 2; Some 3; Some 4]
  /\ unbindable_of (change_type PShared (flat MountCases.tree) 2 true) = [false; false; false; false].
Proof. split; vm_compute; reflexivity. Qed.

(** MS_SHARED on a slave: shared and still a slave (fs/pnode.c:97-99). *)
Example shared_slave :
  peers_of (change_type PShared (flat MountCases.tree_transfer) 5 false) = [None; Some 9; Some 10]
  /\ masters_of (change_type PShared (flat MountCases.tree_transfer) 5 false)
     = [None; Some 7; Some 9].
Proof. split; vm_compute; reflexivity. Qed.

(** MS_UNBINDABLE on mount 2, shared with mount 3, whose slaves 5 and 4 are
    on its list: mount 2 leaves the ring, and its slaves go, in their order,
    to its next peer 3 (fs/pnode.c:104-110, 74-88), still slaves of group
    8. *)
Definition links2 : PropLinks :=
  pl_with_slaves (pl_with_rings empty_prop [(8, [3; 2])]) [(2, [5; 4]); (3, [])].
Definition ordered2 : NsState := with_ns_prop (flat group_tree) links2.
Definition unbound2 : NsState := change_type PUnbindable ordered2 2 false.

Example unbindable_peer :
  prop_okb ordered2 = true
  /\ peers_of unbound2 = [None; None; Some 8; None; None]
  /\ masters_of unbound2 = [None; None; None; Some 8; Some 8]
  /\ unbindable_of unbound2 = [false; true; false; false; false]
  /\ pl_find 3 (pl_slaves (ns_prop unbound2)) = Some [5; 4]
  /\ pl_find 2 (pl_slaves (ns_prop unbound2)) = None
  /\ pl_find 8 (pl_rings (ns_prop unbound2)) = Some [3]
  /\ prop_okb unbound2 = true.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(** MS_UNBINDABLE on mount 3, the only member of group 9 and a slave of
    mount 2 (group 7), with slave 4: group 9 ends, and slave 4 goes to
    mount 2, a slave of group 7 (fs/pnode.c:102-103, 110, 74-88); key 9 is
    not given again. *)
Definition tree_alone : list Mount :=
  [m 1 None; mnt_with_peer (m 2 (Some 1)) (Some 7);
   mnt_with_master (mnt_with_peer (m 3 (Some 1)) (Some 9)) (Some 7);
   mnt_with_master (m 4 (Some 1)) (Some 9)].
Definition unbound_alone : NsState := change_type PUnbindable (flat tree_alone) 3 false.

Example unbindable_alone :
  masters_of unbound_alone = [None; None; None; Some 7]
  /\ peers_of unbound_alone = [None; Some 7; None; None]
  /\ pl_find 2 (pl_slaves (ns_prop unbound_alone)) = Some [4]
  /\ pl_next_group (ns_prop unbound_alone) = 10
  /\ prop_okb unbound_alone = true.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(** MS_SLAVE on slave 4 of mount 2 moves it to the head of mount 2's slave
    list (fs/pnode.c:112-116). *)
Example slave_to_head :
  pl_find 2 (pl_slaves (ns_prop (change_type PSlave ordered 4 false))) = Some [4; 5]
  /\ masters_of (change_type PSlave ordered 4 false) = masters_of ordered.
Proof. split; vm_compute; reflexivity. Qed.

(** On the table, MS_SLAVE and MS_PRIVATE give [Mount.change_propagation]'s
    answer ([change_type_group_level]). *)
Example group_level_slave :
  change_propagation MountCases.tree_prop 2 true PropSlave
  = MOk (ns_mounts (change_type PSlave (flat MountCases.tree_prop) 2 true)).
Proof. vm_compute. reflexivity. Qed.
