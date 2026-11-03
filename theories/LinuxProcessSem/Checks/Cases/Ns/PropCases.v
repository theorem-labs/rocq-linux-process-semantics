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
