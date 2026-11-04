(** * LinuxProcessSem.Checks.Cases.Ns.PropagateCases — binds and new mounts onto a shared mount

    Mount namespace 1 has its root mount 1, a tmpfs at /tmp (mount 2, peer
    group 7) and another tmpfs at /src (mount 3); mount namespace 2 has its
    root mount 5 and a peer of /tmp (mount 6, group 7).  Each example runs
    [mount(2)] (or the function it names) by computation and states which
    secondary mounts the call makes, with their groups and the order data
    (Linux v6.18.46: [propagate_mnt], fs/pnode.c:311-366;
    [attach_recursive_mnt], fs/namespace.c:2559-2673). *)

From Stdlib Require Import ZArith List Bool NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import
  Tables Ext Arm Mount Propagation Userns Walk Clone Files MountArms.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Ns Require MountArmsCases CloneCases.
Import ListNotations.

Open Scope Z_scope.

Definition p_src : list Z := [47; 115; 114; 99].            (* /src *)
Definition p_tmp : list Z := [47; 116; 109; 112].           (* /tmp *)
Definition p_td : list Z := [47; 116; 109; 112; 47; 100].   (* /tmp/d *)
Definition n_tmp : list byte := MountArmsCases.bytes [116; 109; 112].
Definition n_src : list byte := MountArmsCases.bytes [115; 114; 99].
Definition n_mnt : list byte := MountArmsCases.bytes [109; 110; 116].
Definition n_d : list byte := MountArmsCases.bytes [100].
Definition n_e : list byte := MountArmsCases.bytes [101].
Definition n_c : list byte := MountArmsCases.bytes [99].
Definition bind_flags : Z := MS_BIND.
Definition rbind_flags : Z := MS_BIND + MS_REC.
Definition nosuid : MountFlags := mkMountFlags false true false false.
Definition nodev : MountFlags := mkMountFlags false false true false.

Open Scope positive_scope.

(** Mount [i] of namespace [ns] on mount [parent] at dentry [mp], with
    root dentry [root] of superblock [s]. *)
Definition mt (i ns : positive) (parent : option positive) (mp root s : positive) : Mount :=
  mnt_with_ns (MountArmsCases.mnt i parent mp root s false false) ns.
Definition shared (g : positive) (x : Mount) : Mount := mnt_with_peer x (Some g).
Definition slave (g : positive) (x : Mount) : Mount := mnt_with_master x (Some g).

(** The tables around the mounts [ms]: namespace 2 owned by user namespace
    [owner2]; the host superblock 1 (/, /tmp, /src, /mnt), tmpfs 2 (its
    root 20 with the directories d and e), tmpfs 3 (its root 30 with the
    directory c) and tmpfs 4 (its root 40). *)
Definition world (ms : list Mount) (owner2 : positive) : NsState :=
  let base := MountArmsCases.state false false [] in
  let st := with_mounts empty_nsstate ms in
  let st := with_userns st (ns_userns base) in
  let st := with_mntns st [mk_mntns 1 1 1 false; mk_mntns 2 owner2 5 false] in
  let st := with_pidns st (ns_pidns base) in
  let st := with_sbs st [MountArmsCases.sb 1 1 SbHost; MountArmsCases.sb 2 20 SbTmpfs;
                         MountArmsCases.sb 3 30 SbTmpfs; MountArmsCases.sb 4 40 SbTmpfs] in
  let st := with_dentries st
    [MountArmsCases.dent 1 1 None [] 1; MountArmsCases.dent 2 1 (Some 1) n_tmp 2;
     MountArmsCases.dent 3 1 (Some 1) n_src 3; MountArmsCases.dent 4 1 (Some 1) n_mnt 4;
     MountArmsCases.dent 20 2 None [] 20; MountArmsCases.dent 21 2 (Some 20) n_d 21;
     MountArmsCases.dent 23 2 (Some 20) n_e 23; MountArmsCases.dent 30 3 None [] 30;
     MountArmsCases.dent 31 3 (Some 30) n_c 31; MountArmsCases.dent 40 4 None [] 40] in
  with_inodes st (map MountArmsCases.dir [1; 2; 3; 4; 20; 21; 23; 30; 31; 40]).

Definition m1 : Mount := mt 1 1 None 1 1 1.
Definition m2 : Mount := shared 7 (mt 2 1 (Some 1) 2 20 2).
Definition m3 : Mount := mt 3 1 (Some 1) 3 30 3.
Definition m5 : Mount := mt 5 2 None 1 1 1.
Definition m6 : Mount := shared 7 (mt 6 2 (Some 5) 2 20 2).

Definition st_a : NsState := world [m1; m2; m3; m5; m6] 1.

(** [mount("/src", "/tmp/d", flags)] by a task of namespace 1 with
    CAP_SYS_ADMIN. *)
Definition bind_out (st : NsState) (flags : Z) : ext_outcome :=
  mount_fn (MountArmsCases.mount_input p_src p_td flags) MountArmsCases.base_model
           MountArmsCases.c_admin st.

Definition state_of (o : ext_outcome) : option NsState :=
  match o with EOk _ _ _ st _ => Some st | EUnmodeled => None end.

(** Each mount's key, namespace, parent, mount point, group and master
    group. *)
Definition places (o : ext_outcome)
    : option (list (positive * positive * option positive * positive * option positive
                    * option positive)) :=
  option_map (map (fun x => (mnt_id x, mnt_ns x, mnt_parent x, mnt_mountpoint x, mnt_peer x,
                             mnt_master x)))
             (MountArmsCases.mounts_of o).

(** A bind onto /tmp/d, whose mount 2 is a peer of mount 6 in namespace 2:
    the source copy 7 gets a new group 8 ([invent_group_ids],
    fs/namespace.c:2594-2597), and mount 6 gets a secondary 8 at the same
    dentry 21, in the source's group (fs/pnode.c:322-327, 346;
    fs/namespace.c:1259-1262).  Group 8's ring is the two copies, neither
    has a slave, and no later group gets key 8. *)
Example bind_onto_shared :
  places (bind_out st_a bind_flags)
  = Some [(1, 1, None, 1, None, None); (2, 1, Some 1, 2, Some 7, None);
          (3, 1, Some 1, 3, None, None); (5, 2, None, 1, None, None);
          (6, 2, Some 5, 2, Some 7, None);
          (7, 1, Some 2, 21, Some 8, None); (8, 2, Some 6, 21, Some 8, None)]
  /\ option_map (fun s => (pl_find 8 (pl_rings (ns_prop s)), pl_find 8 (pl_slaves (ns_prop s)),
                           pl_next_group (ns_prop s), prop_okb s))
                (state_of (bind_out st_a bind_flags))
     = Some (Some [7; 8], Some [], 9, true).
Proof. split; vm_compute; reflexivity. Qed.

(** Mount 4, a slave of group 7 on /mnt (slave list of mount 2), gets a
    secondary that is a slave of the source's group (fs/pnode.c:329-339:
    CL_SLAVE, a slave in no group gets a copy in no group), at the head of
    the slave list of the last copy made in group 7's walk, mount 8
    (find_master, fs/pnode.c:274-297; fs/namespace.c:1283-1285). *)
Definition m4s : Mount := slave 7 (mt 4 1 (Some 1) 4 20 2).
Definition st_b : NsState :=
  with_ns_prop (world [m1; m2; m3; m4s; m5; m6] 1) (pl_with_slaves empty_prop [(2, [4]); (6, [])]).

Example slave_gets_slave_secondary :
  option_map (skipn 6) (places (bind_out st_b bind_flags))
  = Some [(7, 1, Some 2, 21, Some 8, None); (8, 2, Some 6, 21, Some 8, None);
          (9, 1, Some 4, 21, None, Some 8)]
  /\ option_map (fun s => (pl_find 8 (pl_slaves (ns_prop s)), prop_okb s))
                (state_of (bind_out st_b bind_flags))
     = Some (Some [9], true).
Proof. split; vm_compute; reflexivity. Qed.

(** The target's namespace at its limit once the peer's secondary counts:
    mount 6 is a peer of /tmp in namespace 1 itself.  Four mounts and the
    source are 5, the limit; the secondary is a sixth (count_mounts,
    fs/pnode.c:351, fs/namespace.c:2472-2483): ENOSPC.  With a limit of 6
    the bind succeeds. *)
Definition st_c : NsState :=
  let st := world [m1; m2; m3; shared 7 (mt 6 1 (Some 1) 4 20 2)] 1 in
  with_env st (env_with_mount_max (ns_env st) 5%Z).

Example peer_secondary_over_limit :
  MountArmsCases.ret_of (bind_out st_c bind_flags) = Some (- ENOSPC)%Z
  /\ MountArmsCases.ret_of (bind_out (with_env st_c (env_with_mount_max (ns_env st_c) 6%Z)) bind_flags)
     = Some 0%Z.
Proof. split; vm_compute; reflexivity. Qed.

(** Namespace 2 belongs to user namespace 2, not to the owner of the
    caller's namespace: the secondary tree there (a recursive bind of /src,
    nosuid, with mount 9, nodev, on /src/c) has each flag it carries locked
    and MNT_LOCKED on the child, not on its root (lock_mnt_tree,
    fs/namespace.c:2412-2437, from 2637-2639).  The source copies 10 and 11
    are not locked. *)
Definition st_d : NsState :=
  world [m1; m2; mnt_with_flags m3 nosuid; m5; m6; mnt_with_flags (mt 9 1 (Some 3) 31 40 4) nodev] 2.

Definition locks_of (o : ext_outcome) : option (list (positive * bool * bool * bool)) :=
  option_map (map (fun x => (mnt_id x, mf_nosuid (mnt_lock_flags x), mf_nodev (mnt_lock_flags x),
                             mnt_locked x)))
             (MountArmsCases.mounts_of o).

Example cross_owner_secondary_locked :
  option_map (skipn 6) (locks_of (bind_out st_d rbind_flags))
  = Some [(10, false, false, false); (11, false, false, false);
          (12, true, false, false); (13, false, true, true)].
Proof. vm_compute. reflexivity. Qed.

(** A peer whose root (dentry e) does not hold the target dentry d gets no
    secondary (need_secondary, fs/pnode.c:266-267); the source copy is still
    made shared. *)
Definition st_e : NsState := world [m1; m2; m3; m5; shared 7 (mt 6 2 (Some 5) 2 23 2)] 1.

Example peer_root_misses_dentry :
  option_map (skipn 5) (places (bind_out st_e bind_flags)) = Some [(7, 1, Some 2, 21, Some 8, None)].
Proof. vm_compute. reflexivity. Qed.

(** Mount 9, MNT_LOCKED, already sits on the peer at the target dentry: it
    moves onto the secondary 11, at its root, and keeps MNT_LOCKED
    (fs/namespace.c:2640-2650). *)
Definition st_f : NsState :=
  world [m1; m2; m3; m5; m6; mnt_with_locked (mt 9 2 (Some 6) 21 40 4) true] 1.

Example overmount_moves_onto_secondary :
  option_map (fun ms => map (fun x => (mnt_id x, mnt_parent x, mnt_mountpoint x, mnt_locked x))
                            (List.filter (fun x => Pos.eqb (mnt_ns x) 2) ms))
             (MountArmsCases.mounts_of (bind_out st_f bind_flags))
  = Some [(5, None, 1, false); (6, Some 5, 2, false); (9, Some 11, 30, true); (11, Some 6, 21, false)].
Proof. vm_compute. reflexivity. Qed.

(** A new tmpfs on /tmp/d: the new mount 7 gets group 8 and mount 6 a
    secondary of it (do_add_mount, graft_tree, attach_recursive_mnt). *)
Definition tmpfs_out : ext_outcome :=
  mount_fn (MountArmsCases.mount_new_input MountArmsCases.t_tmpfs p_td None 0%Z)
           MountArmsCases.base_model MountArmsCases.c_admin st_a.

Example new_tmpfs_onto_shared :
  option_map (skipn 5) (places tmpfs_out)
  = Some [(7, 1, Some 2, 21, Some 8, None); (8, 2, Some 6, 21, Some 8, None)].
Proof. vm_compute. reflexivity. Qed.

Example new_tmpfs_onto_shared_arm :
  mount_arm (MountArmsCases.mount_new_input MountArmsCases.t_tmpfs p_td None 0%Z)
            MountArmsCases.base_model MountArmsCases.c_admin st_a tmpfs_out.
Proof. unfold mount_arm. left. reflexivity. Qed.

(** Two peers in namespace 2, mounts 6 and 8, with the ring 2, 8, 6 known:
    the walk from mount 2 makes the secondary on 8 before the one on 6
    (fs/pnode.c:340-356), and mountinfo lists them in that order.  Without
    the ring entry the order is not known and the call has no answer; the
    secondaries are the same, in another order
    ([propagate_group_level_order_free]). *)
Definition m8p : Mount := shared 7 (mt 8 2 (Some 5) 4 20 2).
Definition st_h : NsState :=
  with_ns_prop (world [m1; m2; m3; m5; m6; m8p] 1) (pl_with_rings empty_prop [(7, [2; 8; 6])]).
Definition st_i : NsState := world [m1; m2; m3; m5; m6; m8p] 1.

Example two_peers_ring_order :
  option_map (skipn 6) (places (bind_out st_h bind_flags))
  = Some [(9, 1, Some 2, 21, Some 8, None); (10, 2, Some 8, 21, Some 8, None);
          (11, 2, Some 6, 21, Some 8, None)]
  /\ option_map (fun s => (pl_find 8 (pl_rings (ns_prop s)), prop_okb s))
                (state_of (bind_out st_h bind_flags))
     = Some (Some [9; 10; 11], true).
Proof. split; vm_compute; reflexivity. Qed.

Example two_peers_unknown_order : bind_out st_i bind_flags = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example order_only_orders :
  propagate_copies st_h (dentry_below st_h) 7 2 21 = [(8, 0%nat); (6, 0%nat)]
  /\ propagate_copies st_i (dentry_below st_i) 7 2 21 = [(6, 0%nat); (8, 0%nat)].
Proof. split; vm_compute; reflexivity. Qed.

(** Open groups.  With group 7 open, a walk that enters mount 2 has no
    answer, and so the bind onto /tmp/d has none.  With the bind's own
    decline: mount 4 in namespace 2, in group 9 and a slave of group 7,
    gets a secondary; with group 9 open the host can change what it holds,
    and the arm has no answer ([attach_check]). *)
Example walk_into_open_group :
  follow_mounts (with_open_groups st_a [7]) (LDentry 1 2) = WOver
  /\ follow_mounts st_a (LDentry 1 2) = WOk (LDentry 2 20).
Proof. split; vm_compute; reflexivity. Qed.

Example target_group_open : bind_out (with_open_groups st_a [7]) bind_flags = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Definition st_j : NsState :=
  with_ns_prop (world [m1; m2; m3; slave 7 (shared 9 (mt 4 2 (Some 5) 4 20 2)); m5; m6] 1)
               (pl_with_slaves empty_prop [(2, [4]); (6, [])]).

Example tree_holds_open_group :
  MountArmsCases.ret_of (bind_out st_j bind_flags) = Some 0%Z
  /\ bind_out (with_open_groups st_j [9]) bind_flags = EUnmodeled.
Proof. split; vm_compute; reflexivity. Qed.

(** A bind of the shared /tmp onto /src, which is not shared: the copy 7
    joins group 7 right after mount 2 in its ring (fs/namespace.c:1280-1281,
    [bind_links]). *)
Definition bind_tmp_out : ext_outcome :=
  mount_fn (MountArmsCases.mount_input p_tmp p_src bind_flags) MountArmsCases.base_model
           MountArmsCases.c_admin st_a.

Example bind_shared_source :
  option_map (fun s => (pl_find 7 (pl_rings (ns_prop s)), prop_okb s)) (state_of bind_tmp_out)
  = Some (Some [2; 7; 6], true).
Proof. vm_compute. reflexivity. Qed.

(** copy_mnt_ns of namespace 1 (mounts 1, 2, 3 copied as 7, 8, 9): into a
    namespace of the same owner the copy of mount 2 is right after it in
    group 7's ring (fs/namespace.c:1280-1281); into one of another owner it
    is a slave of mount 2, at the head of its slave list (CL_SLAVE,
    fs/namespace.c:4134-4136, 1283-1285). *)
Example copy_ns_links_owner :
  pl_find 7 (pl_rings (copy_ns_links st_a 1 false)) = Some [2; 8; 6]
  /\ pl_find 2 (pl_slaves (copy_ns_links st_a 1 true)) = Some [8].
Proof. split; vm_compute; reflexivity. Qed.

(** The same through clone(CLONE_NEWNS) by a task of user namespace 2 whose
    mount namespace 1 belongs to user namespace 2: mounts 2 and 6 of group
    7 are copied as 8 and 9, each right after its original. *)
Definition clone_world : NsState :=
  let st := with_mounts empty_nsstate [m1; m2; shared 7 (mt 6 1 (Some 1) 4 20 2)] in
  let st := with_userns st (ns_userns CloneCases.inside) in
  let st := with_mntns st [mk_mntns 1 2 1 false] in
  let st := with_pidns st (ns_pidns CloneCases.inside) in
  with_netns st (ns_netns CloneCases.inside).

Example clone_newns_copy_after_original : forall m,
  option_map (fun s => pl_find 7 (pl_rings (ns_prop s)))
    (CloneCases.st_of (clone_ns_exact (Z.lor CLONE_NEWNS CloneCases.SIGCHLD)
                                      (with_creds (CloneCases.creds 65534) m) CloneCases.shell
                                      clone_world 140))
  = Some (Some [2; 8; 6; 9]).
Proof. intros m. vm_compute. reflexivity. Qed.

(** An outside task can change even private mounts of namespace 1. No
    outside peer group is needed for this uncertainty. *)
Definition entered_a : NsState := with_entered_mntns st_a [1].

Eval vm_compute in (env_open_groups (ns_env entered_a),
                    open_mount entered_a 1, ns_open entered_a 1,
                    targets_open entered_a (Some PPrivate) 1 false,
                    MountArmsCases.ret_of (bind_out entered_a bind_flags)).

Example entered_bind_declines : bind_out entered_a bind_flags = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example entered_private_mount_and_namespace :
  (open_mount entered_a 1, ns_open entered_a 1,
   targets_open entered_a (Some PPrivate) 1 false,
   ns_top_open entered_a m1) = (true, true, true, true).
Proof. vm_compute. reflexivity. Qed.

(** Private A can be put into B's shared group through SET_GROUP: its
    superblock, not only its current peer field, exposes B's group. *)
Definition set_group_world (same_sb : bool) : NsState :=
  with_entered_mntns
    (world [m1; mt 2 1 (Some 1) 2 20 2; m5;
            shared 11 (mt 6 2 (Some 5) 2 20 (if same_sb then 2 else 3))] 1) [1].

Example entered_set_group_source_uncertainty :
  (open_reach (set_group_world true) (shared 11 (mt 6 2 (Some 5) 2 20 2)),
   is_open (set_group_world true) 11,
   open_mount (set_group_world true) 6,
   open_mount (set_group_world false) 6) = (true, true, true, false).
Proof. vm_compute. reflexivity. Qed.

Example entered_group_rejects_ring :
  prop_okb (with_ns_prop (set_group_world true)
                         (pl_with_rings empty_prop [(11, [6])])) = false.
Proof. vm_compute. reflexivity. Qed.

Definition anonymous (id : positive) (origin : option positive) : MntNs :=
  mntns_with_origin (mntns_with_anon (mk_mntns id 1 id false) true) origin.

(** Add the anonymous records AFTER choosing the launch environment. *)
Definition anonymous_world (entered : list positive) : NsState :=
  let st := with_entered_mntns (world [m1; m5] 1) entered in
  let st := with_mntns st (ns_mntns st ++
              [anonymous 3 (Some 1); anonymous 4 (Some 2); anonymous 7 None]) in
  with_mounts st (ns_mounts st ++ [mt 3 3 None 30 30 3;
                                  mt 4 4 None 40 40 4; mt 7 7 None 20 20 2]).

Example anonymous_origin_controls :
  map (open_mount (anonymous_world [1])) [3; 4; 7] = [true; false; true]
  /\ map (open_mount (anonymous_world [2])) [3; 4; 7] = [false; true; true]
  /\ map (open_mount (anonymous_world [9])) [3; 4; 7] = [false; false; true]
  /\ map (open_mount (anonymous_world [])) [3; 4; 7] = [false; false; false].
Proof. repeat split; vm_compute; reflexivity. Qed.

Example clone_entered_namespace_copy : forall m,
  option_map (fun s => (env_entered_mntns (ns_env s),
                        open_mount s 7, open_mount s 8,
                        pl_find 7 (pl_rings (ns_prop s))))
    (CloneCases.st_of (clone_ns_exact (Z.lor CLONE_NEWNS CloneCases.SIGCHLD)
          (with_creds (CloneCases.creds 65534) m) CloneCases.shell
          (with_entered_mntns clone_world [1]) 140))
  = Some ([2; 1], true, true, None).
Proof. intros m. vm_compute. reflexivity. Qed.

Example clone_preserves_other_uncertainty : forall m,
  option_map (fun s => (env_entered_mntns (ns_env s), open_mount s 8))
    (CloneCases.st_of (clone_ns_exact (Z.lor CLONE_NEWNS CloneCases.SIGCHLD)
          (with_creds (CloneCases.creds 65534) m) CloneCases.shell
          (with_open_groups (with_entered_mntns clone_world [9]) [7]) 140))
  = Some ([9], true).
Proof. intros m. vm_compute. reflexivity. Qed.

Print Assumptions entered_bind_declines.
Print Assumptions anonymous_origin_controls.
Print Assumptions clone_entered_namespace_copy.

Example entered_list_survives_environment_setters : forall e,
  map env_entered_mntns
    [env_with_mount_max e 12; env_with_proc_entries e [];
     env_with_net_fallback e []; env_with_mountinfo e default_mi_env;
     env_with_nl_link_max e 42; env_with_host_absent e [];
     env_with_foreign_pgroups e true; env_with_open_groups e [9];
     env_with_overflow_ids e None]
  = repeat (env_entered_mntns e) 9.
Proof. reflexivity. Qed.

Example anonymous_setters_preserve_other_facts : forall n,
  (mntns_id (mntns_with_anon n true), mntns_owner (mntns_with_anon n true),
   mntns_root (mntns_with_anon n true), mntns_released (mntns_with_anon n true),
   mntns_origin (mntns_with_anon n true))
  = (mntns_id n, mntns_owner n, mntns_root n, mntns_released n, mntns_origin n)
  /\ (mntns_id (mntns_with_origin n (Some 9)), mntns_owner (mntns_with_origin n (Some 9)),
      mntns_root (mntns_with_origin n (Some 9)), mntns_released (mntns_with_origin n (Some 9)),
      mntns_anon (mntns_with_origin n (Some 9)))
     = (mntns_id n, mntns_owner n, mntns_root n, mntns_released n, mntns_anon n).
Proof. split; reflexivity. Qed.

(** The launch list precedes the anonymous tree and a possible host
    attachment on its "d" child. A held descriptor must not make the
    old topology an exact answer. A normal component crosses mounts;
    "." does not (Linux v6.18.46, fs/namei.c:2096-2157). *)
Definition anonymous_fd_world (entered : list positive) (attached : bool) : NsState :=
  let st := anonymous_world entered in
  let st := if attached then with_mounts st (ns_mounts st ++ [mt 8 7 (Some 7) 21 30 3])
            else st in
  with_files st [(7%N, mkNsFile (NfPath (LDentry 7 20)) O_PATH (mkIdCred 1 0 0 0))].

Example anonymous_fd_host_attachment_declines : forall attached,
  walk_from (MountArmsCases.model_fd 3 7%N) MountArmsCases.c_admin
    (anonymous_fd_world [9] attached) (walk_creds MountArmsCases.base_model)
    3 n_d
    (mkWalkFlags true false false false false) = (WOver, false).
Proof. intros []; vm_compute; reflexivity. Qed.

Example anonymous_fd_closed_controls :
  walk_from (MountArmsCases.model_fd 3 7%N) MountArmsCases.c_admin
    (anonymous_fd_world [] false) (walk_creds MountArmsCases.base_model)
    3 n_d
    (mkWalkFlags true false false false false) = (WOk (LDentry 7 21), false)
  /\ walk_from (MountArmsCases.model_fd 3 7%N) MountArmsCases.c_admin
    (anonymous_fd_world [] true) (walk_creds MountArmsCases.base_model)
    3 n_d
    (mkWalkFlags true false false false false) = (WOk (LDentry 8 30), false).
Proof. split; vm_compute; reflexivity. Qed.

Print Assumptions closed_no_outside_event.
Print Assumptions targets_open_closed.
Print Assumptions ns_top_open_closed.
Print Assumptions prop_okb_ok.
Print Assumptions entered_list_survives_environment_setters.
Print Assumptions anonymous_setters_preserve_other_facts.
Print Assumptions anonymous_fd_host_attachment_declines.
Print Assumptions entered_set_group_source_uncertainty.
Print Assumptions entered_group_rejects_ring.
Print Assumptions clone_preserves_other_uncertainty.
Print Assumptions entered_private_mount_and_namespace.
Print Assumptions anonymous_fd_closed_controls.
