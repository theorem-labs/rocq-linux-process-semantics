(** * LinuxProcessSem.Checks.Cases.Ns.MountArmsCases — mount namespace call arms

    The world has a host root, a tmpfs mounted at /tmp, one submount below
    /tmp/src and one beside it.  The examples run the four namespace call
    arms by computation. *)

From Stdlib Require Import ZArith List Bool NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Mount Propagation Userns Walk Task Files MountArms.
Import ListNotations.
Open Scope Z_scope.

Definition bytes (zs : list Z) : list byte := map (Z_to_bv 8) zs.

Definition no_flags : MountFlags := mkMountFlags false false false false.
Definition readonly_flags : MountFlags := mkMountFlags true true true false.

Definition mnt (i : positive) (parent : option positive) (point root sb : positive)
    (locked unbindable : bool) : Mount :=
  mkMount i 1 parent point root sb no_flags no_flags locked unbindable None None.

Definition sb (i root : positive) (k : SbKind) : SuperBlock :=
  mkSb i k 1 root false 0 false false false.

Definition dir (i : positive) : Inode := mkInode i IDir 511 0 0 0 [] false.
Definition dent (i s : positive) (parent : option positive) (name : list byte) (ino : positive)
    : Dentry := mkDentry i s parent name ino.

Definition user0 : UserNs := mkUserNs 1 None 0 0 None None true false INT_MAX true.
Definition caps_none : CapSets := mkCaps 0 0 0 0 0.
Definition caps_admin : CapSets := mkCaps (2 ^ CAP_SYS_ADMIN) 0 0 0 0.

Definition state (unbindable locked : bool) (files : list (N * NsFile)) : NsState :=
  let st := with_mounts empty_nsstate
    [mnt 1 None 1 1 1 false false;
     mnt 2 (Some 1%positive) 2 20 2 locked unbindable;
     mnt 3 (Some 2%positive) 22 30 3 false false;
     mnt 4 (Some 2%positive) 23 40 4 false false] in
  let st := with_userns st [user0] in
  let st := with_mntns st [mk_mntns 1 1 1 false] in
  let st := with_pidns st [mkPidNs 1 None 1 0 0] in
  let st := with_sbs st [sb 1 1 SbHost; sb 2 20 SbTmpfs; sb 3 30 SbTmpfs; sb 4 40 SbTmpfs] in
  let st := with_tree st
    [dent 1 1 None [] 1;
     dent 2 1 (Some 1%positive) (bytes [116; 109; 112]) 2;
     dent 3 1 (Some 1%positive) (bytes [98; 105; 110; 100]) 3;
     dent 20 2 None [] 20;
     dent 21 2 (Some 20%positive) (bytes [115; 114; 99]) 21;
     dent 22 2 (Some 21%positive) (bytes [117; 110; 100; 101; 114]) 22;
     dent 23 2 (Some 20%positive) (bytes [111; 116; 104; 101; 114]) 23;
     dent 30 3 None [] 30;
     dent 40 4 None [] 40]
    [dir 1; dir 2; dir 3; dir 20; dir 21; dir 22; dir 23; dir 30; dir 40] in
  with_files st files.

Definition ctx (caps : CapSets) (root cwd : positive * positive) : NsCtx :=
  with_cwd (with_root (with_caps (with_pids init_nsctx [(1%positive, 1%Z)]) caps) root) cwd.
Definition c_admin : NsCtx := ctx caps_admin (1%positive, 1%positive) (1%positive, 1%positive).
Definition c_none : NsCtx := ctx caps_none (1%positive, 1%positive) (1%positive, 1%positive).
Definition c_pivot : NsCtx := ctx caps_admin (2%positive, 20%positive) (3%positive, 30%positive).
Definition c_pivot_same : NsCtx := ctx caps_admin (2%positive, 20%positive) (2%positive, 20%positive).

Definition base_model : Model :=
  init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) demo_sp demo_limit (demo_input [] IEof).

Definition model_fd (fd : Z) (h : N) : Model :=
  with_fds (fd_insert (m_fds base_model) (Z_to_bv 64 fd) (ns_fd_entry h)) base_model.

Definition byte_mem (base : Z) (bs : list byte) : word -> option byte :=
  fun a => let k := bv_unsigned a - base in
           if (0 <=? k) && (k <? Z.of_nat (length bs)) then Some (nth (Z.to_nat k) bs (Z_to_bv 8 0))
           else None.
Definition join_mem (a b : word -> option byte) : word -> option byte :=
  fun p => match a p with Some x => Some x | None => b p end.
Definition cstr (base : Z) (zs : list Z) : word -> option byte :=
  byte_mem base (bytes (zs ++ [0])).

Definition DEV : Z := 4096.
Definition PATH : Z := 8192.
Definition TYPE : Z := 12288.
Definition ATTR : Z := 16384.
Definition DATA : Z := 20480.

Definition call (n : Z) (args : list Z) (rd : word -> option byte) : SyscallInput :=
  mkInput (Z_to_bv 64 n) (map (Z_to_bv 64) args) rd (fun _ => None).

Definition mount_input (source target : list Z) (flags : Z) : SyscallInput :=
  call 40 [DEV; PATH; TYPE; flags; 0]
    (join_mem (cstr DEV source)
      (join_mem (cstr PATH target) (cstr TYPE [110; 111; 110; 101]))).
Definition mount_new_input (fstype target : list Z) (options : option (list Z)) (flags : Z) : SyscallInput :=
  let datap := match options with Some _ => DATA | None => 0 end in
  call 40 [DEV; PATH; TYPE; flags; datap]
    (join_mem (cstr DEV [110; 111; 110; 101])
      (join_mem (cstr PATH target)
        (join_mem (cstr TYPE fstype)
          (match options with Some data => cstr DATA data | None => fun _ => None end)))).

Definition umount_input (path : list Z) (flags : Z) : SyscallInput := call 39 [PATH; flags] (cstr PATH path).
Definition pivot_input (new_root put_old : list Z) : SyscallInput :=
  call 41 [PATH; TYPE] (join_mem (cstr PATH new_root) (cstr TYPE put_old)).

Definition attr_bytes (set_bits : Z) : list byte :=
  Z_to_le_bytes 8 set_bits ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0.
Definition setattr_input (dfd : Z) (path : list Z) (flags set_bits : Z) : SyscallInput :=
  call 442 [dfd; PATH; flags; ATTR; 32]
    (join_mem (cstr PATH path) (byte_mem ATTR (attr_bytes set_bits))).

Definition ret_of (o : ext_outcome) : option Z :=
  match o with EOk eff _ _ _ _ => Some (bv_signed (eff_ret eff)) | EUnmodeled => None end.
Definition mounts_of (o : ext_outcome) : option (list Mount) :=
  match o with EOk _ _ _ st _ => Some (ns_mounts st) | EUnmodeled => None end.
Definition root_of (o : ext_outcome) : option (positive * positive) :=
  match o with EOk _ _ c _ _ => Some (cx_root c) | EUnmodeled => None end.

Definition s_root : list Z := [47].
Definition s_tmp : list Z := [47; 116; 109; 112].
Definition s_src : list Z := [47; 116; 109; 112; 47; 115; 114; 99].
Definition s_bind : list Z := [47; 98; 105; 110; 100].
Definition s_dot : list Z := [46].
Definition t_tmpfs : list Z := [116; 109; 112; 102; 115].
Definition t_proc : list Z := [112; 114; 111; 99].
Definition t_devpts : list Z := [100; 101; 118; 112; 116; 115].
Definition t_opt_tmpfs : list Z := [109; 111; 100; 101; 61; 48; 55; 53; 53].
Definition t_opt_devpts : list Z :=
  [110; 101; 119; 105; 110; 115; 116; 97; 110; 99; 101; 44;
   112; 116; 109; 120; 109; 111; 100; 101; 61; 48; 54; 54; 54; 44;
   109; 111; 100; 101; 61; 54; 50; 48].

(** A recursive bind copies its source mount and the submount below src, not
    the sibling submount.  The old mount magic is ignored before dispatch. *)
Example mount_recursive_bind :
  option_map (map mnt_id) (mounts_of
    (mount_fn (mount_input s_src s_bind (MS_MGC_VAL + MS_BIND + MS_REC)) base_model c_admin
              (state false false []))) = Some [1%positive; 2%positive; 3%positive; 4%positive; 5%positive; 6%positive].
Proof. vm_compute. reflexivity. Qed.

(** A tmpfs instance with mode=0755 is attached to the target mount. *)
Example mount_tmpfs :
  option_map length (mounts_of
    (mount_fn (mount_new_input t_tmpfs s_bind (Some t_opt_tmpfs) (MS_NOSUID + MS_NODEV))
              base_model c_admin (state false false []))) = Some 5%nat.
Proof. vm_compute. reflexivity. Qed.

Example mount_tmpfs_arm :
  mount_arm (mount_new_input t_tmpfs s_bind (Some t_opt_tmpfs) (MS_NOSUID + MS_NODEV))
            base_model c_admin (state false false [])
            (mount_fn (mount_new_input t_tmpfs s_bind (Some t_opt_tmpfs) (MS_NOSUID + MS_NODEV))
                      base_model c_admin (state false false [])).
Proof. unfold mount_arm. left. reflexivity. Qed.

(** A procfs instance with no option bytes is attached to the target mount. *)
Example mount_proc :
  option_map length (mounts_of
    (mount_fn (mount_new_input t_proc s_bind None (MS_NOSUID + MS_NODEV + MS_NOEXEC))
              base_model c_admin (state false false []))) = Some 5%nat.
Proof. vm_compute. reflexivity. Qed.

Example mount_proc_arm :
  mount_arm (mount_new_input t_proc s_bind None (MS_NOSUID + MS_NODEV + MS_NOEXEC))
            base_model c_admin (state false false [])
            (mount_fn (mount_new_input t_proc s_bind None (MS_NOSUID + MS_NODEV + MS_NOEXEC))
                      base_model c_admin (state false false [])).
Proof. unfold mount_arm. left. reflexivity. Qed.

(** A devpts instance accepts newinstance, ptmxmode and mode options. *)
Example mount_devpts :
  option_map length (mounts_of
    (mount_fn (mount_new_input t_devpts s_bind (Some t_opt_devpts) (MS_NOSUID + MS_NOEXEC))
              base_model c_admin (state false false []))) = Some 5%nat.
Proof. vm_compute. reflexivity. Qed.

Example mount_devpts_arm :
  mount_arm (mount_new_input t_devpts s_bind (Some t_opt_devpts) (MS_NOSUID + MS_NOEXEC))
            base_model c_admin (state false false [])
            (mount_fn (mount_new_input t_devpts s_bind (Some t_opt_devpts) (MS_NOSUID + MS_NOEXEC))
                      base_model c_admin (state false false [])).
Proof. unfold mount_arm. left. reflexivity. Qed.

(** An unbindable source is refused before a recursive copy. *)
Example mount_unbindable_source :
  ret_of (mount_fn (mount_input s_src s_bind (MS_BIND + MS_REC)) base_model c_admin
                   (state true false [])) = Some (-EINVAL).
Proof. vm_compute. reflexivity. Qed.

(** A recursive slave change of the root succeeds. *)
Example mount_slave_recursive :
  ret_of (mount_fn (mount_input s_root s_root (MS_SLAVE + MS_REC)) base_model c_admin
                   (state false false [])) = Some 0.
Proof. vm_compute. reflexivity. Qed.

(** A propagation target below a mount root is refused. *)
Example mount_private_nonroot :
  ret_of (mount_fn (mount_input s_src s_src MS_PRIVATE) base_model c_admin
                   (state false false [])) = Some (-EINVAL).
Proof. vm_compute. reflexivity. Qed.

(** [do_change_type] (fs/namespace.c:2856-2887): MS_SHARED with MS_REC gives
    each mount of the subtree a new group of its own (2877-2881, 2453-2456);
    a propagation flag with another flag of the low 32 bits is EINVAL
    (2845-2846), as are two propagation flags (2848-2849); bits 32 to 63 do
    not reach the test (2856: [int ms_flags]); with no CAP_SYS_ADMIN over the
    owner of the mount's namespace, EPERM (2831-2832). *)
Example mount_shared_recursive :
  option_map (map mnt_peer) (mounts_of
    (mount_fn (mount_input s_root s_root (MS_SHARED + MS_REC)) base_model c_admin
              (state false false [])))
  = Some [Some 2%positive; Some 3%positive; Some 4%positive; Some 5%positive].
Proof. vm_compute. reflexivity. Qed.

Example mount_private_rdonly :
  ret_of (mount_fn (mount_input s_root s_root (MS_PRIVATE + MS_RDONLY)) base_model c_admin
                   (state false false [])) = Some (-EINVAL).
Proof. vm_compute. reflexivity. Qed.

Example mount_shared_slave :
  ret_of (mount_fn (mount_input s_root s_root (MS_SHARED + MS_SLAVE)) base_model c_admin
                   (state false false [])) = Some (-EINVAL).
Proof. vm_compute. reflexivity. Qed.

Example mount_private_high_bit :
  ret_of (mount_fn (mount_input s_root s_root (MS_PRIVATE + 2 ^ 40)) base_model c_admin
                   (state false false [])) = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example mount_change_no_admin :
  ret_of (mount_change_type [] (mount_input s_root s_root MS_PRIVATE) base_model c_none
                            (state false false []) 1 1 MS_PRIVATE) = Some (-EPERM).
Proof. vm_compute. reflexivity. Qed.

(** May_mount checks CAP_SYS_ADMIN over the mount namespace's owner. *)
Example mount_needs_admin :
  ret_of (mount_fn (mount_input s_src s_bind MS_BIND) base_model c_none
                   (state false false [])) = Some (-EPERM).
Proof. vm_compute. reflexivity. Qed.

(** A locked mount cannot be detached; an unlocked detach removes its subtree. *)
Example umount_locked :
  ret_of (umount2_fn (umount_input s_tmp MNT_DETACH) base_model c_admin
                     (state false true [])) = Some (-EINVAL).
Proof. vm_compute. reflexivity. Qed.

Example umount_detach :
  option_map (map mnt_id) (mounts_of
    (umount2_fn (umount_input s_tmp MNT_DETACH) base_model c_admin (state false false [])))
  = Some [1%positive].
Proof. vm_compute. reflexivity. Qed.

(** With new_root and put_old at the same directory, pivot_root moves the
    caller's old root to the new mount root. *)
Example pivot_dot_moves_root :
  root_of (pivot_root_fn (pivot_input s_dot s_dot) base_model c_pivot (state false false []))
  = Some (3%positive, 30%positive).
Proof. vm_compute. reflexivity. Qed.

(** A new root on the caller's current root mount is busy. *)
Example pivot_same_mount :
  ret_of (pivot_root_fn (pivot_input s_dot s_dot) base_model c_pivot_same (state false false []))
  = Some (-EBUSY).
Proof. vm_compute. reflexivity. Qed.

(** The call of [pivot_dot_moves_root] in a mount namespace entered from
    outside has no answer: an outside move of the new root's mount changes
    Linux's answer (fs/namespace.c:4584-4618, v6.18.46). *)
Example entered_pivot_dot_declines :
  pivot_root_fn (pivot_input s_dot s_dot) base_model c_pivot
    (with_entered_mntns (state false false []) [1%positive]) = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Definition path_file : NsFile := mkNsFile (NfPath (LDentry 2 20)) O_PATH (mkIdCred 1 0 0 0).
Definition writer_file : NsFile := mkNsFile (NfFile (LDentry 2 21) 0) O_WRONLY (mkIdCred 1 0 0 0).
Definition attr_set : Z := MOUNT_ATTR_RDONLY + MOUNT_ATTR_NOSUID + MOUNT_ATTR_NODEV.

(** An O_PATH descriptor accepts AT_EMPTY_PATH and recursively changes the
    chosen mount subtree. *)
Example setattr_opath_recursive :
  option_map (map mnt_flags) (mounts_of
    (mount_setattr_fn (setattr_input 3 [] (AT_EMPTY_PATH + AT_RECURSIVE) attr_set)
                      (model_fd 3 7%N) c_admin (state false false [(7%N, path_file)])))
  = Some [no_flags; readonly_flags; readonly_flags; readonly_flags].
Proof. vm_compute. reflexivity. Qed.

(** mount_setattr requires the target to be the root of its mount. *)
Example setattr_nonroot :
  ret_of (mount_setattr_fn (setattr_input (-100) s_src 0 attr_set) base_model c_admin
                           (state false false [])) = Some (-EINVAL).
Proof. vm_compute. reflexivity. Qed.

(** A writer on a mount being made read-only makes the change busy. *)
Example setattr_writer_busy :
  ret_of (mount_setattr_fn (setattr_input (-100) s_tmp 0 MOUNT_ATTR_RDONLY) base_model c_admin
                           (state false false [(8%N, writer_file)])) = Some (-EBUSY).
Proof. vm_compute. reflexivity. Qed.

(** [do_mount_setattr] with [attr.propagation] (fs/namespace.c:4781-4838):
    MS_SHARED with AT_RECURSIVE gives each mount of the tree a group of its
    own ([invent_group_ids], 4804-4805); flags and propagation on one mount
    are both applied ([mount_setattr_commit], 4766-4774); a change that
    clears a locked flag is EPERM ([mount_setattr_prepare], 4715-4718) and
    makes no group ([cleanup_group_ids], 4831-4833). *)
Definition attr_prop_bytes (set_bits prop : Z) : list byte :=
  Z_to_le_bytes 8 set_bits ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 prop ++ Z_to_le_bytes 8 0.
Definition setattr_prop_input (dfd : Z) (path : list Z) (flags set_bits prop : Z) : SyscallInput :=
  call 442 [dfd; PATH; flags; ATTR; 32]
    (join_mem (cstr PATH path) (byte_mem ATTR (attr_prop_bytes set_bits prop))).

Example setattr_shared_recursive :
  option_map (map mnt_peer) (mounts_of
    (mount_setattr_fn (setattr_prop_input (-100) s_tmp AT_RECURSIVE 0 MS_SHARED) base_model c_admin
                      (state false false [])))
  = Some [None; Some 2%positive; Some 3%positive; Some 4%positive].
Proof. vm_compute. reflexivity. Qed.

Example setattr_flags_and_shared :
  option_map (map (fun x => (mf_ro (mnt_flags x), mnt_peer x))) (mounts_of
    (mount_setattr_fn (setattr_prop_input (-100) s_tmp 0 MOUNT_ATTR_RDONLY MS_SHARED) base_model c_admin
                      (state false false [])))
  = Some [(false, None); (true, Some 2%positive); (false, None); (false, None)].
Proof. vm_compute. reflexivity. Qed.

Definition ro_locked_state : NsState :=
  let st := state false false [] in
  with_mounts st (map (fun x => if Pos.eqb (mnt_id x) 2 then mnt_with_lock_flags x (mkMountFlags true false false false)
                                else x) (ns_mounts st)).

Example setattr_shared_locked :
  ret_of (mount_setattr_apply [] (mkAttr no_flags (mkMountFlags true false false false)) (Some PShared)
                              false base_model c_admin ro_locked_state 2 20) = Some (-EPERM)
  /\ option_map (map mnt_peer) (mounts_of
       (mount_setattr_apply [] (mkAttr no_flags (mkMountFlags true false false false)) (Some PShared)
                            false base_model c_admin ro_locked_state 2 20))
     = Some [None; None; None; None].
Proof. split; vm_compute; reflexivity. Qed.

(** Open groups ([Propagation.targets_open]).  Mount 1, the root, is the
    only member of peer group 9 that the tables hold, with no master, and
    group 9 is open: it has a member outside the tables.  MS_SLAVE|MS_REC
    on "/" makes the root a slave of that member and leaves group 9's
    slaves with the group ([change_mnt_propagation], fs/pnode.c:101-116),
    which the tables cannot name: no answer.  The walk of "/" crosses no
    mount, so the test is the arm's.  With no open group the root is the
    last member of group 9 and becomes private ([Mount.change_one]). *)
Definition st_root9 : NsState :=
  let st := state false false [] in
  with_mounts st (map (fun x => if Pos.eqb (mnt_id x) 1 then mnt_with_peer x (Some 9%positive) else x)
                      (ns_mounts st)).

Example change_type_open_root :
  ret_of (mount_fn (mount_input s_root s_root (MS_SLAVE + MS_REC)) base_model c_admin
                   (with_open_groups st_root9 [9%positive])) = None
  /\ option_map (map (fun x => (mnt_peer x, mnt_master x)))
       (mounts_of (mount_fn (mount_input s_root s_root (MS_SLAVE + MS_REC)) base_model c_admin st_root9))
     = Some [(None, None); (None, None); (None, None); (None, None)].
Proof. split; vm_compute; reflexivity. Qed.

(** Mount 3, below /tmp/src, is in the open group 9; /tmp (mount 2) is in
    no group.  A recursive change of /tmp, by [mount] with MS_REC or by
    [mount_setattr] with AT_RECURSIVE, reaches mount 3: no answer.  The
    same change without MS_REC or AT_RECURSIVE changes mount 2 alone and
    answers 0. *)
Definition st_sub9 : NsState :=
  let st := state false false [] in
  with_open_groups
    (with_mounts st (map (fun x => if Pos.eqb (mnt_id x) 3 then mnt_with_peer x (Some 9%positive) else x)
                         (ns_mounts st)))
    [9%positive].

Example change_type_open_descendant :
  ret_of (mount_fn (mount_input s_tmp s_tmp (MS_PRIVATE + MS_REC)) base_model c_admin st_sub9) = None
  /\ ret_of (mount_fn (mount_input s_tmp s_tmp MS_PRIVATE) base_model c_admin st_sub9) = Some 0.
Proof. split; vm_compute; reflexivity. Qed.

Example setattr_open_descendant :
  ret_of (mount_setattr_fn (setattr_prop_input (-100) s_tmp AT_RECURSIVE 0 MS_PRIVATE) base_model c_admin
                           st_sub9) = None
  /\ ret_of (mount_setattr_fn (setattr_prop_input (-100) s_tmp 0 0 MS_PRIVATE) base_model c_admin
                              st_sub9) = Some 0.
Proof. split; vm_compute; reflexivity. Qed.

(** AT_EMPTY_PATH starts at the descriptor's mount and crosses no mount:
    with /tmp (mount 2) in the open group 9, a change of its flags has no
    answer; with no open group it answers 0. *)
Definition st_tmp9 : NsState :=
  let st := state false false [(7%N, path_file)] in
  with_mounts st (map (fun x => if Pos.eqb (mnt_id x) 2 then mnt_with_peer x (Some 9%positive) else x)
                      (ns_mounts st)).

Example setattr_empty_path_open :
  ret_of (mount_setattr_fn (setattr_input 3 [] AT_EMPTY_PATH attr_set) (model_fd 3 7%N) c_admin
                           (with_open_groups st_tmp9 [9%positive])) = None
  /\ ret_of (mount_setattr_fn (setattr_input 3 [] AT_EMPTY_PATH attr_set) (model_fd 3 7%N) c_admin
                              st_tmp9) = Some 0.
Proof. split; vm_compute; reflexivity. Qed.

(** A slave outside the selected tree.  Mount 3 (/tmp/src/under) is the
    only member of peer group 9, which is not open, with no master; mount
    4 (/tmp/other), beside it, is a slave of group 9 and the only member
    of peer group 11.  MS_PRIVATE on /tmp/src/under ends group 9 and hands
    mount 4 to mount 3's master, none ([transfer_propagation],
    fs/pnode.c:74-88): the change reads and sets mount 4's master, with or
    without MS_REC.  With group 11 open, mount 4 can receive an event from
    outside the tables, so neither [mount] nor [mount_setattr] has an
    answer ([Propagation.change_reads]); a change of the flags alone does
    not read mount 4 and answers 0.  With no open group both calls answer
    0, and mount 4 keeps group 11 with no master. *)
Definition s_under : list Z := [47; 116; 109; 112; 47; 115; 114; 99; 47; 117; 110; 100; 101; 114].

Definition st_slave9 : NsState :=
  let st := state false false [] in
  with_mounts st (map (fun x => if Pos.eqb (mnt_id x) 3 then mnt_with_peer x (Some 9%positive)
                                else if Pos.eqb (mnt_id x) 4
                                then mnt_with_master (mnt_with_peer x (Some 11%positive)) (Some 9%positive)
                                else x)
                      (ns_mounts st)).

Example change_type_open_slave :
  prop_okb (with_open_groups st_slave9 [11%positive]) = true
  /\ ret_of (mount_fn (mount_input s_under s_under MS_PRIVATE) base_model c_admin
                      (with_open_groups st_slave9 [11%positive])) = None
  /\ ret_of (mount_fn (mount_input s_under s_under (MS_PRIVATE + MS_REC)) base_model c_admin
                      (with_open_groups st_slave9 [11%positive])) = None
  /\ option_map (map (fun x => (mnt_peer x, mnt_master x)))
       (mounts_of (mount_fn (mount_input s_under s_under MS_PRIVATE) base_model c_admin st_slave9))
     = Some [(None, None); (None, None); (None, None); (Some 11%positive, None)].
Proof. vm_compute. repeat split; reflexivity. Qed.

Example setattr_open_slave :
  ret_of (mount_setattr_fn (setattr_prop_input (-100) s_under 0 0 MS_PRIVATE) base_model c_admin
                           (with_open_groups st_slave9 [11%positive])) = None
  /\ ret_of (mount_setattr_fn (setattr_input (-100) s_under 0 attr_set) base_model c_admin
                              (with_open_groups st_slave9 [11%positive])) = Some 0
  /\ option_map (map (fun x => (mnt_peer x, mnt_master x)))
       (mounts_of (mount_setattr_fn (setattr_prop_input (-100) s_under 0 0 MS_PRIVATE) base_model
                                    c_admin st_slave9))
     = Some [(None, None); (None, None); (None, None); (Some 11%positive, None)].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** [mount_setattr_prepare]'s EPERM (fs/namespace.c:4716-4718) reads the
    selected tree alone, and [mount_setattr_commit], which would hand
    mount 4 over, does not run (4824-4826).  With mount 3's read-only flag
    locked, MS_PRIVATE that clears it answers EPERM with group 11 open, as
    with no open group. *)
Definition st_slave9_locked : NsState :=
  with_mounts st_slave9
    (map (fun x => if Pos.eqb (mnt_id x) 3 then mnt_with_lock_flags x (mkMountFlags true false false false)
                   else x)
         (ns_mounts st_slave9)).

Example setattr_open_slave_eperm :
  ret_of (mount_setattr_apply [] (mkAttr no_flags (mkMountFlags true false false false)) (Some PPrivate)
                              false base_model c_admin (with_open_groups st_slave9_locked [11%positive]) 3 30)
  = Some (-EPERM)
  /\ ret_of (mount_setattr_apply [] (mkAttr no_flags (mkMountFlags true false false false)) (Some PPrivate)
                                 false base_model c_admin st_slave9_locked 3 30)
     = Some (-EPERM).
Proof. split; vm_compute; reflexivity. Qed.

(** With no open group no mount is open, so both arms answer as they did
    before the test ([Propagation.targets_open_closed]). *)
Example targets_open_default :
  env_open_groups (ns_env (state false false [])) = []
  /\ targets_open (state false false []) (Some PPrivate) 1 true = false
  /\ targets_open (state false false []) None 1 true = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Only the entered list is nonempty; private targets reached through a
    descriptor must not bypass the topology guard. *)
Example entered_private_setattr_declines :
  mount_setattr_fn (setattr_input 3 [] AT_EMPTY_PATH attr_set) (model_fd 3 7%N) c_admin
    (with_entered_mntns (state false false [(7%N, path_file)]) [1%positive]) = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example entered_private_propagation_declines :
  mount_fn (mount_input s_root s_root MS_PRIVATE) base_model c_admin
    (with_entered_mntns (state false false []) [1%positive]) = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example both_uncertainty_lists_default :
  (env_open_groups (ns_env (state false false [])),
   env_entered_mntns (ns_env (state false false []))) = ([], []).
Proof. reflexivity. Qed.

(** With only an entered receiver, the selected mount is closed. A
    propagation change still reads the receiver through change_type_reads. *)
Definition st_entered_slave : NsState :=
  with_entered_mntns
    (with_mounts st_slave9
      (map (fun x => if Pos.eqb (mnt_id x) 4 then mnt_with_ns x 2 else x)
           (ns_mounts st_slave9))) [2%positive].

Example entered_slave_change_reads :
  (open_mount st_entered_slave 3, targets_open st_entered_slave None 3 false,
   targets_open st_entered_slave (Some PPrivate) 3 false) = (false, false, true)
  /\ mount_fn (mount_input s_under s_under MS_PRIVATE) base_model c_admin st_entered_slave
     = EUnmodeled
  /\ mount_setattr_fn (setattr_prop_input (-100) s_under 0 0 MS_PRIVATE)
       base_model c_admin st_entered_slave = EUnmodeled.
Proof. repeat split; vm_compute; reflexivity. Qed.

Print Assumptions entered_private_setattr_declines.
Print Assumptions entered_private_propagation_declines.
Print Assumptions entered_slave_change_reads.
Print Assumptions both_uncertainty_lists_default.

(** Row 442 admits the group-id allocator's ENOSPC, and still satisfies
    the rule of a row ([Arm.ni_forced_ok]). *)
Example mount442_row :
  ni_errno mount442_injected ENOSPC = true /\ ni_errno mount442_injected ENOMEM = true
  /\ ni_forced_ok mount442_injected = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** can_umount checks may_mount before the path's mount-root check. *)
Example umount_needs_admin_first :
  ret_of (umount2_fn (umount_input s_src MNT_DETACH) base_model c_none
                     (state false false [])) = Some (-EPERM).
Proof. vm_compute. reflexivity. Qed.

(** umount2's int flags discard the high half before selecting MNT_DETACH. *)
Example umount_flags_are_u32 :
  option_map (map mnt_id) (mounts_of
    (umount2_fn (umount_input s_tmp (4294967296 + MNT_DETACH)) base_model c_admin
                (state false false []))) = Some [1%positive].
Proof. vm_compute. reflexivity. Qed.

(** mount_setattr's unsigned-int flags discard the high half too. *)
Example setattr_flags_are_u32 :
  ret_of (mount_setattr_fn (setattr_input (-100) s_tmp (4294967296 + AT_RECURSIVE) 0)
                          base_model c_admin (state false false [])) = Some 0.
Proof. vm_compute. reflexivity. Qed.

(** may_mount precedes copy_struct_from_user, so an unprivileged caller
    gets EPERM without a user-memory fault. *)
Example setattr_permission_precedes_copy :
  ret_of (mount_setattr_fn
    (call 442 [-100; PATH; 0; 9223372036854775808; 32] (cstr PATH s_tmp))
    base_model c_none (state false false [])) = Some (-EPERM).
Proof. vm_compute. reflexivity. Qed.

(** The size tests come before may_mount (fs/namespace.c:4973-4979, Linux
    v6.18.46): an unprivileged caller with a size above PAGE_SIZE gets
    E2BIG, and one with a size below MOUNT_ATTR_SIZE_VER0 gets EINVAL.
    Before this correction the model answered EPERM to both. *)
Example setattr_size_too_big_precedes_permission :
  ret_of (mount_setattr_fn
    (call 442 [-100; PATH; 0; 9223372036854775808; 5000] (cstr PATH s_tmp))
    base_model c_none (state false false [])) = Some (-E2BIG).
Proof. vm_compute. reflexivity. Qed.

Example setattr_size_too_small_precedes_permission :
  ret_of (mount_setattr_fn
    (call 442 [-100; PATH; 0; 9223372036854775808; 16] (cstr PATH s_tmp))
    base_model c_none (state false false [])) = Some (-EINVAL).
Proof. vm_compute. reflexivity. Qed.

(** At the boundary the size passes and may_mount answers. *)
Example setattr_size_page_then_permission :
  ret_of (mount_setattr_fn
    (call 442 [-100; PATH; 0; 9223372036854775808; 4096] (cstr PATH s_tmp))
    base_model c_none (state false false [])) = Some (-EPERM).
Proof. vm_compute. reflexivity. Qed.

(** copy_mount_options distinguishes its first unreadable byte from a
    later partial copy. *)
Example mount_options_first_fault :
  copy_mount_options (call 40 [0; 0; 0; 0; DATA] (fun _ => None)) (Z_to_bv 64 DATA)
  = MOErr [(Z_to_bv 64 DATA, 1%nat)] EFAULT.
Proof. vm_compute. reflexivity. Qed.

(** Every mount arm exports its environment refusals: the walk's ENOMEM
    and EIO, and for mount also a new instance's ENOSPC and EMFILE; ENOSPC
    is also the tables' answer at the mount limit ([ni_forced]).  EPERM and
    EINVAL, the tables' answers, are no refusal. *)
Example mount_injected_rows :
  map ni_no mount_injected = [40; 39; 41; 442]
  /\ map ni_forced mount_injected = [[ENOSPC]; []; []; []]
  /\ ni_errno mount40_injected EMFILE = true /\ ni_errno mount40_injected EIO = true
  /\ ni_errno mount40_injected EPERM = false /\ ni_errno mount40_injected EINVAL = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example mount_arm_numbers : map fst mount_arms = [39; 40; 41; 442].
Proof. vm_compute. reflexivity. Qed.
