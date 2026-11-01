(** * LinuxProcessSem.Checks.Cases.Ns.MountArmsCases — mount namespace call arms

    The world has a host root, a tmpfs mounted at /tmp, one submount below
    /tmp/src and one beside it.  The examples run the four namespace call
    arms by computation. *)

From Stdlib Require Import ZArith List Bool NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Mount Userns Walk Task Files MountArms.
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
  mkNsState
    [mnt 1 None 1 1 1 false false;
     mnt 2 (Some 1%positive) 2 20 2 locked unbindable;
     mnt 3 (Some 2%positive) 22 30 3 false false;
     mnt 4 (Some 2%positive) 23 40 4 false false]
    [user0] [mkMntNs 1 1 1 false] [mkPidNs 1 None 1 0 0] []
    [sb 1 1 SbHost; sb 2 20 SbTmpfs; sb 3 30 SbTmpfs; sb 4 40 SbTmpfs]
    [dent 1 1 None [] 1;
     dent 2 1 (Some 1%positive) (bytes [116; 109; 112]) 2;
     dent 3 1 (Some 1%positive) (bytes [98; 105; 110; 100]) 3;
     dent 20 2 None [] 20;
     dent 21 2 (Some 20%positive) (bytes [115; 114; 99]) 21;
     dent 22 2 (Some 21%positive) (bytes [117; 110; 100; 101; 114]) 22;
     dent 23 2 (Some 20%positive) (bytes [111; 116; 104; 101; 114]) 23;
     dent 30 3 None [] 30;
     dent 40 4 None [] 40]
    [dir 1; dir 2; dir 3; dir 20; dir 21; dir 22; dir 23; dir 30; dir 40]
    files (ns_env empty_nsstate).

Definition ctx (caps : CapSets) (root cwd : positive * positive) : NsCtx :=
  mkNsCtx 1 1 1 1 [(1%positive, 1%Z)] root cwd 18 caps 0 [] false 0 1.
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

(** copy_mount_options distinguishes its first unreadable byte from a
    later partial copy. *)
Example mount_options_first_fault :
  copy_mount_options (call 40 [0; 0; 0; 0; DATA] (fun _ => None)) (Z_to_bv 64 DATA)
  = MOErr [(Z_to_bv 64 DATA, 1%nat)] EFAULT.
Proof. vm_compute. reflexivity. Qed.

(** Every mount arm exports its allocation and security environment
    refusals. *)
Example mount_injected_numbers : map ni_no mount_injected = [39; 40; 41; 442].
Proof. vm_compute. reflexivity. Qed.

Example mount_arm_numbers : map fst mount_arms = [39; 40; 41; 442].
Proof. vm_compute. reflexivity. Qed.
