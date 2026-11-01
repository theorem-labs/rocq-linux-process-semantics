(** * LinuxProcessSem.Checks.Cases.Ns.FsOpsCases — namespace file operations

    Each example computes one [Ns.FsOps] operation over a small tmpfs and
    procfs namespace. *)

From Stdlib Require Import ZArith List Bool NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Mount Userns Walk Task Files FsOps.
Import ListNotations.
Open Scope Z_scope.

Definition bytes (zs : list Z) : list byte := map (Z_to_bv 8) zs.
Definition no_flags : MountFlags := mkMountFlags false false false false.
Definition root_user : UserNs := mkUserNs 1 None 0 0 None None true false INT_MAX true.
Definition root_dir : Inode := mkInode 1 IDir 511 1000 1002 0 [] false.
Definition base_state : NsState :=
  mkNsState [mkMount 1 1 None 1 1 1 no_flags no_flags false false None None]
    [root_user] [mkMntNs 1 1 1 false] [mkPidNs 1 None 1 0 0] []
    [mkSb 1 SbTmpfs 1 1 false 16914836 false false false]
    [mkDentry 1 1 None [] 1] [root_dir] [] (ns_env empty_nsstate).
Definition base_ctx : NsCtx :=
  mkNsCtx 1 1 1 1 [(1%positive, 42%Z)] (1%positive, 1%positive) (1%positive, 1%positive)
    18 (mkCaps 0 0 0 0 0) 0 [] false 0 1.
Definition base_model : Model :=
  init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) demo_sp demo_limit (demo_input [] IEof).
Definition PATH : Z := 8192.
Definition BUF : Z := 16384.
Definition at_ (base : Z) (bs : list Z) : word -> option byte :=
  fun a => let k := bv_unsigned a - base in
           if (0 <=? k) && (k <? Z.of_nat (length bs)) then Some (Z_to_bv 8 (nth (Z.to_nat k) bs 0))
           else None.
Definition path_mem (p : list Z) : word -> option byte := at_ PATH (p ++ [0]).
Definition wmem (n : nat) : word -> option byte := at_ BUF (repeat 0 n).
Definition call (n : Z) (args : list Z) (rd wr : word -> option byte) : SyscallInput :=
  mkInput (Z_to_bv 64 n) (map (Z_to_bv 64) args) rd wr.
Definition ret_of (o : ext_outcome) : option Z :=
  match o with EOk eff _ _ _ _ => Some (bv_signed (eff_ret eff)) | EUnmodeled => None end.
Definition newest_dir (o : ext_outcome) : option (Z * Z * Z * Z) :=
  match o with
  | EOk _ _ _ s _ => match rev (ns_inodes s) with
                      | ino :: _ => Some (Zpos (ino_id ino), ino_perm ino, ino_uid ino, ino_gid ino)
                      | [] => None
                      end
  | EUnmodeled => None
  end.
Definition s_new : list Z := [47; 110; 101; 119].

(** mkdirat creates a tmpfs directory with umask-filtered mode and fsuid/fsgid ownership. *)
Example mkdirat_tmpfs_mode_owner :
  ret_of (mkdirat_fn (call 34 [-100; PATH; 511] (path_mem s_new) (fun _ => None))
                    base_model base_ctx base_state) = Some 0
  /\ newest_dir (mkdirat_fn (call 34 [-100; PATH; 511] (path_mem s_new) (fun _ => None))
                          base_model base_ctx base_state) = Some (2, 493, 1000, 1002).
Proof. split; vm_compute; reflexivity. Qed.

Definition ro_flags : MountFlags := mkMountFlags true false false false.
Definition existing_ro_state : NsState :=
  mkNsState [mkMount 1 1 None 1 1 1 ro_flags no_flags false false None None]
    [root_user] [mkMntNs 1 1 1 false] [mkPidNs 1 None 1 0 0] []
    [mkSb 1 SbTmpfs 1 1 false 16914836 false false false]
    [mkDentry 1 1 None [] 1; mkDentry 2 1 (Some 1%positive) (bytes [101; 120; 105; 115; 116; 115]) 2]
    [root_dir; mkInode 2 IReg 420 1000 1002 0 [] false] [] (ns_env empty_nsstate).
Definition proc_state : NsState :=
  mkNsState [mkMount 1 1 None 1 1 1 no_flags no_flags false false None None]
    [root_user] [mkMntNs 1 1 1 false] [mkPidNs 1 None 1 0 0] []
    [mkSb 1 (SbProc 1) 1 1 false 40864 true true true]
    [mkDentry 1 1 None [] 1] [mkInode 1 IDir 365 0 0 0 [] false] [] (ns_env empty_nsstate).
Definition s_exists : list Z := [47; 101; 120; 105; 115; 116; 115].
Definition s_missing_parent : list Z := [47; 110; 111; 47; 110; 101; 119].
Definition s_link : list Z := [47; 108; 105; 110; 107].
Definition target_fd0 : list Z := [47; 112; 114; 111; 99; 47; 115; 101; 108; 102; 47; 102; 100; 47; 48].

(** A positive dentry is reported before the deferred read-only failure. *)
Example mkdirat_existing_before_readonly :
  ret_of (mkdirat_fn (call 34 [-100; PATH; 511] (path_mem s_exists) (fun _ => None))
                    base_model base_ctx existing_ro_state) = Some (-17).
Proof. vm_compute. reflexivity. Qed.

(** procfs has no mkdir operation, so vfs_mkdir returns EPERM. *)
Example mkdirat_procfs_eperm :
  ret_of (mkdirat_fn (call 34 [-100; PATH; 511] (path_mem s_new) (fun _ => None))
                    base_model base_ctx proc_state) = Some (-1).
Proof. vm_compute. reflexivity. Qed.

(** The parent walk fails before creation for a missing directory. *)
Example mkdirat_missing_parent :
  ret_of (mkdirat_fn (call 34 [-100; PATH; 511] (path_mem s_missing_parent) (fun _ => None))
                    base_model base_ctx base_state) = Some (-2).
Proof. vm_compute. reflexivity. Qed.

Definition newest_link (o : ext_outcome) : option (Z * list Z) :=
  match o with
  | EOk _ _ _ s _ =>
      match rev (ns_inodes s) with
      | ino :: _ => match ino_kind ino with
                    | ILnk => Some (ino_perm ino, map bv_unsigned (ino_bytes ino))
                    | _ => None
                    end
      | [] => None
      end
  | EUnmodeled => None
  end.

Definition symlink_in : SyscallInput :=
  call 36 [PATH; -100; PATH + 128]
       (fun a => match at_ PATH (target_fd0 ++ [0]) a with
                 | Some b => Some b | None => at_ (PATH + 128) (s_link ++ [0]) a
                 end)
       (fun _ => None).

(** symlinkat stores its target bytes on a new tmpfs symbolic link. *)
Example symlinkat_tmpfs_target :
  ret_of (symlinkat_fn symlink_in base_model base_ctx base_state) = Some 0
  /\ newest_link (symlinkat_fn symlink_in base_model base_ctx base_state) = Some (511, target_fd0).
Proof. split; vm_compute; reflexivity. Qed.

Definition identity_map : list IdExtent := [mkExtent 0 0 4294967296].
Definition map_root : UserNs := mkUserNs 1 None 0 0 (Some identity_map) (Some identity_map) true false INT_MAX true.
Definition map_child : UserNs := mkUserNs 2 (Some 1%positive) 1 1000 None None true false INT_MAX true.
Definition mapped_child : UserNs :=
  mkUserNs 2 (Some 1%positive) 1 1000 (Some [mkExtent 0 65534 1]) None true false INT_MAX true.
Definition map_state (users : list UserNs) : NsState :=
  mkNsState [] users [] [] [] [] [] [] [] (ns_env empty_nsstate).
Definition map_caps : CapSets := mkCaps (2 ^ 7 + 2 ^ 21) (2 ^ 7 + 2 ^ 21) 0 0 0.
Definition map_ctx : NsCtx :=
  mkNsCtx 1 1 1 1 [] (1%positive, 1%positive) (1%positive, 1%positive) 18 map_caps 0 [] false 0 1.
Definition map_cred : IdCred := mkIdCred 1 1000 1002 (2 ^ 7 + 2 ^ 21).
Definition uid_loc : Loc := LProcTask 1 42 [bytes [117; 105; 100; 95; 109; 97; 112]].
Definition groups_loc : Loc := LProcTask 1 42 [bytes [115; 101; 116; 103; 114; 111; 117; 112; 115]].
Definition uid_file : NsFile := mkNsFile (NfUserNsFile uid_loc 2 0) 1 map_cred.
Definition groups_file : NsFile := mkNsFile (NfUserNsFile groups_loc 2 0) 1 map_cred.
Definition uid_line : list Z := [48; 32; 54; 53; 53; 51; 52; 32; 49; 10].
Definition deny_line : list Z := [100; 101; 110; 121; 10].
Definition write_in (bs : list Z) : SyscallInput :=
  call 64 [3; BUF; Z.of_nat (length bs)] (at_ BUF bs) (fun _ => None).
Definition uid_map_of (o : ext_outcome) : option (option (list IdExtent)) :=
  match o with
  | EOk _ _ _ st _ => option_map uns_uid_map (find_userns (ns_userns st) 2)
  | EUnmodeled => None
  end.
Definition groups_of (o : ext_outcome) : option bool :=
  match o with
  | EOk _ _ _ st _ => option_map uns_setgroups_allowed (find_userns (ns_userns st) 2)
  | EUnmodeled => None
  end.

(** proc_uid_map_write installs the first permitted one-line map. *)
Example write_uid_map_installs :
  ret_of (write_fn (write_in uid_line) base_model map_ctx (map_state [map_root; map_child]) 1%N uid_file)
    = Some 10
  /\ uid_map_of (write_fn (write_in uid_line) base_model map_ctx (map_state [map_root; map_child])
                           1%N uid_file) = Some (Some [mkExtent 0 65534 1]).
Proof. split; vm_compute; reflexivity. Qed.

(** A second uid map write is refused after the map has been installed. *)
Example write_uid_map_once :
  ret_of (write_fn (write_in uid_line) base_model map_ctx (map_state [map_root; mapped_child]) 1%N uid_file)
  = Some (-1).
Proof. vm_compute. reflexivity. Qed.

(** proc_setgroups_write accepts deny before the gid map exists. *)
Example write_setgroups_deny :
  ret_of (write_fn (write_in deny_line) base_model map_ctx (map_state [map_root; map_child]) 1%N groups_file)
    = Some 5
  /\ groups_of (write_fn (write_in deny_line) base_model map_ctx (map_state [map_root; map_child])
                         1%N groups_file) = Some false.
Proof. split; vm_compute; reflexivity. Qed.

Definition sys_state : NsState :=
  mkNsState [mkMount 2 1 None 1 1 2 no_flags no_flags false false None None]
    [map_root; map_child] [mkMntNs 1 1 2 false] [] []
    [mkSb 2 (SbProc 1) 1 1 false 40864 true true true]
    [mkDentry 1 2 None [] 1;
     mkDentry 2 2 (Some 1%positive) (bytes [115; 121; 115]) 2;
     mkDentry 3 2 (Some 2%positive) (bytes [117; 115; 101; 114]) 3;
     mkDentry 4 2 (Some 3%positive)
       (bytes [109; 97; 120; 95; 117; 115; 101; 114; 95; 110; 97; 109; 101; 115; 112; 97; 99; 101; 115]) 4]
    [mkInode 1 IDir 365 0 0 0 [] false; mkInode 2 IDir 365 0 0 0 [] false;
     mkInode 3 IDir 365 0 0 0 [] false; mkInode 4 IReg 420 0 0 0 [] false]
    [] (ns_env empty_nsstate).
Definition resource_caps : CapSets := mkCaps (2 ^ 24) (2 ^ 24) 0 0 0.
Definition resource_ctx : NsCtx :=
  mkNsCtx 1 2 1 1 [] (2%positive, 1%positive) (2%positive, 1%positive) 18 resource_caps 0 [] false 0 1.
Definition sys_file : NsFile := mkNsFile (NfUserNsFile (LDentry 2 4) 2 0) 1 (mkIdCred 1 1000 1002 (2 ^ 24)).
Definition limit_of (o : ext_outcome) : option Z :=
  match o with
  | EOk _ _ _ st _ => option_map uns_max_userns (find_userns (ns_userns st) 2)
  | EUnmodeled => None
  end.

(** proc_doulongvec_minmax parses the decimal limit and advances the offset. *)
Example write_max_user_namespaces :
  ret_of (write_fn (write_in [49]) base_model resource_ctx sys_state 1%N sys_file) = Some 1
  /\ limit_of (write_fn (write_in [49]) base_model resource_ctx sys_state 1%N sys_file) = Some 1.
Proof. split; vm_compute; reflexivity. Qed.

Definition writes_of (o : ext_outcome) : option (list (Z * list Z)) :=
  match o with
  | EOk eff _ _ _ _ => Some (map (fun p => (bv_unsigned (fst p), map bv_unsigned (snd p))) (eff_writes eff))
  | EUnmodeled => None
  end.
Definition read_in (count : Z) : SyscallInput := call 63 [3; BUF; count] (fun _ => None) (wmem 128).
Definition uid_reader : NsFile := mkNsFile (NfUserNsFile uid_loc 2 0) 0 map_cred.
Definition groups_reader : NsFile := mkNsFile (NfUserNsFile groups_loc 2 0) 0 map_cred.
Definition uid_render : list Z :=
  repeat 32 9 ++ [48; 32] ++ repeat 32 5 ++ [54; 53; 53; 51; 52; 32]
  ++ repeat 32 9 ++ [49; 10].

(** seq_file rendering exposes the installed uid map and the denied setgroups state. *)
Example read_uid_map :
  writes_of (read_fn (read_in 64) base_model map_ctx (map_state [map_root; mapped_child]) 1%N uid_reader)
  = Some [(BUF, uid_render)].
Proof. vm_compute. reflexivity. Qed.

Example read_setgroups :
  writes_of (read_fn (read_in 64) base_model map_ctx
                      (map_state [map_root;
                        mkUserNs 2 (Some 1%positive) 1 1000 None None false false INT_MAX true])
                      1%N groups_reader)
  = Some [(BUF, deny_line)].
Proof. vm_compute. reflexivity. Qed.

Definition file_state : NsState :=
  mkNsState (ns_mounts base_state) (ns_userns base_state) (ns_mntns base_state) (ns_pidns base_state)
    (ns_netns base_state) (ns_sbs base_state)
    [mkDentry 1 1 None [] 1; mkDentry 2 1 (Some 1%positive) (bytes [102]) 2]
    [root_dir; mkInode 2 IReg 420 1000 1002 0 (bytes [97; 98; 99; 100]) false]
    [] (ns_env base_state).
Definition offset_file : NsFile := mkNsFile (NfFile (LDentry 1 2) 2) 0 (mkIdCred 1 1000 1002 0).

(** A regular tmpfs read starts at the shared open-file offset. *)
Example read_tmpfs_offset :
  writes_of (read_fn (read_in 8) base_model base_ctx file_state 1%N offset_file) = Some [(BUF, [99; 100])]
  /\ ret_of (read_fn (read_in 8) base_model base_ctx file_state 1%N offset_file) = Some 2.
Proof. split; vm_compute; reflexivity. Qed.

(** eventfd_read rejects a buffer smaller than its eight-byte counter. *)
Example read_eventfd_short_buffer :
  eventfd_read_arm (read_in 4) base_model base_ctx base_state (Z_to_bv 64 0)
                   (ns_errno EINVAL base_model base_ctx base_state).
Proof. vm_compute. reflexivity. Qed.

(** vfs_write rejects an O_RDONLY open file before it reads the source buffer. *)
Example write_readonly_file_ebadf :
  ret_of (write_fn (write_in [120]) base_model base_ctx file_state 1%N offset_file) = Some (-9).
Proof. vm_compute. reflexivity. Qed.

(** The false EEXIST answer is rejected by computation. *)
Example mkdirat_wrong_return_rejected : True.
Proof.
  Fail assert
    (ret_of (mkdirat_fn (call 34 [-100; PATH; 511] (path_mem s_new) (fun _ => None))
                       base_model base_ctx base_state) = Some (-17))
    by (vm_compute; reflexivity).
  exact I.
Qed.
