(** * LinuxProcessSem.Checks.Cases.Ns.FsOpsCases — namespace file operations

    Each example computes one [Ns.FsOps] operation over a small tmpfs and
    procfs namespace; the last runs an open, an unshare and a write in
    turn. *)

From Stdlib Require Import ZArith List Bool NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Mount Userns Walk Task Files Mountinfo FsOps.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require UserArms.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Ns Require FilesCases.
Import ListNotations.
Open Scope Z_scope.

Definition bytes (zs : list Z) : list byte := map (Z_to_bv 8) zs.
Definition no_flags : MountFlags := mkMountFlags false false false false.
Definition root_user : UserNs := mkUserNs 1 None 0 0 None None true false INT_MAX true.
Definition root_dir : Inode := mkInode 1 IDir 511 1000 1002 0 [] false.
(** One mount (flags [mf]) of superblock [s] in mount namespace 1, user
    namespace [root_user], pid namespace 1, and the dentries [ds] and
    inodes [ins]. *)
Definition one_sb (mf : MountFlags) (s : SuperBlock) (ds : list Dentry) (ins : list Inode) : NsState :=
  let st := with_mounts empty_nsstate [mkMount 1 1 None 1 1 1 mf no_flags false false None None] in
  let st := with_userns st [root_user] in
  let st := with_mntns st [mkMntNs 1 1 1 false] in
  let st := with_pidns st [mkPidNs 1 None 1 0 0] in
  let st := with_sbs st [s] in
  with_tree st ds ins.
Definition tmpfs_sb : SuperBlock := mkSb 1 SbTmpfs 1 1 false 16914836 false false false.
Definition base_state : NsState := one_sb no_flags tmpfs_sb [mkDentry 1 1 None [] 1] [root_dir].
Definition base_ctx : NsCtx := with_pids init_nsctx [(1%positive, 42%Z)].
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
  one_sb ro_flags tmpfs_sb
    [mkDentry 1 1 None [] 1; mkDentry 2 1 (Some 1%positive) (bytes [101; 120; 105; 115; 116; 115]) 2]
    [root_dir; mkInode 2 IReg 420 1000 1002 0 [] false].
Definition proc_state : NsState :=
  one_sb no_flags (mkSb 1 (SbProc 1) 1 1 false 40864 true true true)
    [mkDentry 1 1 None [] 1] [mkInode 1 IDir 365 0 0 0 [] false].
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
Definition map_state (users : list UserNs) : NsState := with_userns empty_nsstate users.
Definition map_caps : CapSets := mkCaps (2 ^ 7 + 2 ^ 21) (2 ^ 7 + 2 ^ 21) 0 0 0.
Definition map_ctx : NsCtx := with_caps init_nsctx map_caps.
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
  let st := with_mounts empty_nsstate [mkMount 2 1 None 1 1 2 no_flags no_flags false false None None] in
  let st := with_userns st [map_root; map_child] in
  let st := with_mntns st [mkMntNs 1 1 2 false] in
  let st := with_sbs st [mkSb 2 (SbProc 1) 1 1 false 40864 true true true] in
  with_tree st
    [mkDentry 1 2 None [] 1;
     mkDentry 2 2 (Some 1%positive) (bytes [115; 121; 115]) 2;
     mkDentry 3 2 (Some 2%positive) (bytes [117; 115; 101; 114]) 3;
     mkDentry 4 2 (Some 3%positive)
       (bytes [109; 97; 120; 95; 117; 115; 101; 114; 95; 110; 97; 109; 101; 115; 112; 97; 99; 101; 115]) 4]
    [mkInode 1 IDir 365 0 0 0 [] false; mkInode 2 IDir 365 0 0 0 [] false;
     mkInode 3 IDir 365 0 0 0 [] false; mkInode 4 IReg 420 0 0 0 [] false].
Definition resource_caps : CapSets := mkCaps (2 ^ 24) (2 ^ 24) 0 0 0.
Definition resource_ctx : NsCtx :=
  with_caps (with_cwd (with_root (with_mount_ns init_nsctx 2) (2%positive, 1%positive)) (2%positive, 1%positive))
            resource_caps.
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

(** A write of no bytes at offset 0: [__do_proc_doulongvec_minmax] answers
    0 for a count of 0 and changes nothing (kernel/sysctl.c:897-900); a
    value of one space is EINVAL (:953-954). *)
Example write_max_user_namespaces_empty :
  ret_of (write_fn (write_in []) base_model resource_ctx sys_state 1%N sys_file) = Some 0
  /\ limit_of (write_fn (write_in []) base_model resource_ctx sys_state 1%N sys_file) = Some INT_MAX
  /\ ret_of (write_fn (write_in [32]) base_model resource_ctx sys_state 1%N sys_file) = Some (-22).
Proof. vm_compute. repeat split; reflexivity. Qed.

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

(** A gid_map line shows its lower id through the gid map of the parent
    namespace, an uid_map line through its uid map ([gid_m_show] calls
    [from_kgid], [uid_m_show] calls [from_kuid], kernel/user_namespace.c:624,
    645, Linux v6.18.46).  Namespace 2 (A), a child of the initial one, maps
    uids 0-65535 to 100000 and gids 0-65535 to 200000; namespace 3 (B), a
    child of A, maps uid 0 to kernel uid 100000 and gid 0 to kernel gid
    200000.  A task of B reads its own maps, so the namespace shown is A
    (620-622, 641-643): both lines are "0 0 1".  Before this correction the
    gid line went through A's uid map, which does not hold 200000, and
    showed 65534. *)
Definition ns_a : UserNs :=
  mkUserNs 2 (Some 1%positive) 1 0 (Some [mkExtent 0 100000 65536]) (Some [mkExtent 0 200000 65536])
    true false INT_MAX true.
Definition ns_b (gid_lower : Z) : UserNs :=
  mkUserNs 3 (Some 2%positive) 2 100000 (Some [mkExtent 0 100000 1]) (Some [mkExtent 0 gid_lower 1])
    true false INT_MAX true.
Definition gid_loc : Loc := LProcTask 1 42 [bytes [103; 105; 100; 95; 109; 97; 112]].
Definition b_cred : IdCred := mkIdCred 3 0 0 0.
Definition b_uid_reader : NsFile := mkNsFile (NfUserNsFile uid_loc 3 0) 0 b_cred.
Definition b_gid_reader : NsFile := mkNsFile (NfUserNsFile gid_loc 3 0) 0 b_cred.
Definition zero_line : list Z :=
  repeat 32 9 ++ [48; 32] ++ repeat 32 9 ++ [48; 32] ++ repeat 32 9 ++ [49; 10].

Example read_gid_map_through_gid_map :
  writes_of (read_fn (read_in 64) base_model map_ctx (map_state [map_root; ns_a; ns_b 200000])
                     1%N b_gid_reader)
  = Some [(BUF, zero_line)].
Proof. vm_compute. reflexivity. Qed.

Example read_uid_map_through_uid_map :
  writes_of (read_fn (read_in 64) base_model map_ctx (map_state [map_root; ns_a; ns_b 200000])
                     1%N b_uid_reader)
  = Some [(BUF, zero_line)].
Proof. vm_compute. reflexivity. Qed.

(** A lower id the shown namespace's map does not hold is [(gid_t)-1],
    4294967295 (map_id_range_up, 399; from_kgid, 509-513), which "%10u"
    prints as "4294967295" (647-650), not 65534.  [map_write] builds no
    such table (it maps every lower range through the parent's map); this
    hand-built one checks the branch.  The case states the id that
    [map_line] prints: rendering it through [decimal_bytes], which counts
    in unary [nat], is not computable for 4294967295. *)
Example read_gid_map_unmapped_lower :
  shown_lower [map_root; ns_a; ns_b 300000] 3%positive b_cred GidMap 300000 = 4294967295.
Proof. vm_compute. reflexivity. Qed.

Definition file_state : NsState :=
  with_tree base_state
    [mkDentry 1 1 None [] 1; mkDentry 2 1 (Some 1%positive) (bytes [102]) 2]
    [root_dir; mkInode 2 IReg 420 1000 1002 0 (bytes [97; 98; 99; 100]) false].
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

(* ---- unlinkat (35) and fchmod (52) ---- *)

Definition st_of (o : ext_outcome) : option NsState :=
  match o with EOk _ _ _ s _ => Some s | EUnmodeled => None end.
Definition unlinked_of (o : ext_outcome) (d : positive) : option bool :=
  match st_of o with Some s => option_map d_unlinked (find_dentry s d) | None => None end.
Definition perm_of (o : ext_outcome) (n : positive) : option Z :=
  match st_of o with Some s => option_map ino_perm (find_inode s n) | None => None end.
Definition unlink_call (p : list Z) (flags : Z) : SyscallInput :=
  call 35 [-100; PATH; flags] (path_mem p) (fun _ => None).
Definition fchmod_call (mode : Z) : SyscallInput := call 52 [3; mode] (fun _ => None) (fun _ => None).
Definition s_f : list Z := [47; 102].
Definition s_f_slash : list Z := [47; 102; 47].

(** A tmpfs root owned by uid 0, mode [dir_perm], with the file "f" (owner
    [fuid]:[fgid], mode 0644) and the mounts [extra] besides the root. *)
Definition unlink_state (dir_perm fuid fgid : Z) (extra : list Mount) : NsState :=
  let st := with_mounts empty_nsstate (mkMount 1 1 None 1 1 1 no_flags no_flags false false None None :: extra) in
  let st := with_userns st [root_user] in
  let st := with_mntns st [mkMntNs 1 1 1 false; mkMntNs 2 1 1 false] in
  let st := with_pidns st [mkPidNs 1 None 1 0 0] in
  let st := with_sbs st [tmpfs_sb] in
  with_tree st
    [mkDentry 1 1 None [] 1; mkDentry 2 1 (Some 1%positive) (bytes [102]) 2]
    [mkInode 1 IDir dir_perm 0 0 0 [] false; mkInode 2 IReg 420 fuid fgid 0 (bytes [107]) false].

(** do_unlinkat removes the name: the call returns 0, no lookup finds "f",
    and the dentry stays, unlinked, for what holds it. *)
Example unlinkat_removes_name :
  let o := unlinkat_fn (unlink_call s_f 0) base_model base_ctx file_state in
  ret_of o = Some 0 /\ unlinked_of o 2 = Some true
  /\ option_map (fun s => child_dentry s 1 (bytes [102])) (st_of o) = Some None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** An unlinked file's path in /proc/<pid>/fd ([d_path]) ends with
    " (deleted)", and a mount whose root it is shows "//deleted" in
    mountinfo ([dentry_path]). *)
Example unlinked_paths :
  let o := unlinkat_fn (unlink_call s_f 0) base_model base_ctx file_state in
  option_map (fun s => option_map (map bv_unsigned) (d_path s base_ctx (LDentry 1 2))) (st_of o)
    = Some (Some [47; 102; 32; 40; 100; 101; 108; 101; 116; 101; 100; 41])
  /\ option_map (fun s => option_map (map bv_unsigned) (Mountinfo.sb_path s 2)) (st_of o)
    = Some (Some [47; 102; 47; 47; 100; 101; 108; 101; 116; 101; 100]).
Proof. vm_compute. split; reflexivity. Qed.

(** A flag other than AT_REMOVEDIR is EINVAL; AT_REMOVEDIR declines. *)
Example unlinkat_bad_flag :
  ret_of (unlinkat_fn (unlink_call s_f 1) base_model base_ctx file_state) = Some (-22)
  /\ unlinkat_fn (unlink_call s_f 512) base_model base_ctx file_state = EUnmodeled.
Proof. vm_compute. split; reflexivity. Qed.

(** No such name, ENOENT; a trailing slash after a regular file, ENOTDIR. *)
Example unlinkat_missing_and_slash :
  ret_of (unlinkat_fn (unlink_call s_new 0) base_model base_ctx file_state) = Some (-2)
  /\ ret_of (unlinkat_fn (unlink_call s_f_slash 0) base_model base_ctx file_state) = Some (-20).
Proof. vm_compute. split; reflexivity. Qed.

(** A read-only mount, EROFS. *)
Example unlinkat_readonly :
  ret_of (unlinkat_fn (unlink_call s_exists 0) base_model base_ctx existing_ro_state) = Some (-30).
Proof. vm_compute. reflexivity. Qed.

(** A directory, EISDIR. *)
Example unlinkat_directory :
  let o := mkdirat_fn (call 34 [-100; PATH; 511] (path_mem s_new) (fun _ => None)) base_model base_ctx
                      base_state in
  option_map (fun s => ret_of (unlinkat_fn (unlink_call s_new 0) base_model base_ctx s)) (st_of o)
    = Some (Some (-21)).
Proof. vm_compute. reflexivity. Qed.

(** In a sticky directory (01777, owner 0) a file of another user is EPERM;
    without the sticky bit (0777) the unlink succeeds. *)
Example unlinkat_sticky :
  ret_of (unlinkat_fn (unlink_call s_f 0) base_model base_ctx (unlink_state 1023 0 0 [])) = Some (-1)
  /\ ret_of (unlinkat_fn (unlink_call s_f 0) base_model base_ctx (unlink_state 511 0 0 [])) = Some 0.
Proof. vm_compute. split; reflexivity. Qed.

(** No write permission on the directory (0755, owner 0), EACCES. *)
Example unlinkat_no_write :
  ret_of (unlinkat_fn (unlink_call s_f 0) base_model base_ctx (unlink_state 493 1000 1002 [])) = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** A mount on "f" in the caller's mount namespace, EBUSY; a mount on it
    only in another namespace declines (the kernel would detach it). *)
Example unlinkat_mountpoint :
  ret_of (unlinkat_fn (unlink_call s_f 0) base_model base_ctx
            (unlink_state 511 1000 1002 [mkMount 2 1 (Some 1%positive) 2 2 1 no_flags no_flags false false None None]))
    = Some (-16)
  /\ unlinkat_fn (unlink_call s_f 0) base_model base_ctx
       (unlink_state 511 1000 1002 [mkMount 2 2 (Some 1%positive) 2 2 1 no_flags no_flags false false None None])
     = EUnmodeled.
Proof. vm_compute. split; reflexivity. Qed.

Definition chmod_file : NsFile := mkNsFile (NfFile (LDentry 1 2) 0) 2 (mkIdCred 1 1000 1002 0).

(** fchmod sets mode & 07777 on the owner's file and keeps S_ISGID when the
    file's group is the fsgid (02755 = 1517). *)
Example fchmod_sets_mode :
  let o := fchmod_fn (fchmod_call 1517) base_model base_ctx file_state chmod_file in
  ret_of o = Some 0 /\ perm_of o 2 = Some 1517.
Proof. vm_compute. split; reflexivity. Qed.

(** S_ISGID is dropped when the file's group is not one of the task's
    groups and the task has no CAP_FSETID (02755 -> 0755 = 493). *)
Example fchmod_drops_sgid :
  perm_of (fchmod_fn (fchmod_call 1517) base_model base_ctx (unlink_state 511 1000 7 []) chmod_file) 2
    = Some 493.
Proof. vm_compute. reflexivity. Qed.

(** Another user's file, EPERM; a read-only mount, EROFS; an O_PATH file,
    EBADF. *)
Example fchmod_refusals :
  ret_of (fchmod_fn (fchmod_call 420) base_model base_ctx (unlink_state 511 0 0 []) chmod_file) = Some (-1)
  /\ ret_of (fchmod_fn (fchmod_call 420) base_model base_ctx existing_ro_state chmod_file) = Some (-30)
  /\ ret_of (fchmod_fn (fchmod_call 420) base_model base_ctx file_state
               (mkNsFile (NfPath (LDentry 1 2)) 2097152 (mkIdCred 1 1000 1002 0))) = Some (-9).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The environment's refusals ([fsops_injected]): a tmpfs create's space
    and allocation failures and its walk's; unlinkat's walk's, and no
    security module's (ENOENT and EACCES, the tables' answers, are not
    refusals); write's on the model's own files ([write_env]); none for
    fchmod. *)
Example fsops_rows :
  map ni_no fsops_injected = [34; 35; 36; 64]
  /\ ni_errno mkdirat_injected ENOSPC = true /\ ni_errno symlinkat_injected ENOMEM = true
  /\ ni_errno unlinkat_injected ENOMEM = true /\ ni_errno unlinkat_injected EIO = true
  /\ ni_errno unlinkat_injected ENOENT = false /\ ni_errno unlinkat_injected EACCES = false
  /\ ni_errno write_injected ENOMEM = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A write's environment refusals ([write_env]): a writable tmpfs file
    ENOSPC, ENOMEM and EIO; a uid_map ENOMEM and no ENOSPC; a setgroups
    file none (its buffer is on the stack); a file opened read-only none
    (EBADF comes first).  The write row ([write_injected]) lists them for
    the forced-only filter, and EBADF, the tables' answer, is no refusal. *)
Example write_env_refusals :
  write_env file_state chmod_file ENOSPC = true /\ write_env file_state chmod_file EIO = true
  /\ write_env file_state chmod_file ENOMEM = true
  /\ write_env (map_state []) uid_file ENOMEM = true /\ write_env (map_state []) uid_file ENOSPC = false
  /\ write_env (map_state []) groups_file ENOMEM = false
  /\ write_env file_state offset_file ENOSPC = false
  /\ ni_errno write_injected ENOSPC = true /\ ni_errno write_injected EBADF = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A short write ([write_short]): two bytes written at offset 4095 of a
    writable tmpfs file cross a page boundary, so the write can stop after
    the first byte, with the offset moved to 4096; every short count the
    arm admits there is that one. *)
Definition edge_file : NsFile := mkNsFile (NfFile (LDentry 1 2) 4095) 2 (mkIdCred 1 1000 1002 0).
Definition edge_state : NsState := with_files file_state [(1%N, edge_file)].
Definition file_off_of (o : ext_outcome) (h : N) : option Z :=
  match o with
  | EOk _ _ _ s _ =>
      match lookup_file (ns_files s) h with
      | Some f => match nf_kind f with NfFile _ off => Some off | _ => None end
      | None => None
      end
  | EUnmodeled => None
  end.

Example write_short_page_end :
  (exists o, write_short (write_in [120; 121]) base_model base_ctx edge_state 1%N edge_file o
             /\ ret_of o = Some 1 /\ file_off_of o 1%N = Some 4096)
  /\ forall o, write_short (write_in [120; 121]) base_model base_ctx edge_state 1%N edge_file o ->
               ret_of o = Some 1.
Proof.
  split.
  - eexists. split.
    + hnf. split; [reflexivity|]. hnf. exists 1%nat.
      split; [vm_compute; reflexivity | reflexivity].
    + vm_compute. split; reflexivity.
  - intros o [_ H]. hnf in H. destruct H as (k & Hk & ->).
    destruct k as [|[|k]]; vm_compute in Hk; try discriminate Hk.
    vm_compute. reflexivity.
Qed.

(** A write of [KMALLOC_MAX_SIZE] bytes or more to
    /proc/sys/user/max_user_namespaces: [proc_sys_call_handler] answers
    ENOMEM before it allocates or copies anything, so an unreadable buffer
    gets it too; one byte less, the copy is reached, and an unreadable
    buffer declines here.  That ENOMEM is the tables' answer, which the
    write row lists in [ni_forced]. *)
Definition big_write (count : Z) : SyscallInput :=
  call 64 [3; BUF; count] (fun _ => None) (fun _ => None).

Example write_sysctl_large_enomem :
  ret_of (write_fn (big_write KMALLOC_MAX_SIZE) base_model resource_ctx sys_state 1%N sys_file)
    = Some (-12)
  /\ ret_of (write_fn (big_write (2 ^ 30)) base_model resource_ctx sys_state 1%N sys_file) = Some (-12)
  /\ write_fn (big_write (KMALLOC_MAX_SIZE - 1)) base_model resource_ctx sys_state 1%N sys_file
     = EUnmodeled
  /\ ni_forced write_injected = [ENOMEM].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** With descriptor 3 naming that file, every answer the write arm admits
    to such a write is ENOMEM: the tables' answer, the environment's
    ENOMEM after it ([write_env]), and no short count (not tmpfs).  So no
    answer shows that the state did not force the ENOMEM, and the
    forced-only filter keeps it ([Spec.ns_witness]). *)
Definition sys_model : Model :=
  with_fds (fd_insert (m_fds base_model) (Z_to_bv 64 3) (ns_fd_entry 1)) base_model.
Definition sys_open_state : NsState := with_files sys_state [(1%N, sys_file)].

Example write_sysctl_large_only_enomem : forall o,
  write_arm (big_write KMALLOC_MAX_SIZE) sys_model resource_ctx sys_open_state o ->
  ret_of o = Some (-12).
Proof.
  intros o H. unfold write_arm in H.
  replace (ns_file_of sys_model sys_open_state (fd_word (in_arg (big_write KMALLOC_MAX_SIZE) 0)))
    with (Some (1%N, sys_file)) in H by (vm_compute; reflexivity).
  cbv beta iota in H.
  replace (write_fn (big_write KMALLOC_MAX_SIZE) sys_model resource_ctx sys_open_state 1%N sys_file)
    with (ns_errno ENOMEM sys_model resource_ctx sys_open_state) in H by (vm_compute; reflexivity).
  destruct H as [-> | [H | [_ H]]].
  - vm_compute. reflexivity.
  - hnf in H. destruct H as (e & He & ->).
    assert (Hw : write_env sys_open_state sys_file e = errno_in [ENOMEM] e)
      by (vm_compute; reflexivity).
    rewrite Hw in He. unfold errno_in in He. cbn [existsb] in He. rewrite orb_false_r in He.
    apply Z.eqb_eq in He. subst e. vm_compute. reflexivity.
  - vm_compute in H. destruct H.
Qed.

(** A WRITE CHECKS [sysctl_perm] AGAIN, WITH THE WRITER'S CREDENTIAL AT
    THE WRITE.  In [FilesCases.W_user_sys], with an initial user namespace
    that maps every id, a task of that namespace (uid 1000, holding
    CAP_SYS_RESOURCE) opens /proc/sys/user/max_user_namespaces for
    writing: descriptor 3, a file of the initial namespace's sysctl set.
    It calls unshare(CLONE_NEWUSER) and is then in namespace 2, a child of
    the initial one, with every capability there.  Its write of "1" to
    descriptor 3 is EPERM.  The Linux path: [ksys_write], [vfs_write],
    [proc_sys_write], then [proc_sys_call_handler], whose [sysctl_perm]
    with MAY_WRITE (fs/proc/proc_sysctl.c:570-572, 436-447) calls
    [set_permissions] (kernel/ucount.c:42-56).  There
    [ns_capable_noaudit(user_ns, CAP_SYS_RESOURCE)], for the namespace of
    the set, the initial one, is false for a credential of namespace 2
    ([cap_capable_helper], security/commoncap.c:88-89: the initial
    namespace's level is not above namespace 2's).  So the mode is the
    entry's other read bit, 0444, [test_perm] (proc_sysctl.c:425-434)
    refuses MAY_WRITE, and the handler answers -EPERM.  The same write
    before the unshare sets the limit. *)
Definition sysw : NsState :=
  let w := FilesCases.W_user_sys in
  with_files (with_userns w [map_root]) [].
Definition sysw_ctx : NsCtx :=
  FilesCases.ctx_at 1 resource_caps (1%positive, 1%positive) (1%positive, 2%positive).
Definition sysw_opened : ext_outcome :=
  openat_fn (FilesCases.open_in FilesCases.s_max_user_namespaces 1 0) FilesCases.m3 sysw_ctx sysw.
Definition opened_model : Model :=
  match sysw_opened with EOk _ m _ _ _ => m | EUnmodeled => FilesCases.m3 end.
Definition opened_ctx : NsCtx :=
  match sysw_opened with EOk _ _ c _ _ => c | EUnmodeled => sysw_ctx end.
Definition opened_state : NsState :=
  match sysw_opened with EOk _ _ _ s _ => s | EUnmodeled => sysw end.

(** unshare(CLONE_NEWUSER)'s success from there ([UserArms.unshare_exact]). *)
Definition unshare_newuser : SyscallInput :=
  call 97 [UserArms.CLONE_NEWUSER] (fun _ => None) (fun _ => None).
Definition sysw_unshared : ext_outcome :=
  match create_user_ns (ns_userns opened_state) (cx_user opened_ctx)
                       (bv_unsigned (cr_euid (m_creds opened_model))) false with
  | NsOk (n, U) => ns_ret (Z_to_bv 64 0) opened_model (UserArms.in_new_userns opened_ctx n)
                          (with_userns opened_state U)
  | NsErr e => ns_errno e opened_model opened_ctx opened_state
  end.

(** The return of [write_fn] on the open file that the call's descriptor
    names, the answer [write_arm] gives when the environment fails
    nothing. *)
Definition write_answer (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : option Z :=
  match ns_file_of m st (fd_word (in_arg i 0)) with
  | Some (h, f) => ret_of (write_fn i m ctx st h f)
  | None => None
  end.

Example sysctl_write_after_unshare_eperm :
  ret_of sysw_opened = Some 3
  /\ write_answer (write_in [49]) opened_model opened_ctx opened_state = Some 1
  /\ UserArms.unshare_arm unshare_newuser opened_model opened_ctx opened_state sysw_unshared
  /\ ret_of sysw_unshared = Some 0
  /\ match sysw_unshared with
     | EOk _ m ctx st _ => cx_user ctx = 2%positive /\ write_answer (write_in [49]) m ctx st = Some (-1)
     | EUnmodeled => False
     end.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split.
  - rewrite (UserArms.unshare_arm_newuser _ _ _ _ _ map_root false);
      [left; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity].
  - vm_compute. repeat split; reflexivity.
Qed.
