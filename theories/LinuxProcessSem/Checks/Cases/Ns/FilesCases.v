(** * LinuxProcessSem.Checks.Cases.Ns.FilesCases — open files and their metadata in a small namespace

    Each example runs one arm of [Ns.Files] on one world and states its
    answer.  The world: mount 1 is the root (a host file system) with the
    directories home, tmp, ro, secret (0700, uid 2000), proc, nx, the file
    "file", the file "other" (owned by 5000) and the link "link" (to
    "file").  Mount 2, a tmpfs, covers tmp and holds "exists" and the 0755
    root-owned directory "locked"; mount 3, a procfs of pid namespace 1,
    covers proc; mount 4, a read-only, nosuid, nodev tmpfs, covers ro and
    holds "f" (0666); mount 5, a noexec tmpfs, covers nx and holds "run"
    (0755).  The task is uid 1000, gid 1002, pid 42, root at mount 1's
    root, cwd at home, umask 022, descriptors 0, 1, 2. *)

From Stdlib Require Import ZArith List Bool NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Mount Userns Walk Task Files Spec.
Import ListNotations.
Open Scope Z_scope.

Definition bytes (zs : list Z) : list byte := map (Z_to_bv 8) zs.

Definition no_flags : MountFlags := mkMountFlags false false false false.
Definition ro_nosuid_nodev : MountFlags := mkMountFlags true true true false.
Definition noexec_flags : MountFlags := mkMountFlags false false false true.

Definition mnt (i : positive) (parent : option positive) (point root sb : positive) (f : MountFlags)
    : Mount := mkMount i 1 parent point root sb f no_flags false false None None.

Definition sb (i root : positive) (k : SbKind) (magic : Z) : SuperBlock :=
  mkSb i k 1 root false magic false false false.

Definition dir (i : positive) (perm uid gid : Z) : Inode := mkInode i IDir perm uid gid 0 [] false.
Definition reg (i : positive) (perm uid gid : Z) : Inode := mkInode i IReg perm uid gid 0 [] false.
Definition lnk (i : positive) (t : list byte) : Inode := mkInode i ILnk 511 1000 1002 0 t false.

Definition dent (i s : positive) (parent : option positive) (name : list byte) (ino : positive)
    : Dentry := mkDentry i s parent name ino.

(** The one builder of each record that grows: a user namespace, a whole
    state, a task context. *)
Definition uns (i : positive) (parent : option positive) (level : nat)
    (umap gmap : option (list IdExtent)) : UserNs :=
  mkUserNs i parent level 0 umap gmap true false INT_MAX true.

Definition state (users : list UserNs) (files : list (N * NsFile)) : NsState :=
  let st := with_mounts empty_nsstate
    [mnt 1 None 1 1 1 no_flags; mnt 2 (Some 1%positive) 3 20 2 no_flags;
     mnt 3 (Some 1%positive) 9 30 3 no_flags; mnt 4 (Some 1%positive) 5 40 4 ro_nosuid_nodev;
     mnt 5 (Some 1%positive) 10 50 5 noexec_flags] in
  let st := with_userns st users in
  let st := with_mntns st [mk_mntns 1 1 1 false] in
  let st := with_pidns st [mkPidNs 1 None 1 0 0] in
  let st := with_sbs st
    [sb 1 1 SbHost 61267; sb 2 20 SbTmpfs 16914836; sb 3 30 (SbProc 1) 40864;
     sb 4 40 SbTmpfs 16914836; sb 5 50 SbTmpfs 16914836] in
  let st := with_dentries st
    [dent 1 1 None [] 1;
     dent 2 1 (Some 1%positive) (bytes [104; 111; 109; 101]) 2;
     dent 3 1 (Some 1%positive) (bytes [116; 109; 112]) 3;
     dent 4 1 (Some 1%positive) (bytes [102; 105; 108; 101]) 4;
     dent 5 1 (Some 1%positive) (bytes [114; 111]) 5;
     dent 6 1 (Some 1%positive) (bytes [108; 105; 110; 107]) 6;
     dent 7 1 (Some 1%positive) (bytes [115; 101; 99; 114; 101; 116]) 7;
     dent 8 1 (Some 1%positive) (bytes [111; 116; 104; 101; 114]) 8;
     dent 9 1 (Some 1%positive) (bytes [112; 114; 111; 99]) 9;
     dent 10 1 (Some 1%positive) (bytes [110; 120]) 10;
     dent 20 2 None [] 20;
     dent 21 2 (Some 20%positive) (bytes [101; 120; 105; 115; 116; 115]) 21;
     dent 22 2 (Some 20%positive) (bytes [108; 111; 99; 107; 101; 100]) 22;
     dent 30 3 None [] 30;
     dent 40 4 None [] 40;
     dent 41 4 (Some 40%positive) (bytes [102]) 41;
     dent 50 5 None [] 50;
     dent 51 5 (Some 50%positive) (bytes [114; 117; 110]) 51] in
  let st := with_inodes st
    [dir 1 493 1000 1002; dir 2 493 1000 1002; dir 3 493 1000 1002; reg 4 420 1000 1002;
     dir 5 493 1000 1002; lnk 6 (bytes [102; 105; 108; 101]); dir 7 448 2000 2000;
     reg 8 420 5000 5000; dir 9 493 1000 1002; dir 10 493 1000 1002;
     dir 20 511 0 0; reg 21 420 1000 1002; dir 22 493 0 0; dir 30 365 0 0;
     dir 40 511 0 0; reg 41 438 1000 1002; dir 50 511 0 0; reg 51 493 1000 1002] in
  with_files st files.

Definition ctx_at (u : positive) (caps : CapSets) (root cwd : positive * positive) : NsCtx :=
  with_cwd (with_root (with_caps (with_pids (with_user_ns init_nsctx u) [(1%positive, 42%Z)]) caps) root) cwd.

Definition root_user : UserNs := uns 1 None 0 None None.
(** A child user namespace mapping its 0 to kernel uid 1000 and gid 1002. *)
Definition child_user : UserNs :=
  uns 2 (Some 1%positive) 1 (Some [mkExtent 0 1000 1]) (Some [mkExtent 0 1002 1]).

Definition no_caps : CapSets := mkCaps 0 0 0 0 0.
Definition admin_caps : CapSets := mkCaps (2 ^ 21) (2 ^ 21) 0 0 0.

Definition c0 : NsCtx := ctx_at 1 no_caps (1%positive, 1%positive) (1%positive, 2%positive).

Definition cred0 : IdCred := mkIdCred 1 1000 1002 0.

Definition W : NsState := state [root_user; child_user] [].

(** A listed /proc/sys/user/max_user_namespaces file below the procfs root. *)
Definition W_user_sys : NsState :=
  with_tree W
    (ns_dentries W ++
     [dent 31 3 (Some 30%positive) (bytes [115; 121; 115]) 31;
      dent 32 3 (Some 31%positive) (bytes [117; 115; 101; 114]) 32;
      dent 33 3 (Some 32%positive)
           (bytes [109; 97; 120; 95; 117; 115; 101; 114; 95; 110; 97; 109; 101; 115; 112; 97; 99; 101; 115])
           33])
    (ns_inodes W ++ [dir 31 365 0 0; dir 32 365 0 0; reg 33 420 0 0]).

Definition base_model : Model :=
  init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) demo_sp demo_limit (demo_input [] IEof).

(** The base model with descriptor [fd] naming open file [h], for each pair. *)
Definition model_with (fs : list (Z * N)) : Model :=
  with_fds (fold_left (fun acc p => fd_insert acc (Z_to_bv 64 (fst p)) (ns_fd_entry (snd p)))
                      fs (m_fds base_model)) base_model.

Definition with_open (fs : list (N * NsFile)) : NsState := state [root_user; child_user] fs.

(** Bytes [bs] at address [base], nothing else mapped. *)
Definition at_ (base : Z) (bs : list Z) : word -> option byte :=
  fun a => let k := bv_unsigned a - base in
           if (0 <=? k) && (k <? Z.of_nat (length bs)) then Some (Z_to_bv 8 (nth (Z.to_nat k) bs 0))
           else None.

Definition union (f g : word -> option byte) : word -> option byte :=
  fun a => match f a with Some b => Some b | None => g a end.

Definition PATH : Z := 8192.
Definition HOW : Z := 12288.
Definition BUF : Z := 16384.

Definition path_mem (p : list Z) : word -> option byte := at_ PATH (p ++ [0]).
Definition wmem (n : nat) : word -> option byte := at_ BUF (repeat 0 n).

Definition call (n : Z) (args : list Z) (rd wr : word -> option byte) : SyscallInput :=
  mkInput (Z_to_bv 64 n) (map (Z_to_bv 64) args) rd wr.

Definition ret_of (o : ext_outcome) : option Z :=
  match o with EOk eff _ _ _ _ => Some (bv_signed (eff_ret eff)) | EUnmodeled => None end.
Definition writes_of (o : ext_outcome) : option (list (Z * list Z)) :=
  match o with
  | EOk eff _ _ _ _ => Some (map (fun p => (bv_unsigned (fst p), map bv_unsigned (snd p))) (eff_writes eff))
  | EUnmodeled => None
  end.
Definition ctx_of (o : ext_outcome) : option NsCtx :=
  match o with EOk _ _ ctx _ _ => Some ctx | EUnmodeled => None end.
Definition st_of (o : ext_outcome) : option NsState :=
  match o with EOk _ _ _ st _ => Some st | EUnmodeled => None end.

Definition loc_view (l : Loc) : Z * Z * list (list Z) :=
  match l with
  | LDentry m d => (Zpos m, Zpos d, [])
  | LProcTask m p r => (Zpos m, p, map (map bv_unsigned) r)
  | LProcSelf m o => (Zpos m, match o with Some p => p | None => -1 end, [])
  end.

(** The newest open file of an answer: 0 for O_PATH, 1 for a directory, 2
    for a file, 3 for a procfs file bound to a user namespace; its
    location; its [f_flags]. *)
Definition new_file (o : ext_outcome) : option (Z * (Z * Z * list (list Z)) * Z) :=
  match st_of o with
  | Some s => match ns_files s with
              | (_, f) :: _ => match nf_kind f with
                               | NfPath l => Some (0, loc_view l, nf_flags f)
                               | NfDir l _ => Some (1, loc_view l, nf_flags f)
                               | NfFile l _ => Some (2, loc_view l, nf_flags f)
                               | NfUserNsFile l _ _ => Some (3, loc_view l, nf_flags f)
                               | _ => None
                               end
              | [] => None
              end
  | None => None
  end.

Definition s_file : list Z := [47; 102; 105; 108; 101].                    (* /file *)
Definition s_link : list Z := [47; 108; 105; 110; 107].                    (* /link *)
Definition s_home : list Z := [47; 104; 111; 109; 101].                    (* /home *)
Definition s_tmp : list Z := [47; 116; 109; 112].                          (* /tmp *)
Definition s_tmp_new : list Z := s_tmp ++ [47; 110; 101; 119].             (* /tmp/new *)
Definition s_tmp_exists : list Z := s_tmp ++ [47; 101; 120; 105; 115; 116; 115].
Definition s_locked_new : list Z := s_tmp ++ [47; 108; 111; 99; 107; 101; 100; 47; 110; 101; 119].
Definition s_ro_f : list Z := [47; 114; 111; 47; 102].                     (* /ro/f *)
Definition s_ro_new : list Z := [47; 114; 111; 47; 110; 101; 119].         (* /ro/new *)
Definition s_ro : list Z := [47; 114; 111].                                (* /ro *)
Definition s_nx_run : list Z := [47; 110; 120; 47; 114; 117; 110].         (* /nx/run *)
Definition s_secret : list Z := [47; 115; 101; 99; 114; 101; 116].         (* /secret *)
Definition s_self : list Z := [47; 112; 114; 111; 99; 47; 115; 101; 108; 102].
Definition s_setgroups : list Z := s_self ++ [47; 115; 101; 116; 103; 114; 111; 117; 112; 115].
Definition s_uid_map : list Z := s_self ++ [47; 117; 105; 100; 95; 109; 97; 112].
Definition s_fd3 : list Z := s_self ++ [47; 102; 100; 47; 51].             (* /proc/self/fd/3 *)
Definition s_mountinfo : list Z :=
  s_self ++ [47; 109; 111; 117; 110; 116; 105; 110; 102; 111].
Definition s_max_user_namespaces : list Z :=
  [47; 112; 114; 111; 99; 47; 115; 121; 115; 47; 117; 115; 101; 114; 47;
   109; 97; 120; 95; 117; 115; 101; 114; 95; 110; 97; 109; 101; 115; 112; 97; 99; 101; 115].

(** AT_FDCWD as the register holds it. *)
Definition CWD : Z := -100.

(** The fcntl command values as syscall integers, avoiding Sys.Uapi's word
    constants imported by the test fixture. *)
Definition FC_GETFD : Z := 1.
Definition FC_SETFD : Z := 2.
Definition FC_GETFL : Z := 3.

Definition open_in (p : list Z) (flags mode : Z) : SyscallInput :=
  call 56 [CWD; PATH; flags; mode] (path_mem p) (fun _ => None).

Definition m3 : Model := model_with [].

(* ---- openat ------------------------------------------------------------ *)

(** An open for reading: the lowest free descriptor, a file of the model,
    O_LARGEFILE in its flags. *)
Example openat_read :
  ret_of (openat_fn (open_in s_file 0 0) m3 c0 W) = Some 3
  /\ new_file (openat_fn (open_in s_file 0 0) m3 c0 W) = Some (2, (1, 4, []), O_LARGEFILE).
Proof. split; vm_compute; reflexivity. Qed.

(** O_PATH|O_NOFOLLOW on a link opens the link itself. *)
Example openat_path_nofollow_link :
  new_file (openat_fn (open_in s_link (O_PATH + O_NOFOLLOW) 0) m3 c0 W)
  = Some (0, (1, 6, []), O_PATH + O_NOFOLLOW).
Proof. vm_compute. reflexivity. Qed.

(** O_NOFOLLOW without O_PATH on a link: ELOOP. *)
Example openat_nofollow_link : ret_of (openat_fn (open_in s_link O_NOFOLLOW 0) m3 c0 W) = Some (-40).
Proof. vm_compute. reflexivity. Qed.

(** O_DIRECTORY on a file: ENOTDIR. *)
Example openat_directory_on_file : ret_of (openat_fn (open_in s_file O_DIRECTORY 0) m3 c0 W) = Some (-20).
Proof. vm_compute. reflexivity. Qed.

(** O_CREAT|O_EXCL in a tmpfs directory makes a regular file owned by the
    fsuid and fsgid, mode 0666 & ~022, opened for writing. *)
Definition creat_excl : Z := 1 + O_CREAT + O_EXCL.

Definition newest_inode (o : ext_outcome) : option (Z * Z * Z * Z) :=
  match st_of o with
  | Some s => match rev (ns_inodes s) with
              | n :: _ => Some (Zpos (ino_id n), ino_perm n, ino_uid n, ino_gid n)
              | [] => None
              end
  | None => None
  end.

Example openat_create_excl :
  ret_of (openat_fn (open_in s_tmp_new creat_excl 438) m3 c0 W) = Some 3
  /\ newest_inode (openat_fn (open_in s_tmp_new creat_excl 438) m3 c0 W) = Some (52, 420, 1000, 1002)
  /\ new_file (openat_fn (open_in s_tmp_new creat_excl 438) m3 c0 W) = Some (2, (2, 52, []), 1 + O_LARGEFILE).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The name exists: EEXIST. *)
Example openat_create_exists : ret_of (openat_fn (open_in s_tmp_exists creat_excl 438) m3 c0 W) = Some (-17).
Proof. vm_compute. reflexivity. Qed.

(** No write permission on the directory: EACCES. *)
Example openat_create_denied : ret_of (openat_fn (open_in s_locked_new creat_excl 438) m3 c0 W) = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** A write open on a read-only mount (the file's mode allows it): EROFS;
    a create of a free name there: EROFS. *)
Example openat_write_readonly : ret_of (openat_fn (open_in s_ro_f 1 0) m3 c0 W) = Some (-30).
Proof. vm_compute. reflexivity. Qed.
Example openat_create_readonly : ret_of (openat_fn (open_in s_ro_new creat_excl 438) m3 c0 W) = Some (-30).
Proof. vm_compute. reflexivity. Qed.

(** A directory opened for writing: EISDIR. *)
Example openat_write_directory : ret_of (openat_fn (open_in s_home 1 0) m3 c0 W) = Some (-21).
Proof. vm_compute. reflexivity. Qed.

(** An empty path: ENOENT; a relative path from a descriptor that is not
    open: EBADF. *)
Example openat_empty : ret_of (openat_fn (open_in [] 0 0) m3 c0 W) = Some (-2).
Proof. vm_compute. reflexivity. Qed.
Example openat_bad_dirfd :
  ret_of (openat_fn (call 56 [7; PATH; 0; 0] (path_mem [102; 105; 108; 101]) (fun _ => None)) m3 c0 W)
  = Some (-9).
Proof. vm_compute. reflexivity. Qed.

(** getname faults on an unmapped first byte and refuses 4096 non-NUL
    bytes with ENAMETOOLONG. *)
Example openat_path_fault :
  ret_of (openat_fn (call 56 [CWD; PATH; 0; 0] (fun _ => None) (fun _ => None)) m3 c0 W)
  = Some (-14).
Proof. vm_compute. reflexivity. Qed.

Example openat_path_too_long :
  ret_of (openat_fn (call 56 [CWD; PATH; 0; 0] (at_ PATH (repeat 97 4096)) (fun _ => None)) m3 c0 W)
  = Some (-36).
Proof. vm_compute. reflexivity. Qed.

(** At the soft RLIMIT_NOFILE: EMFILE. *)
Example openat_emfile :
  ret_of (openat_fn (open_in s_file 0 0) (with_nofile (Z_to_bv 64 3) m3) c0 W) = Some (-24).
Proof. vm_compute. reflexivity. Qed.

(** O_CLOEXEC marks the new descriptor close-on-exec. *)
Example openat_cloexec :
  option_map cx_cloexec (ctx_of (openat_fn (open_in s_file O_CLOEXEC 0) m3 c0 W)) = Some [3].
Proof. vm_compute. reflexivity. Qed.

(** The task's setgroups file opened for writing needs CAP_SYS_ADMIN over
    its user namespace: EACCES without it, a descriptor with it. *)
Example openat_setgroups_write :
  ret_of (openat_fn (open_in s_setgroups 1 0) m3 c0 W) = Some (-13)
  /\ ret_of (openat_fn (open_in s_setgroups 1 0) m3
                       (ctx_at 1 admin_caps (1%positive, 1%positive) (1%positive, 2%positive)) W)
     = Some 3.
Proof. split; vm_compute; reflexivity. Qed.

(** The task's uid_map opens at its procfs location, bound to the task's
    user namespace. *)
Example openat_uid_map :
  new_file (openat_fn (open_in s_uid_map 0 0) m3 c0 W)
  = Some (3, (3, 42, [[117; 105; 100; 95; 109; 97; 112]]), O_LARGEFILE).
Proof. vm_compute. reflexivity. Qed.

(** set_permissions in kernel/ucount.c makes a user namespace sysctl
    read-only without CAP_SYS_RESOURCE. *)
Example openat_user_sys_write_without_resource :
  ret_of (openat_fn (open_in s_max_user_namespaces 1 0) m3 c0 W_user_sys) = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** mounts_open_common binds the task's mount namespace and root at open. *)
Definition mountinfo_binding (o : ext_outcome) : option (Z * Z * Z * Z * Z * Z) :=
  match st_of o with
  | Some s => match ns_files s with
              | (_, f) :: _ =>
                  match nf_kind f with
                  | NfMountinfo (LProcTask m pid _) ns (rm, rd) off =>
                      Some (Zpos m, pid, Zpos ns, Zpos rm, Zpos rd, off)
                  | _ => None
                  end
              | [] => None
              end
  | None => None
  end.

Example openat_mountinfo_binds_namespace_root :
  mountinfo_binding (openat_fn (open_in s_mountinfo 0 0) m3 c0 W) = Some (3, 42, 1, 1, 1, 0).
Proof. vm_compute. reflexivity. Qed.

(* ---- the owners in a sticky directory ---------------------------------- *)

(** INVALID_UID and INVALID_GID ((uid_t) -1, include/linux/uidgid.h:50-51). *)
Definition invalid_id : Z := 4294967295.

(** [W] with the sticky world-writable directory "st" (01777) owned by uid
    and gid [downer], and the regular file "st/f" (mode [fmode]) and the
    link "st/l" (to "/file") owned by uid and gid [fowner]. *)
Definition W_sticky_at (downer fowner fmode : Z) : NsState :=
  with_tree W
    (ns_dentries W ++
     [dent 11 1 (Some 1%positive) (bytes [115; 116]) 11;
      dent 12 1 (Some 11%positive) (bytes [102]) 12;
      dent 13 1 (Some 11%positive) (bytes [108]) 13])
    (ns_inodes W ++
     [dir 11 1023 downer downer; reg 12 fmode fowner fowner;
      mkInode 13 ILnk 511 fowner fowner 0 (bytes [47; 102; 105; 108; 101]) false]).

(** The same with "st/f" of mode 0666 and all three owned by [owner]. *)
Definition W_sticky (owner : Z) : NsState := W_sticky_at owner owner 438.

Definition s_st_f : list Z := [47; 115; 116; 47; 102].                    (* /st/f *)
Definition s_st_l : list Z := [47; 115; 116; 47; 108].                    (* /st/l *)

(** A caller with fsuid and fsgid 2000, no supplementary group. *)
Definition uid2000 : Creds :=
  mkCreds (Z_to_bv 64 2000) (Z_to_bv 64 2000) (Z_to_bv 64 2000) (Z_to_bv 64 2000) (Z_to_bv 64 2000)
          (Z_to_bv 64 2000) [].

(** [may_create_in_sticky] (fs/namei.c:1304-1347, Linux v6.18.46) compares
    the file's owner with the directory's by [vfsuid_eq] (1321), which is
    false when the left one is INVALID (include/linux/mnt_idmapping.h:65-68).
    An O_CREAT open of the existing 0666 file "st/f", in the sticky
    world-writable "st", both owned by INVALID, by the caller with fsuid
    1000, which owns neither: Linux answers EACCES with protected_regular 1
    (1327-1329) and opens with protected_regular 0 (1313-1314); the tables
    do not hold the sysctl, so the model has no answer.  Both owned by 1000
    and a caller with fsuid 2000: the owners match (1321-1322) and the open
    gives descriptor 3. *)
Example openat_creat_sticky_invalid_owners :
  openat_fn (open_in s_st_f O_CREAT 438) m3 c0 (W_sticky invalid_id) = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example openat_creat_sticky_same_owner :
  ret_of (openat_fn (open_in s_st_f O_CREAT 438) (with_creds uid2000 m3) c0 (W_sticky 1000)) = Some 3.
Proof. vm_compute. reflexivity. Qed.

(** Where the open's later steps refuse with EACCES, Linux answers EACCES
    under every sysctl value, and so does the model ([sticky_answer]).
    The 0600 file "st/f", both owners INVALID, opened for reading with
    O_CREAT by the caller with fsuid 1000, which is in the file's other
    class: EACCES with protected_regular 1 (1327-1329), and from
    [may_open] (3973; [generic_permission]) with protected_regular 0.
    The model answered EACCES before the correction too. *)
Example openat_creat_sticky_invalid_owners_denied :
  ret_of (openat_fn (open_in s_st_f O_CREAT 438) m3 c0 (W_sticky_at invalid_id invalid_id 384))
  = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** The same rule for two valid owners that differ: "st" owned by 3000 and
    the 0600 file "st/f" by 2000, the same open by the caller with fsuid
    1000: EACCES, where the model gave no answer before. *)
Example openat_creat_sticky_other_owners_denied :
  ret_of (openat_fn (open_in s_st_f O_CREAT 438) m3 c0 (W_sticky_at 3000 2000 384)) = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** One owner INVALID and the other valid: the owners differ for
    [vfsuid_eq] and for the old plain comparison alike, so the model
    declined before.  Now, as for two valid owners that differ, a denied
    open of "st/f" (0600) by the caller with fsuid 1000 answers EACCES,
    which Linux gives under every protected_regular value (1327-1329, or
    [may_open]'s [inode_permission], 3973): the directory owned by 3000
    and the file by INVALID, then the directory owned by INVALID and the
    file by 2000. *)
Example openat_creat_sticky_mixed_owners_denied :
  ret_of (openat_fn (open_in s_st_f O_CREAT 438) m3 c0 (W_sticky_at 3000 invalid_id 384)) = Some (-13)
  /\ ret_of (openat_fn (open_in s_st_f O_CREAT 438) m3 c0 (W_sticky_at invalid_id 2000 384))
     = Some (-13).
Proof. split; vm_compute; reflexivity. Qed.

(** [W] with the sticky world-writable directory "ro/st" (01777) on the
    read-only mount 4, holding the regular file "ro/st/f" (0666), both
    owned by uid and gid [owner]. *)
Definition W_sticky_ro (owner : Z) : NsState :=
  with_tree W
    (ns_dentries W ++
     [dent 17 4 (Some 40%positive) (bytes [115; 116]) 17;
      dent 18 4 (Some 17%positive) (bytes [102]) 18])
    (ns_inodes W ++ [dir 17 1023 owner owner; reg 18 438 owner owner]).

Definition s_ro_st_f : list Z := [47; 114; 111; 47; 115; 116; 47; 102].  (* /ro/st/f *)
Definition creat_trunc_write : Z := 1 + O_CREAT + O_TRUNC.

(** An O_CREAT|O_TRUNC write open of "ro/st/f", both owners INVALID, by
    the caller with fsuid 1000: Linux answers EACCES with protected_regular
    1 (1327-1329) and EROFS from [mnt_want_write] (3967-3970) with
    protected_regular 0, so the model has no answer; it answered EROFS
    before the correction.  Both owned by 1000 and a caller with fsuid
    2000: the owners match (1321-1322) and the answer is EROFS. *)
Example openat_creat_trunc_sticky_invalid_owners_readonly :
  openat_fn (open_in s_ro_st_f creat_trunc_write 438) m3 c0 (W_sticky_ro invalid_id) = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example openat_creat_trunc_sticky_same_owner_readonly :
  ret_of (openat_fn (open_in s_ro_st_f creat_trunc_write 438) (with_creds uid2000 m3) c0 (W_sticky_ro 1000))
  = Some (-30).
Proof. vm_compute. reflexivity. Qed.

(** A superblock with SB_RDONLY, built as [sb] builds the others. *)
Definition sb_ro (i root : positive) (k : SbKind) (magic : Z) : SuperBlock :=
  mkSb i k 1 root true magic false false false.

(** [W_sticky_ro] with the superblock of mount 4 read-only too. *)
Definition W_sticky_rosb (owner : Z) : NsState :=
  with_sbs (W_sticky_ro owner)
    [sb 1 1 SbHost 61267; sb 2 20 SbTmpfs 16914836; sb 3 30 (SbProc 1) 40864;
     sb_ro 4 40 SbTmpfs 16914836; sb 5 50 SbTmpfs 16914836].

Definition creat_write : Z := 1 + O_CREAT.

(** An O_CREAT write open without O_TRUNC of "ro/st/f" on the read-only
    superblock, both owners INVALID, by the caller with fsuid 1000: Linux
    answers EACCES with protected_regular 1 (1327-1329) and EROFS from
    [sb_permission] in [may_open]'s [inode_permission] (550-551, 3973)
    with protected_regular 0, so the model has no answer; it answered
    EROFS before the correction.  Both owned by 1000 and a caller with
    fsuid 2000: the owners match (1321-1322) and the answer is EROFS. *)
Example openat_creat_write_sticky_invalid_owners_rosb :
  openat_fn (open_in s_ro_st_f creat_write 438) m3 c0 (W_sticky_rosb invalid_id) = EUnmodeled
  /\ ret_of (openat_fn (open_in s_ro_st_f creat_write 438) (with_creds uid2000 m3) c0
               (W_sticky_rosb 1000)) = Some (-30).
Proof. split; vm_compute; reflexivity. Qed.

(** [may_follow_link] (fs/namei.c:1168-1196) lets a follower that does not
    own a last-component link in a sticky world-writable directory follow
    it only when the directory's owner is valid and owns the link (1187).
    The link "st/l" and "st" both owned by INVALID, followed by the caller
    with fsuid 1000: Linux answers EACCES with protected_symlinks 1
    (1187-1195) and follows with protected_symlinks 0 (1173-1174); the
    model has no answer.  Both owned by 1000 and a caller with fsuid 2000:
    the link is followed (1187-1188) and the open gives "/file". *)
Example openat_follow_sticky_invalid_owners :
  openat_fn (open_in s_st_l 0 0) m3 c0 (W_sticky invalid_id) = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

Example openat_follow_sticky_same_owner :
  new_file (openat_fn (open_in s_st_l 0 0) (with_creds uid2000 m3) c0 (W_sticky 1000))
  = Some (2, (1, 4, []), O_LARGEFILE).
Proof. vm_compute. reflexivity. Qed.

(* ---- openat2 ----------------------------------------------------------- *)

Definition how_mem (flags mode resolve : Z) : word -> option byte :=
  at_ HOW (map bv_unsigned (Z_to_le_bytes 8 flags ++ Z_to_le_bytes 8 mode ++ Z_to_le_bytes 8 resolve)).

Definition open2 (dfd : Z) (p : list Z) (flags resolve size : Z) : SyscallInput :=
  call 437 [dfd; PATH; HOW; size] (union (path_mem p) (how_mem flags 0 resolve)) (fun _ => None).

(** O_PATH with any other flag: EINVAL; a size below 24: EINVAL. *)
Example openat2_path_rdwr :
  ret_of (fst (fst (openat2_fn (open2 CWD s_tmp (O_PATH + 2) 0 24) m3 c0 W))) = Some (-22).
Proof. vm_compute. reflexivity. Qed.
Example openat2_small_size :
  ret_of (fst (fst (openat2_fn (open2 CWD s_tmp O_PATH 0 16) m3 c0 W))) = Some (-22).
Proof. vm_compute. reflexivity. Qed.

(** A size above one page: E2BIG, before the open_how is read. *)
Example openat2_large_size :
  ret_of (fst (fst (openat2_fn (open2 CWD s_tmp O_PATH 0 4097) m3 c0 W))) = Some (-7).
Proof. vm_compute. reflexivity. Qed.

(** RESOLVE_IN_ROOT from an O_PATH descriptor on tmpfs's root: ".." stays
    at that root, so "../exists" opens tmpfs's "exists"; the walk took a
    scoped "..", so EAGAIN is also an outcome. *)
Definition m_dir3 : Model := model_with [(3, 1%N)].
Definition W_dir3 : NsState := with_open [(1%N, mkNsFile (NfPath (LDentry 2 20)) O_PATH cred0)].
Definition up_exists : list Z := [46; 46; 47; 101; 120; 105; 115; 116; 115].

Example openat2_in_root_dotdot :
  ret_of (fst (fst (openat2_fn (open2 3 up_exists 0 RESOLVE_IN_ROOT 24) m_dir3 c0 W_dir3))) = Some 4
  /\ snd (openat2_fn (open2 3 up_exists 0 RESOLVE_IN_ROOT 24) m_dir3 c0 W_dir3) = true.
Proof. split; vm_compute; reflexivity. Qed.

Example openat2_in_root_eagain :
  openat2_arm (open2 3 up_exists 0 RESOLVE_IN_ROOT 24) m_dir3 c0 W_dir3
              (err (snd (fst (openat2_fn (open2 3 up_exists 0 RESOLVE_IN_ROOT 24) m_dir3 c0 W_dir3)))
                   EAGAIN m_dir3 c0 W_dir3).
Proof. right. split; [vm_compute; reflexivity | reflexivity]. Qed.

(* ---- close, fcntl ------------------------------------------------------ *)

Definition file1 : NsFile := mkNsFile (NfFile (LDentry 1 4) 0) (2 + O_LARGEFILE) cred0.

(** Closing the last descriptor of an open file drops the file; with a
    second descriptor on it, the file stays. *)
Example close_last_drops_file :
  option_map (fun s => length (ns_files s))
    (match close_fn (call 57 [3] (fun _ => None) (fun _ => None)) (model_with [(3, 1%N)]) c0
                    (with_open [(1%N, file1)]) with Some o => st_of o | None => None end)
  = Some 0%nat.
Proof. vm_compute. reflexivity. Qed.

Example close_shared_keeps_file :
  option_map (fun s => length (ns_files s))
    (match close_fn (call 57 [3] (fun _ => None) (fun _ => None)) (model_with [(3, 1%N); (4, 1%N)]) c0
                    (with_open [(1%N, file1)]) with Some o => st_of o | None => None end)
  = Some 1%nat.
Proof. vm_compute. reflexivity. Qed.

(** F_SETFD (FD_CLOEXEC) then F_GETFD reads the bit back. *)
Example fcntl_cloexec_round_trip :
  match fcntl_fn (call 25 [3; FC_SETFD; 1] (fun _ => None) (fun _ => None)) (model_with [(3, 1%N)]) c0
                 (with_open [(1%N, file1)]) with
  | Some (EOk _ m' c' s' _) =>
      option_map ret_of (fcntl_fn (call 25 [3; FC_GETFD; 0] (fun _ => None) (fun _ => None)) m' c' s')
  | _ => None
  end = Some (Some 1).
Proof. vm_compute. reflexivity. Qed.

(** F_GETFL returns the file's flags; an O_PATH file refuses F_SETFL (4)
    with EBADF. *)
Example fcntl_getfl :
  option_map ret_of (fcntl_fn (call 25 [3; FC_GETFL; 0] (fun _ => None) (fun _ => None))
                              (model_with [(3, 1%N)]) c0 (with_open [(1%N, file1)]))
  = Some (Some (2 + O_LARGEFILE)).
Proof. vm_compute. reflexivity. Qed.
Example fcntl_path_setfl :
  option_map ret_of (fcntl_fn (call 25 [3; 4; 0] (fun _ => None) (fun _ => None)) m_dir3 c0 W_dir3)
  = Some (Some (-9)).
Proof. vm_compute. reflexivity. Qed.

(** A command the namespace-file fcntl arm does not model declines. *)
Example fcntl_other_declines :
  fcntl_fn (call 25 [3; 4; 0] (fun _ => None) (fun _ => None))
            (model_with [(3, 1%N)]) c0 (with_open [(1%N, file1)])
  = Some EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(* ---- fstat, newfstatat ------------------------------------------------- *)

(** In user namespace 2 (0 -> 1000), "other" (owner 5000) shows the
    overflow ids 65534, the default launch value [env_overflow_ids], and
    no other value.  st_dev and st_ino are environment bytes. *)
Definition c_child : NsCtx := ctx_at 2 no_caps (1%positive, 1%positive) (1%positive, 2%positive).

Example fstat_fields_unmapped_owner :
  option_map (fun a => map (fun p => (Z.of_nat (fst p), map bv_unsigned (snd p))) (stat_fields a))
             (loc_attr m3 c_child W (LDentry 1 8))
  = Some [(16, [164; 129; 0; 0])]
  /\ option_map (fun a => (oa_uid a, oa_gid a)) (loc_attr m3 c_child W (LDentry 1 8)) = Some (5000, 5000)
  /\ (forall v, munged_ok W c_child false 5000 v = Z.eqb v 65534)
  /\ (forall v, munged_ok W c_child true 5000 v = Z.eqb v 65534).
Proof.
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  split; intro v; vm_compute; reflexivity.
Qed.

Definition stat_bytes : list byte :=
  Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 8 ++ Z_to_le_bytes 4 33188 ++ Z_to_le_bytes 4 0
  ++ Z_to_le_bytes 4 65534 ++ Z_to_le_bytes 4 65534 ++ repeat (Z_to_bv 8 0) 96.

Definition other_file : NsFile := mkNsFile (NfFile (LDentry 1 8) 0) O_LARGEFILE cred0.

Example fstat_admits_overflow_ids :
  fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (model_with [(3, 1%N)]) c_child
            (with_open [(1%N, other_file)])
            (ans [] (Z_to_bv 64 0) [(Z_to_bv 64 BUF, stat_bytes)] (model_with [(3, 1%N)]) c_child
                 (with_open [(1%N, other_file)])).
Proof. vm_compute. exists stat_bytes. repeat split; vm_compute; reflexivity. Qed.

(** newfstatat with AT_EMPTY_PATH on an O_PATH descriptor stats its
    object; an unknown flag is EINVAL before the name's error. *)
Definition tmp_root_bytes : list byte :=
  Z_to_le_bytes 8 2 ++ Z_to_le_bytes 8 20 ++ Z_to_le_bytes 4 (16384 + 511) ++ Z_to_le_bytes 4 0
  ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 0 ++ repeat (Z_to_bv 8 0) 96.

Example newfstatat_empty_path :
  newfstatat_arm (call 79 [3; PATH; BUF; AT_EMPTY_PATH] (path_mem []) (wmem 128)) m_dir3 c0 W_dir3
                 (ans [(Z_to_bv 64 PATH, 1%nat)] (Z_to_bv 64 0) [(Z_to_bv 64 BUF, tmp_root_bytes)]
                      m_dir3 c0 W_dir3).
Proof. vm_compute. exists tmp_root_bytes. repeat split; vm_compute; reflexivity. Qed.

Example newfstatat_bad_flag :
  newfstatat_arm (call 79 [3; PATH; BUF; 32768] (path_mem []) (wmem 128)) m_dir3 c0 W_dir3
                 (err [(Z_to_bv 64 PATH, 1%nat)] EINVAL m_dir3 c0 W_dir3).
Proof. vm_compute. reflexivity. Qed.

(* ---- faccessat --------------------------------------------------------- *)

Definition access_in (p : list Z) (mode : Z) : SyscallInput :=
  call 48 [CWD; PATH; mode] (path_mem p) (fun _ => None).

(** R_OK on a readable file: 0; W_OK on a read-only mount: EROFS; X_OK on
    a regular file of a noexec mount: EACCES; a bad mode bit: EINVAL. *)
Example faccessat_read : ret_of (faccessat_fn (access_in s_file 4) m3 c0 W) = Some 0.
Proof. vm_compute. reflexivity. Qed.
Example faccessat_write_readonly : ret_of (faccessat_fn (access_in s_ro_f 2) m3 c0 W) = Some (-30).
Proof. vm_compute. reflexivity. Qed.
Example faccessat_exec_noexec : ret_of (faccessat_fn (access_in s_nx_run 1) m3 c0 W) = Some (-13).
Proof. vm_compute. reflexivity. Qed.
Example faccessat_bad_mode : ret_of (faccessat_fn (access_in s_file 8) m3 c0 W) = Some (-22).
Proof. vm_compute. reflexivity. Qed.

(** Access to a 0700 directory owned by another uid: EACCES. *)
Example faccessat_denied : ret_of (faccessat_fn (access_in s_secret 4) m3 c0 W) = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** A /proc/sys/user file's [->permission] is [proc_sys_permission]
    (fs/proc/proc_sysctl.c:792-819), not [generic_permission]: only the
    mode [set_permissions] gives counts ([sysctl_perm_ok]).  So
    CAP_DAC_OVERRIDE alone does not open it for writing and
    CAP_SYS_RESOURCE does; [faccessat]'s W_OK refuses uid 0 without
    CAP_SYS_RESOURCE, although the file is 0644 and owned by uid 0, and
    grants it to uid 0 with CAP_SYS_RESOURCE in its permitted set
    ([access_effective]). *)
Definition dac_override_caps : CapSets := mkCaps 2 2 0 0 0.
Definition sys_resource_caps : CapSets := mkCaps (2 ^ 24) (2 ^ 24) 0 0 0.
Definition c_caps (caps : CapSets) : NsCtx := ctx_at 1 caps (1%positive, 1%positive) (1%positive, 2%positive).
Definition uid0 : Creds :=
  mkCreds (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) [].

Example user_sys_permission :
  ret_of (openat_fn (open_in s_max_user_namespaces 1 0) m3 (c_caps dac_override_caps) W_user_sys)
    = Some (-13)
  /\ ret_of (openat_fn (open_in s_max_user_namespaces 1 0) m3 (c_caps sys_resource_caps) W_user_sys)
    = Some 3
  /\ ret_of (faccessat_fn (access_in s_max_user_namespaces 2) (with_creds uid0 m3) c0 W_user_sys)
    = Some (-13)
  /\ ret_of (faccessat_fn (access_in s_max_user_namespaces 2) (with_creds uid0 m3)
               (c_caps sys_resource_caps) W_user_sys) = Some 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- the id 4294967295 and the overflow ids ---------------------------- *)

(** [W] with the file "o" (mode 0000) and the directory "d" (mode 0000),
    both owned by uid [uid] and gid [gid]; "d" holds the file "f" (0644,
    uid 1000).  The id 4294967295 is INVALID_UID and INVALID_GID
    (include/linux/uidgid.h:50-51): no user namespace maps it, the initial
    one included (its one extent holds 0 to 4294967294, kernel/user.c:40-55). *)
Definition W_owned (uid gid : Z) : NsState :=
  with_tree W
    (ns_dentries W ++
     [dent 14 1 (Some 1%positive) (bytes [111]) 14;
      dent 15 1 (Some 1%positive) (bytes [100]) 15;
      dent 16 1 (Some 15%positive) (bytes [102]) 16])
    (ns_inodes W ++ [reg 14 0 uid gid; dir 15 0 uid gid; reg 16 420 1000 1002]).

Definition s_o : list Z := [47; 111].                                       (* /o *)
Definition s_d_f : list Z := [47; 100; 47; 102].                            (* /d/f *)

(** [privileged_wrt_inode_uidgid] (kernel/capability.c:455-461) needs the
    inode's uid and gid to map into the caller's user namespace
    ([vfsuid_has_mapping], [vfsgid_has_mapping],
    include/linux/mnt_idmapping.h:158-162, 196-200).  A caller in the
    initial namespace with CAP_DAC_OVERRIDE opens the mode-0000 "o" for
    reading when it is owned by 1000:0, but not when its uid or its gid is
    4294967295: EACCES ([generic_permission], fs/namei.c).  The same for
    the search of the mode-0000 directory "d" ([may_lookup]). *)
Example openat_invalid_owner_not_capable :
  ret_of (openat_fn (open_in s_o 0 0) m3 (c_caps dac_override_caps) (W_owned 4294967295 0)) = Some (-13)
  /\ ret_of (openat_fn (open_in s_o 0 0) m3 (c_caps dac_override_caps) (W_owned 1000 4294967295))
     = Some (-13)
  /\ ret_of (openat_fn (open_in s_o 0 0) m3 (c_caps dac_override_caps) (W_owned 1000 0)) = Some 3.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example openat_invalid_dir_owner_not_searchable :
  ret_of (openat_fn (open_in s_d_f 0 0) m3 (c_caps dac_override_caps) (W_owned 4294967295 0))
  = Some (-13)
  /\ ret_of (openat_fn (open_in s_d_f 0 0) m3 (c_caps dac_override_caps) (W_owned 1000 4294967295))
     = Some (-13)
  /\ ret_of (openat_fn (open_in s_d_f 0 0) m3 (c_caps dac_override_caps) (W_owned 1000 0)) = Some 3.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** [mode_strip_sgid] (fs/inode.c:2935-2945) keeps S_ISGID on a new file
    in a setgid directory only for a caller in the directory's group or
    with CAP_FSETID over it ([in_group_or_capable], 2910-2918), and that
    capability needs the directory's uid and gid to map
    ([capable_wrt_inode_uidgid], kernel/capability.c:455-480).  A caller
    outside group 0 creates "new" with mode 02775 in the tmpfs directory
    "/tmp/g" (02777, owned by 0:0): with CAP_FSETID the file keeps S_ISGID
    (02755 after the umask), without it the file loses it (0755).  No case
    uses a directory whose uid or gid is 4294967295: Linux refuses a create
    there with EACCES before [mode_strip_sgid] ([may_o_create],
    fs/namei.c:3611-3626, through [inode_permission]'s [HAS_UNMAPPED_ID],
    589-590), a test the model does not have yet; a separate correction
    adds it. *)
Definition W_sgid : NsState :=
  with_tree W (ns_dentries W ++ [dent 23 2 (Some 20%positive) (bytes [103]) 23])
              (ns_inodes W ++ [dir 23 1535 0 0]).
Definition s_g_new : list Z := s_tmp ++ [47; 103; 47; 110; 101; 119].     (* /tmp/g/new *)
Definition fsetid_caps : CapSets := mkCaps (2 ^ 4) (2 ^ 4) 0 0 0.

Example openat_create_sgid_fsetid :
  newest_inode (openat_fn (open_in s_g_new creat_excl 1533) m3 (c_caps fsetid_caps) W_sgid)
  = Some (52, 1517, 1000, 0)
  /\ newest_inode (openat_fn (open_in s_g_new creat_excl 1533) m3 (c_caps no_caps) W_sgid)
     = Some (52, 493, 1000, 0).
Proof. vm_compute. split; reflexivity. Qed.

(** The tables [st] with the launch value [env_overflow_ids] set to [o]. *)
Definition with_overflow (st : NsState) (o : option (Z * Z)) : NsState :=
  with_env st (env_with_overflow_ids (ns_env st) o).

(** The default launch assumes the kernel's default overflow ids
    (include/linux/highuid.h:41-42, kernel/sys.c:167-168). *)
Example overflow_ids_launch_default :
  env_overflow_ids (ns_env empty_nsstate) = Some (65534, 65534)
  /\ env_overflow_ids (ns_env W) = Some (65534, 65534).
Proof. vm_compute. split; reflexivity. Qed.

(** An fstat of descriptor 3, open on "o", answered with [bs]. *)
Definition o_file : NsFile := mkNsFile (NfFile (LDentry 1 14) 0) O_LARGEFILE cred0.
Definition o_open (st : NsState) : NsState := with_files st [(1%N, o_file)].
Definition o_stat (uid gid : Z) : list byte :=
  Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 14 ++ Z_to_le_bytes 4 32768 ++ Z_to_le_bytes 4 0
  ++ Z_to_le_bytes 4 uid ++ Z_to_le_bytes 4 gid ++ repeat (Z_to_bv 8 0) 96.
Definition fstat_o (ctx : NsCtx) (st : NsState) (bs : list byte) : Prop :=
  fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (model_with [(3, 1%N)]) ctx (o_open st)
            (ans [] (Z_to_bv 64 0) [(Z_to_bv 64 BUF, bs)] (model_with [(3, 1%N)]) ctx (o_open st)).

(** [cp_new_stat] (fs/stat.c:492-493) shows [from_kuid_munged] of the
    owner (kernel/user_namespace.c:466-473): for uid 4294967295, which no
    namespace maps, the overflow id, 65534 by default, and no other value;
    for uid 1000 in the initial namespace, 1000. *)
Example stat_invalid_owner_overflow :
  fstat_o c0 (W_owned 4294967295 0) (o_stat 65534 0)
  /\ (forall v, munged_ok (W_owned 4294967295 0) c0 false 4294967295 v = Z.eqb v 65534)
  /\ fstat_o c0 (W_owned 1000 0) (o_stat 1000 0)
  /\ (forall v, munged_ok (W_owned 1000 0) c0 false 1000 v = Z.eqb v 1000).
Proof.
  split; [vm_compute; exists (o_stat 65534 0); repeat split; vm_compute; reflexivity |].
  split; [intro v; vm_compute; reflexivity |].
  split; [vm_compute; exists (o_stat 1000 0); repeat split; vm_compute; reflexivity |].
  intro v; vm_compute; reflexivity.
Qed.

(** An fstat of descriptor 3, open on "other" (owner 5000:5000, mode
    0644), by the caller in namespace 2, answered with [bs]. *)
Definition other_stat (uid gid : Z) : list byte :=
  Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 8 ++ Z_to_le_bytes 4 33188 ++ Z_to_le_bytes 4 0
  ++ Z_to_le_bytes 4 uid ++ Z_to_le_bytes 4 gid ++ repeat (Z_to_bv 8 0) 96.
Definition fstat_other (st : NsState) (bs : list byte) : Prop :=
  fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (model_with [(3, 1%N)]) c_child
            (with_files st [(1%N, other_file)])
            (ans [] (Z_to_bv 64 0) [(Z_to_bv 64 BUF, bs)] (model_with [(3, 1%N)]) c_child
                 (with_files st [(1%N, other_file)])).

(** A launch that measured kernel.overflowuid as 1234 and
    kernel.overflowgid as 4321 ([Some (1234, 4321)]).  "o" owned by
    4294967295:4294967295, stated in the initial namespace, and "other"
    (5000:5000), stated in namespace 2, which maps neither id: st_uid 1234
    and st_gid 4321, and no other value (kernel/user_namespace.c:471-472,
    538-539; kernel/sys.c:184-202).  "o" owned by 1000:1000, stated in
    namespace 2, whose uid map holds kernel uid 1000 and whose gid map
    holds only kernel gid 1002: st_uid 0 and st_gid 4321. *)
Example stat_overflow_launch_value :
  fstat_o c0 (with_overflow (W_owned 4294967295 4294967295) (Some (1234, 4321))) (o_stat 1234 4321)
  /\ (forall v, munged_ok (with_overflow (W_owned 4294967295 4294967295) (Some (1234, 4321))) c0 false
                          4294967295 v = Z.eqb v 1234)
  /\ (forall v, munged_ok (with_overflow (W_owned 4294967295 4294967295) (Some (1234, 4321))) c0 true
                          4294967295 v = Z.eqb v 4321)
  /\ fstat_other (with_overflow W (Some (1234, 4321))) (other_stat 1234 4321)
  /\ fstat_o c_child (with_overflow (W_owned 1000 1000) (Some (1234, 4321))) (o_stat 0 4321)
  /\ (forall v, munged_ok (with_overflow (W_owned 1000 1000) (Some (1234, 4321))) c_child false 1000 v
                = Z.eqb v 0)
  /\ (forall v, munged_ok (with_overflow (W_owned 1000 1000) (Some (1234, 4321))) c_child true 1000 v
                = Z.eqb v 4321).
Proof.
  split; [vm_compute; exists (o_stat 1234 4321); repeat split; vm_compute; reflexivity |].
  split; [intro v; vm_compute; reflexivity |].
  split; [intro v; vm_compute; reflexivity |].
  split; [vm_compute; exists (other_stat 1234 4321); repeat split; vm_compute; reflexivity |].
  split; [vm_compute; exists (o_stat 0 4321); repeat split; vm_compute; reflexivity |].
  split; intro v; vm_compute; reflexivity.
Qed.

(** No answer where the tables do not decide the ids
    ([stat_ids_decided]): a caller whose user namespace the tables do not
    hold (Linux gives every task a user namespace with its maps; the model
    showed 65534 for both ids before), and a launch value outside 0 to
    65535, which no host can hold (kernel/sys.c:184-202). *)
Example stat_ids_undecided :
  fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (model_with [(3, 1%N)]) c0
            (o_open (with_userns (W_owned 1000 0) [])) EUnmodeled
  /\ fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (model_with [(3, 1%N)]) c0
               (o_open (with_overflow (W_owned 4294967295 0) (Some (65536, 0)))) EUnmodeled.
Proof. split; vm_compute; reflexivity. Qed.

(** No answer for an owner id outside 0 to 4294967295 ([kid_in_range]):
    [kuid_t] and [kgid_t] hold a 32-bit id (include/linux/uidgid_types.h:7-13,
    include/linux/types.h:37-38), so no inode or task has one, and in the
    initial namespace no 4 bytes at offset 24 or 28 show one.  "o" owned
    by 4294967296:0 and by 1000:-1; the caller's own procfs task directory
    (mount 3, pid 42), owned by the task's euid and egid ([loc_attr]),
    under an euid of 4294967296.  The same directory under euid 1000 and
    egid 0 shows st_uid 1000 and st_gid 0. *)
Definition proc_dir_file : NsFile :=
  mkNsFile (NfDir (LProcTask 3 42 []) 0) (O_LARGEFILE + O_DIRECTORY) cred0.
Definition euid_model (u : Z) : Model :=
  with_creds (mkCreds (Z_to_bv 64 u) (Z_to_bv 64 u) (Z_to_bv 64 u) (Z_to_bv 64 0) (Z_to_bv 64 0)
                      (Z_to_bv 64 0) [])
             (model_with [(3, 1%N)]).
Definition proc_dir_stat : list byte :=
  Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 1 ++ Z_to_le_bytes 4 16749 ++ Z_to_le_bytes 4 0
  ++ Z_to_le_bytes 4 1000 ++ Z_to_le_bytes 4 0 ++ repeat (Z_to_bv 8 0) 96.

Example stat_owner_out_of_range :
  fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (model_with [(3, 1%N)]) c0
            (o_open (W_owned 4294967296 0)) EUnmodeled
  /\ fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (model_with [(3, 1%N)]) c0
               (o_open (W_owned 1000 (-1))) EUnmodeled
  /\ fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (euid_model 4294967296) c0
               (with_open [(1%N, proc_dir_file)]) EUnmodeled
  /\ fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (euid_model 1000) c0
               (with_open [(1%N, proc_dir_file)])
               (ans [] (Z_to_bv 64 0) [(Z_to_bv 64 BUF, proc_dir_stat)] (euid_model 1000) c0
                    (with_open [(1%N, proc_dir_file)])).
Proof.
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  vm_compute. exists proc_dir_stat. repeat split; vm_compute; reflexivity.
Qed.

(** The same two ids under [None] (the host may write the sysctls during
    the run): any value from 0 to 65535 (kernel/sys.c:191-192). *)
Example stat_overflow_unknown :
  fstat_o c0 (with_overflow (W_owned 4294967295 0) None) (o_stat 4242 0)
  /\ (forall v, munged_ok (with_overflow (W_owned 4294967295 0) None) c0 false 4294967295 v
                = (0 <=? v) && (v <=? 65535))
  /\ (forall v, munged_ok (with_overflow W None) c_child false 5000 v = (0 <=? v) && (v <=? 65535)).
Proof.
  split; [vm_compute; exists (o_stat 4242 0); repeat split; vm_compute; reflexivity |].
  split; intro v; vm_compute; reflexivity.
Qed.

(** A mapped id stays exact under [None].  A caller in user namespace 3,
    whose uid map is "0 1000 1" and whose gid map is "0 1000 1", stats "o"
    owned by uid 1000 and gid 2000: st_uid is exactly 0 ([from_kuid],
    kernel/user_namespace.c:441-445), st_gid any value from 0 to 65535
    ([from_kgid_munged], 533-541). *)
Definition one_user : UserNs :=
  uns 3 (Some 1%positive) 1 (Some [mkExtent 0 1000 1]) (Some [mkExtent 0 1000 1]).
Definition c_one : NsCtx := ctx_at 3 no_caps (1%positive, 1%positive) (1%positive, 2%positive).
Definition W_mixed : NsState :=
  with_overflow (with_userns (W_owned 1000 2000) [root_user; child_user; one_user]) None.

Example stat_mixed_unknown :
  fstat_o c_one W_mixed (o_stat 0 4242)
  /\ (forall v, munged_ok W_mixed c_one false 1000 v = Z.eqb v 0)
  /\ (forall v, munged_ok W_mixed c_one true 2000 v = (0 <=? v) && (v <=? 65535)).
Proof.
  split; [vm_compute; exists (o_stat 0 4242); repeat split; vm_compute; reflexivity |].
  split; intro v; vm_compute; reflexivity.
Qed.

(* ---- statfs, fstatfs --------------------------------------------------- *)

(** The read-only, nosuid, nodev mount: f_flags ST_VALID|ST_RDONLY|
    ST_NOSUID|ST_NODEV (39), plus any atime bits; the tmpfs magic. *)
Example statfs_held_flags :
  held_f_flags (mnt 4 (Some 1%positive) 5 40 4 ro_nosuid_nodev) (sb 4 40 SbTmpfs 16914836) = 39.
Proof. vm_compute. reflexivity. Qed.

Definition statfs_bytes (flags : Z) : list byte :=
  Z_to_le_bytes 8 16914836 ++ repeat (Z_to_bv 8 0) 72 ++ Z_to_le_bytes 8 flags ++ repeat (Z_to_bv 8 0) 32.

Example statfs_admits_relatime :
  statfs_arm (call 43 [PATH; BUF] (path_mem s_ro) (wmem 120)) m3 c0 W
             (ans [(Z_to_bv 64 PATH, 4%nat)] (Z_to_bv 64 0) [(Z_to_bv 64 BUF, statfs_bytes (39 + 4096))]
                  m3 c0 W).
Proof. vm_compute. exists (statfs_bytes (39 + 4096)). repeat split; vm_compute; reflexivity. Qed.

(** A value without ST_NOSUID is not one the model admits. *)
Example statfs_missing_nosuid :
  Z.eqb (Z.land 37 (Z.lnot ST_UNHELD))
        (held_f_flags (mnt 4 (Some 1%positive) 5 40 4 ro_nosuid_nodev) (sb 4 40 SbTmpfs 16914836))
  = false.
Proof. vm_compute. reflexivity. Qed.

Example fstatfs_bad_fd :
  fstatfs_arm (call 44 [9; BUF] (fun _ => None) (wmem 120)) m3 c0 W (ns_errno EBADF m3 c0 W).
Proof. vm_compute. reflexivity. Qed.

(** fstatfs accepts an O_PATH descriptor and reports its tmpfs magic and
    ST_VALID flags. *)
Example fstatfs_path :
  fstatfs_arm (call 44 [3; BUF] (fun _ => None) (wmem 120)) m_dir3 c0 W_dir3
              (ans [] (Z_to_bv 64 0) [(Z_to_bv 64 BUF, statfs_bytes 32)] m_dir3 c0 W_dir3).
Proof. vm_compute. exists (statfs_bytes 32). repeat split; vm_compute; reflexivity. Qed.

(* ---- readlinkat -------------------------------------------------------- *)

Definition readlink_in (dfd : Z) (p : list Z) (size : Z) : SyscallInput :=
  call 78 [dfd; PATH; BUF; size] (path_mem p) (wmem 64).

Definition exists_file : NsFile := mkNsFile (NfFile (LDentry 2 21) 0) O_LARGEFILE cred0.

(** /proc/self/fd/3 reads as the path of descriptor 3's file. *)
Example readlinkat_fd_link :
  writes_of (readlinkat_fn (readlink_in CWD s_fd3 64) (model_with [(3, 1%N)]) c0
                           (with_open [(1%N, exists_file)]))
  = Some [(BUF, s_tmp_exists)].
Proof. vm_compute. reflexivity. Qed.

(** A link's target, cut to the size, with no NUL. *)
Example readlinkat_cut :
  writes_of (readlinkat_fn (readlink_in CWD s_link 2) m3 c0 W) = Some [(BUF, [102; 105])]
  /\ ret_of (readlinkat_fn (readlink_in CWD s_link 2) m3 c0 W) = Some 2.
Proof. split; vm_compute; reflexivity. Qed.

(** A size of 0: EINVAL; a file that is no link: EINVAL; an empty name on
    a descriptor that is no link: ENOENT. *)
Example readlinkat_zero_size : ret_of (readlinkat_fn (readlink_in CWD s_link 0) m3 c0 W) = Some (-22).
Proof. vm_compute. reflexivity. Qed.
Example readlinkat_not_link : ret_of (readlinkat_fn (readlink_in CWD s_file 64) m3 c0 W) = Some (-22).
Proof. vm_compute. reflexivity. Qed.
Example readlinkat_empty_not_link :
  ret_of (readlinkat_fn (readlink_in 3 [] 64) m_dir3 c0 W_dir3) = Some (-2).
Proof. vm_compute. reflexivity. Qed.

(** /proc/self itself is a link to the caller's tgid in the procfs's pid
    namespace ([proc_self_get_link], fs/proc/self.c): "42", cut to the
    size, no NUL. *)
Example readlinkat_proc_self :
  writes_of (readlinkat_fn (readlink_in CWD s_self 64) m3 c0 W) = Some [(BUF, [52; 50])]
  /\ ret_of (readlinkat_fn (readlink_in CWD s_self 64) m3 c0 W) = Some 2
  /\ writes_of (readlinkat_fn (readlink_in CWD s_self 1) m3 c0 W) = Some [(BUF, [52])].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** A caller with no pid in the procfs's pid namespace: ENOENT. *)
Definition c_nopid : NsCtx := with_caps (with_cwd init_nsctx (1%positive, 2%positive)) no_caps.
Example readlinkat_proc_self_no_pid :
  ret_of (readlinkat_fn (readlink_in CWD s_self 64) m3 c_nopid W) = Some (-2).
Proof. vm_compute. reflexivity. Qed.

(* ---- getcwd ------------------------------------------------------------ *)

(** The cwd's path with its NUL; ERANGE when it does not fit;
    "(unreachable)" before a cwd outside the root. *)
Example getcwd_home :
  writes_of (getcwd_fn (call 17 [BUF; 64] (fun _ => None) (wmem 64)) m3 c0 W)
  = Some [(BUF, s_home ++ [0])].
Proof. vm_compute. reflexivity. Qed.
Example getcwd_erange : ret_of (getcwd_fn (call 17 [BUF; 3] (fun _ => None) (wmem 64)) m3 c0 W) = Some (-34).
Proof. vm_compute. reflexivity. Qed.
Example getcwd_unreachable :
  writes_of (getcwd_fn (call 17 [BUF; 64] (fun _ => None) (wmem 64)) m3
                       (ctx_at 1 no_caps (2%positive, 20%positive) (1%positive, 2%positive)) W)
  = Some [(BUF, [40; 117; 110; 114; 101; 97; 99; 104; 97; 98; 108; 101; 41] ++ s_home ++ [0])].
Proof. vm_compute. reflexivity. Qed.

(** Mount 6 covers mount 2's root. An event received by mount 2 can
    detach mount 6, changing the upward path without touching the procfs
    walk used to read /proc/self/cwd. *)
Definition path_world (parent_peer start_peer : option positive) (gs : list positive) : NsState :=
  with_open_groups
    (with_mounts W
      (map (fun mt => if Pos.eqb (mnt_id mt) 2 then mnt_with_peer mt parent_peer else mt)
           (ns_mounts W) ++
       [mnt_with_peer (mnt 6 (Some 2%positive) 20 20 2 no_flags) start_peer])) gs.
Definition path_ctx : NsCtx := with_cwd c0 (6%positive, 22%positive).
Definition path_getcwd : SyscallInput := call 17 [BUF; 64] (fun _ => None) (wmem 64).
Definition s_locked : list Z := [47; 116; 109; 112; 47; 108; 111; 99; 107; 101; 100].
Definition s_cwd : list Z := [47; 112; 114; 111; 99; 47; 115; 101; 108; 102; 47; 99; 119; 100].

Definition proc_path_world (gs : list positive) : NsState :=
  let st := path_world (Some 7%positive) None gs in
  with_mounts st
    (map (fun mt => if Pos.eqb (mnt_id mt) 3 then mnt_with_place mt (Some 2%positive) 20 else mt)
         (ns_mounts st)).

Example d_path_proc_open_parent_declines :
  d_path (proc_path_world [7%positive]) c0 (LProcTask 3 42 []) = None
  /\ d_path (proc_path_world []) c0 (LProcTask 3 42 []) = Some (bytes [47; 116; 109; 112; 47; 52; 50]).
Proof. split; vm_compute; reflexivity. Qed.

Example getcwd_open_parent_declines :
  getcwd_fn path_getcwd m3 path_ctx (path_world (Some 7%positive) None [7%positive]) = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.
Example readlinkat_cwd_open_parent_declines :
  readlinkat_fn (readlink_in CWD s_cwd 64) m3 path_ctx
               (path_world (Some 7%positive) None [7%positive]) = EUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** A closed chain, an unrelated open group, and a start mount open only
    to peer events keep the path: an event received at the start alone
    changes no upward step. Outside entry is a separate uncertainty. *)
Example getcwd_closed_chain_answers :
  writes_of (getcwd_fn path_getcwd m3 path_ctx (path_world (Some 7%positive) None []))
    = Some [(BUF, s_locked ++ [0])]
  /\ writes_of (getcwd_fn path_getcwd m3 path_ctx (path_world (Some 7%positive) None [8%positive]))
    = Some [(BUF, s_locked ++ [0])]
  /\ writes_of (getcwd_fn path_getcwd m3 path_ctx (path_world None (Some 7%positive) [7%positive]))
    = Some [(BUF, s_locked ++ [0])].
Proof. repeat split; vm_compute; reflexivity. Qed.
Example readlinkat_cwd_closed_chain_answers :
  writes_of (readlinkat_fn (readlink_in CWD s_cwd 64) m3 path_ctx
                          (path_world (Some 7%positive) None [])) = Some [(BUF, s_locked)]
  /\ writes_of (readlinkat_fn (readlink_in CWD s_cwd 64) m3 path_ctx
                            (path_world (Some 7%positive) None [8%positive])) = Some [(BUF, s_locked)]
  /\ writes_of (readlinkat_fn (readlink_in CWD s_cwd 64) m3 path_ctx
                            (path_world None (Some 7%positive) [7%positive])) = Some [(BUF, s_locked)].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** A private cwd mount can be moved by an outside task. The old parent
    edges may still say /a while Linux prints /b; neither is decided. *)
Definition entered_path_world : NsState :=
  with_entered_mntns (path_world None None []) [1%positive].

Example entered_private_cwd_declines :
  getcwd_fn path_getcwd m3 path_ctx entered_path_world = EUnmodeled
  /\ d_path entered_path_world path_ctx (LDentry 6 22) = None
  /\ d_path entered_path_world c0 (LProcTask 3 42 []) = None.
Proof. repeat split; vm_compute; reflexivity. Qed.

Example entered_root_cwd_fd_path_readlink_declines :
  readlinkat_fn (readlink_in CWD s_cwd 64) m3 path_ctx entered_path_world = EUnmodeled
  /\ d_path entered_path_world (with_root path_ctx (6%positive, 22%positive))
            (LDentry 6 22) = None
  /\ readlinkat_fn (readlink_in CWD (s_self ++ [47; 114; 111; 111; 116]) 64)
       m3 path_ctx entered_path_world = EUnmodeled
  /\ readlinkat_fn (readlink_in CWD s_fd3 64) (model_with [(3, 1%N)]) path_ctx
       (with_files entered_path_world [(1%N, mkNsFile (NfPath (LDentry 6 22)) O_PATH cred0)])
       = EUnmodeled.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** A table-level guard control, not a Linux-reachable topology: even an
    inconsistent cross-namespace parent edge must not bypass the climb's
    uncertainty check. Checking only the start namespace would miss it. *)
Definition entered_parent_world : NsState :=
  with_entered_mntns
    (with_mounts (path_world None None [])
      (map (fun mt => if Pos.eqb (mnt_id mt) 6 then mnt_with_ns mt 2 else mt)
           (ns_mounts (path_world None None [])))) [1%positive].

Example entered_parent_path_declines :
  d_path entered_parent_world path_ctx (LDentry 6 22) = None.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions entered_private_cwd_declines.

(** Empty-path descriptors to the procfs links bypass pathname traversal,
    so each case reaches link_text and then the guarded d_path. *)
Definition link_fd_world (name : list (list byte)) : NsState :=
  with_files entered_path_world
    [(1%N, mkNsFile (NfPath (LProcTask 3 42 name)) O_PATH cred0);
     (2%N, mkNsFile (NfPath (LDentry 6 22)) O_PATH cred0)].
Definition link_fd_model : Model := model_with [(3, 1%N); (4, 2%N)].

Example entered_empty_path_proc_links_decline :
  readlinkat_fn (readlink_in 3 [] 64) link_fd_model path_ctx
    (link_fd_world [proc_cwd_name]) = EUnmodeled
  /\ readlinkat_fn (readlink_in 3 [] 64) link_fd_model path_ctx
    (link_fd_world [proc_root_name]) = EUnmodeled
  /\ readlinkat_fn (readlink_in 3 [] 64) link_fd_model path_ctx
    (link_fd_world [proc_fd_name; bytes [52]]) = EUnmodeled.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Two concrete host-move outcomes for the same private cwd mount. *)
Definition moved_private_world (at_b : bool) : NsState :=
  let st := path_world None None [] in
  let st := with_dentries st (ns_dentries st ++
    [dent 90 1 (Some 1%positive) (bytes [97]) 90;
     dent 91 1 (Some 1%positive) (bytes [98]) 91]) in
  with_mounts st (map (fun mt => if Pos.eqb (mnt_id mt) 6
                     then mnt_with_place mt (Some 1%positive) (if at_b then 91 else 90) else mt)
                     (ns_mounts st)).

Definition moved_private_ctx : NsCtx := with_cwd c0 (6%positive, 20%positive).

Example moved_private_exact_controls :
  d_path (moved_private_world false) moved_private_ctx (LDentry 6 20) = Some (bytes [47; 97])
  /\ d_path (moved_private_world true) moved_private_ctx (LDentry 6 20) = Some (bytes [47; 98]).
Proof. split; vm_compute; reflexivity. Qed.

Example moved_private_uncertainty_declines : forall at_b,
  getcwd_fn path_getcwd m3 moved_private_ctx
    (with_entered_mntns (moved_private_world at_b) [1%positive]) = EUnmodeled
  /\ d_path (with_entered_mntns (moved_private_world at_b) [1%positive])
            moved_private_ctx (LDentry 6 20) = None
  /\ d_path (with_entered_mntns (moved_private_world at_b) [1%positive])
            moved_private_ctx (LProcTask 3 42 []) = None.
Proof. intros []; repeat split; vm_compute; reflexivity. Qed.

Print Assumptions path_open_closed.
Print Assumptions entered_root_cwd_fd_path_readlink_declines.
Print Assumptions entered_parent_path_declines.
Print Assumptions entered_empty_path_proc_links_decline.
Print Assumptions moved_private_exact_controls.
Print Assumptions moved_private_uncertainty_declines.

(* ---- chdir, fchdir ----------------------------------------------------- *)

Definition chdir_in (p : list Z) : SyscallInput := call 49 [PATH] (path_mem p) (fun _ => None).

(** chdir moves the cwd to the root of the mount on /tmp; a file is
    ENOTDIR; a directory the caller may not search is EACCES. *)
Example chdir_tmp :
  option_map cx_cwd (ctx_of (chdir_fn (chdir_in s_tmp) m3 c0 W)) = Some (2%positive, 20%positive).
Proof. vm_compute. reflexivity. Qed.
Example chdir_file : ret_of (chdir_fn (chdir_in s_file) m3 c0 W) = Some (-20).
Proof. vm_compute. reflexivity. Qed.
Example chdir_denied : ret_of (chdir_fn (chdir_in s_secret) m3 c0 W) = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** [path_permission] with MAY_EXEC|MAY_CHDIR (fs/open.c:565; fchdir's
    [file_permission], 592) reaches [generic_permission]: a caller in the
    initial namespace with CAP_DAC_OVERRIDE moves into the mode-0000
    directory "d" owned by 2000:0, but not when its uid is 4294967295,
    which the initial namespace does not map
    ([privileged_wrt_inode_uidgid], kernel/capability.c:455-461): EACCES. *)
Definition s_d : list Z := [47; 100].                                       (* /d *)
Example chdir_invalid_owner_not_capable :
  ret_of (chdir_fn (chdir_in s_d) m3 (c_caps dac_override_caps) (W_owned 4294967295 0)) = Some (-13)
  /\ ret_of (chdir_fn (chdir_in s_d) m3 (c_caps dac_override_caps) (W_owned 2000 0)) = Some 0.
Proof. vm_compute. split; reflexivity. Qed.

(** fchdir accepts an O_PATH directory; a file is ENOTDIR; a number that
    is not open is EBADF. *)
Example fchdir_path_dir :
  option_map cx_cwd (ctx_of (fchdir_fn (call 50 [3] (fun _ => None) (fun _ => None)) m_dir3 c0 W_dir3))
  = Some (2%positive, 20%positive).
Proof. vm_compute. reflexivity. Qed.
Example fchdir_file :
  ret_of (fchdir_fn (call 50 [3] (fun _ => None) (fun _ => None)) (model_with [(3, 1%N)]) c0
                    (with_open [(1%N, file1)])) = Some (-20).
Proof. vm_compute. reflexivity. Qed.
Example fchdir_bad : ret_of (fchdir_fn (call 50 [9] (fun _ => None) (fun _ => None)) m3 c0 W) = Some (-9).
Proof. vm_compute. reflexivity. Qed.

(* ---- getdents64 on /proc/self/fd ---------------------------------------- *)

(** Descriptors 0, 1, 2 and 5, where 5 is the task's own fd directory. *)
Definition fd_dir_file : NsFile :=
  mkNsFile (NfDir (LProcTask 3 42 [bytes [102; 100]]) 0) (O_LARGEFILE + O_DIRECTORY) cred0.
Definition m_fd5 : Model := model_with [(5, 1%N)].
Definition W_fd5 : NsState := with_open [(1%N, fd_dir_file)].

(** Each record's offset from the buffer, length, type and name. *)
Definition dent_view (ws : option (list (Z * list Z))) : option (list (Z * Z * Z * list Z)) :=
  option_map (map (fun p => let bs := snd p in
                            (fst p - BUF, nth 16 bs 0 + 256 * nth 17 bs 0, nth 18 bs 0,
                             firstn (length bs - 20) (skipn 19 bs)))) ws.

Definition dents_in (count : Z) : SyscallInput :=
  call 61 [5; BUF; count] (fun _ => None) (wmem 256).

Definition no_choice (_ : nat) : Z * Z := (0, 0).

(** ".", "..", then 0, 1, 2 and 5, each in a 24-byte record. *)
Example getdents64_fd_dir :
  dent_view (writes_of (getdents64_out (dents_in 256) m_fd5 c0 W_fd5 1%N fd_dir_file
                                       (LProcTask 3 42 [bytes [102; 100]]) 0 no_choice 100))
  = Some [(0, 24, 4, [46]); (24, 24, 4, [46; 46]); (48, 24, 10, [48]); (72, 24, 10, [49]);
          (96, 24, 10, [50]); (120, 24, 10, [53])]
  /\ ret_of (getdents64_out (dents_in 256) m_fd5 c0 W_fd5 1%N fd_dir_file
                            (LProcTask 3 42 [bytes [102; 100]]) 0 no_choice 100) = Some 144.
Proof. split; vm_compute; reflexivity. Qed.

Example getdents64_arm_admits :
  getdents64_arm (dents_in 256) m_fd5 c0 W_fd5
                 (getdents64_out (dents_in 256) m_fd5 c0 W_fd5 1%N fd_dir_file
                                 (LProcTask 3 42 [bytes [102; 100]]) 0 no_choice 100).
Proof. vm_compute. exists no_choice, 100. split; [reflexivity | vm_compute; reflexivity]. Qed.

(** A count too small for the first record: EINVAL. *)
Example getdents64_small_count :
  ret_of (getdents64_out (dents_in 10) m_fd5 c0 W_fd5 1%N fd_dir_file
                         (LProcTask 3 42 [bytes [102; 100]]) 0 no_choice 100) = Some (-22).
Proof. vm_compute. reflexivity. Qed.

(** A first fd entry fault advances the directory position before filldir64
    reports EFAULT. *)
Definition fd_dir_at_two : NsFile :=
  mkNsFile (NfDir (LProcTask 3 42 [bytes [102; 100]]) 2) (O_LARGEFILE + O_DIRECTORY) cred0.
Definition dents_fault : SyscallInput :=
  call 61 [5; 18446744073709551615; 256] (fun _ => None) (fun _ => None).
Example getdents64_fault_advances_position :
  match st_of (getdents64_out dents_fault m_fd5 c0 W_fd5 1%N fd_dir_at_two
                              (LProcTask 3 42 [bytes [102; 100]]) 2 no_choice 100) with
  | Some s =>
      match lookup_file (ns_files s) 1%N with
      | Some f => match nf_kind f with NfDir _ p => p =? 2 | _ => false end
      | None => false
      end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** The rows of the exported table: getcwd, openat, openat2, and the five
    calls that read a name and walk it; fcntl, fstatfs, fchdir, close and
    fstat have no environment refusal, and getdents64 none on the task's
    own fd directory (on a descriptor of the released model the released
    filter applies, [Spec.released_fd_call]). *)
Example file_injected_numbers :
  map ni_no file_injected = [17; 56; 437; 43; 48; 49; 78; 79].
Proof. vm_compute. reflexivity. Qed.

(* ---- the forced-only filter on openat and openat2 ---------------------- *)

(** An answer's effect. *)
Definition eff_of (o : ext_outcome) : SyscallEffect :=
  match o with EOk eff _ _ _ _ => eff | EUnmodeled => mkEffect (Z_to_bv 64 0) [] [] end.

(** The refusal [e] the environment injects after the answer [o]: [o]'s
    copy-ins, the errno, nothing written ([Arm.injected_after]). *)
Definition injected_eff (o : ext_outcome) (e : Z) : SyscallEffect :=
  with_copyins (eff_copyins (eff_of o)) (mkEffect (errno_ret e) [] []).

(** The task is outside the released world in both worlds below, so the
    namespace arms answer and [Spec.ns_refusal_eff] is the namespace filter
    of an answer's effect, which [Spec.ns_refusal] applies to the outcome
    ([Spec.ns_refusal_outcome_eff]). *)
Example c0_outside_released : flat_view c0 W = false /\ flat_view c0 W_dir3 = false.
Proof. split; vm_compute; reflexivity. Qed.

(** openat("/tmp/nope", O_RDONLY): tmpfs has no "nope", so the walk answers
    ENOENT.  Under forced-only the injected ENOMEM is filtered (ENOENT is an
    answer that matches no pair of [openat_injected]) and ENOENT is not. *)
Definition s_tmp_nope : list Z := s_tmp ++ [47; 110; 111; 112; 101].
Definition open_nope : SyscallInput := open_in s_tmp_nope 0 0.
Definition nope_answer : ext_outcome := openat_fn open_nope m3 c0 W.

Lemma nope_answer_eq : nope_answer = EOk (eff_of nope_answer) m3 c0 W [].
Proof. vm_compute. reflexivity. Qed.

Lemma ns_spec_open_nope : forall o,
  ns_spec open_nope m3 c0 W o <-> with_injected (ni_errno openat_injected) openat_arm open_nope m3 c0 W o.
Proof.
  intros o. unfold ns_spec. replace (flat_view c0 W) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma open_nope_filter : forall eff,
  ns_refusal_eff forced_only_cfg open_nope m3 c0 W eff
  <-> ns_refusal_off_b forced_only_cfg open_nope (eff_ret eff) = true
      /\ exists eff' m' ctx' st' evs',
           ns_spec open_nope m3 c0 W (EOk eff' m' ctx' st' evs')
           /\ ns_witness open_nope (eff_ret eff) (eff_ret eff') = true.
Proof. intros eff. apply ns_refusal_eff_ns. vm_compute. reflexivity. Qed.

Example openat_enoent_forced_only :
  ret_of nope_answer = Some (-2)
  /\ ns_spec open_nope m3 c0 W (EOk (injected_eff nope_answer ENOMEM) m3 c0 W [])
  /\ ns_refusal_eff forced_only_cfg open_nope m3 c0 W (injected_eff nope_answer ENOMEM)
  /\ ~ ns_refusal_eff forced_only_cfg open_nope m3 c0 W (eff_of nope_answer).
Proof.
  split; [vm_compute; reflexivity|].
  split.
  { apply (proj2 (ns_spec_open_nope _)). right. exists nope_answer. split; [exact eq_refl|].
    rewrite nope_answer_eq. unfold injected_after. exists ENOMEM. split; reflexivity. }
  split.
  - apply (proj2 (open_nope_filter _)). split; [vm_compute; reflexivity|].
    exists (eff_of nope_answer), m3, c0, W, []. split.
    + rewrite <- nope_answer_eq. apply (proj2 (ns_spec_open_nope _)). left. exact eq_refl.
    + vm_compute. reflexivity.
  - intros H. apply (proj1 (open_nope_filter _)) in H. destruct H as [Hoff _].
    vm_compute in Hoff. discriminate Hoff.
Qed.

(** openat2("../nope", RESOLVE_IN_ROOT) from tmpfs's root: the walk takes a
    scoped ".." and answers ENOENT, so EAGAIN is also an answer.  Under
    forced-only EAGAIN, an interruption of [openat2_injected], is filtered
    and ENOENT is not. *)
Definition up_nope : list Z := [46; 46; 47; 110; 111; 112; 101].
Definition open2_nope : SyscallInput := open2 3 up_nope 0 RESOLVE_IN_ROOT 24.
Definition nope2 : (ext_outcome * list (word * nat)) * bool := openat2_fn open2_nope m_dir3 c0 W_dir3.
Definition nope2_eagain : ext_outcome := err (snd (fst nope2)) EAGAIN m_dir3 c0 W_dir3.

Lemma nope2_eq : fst (fst nope2) = EOk (eff_of (fst (fst nope2))) m_dir3 c0 W_dir3 [].
Proof. vm_compute. reflexivity. Qed.

Lemma ns_spec_open2_nope : forall o,
  ns_spec open2_nope m_dir3 c0 W_dir3 o
  <-> with_injected (pairs_errno open_pairs) openat2_arm open2_nope m_dir3 c0 W_dir3 o.
Proof.
  intros o. unfold ns_spec. replace (flat_view c0 W_dir3) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma open2_nope_filter : forall eff,
  ns_refusal_eff forced_only_cfg open2_nope m_dir3 c0 W_dir3 eff
  <-> ns_refusal_off_b forced_only_cfg open2_nope (eff_ret eff) = true
      /\ exists eff' m' ctx' st' evs',
           ns_spec open2_nope m_dir3 c0 W_dir3 (EOk eff' m' ctx' st' evs')
           /\ ns_witness open2_nope (eff_ret eff) (eff_ret eff') = true.
Proof. intros eff. apply ns_refusal_eff_ns. vm_compute. reflexivity. Qed.

Example openat2_dotdot_eagain_forced_only :
  ret_of (fst (fst nope2)) = Some (-2) /\ snd nope2 = true
  /\ ns_spec open2_nope m_dir3 c0 W_dir3 nope2_eagain
  /\ ns_refusal_eff forced_only_cfg open2_nope m_dir3 c0 W_dir3 (eff_of nope2_eagain)
  /\ ~ ns_refusal_eff forced_only_cfg open2_nope m_dir3 c0 W_dir3 (eff_of (fst (fst nope2))).
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split.
  { apply (proj2 (ns_spec_open2_nope _)). left. right.
    split; [vm_compute; reflexivity | exact eq_refl]. }
  split.
  - apply (proj2 (open2_nope_filter _)). split; [vm_compute; reflexivity|].
    exists (eff_of (fst (fst nope2))), m_dir3, c0, W_dir3, []. split.
    + rewrite <- nope2_eq. apply (proj2 (ns_spec_open2_nope _)). left. left. exact eq_refl.
    + vm_compute. reflexivity.
  - intros H. apply (proj1 (open2_nope_filter _)) in H. destruct H as [Hoff _].
    vm_compute in Hoff. discriminate Hoff.
Qed.

(* ---- inodes whose uid or gid is INVALID ------------------------------- *)

(** [inode_permission] refuses every access with MAY_WRITE to an inode
    whose uid or gid is INVALID (4294967295) with EACCES, after
    [sb_permission]'s EROFS and before the mode bits are read
    ([HAS_UNMAPPED_ID], fs/namei.c:589-590; include/linux/fs.h:2587-2591).
    A host (local disk) file system can hold such an inode: an on-disk uid
    or gid 0xFFFFFFFF reads as INVALID ([i_uid_write] and [i_gid_write],
    include/linux/fs.h:1609-1617, called by ext4's [__ext4_iget],
    fs/ext4/inode.c:5302-5303; the initial user namespace maps 0 to
    4294967294 only, kernel/user.c:38-43, so [make_kuid] gives -1,
    kernel/user_namespace.c:333, 425).
    On the root's host superblock, in the directory "hd" (0755, owned by
    1000:1002): "u", a regular file 0666 owned by 4294967295:1002, and
    "g", a regular file 0644 owned by 1000:4294967295.  Mount 6 binds "hd"
    on "rb", read-only, nosuid and nodev; the superblock stays writable.
    Mount 7, on "rs", is a second host file system whose superblock is
    read-only (SB_RDONLY); its root (0755, owned by 1000:1002) holds "u"
    as "hd" does.  The caller (fsuid 1000, fsgid 1002) has the write by
    the mode bits of each. *)
Definition W_unmapped : NsState :=
  let st := with_mounts W (ns_mounts W ++ [mnt 6 (Some 1%positive) 26 23 1 ro_nosuid_nodev;
                                           mnt 7 (Some 1%positive) 27 60 6 no_flags]) in
  let st := with_sbs st (ns_sbs W ++ [sb_ro 6 60 SbHost 61267]) in
  with_tree st
    (ns_dentries W ++
     [dent 23 1 (Some 1%positive) (bytes [104; 100]) 23;
      dent 24 1 (Some 23%positive) (bytes [117]) 24;
      dent 25 1 (Some 23%positive) (bytes [103]) 25;
      dent 26 1 (Some 1%positive) (bytes [114; 98]) 26;
      dent 27 1 (Some 1%positive) (bytes [114; 115]) 27;
      dent 60 6 None [] 60;
      dent 61 6 (Some 60%positive) (bytes [117]) 61])
    (ns_inodes W ++ [dir 23 493 1000 1002; reg 24 438 invalid_id 1002; reg 25 420 1000 invalid_id;
                     dir 26 493 1000 1002; dir 27 493 1000 1002; dir 60 493 1000 1002;
                     reg 61 438 invalid_id 1002]).

Definition s_hd_u : list Z := [47; 104; 100; 47; 117].                      (* /hd/u *)
Definition s_hd_g : list Z := [47; 104; 100; 47; 103].                      (* /hd/g *)
Definition s_rb_u : list Z := [47; 114; 98; 47; 117].                       (* /rb/u *)
Definition s_rs_u : list Z := [47; 114; 115; 47; 117].                      (* /rs/u *)

(** An open for writing ([may_open], fs/namei.c:3565, with [ACC_MODE]'s
    MAY_WRITE): EACCES, where it gave descriptor 3; an open for reading
    asks no MAY_WRITE and still gives descriptor 3. *)
Example openat_write_unmapped_owner :
  ret_of (openat_fn (open_in s_hd_u 1 0) m3 c0 W_unmapped) = Some (-13)
  /\ ret_of (openat_fn (open_in s_hd_u 0 0) m3 c0 W_unmapped) = Some 3.
Proof. split; vm_compute; reflexivity. Qed.

(** The same through openat2 (one [do_filp_open] for both calls). *)
Example openat2_write_unmapped_owner :
  ret_of (fst (fst (openat2_fn (open2 CWD s_hd_u 1 0 24) m3 c0 W_unmapped))) = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** faccessat W_OK ([do_faccessat], fs/open.c:509, mask [mode | MAY_ACCESS]):
    EACCES, where it answered 0, though the caller owns "g"; R_OK still
    answers 0. *)
Example faccessat_write_unmapped_group :
  ret_of (faccessat_fn (access_in s_hd_g 2) m3 c0 W_unmapped) = Some (-13)
  /\ ret_of (faccessat_fn (access_in s_hd_g 4) m3 c0 W_unmapped) = Some 0.
Proof. split; vm_compute; reflexivity. Qed.

(** On a read-only mount whose superblock is writable, [sb_permission]
    does not refuse (fs/namei.c:550, [sb_rdonly]), so the EACCES comes
    before the mount's EROFS: an open for writing ([may_open], 3973, runs
    before [vfs_open]'s [file_get_write_access], fs/open.c:926) and
    faccessat W_OK ([inode_permission] at fs/open.c:509, then
    [__mnt_is_readonly] at 523-524) of "rb/u" answer EACCES, where they
    answered EROFS. *)
Example unmapped_owner_before_readonly_mount :
  ret_of (openat_fn (open_in s_rb_u 1 0) m3 c0 W_unmapped) = Some (-13)
  /\ ret_of (faccessat_fn (access_in s_rb_u 2) m3 c0 W_unmapped) = Some (-13).
Proof. split; vm_compute; reflexivity. Qed.

(** On a read-only superblock, [sb_permission]'s EROFS (fs/namei.c:550-551,
    573-575) comes before the unmapped-owner EACCES (589-590): an open for
    writing ([may_open], 3973) and faccessat W_OK (fs/open.c:509) of
    "rs/u" answer EROFS, as before. *)
Example readonly_superblock_before_unmapped_owner :
  ret_of (openat_fn (open_in s_rs_u 1 0) m3 c0 W_unmapped) = Some (-30)
  /\ ret_of (faccessat_fn (access_in s_rs_u 2) m3 c0 W_unmapped) = Some (-30).
Proof. split; vm_compute; reflexivity. Qed.

(** An O_CREAT write open of the existing 0666 file "st/f" in the sticky
    world-writable "st", both on the host file system and owned by
    INVALID, by the caller with fsuid 1000: [may_open]'s
    [inode_permission] (3973, 589-590) refuses with EACCES, so Linux
    answers EACCES under every protected_regular value
    ([may_create_in_sticky], 1327-1329, or that [may_open]), and so does
    the model ([sticky_answer]), where it gave no answer. *)
Example openat_creat_write_sticky_unmapped_owners :
  ret_of (openat_fn (open_in s_st_f creat_write 438) m3 c0 (W_sticky invalid_id)) = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** A code-path check on a state Linux does not reach.  The model creates
    a file only in tmpfs, and Linux makes no tmpfs inode with an INVALID
    owner: a tmpfs root takes the uid= and gid= options, which must map
    (mm/shmem.c:4678, 4690), or the mounter's fsuid and fsgid (5365-5366,
    5155-5156); a new inode takes the creator's fsuid and fsgid, or a
    set-group-ID parent's gid ([inode_init_owner], fs/inode.c:2593-2605);
    chown refuses an INVALID id (fs/open.c:730-752, 775-778); the model
    has no idmapped mount.  [W] with "ud", a tmpfs directory 0777 owned by
    4294967295:4294967295 on /tmp: an O_CREAT open of a free name in it
    ([may_o_create], fs/namei.c:3622-3623, MAY_WRITE|MAY_EXEC on the
    directory) answers EACCES.  The walk's search of "ud" asks MAY_EXEC
    alone and passes. *)
Definition W_unmapped_tmpfs : NsState :=
  with_tree W
    (ns_dentries W ++ [dent 70 2 (Some 20%positive) (bytes [117; 100]) 70])
    (ns_inodes W ++ [dir 70 511 invalid_id invalid_id]).

Definition s_tmp_ud_new : list Z := s_tmp ++ [47; 117; 100; 47; 110; 101; 119].  (* /tmp/ud/new *)

Example openat_create_unmapped_dir :
  ret_of (openat_fn (open_in s_tmp_ud_new creat_excl 438) m3 c0 W_unmapped_tmpfs) = Some (-13).
Proof. vm_compute. reflexivity. Qed.

(** A code-path check on a state Linux does not reach.  The
    /proc/sys/user branch runs the same test before [proc_sys_permission]
    ([inode_permission], fs/namei.c:589-590, before [do_inode_permission]
    at 593).  Linux makes those inodes root's ([proc_sys_make_inode],
    fs/proc/proc_sysctl.c:490-493; the set's root has no [set_ownership],
    kernel/ucount.c:58-61), so only tables that hold such a file with an
    INVALID owner, as here, reach the refusal: the open for writing and
    faccessat W_OK that [user_sys_permission] grants with CAP_SYS_RESOURCE
    answer EACCES. *)
Definition W_user_sys_unmapped : NsState :=
  with_tree W
    (ns_dentries W_user_sys)
    (ns_inodes W ++ [dir 31 365 0 0; dir 32 365 0 0; reg 33 420 invalid_id 0]).

Example user_sys_write_unmapped_owner :
  ret_of (openat_fn (open_in s_max_user_namespaces 1 0) m3 (c_caps sys_resource_caps)
            W_user_sys_unmapped) = Some (-13)
  /\ ret_of (faccessat_fn (access_in s_max_user_namespaces 2) (with_creds uid0 m3)
               (c_caps sys_resource_caps) W_user_sys_unmapped) = Some (-13).
Proof. split; vm_compute; reflexivity. Qed.
