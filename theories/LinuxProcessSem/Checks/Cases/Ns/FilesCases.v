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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Mount Userns Walk Task Files.
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

Definition dir (i : positive) (perm uid gid : Z) : Inode := mkInode i IDir perm uid gid 0 [].
Definition reg (i : positive) (perm uid gid : Z) : Inode := mkInode i IReg perm uid gid 0 [].
Definition lnk (i : positive) (t : list byte) : Inode := mkInode i ILnk 511 1000 1002 0 t.

Definition dent (i s : positive) (parent : option positive) (name : list byte) (ino : positive)
    : Dentry := mkDentry i s parent name ino.

(** The one builder of each record that grows: a user namespace, a whole
    state, a task context. *)
Definition uns (i : positive) (parent : option positive) (level : nat)
    (umap gmap : option (list IdExtent)) : UserNs :=
  mkUserNs i parent level 0 umap gmap true false.

Definition state (users : list UserNs) (files : list (N * NsFile)) : NsState :=
  mkNsState
    [mnt 1 None 1 1 1 no_flags; mnt 2 (Some 1%positive) 3 20 2 no_flags;
     mnt 3 (Some 1%positive) 9 30 3 no_flags; mnt 4 (Some 1%positive) 5 40 4 ro_nosuid_nodev;
     mnt 5 (Some 1%positive) 10 50 5 noexec_flags]
    users [mkMntNs 1 1 1] [mkPidNs 1 None 1 0] []
    [sb 1 1 SbHost 61267; sb 2 20 SbTmpfs 16914836; sb 3 30 (SbProc 1) 40864;
     sb 4 40 SbTmpfs 16914836; sb 5 50 SbTmpfs 16914836]
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
     dent 51 5 (Some 50%positive) (bytes [114; 117; 110]) 51]
    [dir 1 493 1000 1002; dir 2 493 1000 1002; dir 3 493 1000 1002; reg 4 420 1000 1002;
     dir 5 493 1000 1002; lnk 6 (bytes [102; 105; 108; 101]); dir 7 448 2000 2000;
     reg 8 420 5000 5000; dir 9 493 1000 1002; dir 10 493 1000 1002;
     dir 20 511 0 0; reg 21 420 1000 1002; dir 22 493 0 0; dir 30 365 0 0;
     dir 40 511 0 0; reg 41 438 1000 1002; dir 50 511 0 0; reg 51 493 1000 1002]
    files.

Definition ctx_at (u : positive) (caps : CapSets) (root cwd : positive * positive) : NsCtx :=
  mkNsCtx u 1 1 1 [(1%positive, 42%Z)] root cwd 18 caps 0 [] false 0 1.

Definition root_user : UserNs := uns 1 None 0 None None.
(** A child user namespace mapping its 0 to kernel uid 1000 and gid 1002. *)
Definition child_user : UserNs :=
  uns 2 (Some 1%positive) 1 (Some [mkExtent 0 1000 1]) (Some [mkExtent 0 1002 1]).

Definition no_caps : CapSets := mkCaps 0 0 0 0 0.
Definition admin_caps : CapSets := mkCaps (2 ^ 21) (2 ^ 21) 0 0 0.

Definition c0 : NsCtx := ctx_at 1 no_caps (1%positive, 1%positive) (1%positive, 2%positive).

Definition cred0 : IdCred := mkIdCred 1 1000 1002 0.

Definition W : NsState := state [root_user; child_user] [].

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
  end.

(** The newest open file of an answer: 0 for O_PATH, 1 for a directory, 2
    for a file; its location; its [f_flags]. *)
Definition new_file (o : ext_outcome) : option (Z * (Z * Z * list (list Z)) * Z) :=
  match st_of o with
  | Some s => match ns_files s with
              | (_, f) :: _ => match nf_kind f with
                               | NfPath l => Some (0, loc_view l, nf_flags f)
                               | NfDir l _ => Some (1, loc_view l, nf_flags f)
                               | NfFile l _ => Some (2, loc_view l, nf_flags f)
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

(** The task's uid_map opens as a file at its procfs location. *)
Example openat_uid_map :
  new_file (openat_fn (open_in s_uid_map 0 0) m3 c0 W)
  = Some (2, (3, 42, [[117; 105; 100; 95; 109; 97; 112]]), O_LARGEFILE).
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
    overflow ids 65534; st_dev is superblock 1, st_ino inode 8. *)
Definition c_child : NsCtx := ctx_at 2 no_caps (1%positive, 1%positive) (1%positive, 2%positive).

Example fstat_fields_unmapped_owner :
  option_map (fun a => map (fun p => (Z.of_nat (fst p), map bv_unsigned (snd p))) (stat_fields W c_child a))
             (loc_attr m3 c_child W (LDentry 1 8))
  = Some [(0, [1; 0; 0; 0; 0; 0; 0; 0]); (8, [8; 0; 0; 0; 0; 0; 0; 0]); (16, [164; 129; 0; 0]);
          (24, [254; 255; 0; 0]); (28, [254; 255; 0; 0])].
Proof. vm_compute. reflexivity. Qed.

Definition stat_bytes : list byte :=
  Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 8 ++ Z_to_le_bytes 4 33188 ++ Z_to_le_bytes 4 0
  ++ Z_to_le_bytes 4 65534 ++ Z_to_le_bytes 4 65534 ++ repeat (Z_to_bv 8 0) 96.

Definition other_file : NsFile := mkNsFile (NfFile (LDentry 1 8) 0) O_LARGEFILE cred0.

Example fstat_admits_overflow_ids :
  fstat_arm (call 80 [3; BUF] (fun _ => None) (wmem 128)) (model_with [(3, 1%N)]) c_child
            (with_open [(1%N, other_file)])
            (ans [] (Z_to_bv 64 0) [(Z_to_bv 64 BUF, stat_bytes)] (model_with [(3, 1%N)]) c_child
                 (with_open [(1%N, other_file)])).
Proof. vm_compute. exists stat_bytes. split; vm_compute; reflexivity. Qed.

(** newfstatat with AT_EMPTY_PATH on an O_PATH descriptor stats its
    object; an unknown flag is EINVAL before the name's error. *)
Definition tmp_root_bytes : list byte :=
  Z_to_le_bytes 8 2 ++ Z_to_le_bytes 8 20 ++ Z_to_le_bytes 4 (16384 + 511) ++ Z_to_le_bytes 4 0
  ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 0 ++ repeat (Z_to_bv 8 0) 96.

Example newfstatat_empty_path :
  newfstatat_arm (call 79 [3; PATH; BUF; AT_EMPTY_PATH] (path_mem []) (wmem 128)) m_dir3 c0 W_dir3
                 (ans [(Z_to_bv 64 PATH, 1%nat)] (Z_to_bv 64 0) [(Z_to_bv 64 BUF, tmp_root_bytes)]
                      m_dir3 c0 W_dir3).
Proof. vm_compute. exists tmp_root_bytes. split; vm_compute; reflexivity. Qed.

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
