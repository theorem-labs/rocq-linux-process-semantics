(** * LinuxProcessSem.Checks.Cases.Ns.WalkCases — path walks in a small namespace

    Each example runs [Ns.Walk.walk] or [Ns.Walk.walk_parent] on one small
    world and states its exact result.  The world: mount 1 is the root (a
    host file system) with the directories home, covered, secret (mode 0700,
    uid 2000), proc, the file "file", and the links "link" (to
    home/target) and home/abslink (to /target).  Mount 2, a tmpfs, covers
    "covered"; mount 3, a procfs of pid namespace 1, covers "proc".  The
    task is uid 1000 with pid 42, root at mount 1's root and cwd at home. *)

From Stdlib Require Import List PArith ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount Userns Walk.
Import ListNotations.
Open Scope Z_scope.

Definition bytes (zs : list Z) : list byte := map (Z_to_bv 8) zs.

Definition no_flags : MountFlags := mkMountFlags false false false false.

Definition mnt (i : positive) (parent : option positive) (point root sb : positive) : Mount :=
  mkMount i 1 parent point root sb no_flags no_flags false false None None.

Definition sb (i root : positive) (k : SbKind) : SuperBlock :=
  mkSb i k 1 root false 0 false false false.

Definition dir (i : positive) (perm uid gid : Z) : Inode := mkInode i IDir perm uid gid 0 [].
Definition reg (i : positive) : Inode := mkInode i IReg 420 1000 1000 0 [].
Definition lnk (i : positive) (target : list byte) : Inode := mkInode i ILnk 511 1000 1000 0 target.

Definition dent (i sb : positive) (parent : option positive) (name : list byte) (ino : positive)
    : Dentry := mkDentry i sb parent name ino.

(** The one builder of each record that grows: a user namespace, a whole
    state, a task context. *)
Definition uns (i : positive) (parent : option positive) (level : nat)
    (umap gmap : option (list IdExtent)) : UserNs :=
  mkUserNs i parent level 0 umap gmap true false INT_MAX true.

Definition state (mounts : list Mount) (users : list UserNs) (mntns : list MntNs)
    (pidns : list PidNs) (sbs : list SuperBlock) (dentries : list Dentry) (inodes : list Inode)
    : NsState :=
  mkNsState mounts users mntns pidns [] sbs dentries inodes [] (ns_env empty_nsstate).

Definition ctx_at (u : positive) (caps : CapSets) (root : positive * positive) : NsCtx :=
  mkNsCtx u 1 1 1 [(1%positive, 42%Z)] root (1%positive, 2%positive) 18 caps 0 [] false 0 1.

Definition root_user : UserNs := uns 1 None 0 None None.

Definition s_home : list byte := bytes [104; 111; 109; 101].
Definition s_target : list byte := bytes [116; 97; 114; 103; 101; 116].
Definition s_file : list byte := bytes [102; 105; 108; 101].

Definition world : NsState :=
  state
    [mnt 1 None 1 1 1; mnt 2 (Some 1%positive) 3 20 2; mnt 3 (Some 1%positive) 9 30 3]
    [root_user]
    [mkMntNs 1 1 1 false]
    [mkPidNs 1 None 1 0]
    [sb 1 1 SbHost; sb 2 20 SbTmpfs; sb 3 30 (SbProc 1)]
    [dent 1 1 None [] 1;
     dent 2 1 (Some 1%positive) s_home 2;
     dent 3 1 (Some 1%positive) (bytes [99; 111; 118; 101; 114; 101; 100]) 3;
     dent 4 1 (Some 1%positive) s_file 4;
     dent 5 1 (Some 1%positive) (bytes [115; 101; 99; 114; 101; 116]) 5;
     dent 6 1 (Some 2%positive) s_target 6;
     dent 7 1 (Some 1%positive) (bytes [108; 105; 110; 107]) 7;
     dent 8 1 (Some 2%positive) (bytes [97; 98; 115; 108; 105; 110; 107]) 8;
     dent 9 1 (Some 1%positive) (bytes [112; 114; 111; 99]) 9;
     dent 20 2 None [] 20;
     dent 30 3 None [] 30]
    [dir 1 493 1000 1000; dir 2 493 1000 1000; dir 3 493 1000 1000;
     reg 4; dir 5 448 2000 2000; reg 6;
     lnk 7 (s_home ++ bytes [47] ++ s_target);
     lnk 8 (bytes [47] ++ s_target);
     dir 9 493 1000 1000; dir 20 493 1000 1000; dir 30 365 0 0].

Definition no_caps : CapSets := mkCaps 0 0 0 0 0.
Definition search_caps : CapSets := mkCaps 4 0 0 0 0.   (* CAP_DAC_READ_SEARCH *)

Definition ctx (u : positive) (caps : CapSets) : NsCtx := ctx_at u caps (1%positive, 1%positive).

Definition creds : WalkCreds := mkWalkCreds 1000 1000 [].

Definition f_follow : WalkFlags := mkWalkFlags true false false false false.
Definition f_nofollow : WalkFlags := mkWalkFlags false false false false false.
Definition f_empty : WalkFlags := mkWalkFlags true false true false false.
Definition f_empty_dir : WalkFlags := mkWalkFlags true true true false false.
Definition f_magic : WalkFlags := mkWalkFlags true false false true false.
Definition f_in_root : WalkFlags := mkWalkFlags true false false false true.

Definition no_fd (_ : Z) : option (option Loc) := None.
Definition fd_three (k : Z) : option (option Loc) :=
  if Z.eqb k 3 then Some (Some (LDentry 1 6)) else None.
Definition fd_opaque (k : Z) : option (option Loc) :=
  if Z.eqb k 3 then Some None else None.

Definition p_home_target : list byte := bytes [47] ++ s_home ++ bytes [47] ++ s_target.
Definition p_proc : list byte := bytes [47; 112; 114; 111; 99; 47].
Definition p_self : list byte := p_proc ++ bytes [115; 101; 108; 102].
Definition p_self_fd (k : Z) : list byte := p_self ++ bytes [47; 102; 100; 47; 48 + k].

(** An absolute path starts at the task's root, whatever the start. *)
Example walk_absolute :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 2) p_home_target f_follow
  = (WOk (LDentry 1 6), false).
Proof. vm_compute. reflexivity. Qed.

(** A relative path starts at the start the caller passes. *)
Example walk_relative :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 2) s_target f_follow
  = (WOk (LDentry 1 6), false).
Proof. vm_compute. reflexivity. Qed.

(** ".." at the root of mount 2 goes to its mount point in mount 1, then to
    that dentry's parent. *)
Example walk_dotdot_across_mount :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 2 20) (bytes [46; 46]) f_follow
  = (WOk (LDentry 1 1), false).
Proof. vm_compute. reflexivity. Qed.

(** ".." at the task's root stays there. *)
Example walk_dotdot_at_root :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) (bytes [46; 46]) f_follow
  = (WOk (LDentry 1 1), false).
Proof. vm_compute. reflexivity. Qed.

(** [choose_mountpoint] stops when the next mount point is the task's root:
    with the root at "covered" itself, ".." at the root of mount 2 stays at
    the root of mount 2 rather than reach the covered dentry. *)
Example walk_dotdot_stops_at_root_mountpoint :
  walk world (ctx_at 1 no_caps (1%positive, 3%positive)) creds no_fd (LDentry 2 20)
       (bytes [46; 46]) f_follow
  = (WOk (LDentry 2 20), false).
Proof. vm_compute. reflexivity. Qed.

(** A covered directory shows the root of the mount on it. *)
Example walk_covered_directory :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1)
       (bytes [47; 99; 111; 118; 101; 114; 101; 100]) f_follow
  = (WOk (LDentry 2 20), false).
Proof. vm_compute. reflexivity. Qed.

(** A symbolic link as the last component is followed under LOOKUP_FOLLOW
    (relative to its directory) ... *)
Example walk_last_link_followed :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) (bytes [47; 108; 105; 110; 107]) f_follow
  = (WOk (LDentry 1 6), false).
Proof. vm_compute. reflexivity. Qed.

(** ... and is the result itself without it. *)
Example walk_last_link_not_followed :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) (bytes [47; 108; 105; 110; 107]) f_nofollow
  = (WOk (LDentry 1 7), false).
Proof. vm_compute. reflexivity. Qed.

(** [n] links in a chain at the root: "0" -> "1" -> ... -> "n-1" -> "file". *)
Definition chain_name (i : nat) : list byte := decimal_bytes (Z.of_nat i).

Definition chain_world (n : nat) : NsState :=
  state (ns_mounts world) (ns_userns world) (ns_mntns world) (ns_pidns world) (ns_sbs world)
    (ns_dentries world
     ++ map (fun i => dent (Pos.of_succ_nat (100 + i)) 1 (Some 1%positive) (chain_name i)
                           (Pos.of_succ_nat (200 + i))) (seq 0 n))
    (ns_inodes world
     ++ map (fun i => lnk (Pos.of_succ_nat (200 + i))
                          (if Nat.ltb (S i) n then chain_name (S i) else s_file)) (seq 0 n)).

(** MAXSYMLINKS is 40: a chain of 40 links resolves, a chain of 41 is
    ELOOP. *)
Example walk_link_limit :
  walk (chain_world 40) (ctx 1 no_caps) creds no_fd (LDentry 1 1) (chain_name 0) f_follow
  = (WOk (LDentry 1 4), false)
  /\ walk (chain_world 41) (ctx 1 no_caps) creds no_fd (LDentry 1 1) (chain_name 0) f_follow
  = (WErr ELOOP, false).
Proof. split; vm_compute; reflexivity. Qed.

(** A file used as a directory is ENOTDIR. *)
Example walk_nondirectory :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) (bytes [47] ++ s_file ++ bytes [47; 120])
       f_follow
  = (WErr ENOTDIR, false).
Proof. vm_compute. reflexivity. Qed.

(** A name the directory does not hold is ENOENT. *)
Example walk_missing :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1)
       (bytes [47; 109; 105; 115; 115; 105; 110; 103]) f_follow
  = (WErr ENOENT, false).
Proof. vm_compute. reflexivity. Qed.

Definition p_secret_x : list byte := bytes [47; 115; 101; 99; 114; 101; 116; 47; 120].

(** Uid 1000 may not search the 0700 directory of uid 2000: EACCES. *)
Example walk_permission_denied :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) p_secret_x f_follow
  = (WErr EACCES, false).
Proof. vm_compute. reflexivity. Qed.

(** A child user namespace 2 whose maps take its id 0 to kernel id
    [lower]. *)
Definition cap_world (lower : Z) : NsState :=
  state (ns_mounts world)
    [root_user; uns 2 (Some 1%positive) 1 (Some [mkExtent 0 lower 1]) (Some [mkExtent 0 lower 1])]
    (ns_mntns world) (ns_pidns world) (ns_sbs world) (ns_dentries world) (ns_inodes world).

(** CAP_DAC_READ_SEARCH in namespace 2 searches the directory of kernel uid
    and gid 2000 only when the maps hold 2000 in their lower range: mapped,
    the walk reaches the missing name (ENOENT); unmapped, EACCES. *)
Example walk_capability_requires_mapping :
  walk (cap_world 1000) (ctx 2 search_caps) creds no_fd (LDentry 1 1) p_secret_x f_follow
  = (WErr EACCES, false)
  /\ walk (cap_world 2000) (ctx 2 search_caps) creds no_fd (LDentry 1 1) p_secret_x f_follow
  = (WErr ENOENT, false).
Proof. split; vm_compute; reflexivity. Qed.

(** Under LOOKUP_IN_ROOT, ".." at the start stays there, and the walk
    reports the scoped "..". *)
Example walk_in_root_dotdot :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 2) (bytes [46; 46]) f_in_root
  = (WOk (LDentry 1 2), true).
Proof. vm_compute. reflexivity. Qed.

(** Under LOOKUP_IN_ROOT, an absolute link restarts at the start: home's
    abslink to /target names home/target. *)
Example walk_in_root_absolute_link :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 2) (bytes [97; 98; 115; 108; 105; 110; 107])
       f_in_root
  = (WOk (LDentry 1 6), false).
Proof. vm_compute. reflexivity. Qed.

(** Under LOOKUP_IN_ROOT, following a magic link is EXDEV ([nd_jump_link]). *)
Example walk_in_root_magic_link :
  walk world (ctx 1 no_caps) creds fd_three (LDentry 1 1) (skipn 1 (p_self_fd 3)) f_in_root
  = (WErr EXDEV, false).
Proof. vm_compute. reflexivity. Qed.

(** /proc/self is the caller's own pid directory in the procfs pid
    namespace. *)
Example walk_proc_self :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) p_self f_follow
  = (WOk (LProcTask 3 42 []), false).
Proof. vm_compute. reflexivity. Qed.

(** /proc/self itself, not followed, has no location in the model. *)
Example walk_proc_self_unfollowed :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) p_self f_nofollow
  = (WOver, false).
Proof. vm_compute. reflexivity. Qed.

(** /proc/self/fd/3 follows to the location descriptor 3 has. *)
Example walk_proc_fd :
  walk world (ctx 1 no_caps) creds fd_three (LDentry 1 1) (p_self_fd 3) f_follow
  = (WOk (LDentry 1 6), false).
Proof. vm_compute. reflexivity. Qed.

(** A descriptor the model holds no path for leaves the walk undecided. *)
Example walk_proc_fd_opaque :
  walk world (ctx 1 no_caps) creds fd_opaque (LDentry 1 1) (p_self_fd 3) f_follow
  = (WOver, false).
Proof. vm_compute. reflexivity. Qed.

(** No descriptor 4: /proc/self/fd/4 is ENOENT. *)
Example walk_proc_fd_missing :
  walk world (ctx 1 no_caps) creds fd_three (LDentry 1 1) (p_self_fd 4) f_follow
  = (WErr ENOENT, false).
Proof. vm_compute. reflexivity. Qed.

(** LOOKUP_NO_MAGICLINKS refuses the magic link with ELOOP. *)
Example walk_proc_fd_no_magiclinks :
  walk world (ctx 1 no_caps) creds fd_three (LDentry 1 1) (p_self_fd 3) f_magic
  = (WErr ELOOP, false).
Proof. vm_compute. reflexivity. Qed.

(** Another pid's directory is not decided by the model. *)
Example walk_proc_other_pid :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) (p_proc ++ bytes [52; 51]) f_follow
  = (WOver, false).
Proof. vm_compute. reflexivity. Qed.

(** "042" is not a pid ([name_to_int] refuses a leading zero): ENOENT. *)
Example walk_proc_leading_zero :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) (p_proc ++ bytes [48; 52; 50]) f_follow
  = (WErr ENOENT, false).
Proof. vm_compute. reflexivity. Qed.

(** A trailing '/' on a file is ENOTDIR. *)
Example walk_trailing_separator :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1) (bytes [47] ++ s_file ++ bytes [47])
       f_follow
  = (WErr ENOTDIR, false).
Proof. vm_compute. reflexivity. Qed.

(** An empty path is ENOENT without LOOKUP_EMPTY ... *)
Example walk_empty_refused :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 2) [] f_follow = (WErr ENOENT, false).
Proof. vm_compute. reflexivity. Qed.

(** ... and names the start with it ... *)
Example walk_empty_start :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 2) [] f_empty = (WOk (LDentry 1 2), false).
Proof. vm_compute. reflexivity. Qed.

(** ... where LOOKUP_DIRECTORY still requires a directory. *)
Example walk_empty_directory_on_file :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 4) [] f_empty_dir = (WErr ENOTDIR, false).
Proof. vm_compute. reflexivity. Qed.

(** A missing name of 255 bytes is ENOENT; one of 256 is ENAMETOOLONG. *)
Example walk_name_too_long :
  walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1)
       (Z_to_bv 8 47 :: repeat (Z_to_bv 8 97) 255) f_follow
  = (WErr ENOENT, false)
  /\ walk world (ctx 1 no_caps) creds no_fd (LDentry 1 1)
       (Z_to_bv 8 47 :: repeat (Z_to_bv 8 97) 256) f_follow
  = (WErr ENAMETOOLONG, false).
Proof. split; vm_compute; reflexivity. Qed.

(** [walk_parent] gives the directory of the last name, the name and its
    type ... *)
Example walk_parent_normal :
  walk_parent world (ctx 1 no_caps) creds no_fd (LDentry 1 1) p_home_target f_follow
  = ((WOk (LDentry 1 2), s_target, LastNorm), false).
Proof. vm_compute. reflexivity. Qed.

(** ... after checking search permission on that directory. *)
Example walk_parent_search_denied :
  walk_parent world (ctx 1 no_caps) creds no_fd (LDentry 1 1) p_secret_x f_follow
  = ((WErr EACCES, bytes [120], LastNorm), false).
Proof. vm_compute. reflexivity. Qed.
