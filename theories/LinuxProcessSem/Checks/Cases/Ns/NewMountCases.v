(** * LinuxProcessSem.Checks.Cases.Ns.NewMountCases — new tmpfs, procfs and devpts mounts

    Each example runs [Ns.NewMount]'s option parse or [new_mount] on a
    small world and states the exact answer. *)

From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount Userns Walk NewMount.
Import ListNotations.
Open Scope Z_scope.

Definition b (l : list Z) : list byte := bytes_of l.

(** The options: "mode=0755" for tmpfs, none, an unknown option. *)
Example tmpfs_mode : parse_new_fs fs_tmpfs (Some (b [109;111;100;101;61;48;55;53;53])) = Some (NewTmpfs 493)
  := eq_refl.
Example tmpfs_default : parse_new_fs fs_tmpfs None = Some (NewTmpfs 1023) := eq_refl.
Example tmpfs_unknown_option :
  parse_new_fs fs_tmpfs (Some (b [115;105;122;101;61;49])) = None := eq_refl.        (* size=1 *)
Example tmpfs_bad_octal :
  parse_new_fs fs_tmpfs (Some (b [109;111;100;101;61;57])) = None := eq_refl.        (* mode=9 *)
Example proc_no_options : parse_new_fs fs_proc None = Some NewProc := eq_refl.
Example proc_option_declines : parse_new_fs fs_proc (Some (b [104;105;100;101;112;105;100;61;50])) = None
  := eq_refl.                                                                         (* hidepid=2 *)

(** devpts "newinstance,ptmxmode=0666,mode=620". *)
Example devpts_options :
  parse_new_fs fs_devpts
    (Some (b [110;101;119;105;110;115;116;97;110;99;101;44;
              112;116;109;120;109;111;100;101;61;48;54;54;54;44;
              109;111;100;101;61;54;50;48]))
  = Some (NewDevpts 438) := eq_refl.

Example unknown_type_declines : parse_new_fs (b [101;120;116;52]) None = None := eq_refl.  (* ext4 *)

(** A world: user namespace 1 (initial) and 2 (child, owned by kuid 1000);
    mount namespace 1 owned by 2; pid namespace 1 owned by 2; mount 1 is
    the root (tmpfs, dentry 1, a directory) with a file at dentry 2;
    mount 2 is a procfs mount at dentry 3 whose child mount 3 is locked on
    dentry 31, a directory that stays empty iff [empty]. *)
Definition nf : MountFlags := mkMountFlags false false false false.
Definition world (empty : bool) (proc_locked_ro : bool) : NsState :=
  mkNsState
    [mkMount 1 1 None 1 1 1 nf nf false false None None;
     mkMount 2 1 (Some 1%positive) 3 30 3 nf (mkMountFlags proc_locked_ro false false false)
             true false None None;
     mkMount 3 1 (Some 2%positive) 31 40 4 nf nf true false None None]
    [mkUserNs 1 None 0 0 None None true true 100 false;
     mkUserNs 2 (Some 1%positive) 1 1000 None None true true 100 true]
    [mkMntNs 1 2 1 false]
    [mkPidNs 1 None 2 0 0]
    []
    [mkSb 1 SbTmpfs 2 1 false TMPFS_MAGIC false false true;
     mkSb 3 (SbProc 1) 2 30 false PROC_SUPER_MAGIC true true true;
     mkSb 4 SbTmpfs 2 40 false TMPFS_MAGIC false false true]
    [mkDentry 1 1 None [] 1; mkDentry 2 1 (Some 1%positive) (b [102]) 2;
     mkDentry 3 1 (Some 1%positive) (b [112]) 3;
     mkDentry 30 3 None [] 30; mkDentry 31 3 (Some 30%positive) (b [115]) 31;
     mkDentry 40 4 None [] 40]
    [mkInode 1 IDir 493 1000 1000 0 [] false; mkInode 2 IReg 420 1000 1000 0 [] false;
     mkInode 3 IDir 493 1000 1000 0 [] false;
     mkInode 30 IDir 365 0 0 0 [] false; mkInode 31 IDir 365 0 0 0 [] empty;
     mkInode 40 IDir 493 0 0 0 [] false]
    []
    (mkNsEnv 100 [mkProcEntry [b [115;121;115]] IDir 365 0 0 false] [] default_mi_env)
.

(** A task in user namespace 2, mount namespace 1 and pid namespace 1,
    holding every capability there. *)
Definition ctx : NsCtx :=
  mkNsCtx 2 1 1 1 [(1%positive, 2)] (1%positive, 1%positive) (1%positive, 1%positive) 18
          (mkCaps (2 ^ 41 - 1) (2 ^ 41 - 1) 0 (2 ^ 41 - 1) 0) 0 [] (Some false) (Some 1).
Definition cred : IdCred := mkIdCred 2 1000 1000 (2 ^ 41 - 1).
Definition nocred : IdCred := mkIdCred 2 1000 1000 0.

Definition outcome (r : NewMountRes) : option (list bool * nat * nat) :=
  match r with
  | NMOk ls mk => Some (ls, length (ns_mounts (mk false)), length (ns_dentries (mk false)))
  | _ => None
  end.
Definition err (r : NewMountRes) : option Z := match r with NMErr e => Some e | _ => None end.

(** A tmpfs on dentry 3 of the root mount: one mount more, one dentry
    more, no visibility check. *)
Example tmpfs_mounts :
  outcome (new_mount (world true false) ctx cred 1000 1000 (NewTmpfs 493) nf 2 1 3)
  = Some ([false], 4%nat, 7%nat) := eq_refl.

(** Its root is a directory with the asked mode, owned by the caller's
    fsuid and fsgid. *)
Example tmpfs_root_inode :
  match new_mount (world true false) ctx cred 1000 1000 (NewTmpfs 493) nf 2 1 3 with
  | NMOk _ mk => last (ns_inodes (mk false)) (mkInode 1 IReg 0 0 0 0 [] false)
  | _ => mkInode 1 IReg 0 0 0 0 [] false
  end = mkInode 41 IDir 493 1000 1000 0 [] false := eq_refl.

(** Without CAP_SYS_ADMIN: EPERM. *)
Example tmpfs_needs_admin :
  err (new_mount (world true false) ctx nocred 1000 1000 (NewTmpfs 493) nf 2 1 3) = Some 1 := eq_refl.

(** A target that is not a directory: ENOTDIR. *)
Example tmpfs_on_file :
  err (new_mount (world true false) ctx cred 1000 1000 (NewTmpfs 493) nf 2 1 2) = Some 20 := eq_refl.

(** procfs in a mount namespace of a user namespace below the initial one:
    allowed while the visible procfs mount's locked child sits on a
    directory that stays empty, and the new superblock gets the static
    entries; refused (EPERM) when it does not. *)
Example proc_visible :
  outcome (new_mount (world true false) ctx cred 1000 1000 NewProc nf 2 1 3)
  = Some ([false], 4%nat, 8%nat) := eq_refl.
Example proc_hidden_child :
  err (new_mount (world false false) ctx cred 1000 1000 NewProc nf 2 1 3) = Some 1 := eq_refl.

(** A visible procfs mount whose read-only is locked lets only a
    read-only new mount through, and passes it the lock. *)
Example proc_locked_ro_needs_ro :
  err (new_mount (world true true) ctx cred 1000 1000 NewProc nf 2 1 3) = Some 1 := eq_refl.
Example proc_locked_ro_passes_lock :
  outcome (new_mount (world true true) ctx cred 1000 1000 NewProc (mkMountFlags true false false false) 2 1 3)
  = Some ([true], 4%nat, 8%nat) := eq_refl.

(** devpts: the root and ptmx with the asked mode, owned by the caller. *)
Example devpts_ptmx :
  match new_mount (world true false) ctx cred 1000 1000 (NewDevpts 438) nf 2 1 3 with
  | NMOk _ mk => last (ns_inodes (mk false)) (mkInode 1 IReg 0 0 0 0 [] false)
  | _ => mkInode 1 IReg 0 0 0 0 [] false
  end = mkInode 42 IChr 438 1000 1000 1282 [] false := eq_refl.

(** The mount limit: 3 mounts and a limit of 3 refuse a fourth. *)
Definition at_limit : NsState :=
  let w := world true false in
  mkNsState (ns_mounts w) (ns_userns w) (ns_mntns w) (ns_pidns w) (ns_netns w) (ns_sbs w)
            (ns_dentries w) (ns_inodes w) (ns_files w) (mkNsEnv 3 [] [] default_mi_env).
Example limit_refuses :
  err (new_mount at_limit ctx cred 1000 1000 (NewTmpfs 493) nf 2 1 3) = Some 28 := eq_refl.
