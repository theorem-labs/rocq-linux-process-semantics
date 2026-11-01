(** * LinuxProcessSem.Ns.Tables — namespace and mount state, as data

    The records a namespace-and-mount layer keeps beside the per-process
    model: the mounts of every mount namespace, the user, mount and pid
    namespaces, the superblocks with their dentries and inodes, and the
    per-task context that names which of them a task is in.  Nothing here
    steps; [Ns.Mount], [Ns.Userns] and [Ns.Spec] are the operations, and
    [Ns.ProcsIface] says how a multi-process core carries these records.

    The shapes follow Linux 6.18.44: a mount is [struct mount]
    (fs/mount.h), with [mnt_flags] split into the four flags a mount carries
    and the four locks [lock_mnt_tree] sets (MNT_LOCK_READONLY,
    MNT_LOCK_NOSUID, MNT_LOCK_NODEV, MNT_LOCK_NOEXEC), MNT_LOCKED, the
    unbindable mark that lives in [mnt_t_flags], the peer group
    ([mnt_group_id] of a shared mount) and the peer group it is a slave of
    (that of its [mnt_master]); a user namespace is
    [struct user_namespace] (include/linux/user_namespace.h) with its level,
    owner, the two id maps and the setgroups flag; a mount namespace keeps
    the mount fixed as its root at creation ([mnt_namespace.root]); a
    superblock is [struct super_block] reduced to its kind, owner, flags and
    magic; a dentry is a name in its parent directory, and every dentry and
    inode the model holds is listed, with ids unique across superblocks.

    Mount points and mount roots ([mnt_mountpoint], [mnt_root]) are dentry
    ids.  The entries of procfs below a task's directory are not listed:
    a walk that reaches one ends at a [Loc] of kind [LProcTask]. *)

From Stdlib Require Import List PArith ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.

(** The errnos the operations return. *)
Definition EPERM : Z := 1%Z.
Definition ENOENT : Z := 2%Z.
Definition EBUSY : Z := 16%Z.
Definition ENOTDIR : Z := 20%Z.
Definition EINVAL : Z := 22%Z.
Definition ENOSPC : Z := 28%Z.

Record MountFlags := mkMountFlags {
  mf_ro      : bool;
  mf_nosuid  : bool;
  mf_nodev   : bool;
  mf_noexec  : bool
}.

Record Mount := mkMount {
  mnt_id         : positive;
  mnt_ns         : positive;          (** the mount namespace it is attached in *)
  mnt_parent     : option positive;   (** None for the namespace's root mount *)
  mnt_mountpoint : positive;          (** dentry in the parent it is mounted on *)
  mnt_root       : positive;          (** dentry of its own root *)
  mnt_sb         : positive;          (** superblock *)
  mnt_flags      : MountFlags;
  mnt_lock_flags : MountFlags;        (** which flags may not be cleared *)
  mnt_locked     : bool;              (** MNT_LOCKED: may not be detached alone *)
  mnt_unbindable : bool;
  mnt_peer       : option positive;   (** the peer group when shared *)
  mnt_master     : option positive    (** the group it is a slave of *)
}.

(** One line of a uid_map or gid_map: ids [first, first + count) of the
    namespace map to ids [lower, lower + count) of its parent. *)
Record IdExtent := mkExtent {
  ext_first : Z;
  ext_lower : Z;
  ext_count : Z
}.

Record UserNs := mkUserNs {
  uns_id                   : positive;
  uns_parent               : option positive;
  uns_level                : nat;
  uns_owner                : Z;                        (** kuid of the creator's euid *)
  uns_uid_map              : option (list IdExtent);   (** None until written; lower ids are kernel ids *)
  uns_gid_map              : option (list IdExtent);
  uns_setgroups_allowed    : bool;
  uns_parent_could_setfcap : bool                      (** the creator held CAP_SETFCAP *)
}.

(** A mount namespace: its owner, and the mount fixed as its root when it
    was made ([ns->root]; [pivot_root] does not change it). *)
Record MntNs := mkMntNs {
  mntns_id    : positive;
  mntns_owner : positive;
  mntns_root  : positive
}.

(** A pid namespace: its parent, owner and level. *)
Record PidNs := mkPidNs {
  pidns_id     : positive;
  pidns_parent : option positive;
  pidns_owner  : positive;
  pidns_level  : nat
}.

(** What file system a superblock is.  The contents of a host file system
    are the host's, given as listed dentries and inodes like any other;
    procfs belongs to a pid namespace. *)
Inductive SbKind :=
  | SbHost
  | SbTmpfs
  | SbProc (pidns : positive)
  | SbDevpts.

Record SuperBlock := mkSb {
  sb_id             : positive;
  sb_kind           : SbKind;
  sb_owner          : positive;   (** [s_user_ns] *)
  sb_root           : positive;   (** the root dentry *)
  sb_rdonly         : bool;       (** SB_RDONLY *)
  sb_magic          : Z;          (** [f_type] *)
  sb_userns_visible : bool;       (** SB_I_USERNS_VISIBLE *)
  sb_i_noexec       : bool;       (** SB_I_NOEXEC *)
  sb_i_nodev        : bool        (** SB_I_NODEV *)
}.

Inductive InodeKind := IDir | IReg | ILnk | IChr | IBlk | IFifo | ISock.

(** An inode: its kind, the low twelve bits of [i_mode] (permissions,
    S_ISUID, S_ISGID, S_ISVTX), its owner kuid and kgid, its device
    number, and the bytes of a regular file or the target of a symbolic
    link. *)
Record Inode := mkInode {
  ino_id    : positive;
  ino_kind  : InodeKind;
  ino_perm  : Z;
  ino_uid   : Z;
  ino_gid   : Z;
  ino_rdev  : Z;
  ino_bytes : list byte
}.

(** A name in a directory: dentry [d_id] of superblock [d_sb] names inode
    [d_inode] in directory dentry [d_parent], or is the superblock's root
    when [d_parent] is [None]. *)
Record Dentry := mkDentry {
  d_id     : positive;
  d_sb     : positive;
  d_parent : option positive;
  d_name   : list byte;
  d_inode  : positive
}.

(** Where a walk ends: a dentry seen through a mount, or an entry of a
    task's procfs directory ([/proc/<pid>/...] below the task's
    directory, [rest] the names after it). *)
Inductive Loc :=
  | LDentry (mnt d : positive)
  | LProcTask (mnt : positive) (pid : Z) (rest : list (list byte)).

(** The shared namespace state of a whole system. *)
Record NsState := mkNsState {
  ns_mounts   : list Mount;
  ns_userns   : list UserNs;
  ns_mntns    : list MntNs;
  ns_pidns    : list PidNs;
  ns_sbs      : list SuperBlock;
  ns_dentries : list Dentry;
  ns_inodes   : list Inode
}.

(** The five capability sets of a task, as 64-bit masks. *)
Record CapSets := mkCaps {
  cap_effective   : Z;
  cap_permitted   : Z;
  cap_inheritable : Z;
  cap_bounding    : Z;
  cap_ambient     : Z
}.

(** What one task holds: which user, mount and pid namespace it is in, its
    pid in each pid namespace from its own outwards, its root and current
    directory as (mount, dentry), its umask and its capability sets, which
    are in its user namespace. *)
Record NsCtx := mkNsCtx {
  cx_user  : positive;
  cx_mount : positive;
  cx_pidns : positive;
  cx_pids  : list (positive * Z);
  cx_root  : positive * positive;
  cx_cwd   : positive * positive;
  cx_umask : Z;
  cx_caps  : CapSets
}.

(** The shared state of a system the namespace model knows nothing of: no
    mount tree and no namespace.  A core builds its released world from
    this, never from the constructor, so a new field changes no caller. *)
Definition empty_nsstate : NsState := mkNsState [] [] [] [] [] [] [].

Definition with_mounts (st : NsState) (ms : list Mount) : NsState :=
  mkNsState ms (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_sbs st) (ns_dentries st)
            (ns_inodes st).

(** The context of a task that has entered no namespace: the initial user,
    mount and pid namespace, with root and cwd at the root mount's root
    dentry, the umask 022, and no capability. *)
Definition init_nsctx : NsCtx :=
  mkNsCtx 1%positive 1%positive 1%positive [] (1%positive, 1%positive) (1%positive, 1%positive)
          18%Z (mkCaps 0 0 0 0 0).
