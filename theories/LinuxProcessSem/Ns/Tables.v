(** * LinuxProcessSem.Ns.Tables — namespace and mount state, as data

    The records a namespace-and-mount layer keeps beside the per-process
    model: the mounts of every mount namespace, the user namespaces with their
    id maps, and the per-task context that names which of them a task is in.
    Nothing here steps; [Ns.Mount] and [Ns.Userns] are the operations, and
    [Ns.ProcsIface] says how a multi-process core carries these records.

    The shapes follow Linux 6.18.44: a mount is [struct mount]
    (fs/mount.h), with [mnt_flags] split into the four flags a mount carries
    and the four locks [lock_mnt_tree] sets (MNT_LOCK_READONLY,
    MNT_LOCK_NOSUID, MNT_LOCK_NODEV, MNT_LOCK_NOEXEC), MNT_LOCKED, the
    unbindable mark that lives in [mnt_t_flags], the peer group
    ([mnt_group_id] of a shared mount) and the peer group it is a slave of
    (that of its [mnt_master]); a user namespace is
    [struct user_namespace] (include/linux/user_namespace.h) with its level,
    owner, the two id maps and the setgroups flag. *)

From Stdlib Require Import List PArith ZArith.
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
  uns_id                : positive;
  uns_parent            : option positive;
  uns_level             : nat;
  uns_owner             : Z;
  uns_uid_map           : option (list IdExtent);   (** None until written *)
  uns_gid_map           : option (list IdExtent);
  uns_setgroups_allowed : bool
}.

(** The shared namespace state of a whole system. *)
Record NsState := mkNsState {
  ns_mounts : list Mount;
  ns_userns : list UserNs
}.

(** What one task holds: which user and mount namespace it is in, and its
    root and current directory as (mount, dentry). *)
Record NsCtx := mkNsCtx {
  cx_user  : positive;
  cx_mount : positive;
  cx_root  : positive * positive;
  cx_cwd   : positive * positive
}.
