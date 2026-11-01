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

From Stdlib Require Import List PArith ZArith NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.

(** The errnos the namespace model returns (include/uapi/asm-generic/
    errno-base.h and errno.h), named once for every file of the model. *)
Definition EPERM : Z := 1%Z.
Definition ENOENT : Z := 2%Z.
Definition E2BIG : Z := 7%Z.
Definition EACCES : Z := 13%Z.
Definition EBUSY : Z := 16%Z.
Definition EXDEV : Z := 18%Z.
Definition ENODEV : Z := 19%Z.
Definition ENOTDIR : Z := 20%Z.
Definition EINVAL : Z := 22%Z.
Definition ENOSPC : Z := 28%Z.
Definition ENAMETOOLONG : Z := 36%Z.
Definition ELOOP : Z := 40%Z.
Definition ENODATA : Z := 61%Z.
Definition EOVERFLOW : Z := 75%Z.
Definition ENOBUFS : Z := 105%Z.

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

(** A user namespace.  [uns_max_userns] is its limit on user namespaces
    charged to it ([ucount_max[UCOUNT_USER_NAMESPACES]], written through
    /proc/sys/user/max_user_namespaces); [uns_sealed] says the table holds
    every user namespace charged to it (true for a namespace a modelled
    call made, false for the host's, whose other processes the model does
    not see). *)
Record UserNs := mkUserNs {
  uns_id                   : positive;
  uns_parent               : option positive;
  uns_level                : nat;
  uns_owner                : Z;                        (** kuid of the creator's euid *)
  uns_uid_map              : option (list IdExtent);   (** None until written; lower ids are kernel ids *)
  uns_gid_map              : option (list IdExtent);
  uns_setgroups_allowed    : bool;
  uns_parent_could_setfcap : bool;                     (** the creator held CAP_SETFCAP *)
  uns_max_userns           : Z;
  uns_sealed               : bool
}.

(** A mount namespace: its owner, the mount fixed as its root when it was
    made ([ns->root]; [pivot_root] does not change it), and whether it is
    the host's, whose paths the released model's file system answers
    ([mntns_released]). *)
Record MntNs := mkMntNs {
  mntns_id       : positive;
  mntns_owner    : positive;
  mntns_root     : positive;
  mntns_released : bool
}.

(** A pid namespace: its parent, owner and level, and the last pid
    allocated in it ([pid_ns->idr], which [alloc_pid] walks cyclically
    from the last one).  A namespace with no parent is the host's, whose
    pids the environment chooses. *)
Record PidNs := mkPidNs {
  pidns_id     : positive;
  pidns_parent : option positive;
  pidns_owner  : positive;
  pidns_level  : nat;
  pidns_last   : Z
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
    number, the bytes of a regular file or the target of a symbolic link,
    and whether it is a directory that stays empty ([is_empty_dir_inode]:
    the mount points procfs and sysfs make, such as
    /proc/sys/fs/binfmt_misc). *)
Record Inode := mkInode {
  ino_id        : positive;
  ino_kind      : InodeKind;
  ino_perm      : Z;
  ino_uid       : Z;
  ino_gid       : Z;
  ino_rdev      : Z;
  ino_bytes     : list byte;
  ino_empty_dir : bool
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

(** A credential as capability checks and map writes read it: its user
    namespace, euid and egid (kernel ids), and its effective set, which is
    in its own namespace. *)
Record IdCred := mkIdCred {
  ic_ns        : positive;
  ic_euid      : Z;
  ic_egid      : Z;
  ic_effective : Z
}.

(** A network interface: index, name, flags ([IFF_UP], ...) and its IPv4
    addresses with their prefix lengths. *)
Record NetIf := mkNetIf {
  if_index : Z;
  if_name  : list byte;
  if_flags : Z;
  if_addrs : list (Z * Z)
}.

(** A network namespace: owner, interfaces, and whether the model holds
    every socket in it ([netns_sealed]: true for a namespace a modelled
    clone or unshare made, false for the host's, whose other processes the
    model does not see). *)
Record NetNs := mkNetNs {
  netns_id     : positive;
  netns_owner  : positive;
  netns_ifs    : list NetIf;
  netns_sealed : bool
}.

(** What an open file of the namespace model is: a path opened with O_PATH;
    a directory open for reading and its position; a file open for reading
    or writing (a regular file or a task's procfs file) and its offset; a
    NETLINK_ROUTE socket of a network namespace, its port id and the
    datagrams queued for it; an AF_UNIX datagram socket; an eventfd; a
    signalfd and its mask; a procfs file bound to a user namespace when it
    was opened, and its offset: a task's uid_map, gid_map or setgroups
    (the task's namespace, [proc_id_map_open], [proc_setgroups_open]) or a
    file of /proc/sys/user (the opener's, [set_lookup] in
    kernel/ucount.c); a task's mountinfo, bound when it was opened to the
    task's mount namespace and root ([mounts_open_common],
    fs/proc_namespace.c), and its offset. *)
Inductive NsFileKind :=
  | NfPath (l : Loc)
  | NfDir (l : Loc) (pos : Z)
  | NfFile (l : Loc) (off : Z)
  | NfNetlink (netns : positive) (port : Z) (rxq : list (list byte))
  | NfUnixDgram (netns : positive)
  | NfEventfd
  | NfSignalfd (mask : Z)
  | NfUserNsFile (l : Loc) (userns : positive) (off : Z)
  | NfMountinfo (l : Loc) (mntns : positive) (root : positive * positive) (off : Z).

(** An open file description: its kind, its [f_flags] (access mode and
    status flags) and [f_cred], the opener's credential. *)
Record NsFile := mkNsFile {
  nf_kind  : NsFileKind;
  nf_flags : Z;
  nf_cred  : IdCred
}.

(** A static entry of a procfs instance, outside the task directories:
    its names from the procfs root, its kind, permission bits and owner
    kuid and kgid, and whether it is a directory that stays empty. *)
Record ProcEntry := mkProcEntry {
  px_path  : list (list byte);
  px_kind  : InodeKind;
  px_perm  : Z;
  px_uid   : Z;
  px_gid   : Z;
  px_empty : bool
}.

(** What the running kernel's build and boot configuration fix, which no
    call changes: the mount limit (sysctl fs.mount-max), the static
    entries every procfs instance shows (the entries a kernel build
    creates in the procfs root and below it, outside the task
    directories), and the devices a new network namespace gets besides
    lo (the fallback devices of the loaded modules, such as sit0 or
    ip6tnl0, each down and with no address). *)
Record NsEnv := mkNsEnv {
  env_mount_max     : Z;
  env_proc_entries  : list ProcEntry;
  env_net_fallback  : list NetIf
}.

(** The shared namespace state of a whole system.  [ns_files] holds the
    open files a process's descriptor table names by handle
    ([State.ONsFile]). *)
Record NsState := mkNsState {
  ns_mounts   : list Mount;
  ns_userns   : list UserNs;
  ns_mntns    : list MntNs;
  ns_pidns    : list PidNs;
  ns_netns    : list NetNs;
  ns_sbs      : list SuperBlock;
  ns_dentries : list Dentry;
  ns_inodes   : list Inode;
  ns_files    : list (N * NsFile);
  ns_env      : NsEnv
}.

(** The five capability sets of a task, as 64-bit masks. *)
Record CapSets := mkCaps {
  cap_effective   : Z;
  cap_permitted   : Z;
  cap_inheritable : Z;
  cap_bounding    : Z;
  cap_ambient     : Z
}.

(** What one task holds: which user, mount, pid and network namespace it is
    in, its pid in each pid namespace from its own outwards, its root and
    current directory as (mount, dentry), its umask, its capability sets
    (in its user namespace) and securebits, the descriptors marked
    close-on-exec, the no_new_privs bit and the dumpable mode.  The
    parent-death signal is the released model's ([State.m_pdeath_signal]),
    not this record's.

    [cx_no_new_privs] and [cx_dumpable] are [None] where the model does
    not know them: the released model stores neither, so a task that
    leaves the host's namespaces may have set either there; an arm that
    would report one declines while it is [None]. *)
Record NsCtx := mkNsCtx {
  cx_user         : positive;
  cx_mount        : positive;
  cx_pidns        : positive;
  cx_net          : positive;
  cx_pids         : list (positive * Z);
  cx_root         : positive * positive;
  cx_cwd          : positive * positive;
  cx_umask        : Z;
  cx_caps         : CapSets;
  cx_securebits   : Z;
  cx_cloexec      : list Z;
  cx_no_new_privs : option bool;
  cx_dumpable     : option Z
}.

(** The shared state of a system the namespace model knows nothing of: no
    mount tree and no namespace, Linux's default mount limit (100000) and
    no procfs entry.  A core builds its released world from this, never
    from the constructor, so a new field changes no caller. *)
Definition empty_nsstate : NsState :=
  mkNsState [] [] [] [] [] [] [] [] [] (mkNsEnv 100000%Z [] []).

Definition with_mounts (st : NsState) (ms : list Mount) : NsState :=
  mkNsState ms (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_sbs st)
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_env st).

Definition with_userns (st : NsState) (us : list UserNs) : NsState :=
  mkNsState (ns_mounts st) us (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_sbs st)
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_env st).

Definition with_files (st : NsState) (fs : list (N * NsFile)) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_sbs st)
            (ns_dentries st) (ns_inodes st) fs (ns_env st).

(** The context of a task that has entered no namespace: the initial
    namespaces, root and cwd at the root mount's root dentry, the umask
    022, no capability, no securebits, no close-on-exec descriptor,
    no_new_privs clear, dumpable.  These are assumptions about the
    launcher, as the released model's launch values are: it set the
    umask to 022, set no_new_privs nowhere and left the task dumpable. *)
Definition init_nsctx : NsCtx :=
  mkNsCtx 1%positive 1%positive 1%positive 1%positive [] (1%positive, 1%positive)
          (1%positive, 1%positive) 18%Z (mkCaps 0 0 0 0 0) 0%Z [] (Some false) (Some 1%Z).
