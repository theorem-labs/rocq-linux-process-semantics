(** * LinuxProcessSem.Ns.Tables — namespace and mount state, as data

    The records a namespace-and-mount layer keeps beside the per-process
    model: the mounts of every mount namespace, the user, mount, pid,
    network and UTS namespaces, the superblocks with their dentries and
    inodes, and the per-task context that names which of them a task is
    in.  Nothing here steps; [Ns.Mount], [Ns.Userns] and [Ns.Spec] are the
    operations, and [Ns.ProcsIface] says how a multi-process core carries
    these records.

    [NsState], [NsEnv], [NsCtx], [MntNs], [PropLinks] and [Mount] are built
    and changed through [empty_nsstate], [empty_nsenv], [init_nsctx],
    [mk_mntns], [empty_prop] and the setters below them, never by applying
    [mkNsState], [mkNsEnv], [mkNsCtx], [mkMntNs], [mkPropLinks] or [mkMount] to every field
    elsewhere: a new field then touches the record, its initial value and
    its setters, and no caller.  (Fixtures and copy functions written
    before the [Mount] setters still apply [mkMount]; new code does not.)

    The shapes follow Linux v6.18.46: a mount is [struct mount]
    (fs/mount.h), with [mnt_flags] split into the four flags a mount carries
    and the four locks [lock_mnt_tree] sets (MNT_LOCK_READONLY,
    MNT_LOCK_NOSUID, MNT_LOCK_NODEV, MNT_LOCK_NOEXEC), MNT_LOCKED, the
    unbindable mark that lives in [mnt_t_flags], the peer group
    ([mnt_group_id] of a shared mount) and the peer group it is a slave of
    (that of its [mnt_master]); the order the kernel keeps of a peer
    group's ring and of a mount's slave list is [PropLinks]; a user
    namespace is [struct user_namespace] (include/linux/user_namespace.h)
    with its level, owner, the two id maps and the setgroups flag; a mount
    namespace keeps the mount fixed as its root at creation
    ([mnt_namespace.root]); a superblock is [struct super_block] reduced to
    its kind, owner, flags and magic; a dentry is a name in its parent
    directory, and every dentry and inode the model holds is listed, with
    ids unique across superblocks.

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
Definition EIO : Z := 5%Z.
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

(** The setters of [Mount], one per field ([mnt_with_place] sets the
    parent and the mount point together, as [mnt_set_mountpoint] does,
    fs/namespace.c:1020-1028): with [mkMount] itself, the places new code
    builds a mount from. *)
Definition mnt_with_id (m : Mount) (i : positive) : Mount :=
  mkMount i (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m) (mnt_sb m)
          (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          (mnt_peer m) (mnt_master m).

Definition mnt_with_ns (m : Mount) (n : positive) : Mount :=
  mkMount (mnt_id m) n (mnt_parent m) (mnt_mountpoint m) (mnt_root m) (mnt_sb m)
          (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          (mnt_peer m) (mnt_master m).

Definition mnt_with_place (m : Mount) (parent : option positive) (mp : positive) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) parent mp (mnt_root m) (mnt_sb m)
          (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          (mnt_peer m) (mnt_master m).

Definition mnt_with_root (m : Mount) (d : positive) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) d (mnt_sb m)
          (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          (mnt_peer m) (mnt_master m).

Definition mnt_with_sb (m : Mount) (s : positive) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m) s
          (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          (mnt_peer m) (mnt_master m).

Definition mnt_with_flags (m : Mount) (f : MountFlags) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m) (mnt_sb m)
          f (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          (mnt_peer m) (mnt_master m).

Definition mnt_with_lock_flags (m : Mount) (f : MountFlags) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m) (mnt_sb m)
          (mnt_flags m) f (mnt_locked m) (mnt_unbindable m)
          (mnt_peer m) (mnt_master m).

Definition mnt_with_locked (m : Mount) (b : bool) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m) (mnt_sb m)
          (mnt_flags m) (mnt_lock_flags m) b (mnt_unbindable m)
          (mnt_peer m) (mnt_master m).

Definition mnt_with_unbindable (m : Mount) (b : bool) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m) (mnt_sb m)
          (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) b
          (mnt_peer m) (mnt_master m).

Definition mnt_with_peer (m : Mount) (g : option positive) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m) (mnt_sb m)
          (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          g (mnt_master m).

Definition mnt_with_master (m : Mount) (g : option positive) : Mount :=
  mkMount (mnt_id m) (mnt_ns m) (mnt_parent m) (mnt_mountpoint m) (mnt_root m) (mnt_sb m)
          (mnt_flags m) (mnt_lock_flags m) (mnt_locked m) (mnt_unbindable m)
          (mnt_peer m) g.

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
  mntns_released : bool;
  mntns_anon     : bool;
  mntns_origin   : option positive
}.

(** Real namespaces by default; anonymous copies retain their originating
    real namespace key, or [None] for a tree usable from any namespace
    (Linux v6.18.46, fs/namespace.c:964-965, 3028-3034). *)
Definition mk_mntns (id owner root : positive) (released : bool) : MntNs :=
  mkMntNs id owner root released false None.

Definition mntns_with_anon (n : MntNs) (b : bool) : MntNs :=
  mkMntNs (mntns_id n) (mntns_owner n) (mntns_root n) (mntns_released n) b (mntns_origin n).

Definition mntns_with_origin (n : MntNs) (o : option positive) : MntNs :=
  mkMntNs (mntns_id n) (mntns_owner n) (mntns_root n) (mntns_released n) (mntns_anon n) o.

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
    when [d_parent] is [None].  [d_unlinked]: the name was removed
    ([d_unlinked], include/linux/dcache.h) while something still holds the
    dentry (an open file, or a mount whose root it is); its parent stays, as
    the kernel's does, but no lookup or listing finds it. *)
Record Dentry := mkDentryRec {
  d_id       : positive;
  d_sb       : positive;
  d_parent   : option positive;
  d_name     : list byte;
  d_inode    : positive;
  d_unlinked : bool
}.

(** A dentry that is linked in its directory. *)
Definition mkDentry (i s : positive) (p : option positive) (name : list byte) (ino : positive) : Dentry :=
  mkDentryRec i s p name ino false.

(** Where a walk ends: a dentry seen through a mount, an entry of a
    task's procfs directory ([/proc/<pid>/...] below the task's
    directory, [rest] the names after it), or procfs's "self" link itself
    when the walk does not follow it ([own]: the caller's tgid in that
    procfs's pid namespace, [None] when it has none there). *)
Inductive Loc :=
  | LDentry (mnt d : positive)
  | LProcTask (mnt : positive) (pid : Z) (rest : list (list byte))
  | LProcSelf (mnt : positive) (own : option Z).

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

(** A UTS namespace ([struct uts_namespace], include/linux/uts_namespace.h:11-16,
    Linux v6.18.46): its owner ([user_ns], the user namespace
    [copy_utsname] was given) and the two members of its
    [struct new_utsname] that a call can write: [nodename] ([sethostname])
    and [domainname] ([setdomainname]).  Each is [None] while it is still
    the host's -- those bytes of the released model's utsname pin
    ([State.m_utsname], chosen at the first [uname]) -- and [Some] its 65
    bytes after a write in this namespace or in the namespace it was copied
    from ([clone_uts_ns] copies the whole name, kernel/utsname.c:59).  The
    other four members (sysname, release, version, machine) have no setter
    in kernel/sys.c, so in every namespace they are the pin's. *)
Record UtsNs := mkUtsNs {
  utsns_id         : positive;
  utsns_owner      : positive;
  utsns_nodename   : option (list byte);
  utsns_domainname : option (list byte)
}.

(** The host's UTS namespace ([init_uts_ns]): id [host_uts], owned by the
    initial user namespace (1, the [cx_user] of [init_nsctx]), both members
    the pin's.  No arm writes it ([Task.sethostname_arm] declines there,
    since a write would change the environment's pin), so both stay
    [None]. *)
Definition host_uts : positive := 1%positive.
Definition host_utsns : UtsNs := mkUtsNs host_uts 1%positive None None.

Definition with_nodename (u : UtsNs) (v : option (list byte)) : UtsNs :=
  mkUtsNs (utsns_id u) (utsns_owner u) v (utsns_domainname u).

Definition with_domainname (u : UtsNs) (v : option (list byte)) : UtsNs :=
  mkUtsNs (utsns_id u) (utsns_owner u) (utsns_nodename u) v.

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

(** The values /proc/<pid>/mountinfo prints that the tables do not hold
    ([Ns.Mountinfo]): attributes of kernel objects, fixed for each object
    while it lives, so one value per object for the whole run.  The
    kernel's mount ids and peer-group ids, each superblock's device
    number, the type name of a host superblock, each mount's source name,
    the text a superblock's [show_options] prints, and [propagate_from]
    where a slave's master chain reaches a peer group with no member in
    the tables (inside the tables [Propagation.dominating_id] computes it). *)
Record MiEnv := mkMiEnv {
  mi_id      : positive -> Z;              (** [mnt_id] of a mount *)
  mi_group   : positive -> Z;              (** [mnt_group_id] of a peer group *)
  mi_dev     : positive -> Z * Z;          (** [MAJOR], [MINOR] of a superblock's [s_dev] *)
  mi_type    : positive -> list byte;      (** the type name of a host superblock *)
  mi_source  : positive -> list byte;      (** a mount's [mnt_devname] *)
  mi_sbopts  : positive -> list byte;      (** a superblock's [show_options] text *)
  mi_dom     : positive -> option Z        (** [get_dominating_id] when it differs from the master,
                                               used where the master chain leaves the tables *)
}.

(** One choice of those values: ids as the tables number the objects,
    device 0:<superblock id>, no type, source or options text. *)
Definition default_mi_env : MiEnv :=
  mkMiEnv (fun i => Zpos i) (fun g => Zpos g) (fun s => (0%Z, Zpos s))
          (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => None).

(** What the running kernel's build and boot configuration fix, which no
    call changes: the mount limit (sysctl fs.mount-max), the static
    entries every procfs instance shows (the entries a kernel build
    creates in the procfs root and below it, outside the task
    directories), the devices a new network namespace gets besides lo
    (the fallback devices of the loaded modules, such as sit0 or ip6tnl0,
    each down and with no address), the mountinfo values above, and the
    largest [if_nlmsg_size] (net/core/rtnetlink.c) of a device a namespace
    of this model holds -- lo and the fallback devices, with no virtual
    function and no port -- which bounds every RTM_NEWLINK message of a
    link dump ([Net.nl_env_ok]).  That bound is a fact of the build's
    configuration (the attribute sizes [if_nlmsg_size] and the address
    families' [get_link_af_size] add up); a value below Linux's makes the
    model refuse the dump Linux gives.  Then the names KNOWN ABSENT from
    a host directory: pairs of a host directory's dentry and a name whose
    lookup there returns -ENOENT, as a negative dentry records it.  A
    host lookup of a name the tables do not list is otherwise undecided;
    a pair is a measured fact about the host (stat of that path gave
    ENOENT), and a statement that lists one asks that nothing outside the
    model creates the name.  Then [env_foreign_pgroups]: whether a
    process outside the model may make a process group of a modelled
    task's pid.  Only the task itself or its parent may set the task's
    process group ([setpgid], kernel/sys.c:1144-1155, Linux v6.18.46: a
    caller other than the task must be [p->real_parent], in [p]'s
    session, before [p] execs), and no modelled process can ([setpgid]
    154 has no arm).  But once the modelled parent of pid 1 of a pid
    namespace the model made exits, that pid 1 is reparented to a reaper
    the environment owns, and that reaper may call [setpgid(child, child)]
    before the child execs, after which the child's [setsid] answers EPERM
    (kernel/sys.c:1284-1285).  Another task of such a namespace whose
    parent exits goes to the namespace's pid 1 or to a child subreaper at
    its level ([find_new_reaper], kernel/exit.c:642-675), a modelled
    process.  [false], the default, assumes that no
    environment reaper calls [setpgid] on the caller before the caller's
    [setsid]; a statement that wants that case names
    [env_foreign_pgroups := true] ([Task.setsid_arm]).

    Then the OPEN peer groups: the keys of the peer groups the tables
    hold that have a member outside the tables, in a mount namespace the
    tables do not hold, or in a detached tree held outside them. A mount
    or unmount at that outside member reaches every member of the group
    in the tables and every slave below them ([propagate_mnt],
    [propagate_umount], fs/pnode.c:311-366, 658-687, Linux v6.18.46).
    Host /proc/<pid>/mountinfo reveals namespace-held peers but cannot
    establish the absence of detached copies held by host processes.
    [env_open_groups = []] assumes no such copy of a model group either.
    Separately, [env_entered_mntns] lists namespaces whose mounts an
    outside task may alter by entry, path or descriptor, including detached
    trees. Its default [] assumes none. [Propagation.entered_closure]
    includes anonymous trees by their real origin, or origin [None] under
    any nonempty list; [Propagation.open_groups] also includes groups on
    those superblocks. Arms reading uncertain topology decline. Both
    empty lists rule out these outside events ([closed_no_outside_event]).

    Last, [env_overflow_ids]: the values of kernel.overflowuid and
    kernel.overflowgid, which [from_kuid_munged] and [from_kgid_munged]
    give for an id with no mapping in the caller's user namespace
    (kernel/user_namespace.c:466-473, 533-541, Linux v6.18.46). Each is
    any value from 0 to 65535, 65534 by default (kernel/sys.c:167-168,
    184-202; include/linux/highuid.h:41-42), and the host's root can write
    them at any time. [Some (u, g)]: the launch measured them as [u] and
    [g], and the host does not write them during the run. [None]: they are
    unknown, or the host may write them during the run. The default,
    [Some (65534, 65534)], assumes the kernel's defaults; a statement that
    wants another launch names it with [env_with_overflow_ids]
    ([Files.munged_ok]). A pair with a value outside 0 to 65535 is no
    launch a host can have: a stat under it has no answer
    ([Files.stat_ids_decided]). *)
Record NsEnv := mkNsEnv {
  env_mount_max       : Z;
  env_proc_entries    : list ProcEntry;
  env_net_fallback    : list NetIf;
  env_mountinfo       : MiEnv;
  env_nl_link_max     : Z;
  env_host_absent     : list (positive * list byte);
  env_foreign_pgroups : bool;
  env_open_groups     : list positive;
  env_overflow_ids    : option (Z * Z);
  env_entered_mntns   : list positive
}.

(** The launch values of a system the namespace model knows nothing of:
    Linux's default mount limit (100000), no procfs entry, no fallback
    device, [default_mi_env], a link-message bound of 65536 bytes, no name
    known absent, no foreign process group, no open peer group, the
    default overflow ids (65534, 65534) and no outside namespace entry. *)
Definition empty_nsenv : NsEnv :=
  mkNsEnv 100000%Z [] [] default_mi_env 65536%Z [] false [] (Some (65534, 65534)%Z) [].

(** The setters of [NsEnv], one per field: with [empty_nsenv], the only
    places that apply [mkNsEnv] to every field. *)
Definition env_with_mount_max (e : NsEnv) (v : Z) : NsEnv :=
  mkNsEnv v (env_proc_entries e) (env_net_fallback e) (env_mountinfo e) (env_nl_link_max e)
          (env_host_absent e) (env_foreign_pgroups e) (env_open_groups e) (env_overflow_ids e) (env_entered_mntns e).

Definition env_with_proc_entries (e : NsEnv) (v : list ProcEntry) : NsEnv :=
  mkNsEnv (env_mount_max e) v (env_net_fallback e) (env_mountinfo e) (env_nl_link_max e)
          (env_host_absent e) (env_foreign_pgroups e) (env_open_groups e) (env_overflow_ids e) (env_entered_mntns e).

Definition env_with_net_fallback (e : NsEnv) (v : list NetIf) : NsEnv :=
  mkNsEnv (env_mount_max e) (env_proc_entries e) v (env_mountinfo e) (env_nl_link_max e)
          (env_host_absent e) (env_foreign_pgroups e) (env_open_groups e) (env_overflow_ids e) (env_entered_mntns e).

Definition env_with_mountinfo (e : NsEnv) (v : MiEnv) : NsEnv :=
  mkNsEnv (env_mount_max e) (env_proc_entries e) (env_net_fallback e) v (env_nl_link_max e)
          (env_host_absent e) (env_foreign_pgroups e) (env_open_groups e) (env_overflow_ids e) (env_entered_mntns e).

Definition env_with_nl_link_max (e : NsEnv) (v : Z) : NsEnv :=
  mkNsEnv (env_mount_max e) (env_proc_entries e) (env_net_fallback e) (env_mountinfo e) v
          (env_host_absent e) (env_foreign_pgroups e) (env_open_groups e) (env_overflow_ids e) (env_entered_mntns e).

Definition env_with_host_absent (e : NsEnv) (v : list (positive * list byte)) : NsEnv :=
  mkNsEnv (env_mount_max e) (env_proc_entries e) (env_net_fallback e) (env_mountinfo e)
          (env_nl_link_max e) v (env_foreign_pgroups e) (env_open_groups e) (env_overflow_ids e) (env_entered_mntns e).

Definition env_with_foreign_pgroups (e : NsEnv) (b : bool) : NsEnv :=
  mkNsEnv (env_mount_max e) (env_proc_entries e) (env_net_fallback e) (env_mountinfo e)
          (env_nl_link_max e) (env_host_absent e) b (env_open_groups e) (env_overflow_ids e) (env_entered_mntns e).

Definition env_with_open_groups (e : NsEnv) (v : list positive) : NsEnv :=
  mkNsEnv (env_mount_max e) (env_proc_entries e) (env_net_fallback e) (env_mountinfo e)
          (env_nl_link_max e) (env_host_absent e) (env_foreign_pgroups e) v (env_overflow_ids e) (env_entered_mntns e).

(** The same environment with [env_overflow_ids] set to [o]. *)
Definition env_with_overflow_ids (e : NsEnv) (o : option (Z * Z)) : NsEnv :=
  mkNsEnv (env_mount_max e) (env_proc_entries e) (env_net_fallback e) (env_mountinfo e)
          (env_nl_link_max e) (env_host_absent e) (env_foreign_pgroups e) (env_open_groups e) o (env_entered_mntns e).

(** Namespaces whose mounts an outside task may alter, including through a
    path or descriptor into a detached tree. *)
Definition env_with_entered_mntns (e : NsEnv) (ns : list positive) : NsEnv :=
  mkNsEnv (env_mount_max e) (env_proc_entries e) (env_net_fallback e) (env_mountinfo e)
          (env_nl_link_max e) (env_host_absent e) (env_foreign_pgroups e) (env_open_groups e)
          (env_overflow_ids e) ns.

(** The order the kernel keeps of mount propagation, beyond each mount's
    peer group and master group ([Ns.Propagation]; Linux v6.18.46):
    - [pl_rings]: a peer group's members in [next_peer] order, the order of
      the [mnt_share] ring (fs/mount.h:68, fs/pnode.c:17-20).  The list has
      no start: the member after the last is the first.  A group with one
      member in the tables needs no entry.
    - [pl_slaves]: a mount's [mnt_slave_list], head first, as [first_slave]
      and [next_slave] read it (fs/mount.h:69-71, fs/pnode.c:22-30).  The
      entry's key is the master mount ([mnt_master]) of each slave it
      lists.  A mount with no slave or one slave needs no entry.
    - [pl_next_group]: a lower bound for the key of the next new peer group
      ([Propagation.new_group_key]); no key the tables used before is given
      again.
    Both orders decide the order in which the kernel walks a propagation
    tree ([propagation_next], [next_group], fs/pnode.c:177-212, 228-258),
    so the order in which one call makes secondary mounts, and so their
    [mnt_id_unique] and their order in mountinfo.  The kernel shows neither
    order to user space ([show_mountinfo] prints group numbers only,
    fs/proc_namespace.c:158-169), so a launch states an order only where it
    knows it: an absent entry for a group with two or more members in the
    tables, or for a mount with two or more slaves, means "order unknown",
    and an arm whose answer that order would decide declines. *)
Record PropLinks := mkPropLinks {
  pl_rings      : list (positive * list positive);
  pl_slaves     : list (positive * list positive);
  pl_next_group : positive
}.

(** No order data, and keys from 1. *)
Definition empty_prop : PropLinks := mkPropLinks [] [] 1%positive.

(** The setters of [PropLinks], one per field. *)
Definition pl_with_rings (pl : PropLinks) (v : list (positive * list positive)) : PropLinks :=
  mkPropLinks v (pl_slaves pl) (pl_next_group pl).

Definition pl_with_slaves (pl : PropLinks) (v : list (positive * list positive)) : PropLinks :=
  mkPropLinks (pl_rings pl) v (pl_next_group pl).

Definition pl_with_next_group (pl : PropLinks) (v : positive) : PropLinks :=
  mkPropLinks (pl_rings pl) (pl_slaves pl) v.

(** The shared namespace state of a whole system.  [ns_files] holds the
    open files a process's descriptor table names by handle
    ([State.ONsFile]); [ns_prop] the order data of propagation. *)
Record NsState := mkNsState {
  ns_mounts   : list Mount;
  ns_userns   : list UserNs;
  ns_mntns    : list MntNs;
  ns_pidns    : list PidNs;
  ns_netns    : list NetNs;
  ns_utsns    : list UtsNs;
  ns_sbs      : list SuperBlock;
  ns_dentries : list Dentry;
  ns_inodes   : list Inode;
  ns_files    : list (N * NsFile);
  ns_prop     : PropLinks;
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

(** What one task holds: which user, mount, pid, network and UTS namespace
    it is in, its pid in each pid namespace from its own outwards, its root
    and current directory as (mount, dentry), its umask, its capability
    sets (in its user namespace) and securebits, and the descriptors marked
    close-on-exec.  The parent-death signal, the no-new-privs bit and the
    dumpable mode are the released model's ([State.m_pdeath_signal],
    [State.m_no_new_privs], [State.m_dumpable]), not this record's: a
    clone copies them with the process record ([Procs.child_proc]), so
    they are known in every world. *)
Record NsCtx := mkNsCtx {
  cx_user         : positive;
  cx_mount        : positive;
  cx_pidns        : positive;
  cx_net          : positive;
  cx_uts          : positive;
  cx_pids         : list (positive * Z);
  cx_root         : positive * positive;
  cx_cwd          : positive * positive;
  cx_umask        : Z;
  cx_caps         : CapSets;
  cx_securebits   : Z;
  cx_cloexec      : list Z
}.

(** The pid of the task in pid namespace [pidns] ([task_tgid_nr_ns]), from
    its pids [cx_pids], innermost first. *)
Fixpoint pid_in (ps : list (positive * Z)) (pidns : positive) : option Z :=
  match ps with
  | [] => None
  | (ns, p) :: rest => if Pos.eqb ns pidns then Some p else pid_in rest pidns
  end.

(** The shared state of a system the namespace model knows nothing of: no
    mount tree and no namespace but the host's UTS namespace
    ([host_utsns], whose names are the released pin's), no order data of
    propagation, and the launch values of [empty_nsenv].  A core builds its
    released world from this, never from the constructor, so a new field
    changes no caller. *)
Definition empty_nsstate : NsState :=
  mkNsState [] [] [] [] [] [host_utsns] [] [] [] [] empty_prop empty_nsenv.

(** The setters of [NsState], one per field: with [empty_nsstate], the only
    places that apply [mkNsState] to every field. *)
Definition with_mounts (st : NsState) (ms : list Mount) : NsState :=
  mkNsState ms (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_utsns st) (ns_sbs st)
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_prop st) (ns_env st).

Definition with_userns (st : NsState) (us : list UserNs) : NsState :=
  mkNsState (ns_mounts st) us (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_utsns st) (ns_sbs st)
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_prop st) (ns_env st).

Definition with_mntns (st : NsState) (ns : list MntNs) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) ns (ns_pidns st) (ns_netns st) (ns_utsns st) (ns_sbs st)
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_prop st) (ns_env st).

Definition with_pidns (st : NsState) (ps : list PidNs) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) ps (ns_netns st) (ns_utsns st) (ns_sbs st)
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_prop st) (ns_env st).

Definition with_netns (st : NsState) (ns : list NetNs) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) ns (ns_utsns st) (ns_sbs st)
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_prop st) (ns_env st).

Definition with_utsns (st : NsState) (us : list UtsNs) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) us (ns_sbs st)
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_prop st) (ns_env st).

Definition with_sbs (st : NsState) (sbs : list SuperBlock) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_utsns st) sbs
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_prop st) (ns_env st).

Definition with_dentries (st : NsState) (ds : list Dentry) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_utsns st)
            (ns_sbs st) ds (ns_inodes st) (ns_files st) (ns_prop st) (ns_env st).

Definition with_inodes (st : NsState) (ins : list Inode) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_utsns st)
            (ns_sbs st) (ns_dentries st) ins (ns_files st) (ns_prop st) (ns_env st).

Definition with_files (st : NsState) (fs : list (N * NsFile)) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_utsns st)
            (ns_sbs st) (ns_dentries st) (ns_inodes st) fs (ns_prop st) (ns_env st).

(** The order data of propagation replaced by [pl].  (Not [with_prop]:
    [Mount.with_prop] sets a mount's peer group and master.) *)
Definition with_ns_prop (st : NsState) (pl : PropLinks) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_utsns st)
            (ns_sbs st) (ns_dentries st) (ns_inodes st) (ns_files st) pl (ns_env st).

Definition with_env (st : NsState) (e : NsEnv) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_utsns st)
            (ns_sbs st) (ns_dentries st) (ns_inodes st) (ns_files st) (ns_prop st) e.

(** The launch's open peer groups ([env_open_groups]) replaced by [gs]. *)
Definition with_open_groups (st : NsState) (gs : list positive) : NsState :=
  with_env st (env_with_open_groups (ns_env st) gs).

Definition with_entered_mntns (st : NsState) (ns : list positive) : NsState :=
  with_env st (env_with_entered_mntns (ns_env st) ns).

(** The UTS namespace [n] of the tables. *)
Definition find_utsns (st : NsState) (n : positive) : option UtsNs :=
  find (fun u => Pos.eqb (utsns_id u) n) (ns_utsns st).

(** The UTS namespace with [u]'s id replaced by [u]. *)
Definition set_utsns (st : NsState) (u : UtsNs) : NsState :=
  with_utsns st (map (fun x => if Pos.eqb (utsns_id x) (utsns_id u) then u else x) (ns_utsns st)).

(** The context of a task that has entered no namespace: the initial
    namespaces (the host's UTS namespace [host_uts] among them), root and
    cwd at the root mount's root dentry, the umask 022, no capability, no
    securebits, no close-on-exec descriptor.  These are assumptions about
    the launcher, as the released model's launch values are: it set the
    umask to 022. *)
Definition init_nsctx : NsCtx :=
  mkNsCtx 1%positive 1%positive 1%positive 1%positive host_uts [] (1%positive, 1%positive)
          (1%positive, 1%positive) 18%Z (mkCaps 0 0 0 0 0) 0%Z [].

(** The setters of [NsCtx], one per field: with [init_nsctx], the only
    places that apply [mkNsCtx] to every field. *)
Definition with_user_ns (ctx : NsCtx) (n : positive) : NsCtx :=
  mkNsCtx n (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_uts ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx).

Definition with_mount_ns (ctx : NsCtx) (n : positive) : NsCtx :=
  mkNsCtx (cx_user ctx) n (cx_pidns ctx) (cx_net ctx) (cx_uts ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx).

Definition with_pid_ns (ctx : NsCtx) (n : positive) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) n (cx_net ctx) (cx_uts ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx).

Definition with_net_ns (ctx : NsCtx) (n : positive) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) n (cx_uts ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx).

Definition with_uts_ns (ctx : NsCtx) (n : positive) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) n (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx).

Definition with_pids (ctx : NsCtx) (ps : list (positive * Z)) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_uts ctx) ps (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx).

Definition with_root (ctx : NsCtx) (r : positive * positive) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_uts ctx) (cx_pids ctx) r
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx).

Definition with_cwd (ctx : NsCtx) (c : positive * positive) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_uts ctx) (cx_pids ctx)
          (cx_root ctx) c (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx).

Definition with_umask (ctx : NsCtx) (u : Z) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_uts ctx) (cx_pids ctx)
          (cx_root ctx) (cx_cwd ctx) u (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx).

Definition with_caps (ctx : NsCtx) (c : CapSets) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_uts ctx) (cx_pids ctx)
          (cx_root ctx) (cx_cwd ctx) (cx_umask ctx) c (cx_securebits ctx) (cx_cloexec ctx).

Definition with_securebits (ctx : NsCtx) (b : Z) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_uts ctx) (cx_pids ctx)
          (cx_root ctx) (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) b (cx_cloexec ctx).

(** The descriptors marked close-on-exec replaced by [l]. *)
Definition with_cloexec (ctx : NsCtx) (l : list Z) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_uts ctx) (cx_pids ctx)
          (cx_root ctx) (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) l.
