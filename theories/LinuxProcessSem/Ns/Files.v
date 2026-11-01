(** * LinuxProcessSem.Ns.Files — open files and their metadata, through the walk

    The arms of the calls that resolve a path with [Ns.Walk], or act on an
    open file of the namespace model: [openat] (56), [openat2] (437),
    [close] (57), [fcntl] (25), [fstat] (80), [newfstatat] (79),
    [faccessat] (48), [statfs] (43), [fstatfs] (44), [readlinkat] (78),
    [chdir] (49), [fchdir] (50), [getcwd] (17), and [getdents64] (61) on
    the task's own /proc/<pid>/fd directory.  Each header names the Linux
    6.18.44 functions it follows and its kind: exact, over (the model also
    admits outcomes it does not decide, named in the header), or declines
    ([EUnmodeled]).

    What every arm here shares:
    - a path is read with [State.read_cstr], as [getname_flags]
      (fs/namei.c) reads it: EFAULT, ENAMETOOLONG, and ENOENT for an empty
      path unless the call accepts one; the bytes are recorded as the call's
      copy-in, and only when the kernel reads them;
    - the walk knows the path of a descriptor of the namespace model
      ([Arm.ns_file_of], [Arm.fd_loc_of]) and of no other kind: where the
      kernel needs the path of another kind of descriptor, the arm
      declines;
    - search, read and write permission follow [inode_permission],
      [sb_permission], [generic_permission] and [acl_permission_check]
      (fs/namei.c) and [capable_wrt_inode_uidgid] (kernel/capability.c),
      with no ACL, no idmapped mount and no security module but the
      capability one;
    - a write to user memory goes through [Arm.put_ok]: EFAULT outside
      [access_ok], and a range that is not wholly writable declines;
    - allocation, security-module, and filesystem I/O refusals are admitted
      after the deterministic operation reaches them, and listed below in
      [file_injected]. *)

From Stdlib Require Import ZArith List Bool NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Mount Userns Walk Task.
Import ListNotations.
Local Open Scope Z_scope.

Definition EIO : Z := 5.

(** The environment failures this file represents after the path and
    descriptor checks have passed. *)
Definition file_env_errno (e : Z) : bool :=
  (e =? ENOMEM) || (e =? ENFILE) || (e =? EIO) || ((1 <=? e) && (e <=? 4095)).

(* =========================================================================
   Constants (include/uapi/asm-generic/fcntl.h, include/uapi/linux/fcntl.h,
   include/uapi/linux/openat2.h, include/uapi/linux/stat.h,
   include/linux/statfs.h, include/linux/fs.h)
   ========================================================================= *)

Definition AT_FDCWD : Z := -100.
Definition AT_SYMLINK_NOFOLLOW : Z := 256.
Definition AT_NO_AUTOMOUNT : Z := 2048.
Definition AT_EMPTY_PATH : Z := 4096.
Definition AT_STATX_SYNC_TYPE : Z := 24576.

Definition O_ACCMODE : Z := 3.
Definition O_CREAT : Z := 64.
Definition O_EXCL : Z := 128.
Definition O_NOCTTY : Z := 256.
Definition O_TRUNC : Z := 512.
Definition O_APPEND : Z := 1024.
Definition O_NONBLOCK : Z := 2048.
Definition O_DSYNC : Z := 4096.
Definition FASYNC : Z := 8192.
Definition O_DIRECT : Z := 16384.
Definition O_LARGEFILE : Z := 32768.
Definition O_DIRECTORY : Z := 65536.
Definition O_NOFOLLOW : Z := 131072.
Definition O_NOATIME : Z := 262144.
Definition O_CLOEXEC : Z := 524288.
Definition O_SYNC_BIT : Z := 1048576.   (* __O_SYNC *)
Definition O_PATH : Z := 2097152.
Definition O_TMPFILE_BIT : Z := 4194304.   (* __O_TMPFILE *)

(** [VALID_OPEN_FLAGS] and [O_PATH_FLAGS] (include/linux/fcntl.h,
    fs/open.c). *)
Definition VALID_OPEN_FLAGS : Z :=
  O_ACCMODE + O_CREAT + O_EXCL + O_NOCTTY + O_TRUNC + O_APPEND + O_NONBLOCK + O_SYNC_BIT
  + O_DSYNC + FASYNC + O_DIRECT + O_LARGEFILE + O_DIRECTORY + O_NOFOLLOW + O_NOATIME
  + O_CLOEXEC + O_PATH + O_TMPFILE_BIT.
Definition O_PATH_FLAGS : Z := O_DIRECTORY + O_NOFOLLOW + O_PATH + O_CLOEXEC.

Definition RESOLVE_NO_XDEV : Z := 1.
Definition RESOLVE_NO_MAGICLINKS : Z := 2.
Definition RESOLVE_NO_SYMLINKS : Z := 4.
Definition RESOLVE_BENEATH : Z := 8.
Definition RESOLVE_IN_ROOT : Z := 16.
Definition RESOLVE_CACHED : Z := 32.
Definition VALID_RESOLVE_FLAGS : Z := 63.

Definition S_IALLUGO : Z := 4095.
Definition S_ISGID : Z := 1024.
Definition S_ISVTX : Z := 512.
Definition S_IXGRP : Z := 8.
Definition S_IFREG : Z := 32768.

Definition MAY_EXEC : Z := 1.
Definition MAY_WRITE : Z := 2.
Definition MAY_READ : Z := 4.
Definition MAY_OPEN : Z := 32.

Definition CAP_DAC_OVERRIDE : Z := 1.
Definition CAP_DAC_READ_SEARCH : Z := 2.
Definition CAP_FSETID : Z := 4.

Definition F_GETFD : Z := 1.
Definition F_SETFD : Z := 2.
Definition F_GETFL : Z := 3.
Definition F_DUPFD_QUERY : Z := 1027.
Definition F_CREATED_QUERY : Z := 1028.
Definition F_DUPFD_CLOEXEC : Z := 1030.

Definition ST_RDONLY : Z := 1.
Definition ST_NOSUID : Z := 2.
Definition ST_NODEV : Z := 4.
Definition ST_NOEXEC : Z := 8.
Definition ST_VALID : Z := 32.
(** The [f_flags] bits the tables do not hold: ST_SYNCHRONOUS, ST_MANDLOCK
    (superblock), ST_NOATIME, ST_NODIRATIME, ST_RELATIME, ST_NOSYMFOLLOW
    (mount). *)
Definition ST_UNHELD : Z := 16 + 64 + 1024 + 2048 + 4096 + 8192.

Definition has (x b : Z) : bool := negb (Z.eqb (Z.land x b) 0).

(* =========================================================================
   Setters
   ========================================================================= *)

Definition with_cwd (ctx : NsCtx) (c : positive * positive) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx)
          c (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx)
          (cx_no_new_privs ctx) (cx_pdeathsig ctx) (cx_dumpable ctx).

Definition with_tree (st : NsState) (ds : list Dentry) (ins : list Inode) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_sbs st)
            ds ins (ns_files st) (ns_env st).

Definition drop_fd (l : list Z) (fd : Z) : list Z := List.filter (fun x => negb (Z.eqb x fd)) l.

(* =========================================================================
   Arguments and answers
   ========================================================================= *)

(** [getname_flags] (fs/namei.c) over [State.read_cstr]. *)
Inductive PathArg := PFault | PTooLong | POk (p : list byte).

Definition path_arg (i : SyscallInput) (a : word) : PathArg :=
  match read_cstr (in_mem i) a with
  | CstrOk p => POk p
  | CstrTooLong => PTooLong
  | CstrFault => PFault
  end.

Definition path_reads (i : SyscallInput) (a : word) : list (word * nat) :=
  [(a, cstr_access_len_aux (in_mem i) a path_max)].

Definition ans (reads : list (word * nat)) (r : word) (ws : list (word * list byte))
    (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  EOk (with_copyins reads (mkEffect r ws [])) m ctx st [].

Definition err (reads : list (word * nat)) (e : Z) (m : Model) (ctx : NsCtx) (st : NsState)
    : ext_outcome := ans reads (errno_ret e) [] m ctx st.

(** A descriptor argument ([unsigned int fd]): its low 32 bits. *)
Definition fd_word (w : word) : word := Z_to_bv 64 (Z.land (bv_unsigned w) 4294967295).

(** The start of a walk ([path_init], fs/namei.c): the cwd for AT_FDCWD;
    else the descriptor's path (EBADF for a number that is not open, or a
    negative one); [StNoLoc] for an open file of the namespace model that
    has no path (a socket, an eventfd); [StOver] for a descriptor of
    another kind. *)
Inductive Start := StLoc (l : Loc) | StNoLoc | StErr (e : Z) | StOver.

Definition dirfd_start (m : Model) (ctx : NsCtx) (st : NsState) (dfd : word) : Start :=
  let d := s32 dfd in
  if Z.eqb d AT_FDCWD then StLoc (ctx_cwd_loc ctx)
  else if d <? 0 then StErr EBADF
  else let w := Z_to_bv 64 d in
       match fd_lookup (m_fds m) w with
       | None => StErr EBADF
       | Some _ =>
           match ns_file_of m st w with
           | Some (_, f) => match nsfile_loc f with Some l => StLoc l | None => StNoLoc end
           | None => StOver
           end
       end.

(** [path_init] reads the descriptor only for a relative path, or under
    LOOKUP_IN_ROOT; a relative path from a directory-less object is
    ENOTDIR ([d_can_lookup]). *)
Definition walk_from (m : Model) (ctx : NsCtx) (st : NsState) (cr : WalkCreds) (dfd : word)
    (p : list byte) (fl : WalkFlags) : WalkResult * bool :=
  let s := if path_absolute p && negb (wf_in_root fl) then StLoc (ctx_cwd_loc ctx)
           else dirfd_start m ctx st dfd in
  match s with
  | StLoc l => walk st ctx cr (fd_loc_of m st) l p fl
  | StNoLoc => match p with [] => (WOver, false) | _ :: _ => (WErr ENOTDIR, false) end
  | StErr e => (WErr e, false)
  | StOver => (WOver, false)
  end.

Definition walk_parent_from (m : Model) (ctx : NsCtx) (st : NsState) (cr : WalkCreds)
    (dfd : word) (p : list byte) (fl : WalkFlags)
    : (WalkResult * list byte * LastType) * bool :=
  let s := if path_absolute p && negb (wf_in_root fl) then StLoc (ctx_cwd_loc ctx)
           else dirfd_start m ctx st dfd in
  match s with
  | StLoc l => walk_parent st ctx cr (fd_loc_of m st) l p fl
  | StNoLoc => ((match p with [] => WOver | _ :: _ => WErr ENOTDIR end, [], LastRoot), false)
  | StErr e => ((WErr e, [], LastRoot), false)
  | StOver => ((WOver, [], LastRoot), false)
  end.

Definition AT_FDCWD_word : word := Z_to_bv 64 AT_FDCWD.

(* =========================================================================
   The object at a location
   ========================================================================= *)

Definition loc_mnt (l : Loc) : positive := match l with LDentry m _ => m | LProcTask m _ _ => m end.

(** The mount a location is seen through, and its superblock. *)
Definition loc_mnt_sb (st : NsState) (l : Loc) : option (Mount * SuperBlock) :=
  match find_mount (ns_mounts st) (loc_mnt l) with
  | Some mt => match find_sb st (mnt_sb mt) with Some s => Some (mt, s) | None => None end
  | None => None
  end.

(** The task's pid in the pid namespace of the procfs instance mounted at
    [mt] is [pid]: the entry is the task's own. *)
Definition proc_own (st : NsState) (ctx : NsCtx) (mt : positive) (pid : Z) : bool :=
  match find_mount (ns_mounts st) mt with
  | Some mo =>
      match find_sb st (mnt_sb mo) with
      | Some s => match sb_kind s with
                  | SbProc ns => match pid_in (cx_pids ctx) ns with Some p => Z.eqb p pid | None => false end
                  | _ => false
                  end
      | None => false
      end
  | None => false
  end.

(** What [generic_fillattr] (fs/stat.c) and the permission checks read of
    an object: its kind, mode bits, owner kuid and kgid, the model's inode
    id ([None] for a procfs task entry, whose inode number the tables do
    not hold) and superblock id. *)
Record ObjAttr := mkObj {
  oa_kind : InodeKind;
  oa_perm : Z;
  oa_uid  : Z;
  oa_gid  : Z;
  oa_ino  : option Z;
  oa_dev  : Z
}.

(** The object at a location.  A listed dentry: its inode.  An entry of
    the task's own procfs directory ([tgid_base_stuff], fs/proc/base.c):
    the task directory (S_IFDIR 0555, owned by the task's euid and egid),
    fd (0500), ns (0511), uid_map, gid_map and setgroups (0644), mountinfo
    (0444), the cwd and root links and the ns entries (S_IFLNK 0777,
    [proc_ns_instantiate], fs/proc/namespaces.c); [task_dump_owner] makes
    every entry but the task directory owned by a root of the task's mm
    unless it is dumpable (1), and the tables do not hold that root, so a
    task that is not dumpable gives [None] there, as does an fd link (its
    mode follows the descriptor's [f_mode]) and another task's entry. *)
Definition loc_attr (m : Model) (ctx : NsCtx) (st : NsState) (l : Loc) : option ObjAttr :=
  match l with
  | LDentry _ d =>
      match find_dentry st d with
      | Some x =>
          match find_inode st (d_inode x) with
          | Some ino => Some (mkObj (ino_kind ino) (ino_perm ino) (ino_uid ino) (ino_gid ino)
                                    (Some (Zpos (ino_id ino))) (Zpos (d_sb x)))
          | None => None
          end
      | None => None
      end
  | LProcTask mt pid rest =>
      match find_mount (ns_mounts st) mt with
      | None => None
      | Some mo =>
          if negb (proc_own st ctx mt pid) then None
          else
            let u := bv_unsigned (cr_euid (m_creds m)) in
            let g := bv_unsigned (cr_egid (m_creds m)) in
            let dev := Zpos (mnt_sb mo) in
            let mk k p := Some (mkObj k p u g None dev) in
            match rest with
            | [] => mk IDir 365
            | _ =>
                if negb (Z.eqb (cx_dumpable ctx) 1) then None
                else match rest with
                     | [n] =>
                         if bytes_eqb n proc_fd_name then mk IDir 320
                         else if bytes_eqb n proc_ns_name then mk IDir 329
                         else if bytes_eqb n proc_uid_map_name || bytes_eqb n proc_gid_map_name
                                 || bytes_eqb n proc_setgroups_name then mk IReg 420
                         else if bytes_eqb n proc_mountinfo_name then mk IReg 292
                         else if bytes_eqb n proc_cwd_name || bytes_eqb n proc_root_name
                         then mk ILnk 511
                         else None
                     | [n; k] =>
                         if bytes_eqb n proc_ns_name && existsb (bytes_eqb k) proc_ns_entries
                         then mk ILnk 511 else None
                     | _ => None
                     end
            end
      end
  end.

Definition kind_is (k : InodeKind) (a : ObjAttr) : bool :=
  match k, oa_kind a with
  | IDir, IDir | IReg, IReg | ILnk, ILnk | IChr, IChr | IBlk, IBlk | IFifo, IFifo
  | ISock, ISock => true
  | _, _ => false
  end.

(** [special_file] (include/linux/fs.h): a device, FIFO or socket. *)
Definition special (a : ObjAttr) : bool :=
  kind_is IChr a || kind_is IBlk a || kind_is IFifo a || kind_is ISock a.

(* =========================================================================
   Permission
   ========================================================================= *)

(** [in_group_p] (kernel/groups.c): the fsgid or a supplementary group. *)
Definition in_group (cr : WalkCreds) (g : Z) : bool :=
  Z.eqb (wc_fsgid cr) g || existsb (Z.eqb g) (wc_groups cr).

(** [acl_permission_check] (fs/namei.c) with no ACL: the owner's bits for
    the owner; the group's bits for a member of the group, read only when
    they differ from the other bits; else the other bits. *)
Definition acl_permission_check (cr : WalkCreds) (a : ObjAttr) (mask : Z) : bool :=
  let mode := oa_perm a in
  let m7 := Z.land mask 7 in
  if Z.eqb (wc_fsuid cr) (oa_uid a) then Z.eqb (Z.land m7 (Z.lnot (Z.shiftr mode 6))) 0
  else
    let mode' := if negb (Z.eqb (Z.land m7 (Z.lxor mode (Z.shiftr mode 3))) 0) && in_group cr (oa_gid a)
                 then Z.shiftr mode 3 else mode in
    Z.eqb (Z.land m7 (Z.lnot mode')) 0.

(** [privileged_wrt_inode_uidgid] (kernel/capability.c) on ids. *)
Definition uidgid_mapped (st : NsState) (ctx : NsCtx) (uid gid : Z) : bool :=
  match find_userns (ns_userns st) (cx_user ctx) with
  | None => false
  | Some u =>
      match uns_parent u with
      | None => true
      | Some _ =>
          match uns_uid_map u, uns_gid_map u with
          | Some um, Some gm => kid_mapped um uid && kid_mapped gm gid
          | _, _ => false
          end
      end
  end.

(** [capable_wrt_inode_uidgid] with the effective set [eff]. *)
Definition capable_over (st : NsState) (ctx : NsCtx) (eff : Z) (a : ObjAttr) (cap : Z) : bool :=
  Z.testbit eff cap && uidgid_mapped st ctx (oa_uid a) (oa_gid a).

(** [generic_permission] (fs/namei.c). *)
Definition generic_permission (st : NsState) (ctx : NsCtx) (cr : WalkCreds) (eff : Z)
    (a : ObjAttr) (mask : Z) : bool :=
  acl_permission_check cr a mask
  || match oa_kind a with
     | IDir => (negb (has mask MAY_WRITE) && capable_over st ctx eff a CAP_DAC_READ_SEARCH)
               || capable_over st ctx eff a CAP_DAC_OVERRIDE
     | _ => (Z.eqb (Z.land mask 7) MAY_READ && capable_over st ctx eff a CAP_DAC_READ_SEARCH)
            || ((negb (has mask MAY_EXEC) || has (oa_perm a) 73)
                && capable_over st ctx eff a CAP_DAC_OVERRIDE)
     end.

Definition proc_fd_dir (l : Loc) : bool :=
  match l with LProcTask _ _ [n] => bytes_eqb n proc_fd_name | _ => false end.

(** [inode_permission] (fs/namei.c): [sb_permission]'s EROFS for a write
    to a regular file, directory or link of a read-only superblock; then
    [generic_permission], or [proc_fd_permission] (fs/proc/fd.c), which
    lets the task's own thread group into its fd directory.  [None]: the
    access is granted. *)
Definition inode_permission (st : NsState) (ctx : NsCtx) (cr : WalkCreds) (eff : Z) (l : Loc)
    (sb : SuperBlock) (a : ObjAttr) (mask : Z) : option Z :=
  if has mask MAY_WRITE && sb_rdonly sb && (kind_is IReg a || kind_is IDir a || kind_is ILnk a)
  then Some EROFS
  else if proc_fd_dir l || generic_permission st ctx cr eff a mask then None
  else Some EACCES.

Definition task_eff (ctx : NsCtx) : Z := cap_effective (cx_caps ctx).

(* =========================================================================
   openat, openat2
   ========================================================================= *)

Record OpenHow := mkHow { how_flags : Z; how_mode : Z; how_resolve : Z }.

(** [ACC_MODE] (include/linux/fs.h). *)
Definition acc_mode (flags : Z) : Z :=
  let a := Z.land flags O_ACCMODE in
  if Z.eqb a 0 then MAY_READ else if Z.eqb a 1 then MAY_WRITE else MAY_READ + MAY_WRITE.

Definition will_create (flags : Z) : bool := has flags (O_CREAT + O_TMPFILE_BIT).

(** [build_open_flags] (fs/open.c), in its order.  [BuiltOk flags acc]:
    the open flags ([op->open_flag]) and the access mode the open checks.
    A resolve bit other than RESOLVE_IN_ROOT and RESOLVE_NO_MAGICLINKS
    declines once the checks that refuse it have passed. *)
Inductive Built := BuiltErr (e : Z) | BuiltOver | BuiltOk (flags acc : Z).

Definition build_open_flags (h : OpenHow) : Built :=
  let flags := Z.land (how_flags h) (Z.lnot O_CLOEXEC) in
  let res := how_resolve h in
  let acc := acc_mode flags in
  if negb (Z.eqb (Z.land flags (Z.lnot VALID_OPEN_FLAGS)) 0) then BuiltErr EINVAL
  else if negb (Z.eqb (Z.land res (Z.lnot VALID_RESOLVE_FLAGS)) 0) then BuiltErr EINVAL
  else if has res RESOLVE_BENEATH && has res RESOLVE_IN_ROOT then BuiltErr EINVAL
  else if will_create flags && negb (Z.eqb (Z.land (how_mode h) (Z.lnot S_IALLUGO)) 0)
  then BuiltErr EINVAL
  else if negb (will_create flags) && negb (Z.eqb (how_mode h) 0) then BuiltErr EINVAL
  else if has flags O_DIRECTORY && has flags O_CREAT then BuiltErr EINVAL
  else if has flags O_TMPFILE_BIT && negb (has flags O_DIRECTORY) then BuiltErr EINVAL
  else if has flags O_TMPFILE_BIT && negb (has acc MAY_WRITE) then BuiltErr EINVAL
  else if has flags O_PATH && negb (Z.eqb (Z.land flags (Z.lnot O_PATH_FLAGS)) 0)
  then BuiltErr EINVAL
  else if has res (RESOLVE_NO_XDEV + RESOLVE_NO_SYMLINKS + RESOLVE_BENEATH + RESOLVE_CACHED)
  then BuiltOver
  else
    let flags' := if has flags O_SYNC_BIT then Z.lor flags O_DSYNC else flags in
    let acc' := if has flags O_PATH then 0
                else if has flags O_TRUNC then Z.lor acc MAY_WRITE else acc in
    BuiltOk flags' acc'.

(** The walk an open makes: LOOKUP_FOLLOW unless O_NOFOLLOW or
    O_CREAT|O_EXCL, LOOKUP_DIRECTORY for O_DIRECTORY, and the two resolve
    bits answered. *)
Definition open_lookup (flags resolve : Z) : WalkFlags :=
  mkWalkFlags (negb (has flags O_NOFOLLOW || (has flags O_CREAT && has flags O_EXCL)))
              (has flags O_DIRECTORY) false (has resolve RESOLVE_NO_MAGICLINKS)
              (has resolve RESOLVE_IN_ROOT).

(** The flags an open answers besides O_PATH: an access mode 0, 1 or 2,
    O_CREAT, O_EXCL, O_NOCTTY, O_TRUNC, O_APPEND, O_NONBLOCK, O_DSYNC,
    __O_SYNC, O_LARGEFILE, O_DIRECTORY, O_NOFOLLOW.  O_ACCMODE 3, FASYNC,
    O_DIRECT, O_NOATIME and __O_TMPFILE decline. *)
Definition open_answered (flags : Z) : bool :=
  negb (Z.eqb (Z.land flags O_ACCMODE) O_ACCMODE)
  && negb (has flags (FASYNC + O_DIRECT + O_NOATIME + O_TMPFILE_BIT)).

(** What an open ends with: an errno, a decline, or the state (with a
    created file) and the kind of the new open file. *)
Inductive OpenRes := ORErr (e : Z) | OROver | OROk (st : NsState) (k : NsFileKind).

(** The [f_mode] write bit ([OPEN_FMODE]): access mode 1 or 2. *)
Definition fmode_write (flags : Z) : bool :=
  let a := Z.land flags O_ACCMODE in Z.eqb a 1 || Z.eqb a 2.

Definition is_setgroups (l : Loc) : bool :=
  match l with LProcTask _ _ [n] => bytes_eqb n proc_setgroups_name | _ => false end.

(** A task's uid_map, gid_map or setgroups: the open binds the task's user
    namespace ([proc_id_map_open], [proc_setgroups_open]); the task is the
    caller, the only one whose procfs files the walk resolves. *)
Definition is_userns_file (l : Loc) : bool :=
  match l with
  | LProcTask _ _ [n] => bytes_eqb n proc_uid_map_name || bytes_eqb n proc_gid_map_name
                         || bytes_eqb n proc_setgroups_name
  | _ => false
  end.
(** A /proc/sys/user/max_* dentry is bound to the opener's user namespace.
    The names are checked from the procfs root, so another file system's
    like-named dentry is not accepted. *)
Definition proc_sys_name : list byte := ascii [115; 121; 115].
Definition proc_user_name : list byte := ascii [117; 115; 101; 114].
Definition proc_max_prefix : list byte := ascii [109; 97; 120; 95].
Definition CAP_SYS_RESOURCE : Z := 24.

Fixpoint proc_name_prefixb (pre xs : list byte) : bool :=
  match pre, xs with
  | [], _ => true
  | p :: ps, x :: xs' => Z.eqb (bv_unsigned p) (bv_unsigned x) && proc_name_prefixb ps xs'
  | _ :: _, [] => false
  end.

Fixpoint dentry_names_from_root_fuel (fuel : nat) (st : NsState) (d : positive)
    : option (list (list byte)) :=
  match fuel with
  | O => None
  | S f =>
      match find_dentry st d with
      | Some x =>
          match d_parent x with
          | None => Some []
          | Some p => option_map (fun ns => ns ++ [d_name x])
                                  (dentry_names_from_root_fuel f st p)
          end
      | None => None
      end
  end.

Definition is_user_sys_file (st : NsState) (l : Loc) : bool :=
  match l with
  | LDentry _ d =>
      match loc_mnt_sb st l, dentry_names_from_root_fuel (S (length (ns_dentries st))) st d with
      | Some (_, sb), Some [a; b; n] =>
          match sb_kind sb with
          | SbProc _ => bytes_eqb a proc_sys_name && bytes_eqb b proc_user_name
                      && proc_name_prefixb proc_max_prefix n
          | _ => false
          end
      | _, _ => false
      end
  | _ => false
  end.

Definition is_mountinfo_file (l : Loc) : bool :=
  match l with LProcTask _ _ [n] => bytes_eqb n proc_mountinfo_name | _ => false end.

(** [set_permissions] (kernel/ucount.c): CAP_SYS_RESOURCE over the opener's
    user namespace gives all classes the 0644 owner bits; otherwise each
    gets only the 0644 other read bit. *)
Definition sysctl_permissions (m : Model) (ctx : NsCtx) (st : NsState) (l : Loc)
    (a : ObjAttr) : ObjAttr :=
  if is_user_sys_file st l
  then mkObj (oa_kind a) (if own_capable m ctx st CAP_SYS_RESOURCE then 438 else 292)
             (oa_uid a) (oa_gid a) (oa_ino a) (oa_dev a)
  else a.


(** [may_create_in_sticky] (fs/namei.c) on an O_CREAT open of an existing
    regular file or FIFO in a sticky directory that the caller and the
    directory's owner do not own: its answer is the protected_regular or
    protected_fifos sysctl's, which the tables do not hold, wherever the
    directory is group- or world-writable. *)
Definition sticky_undecided (cr : WalkCreds) (dir a : ObjAttr) : bool :=
  has (oa_perm dir) S_ISVTX && (kind_is IReg a || kind_is IFifo a)
  && negb (Z.eqb (oa_uid a) (oa_uid dir)) && negb (Z.eqb (oa_uid a) (wc_fsuid cr))
  && has (oa_perm dir) 18.

(** [do_open] (fs/namei.c) after the walk found [l]: with O_CREAT,
    EISDIR for a directory and [may_create_in_sticky]; O_TRUNC on a regular
    file ([mnt_want_write]: EROFS on a read-only mount; the truncation
    itself declines); [may_open] (ELOOP for a link not followed, EISDIR
    for a directory opened for writing, EACCES for a device on a nodev
    mount, a device, FIFO or socket opened otherwise declines, then
    [inode_permission]); [vfs_open]: EROFS for a write on a read-only mount
    ([file_get_write_access]), and [proc_setgroups_open]'s EACCES for a
    writer without CAP_SYS_ADMIN over the task's user namespace. *)
Definition open_existing (m : Model) (ctx : NsCtx) (st : NsState) (cr : WalkCreds)
    (flags acc : Z) (creat_dir : option ObjAttr) (l : Loc) : OpenRes :=
  match loc_mnt_sb st l, loc_attr m ctx st l with
  | Some (mt, sb), Some a =>
      let ro := mf_ro (mnt_flags mt) || sb_rdonly sb in
      let opened := sysctl_permissions m ctx st l a in
      let perm_then_open :=
        match inode_permission st ctx cr (task_eff ctx) l sb opened (Z.lor MAY_OPEN acc) with
        | Some e => ORErr e
        | None =>
            if fmode_write flags && negb (special opened) && ro then ORErr EROFS
            else if is_setgroups l && fmode_write flags && negb (own_capable m ctx st CAP_SYS_ADMIN)
            then ORErr EACCES
            else OROk st (if kind_is IDir opened then NfDir l 0
                          else if is_mountinfo_file l then NfMountinfo l (cx_mount ctx) (cx_root ctx) 0
                          else if is_userns_file l || is_user_sys_file st l
                               then NfUserNsFile l (cx_user ctx) 0
                               else NfFile l 0)
        end in
      match creat_dir with
      | Some d =>
          if kind_is IDir a then ORErr EISDIR
          else if sticky_undecided cr d a then OROver
          else if has flags O_TRUNC && kind_is IReg a then (if ro then ORErr EROFS else OROver)
          else match oa_kind a with
               | ILnk => ORErr ELOOP
               | IChr | IBlk => if mf_nodev (mnt_flags mt) || sb_i_nodev sb then ORErr EACCES else OROver
               | IFifo | ISock => OROver
               | _ => perm_then_open
               end
      | None =>
          if has flags O_TRUNC && kind_is IReg a then (if ro then ORErr EROFS else OROver)
          else match oa_kind a with
               | ILnk => ORErr ELOOP
               | IDir => if has acc MAY_WRITE then ORErr EISDIR else perm_then_open
               | IChr | IBlk => if mf_nodev (mnt_flags mt) || sb_i_nodev sb then ORErr EACCES else OROver
               | IFifo | ISock => OROver
               | IReg => perm_then_open
               end
      end
  | _, _ => OROver
  end.

(** The name [name] in directory [P]: [Some true] when it exists, [Some
    false] when it does not, [None] when the tables do not decide (a
    procfs directory). *)
Definition child_exists (st : NsState) (P : Loc) (name : list byte) : option bool :=
  match P with
  | LDentry _ d =>
      match child_dentry st d name with
      | Some _ => Some true
      | None => match proc_root_pidns st d with
                | Some None => Some false
                | _ => None
                end
      end
  | LProcTask _ _ _ => None
  end.

(** [fsuidgid_has_mapping] (fs/namei.c): the fsuid and fsgid have a
    mapping in the superblock's user namespace. *)
Definition fsuidgid_mapped (st : NsState) (owner : positive) (cr : WalkCreds) : bool :=
  match find_userns (ns_userns st) owner with
  | None => false
  | Some u =>
      match uns_parent u with
      | None => true
      | Some _ =>
          match uns_uid_map u, uns_gid_map u with
          | Some um, Some gm => kid_mapped um (wc_fsuid cr) && kid_mapped gm (wc_fsgid cr)
          | _, _ => false
          end
      end
  end.

Definition max_dentry_id (st : NsState) : positive :=
  fold_left (fun acc d => Pos.max acc (d_id d)) (ns_dentries st) 1%positive.
Definition max_inode_id (st : NsState) : positive :=
  fold_left (fun acc n => Pos.max acc (ino_id n)) (ns_inodes st) 1%positive.

(** A new regular file [name] in tmpfs directory [P] ([lookup_open],
    [may_o_create], [vfs_prepare_mode], fs/namei.c; [shmem_create],
    [shmem_mknod], mm/shmem.c; [inode_init_owner], [mode_strip_sgid],
    fs/inode.c).  In kernel order: the create error, computed first
    (EROFS when the mount or superblock is read-only, EOVERFLOW when the
    fsuid or fsgid has no mapping in the superblock's namespace, then
    write and search permission on the directory); the file system's
    lookup, [simple_lookup] (fs/libfs.c), refusing a name longer than
    NAME_MAX with ENAMETOOLONG; then the create error.  The new inode: the
    fsuid, the fsgid or the directory's group when the directory has
    S_ISGID, and [mode & ~umask & 07777] after [mode_strip_sgid].  In a
    host, devpts or procfs directory the create declines: the host's file
    system decides the new inode, devpts and procfs have their own
    refusals. *)
Definition create_file (m : Model) (ctx : NsCtx) (st : NsState) (cr : WalkCreds) (P : Loc)
    (name : list byte) (mode : Z) : OpenRes :=
  match P with
  | LProcTask _ _ _ => OROver
  | LDentry mn d =>
      match find_dentry st d, loc_mnt_sb st P, dentry_inode st d with
      | Some dx, Some (mt, sb), Some dino =>
          match sb_kind sb with
          | SbTmpfs =>
              let dattr := mkObj (ino_kind dino) (ino_perm dino) (ino_uid dino) (ino_gid dino) None
                                 (Zpos (sb_id sb)) in
              let create_error :=
                if mf_ro (mnt_flags mt) || sb_rdonly sb then Some EROFS
                else if negb (fsuidgid_mapped st (sb_owner sb) cr) then Some EOVERFLOW
                else inode_permission st ctx cr (task_eff ctx) P sb dattr (MAY_WRITE + MAY_EXEC) in
              if Nat.ltb NAME_MAX (length name) then ORErr ENAMETOOLONG
              else match create_error with
                   | Some e => ORErr e
                   | None =>
                       let dir_sgid := has (ino_perm dino) S_ISGID in
                       let mode0 := Z.lor mode S_IFREG in
                       let mode1 :=
                         if has mode0 S_ISGID && has mode0 S_IXGRP && dir_sgid
                            && negb (in_group cr (ino_gid dino)
                                     || capable_over st ctx (task_eff ctx) dattr CAP_FSETID)
                         then Z.land mode0 (Z.lnot S_ISGID) else mode0 in
                       let perm := Z.land (Z.land mode1 (Z.lnot (cx_umask ctx))) S_IALLUGO in
                       let gid := if dir_sgid then ino_gid dino else wc_fsgid cr in
                       let nd := Pos.succ (max_dentry_id st) in
                       let ni := Pos.succ (max_inode_id st) in
                       let st' := with_tree st (ns_dentries st ++ [mkDentry nd (d_sb dx) (Some d) name ni])
                                            (ns_inodes st ++ [mkInode ni IReg perm (wc_fsuid cr) gid 0 [] false]) in
                       OROk st' (NfFile (LDentry mn nd) 0)
                   end
          | _ => OROver
          end
      | _, _, _ => OROver
      end
  end.

(** An O_CREAT open ([open_last_lookups], [lookup_fast_for_open],
    [lookup_open], [do_open], fs/namei.c): the directory of the last name
    by [Walk.walk_parent]; a last component that is not a name is EEXIST
    under O_EXCL and EISDIR otherwise; a trailing '/' is EISDIR; an
    existing name is EEXIST under O_EXCL (a link included: O_EXCL does not
    follow), else the existing object opened as [open_existing] finds it
    (a link whose target the walk does not reach declines: the kernel
    would create the target); a free name is created ([create_file]). *)
Definition open_creat (m : Model) (ctx : NsCtx) (st : NsState) (cr : WalkCreds) (dfd : word)
    (p : list byte) (flags resolve mode acc : Z) : OpenRes * bool :=
  let fl := open_lookup flags resolve in
  match walk_parent_from m ctx st cr dfd p fl with
  | ((WErr e, _, _), b) => (ORErr e, b)
  | ((WOver, _, _), b) => (OROver, b)
  | ((WOk P, name, ty), b) =>
      let dots := if has flags O_EXCL then ORErr EEXIST else ORErr EISDIR in
      match ty with
      | LastNorm =>
          if path_trailing_slash p then (ORErr EISDIR, b)
          else match child_exists st P name with
               | Some true =>
                   if has flags O_EXCL then (ORErr EEXIST, b)
                   else match walk_from m ctx st cr dfd p fl, loc_attr m ctx st P with
                        | (WOk l, b'), Some dattr => (open_existing m ctx st cr flags acc (Some dattr) l, b || b')
                        | (_, b'), _ => (OROver, b || b')
                        end
               | Some false => (create_file m ctx st cr P name mode, b)
               | None => (OROver, b)
               end
      | LastDotDot => (dots, b || wf_in_root fl)
      | _ => (dots, b)
      end
  end.

(** [path_openat] (fs/namei.c): [do_o_path] for O_PATH (the walk alone;
    O_PATH|O_NOFOLLOW on a link gives the link); else the walk and
    [do_open]. *)
Definition open_target (m : Model) (ctx : NsCtx) (st : NsState) (cr : WalkCreds) (dfd : word)
    (p : list byte) (flags resolve mode acc : Z) : OpenRes * bool :=
  let fl := open_lookup flags resolve in
  if has flags O_PATH then
    match walk_from m ctx st cr dfd p fl with
    | (WOk l, b) => (OROk st (NfPath l), b)
    | (WErr e, b) => (ORErr e, b)
    | (WOver, b) => (OROver, b)
    end
  else if negb (open_answered flags) then (OROver, false)
  else if has flags O_CREAT then open_creat m ctx st cr dfd p flags resolve mode acc
  else match walk_from m ctx st cr dfd p fl with
       | (WOk l, b) => (open_existing m ctx st cr flags acc None l, b)
       | (WErr e, b) => (ORErr e, b)
       | (WOver, b) => (OROver, b)
       end.

(** [f_flags] of the new file: the open flags; [do_dentry_open]
    (fs/open.c) clears O_CREAT, O_EXCL, O_NOCTTY and O_TRUNC unless the
    file is O_PATH. *)
Definition file_flags (flags : Z) : Z :=
  if has flags O_PATH then flags
  else Z.land flags (Z.lnot (O_CREAT + O_EXCL + O_NOCTTY + O_TRUNC)).

(** [fd_install] at [fd] of a new open file: a fresh handle, the opener's
    credential ([f_cred]), and the close-on-exec bit set exactly when
    O_CLOEXEC was asked ([get_unused_fd_flags], fs/file.c). *)
Definition install (reads : list (word * nat)) (m : Model) (ctx : NsCtx) (st : NsState)
    (fd : word) (k : NsFileKind) (fflags : Z) (cloexec : bool) : ext_outcome :=
  let h := fresh_handle st in
  let st' := with_files st ((h, mkNsFile k fflags (task_cred m ctx)) :: ns_files st) in
  let m' := with_fds (fd_insert (m_fds m) fd (ns_fd_entry h)) m in
  let n := bv_unsigned fd in
  let cl := drop_fd (cx_cloexec ctx) n in
  ans reads fd [] m' (with_cloexec ctx (if cloexec then n :: cl else cl)) st'.

(** [do_sys_openat2] (fs/open.c): [build_open_flags], then [getname]
    (EFAULT, ENAMETOOLONG, ENOENT for an empty path), then
    [get_unused_fd_flags] (the lowest free descriptor, EMFILE at the soft
    RLIMIT_NOFILE), then [do_filp_open].  The boolean: the walk took a ".."
    under LOOKUP_IN_ROOT, where Linux may also answer EAGAIN. *)
Definition open_common (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (reads0 : list (word * nat)) (dfd pathp : word) (h : OpenHow)
    : (ext_outcome * list (word * nat)) * bool :=
  match build_open_flags h with
  | BuiltErr e => ((err reads0 e m ctx st, reads0), false)
  | BuiltOver => ((EUnmodeled, reads0), false)
  | BuiltOk flags acc =>
      let reads := reads0 ++ path_reads i pathp in
      match path_arg i pathp with
      | PFault => ((err reads EFAULT m ctx st, reads), false)
      | PTooLong => ((err reads ENAMETOOLONG m ctx st, reads), false)
      | POk [] => ((err reads ENOENT m ctx st, reads), false)
      | POk p =>
          let fd := alloc_fd (m_fds m) in
          if negb (bv_unsigned fd <? bv_unsigned (m_nofile m)) then ((err reads EMFILE m ctx st, reads), false)
          else match fd_lookup (m_fds m) fd with
               | Some _ => ((EUnmodeled, reads), false)
               | None =>
                   let r := open_target m ctx st (walk_creds m) dfd p flags (how_resolve h) (how_mode h) acc in
                   let o := match fst r with
                            | ORErr e => err reads e m ctx st
                            | OROver => EUnmodeled
                            | OROk st' k => install reads m ctx st' fd k (file_flags flags) (has (how_flags h) O_CLOEXEC)
                            end in
                   ((o, reads), snd r)
               end
      end
  end.

(** [SYSCALL_DEFINE4(openat)] and [build_open_how] (fs/open.c): the low 32
    bits of the flags with O_LARGEFILE added, cut to VALID_OPEN_FLAGS (and
    to O_PATH_FLAGS under O_PATH); the mode cut to 07777, and zero unless
    the open creates. *)
Definition openat_how (i : SyscallInput) : OpenHow :=
  let fl := Z.land (Z.lor (Z.land (bv_unsigned (in_arg i 2)) 4294967295) O_LARGEFILE) VALID_OPEN_FLAGS in
  let fl' := if has fl O_PATH then Z.land fl O_PATH_FLAGS else fl in
  let md := Z.land (bv_unsigned (in_arg i 3)) S_IALLUGO in
  mkHow fl' (if will_create fl' then md else 0) 0.

(** [openat] (56): [SYSCALL_DEFINE4(openat)], [do_sys_openat2],
    [build_open_flags], [do_filp_open] (fs/open.c, fs/namei.c).  Kind:
    exact on objects the tables list; the decline cases are in
    [open_answered], [open_existing], [open_creat] and [create_file]. *)
Definition openat_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  fst (fst (open_common i m ctx st [] (in_arg i 0) (in_arg i 1) (openat_how i))).

Definition openat_arm : NsArm := fun i m ctx st o =>
  o = openat_fn i m ctx st
  \/ injected_after file_env_errno (openat_fn i m ctx st) m ctx st o.

(** [SYSCALL_DEFINE4(openat2)] (fs/open.c): a size below
    OPEN_HOW_SIZE_VER0 (24) is EINVAL, above a page E2BIG;
    [copy_struct_from_user] refuses non-zero bytes past 24 with E2BIG and
    an unreadable range with EFAULT; O_LARGEFILE is added unless O_PATH. *)
Definition openat2_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    : (ext_outcome * list (word * nat)) * bool :=
  let howp := in_arg i 2 in
  let usize := bv_unsigned (in_arg i 3) in
  if usize <? 24 then ((ns_errno EINVAL m ctx st, []), false)
  else if 4096 <? usize then ((ns_errno E2BIG m ctx st, []), false)
  else if negb (access_okb howp usize) then ((ns_errno EFAULT m ctx st, []), false)
  else match read_bytes_map (in_mem i) howp (Z_to_bv 64 usize) with
       | None => ((EUnmodeled, []), false)
       | Some bs =>
           let reads := [(howp, Z.to_nat usize)] in
           if negb (forallb (fun b => Z.eqb (bv_unsigned b) 0) (skipn 24 bs))
           then ((err reads E2BIG m ctx st, reads), false)
           else
             let fl := bytes_le_to_Z (firstn 8 bs) in
             let md := bytes_le_to_Z (firstn 8 (skipn 8 bs)) in
             let rs := bytes_le_to_Z (firstn 8 (skipn 16 bs)) in
             let fl' := if has fl O_PATH then fl else Z.lor fl O_LARGEFILE in
             open_common i m ctx st reads (in_arg i 0) (in_arg i 1) (mkHow fl' md rs)
       end.

(** [openat2] (437): as [openat], with the open_how's resolve bits.  Kind:
    over: under RESOLVE_IN_ROOT a walk that took a ".." may also answer
    EAGAIN ([handle_dots], fs/namei.c: a rename or mount anywhere in the
    system during the walk). *)
Definition openat2_arm : NsArm := fun i m ctx st o =>
  let r := openat2_fn i m ctx st in
  o = fst (fst r)
  \/ (snd r = true /\ o = err (snd (fst r)) EAGAIN m ctx st)
  \/ injected_after file_env_errno (fst (fst r)) m ctx st o.

(* =========================================================================
   close, fcntl
   ========================================================================= *)

(** [close] (57): [SYSCALL_DEFINE1(close)], [file_close_fd], [filp_flush]
    (fs/open.c, fs/file.c).  On a descriptor of the namespace model the
    entry and its close-on-exec bit go, and the open file goes when no
    other descriptor names it; 0, as [filp_flush] cannot fail on the
    objects the model mints.  Every other descriptor and number: the
    released answer.  Kind: exact. *)
Definition close_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    : option ext_outcome :=
  let w := fd_word (in_arg i 0) in
  match ns_file_of m st w with
  | Some (h, _) =>
      let fds' := fd_remove (m_fds m) w in
      let named := existsb (fun p => match fd_entry_handle (snd p) with
                                     | Some h' => N.eqb h h'
                                     | None => false
                                     end) fds' in
      let st' := if named then st
                 else with_files st (List.filter (fun p => negb (N.eqb (fst p) h)) (ns_files st)) in
      Some (EOk (mkEffect (Z_to_bv 64 0) [] []) (with_fds fds' m)
                (with_cloexec ctx (drop_fd (cx_cloexec ctx) (bv_unsigned w))) st' [])
  | None => None
  end.

Definition close_arm : NsArm := fun i m ctx st o =>
  match close_fn i m ctx st with Some r => o = r | None => released i m ctx st o end.

Definition is_path_file (f : NsFile) : bool :=
  match nf_kind f with NfPath _ => true | _ => false end.

(** [check_fcntl_cmd] (fs/fcntl.c): the commands an O_PATH file accepts. *)
Definition fcntl_path_cmd (cmd : Z) : bool :=
  Z.eqb cmd 0 || Z.eqb cmd F_GETFD || Z.eqb cmd F_SETFD || Z.eqb cmd F_GETFL
  || Z.eqb cmd F_DUPFD_QUERY || Z.eqb cmd F_CREATED_QUERY || Z.eqb cmd F_DUPFD_CLOEXEC.

(** [fcntl] (25): [SYSCALL_DEFINE3(fcntl)], [do_fcntl] (fs/fcntl.c) on a
    descriptor of the namespace model: EBADF for a command an O_PATH file
    refuses; F_GETFD and F_SETFD (FD_CLOEXEC) on the close-on-exec bit;
    F_GETFL the file's [f_flags]; any other command declines.  Every other
    descriptor and number: the released answer.  Kind: exact. *)
Definition fcntl_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    : option ext_outcome :=
  let w := fd_word (in_arg i 0) in
  let cmd := Z.land (bv_unsigned (in_arg i 1)) 4294967295 in
  match ns_file_of m st w with
  | None => None
  | Some (_, f) =>
      let n := bv_unsigned w in
      if is_path_file f && negb (fcntl_path_cmd cmd) then Some (ns_errno EBADF m ctx st)
      else if Z.eqb cmd F_GETFD
      then Some (ns_ret (Z_to_bv 64 (if existsb (Z.eqb n) (cx_cloexec ctx) then 1 else 0)) m ctx st)
      else if Z.eqb cmd F_SETFD
      then let cl := drop_fd (cx_cloexec ctx) n in
           Some (ns_ret (Z_to_bv 64 0) m
                        (with_cloexec ctx (if Z.testbit (bv_unsigned (in_arg i 2)) 0 then n :: cl else cl)) st)
      else if Z.eqb cmd F_GETFL then Some (ns_ret (Z_to_bv 64 (nf_flags f)) m ctx st)
      else Some EUnmodeled
  end.

Definition fcntl_arm : NsArm := fun i m ctx st o =>
  match fcntl_fn i m ctx st with Some r => o = r | None => released i m ctx st o end.

(* =========================================================================
   fstat, newfstatat
   ========================================================================= *)

(** The [S_IFMT] bits of a kind (include/uapi/linux/stat.h). *)
Definition ifmt (k : InodeKind) : Z :=
  match k with
  | IDir => 16384 | IReg => 32768 | ILnk => 40960 | IChr => 8192 | IBlk => 24576
  | IFifo => 4096 | ISock => 49152
  end.

(** [map_id_up] (kernel/user_namespace.c): the id an extent's lower range
    holds, seen from its first range. *)
Fixpoint map_up (exts : list IdExtent) (k : Z) : option Z :=
  match exts with
  | [] => None
  | e :: r => if (ext_lower e <=? k) && (k <? ext_lower e + ext_count e)
              then Some (ext_first e + (k - ext_lower e)) else map_up r k
  end.

(** [map_id_down] (kernel/user_namespace.c): the kernel id an extent's
    first range maps [k] to. *)
Fixpoint map_down (exts : list IdExtent) (k : Z) : option Z :=
  match exts with
  | [] => None
  | e :: r => if (ext_first e <=? k) && (k <? ext_first e + ext_count e)
              then Some (ext_lower e + (k - ext_first e)) else map_down r k
  end.

(** [from_kuid_munged] / [from_kgid_munged] (kernel/user_namespace.c):
    the id in the caller's user namespace, or the overflow id 65534
    (the default of kernel.overflowuid and kernel.overflowgid). *)
Definition munged (st : NsState) (ctx : NsCtx) (gid : bool) (k : Z) : Z :=
  match find_userns (ns_userns st) (cx_user ctx) with
  | None => 65534
  | Some u =>
      match uns_parent u with
      | None => k
      | Some _ =>
          match (if gid then uns_gid_map u else uns_uid_map u) with
          | Some ex => match map_up ex k with Some v => v | None => 65534 end
          | None => 65534
          end
      end
  end.

(** The fields of the 128-byte riscv64 [struct stat]
    (include/uapi/asm-generic/stat.h) that [generic_fillattr] and
    [cp_new_stat] (fs/stat.c) fill from what the tables hold, by byte
    offset: [st_dev] the superblock's id and [st_ino] the inode's id (the
    model's names for [s_dev] and [i_ino], equal exactly when the kernel's
    are), [st_mode] the type and mode bits, [st_uid] and [st_gid] mapped
    into the caller's namespace. *)
Definition stat_fields (st : NsState) (ctx : NsCtx) (a : ObjAttr) : list (nat * list byte) :=
  [(16%nat, Z_to_le_bytes 4 (Z.lor (ifmt (oa_kind a)) (oa_perm a)));
   (24%nat, Z_to_le_bytes 4 (munged st ctx false (oa_uid a)));
   (28%nat, Z_to_le_bytes 4 (munged st ctx true (oa_gid a)))].

Definition fields_match (n : nat) (fs : list (nat * list byte)) (bs : list byte) : bool :=
  Nat.eqb (length bs) n
  && forallb (fun p => bytes_eqb (firstn (length (snd p)) (skipn (fst p) bs)) (snd p)) fs.

(** The answer of a stat of [l] into [buf]: [cp_new_stat]'s
    [copy_to_user] (EFAULT), the fields of [stat_fields], every other byte
    the environment's. *)
Definition stat_answer (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (reads : list (word * nat)) (buf : word) (l : Loc) (o : ext_outcome) : Prop :=
  match loc_attr m ctx st l with
  | None => o = EUnmodeled
  | Some a =>
      match put_ok i buf 128 with
      | PutFault => o = err reads EFAULT m ctx st
      | PutPartial => o = EUnmodeled
      | PutOk => exists bs, fields_match 128 (stat_fields st ctx a) bs = true
                            /\ o = ans reads (Z_to_bv 64 0) [(buf, bs)] m ctx st
      end
  end.

(** [fstat] (80): [SYSCALL_DEFINE2(newfstat)], [vfs_fstat] (fs/stat.c) on
    a descriptor of the namespace model, O_PATH included; a file the
    tables give no path declines.  Every other descriptor and number: the
    released answer.  Kind: over (the bytes [stat_fields] does not fix). *)
Definition fstat_arm : NsArm := fun i m ctx st o =>
  match ns_file_of m st (fd_word (in_arg i 0)) with
  | Some (_, f) => match nsfile_loc f with
                   | Some l => stat_answer i m ctx st [] (in_arg i 1) l o
                   | None => o = EUnmodeled
                   end
  | None => released i m ctx st o
  end.

(** [getname_maybe_null] (include/linux/fs.h, fs/namei.c): without
    AT_EMPTY_PATH, [getname]; with it, a NULL pointer or an empty name is
    no name ([NNull]). *)
Inductive MaybeName := NNull | NErr (e : Z) | NName (p : list byte).

Definition name_maybe_null (i : SyscallInput) (pathp : word) (flags : Z)
    : MaybeName * list (word * nat) :=
  if negb (has flags AT_EMPTY_PATH) then
    (match path_arg i pathp with
     | PFault => NErr EFAULT | PTooLong => NErr ENAMETOOLONG
     | POk [] => NErr ENOENT | POk p => NName p
     end, path_reads i pathp)
  else if w_is0 pathp then (NNull, [])
  else (match path_arg i pathp with
        | PFault => NErr EFAULT | PTooLong => NErr ENAMETOOLONG
        | POk [] => NNull | POk p => NName p
        end, path_reads i pathp).

Definition statx_flags_ok (flags : Z) : bool :=
  Z.eqb (Z.land flags (Z.lnot (AT_SYMLINK_NOFOLLOW + AT_NO_AUTOMOUNT + AT_EMPTY_PATH + AT_STATX_SYNC_TYPE))) 0.

(** [newfstatat] (79): [SYSCALL_DEFINE4(newfstatat)], [vfs_fstatat],
    [vfs_statx] (fs/stat.c).  No name and a dirfd of 0 or more: [vfs_fstat]
    of that descriptor (EBADF; a descriptor of another kind declines).
    Otherwise the flags first (EINVAL), then the name's error, then the walk
    (LOOKUP_FOLLOW unless AT_SYMLINK_NOFOLLOW; no name means the dirfd's
    own object). Kind: over (the bytes [stat_fields] does not fix). *)
Definition newfstatat_arm : NsArm := fun i m ctx st o =>
  let dfd := in_arg i 0 in
  let buf := in_arg i 2 in
  let flags := s32 (in_arg i 3) in
  let nm := name_maybe_null i (in_arg i 1) flags in
  let reads := snd nm in
  let fl (p : list byte) := mkWalkFlags (negb (has flags AT_SYMLINK_NOFOLLOW)) false
                                        (match p with [] => true | _ => false end) false false in
  let by_walk (p : list byte) :=
    match walk_from m ctx st (walk_creds m) dfd p (fl p) with
    | (WOk l, _) => stat_answer i m ctx st reads buf l o
    | (WErr e, _) => o = err reads e m ctx st
    | (WOver, _) => o = EUnmodeled
    end in
  match fst nm with
  | NNull =>
      if 0 <=? s32 dfd then
        let w := Z_to_bv 64 (s32 dfd) in
        match fd_lookup (m_fds m) w with
        | None => o = err reads EBADF m ctx st
        | Some _ => match ns_file_of m st w with
                    | Some (_, f) => match nsfile_loc f with
                                     | Some l => stat_answer i m ctx st reads buf l o
                                     | None => o = EUnmodeled
                                     end
                    | None => o = EUnmodeled
                    end
        end
      else if negb (statx_flags_ok (Z.lor flags AT_NO_AUTOMOUNT)) then o = err reads EINVAL m ctx st
      else by_walk []
  | NErr e =>
      if negb (statx_flags_ok (Z.lor flags AT_NO_AUTOMOUNT)) then o = err reads EINVAL m ctx st
      else o = err reads e m ctx st
  | NName p =>
      if negb (statx_flags_ok (Z.lor flags AT_NO_AUTOMOUNT)) then o = err reads EINVAL m ctx st
      else by_walk p
  end.

(* =========================================================================
   faccessat
   ========================================================================= *)

(** [make_kuid (current_user_ns (), 0)]: the kernel id of uid 0 in the
    task's user namespace ([None]: unmapped). *)
Definition root_kuid (st : NsState) (ctx : NsCtx) : option Z :=
  match find_userns (ns_userns st) (cx_user ctx) with
  | None => None
  | Some u => match uns_parent u with
              | None => Some 0
              | Some _ => match uns_uid_map u with Some um => map_down um 0 | None => None end
              end
  end.

(** [access_override_creds] (fs/open.c): with SECURE_NO_SETUID_FIXUP
    clear, the effective set is cleared for a real uid that is not the
    namespace's root and becomes the permitted set for one that is. *)
Definition access_effective (st : NsState) (ctx : NsCtx) (ruid : Z) : Z :=
  if Z.testbit (cx_securebits ctx) 2 then task_eff ctx
  else match root_kuid st ctx with
       | Some r => if Z.eqb r ruid then cap_permitted (cx_caps ctx) else 0
       | None => 0
       end.

(** [faccessat] (48): [do_faccessat] (fs/open.c) with flags 0: EINVAL for a
    mode outside R_OK|W_OK|X_OK; the check runs with the real uid and gid
    and [access_effective]; [getname]; the walk (LOOKUP_FOLLOW); EACCES for
    X_OK on a regular file of a noexec mount or superblock
    ([path_noexec]); [inode_permission]; then, for W_OK on anything but a
    device, FIFO or socket, EROFS on a read-only mount or superblock.
    Kind: exact on objects the tables list. *)
Definition faccessat_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let dfd := in_arg i 0 in
  let pathp := in_arg i 1 in
  let mode := s32 (in_arg i 2) in
  if negb (Z.eqb (Z.land mode (Z.lnot 7)) 0) then ns_errno EINVAL m ctx st
  else
    let reads := path_reads i pathp in
    let ruid := bv_unsigned (cr_uid (m_creds m)) in
    let rgid := bv_unsigned (cr_gid (m_creds m)) in
    let eff := access_effective st ctx ruid in
    let c := cx_caps ctx in
    let ctx' := with_caps ctx (mkCaps eff (cap_permitted c) (cap_inheritable c) (cap_bounding c)
                                      (cap_ambient c)) in
    let cr := mkWalkCreds ruid rgid (wc_groups (walk_creds m)) in
    match path_arg i pathp with
    | PFault => err reads EFAULT m ctx st
    | PTooLong => err reads ENAMETOOLONG m ctx st
    | POk [] => err reads ENOENT m ctx st
    | POk p =>
        match walk_from m ctx' st cr dfd p (mkWalkFlags true false false false false) with
        | (WErr e, _) => err reads e m ctx st
        | (WOver, _) => EUnmodeled
        | (WOk l, _) =>
            match loc_mnt_sb st l, loc_attr m ctx st l with
            | Some (mt, sb), Some a =>
                if has mode MAY_EXEC && kind_is IReg a && (mf_noexec (mnt_flags mt) || sb_i_noexec sb)
                then err reads EACCES m ctx st
                else match inode_permission st ctx' cr eff l sb a mode with
                     | Some e => err reads e m ctx st
                     | None =>
                         if negb (has mode MAY_WRITE) || special a then ans reads (Z_to_bv 64 0) [] m ctx st
                         else if mf_ro (mnt_flags mt) || sb_rdonly sb then err reads EROFS m ctx st
                         else ans reads (Z_to_bv 64 0) [] m ctx st
                     end
            | _, _ => EUnmodeled
            end
        end
    end.

Definition faccessat_arm : NsArm := fun i m ctx st o =>
  o = faccessat_fn i m ctx st
  \/ injected_after file_env_errno (faccessat_fn i m ctx st) m ctx st o.

(* =========================================================================
   statfs, fstatfs
   ========================================================================= *)

(** [calculate_f_flags] (fs/statfs.c) on what the tables hold: ST_VALID,
    the mount's read-only, nosuid, nodev and noexec bits, the superblock's
    read-only bit. *)
Definition held_f_flags (mt : Mount) (sb : SuperBlock) : Z :=
  let f := mnt_flags mt in
  ST_VALID + (if mf_ro f || sb_rdonly sb then ST_RDONLY else 0)
  + (if mf_nosuid f then ST_NOSUID else 0) + (if mf_nodev f then ST_NODEV else 0)
  + (if mf_noexec f then ST_NOEXEC else 0).

(** The answer of a statfs of [l] into [buf] (the 120-byte riscv64 [struct
    statfs], include/uapi/asm-generic/statfs.h; [do_statfs_native],
    fs/statfs.c): [f_type] (offset 0) the superblock's magic, [f_flags]
    (offset 80) [held_f_flags] with any of [ST_UNHELD]; the counts, the
    block sizes, [f_fsid] and [f_namelen] the environment's. *)
Definition statfs_answer (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (reads : list (word * nat)) (buf : word) (l : Loc) (o : ext_outcome) : Prop :=
  match loc_mnt_sb st l with
  | None => o = EUnmodeled
  | Some (mt, sb) =>
      match put_ok i buf 120 with
      | PutFault => o = err reads EFAULT m ctx st
      | PutPartial => o = EUnmodeled
      | PutOk =>
          exists bs, fields_match 120 [(0%nat, Z_to_le_bytes 8 (sb_magic sb))] bs = true
                     /\ Z.eqb (Z.land (bytes_le_to_Z (firstn 8 (skipn 80 bs))) (Z.lnot ST_UNHELD))
                              (held_f_flags mt sb) = true
                     /\ o = ans reads (Z_to_bv 64 0) [(buf, bs)] m ctx st
      end
  end.

(** [statfs] (43): [SYSCALL_DEFINE2(statfs)], [user_statfs], [vfs_statfs]
    (fs/statfs.c): [getname], the walk from the cwd (LOOKUP_FOLLOW), then
    [statfs_answer].  Kind: over (the fields the tables do not hold). *)
Definition statfs_arm : NsArm := fun i m ctx st o =>
  let pathp := in_arg i 0 in
  let reads := path_reads i pathp in
  match path_arg i pathp with
  | PFault => o = err reads EFAULT m ctx st
  | PTooLong => o = err reads ENAMETOOLONG m ctx st
  | POk [] => o = err reads ENOENT m ctx st
  | POk p =>
      match walk_from m ctx st (walk_creds m) AT_FDCWD_word p (mkWalkFlags true false false false false) with
      | (WOk l, _) => statfs_answer i m ctx st reads (in_arg i 1) l o
      | (WErr e, _) => o = err reads e m ctx st
      | (WOver, _) => o = EUnmodeled
      end
  end.

(** [fstatfs] (44): [SYSCALL_DEFINE2(fstatfs)], [fd_statfs] (fs/statfs.c)
    on a descriptor of the namespace model, O_PATH included (EBADF for a
    number that is not open; a file the tables give no path, or a
    descriptor of another kind, declines).  Kind: over, as [statfs]. *)
Definition fstatfs_arm : NsArm := fun i m ctx st o =>
  let w := fd_word (in_arg i 0) in
  match fd_lookup (m_fds m) w with
  | None => o = ns_errno EBADF m ctx st
  | Some _ =>
      match ns_file_of m st w with
      | Some (_, f) => match nsfile_loc f with
                       | Some l => statfs_answer i m ctx st [] (in_arg i 1) l o
                       | None => o = EUnmodeled
                       end
      | None => o = EUnmodeled
      end
  end.

(* =========================================================================
   Path names: readlinkat, getcwd
   ========================================================================= *)

(** [__prepend_path] (fs/d_path.c): from dentry [d] seen through mount [m]
    up to [root], crossing each mount root to its mount point; the error
    code 0 at the root, 1 at the top of the mount tree, 3 at a dentry with
    no parent that is not its mount's root.  [None]: the tables do not
    decide (a missing record, or out of fuel). *)
Fixpoint prepend_fuel (fuel : nat) (st : NsState) (root : Loc) (m d : positive) (acc : list byte)
    : option (Z * list byte) :=
  match fuel with
  | O => None
  | S f =>
      if loc_eqb (LDentry m d) root then Some (0, acc)
      else match find_mount (ns_mounts st) m with
           | None => None
           | Some mt =>
               if Pos.eqb d (mnt_root mt)
               then match mnt_parent mt with
                    | Some p => prepend_fuel f st root p (mnt_mountpoint mt) acc
                    | None => Some (1, acc)
                    end
               else match find_dentry st d with
                    | None => None
                    | Some x => match d_parent x with
                                | None => Some (3, acc)
                                | Some q => prepend_fuel f st root m q (ascii [47] ++ d_name x ++ acc)
                                end
                    end
           end
  end.

(** [prepend_path] (fs/d_path.c): the escaped case starts again empty, and
    an empty name is "/". *)
Definition prepend_path (st : NsState) (root : Loc) (m d : positive) : option (Z * list byte) :=
  match prepend_fuel (S (length (ns_mounts st) + length (ns_dentries st))) st root m d [] with
  | Some (code, acc) =>
      let acc' := if Z.eqb code 3 then [] else acc in
      Some (code, match acc' with [] => ascii [47] | _ => acc' end)
  | None => None
  end.

(** [d_path] (fs/d_path.c) from the task's root, no marker for a path not
    under it; an entry of a task's procfs directory is the procfs root's
    path, the pid and the names below it.  No dentry of the tables is
    unlinked, so " (deleted)" never shows. *)
Definition d_path (st : NsState) (ctx : NsCtx) (l : Loc) : option (list byte) :=
  match l with
  | LDentry m d => option_map snd (prepend_path st (ctx_root_loc ctx) m d)
  | LProcTask m pid rest =>
      match find_mount (ns_mounts st) m with
      | None => None
      | Some mt =>
          match find_sb st (mnt_sb mt) with
          | None => None
          | Some s =>
              match prepend_path st (ctx_root_loc ctx) m (sb_root s) with
              | None => None
              | Some (_, base) =>
                  let base' := if bytes_eqb base (ascii [47]) then [] else base in
                  Some (base' ++ ascii [47] ++ decimal_bytes pid
                        ++ flat_map (fun n => ascii [47] ++ n) rest)
              end
          end
      end
  end.

(** What [vfs_readlink] (fs/namei.c) reads at a location: a link's
    target; for the task's own cwd, root and fd/<k> links,
    [proc_pid_readlink] and [do_proc_readlink] (fs/proc/base.c) on the
    target's path ([proc_cwd_link], [proc_root_link], [proc_fd_link]);
    [NotLink] for an object that is no link; [LinkOver] where the tables
    do not decide (an ns link, whose text holds an nsfs inode number; a
    descriptor with no path; another task's entry, behind a ptrace
    check). *)
Inductive LinkText := LinkBytes (bs : list byte) | LinkPath (l : Loc) | LinkErr (e : Z)
                    | NotLink | LinkOver.

Definition link_text (m : Model) (ctx : NsCtx) (st : NsState) (l : Loc) : LinkText :=
  match l with
  | LDentry _ d =>
      match dentry_inode st d with
      | Some ino => match ino_kind ino with ILnk => LinkBytes (ino_bytes ino) | _ => NotLink end
      | None => LinkOver
      end
  | LProcTask mt pid rest =>
      if negb (proc_own st ctx mt pid) then LinkOver
      else match rest with
           | [n] => if bytes_eqb n proc_cwd_name then LinkPath (ctx_cwd_loc ctx)
                    else if bytes_eqb n proc_root_name then LinkPath (ctx_root_loc ctx)
                    else NotLink
           | [n; k] =>
               if bytes_eqb n proc_fd_name then
                 match name_to_int k with
                 | Some kk => match fd_loc_of m st kk with
                              | Some (Some t) => LinkPath t
                              | Some None => LinkOver
                              | None => LinkErr ENOENT
                              end
                 | None => LinkOver
                 end
               else LinkOver
           | _ => NotLink
           end
  end.

(** [readlinkat] (78): [do_readlinkat] (fs/stat.c): EINVAL for a size of 0
    or less, before the name; [getname_flags] with LOOKUP_EMPTY; the walk
    without LOOKUP_FOLLOW; a link's text, cut to the size, with no NUL
    ([readlink_copy]; a path longer than PATH_MAX - 1 is ENAMETOOLONG); for
    anything else ENOENT on an empty name and EINVAL otherwise.  Kind:
    exact where [link_text] decides. *)
Definition readlinkat_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let dfd := in_arg i 0 in
  let pathp := in_arg i 1 in
  let buf := in_arg i 2 in
  let bufsiz := s32 (in_arg i 3) in
  if bufsiz <=? 0 then ns_errno EINVAL m ctx st
  else
    let reads := path_reads i pathp in
    let copy (bs : list byte) :=
      let n := Z.min (Z.of_nat (length bs)) bufsiz in
      match put_ok i buf n with
      | PutFault => err reads EFAULT m ctx st
      | PutPartial => EUnmodeled
      | PutOk => ans reads (Z_to_bv 64 n) [(buf, firstn (Z.to_nat n) bs)] m ctx st
      end in
    match path_arg i pathp with
    | PFault => err reads EFAULT m ctx st
    | PTooLong => err reads ENAMETOOLONG m ctx st
    | POk p =>
        match walk_from m ctx st (walk_creds m) dfd p (mkWalkFlags false false true false false) with
        | (WErr e, _) => err reads e m ctx st
        | (WOver, _) => EUnmodeled
        | (WOk l, _) =>
            match link_text m ctx st l with
            | LinkBytes bs => copy bs
            | LinkPath t =>
                match d_path st ctx t with
                | Some s => if Nat.ltb (length s) PATH_MAX then copy s else err reads ENAMETOOLONG m ctx st
                | None => EUnmodeled
                end
            | LinkErr e => err reads e m ctx st
            | NotLink => match p with [] => err reads ENOENT m ctx st | _ => err reads EINVAL m ctx st end
            | LinkOver => EUnmodeled
            end
        end
    end.

Definition readlinkat_arm : NsArm := fun i m ctx st o => o = readlinkat_fn i m ctx st.

Definition unreachable_prefix : list byte :=
  ascii [40; 117; 110; 114; 101; 97; 99; 104; 97; 98; 108; 101; 41].

(** [getcwd] (17): [SYSCALL_DEFINE2(getcwd)] (fs/d_path.c): the cwd's path
    from the root by [prepend_path], "(unreachable)" before it when the cwd
    is not under the root, and its NUL; ENAMETOOLONG past PATH_MAX, ERANGE
    when it does not fit, EFAULT; the length with the NUL.  No cwd of the
    tables is unlinked (ENOENT).  Kind: exact. *)
Definition getcwd_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let buf := in_arg i 0 in
  let size := bv_unsigned (in_arg i 1) in
  match prepend_path st (ctx_root_loc ctx) (fst (cx_cwd ctx)) (snd (cx_cwd ctx)) with
  | None => EUnmodeled
  | Some (code, s) =>
      let s' := if 0 <? code then unreachable_prefix ++ s else s in
      let len := Z.of_nat (length s') + 1 in
      if 4096 <? len then ns_errno ENAMETOOLONG m ctx st
      else if size <? len then ns_errno ERANGE m ctx st
      else match put_ok i buf len with
           | PutFault => ns_errno EFAULT m ctx st
           | PutPartial => EUnmodeled
           | PutOk => EOk (mkEffect (Z_to_bv 64 len) [(buf, s' ++ [Z_to_bv 8 0])] []) m ctx st []
           end
  end.

Definition getcwd_arm : NsArm := fun i m ctx st o => o = getcwd_fn i m ctx st.

(* =========================================================================
   chdir, fchdir
   ========================================================================= *)

(** Search permission on a directory the cwd moves to
    ([path_permission] / [file_permission] with MAY_EXEC | MAY_CHDIR), and
    the move ([set_fs_pwd]); a directory with no dentry ([LProcTask])
    declines: the task context holds a cwd as a mount and a dentry. *)
Definition move_cwd (m : Model) (ctx : NsCtx) (st : NsState) (reads : list (word * nat)) (l : Loc)
    : ext_outcome :=
  match l, loc_mnt_sb st l, loc_attr m ctx st l with
  | LDentry lm ld, Some (_, sb), Some a =>
      match inode_permission st ctx (walk_creds m) (task_eff ctx) l sb a MAY_EXEC with
      | Some e => err reads e m ctx st
      | None => ans reads (Z_to_bv 64 0) [] m (with_cwd ctx (lm, ld)) st
      end
  | _, _, _ => EUnmodeled
  end.

(** [chdir] (49): [SYSCALL_DEFINE1(chdir)] (fs/open.c): [getname], the walk
    from the cwd with LOOKUP_FOLLOW | LOOKUP_DIRECTORY, then [move_cwd].
    Kind: exact. *)
Definition chdir_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let pathp := in_arg i 0 in
  let reads := path_reads i pathp in
  match path_arg i pathp with
  | PFault => err reads EFAULT m ctx st
  | PTooLong => err reads ENAMETOOLONG m ctx st
  | POk [] => err reads ENOENT m ctx st
  | POk p =>
      match walk_from m ctx st (walk_creds m) AT_FDCWD_word p (mkWalkFlags true true false false false) with
      | (WOk l, _) => move_cwd m ctx st reads l
      | (WErr e, _) => err reads e m ctx st
      | (WOver, _) => EUnmodeled
      end
  end.

Definition chdir_arm : NsArm := fun i m ctx st o => o = chdir_fn i m ctx st.

(** [fchdir] (50): [SYSCALL_DEFINE1(fchdir)] (fs/open.c): EBADF for a
    number that is not open; ENOTDIR for an object that is no directory
    (an open file of the model with no path is a socket or an eventfd);
    then [move_cwd].  An O_PATH directory works.  A descriptor of another
    kind declines.  Kind: exact. *)
Definition fchdir_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let w := fd_word (in_arg i 0) in
  match fd_lookup (m_fds m) w with
  | None => ns_errno EBADF m ctx st
  | Some _ =>
      match ns_file_of m st w with
      | None => EUnmodeled
      | Some (_, f) =>
          match nsfile_loc f with
          | None => ns_errno ENOTDIR m ctx st
          | Some l => match loc_dir st l with
                      | Some true => move_cwd m ctx st [] l
                      | Some false => ns_errno ENOTDIR m ctx st
                      | None => EUnmodeled
                      end
          end
      end
  end.

Definition fchdir_arm : NsArm := fun i m ctx st o => o = fchdir_fn i m ctx st.

(* =========================================================================
   getdents64 on /proc/<pid>/fd
   ========================================================================= *)

Fixpoint insert_z (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | y :: r => if x <? y then x :: l else if Z.eqb x y then l else y :: insert_z x r
  end.

(** The task's open descriptors, in increasing order. *)
Definition fd_numbers (m : Model) : list Z :=
  fold_right insert_z [] (map (fun p => bv_unsigned (fst p)) (m_fds m)).

(** The entries of the task's fd directory from position [pos]
    ([proc_readfd_common], fs/proc/fd.c, and [dir_emit_dots],
    include/linux/fs.h): "." at 0 and ".." at 1 (DT_DIR), then each open
    descriptor N at N + 2, named by its decimal number (DT_LNK). *)
Definition fd_dir_entries (m : Model) (pos : Z) : list (Z * list byte * Z) :=
  (if pos <=? 0 then [(0, ascii [46], 4)] else [])
  ++ (if pos <=? 1 then [(1, ascii [46; 46], 4)] else [])
  ++ map (fun n => (n + 2, decimal_bytes n, 10)) (List.filter (fun n => pos - 2 <=? n) (fd_numbers m)).

(** [filldir64] (fs/readdir.c): a record of [ALIGN(19 + namelen + 1, 8)]
    bytes. *)
Definition reclen (namelen : nat) : Z := ((19 + Z.of_nat namelen + 1 + 7) / 8) * 8.

(** The records that fit in [room] bytes, at offsets from [off]: the
    writes ([d_ino], [d_off], [d_reclen], [d_type], the name and its NUL;
    the padding after it is not written), the bytes used, and the position
    of the first entry that did not fit.  [choice k] is the [d_ino] and
    [d_off] of record [k], the environment's. *)
Fixpoint emit (buf : word) (es : list (Z * list byte * Z)) (room off : Z) (k : nat)
    (choice : nat -> Z * Z) : list (word * list byte) * Z * option Z :=
  match es with
  | [] => ([], off, None)
  | (p, name, ty) :: rest =>
      let rl := reclen (length name) in
      if room <? rl then ([], off, Some p)
      else
        let rec := Z_to_le_bytes 8 (fst (choice k)) ++ Z_to_le_bytes 8 (snd (choice k))
                   ++ Z_to_le_bytes 2 rl ++ [Z_to_bv 8 ty] ++ name ++ [Z_to_bv 8 0] in
        let '(ws, used, stop) := emit buf rest (room - rl) (off + rl) (S k) choice in
        (((buf + Z_to_bv 64 off)%bv, rec) :: ws, used, stop)
  end.

(** The fd directory [l] is the task's own. *)
Definition own_fd_dir (st : NsState) (ctx : NsCtx) (l : Loc) : bool :=
  match l with
  | LProcTask mt pid [n] => bytes_eqb n proc_fd_name && proc_own st ctx mt pid
  | _ => false
  end.

(** [getdents64] (61): [SYSCALL_DEFINE3(getdents64)], [iterate_dir],
    [filldir64] (fs/readdir.c) on the task's own fd directory: the entries
    of [fd_dir_entries] that fit in the count, the bytes written, EINVAL
    when the first does not fit, 0 at the end; the file's position moves to
    the first entry not written, or past the last descriptor
    ([fget_task_next] runs to the size of the table, which the tables do not
    hold: [endpos]).  EBADF for a number that is not open or an O_PATH file
    ([fdget_pos]); ENOTDIR for a file with no [iterate_shared] (a regular or
    procfs file, a socket, an eventfd, a signalfd); another directory, or
    another task's fd directory, declines; a descriptor of another kind:
    the released answer.  Kind: over ([d_ino], [d_off], and the end
    position are the environment's). *)
Definition getdents64_out (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) (h : N)
    (f : NsFile) (l : Loc) (pos : Z) (choice : nat -> Z * Z) (endpos : Z) : ext_outcome :=
  let buf := in_arg i 1 in
  let count := s32 (in_arg i 2) in
  let es := fd_dir_entries m pos in
  let '(ws, used, stop) := emit buf es count 0 0%nat choice in
  let newpos := match stop with Some p => p | None => endpos end in
  let st' := set_file st h (mkNsFile (NfDir l newpos) (nf_flags f) (nf_cred f)) in
  match es with
  | [] => EOk (mkEffect (Z_to_bv 64 0) [] []) m ctx st' []
  | (p0, name0, _) :: _ =>
      if Z.eqb used 0 then EOk (mkEffect (errno_ret EINVAL) [] []) m ctx st' []
      else match put_ok i buf used with
           | PutOk => EOk (mkEffect (Z_to_bv 64 used) ws []) m ctx st' []
           | PutFault =>
               if negb (access_okb buf (reclen (length name0)))
               then EOk (mkEffect (errno_ret EFAULT) [] []) m ctx
                         (set_file st h (mkNsFile (NfDir l p0) (nf_flags f) (nf_cred f))) []
               else EUnmodeled
           | PutPartial =>
               EOk (mkEffect (errno_ret EFAULT) [] []) m ctx
                 (set_file st h (mkNsFile (NfDir l p0) (nf_flags f) (nf_cred f))) []
           end
  end.

Definition endpos_ok (m : Model) (pos e : Z) : bool :=
  (pos <=? e) && forallb (fun n => n + 3 <=? e) (fd_numbers m).

Definition getdents64_arm : NsArm := fun i m ctx st o =>
  let w := fd_word (in_arg i 0) in
  match fd_lookup (m_fds m) w with
  | None => o = ns_errno EBADF m ctx st
  | Some _ =>
      match ns_file_of m st w with
      | None => released i m ctx st o
      | Some (h, f) =>
          match nf_kind f with
          | NfPath _ => o = ns_errno EBADF m ctx st
          | NfDir l pos =>
              if own_fd_dir st ctx l
              then exists choice endpos, endpos_ok m pos endpos = true
                                         /\ o = getdents64_out i m ctx st h f l pos choice endpos
              else o = EUnmodeled
          | _ => o = ns_errno ENOTDIR m ctx st
          end
      end
  end.

(* =========================================================================
   The arms
   ========================================================================= *)

(** The environment refusals of the path and descriptor arms.  ENOMEM and
    ENFILE are allocation failures, EIO is filesystem I/O, and the final
    predicate is a security module's errno. *)
Definition file_injected : list NsInjected :=
  map (fun n => mkNsInjected n
    [(fun e => (e =? ENOMEM) || (e =? ENFILE), FamAlloc);
     (fun e => e =? EIO, FamFs);
     (fun e => (1 <=? e) && (e <=? 4095), FamCred)])
    [17; 25; 43; 44; 48; 49; 50; 56; 57; 61; 78; 79; 80; 437].

(** The arms of this file by call number, for [Ns.Spec.ns_table].  Every
    listed arm has the environment alternative after one successful
    deterministic witness, so its ledger cannot list an unreachable
    refusal. *)
Definition file_arms : list (Z * NsArm) :=
  [(17, with_injected file_env_errno getcwd_arm); (25, with_injected file_env_errno fcntl_arm);
   (43, with_injected file_env_errno statfs_arm); (44, with_injected file_env_errno fstatfs_arm);
   (48, with_injected file_env_errno faccessat_arm); (49, with_injected file_env_errno chdir_arm);
   (50, with_injected file_env_errno fchdir_arm); (56, with_injected file_env_errno openat_arm);
   (57, with_injected file_env_errno close_arm); (61, with_injected file_env_errno getdents64_arm);
   (78, with_injected file_env_errno readlinkat_arm); (79, with_injected file_env_errno newfstatat_arm);
   (80, with_injected file_env_errno fstat_arm); (437, with_injected file_env_errno openat2_arm)].
