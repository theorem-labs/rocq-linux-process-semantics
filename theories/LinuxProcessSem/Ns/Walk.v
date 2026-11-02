(** * LinuxProcessSem.Ns.Walk — path resolution in a namespace and mount tree

    A pure path walk over the data of [Ns.Tables], in the order of the
    Linux 6.18.44 lookup code.  It resolves listed dentries, crosses mounts
    in both directions, follows symbolic links, synthesizes the procfs
    entries of the calling task, and checks search permission before each
    component.  Where the answer depends on state the tables do not hold
    (another task's procfs directory, an nsfs object, a sysctl), the walk
    answers [WOver] and never an errno.

    Linux 6.18.44 sources:
    - the empty path and the PATH_MAX limit: [getname_flags], fs/namei.c;
    - the start and the root of a walk: [path_init], fs/namei.c;
    - one component after another: [link_path_walk], [walk_component],
      [lookup_fast], [lookup_slow], [lookup_last], [path_lookupat],
      [path_parentat], fs/namei.c;
    - entering a dentry, crossing mounts, following links: [step_into],
      [handle_mounts], [traverse_mounts], [pick_link], [reserve_stack],
      [may_follow_link], [nd_jump_root], [nd_jump_link], fs/namei.c;
    - "..": [handle_dots], [follow_dotdot], [choose_mountpoint],
      fs/namei.c;
    - search permission: [may_lookup], [generic_permission],
      [acl_permission_check], fs/namei.c; [capable_wrt_inode_uidgid],
      [privileged_wrt_inode_uidgid], kernel/capability.c; [map_id_up],
      kernel/user_namespace.c;
    - a name longer than NAME_MAX: [simple_lookup], fs/libfs.c, and the
      lookup of each disk file system;
    - procfs: [proc_root_lookup], fs/proc/root.c; [proc_pid_lookup],
      [proc_cwd_link], [proc_root_link], fs/proc/base.c;
      [proc_self_get_link], fs/proc/self.c; [proc_lookupfd_common],
      [proc_fd_link], [proc_fd_permission], fs/proc/fd.c; [name_to_int],
      fs/proc/util.c; [proc_ns_get_link], fs/proc/namespaces.c. *)

From Stdlib Require Import List PArith ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount Userns.
Import ListNotations.
Open Scope Z_scope.

(** The credentials [generic_permission] (fs/namei.c) reads: fsuid, fsgid
    and the supplementary groups, as kernel ids. *)
Record WalkCreds := mkWalkCreds {
  wc_fsuid  : Z;
  wc_fsgid  : Z;
  wc_groups : list Z
}.

(** The lookup flags of fs/namei.c (include/linux/namei.h) the walk reads:
    LOOKUP_FOLLOW, LOOKUP_DIRECTORY, LOOKUP_EMPTY, LOOKUP_NO_MAGICLINKS and
    LOOKUP_IN_ROOT. *)
Record WalkFlags := mkWalkFlags {
  wf_follow        : bool;
  wf_directory     : bool;
  wf_empty         : bool;
  wf_no_magiclinks : bool;
  wf_in_root       : bool
}.

(** What [path_lookupat] (fs/namei.c) ends with: a location, an errno, or
    [WOver] where the tables do not decide. *)
Inductive WalkResult :=
  | WOk (l : Loc)
  | WErr (e : Z)
  | WOver.

(** [nd->last_type] after [link_path_walk] (fs/namei.c). *)
Inductive LastType := LastNorm | LastDot | LastDotDot | LastRoot.

(** NAME_MAX and PATH_MAX (include/uapi/linux/limits.h), and MAXSYMLINKS
    (include/linux/namei.h), the bound [reserve_stack] (fs/namei.c) puts on
    the links of one walk. *)
Definition NAME_MAX : nat := 255.
Definition PATH_MAX : nat := 4096.
Definition MAXSYMLINKS : nat := 40.

(* =========================================================================
   Table lookups
   ========================================================================= *)

(** The task's root and cwd ([fs->root], [fs->pwd]) as locations, as
    [path_init] and [nd_jump_root] (fs/namei.c) read them. *)
Definition ctx_root_loc (ctx : NsCtx) : Loc :=
  LDentry (fst (cx_root ctx)) (snd (cx_root ctx)).

Definition ctx_cwd_loc (ctx : NsCtx) : Loc :=
  LDentry (fst (cx_cwd ctx)) (snd (cx_cwd ctx)).

(** A dentry, an inode and a superblock by id. *)
Definition find_dentry (st : NsState) (i : positive) : option Dentry :=
  find (fun d => Pos.eqb (d_id d) i) (ns_dentries st).

Definition find_inode (st : NsState) (i : positive) : option Inode :=
  find (fun n => Pos.eqb (ino_id n) i) (ns_inodes st).

Definition find_sb (st : NsState) (i : positive) : option SuperBlock :=
  find (fun s => Pos.eqb (sb_id s) i) (ns_sbs st).

(** [d_inode] of a listed dentry. *)
Definition dentry_inode (st : NsState) (d : positive) : option Inode :=
  match find_dentry st d with
  | Some x => find_inode st (d_inode x)
  | None => None
  end.

(** The inode at a location; [None] for an entry of a task's procfs
    directory, whose inodes the tables do not list. *)
Definition loc_inode (st : NsState) (l : Loc) : option Inode :=
  match l with
  | LDentry _ d => dentry_inode st d
  | LProcTask _ _ _ => None
  end.

Definition byte_eqb (a b : byte) : bool := bv_eqb a b.

Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => byte_eqb x y && bytes_eqb xs ys
  | _, _ => false
  end.

(** [d] is a linked child of directory dentry [p]: an unlinked dentry keeps
    its parent but is no longer in the directory ([d_unlinked]). *)
Definition has_parent (p : positive) (d : Dentry) : bool :=
  match d_parent d with
  | Some q => Pos.eqb q p && negb (d_unlinked d)
  | None => false
  end.

(** [lookup_fast] / [lookup_slow] (fs/namei.c) on listed dentries: the child
    of directory dentry [parent] named [name]; the first in table order if
    the table lists several. *)
Definition child_dentry (st : NsState) (parent : positive) (name : list byte)
    : option Dentry :=
  find (fun d => has_parent parent d && bytes_eqb (d_name d) name) (ns_dentries st).

(** [lookup_mnt] in [traverse_mounts] (fs/namei.c): the mount whose parent is
    mount [parent] and whose mount point is dentry [point].  If the table
    holds several, the first in table order is the one seen. *)
Definition mount_on (st : NsState) (parent point : positive) : option Mount :=
  find (fun m =>
          match mnt_parent m with
          | Some p => Pos.eqb p parent && Pos.eqb (mnt_mountpoint m) point
          | None => false
          end) (ns_mounts st).

(** [topmost_overmount] (fs/namespace.c): from mount [m], the mount on its
    root dentry, and so on up. *)
Fixpoint topmost_fuel (fuel : nat) (st : NsState) (m : Mount) : Mount :=
  match fuel with
  | O => m
  | S f => match mount_on st (mnt_id m) (mnt_root m) with
           | Some m' => topmost_fuel f st m'
           | None => m
           end
  end.

(** The topmost mount on a mount namespace's root mount [r]: where a task of
    that namespace that is not chrooted has its root.  On Linux the
    namespace's root mount is rootfs and "/" is mounted on it, so this is
    "/"'s mount, not rootfs. *)
Definition ns_top (st : NsState) (r : Mount) : Mount :=
  topmost_fuel (length (ns_mounts st)) st r.

(* =========================================================================
   Path text
   ========================================================================= *)

Definition ascii (zs : list Z) : list byte := map (Z_to_bv 8) zs.

Definition is_slash (b : byte) : bool := byte_eqb b (Z_to_bv 8 47).
Definition is_dot_name (s : list byte) : bool := bytes_eqb s (ascii [46]).
Definition is_dotdot_name (s : list byte) : bool := bytes_eqb s (ascii [46; 46]).

(** The components of a path as [link_path_walk] (fs/namei.c) takes them:
    runs of '/' separate them and no component is empty. *)
Fixpoint split_path_aux (p current : list byte) (acc : list (list byte))
    : list (list byte) :=
  match p with
  | [] => match current with [] => rev acc | _ => rev (rev current :: acc) end
  | b :: rest =>
      if is_slash b
      then match current with
           | [] => split_path_aux rest [] acc
           | _ => split_path_aux rest [] (rev current :: acc)
           end
      else split_path_aux rest (b :: current) acc
  end.

Definition split_path (p : list byte) : list (list byte) := split_path_aux p [] [].

(** [path_init] and [pick_link] (fs/namei.c): a leading '/' starts at the
    root. *)
Definition path_absolute (p : list byte) : bool :=
  match p with b :: _ => is_slash b | [] => false end.

(** [lookup_last] (fs/namei.c): a '/' after the last name adds LOOKUP_FOLLOW
    and LOOKUP_DIRECTORY. *)
Definition path_trailing_slash (p : list byte) : bool :=
  match rev p with b :: _ => is_slash b | [] => false end.

(** The decimal text of a pid, as [proc_self_get_link] (fs/proc/self.c)
    prints it with "%u". *)
Fixpoint decimal_rev_fuel (fuel n : nat) : list byte :=
  match fuel with
  | O => []
  | S f =>
      if Nat.eqb n 0 then []
      else Z_to_bv 8 (Z.of_nat (n mod 10) + 48) :: decimal_rev_fuel f (n / 10)
  end.

Definition decimal_bytes (z : Z) : list byte :=
  if z <? 0 then []
  else if z =? 0 then ascii [48]
  else rev (decimal_rev_fuel (S (Z.to_nat z)) (Z.to_nat z)).

(** [name_to_int] (fs/proc/util.c): a decimal number with no leading zero
    and below (~0U - 9) / 10 before its last digit; anything else is not a
    number. *)
Fixpoint name_to_int_aux (acc : Z) (s : list byte) : option Z :=
  match s with
  | [] => Some acc
  | b :: rest =>
      let c := bv_unsigned b - 48 in
      if (c <? 0) || (9 <? c) then None
      else if 429496728 <=? acc then None
      else name_to_int_aux (10 * acc + c) rest
  end.

Definition name_to_int (s : list byte) : option Z :=
  match s with
  | [] => None
  | b :: rest =>
      match rest with
      | _ :: _ => if Z.eqb (bv_unsigned b) 48 then None else name_to_int_aux 0 s
      | [] => name_to_int_aux 0 s
      end
  end.

Fixpoint name_lists_eqb (a b : list (list byte)) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => bytes_eqb x y && name_lists_eqb xs ys
  | _, _ => false
  end.

(** [path_equal] (include/linux/path.h) on locations. *)
Definition loc_eqb (a b : Loc) : bool :=
  match a, b with
  | LDentry am ad, LDentry bm bd => Pos.eqb am bm && Pos.eqb ad bd
  | LProcTask am ap ar, LProcTask bm bp br =>
      Pos.eqb am bm && Z.eqb ap bp && name_lists_eqb ar br
  | _, _ => false
  end.

(* =========================================================================
   procfs names
   ========================================================================= *)

Definition proc_self_name : list byte := ascii [115; 101; 108; 102].
Definition proc_thread_self_name : list byte :=
  ascii [116; 104; 114; 101; 97; 100; 45; 115; 101; 108; 102].
Definition proc_fd_name : list byte := ascii [102; 100].
Definition proc_ns_name : list byte := ascii [110; 115].
Definition proc_cwd_name : list byte := ascii [99; 119; 100].
Definition proc_root_name : list byte := ascii [114; 111; 111; 116].
Definition proc_uid_map_name : list byte := ascii [117; 105; 100; 95; 109; 97; 112].
Definition proc_gid_map_name : list byte := ascii [103; 105; 100; 95; 109; 97; 112].
Definition proc_setgroups_name : list byte :=
  ascii [115; 101; 116; 103; 114; 111; 117; 112; 115].
Definition proc_mountinfo_name : list byte :=
  ascii [109; 111; 117; 110; 116; 105; 110; 102; 111].

(** The entries of /proc/<pid>/ns: [ns_entries] (fs/proc/namespaces.c). *)
Definition proc_ns_entries : list (list byte) :=
  [ascii [99; 103; 114; 111; 117; 112];                                  (* cgroup *)
   ascii [105; 112; 99];                                                 (* ipc *)
   ascii [109; 110; 116];                                                (* mnt *)
   ascii [110; 101; 116];                                                (* net *)
   ascii [112; 105; 100];                                                (* pid *)
   ascii [112; 105; 100; 95; 102; 111; 114; 95; 99; 104; 105; 108; 100; 114; 101; 110];
   ascii [116; 105; 109; 101];                                           (* time *)
   ascii [116; 105; 109; 101; 95; 102; 111; 114; 95; 99; 104; 105; 108; 100; 114; 101; 110];
   ascii [117; 115; 101; 114];                                           (* user *)
   ascii [117; 116; 115]].                                               (* uts *)

(** The directories among the modeled entries of the task's own procfs
    directory: the directory itself, fd and ns. *)
Definition proc_dir_rest (rest : list (list byte)) : bool :=
  match rest with
  | [] => true
  | [n] => bytes_eqb n proc_fd_name || bytes_eqb n proc_ns_name
  | _ => false
  end.

(* =========================================================================
   Search permission
   ========================================================================= *)

(** Whether a location is a directory ([d_can_lookup]); [None] when the
    tables do not list its dentry or inode. *)
Definition loc_dir (st : NsState) (l : Loc) : option bool :=
  match l with
  | LDentry _ d =>
      match dentry_inode st d with
      | Some ino => Some (match ino_kind ino with IDir => true | _ => false end)
      | None => None
      end
  | LProcTask _ _ rest => Some (proc_dir_rest rest)
  end.

(** [acl_permission_check] (fs/namei.c) for MAY_EXEC: the owner bits for the
    owner, else the group bits for a member of the group (fsgid or a
    supplementary group), else the other bits.  The model has no ACLs. *)
Definition inode_exec_bit (cr : WalkCreds) (ino : Inode) : bool :=
  if Z.eqb (wc_fsuid cr) (ino_uid ino) then Z.testbit (ino_perm ino) 6
  else if Z.eqb (wc_fsgid cr) (ino_gid ino)
          || existsb (fun g => Z.eqb g (ino_gid ino)) (wc_groups cr)
       then Z.testbit (ino_perm ino) 3
       else Z.testbit (ino_perm ino) 0.

(** [kuid_has_mapping] (include/linux/uidgid.h) through [map_id_up]
    (kernel/user_namespace.c): a kernel id has a mapping when an extent's
    lower range holds it. *)
Definition kid_mapped (exts : list IdExtent) (x : Z) : bool :=
  existsb (fun e => (ext_lower e <=? x) && (x <? ext_lower e + ext_count e)) exts.

(** [privileged_wrt_inode_uidgid] (kernel/capability.c): the inode's kuid
    and kgid are both mapped in the task's user namespace.  An unwritten map
    maps nothing; the initial namespace maps every id. *)
Definition inode_ids_mapped (st : NsState) (ctx : NsCtx) (ino : Inode) : bool :=
  match find_userns (ns_userns st) (cx_user ctx) with
  | None => false
  | Some u =>
      match uns_parent u with
      | None => true
      | Some _ =>
          match uns_uid_map u, uns_gid_map u with
          | Some um, Some gm => kid_mapped um (ino_uid ino) && kid_mapped gm (ino_gid ino)
          | _, _ => false
          end
      end
  end.

(** [generic_permission] (fs/namei.c) on a directory after the mode bits
    refuse: [capable_wrt_inode_uidgid] with CAP_DAC_READ_SEARCH (2), then
    with CAP_DAC_OVERRIDE (1), in the task's effective set. *)
Definition has_dir_search_cap (ctx : NsCtx) : bool :=
  Z.testbit (cap_effective (cx_caps ctx)) 2 || Z.testbit (cap_effective (cx_caps ctx)) 1.

(** [may_lookup] (fs/namei.c): MAY_EXEC on the directory through
    [inode_permission] and [generic_permission].  The task's own procfs
    directory (mode 0555), its ns directory (0511) and its fd directory
    ([proc_fd_permission], fs/proc/fd.c, grants the task's own thread group)
    are searchable by the task. *)
Definition may_exec_dir (st : NsState) (ctx : NsCtx) (cr : WalkCreds) (l : Loc) : bool :=
  match loc_inode st l with
  | Some ino =>
      match ino_kind ino with
      | IDir => inode_exec_bit cr ino || (has_dir_search_cap ctx && inode_ids_mapped st ctx ino)
      | _ => false
      end
  | None => match l with LProcTask _ _ rest => proc_dir_rest rest | LDentry _ _ => false end
  end.

(* =========================================================================
   Mounts and ".."
   ========================================================================= *)

(** [traverse_mounts] (fs/namei.c): while a mount covers the dentry, go to
    that mount's root.  The fuel bounds the chain by the table; a cycle in a
    malformed table answers [WOver]. *)
Fixpoint follow_mounts_fuel (fuel : nat) (st : NsState) (l : Loc) : WalkResult :=
  match fuel with
  | O => WOver
  | S f =>
      match l with
      | LDentry m d =>
          match mount_on st m d with
          | Some child => follow_mounts_fuel f st (LDentry (mnt_id child) (mnt_root child))
          | None => WOk l
          end
      | LProcTask _ _ _ => WOk l
      end
  end.

Definition follow_mounts (st : NsState) (l : Loc) : WalkResult :=
  follow_mounts_fuel (S (length (ns_mounts st))) st l.

(** [choose_mountpoint_rcu] (fs/namei.c): from mount [m], climb to the
    parent mounts until a mount point that is not the root of its mount.
    [Some (Some (mnt, dentry))]: found; [Some None]: none, either because
    the mount has no parent or because the next mount point is the walk
    root; [None]: the tables do not decide. *)
Fixpoint choose_mountpoint_fuel (fuel : nat) (st : NsState) (root : Loc) (m : positive)
    : option (option (positive * positive)) :=
  match fuel with
  | O => None
  | S f =>
      match find_mount (ns_mounts st) m with
      | None => None
      | Some mt =>
          match mnt_parent mt with
          | None => Some None
          | Some p =>
              if loc_eqb root (LDentry p (mnt_mountpoint mt)) then Some None
              else match find_mount (ns_mounts st) p with
                   | None => None
                   | Some pm =>
                       if Pos.eqb (mnt_mountpoint mt) (mnt_root pm)
                       then choose_mountpoint_fuel f st root p
                       else Some (Some (p, mnt_mountpoint mt))
                   end
          end
      end
  end.

(** [dget_parent] in [follow_dotdot], then [step_into] (fs/namei.c): the
    parent dentry, or the dentry itself at the root of its superblock, with
    the mounts on it followed. *)
Definition dentry_parent (st : NsState) (m d : positive) : WalkResult :=
  match find_dentry st d with
  | None => WOver
  | Some x =>
      match d_parent x with
      | Some parent => follow_mounts st (LDentry m parent)
      | None => follow_mounts st (LDentry m d)
      end
  end.

(** ".." inside the task's procfs directory: one name up, and from the task
    directory itself to the procfs root dentry of the same mount. *)
Definition proc_dotdot (st : NsState) (m : positive) (pid : Z) (rest : list (list byte))
    : WalkResult :=
  match rev rest with
  | [] =>
      match find_mount (ns_mounts st) m with
      | Some mt =>
          match find_sb st (mnt_sb mt) with
          | Some s => follow_mounts st (LDentry m (sb_root s))
          | None => WOver
          end
      | None => WOver
      end
  | _ :: prefix => WOk (LProcTask m pid (rev prefix))
  end.

(** [follow_dotdot] and [handle_dots] (fs/namei.c): at the walk root stay;
    at the root dentry of a mount go to its mount point
    ([choose_mountpoint]; none found: stay); then to the parent dentry; and
    [step_into] follows the mounts on the result. *)
Definition follow_dotdot (st : NsState) (root current : Loc) : WalkResult :=
  if loc_eqb current root then follow_mounts st current
  else match current with
       | LProcTask m pid rest => proc_dotdot st m pid rest
       | LDentry m d =>
           match find_mount (ns_mounts st) m with
           | None => WOver
           | Some mt =>
               if Pos.eqb d (mnt_root mt)
               then match choose_mountpoint_fuel (S (length (ns_mounts st))) st root m with
                    | None => WOver
                    | Some None => follow_mounts st current
                    | Some (Some (p, mp)) => dentry_parent st p mp
                    end
               else dentry_parent st m d
           end
       end.

(* =========================================================================
   One lookup
   ========================================================================= *)

(** What a name in a directory is:
    - [LIDentry l]: an object at [l];
    - [LIProcSelf own]: procfs's "self", a symbolic link to the caller's pid
      in the procfs pid namespace ([None]: the caller has none there);
    - [LIMagicLink l target]: a procfs magic link at [l] to [target]
      ([None]: a target the tables hold no path for);
    - an errno, or [LIOver] where the tables do not decide. *)
Inductive LookupItem :=
  | LIDentry (l : Loc)
  | LIProcSelf (own : option Z)
  | LIMagicLink (l : Loc) (target : option Loc)
  | LIError (e : Z)
  | LIOver.

(** [proc_root_lookup] (fs/proc/root.c) for a name no listed dentry has:
    "self" ([proc_self_get_link], fs/proc/self.c); "thread-self", whose
    thread ids the tables do not hold; the caller's own pid
    ([proc_pid_lookup], fs/proc/base.c); another number, a task the tables
    do not hold; else ENOENT. *)
Definition lookup_proc_root (ctx : NsCtx) (m pidns : positive) (name : list byte)
    : LookupItem :=
  if bytes_eqb name proc_self_name then LIProcSelf (pid_in (cx_pids ctx) pidns)
  else if bytes_eqb name proc_thread_self_name then LIOver
  else match name_to_int name with
       | Some n =>
           match pid_in (cx_pids ctx) pidns with
           | Some own => if Z.eqb n own then LIDentry (LProcTask m n []) else LIOver
           | None => LIOver
           end
       | None => LIError ENOENT
       end.

(** A name in the task's own procfs directory or below it: fd, ns and the
    listed files ([tgid_base_stuff], fs/proc/base.c); cwd and root, magic
    links to the task's cwd and root ([proc_cwd_link], [proc_root_link]);
    fd/<k> ([proc_lookupfd_common], [proc_fd_link], fs/proc/fd.c: ENOENT
    for no such descriptor, the descriptor's path for one the model knows a
    path of); ns/<name> ([proc_ns_get_link], fs/proc/namespaces.c), whose
    target is an nsfs object.  Every other name: [LIOver]. *)
Definition lookup_proc_task (ctx : NsCtx) (fd_loc : Z -> option (option Loc))
    (m : positive) (pid : Z) (rest : list (list byte)) (name : list byte) : LookupItem :=
  match rest with
  | [] =>
      if bytes_eqb name proc_fd_name then LIDentry (LProcTask m pid [proc_fd_name])
      else if bytes_eqb name proc_ns_name then LIDentry (LProcTask m pid [proc_ns_name])
      else if bytes_eqb name proc_cwd_name
      then LIMagicLink (LProcTask m pid [proc_cwd_name]) (Some (ctx_cwd_loc ctx))
      else if bytes_eqb name proc_root_name
      then LIMagicLink (LProcTask m pid [proc_root_name]) (Some (ctx_root_loc ctx))
      else if bytes_eqb name proc_uid_map_name || bytes_eqb name proc_gid_map_name
              || bytes_eqb name proc_setgroups_name || bytes_eqb name proc_mountinfo_name
      then LIDentry (LProcTask m pid [name])
      else LIOver
  | [entry] =>
      if bytes_eqb entry proc_fd_name
      then match name_to_int name with
           | Some k =>
               match fd_loc k with
               | Some target => LIMagicLink (LProcTask m pid [proc_fd_name; name]) target
               | None => LIError ENOENT
               end
           | None => LIError ENOENT
           end
      else if bytes_eqb entry proc_ns_name
      then if existsb (bytes_eqb name) proc_ns_entries
           then LIMagicLink (LProcTask m pid [proc_ns_name; name]) None
           else LIOver
      else LIOver
  | _ => LIOver
  end.

(** The pid namespace of the procfs superblock whose root dentry is [d]:
    [Some (Some ns)]; [Some None] when [d] is not a procfs root; [None] when
    the tables do not list [d] or its superblock. *)
Definition proc_root_pidns (st : NsState) (d : positive) : option (option positive) :=
  match find_dentry st d with
  | None => None
  | Some x =>
      match d_parent x with
      | Some _ => Some None
      | None =>
          match find_sb st (d_sb x) with
          | None => None
          | Some s => Some (match sb_kind s with SbProc ns => Some ns | _ => None end)
          end
      end
  end.

(** [walk_component] (fs/namei.c) on listed dentries.  Missing tmpfs and
    devpts names have the simple-lookup NAME_MAX limit, a host lookup is
    outside this table, and procfs subdirectories enumerate ENOENT. *)
Definition lookup_child (st : NsState) (ctx : NsCtx) (fd_loc : Z -> option (option Loc))
    (current : Loc) (name : list byte) : LookupItem :=
  match current with
  | LProcTask m pid rest => lookup_proc_task ctx fd_loc m pid rest name
  | LDentry m d =>
      match child_dentry st d name with
      | Some child => LIDentry (LDentry m (d_id child))
      | None =>
          match proc_root_pidns st d with
          | None => LIOver
          | Some (Some pidns) => lookup_proc_root ctx m pidns name
          | Some None =>
              match find_dentry st d with
              | Some dx =>
                  match find_sb st (d_sb dx) with
                  | Some sb =>
                      match sb_kind sb with
                      | SbTmpfs | SbDevpts =>
                          if Nat.ltb NAME_MAX (length name) then LIError ENAMETOOLONG else LIError ENOENT
                      | SbProc _ => LIError ENOENT
                      | SbHost => LIOver
                      end
                  | None => LIOver
                  end
              | None => LIOver
              end
          end
      end
  end.

(** [step_into] (fs/namei.c): [handle_mounts] before anything else. *)
Definition step_into (st : NsState) (l : Loc) : WalkResult :=
  match l with LDentry _ _ => follow_mounts st l | LProcTask _ _ _ => WOk l end.

(** [step_into] (fs/namei.c): a link is followed unless it is the last
    component and neither LOOKUP_FOLLOW nor a trailing '/' asks for it. *)
Definition follow_link_now (rest : list (list byte)) (trailing : bool) (fl : WalkFlags) : bool :=
  match rest with [] => wf_follow fl || trailing | _ :: _ => true end.

(** The last component: [link_path_walk] (fs/namei.c) reaches its end. *)
Definition is_last (rest : list (list byte)) : bool :=
  match rest with [] => true | _ :: _ => false end.

(** [may_follow_link] (fs/namei.c) for the last component: with
    fs.protected_symlinks set, a link in a sticky world-writable directory
    whose owner is neither the follower nor the directory's owner is
    refused.  The sysctl is not in the tables, so a link in that position
    is undecided. *)
Definition protected_link_undecided (st : NsState) (cr : WalkCreds) (dir : Loc) (link : Inode)
    : bool :=
  negb (Z.eqb (ino_uid link) (wc_fsuid cr))
  && (match loc_inode st dir with
      | Some di => Z.testbit (ino_perm di) 9 && Z.testbit (ino_perm di) 1
                   && negb (Z.eqb (ino_uid di) (ino_uid link))
      | None => false
      end).

(** [path_init] (fs/namei.c): the root of the walk is the task's root, or
    the start under LOOKUP_IN_ROOT; an absolute path starts at that root
    except under LOOKUP_IN_ROOT, which starts every path at the start. *)
Definition walk_root (ctx : NsCtx) (start : Loc) (fl : WalkFlags) : Loc :=
  if wf_in_root fl then start else ctx_root_loc ctx.

Definition walk_initial (start root : Loc) (p : list byte) (fl : WalkFlags) : Loc :=
  if path_absolute p && negb (wf_in_root fl) then root else start.

(* =========================================================================
   The walk
   ========================================================================= *)

(** [link_path_walk] with [walk_component], [lookup_last] and
    [path_lookupat] (fs/namei.c), over the remaining components.  [links]
    counts the links followed ([nd->total_link_count]); [trailing] is the
    LOOKUP_FOLLOW | LOOKUP_DIRECTORY a trailing '/' set; in [parent_mode]
    the last component is not looked up ([path_parentat]); [scoped] records
    a ".." taken under LOOKUP_IN_ROOT.  Each step, in kernel order: the
    current object must be a directory (ENOTDIR, [link_path_walk] after the
    previous step, or [path_init]); search permission ([may_lookup],
    EACCES); then the name. *)
Fixpoint walk_loop (fuel links : nat) (st : NsState) (ctx : NsCtx) (cr : WalkCreds)
    (fd_loc : Z -> option (option Loc)) (root current : Loc) (components : list (list byte))
    (trailing parent_mode scoped : bool) (fl : WalkFlags) : WalkResult * bool :=
  match fuel with
  | O => (WOver, scoped)
  | S f =>
      match components with
      | [] =>
          if parent_mode then (WOk current, scoped)
          else if wf_directory fl || trailing
          then match loc_dir st current with
               | Some true => (WOk current, scoped)
               | Some false => (WErr ENOTDIR, scoped)
               | None => (WOver, scoped)
               end
          else (WOk current, scoped)
      | name :: rest =>
          match loc_dir st current with
          | None => (WOver, scoped)
          | Some false => (WErr ENOTDIR, scoped)
          | Some true =>
              if negb (may_exec_dir st ctx cr current) then (WErr EACCES, scoped)
              else if parent_mode && is_last rest
              then (WOk current, scoped)
              else if is_dot_name name
              then walk_loop f links st ctx cr fd_loc root current rest trailing parent_mode scoped fl
              else if is_dotdot_name name
              then let scoped' := scoped || wf_in_root fl in
                   match follow_dotdot st root current with
                   | WOk next =>
                       walk_loop f links st ctx cr fd_loc root next rest trailing parent_mode scoped' fl
                   | WErr e => (WErr e, scoped')
                   | WOver => (WOver, scoped')
                   end
              else
                let follow := follow_link_now rest trailing fl in
                match lookup_child st ctx fd_loc current name with
                | LIError e => (WErr e, scoped)
                | LIOver => (WOver, scoped)
                | LIDentry raw =>
                    match step_into st raw with
                    | WErr e => (WErr e, scoped)
                    | WOver => (WOver, scoped)
                    | WOk next =>
                        match next with
                        | LProcTask _ _ _ =>
                            walk_loop f links st ctx cr fd_loc root next rest trailing parent_mode
                              scoped fl
                        | LDentry _ _ =>
                            match loc_inode st next with
                            | None => (WOver, scoped)
                            | Some ino =>
                                match ino_kind ino with
                                | ILnk =>
                                    if negb follow
                                    then walk_loop f links st ctx cr fd_loc root next rest trailing
                                           parent_mode scoped fl
                                    else if Nat.leb MAXSYMLINKS links then (WErr ELOOP, scoped)
                                    else if is_last rest && protected_link_undecided st cr current ino
                                    then (WOver, scoped)
                                    else match ino_bytes ino with
                                         | [] =>
                                             walk_loop f (S links) st ctx cr fd_loc root current rest
                                               trailing parent_mode scoped fl
                                         | target =>
                                             let base := if path_absolute target then root else current in
                                             let tail := match rest with
                                                         | [] => trailing || path_trailing_slash target
                                                         | _ :: _ => trailing
                                                         end in
                                             walk_loop f (S links) st ctx cr fd_loc root base
                                               (split_path target ++ rest) tail parent_mode scoped fl
                                         end
                                | _ =>
                                    walk_loop f links st ctx cr fd_loc root next rest trailing
                                      parent_mode scoped fl
                                end
                            end
                        end
                    end
                | LIProcSelf own =>
                    if negb follow then (WOver, scoped)
                    else if Nat.leb MAXSYMLINKS links then (WErr ELOOP, scoped)
                    else match own with
                         | None => (WErr ENOENT, scoped)
                         | Some pid =>
                             walk_loop f (S links) st ctx cr fd_loc root current
                               (split_path (decimal_bytes pid) ++ rest) trailing parent_mode scoped fl
                         end
                | LIMagicLink link target =>
                    if negb follow
                    then walk_loop f links st ctx cr fd_loc root link rest trailing parent_mode scoped fl
                    else if Nat.leb MAXSYMLINKS links then (WErr ELOOP, scoped)
                    else if wf_no_magiclinks fl then (WErr ELOOP, scoped)
                    else if wf_in_root fl then (WErr EXDEV, scoped)
                    else match target with
                         | Some t =>
                             walk_loop f (S links) st ctx cr fd_loc root t rest trailing parent_mode
                               scoped fl
                         | None => (WOver, scoped)
                         end
                end
          end
      end
  end.

(** The fuel of one walk: one step per component of the path, and room for
    MAXSYMLINKS link bodies of up to PATH_MAX + 1 components each. *)
Definition walk_fuel (p : list byte) : nat := length p + MAXSYMLINKS * (PATH_MAX + 1).

(** [filename_lookup] / [path_lookupat] (fs/namei.c) from [start]: the cwd
    for AT_FDCWD or the directory of a dirfd.  [getname_flags] refuses an
    empty path with ENOENT unless LOOKUP_EMPTY, and a path of PATH_MAX bytes
    or more with ENAMETOOLONG; an empty path under LOOKUP_EMPTY names the
    start, still subject to LOOKUP_DIRECTORY.  The boolean: a ".." was taken
    under LOOKUP_IN_ROOT, where [handle_dots] may also answer EAGAIN on a
    concurrent rename or mount. *)
Definition walk (st : NsState) (ctx : NsCtx) (cr : WalkCreds)
    (fd_loc : Z -> option (option Loc)) (start : Loc) (p : list byte) (fl : WalkFlags)
    : WalkResult * bool :=
  match p with
  | [] =>
      if wf_empty fl
      then walk_loop (walk_fuel p) 0 st ctx cr fd_loc (walk_root ctx start fl) start []
             false false false fl
      else (WErr ENOENT, false)
  | _ :: _ =>
      if Nat.leb PATH_MAX (length p) then (WErr ENAMETOOLONG, false)
      else let root := walk_root ctx start fl in
           walk_loop (walk_fuel p) 0 st ctx cr fd_loc root (walk_initial start root p fl)
             (split_path p) (path_trailing_slash p) false false fl
  end.

(** [nd->last_type] of the last component ([link_path_walk]). *)
Definition last_type (components : list (list byte)) : LastType :=
  match rev components with
  | [] => LastRoot
  | name :: _ => if is_dot_name name then LastDot
                 else if is_dotdot_name name then LastDotDot else LastNorm
  end.

Definition last_name (components : list (list byte)) : list byte :=
  match rev components with [] => [] | name :: _ => name end.

(** [filename_parentat] / [path_parentat] (fs/namei.c): the directory that
    holds the last component, the last name and its type.  Every component
    but the last is resolved as by [walk], links among them followed; the
    last is not looked up, but [link_path_walk] checks search permission on
    its directory first. *)
Definition walk_parent (st : NsState) (ctx : NsCtx) (cr : WalkCreds)
    (fd_loc : Z -> option (option Loc)) (start : Loc) (p : list byte) (fl : WalkFlags)
    : (WalkResult * list byte * LastType) * bool :=
  let components := split_path p in
  match p with
  | [] =>
      if wf_empty fl then ((WOk start, [], LastRoot), false)
      else ((WErr ENOENT, [], LastRoot), false)
  | _ :: _ =>
      if Nat.leb PATH_MAX (length p)
      then ((WErr ENAMETOOLONG, last_name components, last_type components), false)
      else match components with
           | [] =>
               match loc_dir st start with
               | Some true => ((WOk start, [], LastRoot), false)
               | Some false => ((WErr ENOTDIR, [], LastRoot), false)
               | None => ((WOver, [], LastRoot), false)
               end
           | _ :: _ =>
               let root := walk_root ctx start fl in
               let r := walk_loop (walk_fuel p) 0 st ctx cr fd_loc root (walk_initial start root p fl)
                          components false true false fl in
               ((fst r, last_name components, last_type components), snd r)
           end
  end.
