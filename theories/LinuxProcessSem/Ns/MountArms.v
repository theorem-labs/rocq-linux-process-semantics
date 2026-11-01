(** * LinuxProcessSem.Ns.MountArms — mount namespace system calls

    Arms for [mount] (40), [umount2] (39), [pivot_root] (41), and
    [mount_setattr] (442), over the mount operations of [Ns.Mount] and the
    path walk of [Ns.Walk].  New filesystem instances remain the named
    [do_new_mount] hook for the companion filesystem-instance model.

    Linux 6.18.44 sources:
    - [SYSCALL_DEFINE5(mount)], [do_mount], [path_mount], [may_mount],
      [do_loopback], [__do_loopback], [do_change_type], and [do_new_mount],
      fs/namespace.c:2954-3007, 3963-4051, 4216-4244;
    - [SYSCALL_DEFINE2(umount)], [ksys_umount], [path_umount], and
      [can_umount], fs/namespace.c:2016-2071;
    - [SYSCALL_DEFINE2(pivot_root)], fs/namespace.c:4551-4633, and
      [chroot_fs_refs], fs/fs_struct.c:55-78;
    - [SYSCALL_DEFINE5(mount_setattr)], [wants_mount_setattr],
      [build_mount_kattr], [do_mount_setattr], [mount_setattr_prepare], and
      [mnt_hold_writers], fs/namespace.c:596-655, 4705-4739, 4776-4829,
      4896-5030. *)

From Stdlib Require Import ZArith List Bool NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Mount NewMount Userns Walk Arm Task Files.
Import ListNotations.
Local Open Scope Z_scope.

(* =========================================================================
   Constants and common state access
   ========================================================================= *)

(** Legacy mount flags from include/uapi/linux/mount.h:13-59. *)
Definition MS_RDONLY : Z := 1.
Definition MS_NOSUID : Z := 2.
Definition MS_NODEV : Z := 4.
Definition MS_NOEXEC : Z := 8.
Definition MS_REMOUNT : Z := 32.
Definition MS_BIND : Z := 4096.
Definition MS_MOVE : Z := 8192.
Definition MS_REC : Z := 16384.
Definition MS_SILENT : Z := 32768.
Definition MS_NOATIME : Z := 1024.
Definition MS_NODIRATIME : Z := 2048.
Definition MS_UNBINDABLE : Z := 131072.
Definition MS_PRIVATE : Z := 262144.
Definition MS_SLAVE : Z := 524288.
Definition MS_SHARED : Z := 1048576.
Definition MS_RELATIME : Z := 2097152.
Definition MS_STRICTATIME : Z := 16777216.
Definition MS_LAZYTIME : Z := 33554432.
Definition MS_NOUSER : Z := 2147483648.
Definition MS_MGC_VAL : Z := 3236757504.
Definition MS_MGC_MSK : Z := 4294901760.

(** [umount2]'s flags, include/uapi/linux/mount.h and fs/namespace.c:2048. *)
Definition MNT_FORCE : Z := 1.
Definition MNT_DETACH : Z := 2.
Definition MNT_EXPIRE : Z := 4.
Definition UMOUNT_NOFOLLOW : Z := 8.

(** [mount_setattr]'s ABI flags, include/uapi/linux/fcntl.h and mount.h. *)
Definition AT_RECURSIVE : Z := 32768.
Definition MOUNT_ATTR_RDONLY : Z := 1.
Definition MOUNT_ATTR_NOSUID : Z := 2.
Definition MOUNT_ATTR_NODEV : Z := 4.
Definition MOUNT_ATTR_NOEXEC : Z := 8.
Definition MOUNT_ATTR__ATIME : Z := 112.
Definition MOUNT_ATTR_NOATIME : Z := 16.
Definition MOUNT_ATTR_STRICTATIME : Z := 32.
Definition MOUNT_ATTR_NODIRATIME : Z := 128.
Definition MOUNT_ATTR_IDMAP : Z := 1048576.
Definition MOUNT_ATTR_NOSYMFOLLOW : Z := 2097152.
Definition MOUNT_ATTR_SIZE_VER0 : Z := 32.
Definition O_RDWR : Z := 2.

(** [may_mount] (fs/namespace.c:2002-2005): CAP_SYS_ADMIN over the user
    namespace that owns the caller's mount namespace. *)
Definition mount_may_mount (m : Model) (ctx : NsCtx) (st : NsState) : option bool :=
  match find_mntns st (cx_mount ctx) with
  | Some ns => Some (cap_capable (ns_userns st) (task_cred m ctx) (mntns_owner ns) CAP_SYS_ADMIN)
  | None => None
  end.

(** [may_change_propagation] uses the user namespace of the changed mount. *)
Definition mount_may_change (m : Model) (ctx : NsCtx) (st : NsState) (mt : Mount) : option bool :=
  match find_mntns st (mnt_ns mt) with
  | Some ns => Some (cap_capable (ns_userns st) (task_cred m ctx) (mntns_owner ns) CAP_SYS_ADMIN)
  | None => None
  end.

Definition mount_ok (reads : list (word * nat)) (m : Model) (ctx : NsCtx) (st : NsState)
    : ext_outcome := ans reads (Z_to_bv 64 0) [] m ctx st.

Definition mount_mresult (reads : list (word * nat)) (r : MResult) (m : Model)
    (ctx : NsCtx) (st : NsState) : ext_outcome :=
  match r with
  | MOk ms => mount_ok reads m ctx (with_mounts st ms)
  | MErr e => err reads e m ctx st
  end.

Definition mount_env_errno (e : Z) : bool :=
  (e =? ENOMEM) || ((1 <=? e) && (e <=? 4095)).

(** [path_mounted] (fs/namespace.c): a dentry is the root of its mount. *)
Definition path_mounted (st : NsState) (mt d : positive) : option bool :=
  match find_mount (ns_mounts st) mt with
  | Some m => Some (Pos.eqb d (mnt_root m))
  | None => None
  end.

(* =========================================================================
   Mount's copied arguments and path facts
   ========================================================================= *)

(** [copy_mount_string] (fs/namespace.c:3944-3947). *)
Inductive MountString :=
  | MSOk (reads : list (word * nat)) (text : option (list byte))
  | MSErr (reads : list (word * nat)) (e : Z).

Definition copy_mount_string (i : SyscallInput) (p : word) : MountString :=
  if w_is0 p then MSOk [] None
  else let reads := path_reads i p in
       match path_arg i p with
       | PFault => MSErr reads EFAULT
       | PTooLong => MSErr reads ENAMETOOLONG
       | POk s => MSOk reads (Some s)
       end.

(** [copy_mount_options] (fs/namespace.c:3908-3941).  A fault before the
    first byte is EFAULT; once a byte has been copied, the partial option
    string can affect parsing and is outside this model. *)
Inductive MountOptions :=
  | MOOk (reads : list (word * nat)) (data : option (list byte))
  | MOErr (reads : list (word * nat)) (e : Z)
  | MOOver.

Definition copy_mount_options (i : SyscallInput) (p : word) : MountOptions :=
  if w_is0 p then MOOk [] None
  else let reads := path_reads i p in
       match path_arg i p with
       | PFault =>
           match reads with
           | [(_, 1%nat)] => MOErr reads EFAULT
           | _ => MOOver
           end
       | PTooLong => MOOver
       | POk data => MOOk reads (Some data)
       end.

(** [d_is_dir] for the source and target of [graft_tree]. *)
Definition dentry_dir (st : NsState) (d : positive) : option bool :=
  match dentry_inode st d with
  | Some ino => Some (match ino_kind ino with IDir => true | _ => false end)
  | None => None
  end.

(** [is_subdir] over dentry parent links, bounded by the listed dentries. *)
Fixpoint dentry_below_fuel (fuel : nat) (st : NsState) (root child : positive) : bool :=
  if Pos.eqb root child then true
  else match fuel with
       | O => false
       | Datatypes.S f =>
           match find_dentry st child with
           | Some d => match d_parent d with
                       | Some p => dentry_below_fuel f st root p
                       | None => false
                       end
           | None => false
           end
       end.

Definition dentry_below (st : NsState) (root child : positive) : bool :=
  dentry_below_fuel (length (ns_dentries st)) st root child.

(** The path facts [do_loopback] and [graft_tree] pass to [Mount.bind_mount]. *)
Definition bind_paths (st : NsState) (src sd tgt td : positive) : option BindPaths :=
  match find_mount (ns_mounts st) src, dentry_dir st sd, dentry_dir st td with
  | Some _, Some sdir, Some tdir =>
      Some (mkBindPaths sd (dentry_below st sd) false false (xorb sdir tdir))
  | _, _, _ => None
  end.

(** [path_mount] removes the obsolete high-half magic before any flag check. *)
Definition strip_mount_magic (flags : Z) : Z :=
  if Z.eqb (Z.land flags MS_MGC_MSK) MS_MGC_VAL then Z.land flags (Z.lnot MS_MGC_MSK)
  else flags.

Definition one_propagation (flags : Z) : bool :=
  let shared := has flags MS_SHARED in
  let private := has flags MS_PRIVATE in
  let slave := has flags MS_SLAVE in
  let unbindable := has flags MS_UNBINDABLE in
  (shared && negb private && negb slave && negb unbindable)
  || (private && negb shared && negb slave && negb unbindable)
  || (slave && negb shared && negb private && negb unbindable)
  || (unbindable && negb shared && negb private && negb slave).

Definition propagation_extra (flags : Z) : bool :=
  negb (Z.eqb (Z.land flags
    (Z.lnot (MS_SHARED + MS_PRIVATE + MS_SLAVE + MS_UNBINDABLE + MS_REC + MS_SILENT))) 0).

Definition follow_walk_flags : WalkFlags := mkWalkFlags true false false false false.
Definition directory_walk_flags : WalkFlags := mkWalkFlags true true false false false.

(* =========================================================================
   mount(2)
   ========================================================================= *)

(** [do_loopback] (fs/namespace.c:2976-3007), after both LOOKUP_FOLLOW
    walks and [path_mount]'s capability check. *)
Definition mount_bind (reads : list (word * nat)) (source : option (list byte))
    (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (tgt td : positive) (flags : Z) : ext_outcome :=
  match source with
  | None | Some [] => err reads EINVAL m ctx st
  | Some srcpath =>
      match fst (walk_from m ctx st (walk_creds m) AT_FDCWD_word srcpath follow_walk_flags) with
      | WErr e => err reads e m ctx st
      | WOver => EUnmodeled
      | WOk (LProcTask _ _ _) => EUnmodeled
      | WOk (LDentry src sd) =>
          match bind_paths st src sd tgt td with
          | None => EUnmodeled
          | Some bp =>
              match bind_mount (ns_mounts st) (cx_mount ctx) (env_mount_max (ns_env st)) src bp
                               (has flags MS_REC) tgt td with
              | Some r => mount_mresult reads r m ctx st
              | None => EUnmodeled
              end
          end
      end
  end.

(** [do_change_type] (fs/namespace.c:2856-2881).  Shared and unbindable
    propagation need group allocation or state the present mount tree omits. *)
Definition mount_change_type (reads : list (word * nat)) (i : SyscallInput) (m : Model)
    (ctx : NsCtx) (st : NsState) (target td : positive) (flags : Z) : ext_outcome :=
  match find_mount (ns_mounts st) target with
  | None => EUnmodeled
  | Some mt =>
      match path_mounted st target td with
      | Some false => err reads EINVAL m ctx st
      | None => EUnmodeled
      | Some true =>
          if negb (one_propagation flags) then err reads EINVAL m ctx st
          else if propagation_extra flags then EUnmodeled
          else match mount_may_change m ctx st mt with
               | None => EUnmodeled
               | Some false => err reads EPERM m ctx st
               | Some true =>
                   if has flags MS_SLAVE
                   then mount_mresult reads
                          (change_propagation (ns_mounts st) target (has flags MS_REC) PropSlave) m ctx st
                   else if has flags MS_PRIVATE
                   then mount_mresult reads
                          (change_propagation (ns_mounts st) target (has flags MS_REC) PropPrivate) m ctx st
                   else EUnmodeled
               end
      end
  end.

(** [do_new_mount] (fs/namespace.c:3681-3731): all mounts the model creates
    use the relatime default; another atime mode or an unheld flag declines. *)
Definition new_mount_nondefault_atime (flags : Z) : bool :=
  has flags MS_NOATIME || has flags MS_NODIRATIME || has flags MS_STRICTATIME
  || has flags MS_LAZYTIME.

Definition new_mount_extra_flags (flags : Z) : bool :=
  negb (Z.eqb (Z.land flags
    (Z.lnot (MS_RDONLY + MS_NOSUID + MS_NODEV + MS_NOEXEC + MS_RELATIME))) 0).

Definition new_mount_flags (flags : Z) : MountFlags :=
  mkMountFlags (has flags MS_RDONLY) (has flags MS_NOSUID)
               (has flags MS_NODEV) (has flags MS_NOEXEC).

(** [do_new_mount], [mount_capable], [mount_too_revealing], [do_add_mount]
    and [graft_tree], supplied by [Ns.NewMount].  One returned lock gives
    this evaluator's representative successful outcome. *)
Definition mount_new_instance (reads : list (word * nat)) (fstype : option (list byte))
    (data : option (list byte)) (m : Model) (ctx : NsCtx) (st : NsState)
    (target td : positive) (flags : Z) : ext_outcome :=
  if new_mount_nondefault_atime flags || new_mount_extra_flags flags then EUnmodeled
  else match fstype with
       | None => EUnmodeled
       | Some ty =>
           match parse_new_fs ty data, find_mntns st (cx_mount ctx) with
           | Some fs, Some mntns =>
               let fsuid := bv_unsigned (cr_euid (m_creds m)) in
               let fsgid := bv_unsigned (cr_egid (m_creds m)) in
               match new_mount st ctx (task_cred m ctx) fsuid fsgid fs (new_mount_flags flags)
                               (mntns_owner mntns) target td with
               | NMErr e => err reads e m ctx st
               | NMOver => EUnmodeled
               | NMOk locks mk =>
                   match locks with
                   | lk :: _ => mount_ok reads m ctx (mk lk)
                   | [] => EUnmodeled
                   end
               end
           | _, _ => EUnmodeled
           end
       end.

(** [mount] (fs/namespace.c:4216-4244): type, source and options are copied
    before [do_mount] walks the target; then [path_mount] dispatches by the
    stripped flags.  Kind: exact for the listed bind, propagation and new
    tmpfs, procfs and devpts forms; other legacy forms decline. *)
Definition mount_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let devp := in_arg i 0 in
  let dirp := in_arg i 1 in
  let typep := in_arg i 2 in
  let flagsp := bv_unsigned (in_arg i 3) in
  let datap := in_arg i 4 in
  match copy_mount_string i typep with
  | MSErr reads e => err reads e m ctx st
  | MSOk rtype fstype =>
      match copy_mount_string i devp with
      | MSErr reads e => err (rtype ++ reads) e m ctx st
      | MSOk rdev source =>
          match copy_mount_options i datap with
          | MOErr reads e => err (rtype ++ rdev ++ reads) e m ctx st
          | MOOver => EUnmodeled
          | MOOk ropts data =>
              let reads := rtype ++ rdev ++ ropts ++ path_reads i dirp in
              match path_arg i dirp with
              | PFault => err reads EFAULT m ctx st
              | PTooLong => err reads ENAMETOOLONG m ctx st
              | POk target_path =>
                  match fst (walk_from m ctx st (walk_creds m) AT_FDCWD_word target_path follow_walk_flags) with
                  | WErr e => err reads e m ctx st
                  | WOver | WOk (LProcTask _ _ _) => EUnmodeled
                  | WOk (LDentry target td) =>
                      let flags := strip_mount_magic flagsp in
                      if has flags MS_NOUSER then err reads EINVAL m ctx st
                      else match mount_may_mount m ctx st with
                           | None => EUnmodeled
                           | Some false => err reads EPERM m ctx st
                           | Some true =>
                               if has flags MS_REMOUNT then EUnmodeled
                               else if has flags MS_BIND then mount_bind reads source i m ctx st target td flags
                               else if has flags (MS_SHARED + MS_PRIVATE + MS_SLAVE + MS_UNBINDABLE)
                               then mount_change_type reads i m ctx st target td flags
                               else if has flags MS_MOVE then EUnmodeled
                               else mount_new_instance reads fstype data m ctx st target td flags
                           end
                  end
              end
          end
      end
  end.

(** The other [NMOk] choices of [new_mount] (fs/namespace.c:3681-3731):
    the visibility walk may pass either read-only lock that its table
    permits. *)
Definition mount_new_success (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (o : ext_outcome) : Prop :=
  let devp := in_arg i 0 in
  let dirp := in_arg i 1 in
  let typep := in_arg i 2 in
  let flags0 := bv_unsigned (in_arg i 3) in
  let datap := in_arg i 4 in
  match copy_mount_string i typep with
  | MSOk rtype (Some fstype) =>
      match copy_mount_string i devp with
      | MSOk rdev _ =>
          match copy_mount_options i datap with
          | MOOk ropts data =>
              let reads := rtype ++ rdev ++ ropts ++ path_reads i dirp in
              match path_arg i dirp with
              | POk target_path =>
                  match fst (walk_from m ctx st (walk_creds m) AT_FDCWD_word target_path follow_walk_flags) with
                  | WOk (LDentry target td) =>
                      let flags := strip_mount_magic flags0 in
                      has flags MS_NOUSER = false /\
                      mount_may_mount m ctx st = Some true /\
                      has flags MS_REMOUNT = false /\
                      has flags MS_BIND = false /\
                      has flags (MS_SHARED + MS_PRIVATE + MS_SLAVE + MS_UNBINDABLE) = false /\
                      has flags MS_MOVE = false /\
                      new_mount_nondefault_atime flags = false /\
                      new_mount_extra_flags flags = false /\
                      match parse_new_fs fstype data, find_mntns st (cx_mount ctx) with
                      | Some fs, Some mntns =>
                          let fsuid := bv_unsigned (cr_euid (m_creds m)) in
                          let fsgid := bv_unsigned (cr_egid (m_creds m)) in
                          match new_mount st ctx (task_cred m ctx) fsuid fsgid fs (new_mount_flags flags)
                                          (mntns_owner mntns) target td with
                          | NMOk locks mk => exists lk, In lk locks /\ o = mount_ok reads m ctx (mk lk)
                          | _ => False
                          end
                      | _, _ => False
                      end
                  | _ => False
                  end
              | _ => False
              end
          | _ => False
          end
      | _ => False
      end
  | _ => False
  end.

Definition mount_arm : NsArm := fun i m ctx st o =>
  o = mount_fn i m ctx st
  \/ mount_new_success i m ctx st o
  \/ injected_after mount_env_errno (mount_fn i m ctx st) m ctx st o.

(** [mount_arm] keeps every successful [NMOk] lock choice, while [mount_fn]
    supplies the deterministic legacy outcomes and one new-mount witness. *)

(* =========================================================================
   umount2(2)
   ========================================================================= *)

Definition umount_valid (flags : Z) : bool :=
  Z.eqb (Z.land flags (Z.lnot (MNT_FORCE + MNT_DETACH + MNT_EXPIRE + UMOUNT_NOFOLLOW))) 0.

(** [can_umount] and [path_umount] (fs/namespace.c:2016-2045).  The
    MNT_DETACH tree operation itself is [Mount.umount_detach]. *)
Definition umount2_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let pathp := in_arg i 0 in
  let flags := Z.land (bv_unsigned (in_arg i 1)) 4294967295 in
  let reads := path_reads i pathp in
  if negb (umount_valid flags) then err [] EINVAL m ctx st
  else if negb (Z.eqb flags MNT_DETACH) then EUnmodeled
  else match path_arg i pathp with
       | PFault => err reads EFAULT m ctx st
       | PTooLong => err reads ENAMETOOLONG m ctx st
       | POk path =>
           let fl := mkWalkFlags (negb (has flags UMOUNT_NOFOLLOW)) false false false false in
           match fst (walk_from m ctx st (walk_creds m) AT_FDCWD_word path fl) with
           | WErr e => err reads e m ctx st
           | WOver | WOk (LProcTask _ _ _) => EUnmodeled
           | WOk (LDentry mt d) =>
               match follow_mounts st (LDentry mt d) with
               | WErr e => err reads e m ctx st
               | WOver | WOk (LProcTask _ _ _) => EUnmodeled
               | WOk (LDentry top td) =>
                   match mount_may_mount m ctx st with
                   | None => EUnmodeled
                   | Some false => err reads EPERM m ctx st
                   | Some true =>
                       match find_mount (ns_mounts st) top, path_mounted st top td with
                       | Some mount, Some true =>
                           if negb (Pos.eqb (mnt_ns mount) (cx_mount ctx)) then err reads EINVAL m ctx st
                           else if mnt_locked mount then err reads EINVAL m ctx st
                           else if umount_propagates (ns_mounts st) mount then EUnmodeled
                           else mount_mresult reads (umount_detach (ns_mounts st) top) m ctx st
                       | Some _, Some false => err reads EINVAL m ctx st
                       | _, _ => EUnmodeled
                       end
                   end
               end
           end
       end.

Definition umount2_arm : NsArm := fun i m ctx st o =>
  o = umount2_fn i m ctx st
  \/ injected_after mount_env_errno (umount2_fn i m ctx st) m ctx st o.

(* =========================================================================
   pivot_root(2)
   ========================================================================= *)

(** [chroot_fs_refs] (fs/fs_struct.c:55-78) is process-wide; this
    single-task arm is therefore over on other tasks' references. *)
Definition move_pivot_refs (ctx : NsCtx) (old_root new_root : positive * positive) : NsCtx :=
  let root := if Pos.eqb (fst (cx_root ctx)) (fst old_root) && Pos.eqb (snd (cx_root ctx)) (snd old_root)
              then new_root else cx_root ctx in
  let cwd := if Pos.eqb (fst (cx_cwd ctx)) (fst old_root) && Pos.eqb (snd (cx_cwd ctx)) (snd old_root)
             then new_root else cx_cwd ctx in
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) root cwd
          (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx)
          (cx_no_new_privs ctx) (cx_dumpable ctx).

(** [pivot_root] uses the table's retained dentry as [d_unlinked = false]. *)
Definition pivot_paths (st : NsState) (rt rd nr nd : positive) : option PivotPaths :=
  match find_mount (ns_mounts st) rt, find_mount (ns_mounts st) nr,
        find_dentry st nd with
  | Some root, Some new, Some _ =>
      Some (mkPivotPaths false (Pos.eqb rd (mnt_root root)) (Pos.eqb nd (mnt_root new)))
  | _, _, _ => None
  end.

(** [pivot_root] (fs/namespace.c:4551-4633): [may_mount] precedes the two
    LOOKUP_FOLLOW|LOOKUP_DIRECTORY walks; [LOCK_MOUNT] supplies the top
    mount at put_old. *)
Definition pivot_root_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  match mount_may_mount m ctx st with
  | None => EUnmodeled
  | Some false => ns_errno EPERM m ctx st
  | Some true =>
      let newp := in_arg i 0 in
      let oldp := in_arg i 1 in
      let rnew := path_reads i newp in
      match path_arg i newp with
      | PFault => err rnew EFAULT m ctx st
      | PTooLong => err rnew ENAMETOOLONG m ctx st
      | POk new_path =>
          match fst (walk_from m ctx st (walk_creds m) AT_FDCWD_word new_path directory_walk_flags) with
          | WErr e => err rnew e m ctx st
          | WOver | WOk (LProcTask _ _ _) => EUnmodeled
          | WOk (LDentry nr nd) =>
              let reads := rnew ++ path_reads i oldp in
              match path_arg i oldp with
              | PFault => err reads EFAULT m ctx st
              | PTooLong => err reads ENAMETOOLONG m ctx st
              | POk old_path =>
                  match fst (walk_from m ctx st (walk_creds m) AT_FDCWD_word old_path directory_walk_flags) with
                  | WErr e => err reads e m ctx st
                  | WOver | WOk (LProcTask _ _ _) => EUnmodeled
                  | WOk (LDentry old od) =>
                      let rt := fst (cx_root ctx) in
                      let rd := snd (cx_root ctx) in
                      match pivot_paths st rt rd nr nd with
                      | None => EUnmodeled
                      | Some pp =>
                          match pivot_root (ns_mounts st) (cx_mount ctx) rt nr old od pp with
                          | MErr e => err reads e m ctx st
                          | MOk ms =>
                              mount_ok reads m
                                (move_pivot_refs ctx (rt, rd) (nr, nd)) (with_mounts st ms)
                          end
                      end
                  end
              end
          end
      end
  end.

Definition pivot_root_arm : NsArm := fun i m ctx st o =>
  o = pivot_root_fn i m ctx st
  \/ injected_after mount_env_errno (pivot_root_fn i m ctx st) m ctx st o.

(* =========================================================================
   mount_setattr(2)
   ========================================================================= *)

Record MountAttr := mkMountAttr {
  ma_set : Z;
  ma_clr : Z;
  ma_propagation : Z;
  ma_userns_fd : Z
}.

Inductive AttrCopy :=
  | ACok (reads : list (word * nat)) (attr : MountAttr)
  | ACerr (reads : list (word * nat)) (e : Z)
  | ACover.

Definition attr_word (bs : list byte) (off : nat) : Z :=
  bytes_le_to_Z (firstn 8 (skipn off bs)).

Definition byte_zero (b : byte) : bool := bv_eqb b (Z_to_bv 8 0).

(** [copy_struct_from_user] (lib/struct.c), as called by
    [wants_mount_setattr] (fs/namespace.c:4965-4988). *)
Definition copy_mount_attr (i : SyscallInput) (p : word) (usize : Z) : AttrCopy :=
  if 4096 <? usize then ACerr [] E2BIG
  else if usize <? MOUNT_ATTR_SIZE_VER0 then ACerr [] EINVAL
  else if negb (access_okb p usize) then ACerr [(p, Z.to_nat usize)] EFAULT
  else match read_bytes_map (in_mem i) p (Z_to_bv 64 usize) with
       | None => ACover
       | Some bs =>
           if negb (forallb byte_zero (skipn (Z.to_nat MOUNT_ATTR_SIZE_VER0) bs)) then ACerr [(p, Z.to_nat usize)] E2BIG
           else ACok [(p, Z.to_nat usize)]
                  (mkMountAttr (attr_word bs 0) (attr_word bs 8) (attr_word bs 16) (attr_word bs 24))
       end.

Inductive AttrBuild := ABok (change : AttrChange) | ABerr (e : Z) | ABover.

Definition mount_attr_valid : Z :=
  MOUNT_ATTR_RDONLY + MOUNT_ATTR_NOSUID + MOUNT_ATTR_NODEV + MOUNT_ATTR_NOEXEC
  + MOUNT_ATTR__ATIME + MOUNT_ATTR_NODIRATIME + MOUNT_ATTR_IDMAP + MOUNT_ATTR_NOSYMFOLLOW.

Definition mount_attr_prop_valid : Z := MS_SHARED + MS_PRIVATE + MS_SLAVE + MS_UNBINDABLE.

Definition attr_atime_valid (a : MountAttr) : bool :=
  let clear := Z.land (ma_clr a) MOUNT_ATTR__ATIME in
  let set := Z.land (ma_set a) MOUNT_ATTR__ATIME in
  if Z.eqb clear 0 then Z.eqb set 0
  else if Z.eqb clear MOUNT_ATTR__ATIME
       then (Z.eqb set 0 || Z.eqb set MOUNT_ATTR_NOATIME || Z.eqb set MOUNT_ATTR_STRICTATIME)
       else false.

(** [build_mount_kattr] (fs/namespace.c:4896-4942).  The four basic flags
    are the handled subset; atime, idmap and no-symlink flags decline only
    after their kernel validity checks have succeeded. *)
Definition build_mount_attr (a : MountAttr) : AttrBuild :=
  if negb (Z.eqb (Z.land (ma_propagation a) (Z.lnot mount_attr_prop_valid)) 0) then ABerr EINVAL
  else if negb (one_propagation (ma_propagation a) || Z.eqb (ma_propagation a) 0) then ABerr EINVAL
  else if negb (Z.eqb (Z.land (Z.lor (ma_set a) (ma_clr a)) (Z.lnot mount_attr_valid)) 0) then ABerr EINVAL
  else if negb (attr_atime_valid a) then ABerr EINVAL
  else if has (ma_clr a) MOUNT_ATTR_IDMAP then ABerr EINVAL
  else if negb (Z.eqb (ma_propagation a) 0) then ABover
  else if negb (Z.eqb (ma_clr a) 0) then ABover
  else if negb (Z.eqb (ma_userns_fd a) 0) then ABover
  else if negb (Z.eqb (Z.land (ma_set a)
                     (Z.lnot (MOUNT_ATTR_RDONLY + MOUNT_ATTR_NOSUID + MOUNT_ATTR_NODEV + MOUNT_ATTR_NOEXEC))) 0)
       then ABover
       else ABok (mkAttr
         (mkMountFlags (has (ma_set a) MOUNT_ATTR_RDONLY) (has (ma_set a) MOUNT_ATTR_NOSUID)
                       (has (ma_set a) MOUNT_ATTR_NODEV) (has (ma_set a) MOUNT_ATTR_NOEXEC))
         (mkMountFlags false false false false)).

Definition mount_setattr_flags_valid (flags : Z) : bool :=
  Z.eqb (Z.land flags (Z.lnot (AT_EMPTY_PATH + AT_RECURSIVE + AT_SYMLINK_NOFOLLOW + AT_NO_AUTOMOUNT))) 0.

Definition mount_setattr_handled_flags (flags : Z) : bool :=
  Z.eqb (Z.land flags (Z.lnot (AT_EMPTY_PATH + AT_RECURSIVE))) 0.

Definition file_writes (f : NsFile) : bool :=
  let access := Z.land (nf_flags f) O_ACCMODE in
  Z.eqb access O_WRONLY || Z.eqb access O_RDWR.

(** [mnt_hold_writers] (fs/namespace.c:613-624), for each mount reached by
    [mount_setattr_prepare]. *)
Definition setattr_writer_busy (st : NsState) (targets : list positive) : bool :=
  existsb (fun p =>
    let f := snd p in
    file_writes f &&
    match nsfile_loc f with
    | None => false
    | Some l =>
        if mem (loc_mnt l) targets then
          match find_mount (ns_mounts st) (loc_mnt l) with
          | Some mt => negb (mf_ro (mnt_flags mt))
          | None => false
          end
        else false
    end) (ns_files st).

(** [do_mount_setattr] (fs/namespace.c:4776-4829): the target must name a
    mount root in the caller's namespace before [Mount.mount_setattr]
    changes the selected tree. *)
Definition mount_setattr_apply (reads : list (word * nat)) (change : AttrChange) (recursive : bool)
    (m : Model) (ctx : NsCtx) (st : NsState) (mt d : positive) : ext_outcome :=
  match find_mount (ns_mounts st) mt, path_mounted st mt d with
  | Some mount, Some true =>
      if negb (Pos.eqb (mnt_ns mount) (cx_mount ctx)) then err reads EINVAL m ctx st
      else if mf_ro (at_set change) && setattr_writer_busy st (setattr_targets (ns_mounts st) mt recursive)
      then err reads EBUSY m ctx st
      else mount_mresult reads (mount_setattr (ns_mounts st) mt recursive change) m ctx st
  | Some _, Some false => err reads EINVAL m ctx st
  | _, _ => EUnmodeled
  end.

(** [mount_setattr] (fs/namespace.c:4993-5030): flag and struct validation,
    [may_mount], and path resolution precede [do_mount_setattr].  Kind:
    exact for the stated basic attribute subset; all other accepted ABI
    forms decline. *)
Definition mount_setattr_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    : ext_outcome :=
  let dfd := in_arg i 0 in
  let pathp := in_arg i 1 in
  let flags := Z.land (bv_unsigned (in_arg i 2)) 4294967295 in
  let attrp := in_arg i 3 in
  let usize := bv_unsigned (in_arg i 4) in
  if negb (mount_setattr_flags_valid flags) then ns_errno EINVAL m ctx st
  else if negb (mount_setattr_handled_flags flags) then EUnmodeled
  else match mount_may_mount m ctx st with
       | None => EUnmodeled
       | Some false => ns_errno EPERM m ctx st
       | Some true =>
           match copy_mount_attr i attrp usize with
           | ACerr reads e => err reads e m ctx st
           | ACover => EUnmodeled
           | ACok attr_reads attr =>
               match build_mount_attr attr with
               | ABerr e => err attr_reads e m ctx st
               | ABover => EUnmodeled
               | ABok change =>
                   if Z.eqb (ma_set attr) 0 && Z.eqb (ma_clr attr) 0 && Z.eqb (ma_propagation attr) 0
                   then mount_ok attr_reads m ctx st
                   else
                     let reads := attr_reads ++ path_reads i pathp in
                     match path_arg i pathp with
                     | PFault => err reads EFAULT m ctx st
                     | PTooLong => err reads ENAMETOOLONG m ctx st
                     | POk path =>
                         let fl := mkWalkFlags true false (has flags AT_EMPTY_PATH) false false in
                         match fst (walk_from m ctx st (walk_creds m) dfd path fl) with
                         | WErr e => err reads e m ctx st
                         | WOver | WOk (LProcTask _ _ _) => EUnmodeled
                         | WOk (LDentry mt d) =>
                             mount_setattr_apply reads change (has flags AT_RECURSIVE) m ctx st mt d
                         end
                     end
               end
           end
       end.

Definition mount_setattr_arm : NsArm := fun i m ctx st o =>
  o = mount_setattr_fn i m ctx st
  \/ injected_after mount_env_errno (mount_setattr_fn i m ctx st) m ctx st o.

(** The environment refusals of mount namespace operations. *)
Definition mount_injected : list NsInjected :=
  map (fun n => mkNsInjected n
    [(fun e => e =? ENOMEM, FamAlloc);
     (fun e => (1 <=? e) && (e <=? 4095), FamCred)])
    [39; 40; 41; 442].

(** The four legacy mount-namespace calls supplied by this module. *)
Definition mount_arms : list (Z * NsArm) :=
  [(39, with_injected mount_env_errno umount2_arm);
   (40, with_injected mount_env_errno mount_arm);
   (41, with_injected mount_env_errno pivot_root_arm);
   (442, with_injected mount_env_errno mount_setattr_arm)].
