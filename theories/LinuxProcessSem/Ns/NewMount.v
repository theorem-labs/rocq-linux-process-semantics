(** * LinuxProcessSem.Ns.NewMount — a new mount of tmpfs, procfs or devpts

    What [mount(2)] does after [path_mount] chose [do_new_mount] (Linux
    6.18.44 fs/namespace.c), for the three file systems a user namespace
    may mount (FS_USERNS_MOUNT): the type and options, the new superblock
    and its root, the capability [mount_capable] asks for, the visibility
    check [mount_too_revealing] makes for procfs, and the attach
    ([do_add_mount], [graft_tree], [attach_recursive_mnt]).

    - tmpfs (mm/shmem.c [shmem_init_fs_context], [shmem_parse_one],
      [shmem_fill_super]): the root directory has mode [mode] (01777 when
      no option gives one) and the caller's fsuid and fsgid; the
      superblock belongs to the caller's user namespace.
    - procfs (fs/proc/root.c [proc_init_fs_context], [proc_fill_super]):
      a new superblock of the caller's pid namespace, owned by that pid
      namespace's user namespace, with SB_I_USERNS_VISIBLE, SB_I_NOEXEC and
      SB_I_NODEV; the root directory (0555, kuid 0) and the static entries
      the kernel configuration lists ([env_proc_entries]); the task
      directories, self and thread-self are the walk's.
    - devpts (fs/devpts/inode.c [devpts_parse_param], [devpts_fill_super],
      [mknod_ptmx]): the root directory (0755, kuid 0) and [ptmx], a
      character device 5:2 with mode [ptmxmode] (0 by default) owned by the
      caller's fsuid and fsgid.

    A superblock of a user namespace other than the initial one has
    SB_I_NODEV ([alloc_super], fs/super.c), but devpts clears it.

    The model holds no atime mode: every mount is relatime, the default
    [path_mount] gives, so a new mount asking for another atime mode
    declines, and [mnt_already_visible]'s atime comparison always holds.
    A start state whose mounts are not all relatime is outside the model. *)

From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount Userns Walk.
Import ListNotations.
Local Open Scope Z_scope.

Inductive NewFs :=
  | NewTmpfs (mode : Z)
  | NewProc
  | NewDevpts (ptmxmode : Z).

Definition TMPFS_MAGIC : Z := 16914836.        (* 0x01021994 *)
Definition PROC_SUPER_MAGIC : Z := 40864.      (* 0x9fa0 *)
Definition DEVPTS_SUPER_MAGIC : Z := 7377.     (* 0x1cd1 *)

(* =========================================================================
   Type and options
   ========================================================================= *)

Definition bytes_of (l : list Z) : list byte := map (Z_to_bv 8) l.

Definition fs_tmpfs : list byte := bytes_of [116; 109; 112; 102; 115].
Definition fs_proc : list byte := bytes_of [112; 114; 111; 99].
Definition fs_devpts : list byte := bytes_of [100; 101; 118; 112; 116; 115].
Definition opt_mode : list byte := bytes_of [109; 111; 100; 101].
Definition opt_ptmxmode : list byte := bytes_of [112; 116; 109; 120; 109; 111; 100; 101].
Definition opt_newinstance : list byte :=
  bytes_of [110; 101; 119; 105; 110; 115; 116; 97; 110; 99; 101].

(** The options as [generic_parse_monolithic] splits them: at each comma. *)
Fixpoint split_commas (l : list byte) : list (list byte) :=
  match l with
  | [] => [[]]
  | c :: r => if (bv_unsigned c =? 44) then [] :: split_commas r
              else match split_commas r with
                   | w :: ws => (c :: w) :: ws
                   | [] => [[c]]
                   end
  end.

(** [key=value] split at the first '='. *)
Fixpoint split_eq (l : list byte) : list byte * option (list byte) :=
  match l with
  | [] => ([], None)
  | c :: r => if (bv_unsigned c =? 61) then ([], Some r)
              else let (k, v) := split_eq r in (c :: k, v)
  end.

(** [fsparam_u32oct]: the value read as an octal number ([kstrtouint] in
    base 8 with an optional leading 0): [None] for a value that is not
    one; the kernel's EINVAL for it is not modelled (the arm declines). *)
Fixpoint octal_acc (acc : Z) (l : list byte) : option Z :=
  match l with
  | [] => Some acc
  | c :: r => let v := bv_unsigned c in
              if (48 <=? v) && (v <=? 55) then octal_acc (acc * 8 + (v - 48)) r else None
  end.

Definition octal (l : list byte) : option Z :=
  match l with [] => None | _ => match octal_acc 0 l with
                                 | Some v => if v <? 4294967296 then Some v else None
                                 | None => None
                                 end end.

(** The options the model reads, folded over the pieces: tmpfs takes
    [mode=]; devpts takes [newinstance], [ptmxmode=] and [mode=] (the mode
    of pty slaves, which no modelled call creates); procfs takes none.
    Any other piece, or a value that is not octal, declines. *)
Definition parse_new_fs (fstype : list byte) (data : option (list byte)) : option NewFs :=
  let pieces := match data with
                | None => []
                | Some d => List.filter (fun p => negb (Nat.eqb (length p) 0)) (split_commas d)
                end in
  if bytes_eqb fstype fs_tmpfs then
    fold_left (fun acc p => match acc with
                            | None => None
                            | Some (NewTmpfs m) =>
                                match split_eq p with
                                | (k, Some v) => if bytes_eqb k opt_mode
                                                 then option_map (fun x => NewTmpfs (Z.land x 4095)) (octal v)
                                                 else None
                                | _ => None
                                end
                            | Some _ => None
                            end) pieces (Some (NewTmpfs 1023))
  else if bytes_eqb fstype fs_proc then
    match pieces with [] => Some NewProc | _ => None end
  else if bytes_eqb fstype fs_devpts then
    fold_left (fun acc p => match acc with
                            | None => None
                            | Some (NewDevpts x) =>
                                match split_eq p with
                                | (k, None) => if bytes_eqb k opt_newinstance then Some (NewDevpts x) else None
                                | (k, Some v) =>
                                    if bytes_eqb k opt_ptmxmode
                                    then option_map (fun y => NewDevpts (Z.land y 4095)) (octal v)
                                    else if bytes_eqb k opt_mode
                                    then option_map (fun _ => NewDevpts x) (octal v)
                                    else None
                                end
                            | Some _ => None
                            end) pieces (Some (NewDevpts 0))
  else None.

(* =========================================================================
   The new superblock and its root
   ========================================================================= *)

Definition max_sb_id (st : NsState) : positive :=
  fold_left (fun acc s => Pos.max acc (sb_id s)) (ns_sbs st) 1%positive.
Definition max_dentry_id' (st : NsState) : positive :=
  fold_left (fun acc d => Pos.max acc (d_id d)) (ns_dentries st) 1%positive.
Definition max_inode_id' (st : NsState) : positive :=
  fold_left (fun acc n => Pos.max acc (ino_id n)) (ns_inodes st) 1%positive.

Definition pid_owner (st : NsState) (p : positive) : option positive :=
  match find (fun x => Pos.eqb (pidns_id x) p) (ns_pidns st) with
  | Some x => Some (pidns_owner x)
  | None => None
  end.

(** The user namespace [fc->user_ns] that owns the new superblock: the
    caller's for tmpfs and devpts, its pid namespace's owner for procfs. *)
Definition fs_owner (st : NsState) (ctx : NsCtx) (fs : NewFs) : option positive :=
  match fs with
  | NewProc => pid_owner st (cx_pidns ctx)
  | _ => Some (cx_user ctx)
  end.

Definition is_init_userns (st : NsState) (u : positive) : bool :=
  match find_userns (ns_userns st) u with
  | Some x => match uns_parent x with None => true | Some _ => false end
  | None => true
  end.

(** The static entries of a procfs instance, made under root dentry
    [root] of superblock [s], with dentries and inodes from [d0] and [i0]
    on: each entry's parent is the entry with its path less the last
    name, made before it, or the root. *)
Fixpoint proc_entries (s root : positive) (d0 i0 : positive) (made : list (list (list byte) * positive))
    (es : list ProcEntry) : list Dentry * list Inode :=
  match es with
  | [] => ([], [])
  | e :: r =>
      let parent_path := removelast (px_path e) in
      let parent := match find (fun p => (Nat.eqb (length (fst p)) (length parent_path))
                                         && forallb (fun ab => bytes_eqb (fst ab) (snd ab))
                                                    (combine (fst p) parent_path)) made with
                    | Some (_, d) => d
                    | None => root
                    end in
      let name := last (px_path e) [] in
      let (ds, ins) := proc_entries s root (Pos.succ d0) (Pos.succ i0) ((px_path e, d0) :: made) r in
      (mkDentry d0 s (Some parent) name i0 :: ds,
       mkInode i0 (px_kind e) (px_perm e) (px_uid e) (px_gid e) 0 [] (px_empty e) :: ins)
  end.

(** The new superblock, its dentries and inodes: [get_tree] of each file
    system.  [pidns] is the caller's pid namespace; [rdonly] is SB_RDONLY
    from the mount flags; [fsuid] and [fsgid] are the caller's.  The
    device number of ptmx is [new_encode_dev (MKDEV (5, 2))]. *)
Definition new_tree (st : NsState) (owner pidns : positive) (fs : NewFs) (rdonly : bool)
    (fsuid fsgid : Z) : SuperBlock * list Dentry * list Inode :=
  let s := Pos.succ (max_sb_id st) in
  let rd := Pos.succ (max_dentry_id' st) in
  let ri := Pos.succ (max_inode_id' st) in
  let nodev := negb (is_init_userns st owner) in
  match fs with
  | NewTmpfs mode =>
      (mkSb s SbTmpfs owner rd rdonly TMPFS_MAGIC false false nodev,
       [mkDentry rd s None [] ri],
       [mkInode ri IDir mode fsuid fsgid 0 [] false])
  | NewProc =>
      let (ds, ins) := proc_entries s rd (Pos.succ rd) (Pos.succ ri) [] (env_proc_entries (ns_env st)) in
      (mkSb s (SbProc pidns) owner rd rdonly PROC_SUPER_MAGIC true true true,
       mkDentry rd s None [] ri :: ds,
       mkInode ri IDir 365 0 0 0 [] false :: ins)
  | NewDevpts ptmxmode =>
      (mkSb s SbDevpts owner rd rdonly DEVPTS_SUPER_MAGIC false false false,
       [mkDentry rd s None [] ri;
        mkDentry (Pos.succ rd) s (Some rd) (bytes_of [112; 116; 109; 120]) (Pos.succ ri)],
       [mkInode ri IDir 493 0 0 0 [] false;
        mkInode (Pos.succ ri) IChr ptmxmode fsuid fsgid 1282 [] false])
  end.

(* =========================================================================
   mount_too_revealing
   ========================================================================= *)

Definition is_proc_sb (st : NsState) (s : positive) : bool :=
  match find_sb st s with Some x => match sb_kind x with SbProc _ => true | _ => false end
                        | None => false end.

(** [mnt_already_visible]: the procfs mounts of mount namespace [ns] that
    show their superblock's root, are no more restrictive than the new
    mount ([new_ro]: MNT_READONLY; a mount whose read-only is locked, or
    whose superblock is read-only, needs it), and whose MNT_LOCKED child
    mounts all sit on directories that stay empty.  Each answers with the
    read-only lock it passes to the new mount; the kernel takes the first
    in its walk of the namespace's mount tree, which the model does not
    order, so any of them may be the one. *)
Definition visible_locks (st : NsState) (ns : positive) (new_ro : bool) : list bool :=
  flat_map (fun mt =>
    match find_sb st (mnt_sb mt) with
    | Some s =>
        let lock_ro := mf_ro (mnt_lock_flags mt) || sb_rdonly s in
        if negb (Pos.eqb (mnt_ns mt) ns) then []
        else if negb (match sb_kind s with SbProc _ => true | _ => false end) then []
        else if negb (Pos.eqb (mnt_root mt) (sb_root s)) then []
        else if lock_ro && negb new_ro then []
        else if existsb (fun c => is_child_of (mnt_id mt) c && mnt_locked c
                                  && negb (match dentry_inode st (mnt_mountpoint c) with
                                           | Some i => ino_empty_dir i
                                           | None => false
                                           end))
                        (ns_mounts st)
        then []
        else [lock_ro]
    | None => []
    end) (ns_mounts st).

(** [mount_too_revealing]: never for a mount namespace of the initial user
    namespace or a file system without SB_I_USERNS_VISIBLE; else the
    read-only locks a visible procfs mount can pass, none meaning EPERM.
    [None] is "not revealing, nothing passed". *)
Definition revealing_locks (st : NsState) (ctx : NsCtx) (mntns_owner : positive) (fs : NewFs)
    (new_ro : bool) : option (list bool) :=
  if is_init_userns st mntns_owner then None
  else match fs with
       | NewProc => Some (visible_locks st (cx_mount ctx) new_ro)
       | _ => None
       end.

(* =========================================================================
   The new mount
   ========================================================================= *)

Inductive NewMountRes :=
  | NMErr (e : Z)
  | NMOver
  | NMOk (locks : list bool) (mk : bool -> NsState).

(** The new mount of [fs] with mount flags [mf] onto dentry [tgt_dentry]
    of mount [tgt] (the top of the mount stack there), by a task with
    context [ctx], credential [cred] and fsuid/fsgid [fsuid]/[fsgid], in
    [do_new_mount]'s order after the options: [mount_capable] (EPERM);
    [get_tree]; [mount_too_revealing] (EPERM); [do_add_mount]: a target
    mount outside the caller's mount namespace (EINVAL), the same
    superblock on the same place (EBUSY, which a new superblock never
    is); [graft_tree]: a target that is not a directory (ENOTDIR); the
    mount limit (ENOSPC); a shared target declines (the new mount
    propagates).  [NMOk locks mk]: the answer is [mk lk] for some [lk] in
    [locks], the read-only lock the new mount takes (one value, false,
    when no visibility check ran). *)
Definition new_mount (st : NsState) (ctx : NsCtx) (cred : IdCred) (fsuid fsgid : Z) (fs : NewFs)
    (mf : MountFlags) (mntns_owner tgt tgt_dentry : positive) : NewMountRes :=
  match fs_owner st ctx fs, find_mount (ns_mounts st) tgt with
  | Some owner, Some t =>
      if negb (cap_capable (ns_userns st) cred owner CAP_SYS_ADMIN) then NMErr EPERM
      else
        let locks := match revealing_locks st ctx mntns_owner fs (mf_ro mf) with
                     | None => [false]
                     | Some l => l
                     end in
        match locks with
        | [] => NMErr EPERM
        | _ =>
            if negb (Pos.eqb (mnt_ns t) (cx_mount ctx)) then NMErr EINVAL
            else match dentry_inode st tgt_dentry with
                 | None => NMOver
                 | Some ti =>
                     if negb (match ino_kind ti with IDir => true | _ => false end) then NMErr ENOTDIR
                     else if (env_mount_max (ns_env st)
                              <? Z.of_nat (ns_mount_count (ns_mounts st) (cx_mount ctx) + 1))
                     then NMErr ENOSPC
                     else if is_shared (ns_mounts st) tgt then NMOver
                     else
                       let '(s, ds, ins) := new_tree st owner (cx_pidns ctx) fs (mf_ro mf) fsuid fsgid in
                       let mid := Pos.succ (max_mount_id (ns_mounts st)) in
                       NMOk locks (fun lk =>
                         mkNsState
                           (ns_mounts st ++
                              [mkMount mid (cx_mount ctx) (Some tgt) tgt_dentry (sb_root s) (sb_id s) mf
                                       (mkMountFlags lk false false false) false false None None])
                           (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st)
                           (ns_sbs st ++ [s]) (ns_dentries st ++ ds) (ns_inodes st ++ ins)
                           (ns_files st) (ns_env st))
                 end
        end
  | _, _ => NMOver
  end.

(** A new mount that succeeds adds one mount, in the caller's mount
    namespace, on the target, showing the new superblock's root. *)
Theorem new_mount_adds : forall st ctx cred fsuid fsgid fs mf o tgt d locks mk lk,
  new_mount st ctx cred fsuid fsgid fs mf o tgt d = NMOk locks mk ->
  exists m s, ns_mounts (mk lk) = ns_mounts st ++ [m] /\ In s (ns_sbs (mk lk))
              /\ mnt_ns m = cx_mount ctx /\ mnt_parent m = Some tgt /\ mnt_mountpoint m = d
              /\ mnt_sb m = sb_id s /\ mnt_root m = sb_root s /\ mnt_flags m = mf.
Proof.
  intros st ctx cred fsuid fsgid fs mf o tgt d locks mk lk. unfold new_mount.
  destruct (fs_owner st ctx fs) as [owner|]; [|intros Hc; discriminate Hc].
  destruct (find_mount (ns_mounts st) tgt) as [t|]; [|intros Hc; discriminate Hc].
  destruct (negb (cap_capable (ns_userns st) cred owner CAP_SYS_ADMIN)); [intros Hc; discriminate Hc|].
  destruct (match revealing_locks st ctx o fs (mf_ro mf) with None => [false] | Some l => l end)
    as [|l0 ls]; [intros Hc; discriminate Hc|].
  destruct (negb (Pos.eqb (mnt_ns t) (cx_mount ctx))); [intros Hc; discriminate Hc|].
  destruct (dentry_inode st d) as [ti|]; [|intros Hc; discriminate Hc].
  destruct (negb (match ino_kind ti with IDir => true | _ => false end)); [intros Hc; discriminate Hc|].
  destruct (env_mount_max (ns_env st) <? Z.of_nat (ns_mount_count (ns_mounts st) (cx_mount ctx) + 1));
    [intros Hc; discriminate Hc|].
  destruct (is_shared (ns_mounts st) tgt); [intros Hc; discriminate Hc|].
  destruct (new_tree st owner (cx_pidns ctx) fs (mf_ro mf) fsuid fsgid) as [[s ds] ins].
  intros H. injection H as Hl Hmk. subst mk.
  eexists; exists s. cbn [ns_mounts ns_sbs].
  split; [reflexivity|]. split; [apply in_or_app; right; left; reflexivity|].
  repeat split; reflexivity.
Qed.
