(** * LinuxProcessSem.Ns.FsOps — namespace creation and file I/O

    Linux 6.18.44 operations for mkdirat (34), symlinkat (36), write (64)
    and read (63).  The arms work only on the namespace model's own open
    files, except that read also describes a shared eventfd counter. *)

From Stdlib Require Import ZArith List Bool NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Mount Userns Walk Task Files Mountinfo.
Import ListNotations.
Local Open Scope Z_scope.

Definition S_IFDIR : Z := 16384.
Definition S_IFLNK : Z := 40960.
Definition PAGE_SIZE : nat := 4096%nat.


(* =========================================================================
   Shared updates and names
   ========================================================================= *)

Definition with_inodes (st : NsState) (ins : list Inode) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) (ns_netns st) (ns_sbs st)
            (ns_dentries st) ins (ns_files st) (ns_env st).

Definition set_inode_bytes (st : NsState) (i : positive) (bs : list byte) : NsState :=
  with_inodes st (map (fun ino => if Pos.eqb (ino_id ino) i
                              then mkInode (ino_id ino) (ino_kind ino) (ino_perm ino)
                                           (ino_uid ino) (ino_gid ino) (ino_rdev ino) bs
                                           (ino_empty_dir ino)
                              else ino) (ns_inodes st)).

Definition set_file_kind (st : NsState) (h : N) (k : NsFileKind) : NsState :=
  match lookup_file (ns_files st) h with
  | Some f => set_file st h (mkNsFile k (nf_flags f) (nf_cred f))
  | None => st
  end.

Definition bytes_z (bs : list byte) : list Z := map bv_unsigned bs.
Definition name_sys : list byte := ascii [115; 121; 115].
Definition name_user : list byte := ascii [117; 115; 101; 114].
Definition name_max : list byte := ascii [109; 97; 120; 95].
Definition name_max_user_namespaces : list byte :=
  ascii [109; 97; 120; 95; 117; 115; 101; 114; 95; 110; 97; 109; 101; 115; 112; 97; 99; 101; 115].

Fixpoint bytes_prefixb (pre xs : list byte) : bool :=
  match pre, xs with
  | [], _ => true
  | p :: ps, x :: xs' => Z.eqb (bv_unsigned p) (bv_unsigned x) && bytes_prefixb ps xs'
  | _ :: _, [] => false
  end.

Fixpoint dentry_names_fuel (fuel : nat) (st : NsState) (d : positive) : option (list (list byte)) :=
  match fuel with
  | O => None
  | S f =>
      match find_dentry st d with
      | None => None
      | Some x =>
          match d_parent x with
          | None => Some []
          | Some p => option_map (fun ns => ns ++ [d_name x]) (dentry_names_fuel f st p)
          end
      end
  end.

Definition dentry_names (st : NsState) (d : positive) : option (list (list byte)) :=
  dentry_names_fuel (S (length (ns_dentries st))) st d.

(** A listed /proc/sys/user/max_* file, named from that procfs root. *)
Definition user_sys_name (st : NsState) (l : Loc) : option (list byte) :=
  match l with
  | LDentry _ d =>
      match loc_mnt_sb st l, dentry_names st d with
      | Some (_, sb), Some [a; b; n] =>
          match sb_kind sb with
          | SbProc _ => if bytes_eqb a name_sys && bytes_eqb b name_user && bytes_prefixb name_max n
                        then Some n else None
          | _ => None
          end
      | _, _ => None
      end
  | _ => None
  end.

Definition map_kind_at (l : Loc) : option MapKind :=
  match l with
  | LProcTask _ _ [n] =>
      if bytes_eqb n proc_uid_map_name then Some UidMap
      else if bytes_eqb n proc_gid_map_name then Some GidMap else None
  | _ => None
  end.

Definition setgroups_at (l : Loc) : bool :=
  match l with LProcTask _ _ [n] => bytes_eqb n proc_setgroups_name | _ => false end.

Definition regular_tmpfs (st : NsState) (l : Loc) : option Inode :=
  match l, loc_mnt_sb st l with
  | LDentry _ d, Some (_, sb) =>
      match sb_kind sb, dentry_inode st d with
      | SbTmpfs, Some ino => match ino_kind ino with IReg => Some ino | _ => None end
      | _, _ => None
      end
  | _, _ => None
  end.

Definition file_can_read (f : NsFile) : bool :=
  let a := Z.land (nf_flags f) O_ACCMODE in Z.eqb a 0 || Z.eqb a 2.

Definition file_can_write (f : NsFile) : bool :=
  let a := Z.land (nf_flags f) O_ACCMODE in Z.eqb a 1 || Z.eqb a 2.

(* =========================================================================
   mkdirat and symlinkat
   ========================================================================= *)

Inductive CreatedKind := CDir | CLink (target : list byte).

(** [may_create], [vfs_mkdir] and [vfs_symlink] first refuse unsupported
    directory operations on procfs and devpts, then create a tmpfs inode.
    Linux 6.18.44: fs/namei.c [may_create], [vfs_prepare_mode], [vfs_mkdir],
    [vfs_symlink]; mm/shmem.c [shmem_mkdir], [shmem_symlink]; fs/inode.c
    [inode_init_owner].  A host directory declines. *)
Definition create_tmpfs (m : Model) (ctx : NsCtx) (st : NsState) (cr : WalkCreds)
    (p : Loc) (name : list byte) (mode : Z) (ck : CreatedKind) : OpenRes :=
  match loc_mnt_sb st p with
  | Some (mt, sb) =>
      match sb_kind sb with
      | SbProc _ | SbDevpts => ORErr EPERM
      | SbHost => OROver
      | SbTmpfs =>
          match p with
          | LProcTask _ _ _ => OROver
          | LDentry mn d =>
              match find_dentry st d, dentry_inode st d with
              | Some dx, Some parent =>
                  let attr := mkObj (ino_kind parent) (ino_perm parent) (ino_uid parent) (ino_gid parent)
                                    None (Zpos (d_sb dx)) in
                  let denied :=
                    if mf_ro (mnt_flags mt) || sb_rdonly sb then Some EROFS
                    else if negb (fsuidgid_mapped st (sb_owner sb) cr) then Some EOVERFLOW
                    else inode_permission st ctx cr (task_eff ctx) p sb attr (MAY_WRITE + MAY_EXEC) in
                  if Nat.ltb NAME_MAX (length name) then ORErr ENAMETOOLONG
                  else match denied with
                       | Some e => ORErr e
                       | None =>
                           let setgid := has (ino_perm parent) S_ISGID in
                           let perm :=
                             match ck with
                             | CDir => Z.land (Z.land mode (Z.lnot (cx_umask ctx))) (511 + S_ISVTX)
                             | CLink _ => 511
                             end in
                           let perm' := match ck with
                                        | CDir => if setgid then Z.lor perm S_ISGID else perm
                                        | CLink _ => perm
                                        end in
                           let gid := if setgid then ino_gid parent else wc_fsgid cr in
                           let ni := Pos.succ (max_inode_id st) in
                           let nd := Pos.succ (max_dentry_id st) in
                           let kind := match ck with CDir => IDir | CLink _ => ILnk end in
                           let data := match ck with CDir => [] | CLink t => t end in
                           let st' := with_tree st
                                      (ns_dentries st ++ [mkDentry nd (d_sb dx) (Some d) name ni])
                                      (ns_inodes st ++ [mkInode ni kind perm' (wc_fsuid cr) gid 0 data false]) in
                           OROk st' (NfDir (LDentry mn nd) 0)
                       end
              | _, _ => OROver
              end
          end
      end
  | None => OROver
  end.

(** [filename_create] performs the parent walk, gives a non-normal last
    component EEXIST, preserves a positive lookup's EEXIST ahead of its
    deferred read-only error, and gives ENOENT for a missing trailing name.
    Linux 6.18.44: fs/namei.c [filename_create], [lookup_one_qstr_excl]. *)
Definition create_at (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (dfd pathp : word) (mode : Z) (ck : CreatedKind) (reads : list (word * nat)) : ext_outcome :=
  match path_arg i pathp with
  | PFault => err reads EFAULT m ctx st
  | PTooLong => err reads ENAMETOOLONG m ctx st
  | POk [] => err reads ENOENT m ctx st
  | POk p =>
      match walk_parent_from m ctx st (walk_creds m) dfd p (mkWalkFlags false false false false false) with
      | ((WErr e, _, _), _) => err reads e m ctx st
      | ((WOver, _, _), _) => EUnmodeled
      | ((WOk parent, name, last), _) =>
          match last with
          | LastNorm =>
              match child_exists st parent name with
              | Some true => err reads EEXIST m ctx st
              | Some false =>
                  if path_trailing_slash p then err reads ENOENT m ctx st
                  else match create_tmpfs m ctx st (walk_creds m) parent name mode ck with
                       | ORErr e => err reads e m ctx st
                       | OROver => EUnmodeled
                       | OROk st' _ => ans reads (Z_to_bv 64 0) [] m ctx st'
                       end
              | None =>
                  match create_tmpfs m ctx st (walk_creds m) parent name mode ck with
                  | ORErr e => err reads e m ctx st
                  | _ => EUnmodeled
                  end
              end
          | _ => err reads EEXIST m ctx st
          end
      end
  end.

(** [mkdirat] (34): [do_mkdirat], [filename_create], [vfs_mkdir] and
    [vfs_prepare_mode] in fs/namei.c, then [shmem_mkdir] in mm/shmem.c.
    Kind: exact on tmpfs; host creation declines; ENOSPC and ENOMEM are
    environment outcomes in [fsops_injected]. *)
Definition mkdirat_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  create_at i m ctx st (in_arg i 0) (in_arg i 1) (bv_unsigned (in_arg i 2)) CDir
            (path_reads i (in_arg i 1)).

(** [symlinkat] (36): [do_symlinkat], [filename_create] and [vfs_symlink]
    in fs/namei.c, then [shmem_symlink] in mm/shmem.c.  The target is read
    before the destination name.  Kind: exact on tmpfs; host creation
    declines; ENOSPC and ENOMEM are environment outcomes. *)
Definition symlinkat_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let oldp := in_arg i 0 in
  let reads := path_reads i oldp ++ path_reads i (in_arg i 2) in
  match path_arg i oldp with
  | PFault => err reads EFAULT m ctx st
  | PTooLong => err reads ENAMETOOLONG m ctx st
  | POk [] => err reads ENOENT m ctx st
  | POk target =>
      if Nat.ltb PAGE_SIZE (length target) then err reads ENAMETOOLONG m ctx st
      else create_at i m ctx st (in_arg i 1) (in_arg i 2) 0 (CLink target) reads
  end.

Definition create_injected (core : ext_outcome) (m : Model) (ctx : NsCtx) (st : NsState) (e : Z)
    : option ext_outcome :=
  match core with EOk _ _ _ _ _ => Some (ns_errno e m ctx st) | EUnmodeled => None end.

Definition mkdirat_arm : NsArm := fun i m ctx st o =>
  o = mkdirat_fn i m ctx st
  \/ create_injected (mkdirat_fn i m ctx st) m ctx st ENOSPC = Some o
  \/ create_injected (mkdirat_fn i m ctx st) m ctx st ENOMEM = Some o.

Definition symlinkat_arm : NsArm := fun i m ctx st o =>
  o = symlinkat_fn i m ctx st
  \/ create_injected (symlinkat_fn i m ctx st) m ctx st ENOSPC = Some o
  \/ create_injected (symlinkat_fn i m ctx st) m ctx st ENOMEM = Some o.

(* =========================================================================
   Procfs text
   ========================================================================= *)

Definition space : byte := Z_to_bv 8 32.
Definition newline : byte := Z_to_bv 8 10.

Definition left_pad (n : nat) (bs : list byte) : list byte :=
  repeat space (n - length bs) ++ bs.

Definition shown_lower (us : list UserNs) (bound : positive) (opener : IdCred) (lower : Z) : Z :=
  let shown := if Pos.eqb (ic_ns opener) bound
               then match find_userns us bound with
                    | Some u => match uns_parent u with Some p => p | None => bound end
                    | None => bound
                    end
               else ic_ns opener in
  match find_userns us shown with
  | Some u => match uns_parent u with
              | None => lower
              | Some _ => match uns_uid_map u with Some es => match map_up es lower with
                                                   Some x => x | None => 65534 end
                                                   | None => 65534 end
              end
  | None => 65534
  end.

Definition map_line (us : list UserNs) (bound : positive) (opener : IdCred) (e : IdExtent) : list byte :=
  left_pad 10 (decimal_bytes (ext_first e)) ++ [space]
  ++ left_pad 10 (decimal_bytes (shown_lower us bound opener (ext_lower e))) ++ [space]
  ++ left_pad 10 (decimal_bytes (ext_count e)) ++ [newline].

Definition map_text (us : list UserNs) (bound : positive) (opener : IdCred) (k : MapKind) : option (list byte) :=
  match find_userns us bound with
  | None => None
  | Some u => match the_map k u with
              | Some es => Some (flat_map (map_line us bound opener) es)
              | None => Some []
              end
  end.

Definition setgroups_text (us : list UserNs) (bound : positive) : option (list byte) :=
  match find_userns us bound with
  | Some u => Some (if uns_setgroups_allowed u then ascii [97; 108; 108; 111; 119; 10]
                    else ascii [100; 101; 110; 121; 10])
  | None => None
  end.

Definition user_sys_text (us : list UserNs) (bound : positive) (name : list byte) : option (list byte) :=
  if bytes_eqb name name_max_user_namespaces
  then match find_userns us bound with Some u => Some (decimal_bytes (uns_max_userns u) ++ [newline]) | None => None end
  else None.

Definition user_file_text (st : NsState) (f : NsFile) : option (list byte * positive * Z) :=
  match nf_kind f with
  | NfUserNsFile l bound off =>
      match map_kind_at l with
      | Some k => option_map (fun bs => (bs, bound, off)) (map_text (ns_userns st) bound (nf_cred f) k)
      | None => if setgroups_at l
                then option_map (fun bs => (bs, bound, off)) (setgroups_text (ns_userns st) bound)
                else match user_sys_name st l with
                     | Some name => option_map (fun bs => (bs, bound, off))
                                                (user_sys_text (ns_userns st) bound name)
                     | None => None
                     end
      end
  | _ => None
  end.

(* =========================================================================
   read
   ========================================================================= *)

(** [read_delivery] models [copy_to_user] after a deterministic file or
    procfs read.  Linux 6.18.44: fs/read_write.c [ksys_read], [vfs_read],
    [rw_verify_area], and mm/shmem.c [shmem_file_read_iter]. *)
Definition read_delivery (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (h : N) (next : NsFileKind) (bs : list byte) : ext_outcome :=
  let buf := in_arg i 1 in
  match read_bytes_map (in_wmem i) buf (len_word bs) with
  | Some _ => ans [] (len_word bs) [(buf, bs)] m ctx (set_file_kind st h next)
  | None => match bs with
            | [] => ans [] (Z_to_bv 64 0) [] m ctx (set_file_kind st h next)
            | _ :: _ => match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
                        | None => ns_errno EFAULT m ctx st
                        | Some _ => EUnmodeled
                        end
            end
  end.

(** [read] (63) on an [ONsFile].  Regular tmpfs and host files use their
    inode bytes, while uid_map, gid_map, setgroups and /proc/sys/user use
    their kernel renderings.  Linux 6.18.44: fs/read_write.c [ksys_read],
    [vfs_read], [rw_verify_area]; mm/shmem.c [shmem_file_read_iter];
    kernel/user_namespace.c [proc_uid_map_show], [uid_m_start],
    [proc_setgroups_show]; kernel/sysctl.c [proc_doulongvec_minmax]; and
    fs/seq_file.c [seq_read_iter].  Kind: exact for modeled files. *)
Definition read_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (h : N) (f : NsFile) : ext_outcome :=
  let count := in_arg i 2 in
  if negb (file_can_read f) then ns_errno EBADF m ctx st
  else if negb (access_okb (in_arg i 1) (bv_unsigned count)) then ns_errno EFAULT m ctx st
  else match nf_kind f with
       | NfPath _ => ns_errno EBADF m ctx st
       | NfDir _ _ => ns_errno EISDIR m ctx st
       | NfFile l off =>
           match l with
           | LDentry _ d =>
               match dentry_inode st d with
               | Some ino => match ino_kind ino with
                             | IReg =>
                                 let bs := file_read (ino_bytes ino) (Z_to_bv 64 off)
                                                     (Z_to_bv 64 (rw_count_clamp count)) in
                                 read_delivery i m ctx st h (NfFile l (off + Z.of_nat (length bs))) bs
                             | _ => EUnmodeled
                             end
               | None => EUnmodeled
               end
           | _ => EUnmodeled
           end
       | NfUserNsFile l bound off =>
           match user_file_text st f with
           | Some (text, _, _) =>
               let bs := file_read text (Z_to_bv 64 off) (Z_to_bv 64 (rw_count_clamp count)) in
               read_delivery i m ctx st h (NfUserNsFile l bound (off + Z.of_nat (length bs))) bs
           | None => EUnmodeled
           end
       | _ => EUnmodeled
       end.

(** [eventfd_read] (fs/eventfd.c): a shared counter cannot be represented
    in this task's state.  The arm therefore admits each nonzero counter
    value Linux can return, or EAGAIN for an O_NONBLOCK eventfd.  Kind: over. *)
Definition eventfd_read_arm (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (flags : word) (o : ext_outcome) : Prop :=
  let count := bv_unsigned (in_arg i 2) in
  if count <? 8 then o = ns_errno EINVAL m ctx st
  else match put_ok i (in_arg i 1) 8 with
       | PutFault => o = ns_errno EFAULT m ctx st
       | PutPartial => o = EUnmodeled
       | PutOk =>
           (exists v, 1 <= v /\ (has (bv_unsigned flags) EFD_SEMAPHORE -> v = 1)
                    /\ o = ans [] (Z_to_bv 64 8) [(in_arg i 1, Z_to_le_bytes 8 v)] m ctx st)
           \/ (has (bv_unsigned flags) O_NONBLOCK = true /\ o = ns_errno EAGAIN m ctx st)
       end.

(** [proc_mounts_read] and [show_mountinfo] (fs/proc_namespace.c): the
    mount namespace and root are captured by the open.  The identifiers
    and file-system display fields are environment values.  Kind: over. *)
Definition mountinfo_read_arm (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (h : N) (f : NsFile) (l : Loc) (ns : positive) (root : positive * positive) (off : Z)
    (o : ext_outcome) : Prop :=
  if negb (file_can_read f) then o = ns_errno EBADF m ctx st
  else if negb (access_okb (in_arg i 1) (bv_unsigned (in_arg i 2))) then o = ns_errno EFAULT m ctx st
  else
    (exists E, mi_env_ok E st
       /\ mountinfo_text E st ns (LDentry (fst root) (snd root)) = None
       /\ o = EUnmodeled)
    \/ (exists E text, mi_env_ok E st
          /\ mountinfo_text E st ns (LDentry (fst root) (snd root)) = Some text
          /\ let bs := firstn (Z.to_nat (rw_count_clamp (in_arg i 2))) (skipn (Z.to_nat off) text) in
             o = read_delivery i m ctx st h
                   (NfMountinfo l ns root (off + Z.of_nat (length bs))) bs).

Definition read_arm : NsArm := fun i m ctx st o =>
  let fd := fd_word (in_arg i 0) in
  match eventfd_flags_of m fd with
  | Some flags => eventfd_read_arm i m ctx st flags o
  | None => match ns_file_of m st fd with
            | Some (h, f) =>
                match nf_kind f with
                | NfMountinfo l ns root off => mountinfo_read_arm i m ctx st h f l ns root off o
                | _ => o = read_fn i m ctx st h f
                end
            | None => released i m ctx st o
            end
  end.

(* =========================================================================
   write
   ========================================================================= *)

Inductive WriteBytes := WFault | WBytesOver | WBytes (bs : list byte).

Definition write_bytes (i : SyscallInput) : WriteBytes :=
  let buf := in_arg i 1 in
  let count := in_arg i 2 in
  if negb (access_okb buf (bv_unsigned count)) then WFault
  else match read_bytes_map (in_mem i) buf (Z_to_bv 64 (rw_count_clamp count)) with
       | Some bs => WBytes bs
       | None => WBytesOver
       end.

Definition all_space (bs : list Z) : bool := forallb is_space bs.

(** One nonnegative decimal value in the range of user namespace limits. *)
Definition user_limit_value (bs : list Z) : option Z :=
  match skip_spaces (upto_nul bs) with
  | c :: r =>
      if (48 <=? c) && (c <=? 57)
      then let '(v, tail) := strtoul 0 (c :: r) in
           if all_space tail && (v <=? INT_MAX) then Some v else None
      else None
  | [] => None
  end.

Definition set_user_limit (st : NsState) (bound : positive) (value : Z) : option NsState :=
  match find_userns (ns_userns st) bound with
  | Some u => Some (with_userns st (replace_userns (ns_userns st) (set_max_userns u value)))
  | None => None
  end.

(** [write] (64) on an [ONsFile].  Map and setgroups writes delegate their
    ordered permission checks to [map_write] and [setgroups_write].  A
    /proc/sys/user/max_user_namespaces write follows [proc_sys_call_handler]
    and [proc_doulongvec_minmax].  Linux 6.18.44: fs/read_write.c
    [ksys_write], [vfs_write], [rw_verify_area]; mm/shmem.c
    [shmem_file_write_iter]; kernel/user_namespace.c [proc_uid_map_write],
    [proc_gid_map_write], [proc_setgroups_write]; kernel/sysctl.c
    [proc_doulongvec_minmax], [__do_proc_doulongvec_minmax], [proc_get_long];
    and fs/proc/proc_sysctl.c [proc_sys_call_handler].  Kind: exact on
    tmpfs and the named procfs files; host regular files and other kinds
    decline. *)
Definition write_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (h : N) (f : NsFile) : ext_outcome :=
  if negb (file_can_write f) then ns_errno EBADF m ctx st
  else match write_bytes i with
       | WFault => ns_errno EFAULT m ctx st
       | WBytesOver => EUnmodeled
       | WBytes bs =>
           let n := Z.of_nat (length bs) in
           match nf_kind f with
           | NfPath _ => ns_errno EBADF m ctx st
           | NfDir _ _ => ns_errno EISDIR m ctx st
           | NfFile l off =>
               match regular_tmpfs st l with
               | Some ino =>
                   let start := if has (nf_flags f) O_APPEND then Z.of_nat (length (ino_bytes ino)) else off in
                   let st' := set_inode_bytes st (ino_id ino)
                                     (file_write (ino_bytes ino) (Z_to_bv 64 start) bs) in
                   ans [] (Z_to_bv 64 n) [] m ctx (set_file_kind st' h (NfFile l (start + n)))
               | None => EUnmodeled
               end
           | NfUserNsFile l bound off =>
               match map_kind_at l with
               | Some k =>
                   match map_write (ns_userns st) bound k (nf_cred f) (task_cred m ctx) off (bytes_z bs) with
                   | NsErr e => ns_errno e m ctx st
                   | NsOk us =>
                       ans [] (Z_to_bv 64 n) [] m ctx
                           (set_file_kind (with_userns st us) h (NfUserNsFile l bound (off + n)))
                   end
               | None =>
                   if setgroups_at l
                   then match setgroups_write (ns_userns st) bound off (bytes_z bs) with
                        | NsErr e => ns_errno e m ctx st
                        | NsOk us => ans [] (Z_to_bv 64 n) [] m ctx
                                      (set_file_kind (with_userns st us) h (NfUserNsFile l bound (off + n)))
                        end
                   else match user_sys_name st l with
                        | Some name =>
                            if negb (bytes_eqb name name_max_user_namespaces) then EUnmodeled
                            else if negb (Z.eqb off 0) then
                                   ans [] (Z_to_bv 64 n) [] m ctx
                                       (set_file_kind st h (NfUserNsFile l bound (off + n)))
                            else match user_limit_value (bytes_z bs), set_user_limit st bound 0 with
                                 | Some value, Some _ =>
                                     match set_user_limit st bound value with
                                     | Some st' => ans [] (Z_to_bv 64 n) [] m ctx
                                                       (set_file_kind st' h (NfUserNsFile l bound (off + n)))
                                     | None => EUnmodeled
                                     end
                                 | _, _ => ns_errno EINVAL m ctx st
                                 end
                        | None => EUnmodeled
                        end
               end
           | _ => EUnmodeled
           end
       end.

Definition write_arm : NsArm := fun i m ctx st o =>
  match ns_file_of m st (fd_word (in_arg i 0)) with
  | Some (h, f) => o = write_fn i m ctx st h f
  | None => released i m ctx st o
  end.

(* =========================================================================
   Exports
   ========================================================================= *)

Definition fsops_arms : list (Z * NsArm) :=
  [(34, mkdirat_arm); (36, symlinkat_arm); (63, read_arm); (64, write_arm)].

(** ENOSPC and ENOMEM are allocation and filesystem-space outcomes after a
    tmpfs create reaches its file-system operation. *)
Definition fsops_injected : list NsInjected :=
  [mkNsInjected 34 [(fun e => e =? ENOSPC, FamFs); (fun e => e =? ENOMEM, FamAlloc)];
   mkNsInjected 36 [(fun e => e =? ENOSPC, FamFs); (fun e => e =? ENOMEM, FamAlloc)]].
