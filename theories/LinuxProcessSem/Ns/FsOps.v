(** * LinuxProcessSem.Ns.FsOps — namespace creation and file I/O

    Linux 6.18.44 operations for mkdirat (34), unlinkat (35), symlinkat
    (36), fchmod (52), write (64) and read (63).  The arms work only on the
    namespace model's own open files and tmpfs directories, except that
    read also describes a shared eventfd counter. *)

From Stdlib Require Import ZArith List Bool NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Mount Userns Walk Task Files Mountinfo.
Import ListNotations.
Local Open Scope Z_scope.

Definition S_IFDIR : Z := 16384.
Definition S_IFLNK : Z := 40960.
Definition PAGE_SIZE : nat := 4096%nat.
Definition CAP_FOWNER : Z := 3.
Definition AT_REMOVEDIR : Z := 512.


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
    and file-system display fields are the environment's, one value per
    kernel object for the whole run ([Tables.env_mountinfo]), so two reads
    of the same open file see one text when no mount changed between
    them.  Kind: exact given those values. *)
Definition mountinfo_read_arm (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (h : N) (f : NsFile) (l : Loc) (ns : positive) (root : positive * positive) (off : Z)
    (o : ext_outcome) : Prop :=
  if negb (file_can_read f) then o = ns_errno EBADF m ctx st
  else if negb (access_okb (in_arg i 1) (bv_unsigned (in_arg i 2))) then o = ns_errno EFAULT m ctx st
  else
    match mountinfo_text (env_mountinfo (ns_env st)) st ns (LDentry (fst root) (snd root)) with
    | None => o = EUnmodeled
    | Some text =>
        let bs := firstn (Z.to_nat (rw_count_clamp (in_arg i 2))) (skipn (Z.to_nat off) text) in
        o = read_delivery i m ctx st h (NfMountinfo l ns root (off + Z.of_nat (length bs))) bs
    end.

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

(** A descriptor the released model owns: neither one of the namespace
    model's open files ([ns_file_of]) nor an eventfd, whose counter other
    processes share and which [read_arm] answers with every value Linux
    can return ([eventfd_read_arm]).  A number that is not open is one too:
    the released model answers EBADF. *)
Definition released_owned (m : Model) (st : NsState) (fd : word) : Prop :=
  ns_file_of m st fd = None /\ eventfd_flags_of m fd = None.

(** A READ ON A DESCRIPTOR THE RELEASED MODEL OWNS HAS EXACTLY THE RELEASED
    ANSWERS, for every input and in every world: the released world, or one
    with a mount tree where released descriptors and the namespace model's
    files coexist ([Ext.ext_coherent] gives it only in the released
    world). *)
Theorem read_arm_released : forall i m ctx st o,
  released_owned m st (fd_word (in_arg i 0)) ->
  (read_arm i m ctx st o <-> released i m ctx st o).
Proof.
  intros i m ctx st o [Hns Hev]. unfold read_arm. cbv zeta. rewrite Hev, Hns. reflexivity.
Qed.

(** The same for write, which answers an eventfd as the released model
    does: only the namespace model's own files are not released. *)
Theorem write_arm_released : forall i m ctx st o,
  ns_file_of m st (fd_word (in_arg i 0)) = None ->
  (write_arm i m ctx st o <-> released i m ctx st o).
Proof. intros i m ctx st o Hns. unfold write_arm. rewrite Hns. reflexivity. Qed.

(* =========================================================================
   fchmod and unlinkat
   ========================================================================= *)

(** A security module's refusal ([security_path_chmod],
    [security_inode_setattr], [security_path_unlink],
    [security_inode_unlink]): any errno. *)
Definition lsm_errno (e : Z) : bool := (1 <=? e) && (e <=? 4095).

(** INVALID_UID and INVALID_GID ((uid_t) -1, include/linux/uidgid.h): the
    id no namespace maps, which [vfsuid_valid] refuses. *)
Definition kid_invalid (k : Z) : bool := Z.eqb k 4294967295.

(** [inode_owner_or_capable] (fs/inode.c): the fsuid owns the inode, or the
    task has CAP_FOWNER over it ([capable_wrt_inode_uidgid]). *)
Definition owner_or_capable (st : NsState) (ctx : NsCtx) (cr : WalkCreds) (a : ObjAttr) : bool :=
  Z.eqb (wc_fsuid cr) (oa_uid a) || capable_over st ctx (task_eff ctx) a CAP_FOWNER.

(** [in_group_or_capable] (fs/inode.c): the fsgid or a supplementary group
    is the inode's group, or the task has CAP_FSETID over it. *)
Definition group_or_capable (st : NsState) (ctx : NsCtx) (cr : WalkCreds) (a : ObjAttr) : bool :=
  in_group cr (oa_gid a) || capable_over st ctx (task_eff ctx) a CAP_FSETID.

Definition set_inode_perm (st : NsState) (i : positive) (perm : Z) : NsState :=
  with_inodes st (map (fun ino => if Pos.eqb (ino_id ino) i
                              then mkInode (ino_id ino) (ino_kind ino) perm
                                           (ino_uid ino) (ino_gid ino) (ino_rdev ino) (ino_bytes ino)
                                           (ino_empty_dir ino)
                              else ino) (ns_inodes st)).

(** [fchmod] (52): [SYSCALL_DEFINE2(fchmod)], [vfs_fchmod], [chmod_common]
    (fs/open.c:631-678); [notify_change], [may_setattr], [setattr_prepare],
    [setattr_copy] (fs/attr.c); [shmem_setattr] (mm/shmem.c:1298);
    [inode_owner_or_capable], [in_group_or_capable] (fs/inode.c).  In
    kernel order: an O_PATH file, EBADF ([fdget] skips FMODE_PATH); a
    read-only mount or superblock, EROFS ([mnt_want_write]); an inode with
    an invalid owner or group, EOVERFLOW ([notify_change]); a fsuid that
    does not own the inode, with no CAP_FOWNER over it, EPERM
    ([setattr_prepare]); else the new mode [mode & 07777], less S_ISGID
    when the inode's group is not the fsgid or a supplementary group and
    the task has no CAP_FSETID over it.  For a tmpfs file or directory
    only: the tables hold no immutable or append-only inode, no seal, no
    ACL and no lease.  A procfs, devpts, host or anonymous file declines.
    The security module's refusals come after EROFS ([fsops_injected]).
    Kind: exact. *)
Definition fchmod_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) (f : NsFile)
    : ext_outcome :=
  let mode := Z.land (bv_unsigned (in_arg i 1)) S_IALLUGO in
  match nf_kind f with
  | NfPath _ => ns_errno EBADF m ctx st
  | NfFile l _ | NfDir l _ =>
      match l, loc_mnt_sb st l with
      | LDentry _ d, Some (mt, sb) =>
          match sb_kind sb, dentry_inode st d, loc_attr m ctx st l with
          | SbTmpfs, Some ino, Some a =>
              let cr := walk_creds m in
              if mf_ro (mnt_flags mt) || sb_rdonly sb then ns_errno EROFS m ctx st
              else if kid_invalid (ino_uid ino) || kid_invalid (ino_gid ino) then ns_errno EOVERFLOW m ctx st
              else if negb (owner_or_capable st ctx cr a) then ns_errno EPERM m ctx st
              else
                let mode' := if group_or_capable st ctx cr a then mode else Z.land mode (Z.lnot S_ISGID) in
                ns_ret (Z_to_bv 64 0) m ctx (set_inode_perm st (ino_id ino) mode')
          | _, _, _ => EUnmodeled
          end
      | _, _ => EUnmodeled
      end
  | _ => EUnmodeled
  end.

(** [security_path_chmod] runs after [mnt_want_write] (fs/open.c:638-645):
    the answers before it (EBADF, EROFS, a file the arm declines) have no
    security-module alternative. *)
Definition fchmod_hook_reached (m : Model) (ctx : NsCtx) (st : NsState) (f : NsFile) : bool :=
  match nf_kind f with
  | NfFile l _ | NfDir l _ =>
      match l, loc_mnt_sb st l with
      | LDentry _ d, Some (mt, sb) =>
          match sb_kind sb, dentry_inode st d, loc_attr m ctx st l with
          | SbTmpfs, Some _, Some _ => negb (mf_ro (mnt_flags mt) || sb_rdonly sb)
          | _, _, _ => false
          end
      | _, _ => false
      end
  | _ => false
  end.

Definition fchmod_arm : NsArm := fun i m ctx st o =>
  match ns_file_of m st (fd_word (in_arg i 0)) with
  | Some (_, f) =>
      o = fchmod_fn i m ctx st f
      \/ (fchmod_hook_reached m ctx st f = true
          /\ injected_after lsm_errno (fchmod_fn i m ctx st f) m ctx st o)
  | None => released i m ctx st o
  end.

(** [d_mountpoint] (include/linux/dcache.h): some mount, in any mount
    namespace, is mounted on dentry [d]. *)
Definition d_mountpoint (st : NsState) (d : positive) : bool :=
  existsb (fun mt => match mnt_parent mt with
                     | Some _ => Pos.eqb (mnt_mountpoint mt) d
                     | None => false
                     end) (ns_mounts st).

(** [is_local_mountpoint] (fs/mount.h:176; [__is_local_mountpoint],
    fs/namespace.c:844): a mount point, and some mount of the caller's
    mount namespace has [d] as its mount point (a namespace's root mount
    has its own root there). *)
Definition local_mountpoint (st : NsState) (ctx : NsCtx) (d : positive) : bool :=
  d_mountpoint st d
  && existsb (fun mt => Pos.eqb (mnt_ns mt) (cx_mount ctx)
                        && Pos.eqb (match mnt_parent mt with
                                    | Some _ => mnt_mountpoint mt
                                    | None => mnt_root mt
                                    end) d)
             (ns_mounts st).

(** The name of dentry [d] removed ([d_delete], fs/dcache.c): the dentry
    stays, unlinked, for whatever still holds it. *)
Definition set_unlinked (st : NsState) (d : positive) : NsState :=
  with_tree st (map (fun x => if Pos.eqb (d_id x) d
                              then mkDentryRec (d_id x) (d_sb x) (d_parent x) (d_name x) (d_inode x) true
                              else x) (ns_dentries st))
            (ns_inodes st).

(** [do_unlinkat] (fs/namei.c:4705) after the parent walk, for a normal last
    component [name] in directory [parent]; [slash]: the path ends with a
    slash.  In kernel order: a read-only mount or superblock, EROFS
    ([mnt_want_write]); [lookup_one_qstr_excl] (fs/namei.c:1685): a name
    longer than NAME_MAX, ENAMETOOLONG ([simple_lookup], fs/libfs.c); no
    such name, ENOENT; a trailing slash, EISDIR for a directory and
    ENOTDIR otherwise; [may_delete] (fs/namei.c:3255): an invalid owner or
    group, EOVERFLOW; write and search permission on the directory
    ([inode_permission]); a sticky directory, EPERM unless the fsuid owns
    the file or the directory or the task has CAP_FOWNER over the file
    ([__check_sticky], fs/namei.c:3222); a directory, EISDIR; then
    [vfs_unlink] (fs/namei.c:4654): a mount point in the caller's mount
    namespace, EBUSY; [shmem_unlink] (mm/shmem.c:4006), which does not
    fail; [d_delete].  A tmpfs directory only: a procfs, devpts or host
    directory declines, and so does a dentry that only another mount
    namespace mounts on ([detach_mounts] would detach those mounts). *)
Definition unlink_at_parent (m : Model) (ctx : NsCtx) (st : NsState) (reads : list (word * nat))
    (parent : Loc) (name : list byte) (slash : bool) : ext_outcome :=
  match parent, loc_mnt_sb st parent, loc_attr m ctx st parent with
  | LDentry mn d, Some (mt, sb), Some dattr =>
      match sb_kind sb with
      | SbTmpfs =>
          if mf_ro (mnt_flags mt) || sb_rdonly sb then err reads EROFS m ctx st
          else if Nat.ltb NAME_MAX (length name) then err reads ENAMETOOLONG m ctx st
          else match child_dentry st d name with
               | None => err reads ENOENT m ctx st
               | Some x =>
                   match loc_attr m ctx st (LDentry mn (d_id x)) with
                   | None => EUnmodeled
                   | Some va =>
                       let cr := walk_creds m in
                       let isdir := kind_is IDir va in
                       if slash then err reads (if isdir then EISDIR else ENOTDIR) m ctx st
                       else if kid_invalid (oa_uid va) || kid_invalid (oa_gid va)
                       then err reads EOVERFLOW m ctx st
                       else match inode_permission st ctx cr (task_eff ctx) parent sb dattr
                                                   (MAY_WRITE + MAY_EXEC) with
                            | Some e => err reads e m ctx st
                            | None =>
                                if has (oa_perm dattr) S_ISVTX
                                   && negb (Z.eqb (wc_fsuid cr) (oa_uid va) || Z.eqb (wc_fsuid cr) (oa_uid dattr)
                                            || capable_over st ctx (task_eff ctx) va CAP_FOWNER)
                                then err reads EPERM m ctx st
                                else if isdir then err reads EISDIR m ctx st
                                else if local_mountpoint st ctx (d_id x) then err reads EBUSY m ctx st
                                else if d_mountpoint st (d_id x) then EUnmodeled
                                else ans reads (Z_to_bv 64 0) [] m ctx (set_unlinked st (d_id x))
                            end
                   end
               end
      | _ => EUnmodeled
      end
  | _, _, _ => EUnmodeled
  end.

(** [unlinkat] (35): [SYSCALL_DEFINE3(unlinkat)] (fs/namei.c:4775): a flag
    other than AT_REMOVEDIR, EINVAL; AT_REMOVEDIR ([do_rmdir]) declines;
    then [do_unlinkat]: the path ([getname]: EFAULT, ENAMETOOLONG, ENOENT
    for an empty one), the parent walk ([filename_parentat]) and its
    errors, a last component that is "." or ".." or the root, EISDIR, and
    [unlink_at_parent].  The security module's refusals come after the
    lookup ([fsops_injected]).  Kind: exact on tmpfs. *)
Definition unlinkat_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let pathp := in_arg i 1 in
  let flags := s32 (in_arg i 2) in
  if negb (Z.eqb (Z.land flags (Z.lnot AT_REMOVEDIR)) 0) then ns_errno EINVAL m ctx st
  else if has flags AT_REMOVEDIR then EUnmodeled
  else
    let reads := path_reads i pathp in
    match path_arg i pathp with
    | PFault => err reads EFAULT m ctx st
    | PTooLong => err reads ENAMETOOLONG m ctx st
    | POk [] => err reads ENOENT m ctx st
    | POk p =>
        match walk_parent_from m ctx st (walk_creds m) (in_arg i 0) p
                               (mkWalkFlags false false false false false) with
        | ((WErr e, _, _), _) => err reads e m ctx st
        | ((WOver, _, _), _) => EUnmodeled
        | ((WOk parent, name, LastNorm), _) =>
            unlink_at_parent m ctx st reads parent name (path_trailing_slash p)
        | ((WOk _, _, _), _) => err reads EISDIR m ctx st
        end
    end.

(** [security_path_unlink] runs after the lookup found the name and the
    trailing-slash check passed (fs/namei.c:4729-4738): the answers before
    it have no security-module alternative. *)
Definition unlinkat_hook_reached (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : bool :=
  let flags := s32 (in_arg i 2) in
  if negb (Z.eqb (Z.land flags (Z.lnot AT_REMOVEDIR)) 0) || has flags AT_REMOVEDIR then false
  else
    match path_arg i (in_arg i 1) with
    | POk ((_ :: _) as p) =>
        match walk_parent_from m ctx st (walk_creds m) (in_arg i 0) p
                               (mkWalkFlags false false false false false) with
        | ((WOk ((LDentry mn d) as parent), name, LastNorm), _) =>
            match loc_mnt_sb st parent, loc_attr m ctx st parent with
            | Some (mt, sb), Some _ =>
                match sb_kind sb with
                | SbTmpfs =>
                    negb (mf_ro (mnt_flags mt) || sb_rdonly sb) && negb (Nat.ltb NAME_MAX (length name))
                    && match child_dentry st d name with
                       | Some x => match loc_attr m ctx st (LDentry mn (d_id x)) with
                                   | Some _ => negb (path_trailing_slash p)
                                   | None => false
                                   end
                       | None => false
                       end
                | _ => false
                end
            | _, _ => false
            end
        | _ => false
        end
    | _ => false
    end.

Definition unlinkat_arm : NsArm := fun i m ctx st o =>
  o = unlinkat_fn i m ctx st
  \/ (unlinkat_hook_reached i m ctx st = true
      /\ injected_after lsm_errno (unlinkat_fn i m ctx st) m ctx st o).

(* =========================================================================
   Exports
   ========================================================================= *)

Definition fsops_arms : list (Z * NsArm) :=
  [(34, mkdirat_arm); (35, unlinkat_arm); (36, symlinkat_arm); (52, fchmod_arm); (63, read_arm);
   (64, write_arm)].

(** ENOSPC and ENOMEM are allocation and filesystem-space outcomes after a
    tmpfs create reaches its file-system operation; unlinkat and fchmod
    admit a security module's errno. *)
Definition fsops_injected : list NsInjected :=
  [mkNsInjected 34 [(fun e => e =? ENOSPC, FamFs); (fun e => e =? ENOMEM, FamAlloc)];
   mkNsInjected 35 [(lsm_errno, FamCred)];
   mkNsInjected 36 [(fun e => e =? ENOSPC, FamFs); (fun e => e =? ENOMEM, FamAlloc)];
   mkNsInjected 52 [(lsm_errno, FamCred)]].
