(** * LinuxProcessSem.Sys.Fs.Namei — mkdirat (34), unlinkat (35)

    This file answers to Linux [fs/namei.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    "." is a path constant more than one file needs, so it does not
    live in any syscall file: [Uapi.dot_path] defines it.  No arm here
    or in [openat] or [newfstatat] reads it any more: [Fs.resolve]
    answers "." itself, as [Fs.LastDot].

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

    Ported from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** ".." — the parent directory.  Like ".", it is a path the kernel
    answers without consulting any file system: [link_path_walk] types
    the last component, and both [do_unlinkat] and [do_rmdir] branch on
    that type before they look anything up.  Their answers differ, which
    is why the two paths are separate constants here rather than one
    "directory reference" class. *)
Definition dotdot_path : path := [Z_to_bv 8 46; Z_to_bv 8 46].

Definition slash_byte : byte := Z_to_bv 8 47.

(** Pinned equal to the byte [Fs] interprets, so moving either is a
    compile error rather than a silent divergence. *)
Lemma slash_byte_is_path_slash_byte : slash_byte = Fs.path_slash_byte.
Proof. reflexivity. Qed.

(** Does the path contain a component separator? *)
Definition path_has_slash (p : path) : bool :=
  existsb (fun b => bv_eqb b slash_byte) p.

(** Drop the separators a path ENDS with.  [link_path_walk] hashes a
    component, then skips every following "/" and stops if the string
    ends there, so trailing separators never start a component and never
    change which component is the last one (Linux fs/namei.c,
    [link_path_walk], the [if (!*name) goto OK] / skip-slashes / [if
    (unlikely(!*name))] sequence just after the [LAST_NORM] arm).  What
    they DO change is the byte [do_unlinkat] tests as
    [last.name[last.len]], and R22 moved that test into the walk:
    [Fs.resolve] returns it as the third component of its answer, so
    every arm reads one flag off one function.  The two helpers that
    used to compute it here -- [path_strip_trailing_slashes] and
    [path_trailing_slash] -- were the deleted separator gate's, had no
    caller left once the walk returned the flag, and are gone. *)

(** [p] is a DIRECTORY COMPONENT of [q]: [q] is [p] followed by "/" and
    then anything.  The base case is "[p] fully consumed", so the caller
    must not pass the empty path — a stripped path of nothing is the
    LAST_ROOT arm, answered before this is reached. *)
Fixpoint dir_prefixb (p q : path) : bool :=
  match p, q with
  | [], [] => false
  | [], c :: _ => bv_eqb c slash_byte
  | _ :: _, [] => false
  | a :: p', b :: q' => bv_eqb a b && dir_prefixb p' q'
  end.

(** Does any key in [fs] live UNDER [p]?  [dir_prefixb] over every key:
    no arm reads it, and the [Common.FileSim] lemmas that carry it as a
    premise are what keeps it here. *)
Fixpoint tree_under (t : Fs.Tree) (p : path) : bool :=
  match t with
  | [] => false
  | (q, _) :: r => dir_prefixb p q || tree_under r p
  end.

Definition fs_under (fs : Fs) (p : path) : bool := tree_under (Fs.fs_tree fs) p.

(** Does any open DIRECTORY descriptor name the key [k]?  This is
    [rmdir]'s guard and nothing else asks it.

    WHY IT IS A GUARD AND NOT AN ANSWER.  Linux lets you rmdir a
    directory an open descriptor still names: [vfs_rmdir] marks the
    inode S_DEAD, detaches the mounts, and the descriptor survives
    pointing at a directory that is no longer in any namespace, whose
    [getdents64] is -ENOENT ([iterate_dir] tests [IS_DEADDIR],
    fs/readdir.c:105-112, Linux v6.18.46) and whose [openat] children are all
    -ENOENT.  This model has no term for a dead directory — an
    [State.FdDir] names a key, and [State.descriptor_invariant] says that
    key resolves to an [Fs.EDir] — so it declines instead of inventing
    an errno Linux does not return.  That is the maintainer's ruling on
    issue #1011, section 15, question 3, DECLINED. *)
Fixpoint fd_names_dir (fds : list (word * FdEntry)) (k : Fs.path) : bool :=
  match fds with
  | [] => false
  | (_, FdDir q) :: r => path_eqb k q || fd_names_dir r k
  | (_, FdFile _ _) :: r => fd_names_dir r k
  | (_, FdFileW _ _) :: r => fd_names_dir r k
  | (_, FdFileA _ _) :: r => fd_names_dir r k
  | (_, FdFileRW _ _) :: r => fd_names_dir r k
  | (_, FdChannel _) :: r => fd_names_dir r k
  | (_, FdSocket _) :: r => fd_names_dir r k
  | (_, FdPipe _ _) :: r => fd_names_dir r k
  | (_, FdDevNull _ _) :: r => fd_names_dir r k
  | (_, FdUrandom _ _) :: r => fd_names_dir r k
  | (_, FdStream _ _ _) :: r => fd_names_dir r k
  | (_, FdEventfd _) :: r => fd_names_dir r k
  | (_, FdDgram _) :: r => fd_names_dir r k
    (* none of these is a directory descriptor *)
  end.

(** Whether the directory at key [k] is EMPTY is [Fs.fs_dir_empty]: a
    directory is non-empty exactly when some key's parent is it, because
    the image holds every entry under its own absolute key and
    [Fs.wf_fs]'s fourth conjunct says every key's parent is a directory
    in the image. *)

(** Is [c] strictly BELOW the directory [k]?  [rmdir] asks it of the
    working directory, to decline removing a directory the run is
    standing in or under.

    THE ROOT NEEDS ITS OWN ROW, and that is a property of the key
    spelling rather than of the tree.  A canonical key is "/" for the
    root and "/a/b/..." with single separators and no trailing one for
    everything else, so [Fs.Namei.dir_prefixb] — which asks that [k] be
    followed by "/" and then something — answers correctly for every key
    but the root, whose own trailing byte IS the separator.  Every key
    but the root is below the root. *)
Definition key_strictly_under (k c : Fs.path) : bool :=
  if path_eqb k Fs.root then negb (path_eqb c Fs.root)
  else dir_prefixb k c.

(** Is [k] a TOP-LEVEL key, a child of the root?  [rmdir] asks it of the
    folder it would remove, and declines one: SCOPE.md's launch premise
    allows a mount point at every top-level folder and at nothing lower,
    and the image does not say which top-level folder is one.  The root
    is its own parent ([Fs.path_parent_root]) and is not a child of
    itself, so it is left out by name; no [rmdir] row reaches it anyway,
    since "/" is [Fs.LastRoot]. *)
Definition top_level_key (k : Fs.path) : bool :=
  negb (path_eqb k Fs.root) && path_eqb (Fs.path_parent k) Fs.root.

(** unlinkat's injectable failures: environment conditions the model does
    not track, all of them documented for unlink(2) and all reachable on
    a directory entry this model cannot tell apart from an ordinary one
    — kernel memory (ENOMEM, listed first as the canonical witness), the
    parent directory's write and search permission (EACCES, from
    [may_delete]'s [inode_permission]), a sticky, append-only or
    immutable entry (EPERM, from the two clauses just after it), a
    read-only mount (EROFS, from [mnt_want_write], which runs before the
    lookup), and an unmapped victim uid or gid (EOVERFLOW, from
    [may_delete], Linux v6.18.46 fs/namei.c:3267-3270) (Linux
    fs/namei.c, [may_delete] / [vfs_unlink]).
    ENOENT is NOT injectable: entry existence IS tracked.

    -EBUSY IS NOT ADMITTED, because no launch the statements cover gives
    it on a row that answers.  Each source of it on a removal that
    reaches the victim is a mount point or a file system the
    configuration of record does not build: [vfs_unlink]'s
    [is_local_mountpoint] of the victim (fs/namei.c:4669) and
    [vfs_rmdir]'s (4543-4546); [vfs_rmdir]'s
    [S_KERNEL_FILE], which only cachefiles sets
    (fs/cachefiles/namei.c:22-23, and CONFIG_CACHEFILES is not set in
    arch/riscv/configs/defconfig); and [may_delete]'s
    [DCACHE_NFSFS_RENAMED] (3293-3294), NFS's, which
    testing/vm/kernel.fragment leaves out.  [may_delete]'s [IS_ROOT]
    victim (3287-3288) is no source on these paths: only rmdir's
    [isdir] call reaches it, and [do_rmdir] takes its victim from
    [lookup_one_qstr_excl] (4600), which returns a child of the parent
    it is given, from [lookup_dcache] or [d_alloc] (1692-1703), and
    crosses no mount, so the victim is never its own parent.
    SCOPE.md's launch premises leave a mount point at a top-level folder
    only: the tree holds no bind mount, so a file or a link is never
    one, and every mount point is a child of "/", which [rmdir_spec]
    declines.  So no unlink and no rmdir below the top level answers
    it.  [do_rmdir]'s -EBUSY for a name that is nothing but separators
    ([rmdir_nonnorm_errno]'s [Fs.LastRoot], 4590-4592) is a different
    answer, the arm's own and certain, and stays.  This stops being
    true when either premise is dropped. *)
Definition unlinkat_errnos : list Z := [ENOMEM; EACCES; EPERM; EROFS; EOVERFLOW].

(** mkdirat's injectable failures, the same environment conditions one
    rung down: the allocations [filename_create] and the filesystem's
    own [->mkdir] make (ENOMEM), the parent's write and search
    permission (EACCES, from [may_create]'s [inode_permission]), a
    read-only mount (EROFS, from [filename_create]'s [mnt_want_write]),
    a caller whose fsuid or fsgid has no mapping in the
    superblock's user namespace (EOVERFLOW, from
    [may_create]'s [fsuidgid_has_mapping] test, Linux v6.18.46
    fs/namei.c:3315-3316 and include/linux/fs.h:1762-1776, which
    [vfs_mkdir] reaches at 4440-4442; tmpfs can be mounted in another
    user namespace, mm/shmem.c:5380-5388, and the model tracks no
    mount's namespace, as [unlinkat_errnos] does not for [may_delete]'s
    -EOVERFLOW), and no room for the new inode (ENOSPC, from the
    filesystem's [->mkdir], which [vfs_mkdir] calls at 4457, past
    [may_create] and its -EMLINK test at 4454.  On tmpfs, Linux
    v6.18.46: [shmem_mkdir] (mm/shmem.c:3944-3949) creates the folder
    through [shmem_mknod] (:3883), and [__shmem_get_inode] (:3084-3091)
    answers -ENOSPC when [new_inode] fails and when
    [shmem_reserve_inode] finds the inode budget spent (:354-358), the
    budget [shmem_fill_super] gives every tmpfs a user mounts (:5062,
    :5092-5093).  On ramfs, Linux v6.18.46, which keeps no budget:
    [ramfs_mknod] answers -ENOSPC when [ramfs_get_inode] finds no new
    inode (fs/ramfs/inode.c:101-104), and [ramfs_mkdir] passes it on
    (:125-128)) (Linux fs/namei.c, [do_mkdirat] / [filename_create] /
    [may_create] / [vfs_mkdir]).
    Every member is admitted only on the row that creates the folder
    ([mkdirat_body_spec]): [may_create] answers -EEXIST for an existing
    name before its -EOVERFLOW (3311-3312), [vfs_mkdir] reaches
    [->mkdir] only past [may_create], and [filename_create]'s lookup has
    answered -EEXIST earlier still.

    EEXIST IS NOT INJECTABLE: existence is resolution, and the arm
    decides it.  The model tracks neither the inode budget nor kernel
    memory, so -ENOSPC is injected rather than decided, as -ENOMEM is.

    -EPERM IS NOT ADMITTED.  [vfs_mkdir] answers it for a parent whose
    file system has no [->mkdir] (fs/namei.c:4444-4446, Linux v6.18.46),
    as an mqueue folder has none ([mqueue_dir_inode_operations],
    ipc/mqueue.c:1613-1617).  SCOPE.md's launch premise puts every folder
    the walk reaches on tmpfs or ramfs, and both install one
    ([shmem_dir_inode_operations], mm/shmem.c:5281-5289;
    [ramfs_dir_inode_operations], fs/ramfs/inode.c:191-197).  The other
    -EPERM on this path, [inode_permission]'s for an immutable parent
    (fs/namei.c:581-582), needs the attribute, which SCOPE.md's premise
    on the launch file system excludes and no modeled call sets.
    [may_create] has no [IS_APPEND] test; that one is [may_delete]'s at
    3277-3278, so an append-only parent takes a new folder.  This stops
    being true when either premise is dropped. *)
Definition mkdirat_errnos : list Z := [ENOMEM; EACCES; EROFS; EOVERFLOW; ENOSPC].

(** THE REFUSALS THE PATH WALK ITSELF CAN GIVE, ahead of whatever answer
    the walk's outcome leads to.  Linux v6.18.46, fs/namei.c:

    - -EACCES from [may_lookup] (1852-1874), which [link_path_walk]
      calls at the top of its component loop (2466-2469), before it
      hashes the component, on the folder the walk stands on.  So it
      can refuse any pathname that HAS a component, "." and ".."
      included; a pathname that is nothing but separators returns from
      [link_path_walk] at 2455-2458 without reaching the loop, and that
      is [Fs.LastRoot].  The model holds no permission bits (an
      [Fs.EDir] carries no mode and no owner), so which folder refuses
      is not something it can decide.  [may_follow_link]'s -EACCES under
      [fs.protected_symlinks] (1168-1196, reached from [pick_link] at
      1921-1925) needs a followed link, so a component, and is the same
      member.
    - -ENOMEM from the dentry the lookup allocates on a cache miss
      ([lookup_one_qstr_excl]'s [d_alloc], 1701-1703;
      [__lookup_slow]'s [d_alloc_parallel], 1801) and from the third
      nested link body ([nd_alloc_stack], 1881-1886, 1899), each of them
      after [getname_flags] has copied the whole name, so this -ENOMEM
      carries the pathname copy-in.  A pathname that is nothing but
      separators ([Fs.LastRoot]) looks nothing up, and neither does one
      made of nothing but "." and ".." components: [link_path_walk] runs
      only [may_lookup] on each (2466-2469), which allocates nothing in
      the configuration of record (it builds no LSM), [handle_dots]
      steps on dentries the walk already holds, and a "." or ".." LAST
      name is answered before any lookup ([do_unlinkat]'s -EISDIR at
      4720-4722, [do_rmdir]'s switch at 4582-4592, [filename_create]'s
      -EEXIST at 4219-4220).  Both keep the member, for the arms that
      allocate past the walk ([path_openat]'s [alloc_empty_file],
      4124-4126 and fs/file_table.c:258-260, is one).  On an arm that
      allocates nothing there -- [unlinkat(".")], [rmdir("..")],
      [mkdirat("./.")], a [newfstatat] or [readlinkat] of "." -- the
      -ENOMEM is no allocation of Linux's: it is an over-admission this
      list makes on purpose by standing -ENOMEM beside every walk, an
      answer Linux does not give, a priority-2 gap.
    - -ELOOP beside every walk that followed a link ([Fs.wr_followed]):
      a [nosymfollow] mount refuses every follow ([pick_link],
      1927-1929), and the follow count is not reset when the kernel
      repeats a walk after an RCU -ECHILD ([filename_lookup] 2705-2709,
      [__filename_parentat] 2747-2751; [path_init] does not reset
      [total_link_count]), so a chain of fewer than 40 links may still
      reach [reserve_stack]'s limit (1878-1879).  A walk that ends
      OUTSIDE the image admits it too: "/proc/self" is a link
      ([proc_self_get_link], fs/proc/self.c) and an fd entry under it a
      magic link, both followed through [pick_link].
    - -ENAMETOOLONG beside every walk that handed a component over
      [Fs.name_max] to a file system's [->lookup] ([Fs.wr_long]): the
      limit is the file system's ([simple_lookup], fs/libfs.c:71-72, the
      lookup of tmpfs and ramfs), so -ENAMETOOLONG is every supported
      kernel's answer there, and the walk's own answer beside it is a
      priority-2 gap ([Fs.comp_too_long]).

    The -ENOMEM of [getname_flags]' own allocations is not among these.
    It carries the copy-in [getname_flags] had made when it failed,
    none or the first EMBEDDED_NAME_MAX bytes and never the whole name,
    so it stands outside the ledger ([getname_refusals]). *)
Definition walk_errnos (lk : Fs.LastKind) (w : Fs.WalkRes) : list Z :=
  match lk with
  | Fs.LastRoot => [ENOMEM]
  | Fs.LastNorm | Fs.LastDot | Fs.LastDotDot => [ENOMEM; EACCES]
  end
  ++ (if Fs.wr_followed w
         || match Fs.wr_res w with Fs.ROutside => true | _ => false end
      then [ELOOP] else [])
  ++ (if Fs.wr_long w then [ENAMETOOLONG] else []).

(** THE REFUSAL [getname_flags] CAN GIVE AHEAD OF ITS OWN ANSWERS: the
    -ENOMEM of [__getname] (fs/namei.c:146-148, Linux v6.18.46).
    [getname_flags] allocates the name's buffer before it copies a byte.
    The [strncpy_from_user] at 157 is what answers -EFAULT (a negative
    count, 161-165), a count of PATH_MAX on the re-copy a long name
    takes (180-195) is what answers -ENAMETOOLONG (207-211), and the
    empty name's -ENOENT is the test on a count of 0 (167-171, and
    201-206 on the re-copy).  So where the allocation fails, none of the
    three is reached and -ENOMEM is the answer instead, for an
    unreadable, an over-long and an empty pathname alike.
    [getname_flags] is the same function in v6.16.

    Every arm that answers those three reaches [getname_flags] first: a
    plain [getname], which is [getname_flags] with no flags
    (include/linux/fs.h:2944-2947), in [do_sys_openat2] (fs/open.c:1431),
    in [SYSCALL_DEFINE3(unlinkat)] and [SYSCALL_DEFINE3(mkdirat)]
    (fs/namei.c) and in [user_path_at] (fs/namei.c:3211-3219), which
    [do_faccessat] calls; or [getname_flags] under LOOKUP_EMPTY in
    [do_readlinkat] (fs/stat.c:569, :575), which runs [__getname] the
    same way.  The one fetch that can answer without [getname_flags] is
    [newfstatat]'s under AT_EMPTY_PATH ([Stat.statat_getname_runs]), and
    that spec hands these refusals only to the calls that reach it. *)
Definition getname_errnos : list Z := [ENOMEM].

(** EMBEDDED_NAME_MAX (126): the count [getname_flags]' first
    [strncpy_from_user] asks for (157), PATH_MAX less
    [offsetof(struct filename, iname)].  [struct filename]
    (include/linux/fs.h:2842-2848, Linux v6.18.46) holds two pointers,
    an [atomic_t] and a third pointer ahead of [iname], so under the
    riscv64 LP64 ABI [iname] sits at 32 (0, 8, 16, then 24 once the
    [atomic_t] is padded to the pointer's alignment, then 32), as the
    [static_assert] at 2849 allows, and the count is 4096 - 32.  The
    struct and [getname_flags] read the same in v6.16 and v6.17
    (include/linux/fs.h:2821-2827 and 2833-2839 there). *)
Definition embedded_name_max : nat := 4064%nat.

(** Does [getname_flags] take its re-copy path (180)?  Exactly when the
    first copy returned its count: EMBEDDED_NAME_MAX bytes below
    [TASK_SIZE], all readable and none NUL.  [read_cstr_aux] at that
    bound answers [CstrTooLong] on exactly those, with the clamp
    [strncpy_from_user] applies byte for byte ([State.read_cstr_aux]). *)
Definition getname_recopies (mp : word -> option byte) (pathp : word) : bool :=
  match read_cstr_aux mp pathp embedded_name_max with
  | CstrTooLong => true
  | CstrOk _ | CstrFault => false
  end.

(** THE COPY-IN EACH OF [getname_flags]' ALLOCATION FAILURES CARRIES.
    [__getname] fails before the first copy (146-148, before 157): no
    copy-in of [getname_flags]' own, whatever the pathname is, an
    ordinary one included, so its ledger is [lead], what the fetch read
    before it called [getname_flags].  That is [] for a plain [getname]
    and for [do_readlinkat]'s [getname_flags], which read nothing first,
    and the lead byte [(pathp, 1)] for [__getname_maybe_null]
    (fs/namei.c:225-242, Linux v6.18.46), whose [get_user] loads it at
    231 before the [getname_flags] at 236 ([Stat.statat_lead_reads]).
    The [kzalloc] of the re-copy path fails after the first copy and
    before the second (189-193, between 157 and 195): exactly the first
    EMBEDDED_NAME_MAX bytes, on a pathname [getname_recopies], a range
    that holds the lead byte too, so [lead] adds nothing to it.  Neither
    is the whole name every answer past the fetch records: only the
    second copy reads an over-long name to PATH_MAX, or a name that
    faults past EMBEDDED_NAME_MAX to its fault. *)
Definition getname_alloc_reads (lead : list (word * nat))
    (mp : word -> option byte) (pathp : word) : list (list (word * nat)) :=
  lead :: (if getname_recopies mp pathp then [[(pathp, embedded_name_max)]] else []).

(** [s], and BESIDE EVERY ANSWER [s] GIVES, [getname_flags]' -ENOMEM
    ([getname_errnos]) with each copy-in of [getname_alloc_reads] after
    the fetch's [lead] reads, as a bare return that leaves the model as
    it was.  [s] is the arm from the pathname fetch on, its copy-in
    ledger included, so this stands OUTSIDE [record_copyins]: from
    inside, the refusal would claim the whole name read, and
    [State.materialize_model_accesses] charges what is claimed, so a
    page Linux never touched could fault the run where Linux answered
    -ENOMEM and went on.

    As in [walk_refusals], a call [s] declines admits no refusal, and an
    effect [s] gives itself is answered once, with [s]'s model.  Each
    arm applies this once it has reached [getname_flags]: behind every
    test Linux makes before [getname] (a flag word's -EINVAL, readlink's
    count), and in [newfstatat] only where the fetch reaches it
    ([Stat.statat_getname_runs]), with the lead byte as [lead] under
    AT_EMPTY_PATH; every other arm's [lead] is []. *)
Definition getname_refusals (lead : list (word * nat)) (pathp : word)
    (s : Sys SyscallEffect) : Sys SyscallEffect :=
  fun i m o =>
    s i m o
    \/ (~ s i m Unmodeled
        /\ exists reads e,
             In reads (getname_alloc_reads lead (in_mem i) pathp)
             /\ In e getname_errnos
             /\ o = Ok (with_copyins reads (mkEffect (errno_ret e) [] [])) m []
             /\ forall m1 evs1,
                  ~ s i m (Ok (with_copyins reads (mkEffect (errno_ret e) [] []))
                              m1 evs1)).

(** Every outcome of [s] is one of the wrapped arm's. *)
Lemma getname_refusals_intro : forall lead pathp s i m o,
  s i m o -> getname_refusals lead pathp s i m o.
Proof. intros. left. assumption. Qed.

(** The refusals a call admits beside its answer once [getname_flags]
    has copied [pathp]: on a nonempty string, the walk's own
    ([walk_errnos]), walked from the working directory with the end [md]
    the call asks for.  Every other outcome of the fetch is [None]: a
    pathname that faulted or holds no NUL within PATH_MAX never reaches
    the walk, and the empty one, which [getname_flags] refuses or under
    LOOKUP_EMPTY hands on, has no component to look up, so no
    allocation of the walk's runs on it.  [getname_flags]' own -ENOMEM
    is [getname_refusals]'. *)
Definition walk_reached (md : Fs.WalkMode) (i : SyscallInput) (m : Model)
    (pathp : word) : option (list Z) :=
  match read_cstr (in_mem i) pathp with
  | CstrOk p =>
      if path_eqb p [] then None
      else Some (walk_errnos (Fs.path_last_kind p)
                   (Fs.resolve_res md (m_fs m) (m_cwd m) p))
  | CstrTooLong | CstrFault => None
  end.

(** [s], and BESIDE EVERY ANSWER [s] GIVES, each of the walk's refusals
    as a bare return that leaves the model as it was.  [s] is the part
    of an arm that runs once the pathname is in hand: the walk and what
    the arm does with its outcome.  Each arm applies this inside its own
    copy-in ledger, which is right for these refusals alone: each comes
    after [getname_flags] has copied the whole pathname, so it carries
    the copy-in every other answer past [getname] does.
    [getname_flags]' own -ENOMEM fails before that copy is done and
    stands outside the ledger ([getname_refusals]).

    A CALL [s] DECLINES ADMITS NO REFUSAL: the model has said nothing
    about it, so it does not say this either.  The last conjunct keeps
    the refusal to effects [s] does not itself give, so that an errno
    [s] already answers (an arm's own [-ENOMEM] beside a success, say)
    is answered once, with [s]'s model. *)
Definition walk_refusals (md : Fs.WalkMode) (pathp : word) (s : Sys SyscallEffect)
    : Sys SyscallEffect :=
  fun i m o =>
    s i m o
    \/ (~ s i m Unmodeled
        /\ exists es e,
             walk_reached md i m pathp = Some es
             /\ In e es
             /\ o = Ok (mkEffect (errno_ret e) [] []) m []
             /\ forall m1 evs1, ~ s i m (Ok (mkEffect (errno_ret e) [] []) m1 evs1)).

(** Every outcome of [s] is one of the wrapped arm's. *)
Lemma walk_refusals_intro : forall md pathp s i m o,
  s i m o -> walk_refusals md pathp s i m o.
Proof. intros. left. assumption. Qed.

(** The flag words [unlinkat_spec] interprets: 0 and AT_REMOVEDIR, which
    is every word the kernel accepts.  Unlike [modeled_open_flags] this
    is not a modeling choice — a word outside it is the kernel's own
    -EINVAL, not [unmodeled]. *)
Definition modeled_unlink_flags (flags : word) : bool :=
  Z.eqb (bv_unsigned (flag32 flags)) 0
  || Z.eqb (bv_unsigned (flag32 flags)) AT_REMOVEDIR.

(** Which of the two calls this is: [do_rmdir] or [do_unlinkat]. *)
Definition unlink_rmdir (flags : word) : bool :=
  Z.eqb (bv_unsigned (flag32 flags)) AT_REMOVEDIR.

(** THE REFUSALS LINUX REACHES BEFORE IT TESTS THE VICTIM'S TYPE, in the
    order it reaches them (fs/namei.c, Linux v6.18.46):

    - -EROFS from [mnt_want_write], on a read-only mount or superblock.
      [do_rmdir] (4595-4597) and [do_unlinkat] (4724-4726) both call it
      before the lookup;
    - -ENOMEM from the lookup: [lookup_one_qstr_excl] allocates the
      dentry when the cache misses (1701-1703);
    - then [may_delete] (3255-3296), the first thing [vfs_rmdir] (4532)
      and [vfs_unlink] (4658) do: -EOVERFLOW for a victim whose uid or
      gid has no mapping (3267-3270); -EACCES from [inode_permission] on
      the parent for write and search (3274-3276; it can also answer
      -EROFS and -EPERM, both already here); -EPERM for an append-only
      parent (3277-3278); and -EPERM for a sticky parent the caller may
      not delete from, or for an append-only, immutable or swap victim,
      or one with an unmapped id (3280-3283).

    Only then does [may_delete] test the type: -ENOTDIR for a victim
    that is not a directory when AT_REMOVEDIR asked for one (3284-3286),
    and -EISDIR for a directory when it did not (3289-3290).  The model
    tracks none of the mount's flags, the parent's permission, the
    entries' owners or their inode flags, so these five stand BESIDE the
    type answer in [unlinkat_file_spec] and [rmdir_spec], and never
    replace it.

    The members are [unlinkat_errnos]' five, in the order Linux reaches
    them: the -EBUSY of a mount point, which [vfs_unlink] and
    [vfs_rmdir] raise only after [may_delete] has passed, is in neither
    list ([unlinkat_errnos]). *)
Definition unlink_before_type_errnos : list Z :=
  [EROFS; ENOMEM; EOVERFLOW; EACCES; EPERM].

(** The refusals before [lookup_one_qstr_excl] answers (Linux v6.18.46
    fs/namei.c): [mnt_want_write]'s -EROFS, then the dentry the lookup
    allocates on a cache miss, -ENOMEM (1701-1703).  [do_unlinkat] calls
    the two at 4724-4726 and 4729-4730, [do_rmdir] at 4595-4597 and
    4600.  So they stand beside the lookup's own -ENOENT for an absent
    last name (1713-1716) on both calls, and beside [do_unlinkat]'s
    [slashes:] answers (4767-4772), which the jump at 4734-4735 reaches
    before [vfs_unlink], so [may_delete]'s -EOVERFLOW, -EACCES and
    -EPERM do not belong to this list. *)
Definition unlink_before_slashes_errnos : list Z := [EROFS; ENOMEM].

(** THE REMOVAL OF A REGULAR FILE'S NAME, once resolution has found the
    file's inode [i] at the key [k]: either an untracked environment
    failure, or the name dropped from the image ([Fs.fs_unlink_file]).

    LINUX, v6.18.46: [do_unlinkat] (fs/namei.c, 4705-4773) finds the
    dentry and calls [vfs_unlink] (4654-4696), which runs [may_delete]
    and the filesystem's [->unlink] ([shmem_unlink] on tmpfs,
    mm/shmem.c:4006-4030, whose [drop_nlink] at :4019 lowers the
    inode's link count by one), and [d_delete] then only unhashes the
    dentry while open files still hold references to it.  So the
    removal lowers [Fs.fs_ino_nlink] by one -- it is computed from the
    names -- and touches no descriptor: every [struct file] on the inode
    keeps its [f_path] on the unhashed dentry, its [f_pos], its
    [f_mode] and its [f_flags], and [State.FdFile] carries the inode
    number, not the name.

    THE INODE STAYS WHILE SOMETHING HOLDS IT.  Another name keeps it, and
    so does an open descriptor ([State.ino_held]): the inode is freed
    only by the last [iput] ([iput_final], fs/inode.c:1874-1915), and
    on tmpfs and ramfs that last [iput] always evicts ([->drop_inode] is
    [inode_just_drop], mm/shmem.c:5330 and fs/ramfs/inode.c:218, which
    answers 1, fs/inode.c:1858-1861), so it is the references that
    keep the inode: each name's dentry, which the create pinned
    ([dget], mm/shmem.c:3908, fs/ramfs/inode.c:114), and each [struct
    file]'s.  musl's [tmpfile()] (src/stdio/tmpfile.c) creates a
    file with O_RDWR|O_CREAT|O_EXCL and removes its name at once, and
    this is the arm its descriptor then lives on.  A file nothing holds
    any more is not in the file system the exit event carries, as on
    Linux.

    [Fs.wf_fs_unlink_file] says the image this leaves is still a
    namespace: dropping a FILE cannot orphan anything, because no key's
    parent is a file in a well-formed image.  [State.with_fs] drops the
    inode's stat pin exactly when the inode is gone.

    EVERY KEY IS ANSWERED, not only those under one folder: the walk
    names the file the same way wherever it sits, and [vfs_unlink] does
    not care which directory the victim is in. *)
Definition unlink_file_spec (k : Fs.path) (i : Fs.ino) (m : Model)
    : Sys SyscallEffect :=
  alt (e <- errno_from unlinkat_errnos ;; err_ret e)  (* untracked env failure *)
      (set_fs (Fs.fs_unlink_file (m_fs m) k i (ino_held (m_fds m) i)) ;;
       ret_only (Z_to_bv 64 0)).

(** THE REMOVAL OF A NAME THAT IS NOT A FILE'S: a link, which
    [do_unlinkat] (fs/namei.c:4729-4730) removes without following: it
    takes the last name with [lookup_one_qstr_excl] and calls
    [vfs_unlink] on that dentry, so the link goes and what it names stays.
    [Fs.wf_fs_remove_file] says the image is still a namespace. *)
Definition unlink_remove_spec (k : Fs.path) (m : Model) : Sys SyscallEffect :=
  alt (e <- errno_from unlinkat_errnos ;; err_ret e)  (* untracked env failure *)
      (set_fs (fs_remove (m_fs m) k) ;; ret_only (Z_to_bv 64 0)).

(** THE unlinkat(flags = 0) ARM, over resolution.

    THE LAST COMPONENT'S KIND COMES FIRST, and it is one answer for all
    three non-normal kinds.  [do_unlinkat] (fs/namei.c, Linux v6.18.46,
    4720-4722) opens with

        error = -EISDIR;
        if (type != LAST_NORM)
                goto exit2;

    which does not distinguish them, so ".", ".." and a path that is
    nothing but separators are all -EISDIR.  That is decided before any
    lookup, so it preempts every outcome of the walk's last step but not
    the walk's own prefix errors: [filename_parentat] runs first
    (4716-4718) and its failure is what [Fs.RNotDir] and [Fs.RAbsent]
    are.

    THEN THE TRAILING SEPARATOR, and only on the arm where the lookup
    FOUND something.  [do_unlinkat] tests [last.name[last.len]] — the
    byte just past the component — and jumps to its [slashes:] label
    when it is not NUL (4734-4735, 4767-4772):

        if (last.name[last.len])
                goto slashes;
        ...
    slashes:
        if (d_is_dir(dentry))
                error = -EISDIR;
        else
                error = -ENOTDIR;

    So a trailing separator on a regular file is -ENOTDIR and on a
    directory is -EISDIR.  An ABSENT name never gets there:
    [lookup_one_qstr_excl] returns -ENOENT for the negative dentry when
    the caller passed no LOOKUP_CREATE, before the jump.  The parent end
    never follows the last name, so a link there is a non-directory to
    this test ([Fs.WalkParent]).  The jump
    is taken after [mnt_want_write] and the lookup, so their -EROFS and
    -ENOMEM stand beside both answers, as they stand beside the absent
    name's -ENOENT ([unlink_before_slashes_errnos]); [may_delete] never
    runs on either route.

    A DIRECTORY WITHOUT A SEPARATOR IS -EISDIR, from
    [may_delete(..., isdir = 0)]'s [else if (d_is_dir(victim)) return
    -EISDIR] (3289-3290), with [unlink_before_type_errnos] beside it,
    since [may_delete] reaches its own refusals first.

    A DEVICE DECLINES.  Linux unlinks a character device node like any
    other entry, and the model could drop the [Fs.EDev] from the image
    and stay well formed — but what it cannot describe is the DEVICE
    surviving the name: an open [State.FdDevNull] carries no key, so
    after the removal the model has a descriptor on a device that the
    image no longer mentions, and no arm says what that descriptor now
    is.  Removing a device the run may still hold is a state the
    descriptor invariant has nothing to say about, so the arm fails
    closed rather than answering.

    A FILE'S NAME IS REMOVED whether or not a descriptor holds the file
    ([unlink_file_spec]): the descriptor holds the inode, not the name.
    A LINK'S NAME IS REMOVED and its target stays ([unlink_remove_spec]);
    the walk does not follow the last component here, as
    [do_unlinkat] does not. *)
(** THE THREE LAST-COMPONENT SWITCHES, EACH AS A FUNCTION OF THE KIND,
    so that the arm below can run them where Linux runs them: AFTER
    [filename_parentat] and not before it.

    [None] is LAST_NORM, the case every switch falls THROUGH — which is
    what makes these total without inventing an answer for the normal
    component.

    WHY THIS IS A FUNCTION AND NOT THE ARM'S OUTERMOST MATCH.  Each
    [do_*] reads the last component's kind from the parent walk's own
    result, so the walk has already either failed or succeeded by the
    time the switch runs ([do_unlinkat], fs/namei.c:4716-4722, Linux
    v6.18.46):

        error = filename_parentat(dfd, name, lookup_flags, &path, &last, &type);
        if (error)
                goto exit1;              <- the PREFIX's errno wins here
        error = -EISDIR;                 <- and only now the kind
        if (type != LAST_NORM)
                goto exit2;

    An arm that switched on the kind first would answer -EISDIR for
    "a/.." with [a] a regular file, where Linux answers -ENOTDIR from
    the failed parent walk.  So the prefix outcomes -- [Fs.RNotDir],
    [Fs.RAbsent], [Fs.RLoop] and [Fs.ROutside] ("proc" and "sys" at the
    root), which are exactly the shapes [filename_parentat] fails with
    -- are read first, and the kind is read inside the two rows where
    the parent walk SUCCEEDED ([Fs.resolve_parent] turns its end into
    the last name's own lookup). *)
Definition unlink_nonnorm_errno (lk : Fs.LastKind) : option Z :=
  match lk with
  | Fs.LastNorm => None
  | Fs.LastDot | Fs.LastDotDot | Fs.LastRoot => Some EISDIR
  end.

(** [do_rmdir] distinguishes all three where [do_unlinkat] does not
    (fs/namei.c:4583-4593, Linux v6.18.46). *)
Definition rmdir_nonnorm_errno (lk : Fs.LastKind) : option Z :=
  match lk with
  | Fs.LastNorm => None
  | Fs.LastDotDot => Some ENOTEMPTY
  | Fs.LastDot => Some EINVAL
  | Fs.LastRoot => Some EBUSY
  end.

(** [filename_create]'s [if (unlikely(type != LAST_NORM)) goto out;]
    with [error] still -EEXIST from the line above it (fs/namei.c:4203,
    4219-4220, Linux v6.18.46). *)
Definition mkdir_nonnorm_errno (lk : Fs.LastKind) : option Z :=
  match lk with
  | Fs.LastNorm => None
  | Fs.LastDot | Fs.LastDotDot | Fs.LastRoot => Some EEXIST
  end.

Definition unlinkat_file_spec (r : Fs.Resolved) (lk : Fs.LastKind)
    (ts : bool) (m : Model) : Sys SyscallEffect :=
  match r with
  (* [filename_parentat] FAILED: its errno wins, whatever the last kind *)
  | Fs.RNotDir _ => err_ret ENOTDIR
  | Fs.RAbsent _ => err_ret ENOENT
  | Fs.RLoop => err_ret ELOOP                (* the 41st link, fs/namei.c:1878-1879 *)
  | Fs.RParent _ _ => unmodeled              (* [Fs.resolve_parent] maps it away *)
  | Fs.ROutside => unmodeled
  (* the parent walk SUCCEEDED, so the kind switch runs now *)
  | Fs.RMissing _ _ =>
      match unlink_nonnorm_errno lk with
      | Some e => err_ret e
      | None =>
          alt (er <- errno_from unlink_before_slashes_errnos ;; err_ret er)
              (err_ret ENOENT)              (* [lookup_one_qstr_excl]'s -ENOENT *)
      end
  | Fs.RFound k e =>
      match unlink_nonnorm_errno lk with
      | Some er => err_ret er
      | None =>
          match e with
          | EDir =>
              if ts then
                alt (er <- errno_from unlink_before_slashes_errnos ;; err_ret er)
                    (err_ret EISDIR)            (* do_unlinkat's [slashes:] *)
              else
                alt (er <- errno_from unlink_before_type_errnos ;; err_ret er)
                    (err_ret EISDIR)            (* may_delete's -EISDIR *)
          | EDev _ => unmodeled
          | EFile i =>
              if ts then
                alt (er <- errno_from unlink_before_slashes_errnos ;; err_ret er)
                    (err_ret ENOTDIR)           (* do_unlinkat's [slashes:] *)
              else unlink_file_spec k i m
          | ELink _ =>
              if ts then
                alt (er <- errno_from unlink_before_slashes_errnos ;; err_ret er)
                    (err_ret ENOTDIR)           (* [slashes:]: a link is no directory *)
              else unlink_remove_spec k m
          end
      end
  end.

(** THE unlinkat(AT_REMOVEDIR) ARM — rmdir — over resolution.

    [do_rmdir] SWITCHES ON THE LAST COMPONENT'S KIND BEFORE ANY LOOKUP,
    and unlike [do_unlinkat] it distinguishes all three
    (fs/namei.c:4583-4593, Linux v6.18.46):

        switch (type) {
        case LAST_DOTDOT: error = -ENOTEMPTY; goto exit2;
        case LAST_DOT:    error = -EINVAL;    goto exit2;
        case LAST_ROOT:   error = -EBUSY;     goto exit2;
        }

    So "/tmp/../.." is -ENOTEMPTY, "d/." is -EINVAL, and "/" and "//"
    are -EBUSY, each without the directory being looked at.  That is why
    [Fs.resolve] returns the kind: no other arm needs it, and this one
    cannot be written without it.

    THE TRAILING SEPARATOR IS IGNORED: [do_rmdir] reads
    [last] for its name and its type and never looks at the byte past
    it, so "d/" and "d" are one call.

    A NON-DIRECTORY IS -ENOTDIR, from [may_delete(..., isdir = 1)]'s
    [if (!d_is_dir(victim)) return -ENOTDIR] (3284-3286), which is one
    answer for a regular file and for a device alike, with the five
    refusals [may_delete] and its caller reach first beside it
    ([unlink_before_type_errnos]).

    A NON-EMPTY DIRECTORY IS -ENOTEMPTY, which is the filesystem's own
    [->rmdir] (tmpfs's [shmem_rmdir] tests [simple_empty],
    mm/shmem.c:4032-4035) and the one answer here that is a function of
    the image rather than of the victim alone.  [fs_dir_empty] is the
    test.  [vfs_rmdir] reaches [->rmdir] only after [may_delete] and its
    -EBUSY for a mount point (fs/namei.c:4532-4552), so every member of
    [unlinkat_errnos] stands beside it; that -EBUSY is not one of them,
    because below the top level no folder is a mount point
    ([unlinkat_errnos]).

    THE FOUR DECLINES, and each is a state the model has no term for, an
    answer it cannot tell from another, or a decline kept for safety
    rather than an errno it is unsure of.  Linux SUCCEEDS at the second
    and the fourth and leaves something behind:

    - a TOP-LEVEL folder, a child of "/" ([top_level_key]).  SCOPE.md's
      launch premise lets every one be a mount point, as /work, /tmp,
      /dev and a seed root are in the agreement checks' launch, and the
      image does not say which.  On a mount point [vfs_rmdir] answers
      -EBUSY before [->rmdir] ([is_local_mountpoint], 4543-4546, ahead
      of 4552), since [do_rmdir] looks the last name up in its parent
      without following the mount (4600-4607); on the same folder
      unmounted it removes it or answers -ENOTEMPTY.  A list beside the
      answer would not do: -EBUSY is FORCED on a mount point, and the
      forced-only reading of the injected errnos ([Run.injected_table])
      would remove it beside the success.  "/" itself is
      [Fs.LastRoot]'s -EBUSY above, unchanged.
    - the working directory itself.  [vfs_rmdir] marks it S_DEAD
      (4557) and the process keeps standing in a directory that is in
      no namespace.  A name looked up in it is -ENOENT ([__lookup_slow]
      tests [IS_DEADDIR], 1797-1799), but "." still resolves to it and
      ".." to its parent: [walk_component] hands both to [handle_dots]
      (2141-2145, 2096-2131), which tests no dead folder.
      The model's [State.m_cwd] would name a key the image no longer
      holds, which [State.model_fs_wf]'s third conjunct forbids.
    - an ANCESTOR of the working directory.  Linux never removes one:
      every strict ancestor holds the next folder of the chain down to
      the working directory, which the image holds (the decline above
      keeps it there), so it is never empty, and [->rmdir] answers
      -ENOTEMPTY ([simple_rmdir], fs/libfs.c:799-807, with
      [simple_empty], :766-784; [shmem_rmdir], mm/shmem.c:4032-4035),
      as [fs_dir_empty] would too.  The decline is conservative, not
      needed to keep the S_DEAD state out; [key_strictly_under] is the
      test.
    - a directory an open [State.FdDir] names, which [fd_names_dir]
      carries with its own argument.

    No errno is invented for any of them.

    THE PARENT'S LINK COUNT FOLLOWS ([Fs.fs_rmdir]): one lower under the
    counting rule ([drop_nlink(dir)] in [shmem_rmdir] at mm/shmem.c:4038
    and in ramfs's [simple_rmdir] at fs/libfs.c:806), the same under the
    fixed one ([Fs.DirLinks]); a stat of the parent reads it there.

    A LINK AT THE LAST NAME IS -ENOTDIR, as a file is: [do_rmdir] looks
    the last name up without following it and [may_delete(..., isdir =
    1)] refuses any victim that is not a directory (3284-3286). *)
Definition rmdir_spec (r : Fs.Resolved) (lk : Fs.LastKind) (m : Model)
    : Sys SyscallEffect :=
  match r with
  (* [filename_parentat] FAILED: its errno wins, whatever the last kind *)
  | Fs.RNotDir _ => err_ret ENOTDIR
  | Fs.RAbsent _ => err_ret ENOENT
  | Fs.RLoop => err_ret ELOOP
  | Fs.RParent _ _ => unmodeled              (* [Fs.resolve_parent] maps it away *)
  | Fs.ROutside => unmodeled
  (* the parent walk SUCCEEDED, so [do_rmdir]'s switch runs now *)
  | Fs.RMissing _ _ =>
      match rmdir_nonnorm_errno lk with
      | Some e => err_ret e
      | None =>
          alt (er <- errno_from unlink_before_slashes_errnos ;; err_ret er)
              (err_ret ENOENT)              (* [lookup_one_qstr_excl]'s -ENOENT *)
      end
  | Fs.RFound k e =>
      match rmdir_nonnorm_errno lk with
      | Some er => err_ret er
      | None =>
          match e with
          | EFile _ | EDev _ | ELink _ =>
              alt (er <- errno_from unlink_before_type_errnos ;; err_ret er)
                  (err_ret ENOTDIR)             (* may_delete's -ENOTDIR *)
          | EDir =>
              if top_level_key k then unmodeled  (* maybe a mount point *)
              else if path_eqb k (m_cwd m) then unmodeled
              else if key_strictly_under k (m_cwd m) then unmodeled
              else if fd_names_dir (m_fds m) k then unmodeled
              else if negb (fs_dir_empty (m_fs m) k) then
                alt (er <- errno_from unlinkat_errnos ;; err_ret er)
                    (err_ret ENOTEMPTY)         (* the filesystem's [->rmdir] *)
              else
                alt (er <- errno_from unlinkat_errnos ;; err_ret er)
                    (set_fs (Fs.fs_rmdir (m_fs m) k) ;; ret_only (Z_to_bv 64 0))
          end
      end
  end.

(** [unlinkat dirfd path flags]: remove a directory entry.  The two
    calls the flag word selects are different kernel functions with
    different answers, and this arm is the pair of them.

    ORDER, following the kernel's exactly:

    - the flag word first: anything but 0 or AT_REMOVEDIR is -EINVAL,
      before the pathname is fetched.  [SYSCALL_DEFINE3(unlinkat)] is

        if ((flag & ~AT_REMOVEDIR) != 0)
                return -EINVAL;
        if (flag & AT_REMOVEDIR)
                return do_rmdir(dfd, getname(pathname));
        return do_unlinkat(dfd, getname(pathname));

      so [getname] is an argument expression on the two return paths
      only and the -EINVAL genuinely precedes it.  Note AT_EMPTY_PATH
      and AT_SYMLINK_NOFOLLOW are NOT accepted: they are -EINVAL like
      any other bit.
    - then [getname()], with all three of its answers, as [openat_spec]
      has them: -ENAMETOOLONG for no NUL within PATH_MAX, -ENOENT for
      the empty string, and -EFAULT for an unmapped byte;
    - only then the dirfd, resolved in [path_init]: the
      relative-to-a-dirfd modes are not modeled, so any dirfd but
      AT_FDCWD is [unmodeled].

    For an UNREADABLE pathname too: an illegal flag word with a NULL or
    unmapped path is -EINVAL, the pathname never fetched.

    THE WORLD IS THE NAMESPACE, and the three guards the flat map needed
    are gone with it.  A path containing "/" anywhere but at the end was
    [unmodeled] because the model could not walk it; [Fs.resolve] walks
    it.  A name some key lived UNDER was [unmodeled] because the map
    only IMPLIED a directory there; a directory is an [Fs.EDir] and both
    arms answer it.  The "/tmp/<one component>" arm, which answered a
    single shape under a declaration of its own, is gone: "/tmp/x" is an
    ordinary absolute key and the premise it carried is the whole
    image's (see [Fs]'s header).  What is left of the [Uapi.NAME_MAX]
    guard is the walk's admitted -ENAMETOOLONG ([walk_errnos]).

    THE ANSWERS, once the path is in hand, by the last component's type
    (fs/namei.c, Linux v6.18.46, [do_unlinkat] 4705-4773 and [do_rmdir]
    4570-4622), each read only after the parent walk succeeded:

      | last component | type        | flags = 0 | AT_REMOVEDIR |
      | "."            | LAST_DOT    | -EISDIR   | -EINVAL      |
      | ".."           | LAST_DOTDOT | -EISDIR   | -ENOTEMPTY   |
      | none at all    | LAST_ROOT   | -EISDIR   | -EBUSY       |

    and for LAST_NORM, [unlinkat_file_spec] and [rmdir_spec] answer off
    the entry the walk found.

    THE OPEN-FD CASE.  Linux keeps an unlinked file's contents reachable
    through a descriptor already open on it until the last close.  The
    model's file descriptors record the INODE ([State.FdFile] and its
    kin), so the removal of a name changes no descriptor: the inode
    keeps its row while a descriptor holds it ([Fs.fs_unlink_file]), and
    every read and write through the descriptor reaches it there.

    THE WALK'S OWN REFUSALS stand beside every answer the walk leads to
    ([walk_refusals], applied in [unlinkat_spec]): [may_lookup]'s
    -EACCES on every pathname that has a component, and the walk's
    -ENOMEM on every nonempty pathname it is handed.  [getname_flags]'
    own -ENOMEM stands beside every answer from the fetch on, the three
    [getname_flags] gives itself (the empty path, an unreadable pointer,
    an over-long one) included, with the copy-in it had made when its
    allocation failed ([getname_refusals], applied in [unlinkat_spec]
    outside the ledger).

    Two more untracked conditions sit ahead of the answers; which one
    reaches which arm follows the last component's TYPE rather than the
    answer:

    - [complete_walk]'s -ESTALE, on a file system defining
      [d_weak_revalidate]: [path_parentat] runs it after the walk
      (2719-2733), and it returns 0 at once unless ND_JUMPED is still
      set.  [path_init] sets that flag, and on this route the LAST_NORM
      arm of [link_path_walk]'s switch is the only thing that clears it.
    - [mnt_want_write]'s -EROFS, which both [do_unlinkat] and [do_rmdir]
      raise after the type test and before the lookup.

      | arm                    | -EACCES | -ESTALE | -EROFS |
      | LAST_ROOT              | no      | yes     | no     |
      | LAST_DOT, LAST_DOTDOT  | yes     | yes     | no     |
      | LAST_NORM              | yes     | no      | yes    |

    (the -EACCES column is [walk_errnos]).  Past those, the arms differ
    in what ELSE comes before their answer, because they sit at
    different depths.  The type answers of [may_delete] (the
    AT_REMOVEDIR -ENOTDIR and the plain -EISDIR of a directory) admit
    the five refusals it and its caller reach first
    ([unlink_before_type_errnos]).  The trailing-separator answers do
    not come out of [may_delete]: [do_unlinkat] jumps to [slashes:] from
    ABOVE [vfs_unlink], so they admit only -EROFS and the lookup's
    -ENOMEM ([unlink_before_slashes_errnos]), and so do the absent-name
    answers, whose -ENOENT the lookup gives after both.  The -ESTALE
    column is admitted nowhere.  That omission narrows the spec rather
    than widening it. *)
Definition unlinkat_body_spec (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
    match read_cstr (in_mem i) pathp with
    | CstrTooLong => err_ret ENAMETOOLONG        (* no NUL within PATH_MAX *)
    | CstrFault => err_ret EFAULT                (* unmapped byte in the path string *)
    | CstrOk p =>
        if path_eqb p [] then err_ret ENOENT     (* empty pathname: getname's own -ENOENT *)
        else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
        else
          let '(r, lk, ts) := Fs.resolve_parent (m_fs m) (m_cwd m) p in
          if unlink_rmdir flags then rmdir_spec r lk m
          else unlinkat_file_spec r lk ts m
    end.

(** [mkdirat dirfd path mode] (riscv64 nr 34, [SYSCALL_DEFINE3]), which
    is [do_mkdirat(dfd, getname(pathname), mode)].  NEW IN R22: before
    the namespace there was no value a created directory could BE, so
    the call was outside the modeled surface entirely.

    THE MODE IS IGNORED, and that is a decline about permissions rather
    than about the directory.  [Fs.EDir] carries no mode, no owner and
    no timestamps, so a directory this creates is indistinguishable from
    one the image shipped.  [faccessat]'s W_OK, R_OK and X_OK, which
    would read the mode, are [unmodeled].  [newfstatat] is not: it
    delivers the folder's [st_mode], and its first stat of a folder
    ([Stat.fstat_dir_spec]) asserts the type and the link count but
    chooses the permission bits, which later stats then hold.  So after
    [mkdirat(AT_FDCWD, "d", 0)] the model admits a stat of "d" that
    reports 0777, which no supported kernel gives.  [vfs_mkdir]
    (fs/namei.c:4448, Linux v6.18.46) hands the mode to
    [vfs_prepare_mode] (3448-3455), which strips the umask
    ([mode_strip_umask], include/linux/namei.h:116) and keeps only
    S_IRWXUGO and S_ISVTX; a default ACL only clears bits too
    ([posix_acl_create_masq], fs/posix_acl.c:459-511); the one bit a new
    folder can gain is S_ISGID, from a set-group-ID parent
    ([inode_init_owner], fs/inode.c:2593-2606, which tmpfs calls at
    mm/shmem.c:3095); and [generic_fillattr] reports that [i_mode]
    (fs/stat.c:90).  Accepting every mode word is therefore an
    over-admission (AGENTS.md's second priority), not an exact answer:
    bounding the stat's bits would need the requested mode, the umask
    and the parent's S_ISGID, and the model holds none of them: folders
    carry no mode, and the umask is not modeled (bugs/umask-unmodeled.md
    records that decline and this cost of it).

    A NON-NORMAL LAST COMPONENT IS -EEXIST, all three of them, and this
    is the one place [do_mkdirat] differs from [do_rmdir] in how it
    reads the kind.  [filename_create] (fs/namei.c:4200-4250, Linux
    v6.18.46) initialises

        struct dentry *dentry = ERR_PTR(-EEXIST);

    and then

        if (unlikely(type != LAST_NORM))
                goto out;

    (4203, 4219-4220) with [out:] returning that dentry unchanged.  So
    [mkdir(".")], [mkdir("..")] and [mkdir("/")] are -EEXIST, not the
    -EINVAL and -EBUSY rmdir gives the same spellings.

    THE TRAILING SEPARATOR IS IGNORED, and the derivation
    is one line of [filename_create] rather than an absence (4205,
    4228-4229):

        bool want_dir = lookup_flags & LOOKUP_DIRECTORY;
        ...
        if (last.name[last.len] && !want_dir)
                create_flags &= ~LOOKUP_CREATE;

    [do_mkdirat] passes LOOKUP_DIRECTORY (4479), so [want_dir] is true,
    the create flags survive, and "d/" creates exactly what "d" does.

    AN EXISTING NAME IS -EEXIST whatever kind it is:
    [filename_create] looks the name up with LOOKUP_EXCL (4231-4232),
    and [lookup_one_qstr_excl] answers -EEXIST for a positive dentry
    (1717-1719), before [may_create] and before the filesystem is asked
    anything.  [mnt_want_write]'s -EROFS is read only after that lookup
    (4223, 4236-4237: "don't fail immediately if it's r/o, at least try
    to report other errors"), so it does not stand beside the -EEXIST.

    AN ABSENT LAST COMPONENT IS CREATED as an [Fs.EDir] at the key
    [Fs.RMissing] names.  [Fs.resolve_missing_parent] is what makes that
    safe: the parent resolved as a directory, the name is nameable, the
    child key is canonical with that parent, and nothing is there yet,
    so [Fs.wf_fs] survives ([Fs.wf_fs_mkdir]).  That holds under /dev as
    anywhere else: the image describes /dev completely at launch (see
    [Fs.dev_dir]),
    so an absent name there is absent, and devtmpfs makes the folder as
    any tmpfs does.

    THE PARENT'S LINK COUNT FOLLOWS ([Fs.fs_mkdir]): one higher under the
    counting rule ([inc_nlink(dir)] in [shmem_mkdir] at mm/shmem.c:3952
    and in [ramfs_mkdir] at fs/ramfs/inode.c:127), the same under the
    fixed one ([Fs.DirLinks]), and the new folder starts at 2 or 1.

    ONE CREATE DECLINES: the one that would take the parent's counting
    count past [Fs.dir_count_max], ext4's limit.  tmpfs and ramfs set no
    [s_max_links] and go on counting, so every supported kernel answers
    that [mkdir]: the decline is a fail-closed gap, priority 3 only.

    THE PREFIX ERRORS ARE THE WALK'S OWN, as everywhere:
    [filename_parentat] runs first inside [filename_create] (4211-4213),
    so [Fs.RNotDir] is -ENOTDIR and [Fs.RAbsent] is -ENOENT before the
    last component is typed at all.

    A LINK AT THE LAST NAME IS -EEXIST like any other existing name:
    [filename_create] looks the last name up without following it.

    THE CREATE'S REFUSALS ARE [mkdirat_errnos], -ENOSPC among them:
    the file system's [->mkdir] answers it when the inode budget is
    spent or the inode allocation fails, on tmpfs and on ramfs alike,
    and the model tracks neither.  They stand on the creating row only,
    since [vfs_mkdir] reaches [->mkdir] and [may_create] only for a name
    the lookup found absent.  The walk's own -EACCES and -ENOMEM stand
    beside every answer past the fetch ([walk_refusals], in
    [mkdirat_spec]), the deterministic -EEXIST's included, and
    [getname_flags]' own -ENOMEM beside every answer
    ([getname_refusals]). *)
Definition mkdirat_body_spec (dirfd pathp : word)
    (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => err_ret ENAMETOOLONG          (* no NUL within PATH_MAX *)
  | CstrFault => err_ret EFAULT                  (* unmapped byte in the path string *)
  | CstrOk p =>
      if path_eqb p [] then err_ret ENOENT       (* empty pathname: getname's own -ENOENT *)
      else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
      else
        let '(r, lk, _) := Fs.resolve_parent (m_fs m) (m_cwd m) p in
        match r with
        (* [filename_parentat] FAILED: its errno wins, whatever the last
           kind.  [filename_create] returns that error before it ever
           reaches its own [type != LAST_NORM] test. *)
        | Fs.RNotDir _ => err_ret ENOTDIR
        | Fs.RAbsent _ => err_ret ENOENT
        | Fs.RLoop => err_ret ELOOP
        | Fs.RParent _ _ => unmodeled        (* [Fs.resolve_parent] maps it away *)
        | Fs.ROutside => unmodeled
        (* the parent walk SUCCEEDED, so the kind test runs now *)
        | Fs.RFound _ _ =>
            match mkdir_nonnorm_errno lk with
            | Some e => err_ret e
            | None => err_ret EEXIST
            end
        | Fs.RMissing par nm =>
            match mkdir_nonnorm_errno lk with
            | Some e => err_ret e
            | None =>
                if Nat.ltb Fs.dir_count_max
                     (S (Fs.dl_counting (Fs.fs_dir_links (m_fs m) par)))
                then unmodeled                  (* past EXT4_LINK_MAX: see above *)
                else
                  alt (e <- errno_from mkdirat_errnos ;; err_ret e)
                      (set_fs (Fs.fs_mkdir (m_fs m) (Fs.child_key par nm)) ;;
                       ret_only (Z_to_bv 64 0))
            end
        end
  end.

(** The pathname copy-in, recorded exactly as [openat_spec] records it.
    [do_mkdirat]'s caller fetches the name with [getname] before
    anything else, and there is no second copy-in on any arm.  Inside
    it, the walk's own refusals ([walk_refusals]); outside it,
    [getname_flags]' own ([getname_refusals]), which fail before the
    copy is done. *)
Definition mkdirat_spec (dirfd pathp : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  getname_refusals [] pathp
    (record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
       (walk_refusals Fs.WalkParent pathp (mkdirat_body_spec dirfd pathp i m))).

(** The flag word, then the body under its copy-in ledger.

    THE PATHNAME COPY-IN is recorded exactly as [Open.openat_spec]
    records it, and for the same reason: [read_cstr] is a read of user
    memory, and [State.syscall_effect_accesses] turns the ledger into a
    materialization charge, so an unrecorded read is a page the run never
    pays for.  It goes INSIDE the flag test rather than around the whole
    spec as openat's does, because openat's flag arm is [unmodeled] while
    this one is a real -EINVAL the kernel reaches before [getname()] is
    evaluated — recording a copy there would claim a read Linux did not
    perform.  The range is the prefix through the first NUL, the first
    faulting byte, or PATH_MAX, as for openat.  [getname_flags]' own
    -ENOMEM stands outside the ledger and inside the flag test
    ([getname_refusals]): the flag word is tested before [getname] is
    called, and the allocation fails before the copy is done. *)
Definition unlinkat_spec (dirfd pathp flags : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (modeled_unlink_flags flags) then err_ret EINVAL
  else
    getname_refusals [] pathp
      (record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
         (walk_refusals Fs.WalkParent pathp (unlinkat_body_spec dirfd pathp flags i m))).
