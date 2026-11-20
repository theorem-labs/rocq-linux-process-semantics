(** * LinuxProcessSem.Sys.Fs.Stat — readlinkat (78), newfstatat (79), fstat (80)

    This file answers to Linux [fs/stat.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

    Ported from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Fs.Namei.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** How many bytes [readlink_copy] copies: the body's length up to its
    first NUL ([strlen], fs/namei.c:5469), cut at [bufsiz]
    (:5419-5429).  [bufsiz] is the [int] [do_readlinkat] takes
    (fs/stat.c:563-564), so its SIGNED low half ([sint32]).  THE MINIMUM
    IS TAKEN IN [Z], and only the result, at most the body's length, is
    made a [nat]: the extracted checker computes this function, and a
    [Nat.min] of [Z.to_nat bufsiz] would first build a unary [nat] as
    large as [bufsiz] (up to 2^31 - 1), which exhausts the checker's stack
    on any link.  [readlinkat_largest_int_bufsiz_copies_a_short_body]
    (Checks/Cases/Fs/Stat.v) pins the largest [int] by computation. *)
Definition readlink_count (b : path) (bufsiz : word) : nat :=
  Z.to_nat (Z.min (Z.of_nat (length (Fs.link_text b))) (sint32 bufsiz)).

(** DOES THE COPY OF [n] BYTES TO [buf] FAULT before a byte moves?  Only
    when there is a byte to copy: [copy_to_user] returns the count it
    did NOT copy, and [_inline_copy_to_user]
    (include/linux/uaccess.h:190-200, Linux v6.18.46; riscv64's
    [_copy_to_user] is it, lib/usercopy.c:24-27) returns [n] itself
    when [access_ok] refuses the range, so a copy of no byte returns 0
    wherever [buf] points and [readlink_copy] (fs/namei.c:5419-5429)
    answers its count, 0.  A link whose body is empty, or starts with a
    NUL, is such a copy: tmpfs makes one from an initramfs entry
    ([do_symlink], init/initramfs.c:436-452, through [init_symlink],
    fs/init.c:200-215, to [shmem_symlink], which takes "", mm/shmem.c),
    and the image may hold one ([Fs.ELink]). *)
Definition readlink_copy_faults (buf : word) (n : nat) : bool :=
  negb (Nat.eqb n 0) && negb (access_okb buf (Z.of_nat n)).

(** THE COPY OF A LINK'S BODY to [buf]: [readlink_copy]
    (fs/namei.c:5419-5429) copies [min(len, buflen)] bytes with no NUL
    and returns that count, or -EFAULT when [copy_to_user] faults.  A
    nonempty range [access_ok] refuses faults before a byte moves
    ([readlink_copy_faults]); a partly writable range commits a prefix
    the model has no term for, and declines, as [fstat_file_spec] does.
    A copy of no byte writes nothing ([delivered_writes]) and reads no
    memory: [read_bytes_map] of a length 0 is [Some []] at any
    address. *)
Definition readlink_copy_spec (i : SyscallInput) (b : path) (buf bufsiz : word)
    : Sys SyscallEffect :=
  let n := readlink_count b bufsiz in
  if readlink_copy_faults buf n then err_ret EFAULT
  else
    match read_bytes_map (in_wmem i) buf (Z_to_bv 64 (Z.of_nat n)) with
    | None => unmodeled      (* a partial [copy_to_user] then -EFAULT *)
    | Some _ =>
        pure (mkEffect (Z_to_bv 64 (Z.of_nat n))
                (delivered_writes buf (firstn n (Fs.link_text b))) [])
    end.

(** [readlinkat dirfd path buf bufsiz] (riscv64 nr 78,
    [SYSCALL_DEFINE4], fs/stat.c:604-608), which is [do_readlinkat]
    (fs/stat.c:563-602, Linux v6.18.46).

    THE PATHNAME IS INTERPRETED, with the last component never followed
    ([do_readlinkat] walks with LOOKUP_EMPTY and without LOOKUP_FOLLOW,
    fs/stat.c:569, :575-576); a link before it is followed, and a
    trailing separator still forces the follow (fs/namei.c:2649-2650).

    THE ORDER IS THE KERNEL'S:

    - [bufsiz <= 0] is -EINVAL, and it is the FIRST statement (571-572),
      before [getname_flags].  So it records no copy-in, and a negative
      size with an unreadable path is -EINVAL rather than -EFAULT.  The
      parameter is an [int], so the test is on the SIGNED low half.
    - then the pathname fetch (575), with all three of [getname]'s
      answers;
    - then the dirfd, which the model answers only for AT_FDCWD;
    - then the walk ([filename_lookup], 576), whose outcomes are the
      answer.

    THE EMPTY PATHNAME IS -ENOENT, and the derivation is one flag:
    [do_readlinkat] sets LOOKUP_EMPTY unconditionally (569), so the
    empty name resolves to the dirfd itself rather than failing in
    [getname_flags].  For AT_FDCWD that is the working directory, which
    is not a symlink, so the call falls to the arm that distinguishes
    the two failures by the first byte of the name — -ENOENT for the
    empty one and -EINVAL for every other (593).

    A RESOLVED LINK IS READ ([d_is_symlink] and [->readlink], fs/stat.c
    :585-591, through [vfs_readlink] fs/namei.c:5441-5470): its body, up
    to the first NUL and cut at [bufsiz], goes to [buf] with no NUL
    ([readlink_copy_spec]).  ANY OTHER ENTRY IS -EINVAL (:592-594).

    THE TRAILING SEPARATOR IS THE WALK'S.  [do_readlinkat] reaches
    [filename_lookup] and so [path_lookupat], whose closing test
    (fs/namei.c:2685-2687)

        if (!err && nd->flags & LOOKUP_DIRECTORY)
                if (!d_can_lookup(nd->path.dentry))
                        err = -ENOTDIR;

    fires on the LOOKUP_DIRECTORY [lookup_last] set for a LAST_NORM
    component a separator follows (2649-2650), with LOOKUP_FOLLOW
    beside it.  The [Fs.WalkFull] walk sets both: [readlink("f/")] on a
    regular file is its [Fs.RNotDir], -ENOTDIR and not -EINVAL, and
    [readlink("l/")] follows the link [l].  A directory takes the [EDir]
    row and keeps its -EINVAL, with or without the separator.

    THE WRITE is the only one on any arm, and it is the link's body.

    THE WALK'S OWN -EACCES AND -ENOMEM stand beside every answer past
    the fetch ([Fs.Namei.walk_refusals]); the empty pathname is not
    walked component by component ([link_path_walk] returns at once on
    it, fs/namei.c:2455-2458) and takes neither.  [getname_flags]'s own
    -ENOMEM ([__getname], fs/namei.c:146-148, and the re-copy's
    [kzalloc], 189-193) stands beside every answer, the fetch's and the
    empty pathname's -ENOENT included, with the copy-in made when the
    allocation failed ([Fs.Namei.getname_refusals]): LOOKUP_EMPTY lets
    the empty name through [getname_flags], but only after the
    allocation. *)
Definition readlinkat_body_spec (dirfd pathp buf bufsiz : word) (i : SyscallInput)
    (m : Model) : Sys SyscallEffect :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => err_ret ENAMETOOLONG      (* no NUL within PATH_MAX *)
  | CstrFault => err_ret EFAULT              (* unmapped byte in the path string *)
  | CstrOk p =>
      if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
      else if path_eqb p [] then err_ret ENOENT
        (* LOOKUP_EMPTY makes the EMPTY pathname resolve to the
           dirfd itself, which for AT_FDCWD is the working
           directory: a directory, not a symlink, and the
           [name->name[0] == '\0'] arm answers -ENOENT rather than
           the -EINVAL every other name gets *)
      else
        let '(r, _, _) := Fs.resolve (Fs.WalkFull false false) (m_fs m) (m_cwd m) p in
        match r with
        | Fs.RFound _ (ELink b) => readlink_copy_spec i b buf bufsiz
        | Fs.RFound _ _ => err_ret EINVAL
        | Fs.RMissing _ _ => err_ret ENOENT
        | Fs.RNotDir _ => err_ret ENOTDIR
        | Fs.RAbsent _ => err_ret ENOENT
        | Fs.RLoop => err_ret ELOOP           (* the 41st link, fs/namei.c:1878-1879 *)
        | Fs.ROutside => unmodeled           (* "proc" and "sys" at the root *)
        | Fs.RParent _ _ => unmodeled        (* the parent and [O_CREAT] ends only *)
        end
  end.

Definition readlinkat_spec (dirfd pathp buf bufsiz : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if (sint32 bufsiz <=? 0)%Z then err_ret EINVAL
    (* [do_readlinkat]'s first statement, before [getname_flags] and so
       before any copy-in is recorded: [int bufsiz] and
       [if (bufsiz <= 0) return -EINVAL;] (fs/stat.c:563-572, Linux
       v6.18.46), so a low half of 0x80000000 or more is negative *)
  else
    getname_refusals [] pathp
      (record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
         (walk_refusals (Fs.WalkFull false false) pathp
            (readlinkat_body_spec dirfd pathp buf bufsiz i m))).

(** The flag WORDS [newfstatat_spec] interprets: 0 (plain [stat]) and
    AT_SYMLINK_NOFOLLOW ([lstat]).  Those are the only two riscv64 musl
    ever puts on syscall 79.  Following that through musl takes three
    steps, none of them obvious from the file names: riscv64 has no
    [__NR_fstatat], but src/internal/syscall.h defines [SYS_fstatat] to
    be [SYS_newfstatat] when the latter exists, so the [#ifdef
    SYS_fstatat] arm of src/stat/fstatat.c IS compiled; that arm takes
    the [statx] path only when the kernel [struct kstat]'s timestamps
    are narrower than [time_t], and on riscv64 both are 64 bits, so
    [__fstatat] falls through to [fstatat_kstat]; and [fstatat_kstat]
    has no [SYS_stat]/[SYS_lstat] to prefer, so it issues syscall 79
    with whatever flag it was given.  [stat()] gives it 0 and [lstat()]
    AT_SYMLINK_NOFOLLOW (src/stat/stat.c, src/stat/lstat.c).  [fstat()]
    does NOT arrive here: it calls [__fstatat(fd, "", st, AT_EMPTY_PATH)]
    (src/stat/fstat.c), and [fstatat_kstat] spends exactly that shape on
    [fstat] (80) before it would reach 79.

    The two flag words differ in how the walk ends ([statat_walk_mode]):
    [stat] follows a last link, [lstat] stats the link itself.

    AT_EMPTY_PATH is answered too, beside either word: with an EMPTY
    pathname it makes [vfs_fstatat] stat the descriptor or, for
    AT_FDCWD, the working directory ([newfstatat_body_spec]); with a
    NULL one it is declined ([statat_null_name]).
    Everything else -- AT_NO_AUTOMOUNT, the AT_STATX_SYNC_TYPE bits, and
    every word Linux answers -EINVAL for -- is unmodeled and DECLINED,
    not answered.  Declining costs precision and nothing else: see the
    ORDER paragraph at [newfstatat_spec]. *)
Definition modeled_statat_flags (flag : word) : bool :=
  let fl := Z.ldiff (bv_unsigned flag) AT_EMPTY_PATH in
  Z.eqb fl 0 || Z.eqb fl AT_SYMLINK_NOFOLLOW.

(** How [vfs_statx]'s walk ends: [LOOKUP_FOLLOW] unless
    AT_SYMLINK_NOFOLLOW (fs/stat.c:288-289). *)
Definition statat_walk_mode (flag : word) : Fs.WalkMode :=
  Fs.WalkFull (negb (Z.eqb (Z.land (bv_unsigned flag) AT_SYMLINK_NOFOLLOW)
                           AT_SYMLINK_NOFOLLOW)) false.

(** Is AT_EMPTY_PATH set? *)
Definition statat_empty_path (flag : word) : bool :=
  Z.eqb (Z.land (bv_unsigned flag) AT_EMPTY_PATH) AT_EMPTY_PATH.

(** A NULL PATHNAME UNDER AT_EMPTY_PATH IS DECLINED.  [vfs_fstatat]
    (fs/stat.c:365-379, Linux v6.18.46) fetches through
    [getname_maybe_null] (include/linux/fs.h:2950-2958), which under
    AT_EMPTY_PATH returns NULL for a NULL pointer (2955-2956) without
    loading a byte.  [vfs_fstatat] then stats the descriptor itself for
    a dfd of 0 or more (its call of vfs_fstat, fs/stat.c:372-373, Linux
    v6.18.46), and otherwise hands the NULL name to [vfs_statx], whose
    walk reads it as "" ([__set_nameidata], fs/namei.c:668, Linux
    v6.18.46): for AT_FDCWD, the working
    folder.  So Linux answers that call as the empty name, whatever user
    memory holds at address 0, and copies nothing in.
    [newfstatat_body_spec] reads the string at address 0 instead
    ([read_cstr]): -EFAULT where it is unmapped, a walk of its bytes
    where it is mapped.  [newfstatat_core_spec] declines the shape
    before that body is reached.  No program in theories/Examples makes
    syscall 79 at all: none of its proofs steps that arm. *)
Definition statat_null_name (pathp flag : word) : bool :=
  statat_empty_path flag && bv_eqb pathp (Z_to_bv 64 0).

(** DOES THE FETCH REACH [getname_flags]?  [vfs_fstatat] fetches the
    pathname through [getname_maybe_null] (include/linux/fs.h:2950-2958,
    Linux v6.18.46).  Without AT_EMPTY_PATH that is plain [getname]
    (2952-2953), which is [getname_flags] with no flags, so it always
    does.  With AT_EMPTY_PATH a NULL pointer is no name at all
    (2955-2956), a call [newfstatat_core_spec] declines before this test
    ([statat_null_name]).  Any other pointer goes to
    [__getname_maybe_null] (fs/namei.c:225-242, Linux v6.18.46), which first loads the
    lead byte with [get_user]: a load that faults is -EFAULT (231-232)
    and a NUL is no name (233-234), both before anything is allocated,
    and only a readable lead byte that is not NUL goes on to
    [getname_flags] (236).  [get_user] tests [access_ok] on the one byte
    as [strncpy_from_user]'s clamp does ([State.read_cstr_aux]).  Those
    three functions read the same in v6.16.

    So the refusals [getname_flags] gives ahead of its answers
    ([Fs.Namei.getname_refusals], after the lead byte's load under
    AT_EMPTY_PATH: [statat_lead_reads]), and the walk's after it, belong
    to the call exactly when this holds ([newfstatat_spec],
    [newfstatat_core_spec]). *)
Definition statat_getname_runs (i : SyscallInput) (pathp flag : word) : bool :=
  negb (statat_empty_path flag)
  || (access_okb pathp 1
      && match in_mem i pathp with
         | Some b => negb (bv_eqb b (Z_to_bv 8 0))
         | None => false
         end).

(** WHAT THE FETCH HAS READ WHEN IT CALLS [getname_flags], on a call
    [statat_getname_runs]: the lead byte under AT_EMPTY_PATH, nothing
    without it.  [__getname_maybe_null] loads that byte with [get_user]
    (fs/namei.c:231, Linux v6.18.46) before it calls [getname_flags]
    (236), so there [__getname]'s -ENOMEM (146-148) carries the one-byte
    read [(pathp, 1)], never an empty ledger; plain [getname]
    (include/linux/fs.h:2952-2953) allocates before it reads a byte.
    The re-copy's -ENOMEM carries the first EMBEDDED_NAME_MAX bytes
    either way, which hold the lead byte
    ([Fs.Namei.getname_alloc_reads]).  [newfstatat_spec] reads this
    only on a call [statat_getname_runs]. *)
Definition statat_lead_reads (pathp flag : word) : list (word * nat) :=
  if statat_empty_path flag then [(pathp, 1%nat)] else [].

(* -------------------------------------------------------------------------
   Delivering a struct stat: the machinery both 79 and 80 read

   [newfstatat] answers its success arm off the resolved entry with the
   same delivery, pin and predicates [fstat] uses, so they live here,
   above both.
   ------------------------------------------------------------------------- *)

(** The model a regular file's stat leaves when its inode [ino] already
    had the pin [sp] and the stat delivered [bs]: the same model while
    the mode is the pin's, and otherwise [bs] as the inode's new pin.
    [Uapi.stat_stable_eqb] lets a later [st_mode] differ from the pin's
    only by the set-user-ID and set-group-ID bits a write or truncate
    clears, so this is the stat that first shows one cleared; holding
    every later stat to its mode is what keeps a bit Linux cleared from
    being shown set again, since no modeled syscall sets one. *)
Definition file_pin_after (ino : Fs.ino) (sp : StatPin) (bs : list byte) (m : Model)
    : Model :=
  if Z.eqb (stat_mode bs) (stat_mode (sp_bytes sp)) then m
  else with_statpin (IdIno ino) (mkStatPin bs (sp_rule sp) (sp_released sp)) m.

(** THE SUCCESS ARM, for a descriptor on a file the interpreted file
    system holds.  It is the second line of the two above:

      if (!error) error = cp_new_stat(&stat, statbuf);

    and everything below is [cp_new_stat] (fs/stat.c, Linux v6.18.46,
    commit 1f99e9ab748f) rather than [vfs_fstat].

    WHAT THE MODEL DETERMINES, and it is less than half the struct:

    - THE WIDTH AND THE PADDING.  [cp_new_stat] clears its whole stack
      copy through [INIT_STRUCT_STAT_PADDING] — the generic [memset] on
      riscv64, only x86 overriding it — assigns the members, and hands
      all 128 bytes to ONE [copy_to_user].  So [__pad1], [__pad2],
      [__unused4] and [__unused5] are delivered as ZERO, and the write
      is exactly [Uapi.STAT_SIZE] bytes wide at [statbuf].  This is the
      part of the answer the model knows exactly, and it is what makes a
      poisoned, short or invented buffer rejectable
      ([Uapi.stat_buf_wf]).
    - THE TYPE IS S_IFREG, [st_rdev] IS 0, [st_blksize] IS THE PAGE SIZE
      AND [st_size] IS THE FILE'S LENGTH, all asserted.
      [generic_fillattr] (fs/stat.c:82-113, Linux v6.18.46) copies
      [inode->i_mode] into [stat->mode] (:90), [inode->i_rdev] into
      [stat->rdev] (:94), [i_size_read(inode)] into [stat->size] (:95)
      and [i_blocksize(inode)] into [stat->blksize] (:105), and
      [cp_new_stat] copies all four out.
      An [Fs.EFile] is a regular file: the image
      names a device by [Fs.EDev] and a folder by [Fs.EDir], so an
      [EFile] it holds is the launch file system's regular file, and an
      [EFile] this run made came from an O_CREAT open, whose
      [build_open_flags] sets [op->mode = how->mode | S_IFREG]
      (fs/open.c:1271).  A regular file on tmpfs or ramfs has no device
      number ([Uapi.stat_no_rdev]) and the page size as its block size,
      the configuration of record having no huge pages for
      [shmem_getattr] to raise it to ([Uapi.stat_page_blksize]).  For a
      regular file [i_size] is the number of bytes it holds, which is the
      length of the [EFile]'s byte list.  So any other type, device
      number, block size or size is rejected ([Uapi.stat_reg_fixed],
      [Uapi.stat_size_ok]).

    - [st_nlink] IS THE INODE'S LINK COUNT, asserted:
      [generic_fillattr] copies [inode->i_nlink] (fs/stat.c:91), which
      is [Fs.fs_ino_nlink] -- one per name the image shows, plus the
      names it does not ([Fs.Inode]'s [ino_outside]), so 0 for a file
      no name reaches any more ([Uapi.stat_nlink_ok]).

    WHAT IT DOES NOT DETERMINE, and how it answers anyway.  The device,
    the inode number, the permission bits, the owning ids, the block
    count and the three timestamp pairs have no source in [Fs].  Each is
    a [choose] — an environment value, not a zero.  Zero-filling them
    would be a confident wrong answer of exactly the kind AGENTS.md's
    first priority forbids.

    FOUR MEMBERS ARE LEFT OUT OF THE PIN and are therefore re-chosen at
    every call: [st_blocks] and the three timestamp pairs.  That is
    over-admission — the model accepts a run in which two stats of one
    untouched file report time running backwards, which Linux does not
    produce — and it is kept because holding them fixed would reject the
    ordinary stat/write/stat trace instead.
    bugs/fstat-unpinned-members-over-admit.md carries the argument and
    what it costs.

    THE CHOICE IS PINNED, per INODE, in [State.procst_statpins], and that
    is what makes it a check rather than a shrug.  Chosen afresh at each
    call these members would admit a trace in which two [fstat]s of one
    unchanged file report different inodes, which no Linux machine
    produces — the objection [State.procst_utsname] answers for the UTS
    name and [Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec] answers
    by declining.  So the first stat of a file records the 128 bytes it
    delivered under [State.IdIno], and every later stat of the same
    inode -- through any of its names or any descriptor on it -- must
    repeat its STABLE members ([Uapi.stat_stable_eqb]): the device,
    inode number, mode, ids, [st_rdev] and block size.  [st_size],
    [st_blocks] and the timestamps are deliberately NOT held against the
    pin, because a write moves all three, and [st_nlink] is asserted
    instead.  Two names of one file therefore report one [st_ino].

    THE MODE IS HELD BUT FOR ITS SET-ID BITS, which a write or a
    truncate by a caller without CAP_FSETID clears
    ([Uapi.stat_mode_killed] reads that out of [file_remove_privs] and
    [do_truncate]).  A later stat may show S_ISUID or S_ISGID cleared
    where the pin had it set, as those calls leave it
    ([Uapi.stat_mode_stable]), and never set where the pin had it clear,
    since the model has no [chmod].  The stat that shows the drop
    becomes the pin ([file_pin_after]), so a bit once shown cleared
    stays cleared.  The drop is admitted whether or not a write ran in
    between, which [Uapi.stat_stable_eqb] names as an over-approximation.

    A PIN THAT IS NOT [Uapi.stat_buf_wf], OR NOT [Uapi.stat_reg_fixed],
    IS DECLINED, and that branch is unreachable: the only writers are
    the two branches below, and each writes a delivery it has just
    checked against both predicates.  It is written rather than
    argued away because receptiveness ([Checks.Progress]) is a
    statement about every [Model], including ones no run can build, and
    an unsatisfiable [choose] is the one way to write a non-receptive
    spec (Monad.v): the type, [st_rdev] and the block size are stable
    members, so a pin of another type, device number or block size
    leaves no answer to choose.

    THE ORDER IS THE KERNEL'S.  [vfs_fstat] resolves the descriptor
    before [cp_new_stat] runs, so -EBADF preempts everything here; then
    [copy_to_user]'s [access_ok] gate refuses the 128-byte range with
    -EFAULT before a byte moves; then the range is either wholly
    writable, which is the modeled path, or partially so, which is
    [unmodeled] — a [copy_to_user] that commits a prefix and then faults
    leaves a half-written struct this model has no vocabulary for, the
    shape [Kernel.Sys.uname_spec] and [Time.gettimeofday_spec] decline
    for the same reason.  Asking [access_ok] BEFORE the walk is
    load-bearing rather than cosmetic, for the wrapping reason
    [Kernel.Sys.uname_spec] states and
    bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md records.

    THE INODE IS WHAT THE CALLER PASSES: the inode an [Fs.EFile] names,
    or the one a descriptor holds ([State.FdFile]).  A number with no
    row reads as the empty file with no name outside the image
    ([Fs.fs_inode]), so there is no case to decline. *)
Definition fstat_file_spec (ino : Fs.ino) (statbuf : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (access_okb statbuf STAT_SIZE) then err_ret EFAULT
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => unmodeled      (* a partial [copy_to_user] then -EFAULT *)
    | Some _ =>
        match statpin_lookup (m_statpins m) (IdIno ino) with
        | Some sp =>
            if negb (stat_buf_wf (sp_bytes sp) && stat_reg_fixed (sp_bytes sp))%bool
            then unmodeled
              (* no branch writes such a pin *)
            else
              bs <- choose (fun bs : list byte =>
                              stat_buf_wf bs = true
                              /\ stat_reg_fixed bs = true
                              /\ stat_size_ok (length (Fs.fs_ino_data (m_fs m) ino)) bs = true
                              /\ stat_nlink_ok (Fs.fs_ino_nlink (m_fs m) ino) bs = true
                              /\ stat_stable_eqb bs (sp_bytes sp) = true) ;;
              modify (file_pin_after ino sp bs) ;;
              pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        | None =>
            bs <- choose (fun bs : list byte =>
                            stat_buf_wf bs = true
                            /\ stat_reg_fixed bs = true
                            /\ stat_size_ok (length (Fs.fs_ino_data (m_fs m) ino)) bs = true
                            /\ stat_nlink_ok (Fs.fs_ino_nlink (m_fs m) ino) bs = true) ;;
            set_statpin (IdIno ino) (mkStatPin bs None false) ;;
            pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        end
    end.

(** WHAT A PIN HOLDS BESIDE THE STABLE MEMBERS ([Uapi.stat_stable_eqb]),
    by identity: the members [generic_fillattr] reads off the inode
    (fs/stat.c:91-106, Linux v6.18.46) that no call the model answers
    moves for that kind of object, or that only the removal of a link
    name moves.  A later stat must repeat each
    ([Uapi.stat_field_eqb]):

    - a DEVICE NODE's link count (bytes 20..23) and its three timestamp
      pairs (72..119), whether the pin is the node's ([State.IdDev]) or
      a descriptor's on it ([State.IdDevFd]).  No arm gives a device
      node a name ([mknod] and
      [link] are unmodeled) or takes one away ([Fs.Namei.unlinkat_file_spec]
      declines it), and no answered call on /dev/null or /dev/urandom
      touches the inode's times: [read_null], [write_null] and their
      [_iter] twins return at once (drivers/char/mem.c:412-433);
      [urandom_read_iter] copies out what the crng generates
      ([get_random_bytes_user], drivers/char/random.c:434-482, called at
      :1474, Linux v6.18.46), before which, while the crng is not ready,
      it mixes timer samples into the input pool
      ([try_to_generate_entropy], :1282-1354, called at :1462);
      [random_write_iter] (:1448-1451) mixes the written bytes into the
      pool ([write_pool_user], :1420-1446, its [mix_pool_bytes] at
      :1432); and [vfs_read] and [vfs_write] update no time
      (fs/read_write.c:552, :666, Linux v6.18.46);
    - a LINK's link count, [st_blocks] (64..71), [st_mtime] (88..103)
      and [st_ctime] (104..119).  Nothing writes a link's body, so its
      blocks and mtime stay as [shmem_symlink] left them
      (mm/shmem.c:4159-4170, Linux v6.18.46); its count and ctime move
      only when one of its names is removed ([simple_unlink],
      fs/libfs.c:787-795, and [shmem_unlink], mm/shmem.c:4016-4019, set
      the inode's ctime and drop its count).  The image cannot show two
      names of one link as one identity, so the removal of any link
      name RELEASES those two ([State.statpins_release_links]): with
      [released] set, a later stat must still repeat the blocks and the
      mtime, and may deliver any count and ctime;
    - a FOLDER's [st_blocks]: tmpfs makes every inode with none
      ([__shmem_get_inode], mm/shmem.c:3096, Linux v6.18.46) and adds
      none to a folder, and a ramfs folder reports the [i_blocks] ramfs
      never sets ([ramfs_dir_inode_operations] has no [getattr],
      fs/ramfs/inode.c:191, Linux v6.18.46), so a folder's is 0 for its
      whole life.  [fstat_dir_spec] asserts that 0 at every delivery
      ([Uapi.stat_dir_fixed]), the first included, so the hold restates
      the assertion.

    LEFT FREE, because an answered call moves them: a regular file's
    [st_blocks] and timestamps (a write, a truncate, an O_TRUNC open; a
    read's [file_accessed]); a folder's [st_size], [st_mtime] and
    [st_ctime] (a name made or removed in it: [dir->i_size] by
    [BOGO_DIRENT_SIZE] and the times, mm/shmem.c:3899-3900, :4015-4017)
    and its [st_atime] ([getdents64]'s [iterate_dir] calls
    [file_accessed] even when it answers -EINVAL, fs/readdir.c:111); and
    a link's [st_atime] ([touch_atime] in [readlinkat],
    fs/stat.c:589, and in a walk that follows it, fs/namei.c:1936, Linux
    v6.18.46).  bugs/fstat-unpinned-members-over-admit.md records what
    that admits.  A regular file's pin holds nothing here: its link
    count and length are computed ([fstat_file_spec]). *)
Definition stat_pin_held (id : StatId) (released : bool) (b1 b2 : list byte) : bool :=
  match id with
  | IdIno _ => true
  | IdDir _ => stat_field_eqb ST_BLOCKS_OFF 8 b1 b2
  | IdDev _ | IdDevFd _ _ =>
      (stat_field_eqb ST_NLINK_OFF 4 b1 b2 && stat_field_eqb ST_ATIME_OFF 48 b1 b2)%bool
  | IdLink _ =>
      ((released
        || (stat_field_eqb ST_NLINK_OFF 4 b1 b2 && stat_field_eqb ST_CTIME_OFF 16 b1 b2))
       && stat_field_eqb ST_BLOCKS_OFF 8 b1 b2 && stat_field_eqb ST_MTIME_OFF 16 b1 b2)%bool
  end.

Lemma stat_pin_held_refl : forall id r b, stat_pin_held id r b b = true.
Proof. intros [] r b; destruct r; cbn [stat_pin_held]; now rewrite ?stat_field_eqb_refl. Qed.

(** The model a pinned identity's stat leaves when its pin was [sp] and
    the stat delivered [bs]: the same model, or, when the pin's link
    count and ctime were released ([State.StatPin]'s [sp_released]),
    [bs] as the identity's new pin, which holds them again. *)
Definition pinned_after (id : StatId) (sp : StatPin) (bs : list byte) (m : Model)
    : Model :=
  if sp_released sp then with_statpin id (mkStatPin bs (sp_rule sp) false) m else m.

(** THE SUCCESS ARM FOR A CHARACTER DEVICE THE MODEL KNOWS, in two
    instances: /dev/null ([fstat_devnull_spec], [Uapi.stat_devnull_ok])
    and /dev/urandom ([fstat_urandom_spec], [Uapi.stat_urandom_ok]).
    It is [fstat_file_spec]'s shape with the file's assertions replaced
    by the device's: the model KNOWS which device this descriptor is —
    that is the assumption the openat arm states — so [st_mode]'s type,
    [st_rdev], [st_size], [st_blocks] and [st_blksize] are pinned
    outright, and the
    members the kernel does not decide are chosen once and held in
    [State.procst_statpins] under the device node's identity
    ([State.IdDev] of its key), exactly as a file's are under its
    inode, or under the descriptor's ([State.IdDevFd]) when the stat
    cannot name the node ([fstat_devfd_spec]).  [id] is that identity
    and [ok] the device's assertions; nothing below reads either for
    anything but the pin's key and the delivery's test.

    THE LINK COUNT AND THE THREE TIMESTAMP PAIRS ARE THE ENVIRONMENT'S,
    CHOSEN ONCE AND HELD like the stable members, and a link's count,
    [st_blocks], [st_mtime] and [st_ctime] too ([stat_pin_held] says
    why no answered call moves them).  A link's count may fall during a
    run: the image cannot show two names of one link as one
    ([State.StatId]), so an [unlinkat] of another link's name may remove
    a name of this one.  That is why [State.with_fs] RELEASES every
    link's count and ctime when a link name goes
    ([State.statpins_release_links]): the next stat may deliver any
    count and ctime, must repeat every other member the pin holds, and
    becomes the pin ([pinned_after]).

    THE PIN IS CHECKED AGAINST BOTH PREDICATES before it is used, where
    the file arm checks [stat_buf_wf] alone.  The file arm patches
    [st_size] into whatever pin it holds, and [st_size] is outside the
    stable members, so any well-formed pin admits a delivery; here the
    asserted members are INSIDE the stable region ([st_mode], [st_rdev]
    and [st_blksize]) or asserted constant ([st_size], [st_blocks]), so a pin
    that failed [stat_devnull_ok] would leave the [choose] below with no
    satisfying buffer — a non-receptive spec, the one shape Monad.v
    forbids.  Declining such a pin keeps the arm receptive on every
    [Model]; the branch is unreachable, since the only writer is the
    branch below, which has just checked both predicates.

    A device descriptor carries no key, so [fstat] on one reads the pin
    of its kind's node at the device's own name only when that node is
    the image's one node of the kind, and the descriptor's own pin
    otherwise ([fstat_devfd_spec]); [unlinkat] declines the removal of
    an [Fs.EDev] entry ([Fs.Namei.unlinkat_file_spec]).  The rest — -EBADF before
    anything, [access_ok]'s -EFAULT, the partial [copy_to_user] decline,
    the errnos past an open descriptor — is [fstat_file_spec]'s argument
    unchanged. *)
Definition fstat_pinned_spec (id : StatId) (ok : list byte -> bool)
    (statbuf : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (access_okb statbuf STAT_SIZE) then err_ret EFAULT
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => unmodeled      (* a partial [copy_to_user] then -EFAULT *)
    | Some _ =>
        match statpin_lookup (m_statpins m) id with
        | Some sp =>
            if negb (stat_buf_wf (sp_bytes sp) && ok (sp_bytes sp))%bool then unmodeled
              (* no branch writes such a pin: see above *)
            else
              bs <- choose (fun bs : list byte =>
                              stat_buf_wf bs = true
                              /\ ok bs = true
                              /\ stat_pin_held id (sp_released sp) bs (sp_bytes sp) = true
                              /\ stat_stable_eqb bs (sp_bytes sp) = true) ;;
              modify (pinned_after id sp bs) ;;
              pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        | None =>
            bs <- choose (fun bs : list byte =>
                            stat_buf_wf bs = true
                            /\ ok bs = true) ;;
            set_statpin id (mkStatPin bs None false) ;;
            pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        end
    end.

Definition fstat_chrdev_spec (k : path) (ok : list byte -> bool)
    (statbuf : word) : Sys SyscallEffect :=
  fstat_pinned_spec (IdDev k) ok statbuf.

(** The keys of the image's device nodes of kind [d]. *)
Definition dev_node_keys (fs : Fs.Fs) (d : DevKind) : list Fs.path :=
  List.map fst (List.filter (fun ke => match snd ke, d with
                             | EDev DevNull, DevNull => true
                             | EDev DevUrandom, DevUrandom => true
                             | _, _ => false
                             end) (Fs.fs_tree fs)).

(** Is [k] the key of the image's ONE node of kind [d]? *)
Definition dev_sole_node (fs : Fs.Fs) (d : DevKind) (k : Fs.path) : bool :=
  match dev_node_keys fs d with
  | [k'] => path_eqb k' k
  | _ => false
  end.

(** THE STAT OF DEVICE DESCRIPTOR [fd], of kind [d], whose own name is
    [k].  The descriptor carries no key ([State.FdDevNull],
    [State.FdUrandom]) and an open answers at any node of the kind
    ([Fs.Open.open_devnull]), while two nodes are two inodes in Linux,
    with their own [st_ino], link count and times
    ([init_special_inode], fs/inode.c:2552-2577, Linux v6.18.46, gives
    each node its own inode).  So the stat holds the node's members
    under its key's pin ([fstat_chrdev_spec]) when the node at [k] is
    the image's one node of kind [d], the only node such a descriptor
    can have come from.  Otherwise it holds them under the DESCRIPTOR's
    pin ([State.IdDevFd] of [fd] and [d]): which node the descriptor
    came from is not known, but it is one node for the descriptor's
    whole life, and [vfs_fstat] (fs/stat.c:276-281) reports that held
    file's inode at every call ([generic_fillattr], fs/stat.c:82-94).
    So two stats of one descriptor with nothing between them repeat the
    node's members, as on Linux.  The pin never outlives the descriptor's
    file: it is dropped by the arm that installs a device descriptor at
    [fd] ([State.with_fd_unpinned]), and by the next image when [fd]
    holds no descriptor of the kind ([State.stat_id_alive]).  Two
    descriptors of one file, as a [dup] makes, hold two pins and may
    report two [st_ino]s, which over-admits and refuses nothing Linux
    reports.  Which branch answers depends on the image alone, which no
    answered call changes for a device: no arm makes a device node, and
    [unlinkat] declines the removal of one
    ([Fs.Namei.unlinkat_file_spec]). *)
Definition fstat_devfd_spec (d : DevKind) (k : path) (ok : list byte -> bool)
    (fd statbuf : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if dev_sole_node (m_fs m) d k then fstat_chrdev_spec k ok statbuf
  else fstat_pinned_spec (IdDevFd fd d) ok statbuf.

(** THE SUCCESS ARM FOR A LINK the walk did not follow ([lstat]): the
    device node's shape over the link's identity, its key
    ([State.IdLink]).  [generic_fillattr] copies the link inode's
    [i_mode] (fs/stat.c:90), S_IFLNK|0777 on tmpfs and ramfs, its
    [i_rdev] (:94), 0, its [i_size] (:95), which tmpfs sets to the
    body's length up to its first NUL (mm/shmem.c:4158), its block size
    (:105), the page size, and its [i_blocks] (:106), which the body's
    length bounds: all asserted ([Uapi.stat_lnk_fixed]).  Its link
    count, [st_blocks], [st_mtime] and [st_ctime] are held, and the
    count and ctime released when a link name goes ([stat_pin_held]). *)
Definition fstat_link_spec (k : path) (b : path) (statbuf : word)
    : Sys SyscallEffect :=
  fstat_pinned_spec (IdLink k) (stat_lnk_fixed (length (Fs.link_text b))) statbuf.

(** A FOLDER'S LINK COUNT UNDER ONE RULE ([Fs.DirLinks]). *)
Definition dir_rule_count (d : Fs.DirLinks) (r : DirRule) : nat :=
  match r with
  | DirCounting => Fs.dl_counting d
  | DirFixed => Fs.dl_fixed d
  end.

(** Do the two rules give the folder different [st_nlink]s?  Compared
    as [Uapi.stat_nlink_ok] compares, modulo 2^32. *)
Definition dir_counts_differ (d : Fs.DirLinks) : bool :=
  negb (Z.eqb (bv_unsigned (Z_to_bv 32 (Z.of_nat (Fs.dl_counting d))))
              (bv_unsigned (Z_to_bv 32 (Z.of_nat (Fs.dl_fixed d))))).

(** The [st_nlink] a folder's stat may report: the count of the rule its
    pin chose, or either count while none is chosen. *)
Definition dir_nlink_ok (d : Fs.DirLinks) (r : option DirRule) (bs : list byte)
    : bool :=
  match r with
  | Some r => stat_nlink_ok (dir_rule_count d r) bs
  | None => (stat_nlink_ok (Fs.dl_counting d) bs || stat_nlink_ok (Fs.dl_fixed d) bs)%bool
  end.

(** The rule a delivery [bs] chooses, once the counts differ. *)
Definition dir_rule_of (d : Fs.DirLinks) (bs : list byte) : DirRule :=
  if stat_nlink_ok (Fs.dl_counting d) bs then DirCounting else DirFixed.

(** The rule a pin carries after a delivery [bs]: kept once chosen, and
    chosen by the first delivery that tells the counts apart. *)
Definition dir_rule_after (d : Fs.DirLinks) (r : option DirRule) (bs : list byte)
    : option DirRule :=
  match r with
  | Some _ => r
  | None => if dir_counts_differ d then Some (dir_rule_of d bs) else None
  end.

(** Does a pin carrying [r] choose its rule at this stat? *)
Definition dir_rule_new (d : Fs.DirLinks) (r : option DirRule) : bool :=
  match r with
  | Some _ => false
  | None => dir_counts_differ d
  end.

(** The model a folder's stat leaves when its key [k] already had the
    pin [sp]: the same model, or the pin's bytes again with the rule the
    delivery [bs] chose, at the first stat that tells the counts apart. *)
Definition dir_pin_after (k : Fs.path) (d : Fs.DirLinks) (sp : StatPin)
    (bs : list byte) (m : Model) : Model :=
  if dir_rule_new d (sp_rule sp)
  then with_statpin (IdDir k)
         (mkStatPin (sp_bytes sp) (Some (dir_rule_of d bs)) (sp_released sp)) m
  else m.

(** THE SUCCESS ARM FOR A DIRECTORY.

    THE TYPE BITS ARE ASSERTED, as the file arm asserts S_IFREG.
    [Fs.EDir] is an entry kind, so the model KNOWS the object is a
    directory.  [stat_is_dir] is that assertion and
    [generic_fillattr] (fs/stat.c:82-113, Linux v6.18.46) is where it
    comes from: [i_mode]'s type bits were set when the directory was
    made and nothing moves them.  So are what tmpfs and ramfs fix of a
    folder ([Uapi.stat_dir_fixed]): [st_rdev] 0 (fs/stat.c:94), the
    page size as [st_blksize] (:105), and [st_blocks] 0 (:106), at
    every delivery, the first included.

    THE LINK COUNT IS ASSERTED UNDER THE FOLDER'S RULE ([Fs.DirLinks]):
    a file system that counts subfolders (tmpfs and ramfs, the file
    systems of the configuration of record) reports [Fs.dl_counting],
    one that does not (btrfs) [Fs.dl_fixed], which no supported kernel
    gives: a priority-2 gap ([Fs.DirLinks]).  Which rule the folder's
    file system follows is not image data; it is chosen by the first
    stat whose [st_nlink] tells the two counts apart ([dir_rule_after])
    and kept in the pin ([State.StatPin]), so every later stat must
    follow it.  Before the counts differ either rule gives the same
    answer.  A folder with no row of the image's folder table counts as
    the image implies ([Fs.fs_dir_links], [Fs.fs_tree_count]): two, plus
    one per subfolder, and at the root also /proc and /sys, folders of
    the root file system, not symbolic links, by a launch premise,
    whether or not the image holds them ([Fs.root_unheld_dirs]).

    THE STABLE MEMBERS ARE CHOSEN ONCE AND HELD, as for a file
    ([Uapi.stat_stable_eqb]): the device, inode, mode and ids; and
    [st_blocks], which a folder on tmpfs or ramfs never moves
    ([stat_pin_held]), is held too, restating its assertion.  [st_size]
    and the timestamps are NOT held: they move whenever an entry is
    made or removed in the
    folder — tmpfs adds and subtracts [BOGO_DIRENT_SIZE] on every
    [shmem_mknod] (mm/shmem.c:3899) and [shmem_unlink]
    (mm/shmem.c:4015), so creating a FILE in a folder an earlier stat
    saw changes the folder's [st_size] — and [getdents64] moves the
    atime.

    THE PIN IS KEYED BY THE FOLDER'S KEY ([State.IdDir]), a folder's
    identity, and it dies with the folder: [rmdir]'s removal goes
    through [State.with_fs], whose [State.statpins_restrict] drops it,
    so a folder made again at the same key starts with no pin, as Linux
    gives it a new inode.

    The rest — [access_ok]'s -EFAULT, the partial [copy_to_user]
    decline, the unsatisfiable-pin decline that keeps the [choose]
    receptive — is [fstat_file_spec]'s argument unchanged. *)
Definition fstat_dir_spec (k : Fs.path) (statbuf : word)
    : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (access_okb statbuf STAT_SIZE) then err_ret EFAULT
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => unmodeled      (* a partial [copy_to_user] then -EFAULT *)
    | Some _ =>
        match statpin_lookup (m_statpins m) (IdDir k) with
        | Some sp =>
            if negb (stat_buf_wf (sp_bytes sp) && stat_dir_fixed (sp_bytes sp))%bool
            then unmodeled
              (* no branch writes such a pin: the one writer below has
                 just checked both predicates *)
            else
              bs <- choose (fun bs : list byte =>
                              stat_buf_wf bs = true
                              /\ stat_dir_fixed bs = true
                              /\ dir_nlink_ok (Fs.fs_dir_links (m_fs m) k) (sp_rule sp) bs
                                 = true
                              /\ stat_pin_held (IdDir k) (sp_released sp) bs (sp_bytes sp)
                                 = true
                              /\ stat_stable_eqb bs (sp_bytes sp) = true) ;;
              modify (dir_pin_after k (Fs.fs_dir_links (m_fs m) k) sp bs) ;;
              pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        | None =>
            bs <- choose (fun bs : list byte =>
                            stat_buf_wf bs = true
                            /\ stat_dir_fixed bs = true
                            /\ dir_nlink_ok (Fs.fs_dir_links (m_fs m) k) None bs = true) ;;
            set_statpin (IdDir k)
              (mkStatPin bs (dir_rule_after (Fs.fs_dir_links (m_fs m) k) None bs) false) ;;
            pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        end
    end.


(** THE DELIVERY FOR A RESOLVED ENTRY, one row per kind.  This is what
    [newfstatat]'s success arm is, and it is calls into the machinery
    above rather than another copy of it.

    A DEVICE NODE'S PIN IS ITS KEY'S ([State.IdDev]), so a second node
    of one kind at another key is its own identity with its own pin, as
    two device nodes are two inodes in Linux.  A LINK the walk handed
    back unfollowed ([lstat]) is delivered as one ([fstat_link_spec]). *)
Definition stat_entry_spec (k : Fs.path) (e : Entry) (statbuf : word)
    : Sys SyscallEffect :=
  match e with
  | EFile ino => fstat_file_spec ino statbuf
  | EDir => fstat_dir_spec k statbuf
  | EDev DevNull => fstat_chrdev_spec k stat_devnull_ok statbuf
  | EDev DevUrandom => fstat_chrdev_spec k stat_urandom_ok statbuf
  | ELink b => fstat_link_spec k b statbuf
  end.

(** [newfstatat dirfd path statbuf flag] — [stat]/[lstat] as modern libc
    issues them.  KERNEL SCOPE for everything below: the supported
    kernels, v6.16 to v6.18.46 (SCOPE.md).  It was read over Linux
    v6.10-v6.15, fs/stat.c, [SYSCALL_DEFINE4(newfstatat)] /
    [cp_new_stat], and fs/namei.c, [getname_flags] / [filename_lookup] /
    [path_init].  [SYSCALL_DEFINE4(newfstatat)] and [cp_new_stat] are
    byte-identical across that range; [vfs_fstatat] and [vfs_statx] are
    not, and the part that moved is the fetch through
    [getname_maybe_null], whose NULL pathname under AT_EMPTY_PATH is
    declined below ([statat_null_name]).  From v6.15 to v6.18.46 these
    functions change only in spelling: [SYSCALL_DEFINE4(newfstatat)]
    returns early on [unlikely(error)] from v6.16, [filename_lookup]
    takes a [const] root at v6.18.46, and [path_init] reads [fs->seq]
    with [read_seqbegin] from v6.17; [cp_new_stat], [vfs_fstatat],
    [vfs_statx], [statx_lookup_flags] and [getname_flags] are v6.15's
    text.

    THE SUCCESS ARM IS THE RESOLVED ENTRY'S DELIVERY.  A successful call
    writes 128 bytes of [struct stat] (riscv64 has no [asm/stat.h] of
    its own, so it uses the asm-generic layout,
    include/uapi/asm-generic/stat.h): st_dev at 0, st_ino at 8, st_mode
    at 16, st_nlink at 20, st_uid at 24, st_gid at 28, st_rdev at 32,
    st_size at 48, st_blksize at 56, st_blocks at 64, and three
    timestamps with their nanosecond halves from 72 to 120.  All 128
    bytes are written: [cp_new_stat] zeroes its stack copy through
    [INIT_STRUCT_STAT_PADDING] (which riscv64 leaves at the generic
    [memset], as only x86 overrides it) and hands the whole thing to
    [copy_to_user] in one call, so the padding is delivered too.

    [Fs.resolve] finds the entry, and [stat_entry_spec] delivers it with
    the same machinery [fstat] uses for a descriptor on it: the padding
    pinned to zero; the type asserted for every kind; [st_size] for a
    file, a device and a link; the link count for a file and a folder;
    [st_rdev] and [st_blocks] for the two devices; and what tmpfs and
    ramfs fix of the other kinds ([Uapi.stat_reg_fixed],
    [Uapi.stat_dir_fixed], [Uapi.stat_lnk_fixed]): [st_rdev] 0 for a
    file, a folder and a link, the page size as [st_blksize] for every
    kind, a folder's [st_blocks] 0, and a link's whole [st_mode]
    S_IFLNK|0777 and its [st_blocks], 0 for a body kept inline and 0 or
    8 for one in a page.  Of the members [Fs] cannot supply, the stable
    ones ([Uapi.stat_stable_eqb]: the device, inode number, mode, ids,
    [st_rdev] and block size, where not asserted) and those
    [stat_pin_held] names (a device node's link count and timestamps, a
    link's link count, [st_blocks], [st_mtime] and [st_ctime], a
    folder's [st_blocks]) are chosen at the first stat of an identity
    ([State.StatId]: a file's inode, a folder's, a device node's or a
    link's key) and held, except that a regular file's set-id bits may
    be shown cleared, and that the removal of a link name releases every
    link's count and [st_ctime], and nothing else, until the link's next
    stat pins them again ([State.statpins_release_links]); the rest are
    chosen afresh at every call: a file's block count and timestamps, a
    folder's [st_size] and timestamps, and a link's [st_atime].  On
    every failing arm [SYSCALL_DEFINE4(newfstatat)] reaches
    [cp_new_stat] only once [vfs_fstatat] has returned 0, so the kernel
    leaves [statbuf] untouched, and a bad [statbuf] with an absent file
    really is -ENOENT: the -EFAULT of a bad [statbuf] is
    [copy_to_user]'s, raised after the stat has already succeeded, and
    it is the LAST thing that can go wrong.

    ORDER.  Chronologically the kernel copies the pathname in first
    ([vfs_fstatat] calls [getname_flags] before [vfs_statx]), but a
    failure there is only STASHED as an [ERR_PTR]; [vfs_statx] tests the
    flags before it hands that stashed value to [filename_lookup], which
    is what finally returns it.  So the priority of the errno the caller
    actually sees is: the flag word first ([flags & ~(AT_SYMLINK_NOFOLLOW
    | AT_NO_AUTOMOUNT | AT_EMPTY_PATH | AT_STATX_SYNC_TYPE)] is -EINVAL),
    then the pathname, then the dirfd ([path_init] raises -EBADF only for
    a relative walk), then the file, then -EFAULT on [statbuf].  ONE
    SHAPE SKIPS THE FLAG TEST: under AT_EMPTY_PATH a NULL pathname or a
    NUL lead byte gives [getname_maybe_null] no name, and for a dirfd of
    0 or more [vfs_fstatat] returns [vfs_fstat] of that descriptor
    (fs/stat.c:372-373, Linux v6.18.46) without reaching [vfs_statx]'s
    flag test (:348-350), so an otherwise invalid flag word beside
    AT_EMPTY_PATH answers the descriptor's stat there, not -EINVAL.  The
    model declines both halves of that shape, the uninterpreted flag
    word and every dirfd but AT_FDCWD, so no answer here turns on it.
    This spec follows that priority exactly, with DECLINING substituted
    for the -EINVAL: a flag word the model has not interpreted is one it
    cannot judge the call from.

    Declining rather than asserting -EINVAL costs precision, and nothing
    else, in two kinds of call.  Every flag word Linux refuses gives up
    its -EINVAL, [vfs_statx]'s test (fs/stat.c:348-350, Linux v6.18.46),
    which is Linux's certain answer there and is declined here.  And
    every word Linux accepts but the model does not interpret
    (AT_NO_AUTOMOUNT, the AT_STATX_SYNC_TYPE bits) gives up every answer
    under it: [newfstatat(AT_FDCWD, <a 4096-byte path>, buf,
    AT_NO_AUTOMOUNT)] is -ENAMETOOLONG on Linux, and here it is
    declined.  Asserting -EINVAL instead would be a confident wrong
    answer on every flag word Linux ACCEPTS.  The flag arrives already
    truncated to 32 bits ([Syscall.flag32]), so the high half of the
    register is not part of the comparison.

    Under a modeled flag word the pathname fetch comes first, with all
    three of [getname_flags]'s answers — -ENAMETOOLONG for no NUL within
    PATH_MAX, -EFAULT for an unmapped byte, and the string otherwise.
    WITHOUT AT_EMPTY_PATH the empty pathname is its -ENOENT
    ([getname_flags] returns that unless LOOKUP_EMPTY is set, and a flag
    word without AT_EMPTY_PATH does not set it at either end of the
    window: v6.10-v6.12 route through [getname_statx_lookup_flags],
    which sets LOOKUP_EMPTY only for AT_EMPTY_PATH, and from v6.13
    [vfs_fstatat] calls [getname_maybe_null], which for a
    non-AT_EMPTY_PATH flag word is plain [getname] — that is,
    [getname_flags] with no flags at all; the successor
    [statx_lookup_flags] dropped the LOOKUP_EMPTY arm entirely).  UNDER
    AT_EMPTY_PATH the empty pathname is no error: [__getname_maybe_null]
    returns no name for a NUL lead byte (fs/namei.c:233-234, Linux
    v6.18.46), and [vfs_fstatat] then stats the descriptor for a dirfd
    of 0 or more, or hands the missing name to [vfs_statx], which for
    AT_FDCWD stats the working folder (fs/stat.c:370-375, Linux
    v6.18.46); [newfstatat_body_spec] answers the working folder's stat
    and declines every other dirfd.  The fetch's errnos preempt the
    dirfd, so they are answered before it is looked at, exactly as
    [Open.openat_spec] does.

    Then the dirfd: only AT_FDCWD is modeled, and any other is
    [unmodeled] — asserting an errno for a directory the model cannot
    name would reject a conforming trace.  [dirfd] arrives already
    truncated to 32 bits (see [Syscall.fd32]), so
    [newfstatat(2^32 - 100, ...)] names the working directory as Linux
    does.

    Then the path, through [Fs.resolve]: "." and ".." are ordinary
    components of the walk, a found entry is delivered
    ([stat_entry_spec]), an absent last component or prefix is -ENOENT,
    a non-directory met by a prefix or by a trailing separator is
    -ENOTDIR (the walk sets LOOKUP_DIRECTORY for a LAST_NORM component a
    separator follows, fs/namei.c:2649-2650, :2685-2687), the 41st link
    is -ELOOP, and "proc" or "sys" at the root decline.

    THE WALK'S OWN REFUSALS.  Linux can fail the call during resolution
    with [may_lookup]'s -EACCES (fs/namei.c:2466-2469, Linux v6.18.46)
    and with the -ENOMEM of the walk's allocations, ahead of every
    answer the walk leads to, the success included; both stand beside
    those answers ([Fs.Namei.walk_refusals], in [newfstatat_core_spec]).
    [getname_flags]'s own -ENOMEM ([__getname], fs/namei.c:146-148, and
    the re-copy's [kzalloc], 189-193) stands beside every answer, the
    fetch's three included, with the copy-in made when its allocation
    failed ([Fs.Namei.getname_refusals], in [newfstatat_spec]) — on
    every call whose fetch reaches [getname_flags]
    ([statat_getname_runs]).  Under AT_EMPTY_PATH that copy-in includes
    the lead byte [__getname_maybe_null] loaded first
    ([statat_lead_reads]), so [__getname]'s -ENOMEM reads one byte
    there and none without the flag.  Under AT_EMPTY_PATH a faulting or
    NUL lead byte is answered by [__getname_maybe_null] before any
    allocation, so there neither refusal stands: such a call is answered
    by [newfstatat_body_spec] alone.

    THE COPY-IN LEDGER.  The pathname fetch is a real
    [strncpy_from_user] of user memory, so it is recorded as one, with
    the same [record_copyins] wrapper and the same range
    [Open.openat_spec] uses: [cstr_access_len_aux (in_mem i) pathp
    path_max], the bytes through the first NUL, the first unreadable
    byte, the last byte below [TASK_SIZE], or PATH_MAX.  The wrapper
    sits OUTSIDE the flag test, so every
    arm the spec ANSWERS carries the ledger — the [CstrFault] one
    included, where [cstr_access_len_aux] counts the faulting byte
    itself (a [None] byte is 1, [State.v]): the kernel attempted that
    byte, and an immediate -EFAULT is a fetch that happened, not one
    that did not.  The other [CstrFault], the walk reaching [TASK_SIZE],
    counts nothing at [TASK_SIZE]: [strncpy_from_user]'s clamp ends the
    scan below it, so that byte is never fetched ([State.read_cstr_aux]).
    The declining arms cost nothing, because
    [Syscall.record_copyins_unmodeled] carries [unmodeled] through the
    wrapper untouched — so wrapping the uninterpreted flag word does not
    disturb the ORDER argument above.

    This is not bookkeeping.  [State.syscall_effect_accesses] is
    [eff_copyins] followed by the write ranges, and [Run.v]'s
    [sstep_syscall] charges exactly that list against the process's
    backing budget.  An empty ledger here would charge NOTHING for a
    page the model holds lazily and the machine overlay ([Run.v]'s
    [in_mem]) answers from anyway — an under-charge, which is the
    direction that grants an allocation the kernel refuses.  The ledger
    is short by up to 7 bytes, because [strncpy_from_user] reads a word
    at a time, and this spec inherits that bound rather than restating it.

    SHARED WITH [Open.openat_spec], AND DELIBERATELY LEFT INLINE.  The
    three steps between the flag word and the path — [read_cstr]'s three
    answers, the empty pathname's -ENOENT, and the AT_FDCWD gate — are
    the same sequence [Open.openat_spec] runs, wrapped in the same
    ledger, and those two specs are its only copies (mirrored once more
    by [Open.check_openat] and [Stat.check_newfstatat], whose soundness
    and completeness lemmas discharge by destructing [read_cstr]
    directly).  They are kept side by side rather than hoisted into a
    shared combinator: what repeats is five lines of already shared
    primitives ([read_cstr], [Fs.path_eqb], [Uapi.AT_FDCWD32],
    [err_ret]) under one already shared wrapper
    ([Syscall.record_copyins]), and hoisting them would have to thread a
    continuation through both checkers, where the arm-for-arm mirroring
    is what keeps those four lemmas short.  The price is that any later
    correction to this precedence or to the recorded range must be made
    in both places.  ([getname_flags]'s own -ENOMEM is not repeated: it
    is [Fs.Namei.getname_refusals]', one definition every pathname arm
    applies.)  [readlinkat_spec]
    above is the third call site: it runs the same five lines, so the
    three of them repeat one shape.  It is still not extracted, for the
    reason above — threading a continuation through three checkers costs
    more than it saves while the mirroring is what keeps their verdict
    lemmas short.  What the three DO share already is the walk:
    [newfstatat_body_spec] and [readlinkat_spec] answer the trailing
    separator through [Fs.resolve] alone, which is what stops them from
    drifting. *)
Definition newfstatat_body_spec (i : SyscallInput) (m : Model)
    (dirfd pathp statbuf flag : word) : Sys SyscallEffect :=
    (* [getname_flags()]: all three of its answers are real errnos, and
       all three preempt the dirfd. *)
    match read_cstr (in_mem i) pathp with
    | CstrTooLong => err_ret ENAMETOOLONG        (* no NUL within PATH_MAX *)
    | CstrFault => err_ret EFAULT                (* unmapped byte in the path string *)
    | CstrOk p =>
        if path_eqb p [] then
          if negb (statat_empty_path flag) then err_ret ENOENT
            (* [getname_flags] without LOOKUP_EMPTY, fs/namei.c:167-171 *)
          else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
            (* [vfs_fstatat] stats the descriptor itself
               (fs/stat.c:372-373): declined here *)
          else
            (* AT_FDCWD: the empty name walks to the working folder
               (fs/namei.c:668, :2590-2604, :2455-2458) *)
            match Fs.fs_lookup (m_fs m) (m_cwd m) with
            | Some e => stat_entry_spec (m_cwd m) e statbuf
            | None => unmodeled
            end
        else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled  (* unmodeled dirfd: fail closed *)
        else
          let '(r, _, _) := Fs.resolve (statat_walk_mode flag) (m_fs m) (m_cwd m) p in
          match r with
          | Fs.RFound k e => stat_entry_spec k e statbuf
          | Fs.RMissing _ _ => err_ret ENOENT
          | Fs.RNotDir _ => err_ret ENOTDIR
          | Fs.RAbsent _ => err_ret ENOENT
          | Fs.RLoop => err_ret ELOOP            (* the 41st link, fs/namei.c:1878-1879 *)
          | Fs.ROutside => unmodeled             (* "proc" and "sys" at the root *)
          | Fs.RParent _ _ => unmodeled          (* the parent and [O_CREAT] ends only *)
          end
    end.

(** The flag word, then the NULL name under AT_EMPTY_PATH, then the
    fetch.  A call whose fetch reaches [getname_flags]
    ([statat_getname_runs]) admits beside every answer past it the
    walk's own refusals ([Fs.Namei.walk_refusals]), on a nonempty name.
    Under AT_EMPTY_PATH a lead byte that faults or is NUL is answered
    before anything is allocated or walked, so it admits none. *)
Definition newfstatat_core_spec (dirfd pathp statbuf flag : word)
    : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  (* a flag word the model does not interpret: decline, never assert *)
  if negb (modeled_statat_flags flag) then unmodeled
  (* NULL under AT_EMPTY_PATH: Linux reads no byte and stats the
     descriptor or the working folder ([statat_null_name]); declined *)
  else if statat_null_name pathp flag then unmodeled
  else if statat_getname_runs i pathp flag then
    walk_refusals (statat_walk_mode flag) pathp
      (newfstatat_body_spec i m dirfd pathp statbuf flag)
  else newfstatat_body_spec i m dirfd pathp statbuf flag.

(** The pathname fetch, recorded.  In Linux v6.18.46 [vfs_fstatat]
    (fs/stat.c) fetches the pathname in the initializer of its [name]
    local, before it calls [vfs_statx] at all.  Its callee is
    [getname_maybe_null] (include/linux/fs.h); without AT_EMPTY_PATH
    that is plain [getname] — which is [getname_flags] with no flags at
    all (fs/namei.c) — and with it [__getname_maybe_null], whose
    [get_user] of the lead byte comes first ([statat_getname_runs]);
    [getname_flags]'s [strncpy_from_user] is the byte fetch itself.
    Every outcome the core spec answers is downstream of that fetch, so
    the range belongs to all of them; see THE COPY-IN LEDGER above.  The
    ORDER paragraph above answers a different question — which errno the
    caller finally sees, where the flag word still wins.

    [getname_flags]' own -ENOMEM is not downstream of the whole fetch:
    its allocations fail before the copy is done, so it stands outside
    the ledger ([Fs.Namei.getname_refusals]), on a call whose fetch
    reaches [getname_flags] at all ([statat_getname_runs]), after the
    lead byte's load under AT_EMPTY_PATH ([statat_lead_reads]). *)
Definition newfstatat_spec (dirfd pathp statbuf flag : word)
    : Sys SyscallEffect :=
  i <- input ;;
  if statat_getname_runs i pathp flag then
    getname_refusals (statat_lead_reads pathp flag) pathp
      (record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
         (newfstatat_core_spec dirfd pathp statbuf flag))
  else
    record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
      (newfstatat_core_spec dirfd pathp statbuf flag).

(** [fstat fd statbuf] — [newfstatat]'s descriptor-only sibling, and the
    number riscv64 musl really reaches for [fstat()].  Syscall 79 is
    modeled above, by [newfstatat_spec]; nothing below leans on it.
    KERNEL SCOPE: the supported kernels, v6.16 to v6.18.46 (SCOPE.md),
    read over Linux v6.10-v6.15, fs/stat.c, [SYSCALL_DEFINE2(newfstat)],
    [cp_new_stat] and [vfs_fstat].  The first two are byte-identical
    across that range and its stable branches; [vfs_fstat] is not, and
    where it moved is recorded below.  [cp_new_stat] and [vfs_fstat] are
    v6.15's text through v6.18.46, and from v6.16
    [SYSCALL_DEFINE2(newfstat)] returns [vfs_fstat]'s error before it
    calls [cp_new_stat] instead of testing [!error] around the call: the
    two steps below, in the same order.

    riscv64 has no [__NR_fstat] of its own, but WHERE it inherits 80
    changed inside the window, so the citation is two.  Through v6.10 it
    is the generic table's
    [__SC_3264(__NR3264_fstat, sys_fstat64, sys_newfstat)]
    (include/uapi/asm-generic/unistd.h), resolving to [sys_newfstat]
    because [__BITS_PER_LONG] is 64.  From v6.11 riscv generates its
    table instead, and the entry is [80 64 fstat sys_newfstat] in
    scripts/syscall.tbl.  The [64] on that line is one of the ABI tokens
    scripts/Makefile.asm-headers contributes ([syscall_abis_64 +=
    common,64]); arch/riscv/kernel/Makefile.syscalls appends only
    [riscv], [rlimit] and [memfd_secret] to the same variable, so it is
    not where the [64] comes from.  Either way the definition is
    reached because riscv64 defines [__ARCH_WANT_NEW_STAT], which is the
    only guard on it — the [__ARCH_WANT_STAT64] one nearby covers
    [newfstatat], not this.

    THE SPEC IS THE ORDER, AND THE ORDER IS TWO STEPS:

      SYSCALL_DEFINE2(newfstat, unsigned int, fd, struct stat __user *, statbuf)
        error = vfs_fstat(fd, &stat);        <- -EBADF here, WRITING NOTHING
        if (!error) error = cp_new_stat(&stat, statbuf);

    Everything this spec answers is the first line, and everything it
    declines is the second.  [vfs_fstat] resolves the descriptor before
    it looks at anything else and returns -EBADF when the process does
    not hold it, so a call that names a closed fd AND a bad [statbuf] is
    -EBADF and never -EFAULT: [cp_new_stat], which is where a bad
    [statbuf] would be noticed, has not run.  That is the whole of the
    -EBADF arm, and on it the pointer is never read and never written.

    [vfs_fstat] is REWRITTEN TWICE inside the version window and the
    -EBADF survives all three spellings, which is why the arm can be
    asserted over the whole of it: v6.10-v6.11 take [fdget_raw] and test
    [!f.file], v6.12 keeps [fdget_raw] and tests [!fd_file(f)], and
    v6.13 onward is [CLASS(fd_raw, f)(fd)] with [fd_empty(f)].  The
    guard class expands to the same [fdget_raw], and its [EMPTY_FD] is
    returned exactly where the older code left [.file] NULL.  Neither
    rewrite was backported, so a stable branch carries its series' form.

    THE DESCRIPTOR IS 32 BITS, and the truncation is the syscall
    wrapper's rather than the hardware's: [fd] is declared [unsigned
    int], [__SC_LONG] widens it to a [long] on the way in, and
    [__SC_CAST] discards the high half at the call
    (arch/riscv/include/asm/syscall_wrapper.h, include/linux/syscalls.h).
    [Syscall.fd32] is that cast.  Two consequences it is worth being
    able to read off this spec: a register of all ones is fd -1 and
    -EBADF, and a register of 2^32 is fd ZERO — a live descriptor, not a
    rejected one — so the truncation can turn a nonsense argument into a
    call this spec declines rather than answers.

    THE SUCCESS ARM IS MODELED, FOR THE FOUR FILE KINDS, THE DIRECTORY
    AND THE TWO DEVICE KINDS AND NO OTHER, and it is [fstat_file_spec]
    above (and its twins [fstat_dir_spec] and [fstat_chrdev_spec])
    rather than part of this definition: [vfs_fstat]'s -EBADF is what
    THIS spec answers, and everything a success delivers is
    [cp_new_stat]'s.  The split follows the kernel's two lines, and it
    is why this spec takes [statbuf] — the pointer really is read on
    the arms that succeed.

    A FILE NO NAME REACHES ANY MORE answers like any other: the
    descriptor holds its inode, and [st_nlink] is the inode's count,
    0 once the last name the image shows is gone and no name outside it
    remains ([Fs.fs_ino_nlink]).

    WHAT THE ARM COSTS AND WHAT IT BUYS is argued on
    [fstat_file_spec].  In one line: S_IFREG, [st_size] and [st_nlink]
    are asserted off the inode, the twenty bytes of padding are pinned
    to zero, the stable members are chosen once per inode and then held
    fixed, so a second [fstat] of one file cannot report a different
    inode, and [st_blocks] and the timestamps are chosen afresh at every
    call.

    THE SHAPE A REAL PROGRAM SPENDS ON IT is musl's [__map_file]
    (src/time/__map_file.c, called from src/time/__tz.c), which opens a
    TZif file, fstats it for [st_size] alone, and maps exactly that many
    bytes.  It is worth naming because it is CHECKABLE FROM THIS TREE
    that the shape leaves the modeled surface on the FAR side of the
    fstat, whoever issues it: the map is file-backed MAP_SHARED, where
    all three of [Mmap.mmap_modeled_b], [Mmap.mmap_noaccess_b] and
    [Mmap.mmap_fixed_noaccess_b] require MAP_PRIVATE|MAP_ANONYMOUS, and
    [Mmap.mmap_spec]'s file-backed branch declines every
    MAP_ANONYMOUS-clear call before a shape is matched at all.  Its
    open — O_RDONLY|O_CLOEXEC|O_NONBLOCK — is ADMITTED
    ([Open.open_ignored_flags] strips O_NONBLOCK alongside O_CLOEXEC and
    O_LARGEFILE), so the near side carries no decline.  The fstat itself
    is answered; the mmap after it is not, which is why this
    arm buys no additional COVERED RUN on that path and is not defended
    on those grounds.

    That this is the ONLY [fstat] a [dropbear -i] session issues is an
    OUT-OF-TREE MEASUREMENT and is not a checked fact: a qemu-riscv64
    -strace of a static riscv64-musl [dropbear -i],
    404 syscalls through KEX, auth and exit, whose log is not committed
    here.  It corroborates the paragraph above rather than carrying it —
    re-measure before relying on it.

    THE -EBADF IS ASSERTED WITH NO ALTERNATIVE, and that is exactness
    rather than an approximation: [vfs_fstat] resolves the descriptor
    before anything else can fail, so a call naming a closed fd AND a bad
    [statbuf] is -EBADF and never -EFAULT.  [cp_new_stat] has not run.
    The errnos reachable past an OPEN descriptor are
    [fstat_file_spec]'s subject. *)

(** The null device: S_IFCHR, [st_rdev] 1:3, zero size and blocks, the
    page size as [st_blksize], under the pin of the node at the device's
    own name when that is the image's one null-device node, and of the
    descriptor [fd] otherwise ([fstat_devfd_spec]). *)
Definition fstat_devnull_spec (fd statbuf : word) : Sys SyscallEffect :=
  fstat_devfd_spec DevNull devnull_path stat_devnull_ok fd statbuf.

(** The random device: S_IFCHR, [st_rdev] 1:9, zero size and blocks
    ([Uapi.stat_urandom_ok]), on the assumption
    [Open.open_urandom] states — an [Fs.EDev DevUrandom] is the
    random device, major 1 minor 9.  [cp_new_stat] (fs/stat.c,
    v6.18.46) reads the same inode members it reads for /dev/null; the
    zero [st_size] and [st_blocks] rest on the same premise about a
    node nothing ever resized.  The pin is the null device's rule
    ([fstat_devfd_spec]). *)
Definition fstat_urandom_spec (fd statbuf : word) : Sys SyscallEffect :=
  fstat_devfd_spec DevUrandom urandom_path stat_urandom_ok fd statbuf.

(** THE MATCH BELOW IS TOTAL ON [FdEntry] ON PURPOSE, with no wildcard.
    A new constructor is a new kind of file, and whoever adds it must
    decide what [fstat] says about it; the non-exhaustive-match error is
    the only thing that makes them.

    THE FOUR FILE KINDS SHARE ONE ANSWER because they share one inode:
    [FdFile], [FdFileW], [FdFileA] and [FdFileRW] differ in how the
    descriptor was opened and in nothing [cp_new_stat] reads.  Neither
    [f_mode] nor [f_flags] is a member of [struct stat], so HOW A
    DESCRIPTOR WAS OPENED is not something a stat can report; and the
    model's own difference between them — which of [ReadWrite]'s arms
    will serve the descriptor — is not a member either.  Two of them are
    worth naming, and for one reason: [FdFileA]'s writes land at the
    file's end, and [FdFileRW]'s single shared [f_pos] means a read
    moves the offset the next write lands at, so in both the [st_size]
    moves under the descriptor exactly as [FdFileW]'s does.  That is
    what the ONE size obligation below is: it is a function of the
    CURRENT contents rather than of the descriptor, which is why the
    same one serves all four.

    /dev/null ANSWERS TOO, through [fstat_devnull_spec]: the model minted
    that descriptor knowing it is the null device, so the type bits and
    the device number are asserted where the file arm can only imply.
    /dev/urandom answers the same way through [fstat_urandom_spec], and
    a directory through [fstat_dir_spec] (S_IFDIR asserted off the entry
    kind).

    THE OTHER KINDS STILL DECLINE, and they are not equally far from an
    answer:

      - [FdChannel] — the type bits alone are undecidable.  A channel is
        the model's one name for a pipe, a socket and a terminal (see
        [FdChannel]'s own note), so S_IFIFO, S_IFSOCK and S_IFCHR are
        all live and nothing in the model chooses between them.  A
        [choose] over the type would not fix it: the pin makes two stats
        agree with each other, not with the kernel, and there is nothing
        here for the size obligation to bite on.
      - [FdSocket] — the BEST-DETERMINED of them.  [sock_alloc]
        (net/socket.c, v6.18.46) sets [i_mode = S_IFSOCK | S_IRWXUGO] —
        a CONSTANT — and [i_uid]/[i_gid] from
        [current_fsuid]/[current_fsgid], which [State.Creds] argues
        coincide with euid/egid here.  [sockfs_inode_ops] carries no
        [.getattr], so [vfs_getattr_nosec] fills the rest with
        [generic_fillattr] out of pseudo-filesystem constants:
        [inode_init_always] (fs/inode.c) leaves [i_nlink] 1, [i_rdev] 0,
        [i_size] 0 and [i_blocks] 0, and [i_blkbits] is
        [pseudo_fs_fill_super]'s PAGE_SHIFT (fs/libfs.c).  What is out of
        reach is [st_ino] ([get_next_ino]), [st_dev] (the sockfs
        superblock's anonymous device, from [set_anon_super]) and the
        three timestamps.  Those are the members the machinery above
        exists for, so this arm is a matter of WRITING IT rather than
        of the model lacking a mechanism; it is left declined here
        because the fields it would pin are kernel constants that want
        their own citations, not because it cannot be done.
      - [FdPipe] — S_IFIFO is known and the rest is not, and a pipe's
        [st_size]/[st_blocks] are not even the queue's length, so
        nothing plays the role [Fs]'s contents play above.

    WHAT IS NOT REACHABLE PAST THE ARMS ASSERTED.  On an open descriptor
    Linux can still fail where a filesystem's own [.getattr] returns an
    error.  [vfs_getattr] also runs [security_inode_getattr], but the
    configuration of record builds no LSM (SCOPE.md), so that hook is
    the stub of include/linux/security.h that answers 0 and no LSM
    refusal is an answer a supported kernel gives.
    [cp_new_stat]'s five -EOVERFLOW tests cannot fire on riscv64: four
    are false because every destination member is at least as wide as
    its [kstat] source, and the [MAX_NON_LFS] one is inside
    [#if BITS_PER_LONG == 32]. *)
Definition fstat_spec (fd statbuf : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF          (* [vfs_fstat]'s own answer, before [statbuf] is touched *)
  | Some (FdChannel _) => unmodeled  (* pipe, socket or terminal: even the type bits are undecided *)
  | Some (FdFile i _)  => fstat_file_spec i statbuf   (* [cp_new_stat] over the file's inode *)
  | Some (FdFileW i _) => fstat_file_spec i statbuf   (* the same inode, opened for writing *)
  | Some (FdFileA i _) => fstat_file_spec i statbuf   (* and again in append mode *)
  | Some (FdFileRW i _) => fstat_file_spec i statbuf
                                     (* and again opened O_RDWR.  Same inode, and the
                                        read-write kind's SINGLE SHARED [f_pos] means a
                                        read moves the offset the next write lands at, so
                                        its [st_size] moves under it exactly as
                                        [FdFileW]'s does -- the size obligation is a
                                        function of the CURRENT contents, not of the
                                        descriptor ([cp_new_stat]/[generic_fillattr],
                                        fs/stat.c, v6.18.46, 1f99e9ab748f) *)
  | Some (FdDir k)     => fstat_dir_spec k statbuf
                                     (* the directory the descriptor names.  S_IFDIR and
                                        the link count are asserted off the entry kind
                                        and the image, the stable members and
                                        [st_blocks] are chosen once and held under the
                                        key, which is what the pin is for, and
                                        [st_size] and the timestamps are chosen afresh
                                        at every call ([fstat_dir_spec]) *)
  | Some (FdSocket _)  => unmodeled  (* mode/uid/gid are known; ino, dev and the timestamps are not *)
  | Some (FdStream _ _ _) => unmodeled  (* the [FdSocket] case: S_IFSOCK is known; the sockfs
                                        inode number and the timestamps are not *)
  | Some (FdDgram _)   => unmodeled  (* the [FdSocket] case again: another sockfs inode *)
  | Some (FdEventfd _) => unmodeled  (* the shared anonymous inode: [alloc_anon_inode]
                                        (fs/libfs.c, v6.18.46) gives it mode 0600 with no
                                        type bits, but its inode number and timestamps are
                                        the boot's, not the model's *)
  | Some (FdPipe _ _)  => unmodeled  (* S_IFIFO is known; a pipe's [st_size]/[st_blocks] are
                                        not even the queue's length, so nothing plays the
                                        role the file contents play above *)
  | Some (FdDevNull _ _) => fstat_devnull_spec fd statbuf
                                     (* the null device: S_IFCHR, [st_rdev] 1:3, [st_size]
                                        and [st_blocks] 0 asserted ([Uapi.stat_devnull_ok]),
                                        the rest pinned under [Uapi.devnull_path] when that
                                        node is the image's one, and under the descriptor
                                        otherwise ([fstat_devfd_spec]) *)
  | Some (FdUrandom _ _) => fstat_urandom_spec fd statbuf
                                     (* the random device: S_IFCHR, [st_rdev] 1:9
                                        ([Uapi.stat_urandom_ok]), the rest pinned under
                                        [Uapi.urandom_path] on the same rule *)
  end.

