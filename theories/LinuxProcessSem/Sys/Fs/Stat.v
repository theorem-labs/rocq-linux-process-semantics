(** * LinuxProcessSem.Sys.Fs.Stat — readlinkat (78), newfstatat (79), fstat (80)

    This file answers to Linux [fs/stat.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** [readlinkat dirfd path buf bufsiz]: the modeled file system has NO
    symlinks (Fs.v: paths are uninterpreted names, no symlink objects),
    so no path a program can name resolves to one — and readlink(2) on
    anything that is not a symlink is -EINVAL.

    The DIRFD is the one argument that is checked, and only AT_FDCWD is
    modeled: [do_readlinkat] resolves the dirfd through [fdget_raw]
    inside path resolution, so [readlinkat(999, "f", buf, 64)] is -EBADF
    on Linux — asserting -EINVAL there would
    REJECT a conforming trace, which is worse than declining.  Any other
    dirfd therefore is [unmodeled], fail closed, exactly as openat's does.
    [dirfd] arrives already truncated to 32 bits (see [Syscall.fd32]), so
    [readlinkat(2^32 - 100, ...)] names the working directory as Linux
    does.

    Everything under AT_FDCWD is the deterministic -EINVAL.  No other
    argument is validated.  ORDERING CHOICE: the kernel resolves the
    path BEFORE touching the output buffer, so the path-based -EINVAL
    wins over any buffer problem — the buffer is deliberately NOT
    checked against [in_wmem] (a successful readlinkat never happens, so
    no byte is ever delivered).

    APPROXIMATION (deliberate).  Under AT_FDCWD the path itself
    is still not interpreted, so a missing path (-ENOENT on Linux) and a bad
    path pointer (-EFAULT) are both coarsened to -EINVAL, and the [int bufsiz]
    gate Linux applies BEFORE path resolution ([bufsiz <= 0] is -EINVAL) is
    subsumed rather than modeled.  Those are FALSE REJECTIONS of conforming
    traces, not fail-closed gaps: no modeled binary consumes readlinkat's
    result, and interpreting the path here would duplicate openat's path-errno
    machinery. *)
Definition readlinkat_spec (dirfd : word) : Sys SyscallEffect :=
  if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled   (* unmodeled dirfd: fail closed *)
  else err_ret EINVAL.

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

    The two modeled flag words are also indistinguishable IN the model:
    the interpreted file system has no symlink objects (Fs.v), so
    following one is never different from not following one.

    Everything else — AT_EMPTY_PATH, AT_NO_AUTOMOUNT, the
    AT_STATX_SYNC_TYPE bits, and every word Linux answers -EINVAL for —
    is unmodeled and DECLINED, not answered.  Declining costs precision
    and nothing else: see the ORDER paragraph at [newfstatat_spec]. *)
Definition modeled_statat_flags (flag : word) : bool :=
  let fl := bv_unsigned flag in
  Z.eqb fl 0 || Z.eqb fl AT_SYMLINK_NOFOLLOW.

(** [newfstatat]'s procfs shape: a RELATIVE name and a [dirfd] that is an
    O_PATH descriptor on a procfs name ([State.OProcPath]), which
    [path_init] (fs/namei.c) starts the walk from ([CLASS(fd_raw, f)]
    accepts an O_PATH file).  An absolute name ignores [dirfd] and is
    left to the arms below, which decline it. *)
Definition newfstatat_proc_dir (fds : list (word * FdEntry)) (dirfd : word)
    (p : path) : bool :=
  match p, fd_lookup fds dirfd with
  | b :: _, Some (FdOpaque (OProcPath _)) => negb (bv_eqb b path_slash_byte)
  | _, _ => false
  end.

(** What [cp_new_stat] (fs/stat.c, read at v6.18.44; identical at
    v6.18.46) settles for EVERY object: 128 bytes, and [__pad1],
    [__pad2] and [__unused4]/[__unused5] zero, because
    [INIT_STRUCT_STAT_PADDING] is a [memset] of the whole struct and no
    member assignment covers those bytes.

    NOT [Uapi.stat_buf_wf], whose [st_mode] must name one of the seven
    file types: a name under /proc can be a link to ANY open file
    ("/proc/self/fd/N"), and an anonymous inode has no type bits at all
    ([alloc_anon_inode], fs/libfs.c, read at v6.18.44: "Historically
    anonymous inodes don't have a type at all"), so that test would
    reject a real answer. *)
Definition stat_proc_buf_ok (bs : list byte) : bool :=
  (Nat.eqb (length bs) 128
   && Z.eqb (stat_field_le ST_PAD1_OFF 8 bs) 0
   && Z.eqb (stat_field_le ST_PAD2_OFF 4 bs) 0
   && Z.eqb (stat_field_le ST_UNUSED45_OFF 8 bs) 0)%bool.

(** [newfstatat(dirfd, name, statbuf, flag)] with [dirfd] an O_PATH
    descriptor on a procfs name and [name] relative
    ([newfstatat_proc_dir]), under the two flag words
    [modeled_statat_flags] admits: bubblewrap's
    [newfstatat(ns_fd, "net", &st, 0)] after
    [openat(proc_fd, "<pid>/ns", O_PATH)].

    KERNEL PATH, read at v6.18.44:
      fs/stat.c [SYSCALL_DEFINE4(newfstatat)], [vfs_fstatat],
        [vfs_statx], [cp_new_stat]: read at v6.18.44; identical at v6.18.46.
      fs/namei.c [path_init], [filename_lookup]: read at v6.18.44; identical at v6.18.46.

    The answer is an errno, or 0 with 128 bytes of the environment's
    choice at [statbuf].  [vfs_fstatat] walks the name from [dirfd]
    through procfs (the pid directories, [proc_ns_dir_lookup], the
    namespace links and their [ptrace_may_access] test) and asks the
    inode's [getattr] and the LSM's [inode_getattr] hook: an errno
    list for that is not one this model can defend, so every errno is
    admitted ([Syscall.errno_any]).  On success [cp_new_stat] fills the
    struct; the model holds no metadata for procfs, so the bytes are
    chosen, constrained only by what [cp_new_stat] settles for every
    object ([stat_proc_buf_ok]), and not pinned from one call to the
    next.  That is a PRECISION gap (SCOPE.md, "Known gaps in
    precision"): two stats of one namespace may report different
    inode numbers here.

    THE DESTINATION, in [cp_new_stat]'s order: [copy_to_user]'s
    [access_ok] refuses a range outside the user address space before a
    byte moves, and then every answer is an errno (the -EFAULT among
    them), so the arm admits [errno_any] there.  A range inside it but
    not wholly writable can take a partial [copy_to_user] that writes a
    prefix and answers -EFAULT, which this model has no form for, so
    that shape is declined as [fstat_file_spec] declines it.  A wholly
    writable range takes the errno or the delivery. *)
Definition newfstatat_proc_spec (statbuf : word) : Sys SyscallEffect :=
  i <- input ;;
  if negb (access_okb statbuf STAT_SIZE) then (e <- errno_any ;; err_ret e)
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => unmodeled      (* a partial [copy_to_user] then -EFAULT *)
    | Some _ =>
        alt (e <- errno_any ;; err_ret e)
            (bs <- choose (fun bs : list byte => stat_proc_buf_ok bs = true) ;;
             pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []))
    end.

(** [newfstatat dirfd path statbuf flag] — [stat]/[lstat] as modern libc
    issues them.  KERNEL SCOPE for everything below: Linux v6.10-v6.15,
    fs/stat.c, [SYSCALL_DEFINE4(newfstatat)] / [cp_new_stat], and
    fs/namei.c, [getname_flags] / [filename_lookup] / [path_init].
    [SYSCALL_DEFINE4(newfstatat)] and [cp_new_stat] are byte-identical
    across that range; [vfs_fstatat] and [vfs_statx] are not, and the
    part that moved is the reason AT_EMPTY_PATH is declined below.

    THE SUCCESS ARM IS NOT MODELED, AND CANNOT BE FROM WHAT [Fs] CARRIES.
    A successful call writes 128 bytes of [struct stat] (riscv64 has no
    [asm/stat.h] of its own, so it uses the asm-generic layout,
    include/uapi/asm-generic/stat.h): st_dev at 0, st_ino at 8, st_mode
    at 16, st_nlink at 20, st_uid at 24, st_gid at 28, st_rdev at 32,
    st_size at 48, st_blksize at 56, st_blocks at 64, and three
    timestamps with their nanosecond halves from 72 to 120.  All 128
    bytes are written: [cp_new_stat] zeroes its stack copy through
    [INIT_STRUCT_STAT_PADDING] (which riscv64 leaves at the generic
    [memset], as only x86 overrides it) and hands the whole thing to
    [copy_to_user] in one call, so the padding is delivered too.

    The interpreted file system is a map from path to CONTENTS (Fs.v)
    and carries none of that — no file type, no permission bits, no
    owner, no inode, no device, no link count, no timestamps.  Of the
    128 bytes only st_size follows from what [Fs] holds — and the
    S_IFMT type bits follow only from the premise named below, not from
    [Fs] at all.  A spec that answered the call would be inventing the
    rest, so every path that RESOLVES is [unmodeled]: fail closed.

    THE MACHINERY IS NOT WHAT IS MISSING — [fstat_file_spec] BELOW HAS
    IT.  That arm answers the same 128 bytes for a DESCRIPTOR: it pins
    the padding [cp_new_stat] clears, derives [st_size] under the
    kernel's own S_IFREG test rather than asserting the type, and
    chooses the members [Fs] cannot supply once per file and holds them
    fixed.  None of that needs a path.

    WHAT IS MISSING HERE IS THE RESOLUTION.  This spec reaches its file
    through [fs_lookup] on an uninterpreted pathname, and the same flat
    namespace that makes it answer -ENOENT for "f/x" and ".." is what a
    success arm would have to resolve first — and that is a change to
    [Fs] rather than to this spec.  The premise that every path names a
    regular file is the second half:
    [Open.openat_spec] admits a name the model has no type for, and a
    path-based stat meets that on its most ordinary input rather than
    behind a descriptor whose file the model has already been reading
    and writing.  Per-file metadata closes neither.

    WHAT IS MODELED is the failing side, which is exactly the part of
    the call that writes nothing: [SYSCALL_DEFINE4(newfstatat)] reaches
    [cp_new_stat] only once [vfs_fstatat] has returned 0, so on every
    arm below except one the kernel leaves [statbuf] untouched.  The
    exception is a name relative to an O_PATH descriptor on a procfs
    name ([newfstatat_proc_spec]), which answers a success with 128
    bytes of the environment's choice, and is the one reader of
    [statbuf].  (A bad [statbuf] with an absent file really is -ENOENT
    on Linux: the -EFAULT of a bad [statbuf] is [copy_to_user]'s, raised
    after the stat has already succeeded, and it is the LAST thing that
    can go wrong.)

    ORDER.  Chronologically the kernel copies the pathname in first
    ([vfs_fstatat] calls [getname_flags] before [vfs_statx]), but a
    failure there is only STASHED as an [ERR_PTR]; [vfs_statx] tests the
    flags before it hands that stashed value to [filename_lookup], which
    is what finally returns it.  So the priority of the errno the caller
    actually sees is: the flag word first ([flags & ~(AT_SYMLINK_NOFOLLOW
    | AT_NO_AUTOMOUNT | AT_EMPTY_PATH | AT_STATX_SYNC_TYPE)] is -EINVAL),
    then the pathname, then the dirfd ([path_init] raises -EBADF only for
    a relative walk), then the file, then -EFAULT on [statbuf].  This
    spec follows that priority exactly, with DECLINING substituted for
    the -EINVAL: a flag word the model has not interpreted is one it
    cannot judge the call from.

    Declining rather than asserting -EINVAL costs precision in one
    shape and nothing else: [newfstatat(AT_FDCWD, <a 4096-byte path>,
    buf, AT_NO_AUTOMOUNT)] is -ENAMETOOLONG on Linux, and here it is
    declined.  Asserting -EINVAL instead would be a confident wrong
    answer on every flag word Linux ACCEPTS.  The flag arrives already
    truncated to 32 bits ([Syscall.flag32]), so the high half of the
    register is not part of the comparison.

    Under a modeled flag word the pathname fetch comes first, with all
    three of [getname_flags]'s answers — -ENAMETOOLONG for no NUL within
    PATH_MAX, -EFAULT for an unmapped byte, and the string otherwise —
    and the empty pathname is its -ENOENT ([getname_flags] returns that
    unless LOOKUP_EMPTY is set, and no modeled flag word sets it at
    either end of the window: v6.10-v6.12 route through
    [getname_statx_lookup_flags], which sets LOOKUP_EMPTY only for
    AT_EMPTY_PATH, and from v6.13 [vfs_fstatat] calls
    [getname_maybe_null], which for a non-AT_EMPTY_PATH flag word is
    plain [getname] — that is, [getname_flags] with no flags at all; the
    successor [statx_lookup_flags] dropped the LOOKUP_EMPTY arm
    entirely).  All three preempt the dirfd, so they are answered before it
    is looked at, exactly as [Open.openat_spec] does.

    Then the dirfd: AT_FDCWD is modeled, and so is an O_PATH descriptor
    on a procfs name ([State.OProcPath]) under a RELATIVE name, which is
    [newfstatat_proc_spec]'s.  Any other is [unmodeled] — asserting an
    errno for a directory the model cannot name would reject a
    conforming trace.  [dirfd] arrives already truncated to 32 bits (see
    [Syscall.fd32]), so [newfstatat(2^32 - 100, ...)] names the working
    directory as Linux does.

    Then the path.  "." is a path the model resolves to a directory
    ([Uapi.dot_path]), and a directory's metadata is as absent from [Fs]
    as a file's, so it is declined too.  ".." is NOT declined here, and
    that is a divergence rather than a choice: this spec lets it fall
    through to [fs_lookup] and so answers a deterministic -ENOENT, an
    errno Linux never gives for "..", while [Open.openat_spec] and
    [Open.faccessat_spec] both resolve it ([Open.path_is_dirref]).  The
    same model therefore says two things about "..", one function call
    apart.  Any other path the
    file system does not hold is the real -ENOENT; any path it does hold
    would succeed on Linux, and is declined.

    APPROXIMATION 1 (deliberate, and the same shape as
    [Open.openat_spec]'s path-resolution arms).  The -ENOENT is asserted
    with no alternative, whereas Linux can fail the call before
    resolution with [getname_flags]'s own -ENOMEM.  This NARROWS the
    spec, so it admits nothing unsound; the cost is that a source and a
    target which diverge only under allocation failure are not
    distinguished.

    APPROXIMATION 2 (deliberate, inherited from [Fs]'s flat namespace,
    not introduced here).  Paths are uninterpreted byte strings with no
    directory structure, so "f/x" where "f" is a regular file is simply
    a key the map does not hold, and answers -ENOENT where Linux answers
    -ENOTDIR.  [Open.openat_spec] does not have this property on the
    same paths: it declines a pathname with a separator instead of
    answering off the map.  This spec answers, so the divergence is
    this spec's alone.
    It is a fact about [Fs], and fixing it means giving [Fs] directories.

    THE COPY-IN LEDGER.  The pathname fetch is a real
    [strncpy_from_user] of user memory, so it is recorded as one, with
    the same [record_copyins] wrapper and the same range
    [Open.openat_spec] uses: [cstr_access_len_aux (in_mem i) pathp
    path_max], the bytes through the first NUL, the first unreadable
    byte, or PATH_MAX.  The wrapper sits OUTSIDE the flag test, so every
    arm the spec ANSWERS carries the ledger — the [CstrFault] one
    included, where [cstr_access_len_aux] counts the faulting byte
    itself (a [None] byte is 1, [State.v]): the kernel attempted that
    byte, and an immediate -EFAULT is a fetch that happened, not one
    that did not.  The declining arms cost nothing, because
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
    is what keeps those four lemmas short.  The price is that
    APPROXIMATION 1, and any later correction to this precedence or to
    the recorded range, must be made in both places.  [readlinkat_spec]
    above is the third call site waiting to happen — it asserts -EINVAL
    without interpreting its pathname at all, and fixing it means
    reusing this machinery — so that is the point at which
    extracting a shared helper pays for itself. *)
Definition newfstatat_core_spec (dirfd pathp flag : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  (* a flag word the model does not interpret: decline, never assert *)
  if negb (modeled_statat_flags flag) then unmodeled
  else
    (* [getname_flags()]: all three of its answers are real errnos, and
       all three preempt the dirfd. *)
    match read_cstr (in_mem i) pathp with
    | CstrTooLong => err_ret ENAMETOOLONG        (* no NUL within PATH_MAX *)
    | CstrFault => err_ret EFAULT                (* unmapped byte in the path string *)
    | CstrOk p =>
        if path_eqb p [] then err_ret ENOENT     (* empty pathname: AT_EMPTY_PATH is not modeled *)
        else if negb (bv_eqb dirfd AT_FDCWD32) then
          (if newfstatat_proc_dir (m_fds m) dirfd p
           then newfstatat_proc_spec (in_arg i 2)
             (* relative to an O_PATH procfs descriptor; [statbuf] is a2,
                read from the input as [Kernel.Sys.prctl_spec] reads its
                extra arguments *)
           else unmodeled)                       (* unmodeled dirfd: fail closed *)
        else if path_eqb p dot_path then unmodeled  (* the working directory: no metadata in [Fs] *)
        else
        match fs_lookup (m_fs m) p with
        | None => err_ret ENOENT                 (* file absent: real -ENOENT, not a modeling gap *)
        | Some _ => unmodeled                    (* resolves: 128 bytes [Fs] cannot supply *)
        end
    end.

(** The pathname fetch, recorded.  In Linux v6.18.46 [vfs_fstatat]
    (fs/stat.c) fetches the pathname in the initializer of its [name]
    local, before it calls [vfs_statx] at all.  Its callee is
    [getname_maybe_null] (include/linux/fs.h); no flag word this spec
    answers sets AT_EMPTY_PATH, so that is plain [getname] — which is
    [getname_flags] with no flags at all (fs/namei.c) — and
    [getname_flags]'s [strncpy_from_user] is the byte fetch itself.
    Every outcome the core spec answers is downstream of that fetch, so
    the range belongs to all of them; see THE COPY-IN LEDGER above.  The
    ORDER paragraph above answers a different question — which errno the
    caller finally sees, where the flag word still wins. *)
Definition newfstatat_spec (dirfd pathp flag : word) : Sys SyscallEffect :=
  i <- input ;;
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (newfstatat_core_spec dirfd pathp flag).

(** [fstat fd statbuf] — [newfstatat]'s descriptor-only sibling, and the
    number riscv64 musl really reaches for [fstat()].  Syscall 79 is
    modeled above, by [newfstatat_spec]; nothing below leans on it.
    KERNEL SCOPE:
    Linux v6.10-v6.15, fs/stat.c, [SYSCALL_DEFINE2(newfstat)],
    [cp_new_stat] and [vfs_fstat].  The first two are byte-identical
    across that range and its stable branches; [vfs_fstat] is not, and
    where it moved is recorded below.

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

    THE SUCCESS ARM IS MODELED, FOR THE FOUR FILE KINDS AND FOR THE TWO
    DEVICE KINDS AND NO OTHER, and it is [fstat_file_spec] below (and
    its device twin [fstat_chrdev_spec]) rather than part of this
    definition: [vfs_fstat]'s -EBADF is what THIS spec answers, and
    everything a success delivers is [cp_new_stat]'s.  The split follows
    the kernel's two lines, and it is why this spec takes [statbuf] —
    the pointer really is read on the arms that succeed.

    WHAT THE ARM COSTS AND WHAT IT BUYS is argued on
    [fstat_file_spec].  In one line: [st_size] is derived under the
    kernel's own S_IFREG condition, the twenty bytes of padding are
    pinned to zero, and the other members are chosen once per file and
    then held fixed, so a second [fstat] of one file cannot report a
    different inode.

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
    - [st_size], AND ONLY IF THE KERNEL SAYS THE FILE IS REGULAR.
      [generic_fillattr] (fs/stat.c) copies [inode->i_size], which for a
      regular file is the file's length, and the model's length is the
      byte list [Fs] carries for the path this descriptor names.  The
      IMPLICATION is the whole of the claim
      ([Uapi.stat_size_ok]): the model does NOT know the file is
      regular, and a path it resolves can be one that Linux calls a
      character device, where the true answer is S_IFCHR with [st_size]
      0 against a nonempty byte list.  Asserting S_IFREG, or asserting the length outright,
      would REJECT that conforming trace.  Under the implication the
      model says nothing about it and still says something sharp about
      every file that really is regular — which is the same premise
      [ReadWrite.read_spec] already commits to on the same descriptor,
      and no wider.

    WHAT IT DOES NOT DETERMINE, and how it answers anyway.  The device,
    the inode, the mode's type and permission bits, the link count, the
    owning ids, [st_rdev], the block size, the block count and the three
    timestamp pairs have no source in [Fs], which is a map from path to
    CONTENTS.  Each is a [choose] — an environment value, not a zero.
    Zero-filling them would be a confident wrong answer of exactly the
    kind design priority 1 (README.md) forbids.

    FOUR MEMBERS ARE LEFT OUT OF THE PIN and are therefore re-chosen at
    every call: [st_blocks] and the three timestamp pairs.  That is
    over-admission — the model accepts a run in which two stats of one
    untouched file report time running backwards, which Linux does not
    produce — and it is kept because holding them fixed would reject the
    ordinary stat/write/stat trace instead.

    THE CHOICE IS PINNED, per file, in [State.procst_statpins], and that
    is what makes it a check rather than a shrug.  Chosen afresh at each
    call these members would admit a trace in which two [fstat]s of one
    unchanged file report different inodes, which no Linux machine
    produces — the objection [State.procst_utsname] answers for the UTS
    name and [Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec] answers
    by declining.  So the first stat of a file records the 128 bytes it
    delivered, and every later stat of the same file must repeat its
    STABLE members ([Uapi.stat_stable_eqb]): the device, inode, mode,
    link count, ids, [st_rdev] and block size.  [st_size], [st_blocks]
    and the timestamps are deliberately NOT held against the pin,
    because a write moves all three.

    A PIN THAT IS NOT [Uapi.stat_buf_wf] IS DECLINED, and that branch is
    unreachable: the only writer is the branch below, which has just
    checked the predicate.  It is written rather than argued away
    because receptiveness ([Checks.Progress]) is a statement about every
    [Model], including ones no run can build, and an unsatisfiable
    [choose] is the one way to write a non-receptive spec (Monad.v).

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
    [Kernel.Sys.uname_spec] states.

    A PATH [Fs] NO LONGER HOLDS IS DECLINED.  [unlinkat] (35) removes a
    key while a descriptor on it stays open, and Linux answers such an
    [fstat] with the inode's surviving metadata and [st_nlink] 0.  The
    model has no contents to size and no link count to drop, so it
    declines — which is also what keeps [st_nlink] among the members the
    pin holds fixed. *)
Definition fstat_file_spec (p : path) (statbuf : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fs_lookup (m_fs m) p with
  | None => unmodeled            (* unlinked under an open fd: no contents to size *)
  | Some data =>
      if negb (access_okb statbuf STAT_SIZE) then err_ret EFAULT
      else
        match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
        | None => unmodeled      (* a partial [copy_to_user] then -EFAULT *)
        | Some _ =>
            match statpin_lookup (m_statpins m) p with
            | Some b0 =>
                if negb (stat_buf_wf b0) then unmodeled  (* no branch writes such a pin *)
                else
                  bs <- choose (fun bs : list byte =>
                                  stat_buf_wf bs = true
                                  /\ stat_size_ok (length data) bs = true
                                  /\ stat_stable_eqb bs b0 = true) ;;
                  pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
            | None =>
                bs <- choose (fun bs : list byte =>
                                stat_buf_wf bs = true
                                /\ stat_size_ok (length data) bs = true) ;;
                set_statpin p bs ;;
                pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
            end
        end
  end.

(** THE SUCCESS ARM FOR A CHARACTER DEVICE THE MODEL KNOWS, in two
    instances: /dev/null ([fstat_devnull_spec], under [Uapi.devnull_path]
    and [Uapi.stat_devnull_ok]) and /dev/urandom ([fstat_urandom_spec],
    under [Uapi.urandom_path] and [Uapi.stat_urandom_ok]).  It is
    [fstat_file_spec]'s shape with the file's one implication replaced
    by the device's assertions: the model KNOWS which device this
    descriptor is — that is the assumption the openat arm states — so
    [st_mode]'s type, [st_rdev], [st_size] and [st_blocks] are pinned
    outright, and the members the kernel does not decide are chosen
    once and held in [State.procst_statpins] under the device's path,
    exactly as a file's are under its key.  [p] is that path and [ok]
    the device's assertions; nothing below reads either for anything
    but the pin's key and the delivery's test.

    THE PIN IS CHECKED AGAINST BOTH PREDICATES before it is used, where
    the file arm checks [stat_buf_wf] alone.  The file arm patches
    [st_size] into whatever pin it holds, and [st_size] is outside the
    stable members, so any well-formed pin admits a delivery; here the
    asserted members are INSIDE the stable region ([st_mode] and
    [st_rdev]) or asserted constant ([st_size], [st_blocks]), so a pin
    that failed [stat_devnull_ok] would leave the [choose] below with no
    satisfying buffer — a non-receptive spec, the one shape Monad.v
    forbids.  Declining such a pin keeps the arm receptive on every
    [Model]; the branch is unreachable, since the only writer is the
    branch below, which has just checked both predicates.

    No [fs_lookup]: the device is not a key, and [unlinkat] cannot reach
    it (the separator decline stands for it), so there is no
    unlinked-under-an-open-fd case to decline.  The rest — -EBADF before
    anything, [access_ok]'s -EFAULT, the partial [copy_to_user]
    decline, the errnos past an open descriptor — is [fstat_file_spec]'s
    argument unchanged. *)
Definition fstat_chrdev_spec (p : path) (ok : list byte -> bool)
    (statbuf : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (access_okb statbuf STAT_SIZE) then err_ret EFAULT
  else
    match read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE) with
    | None => unmodeled      (* a partial [copy_to_user] then -EFAULT *)
    | Some _ =>
        match statpin_lookup (m_statpins m) p with
        | Some b0 =>
            if negb (stat_buf_wf b0 && ok b0)%bool then unmodeled
              (* no branch writes such a pin: see above *)
            else
              bs <- choose (fun bs : list byte =>
                              stat_buf_wf bs = true
                              /\ ok bs = true
                              /\ stat_stable_eqb bs b0 = true) ;;
              pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        | None =>
            bs <- choose (fun bs : list byte =>
                            stat_buf_wf bs = true
                            /\ ok bs = true) ;;
            set_statpin p bs ;;
            pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        end
    end.

(** The null device: S_IFCHR, [st_rdev] 1:3, zero size and blocks. *)
Definition fstat_devnull_spec (statbuf : word) : Sys SyscallEffect :=
  fstat_chrdev_spec devnull_path stat_devnull_ok statbuf.

(** The random device: S_IFCHR, [st_rdev] 1:9, zero size and blocks
    ([Uapi.stat_urandom_ok]), on the assumption
    [Open.openat_urandom_spec] states — the image's /dev/urandom is the
    random device, major 1 minor 9.  [cp_new_stat] (fs/stat.c,
    v6.18.46) reads the same inode members it reads for /dev/null; the
    zero [st_size] and [st_blocks] rest on the same premise about a
    node nothing ever resized. *)
Definition fstat_urandom_spec (statbuf : word) : Sys SyscallEffect :=
  fstat_chrdev_spec urandom_path stat_urandom_ok statbuf.

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
    what the ONE implication below is: the size obligation is a function
    of the CURRENT contents rather than of the descriptor, which is why
    the same one serves all four.

    /dev/null ANSWERS TOO, through [fstat_devnull_spec]: the model minted
    that descriptor knowing it is the null device, so the type bits and
    the device number are asserted where the file arm can only imply.
    /dev/urandom answers the same way through [fstat_urandom_spec].

    THE FOUR OTHER KINDS STILL DECLINE, and they are not equally far
    from an answer:

      - [FdChannel] — the type bits alone are undecidable.  A channel is
        the model's one name for a pipe, a socket and a terminal (see
        [FdChannel]'s own note), so S_IFIFO, S_IFSOCK and S_IFCHR are
        all live and nothing in the model chooses between them.  A
        [choose] over the type would not fix it: the pin makes two stats
        agree with each other, not with the kernel, and there is nothing
        here for the size obligation to bite on.
      - [FdDir] — S_IFDIR is the one type bit the model does know, and it
        buys nothing: a directory's [st_size] and [st_blocks] are the
        filesystem's own bookkeeping, not a function of anything [Fs]
        holds, so the arm would carry no obligation at all.
      - [FdSocket] — the BEST-DETERMINED of the four.  [sock_alloc]
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
    Linux can still fail — [vfs_getattr] runs [security_inode_getattr],
    which an LSM may refuse, and a filesystem's own [.getattr] may return
    an error.  This model has no security module, so an LSM refusal is
    not an outcome it can represent; that is a premise on the
    environment rather than a claim about Linux, and it is the one thing
    the success arm adds to what the -EBADF arm already assumed.
    [cp_new_stat]'s five -EOVERFLOW tests cannot fire on riscv64: four
    are false because every destination member is at least as wide as
    its [kstat] source, and the [MAX_NON_LFS] one is inside
    [#if BITS_PER_LONG == 32]. *)
Definition fstat_spec (fd statbuf : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF          (* [vfs_fstat]'s own answer, before [statbuf] is touched *)
  | Some (FdChannel _) => unmodeled  (* pipe, socket or terminal: even the type bits are undecided *)
  | Some (FdFile p _)  => fstat_file_spec p statbuf   (* [cp_new_stat] over the file's inode *)
  | Some (FdFileW p _) => fstat_file_spec p statbuf   (* the same inode, opened for writing *)
  | Some (FdFileA p _) => fstat_file_spec p statbuf   (* and again in append mode *)
  | Some (FdFileRW p _) => fstat_file_spec p statbuf
                                     (* and again opened O_RDWR.  Same inode, and the
                                        read-write kind's SINGLE SHARED [f_pos] means a
                                        read moves the offset the next write lands at, so
                                        its [st_size] moves under it exactly as
                                        [FdFileW]'s does -- the size obligation is a
                                        function of the CURRENT contents, not of the
                                        descriptor ([cp_new_stat]/[generic_fillattr],
                                        fs/stat.c, v6.18.46, 1f99e9ab748f) *)
  | Some FdDir         => unmodeled  (* S_IFDIR is known; a directory's size and blocks are not *)
  | Some (FdSocket _)  => unmodeled  (* mode/uid/gid are known; ino, dev and the timestamps are not *)
  | Some (FdPipe _ _)  => unmodeled  (* S_IFIFO is known; a pipe's [st_size]/[st_blocks] are
                                        not even the queue's length, so nothing plays the
                                        role the file contents play above *)
  | Some (FdDevNull _ _) => fstat_devnull_spec statbuf
                                     (* the null device: S_IFCHR, [st_rdev] 1:3, [st_size]
                                        and [st_blocks] 0 asserted ([Uapi.stat_devnull_ok]),
                                        the rest pinned once under [Uapi.devnull_path] *)
  | Some FdUrandom => fstat_urandom_spec statbuf
                                     (* the random device: S_IFCHR, [st_rdev] 1:9
                                        ([Uapi.stat_urandom_ok]), the rest pinned once
                                        under [Uapi.urandom_path] *)
  | Some (FdOpaque _) => unmodeled
                                     (* DECLINED: [vfs_fstat]'s [CLASS(fd_raw, f)] accepts
                                        an O_PATH file, so all three objects reach
                                        [cp_new_stat], with metadata the model does not
                                        hold (fs/stat.c, read at v6.18.44) *)
  end.

