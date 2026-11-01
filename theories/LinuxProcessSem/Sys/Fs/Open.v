(** * LinuxProcessSem.Sys.Fs.Open — openat (56), close (57), ftruncate (46), faccessat (48), faccessat2 (439)

    This file answers to Linux [fs/open.c]: it holds what the kernel
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
  Syscall Uapi Fs.File Fs.ReadWrite Fs.Namei.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** openat's injectable failures: environment conditions the model does
    not track — kernel memory (ENOMEM, listed first as the canonical
    witness), permissions (EACCES), fd-table exhaustion (EMFILE/ENFILE,
    which also keep the spec receptive when no free fd < 2^31 exists).
    ENOENT is NOT injectable: file existence IS tracked, and a missing
    file returns a deterministic -ENOENT. *)
Definition openat_errnos : list Z := [ENOMEM; EACCES; EMFILE; ENFILE].

(** The clobbering write-open combination the model covers. *)
Definition wr_create_flags : Z := (O_WRONLY + O_CREAT + O_TRUNC)%Z.

(** The EXCLUSIVE write-open combinations the model covers:
    O_WRONLY|O_CREAT|O_EXCL, with or without O_TRUNC.  O_EXCL makes the
    open fail outright when the path already exists, so O_TRUNC can
    never fire alongside it — the two spellings denote exactly the same
    kernel behavior and are modeled by the one branch.  (toybox's
    `cp -n` issues the O_TRUNC spelling; the plain one is what
    mkstemp-style create-if-absent code uses.) *)
Definition excl_create_flags : Z := (O_WRONLY + O_CREAT + O_EXCL)%Z.

Definition is_excl_create (fl : Z) : bool :=
  Z.eqb fl excl_create_flags || Z.eqb fl (excl_create_flags + O_TRUNC).

(** The APPEND write-open combination the model covers:
    O_WRONLY|O_CREAT|O_APPEND, the word C's [fopen(p, "a")] issues (musl
    1.2.6, src/stdio/fopen.c through [__fmodeflags]) and the one zlib's
    gzio output path uses.  It is a SINGLE word and not a mask test: the
    O_TRUNC spelling beside it is declined, the O_EXCL spellings have an
    arm of their own ([is_excl_append_create]), and
    [modeled_open_flags]'s note says why each is not this one.

    ITS RESIDUE MEETS [Fs.Fcntl.setfl_acted_on], because O_APPEND is a
    bit F_SETFL acts on, and so does every residue
    [is_excl_append_create] admits; [Fs.Fcntl.modeled_open_flags_clear_of_setfl]
    proves every other admitted word clear of it.  That is why the fd
    these words mint is a [State.FdFileA] rather than a
    [State.FdFileW]: [Fs.Fcntl.setfl_noop_on] declines the new kind, and
    its arm carries the argument.  A future widening that routed either
    word to [FdFileW] would silently make that predicate unsound. *)
Definition append_create_flags : Z := (O_WRONLY + O_CREAT + O_APPEND)%Z.

(** The EXCLUSIVE APPEND write-open combinations the model covers:
    O_WRONLY|O_CREAT|O_EXCL|O_APPEND, with or without O_TRUNC.  The plain
    spelling is the word zlib's [gz_open] (gzlib.c) builds for
    [gzopen(p, "ax")].  Ported from main LPS
    (theorem-labs/linux-process-semantics) commit 4d80c33d83, #1760,
    with the one change the next paragraph names.

    EACH HALF OF ITS ANSWER IS ALREADY A NEIGHBOUR'S, and that is the
    whole derivation.  [do_open] (fs/namei.c, Linux v6.18.46) opens its
    [open_flag & O_CREAT] block with
    [(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)], and
    returns -EEXIST there, BEFORE the [d_is_dir(nd->path.dentry)] test
    that answers -EISDIR.  So a name that exists -- a key, a directory
    reference, or a directory some key lives under -- is -EEXIST before
    anything else is looked at: the answer [openat_excl_spec] gives, and
    the reason no append rule ever meets an existing tail.  A DIRECTORY
    REFERENCE IS -EEXIST AND NOTHING ELSE HERE, which is the one place
    this port differs from main LPS 4d80c33d83: that model admits
    -EISDIR beside it, the answer kernels v4.17 through v5.6 give in the
    function [do_open] replaced.  This model describes Linux v6.18.46
    alone (dispatch://OSSV-266/ask/9128d2b8), so the arm answers
    v6.18.46's -EEXIST and offers no alternative.  An absent name is
    created, and then
    [do_open] clears O_TRUNC under [FMODE_CREATED] (which is why the
    O_TRUNC spelling is the same behaviour, as it is for
    [is_excl_create]), while O_APPEND survives into [f_flags]:
    [do_dentry_open] (fs/open.c, Linux v6.18.46) clears only
    O_CREAT|O_EXCL|O_NOCTTY|O_TRUNC there.  So the created descriptor is
    the append kind on a new empty file, which is what [open_append]
    records for an absent name.

    The descriptor is a [State.FdFileA] for the reason
    [append_create_flags] gives: the residue carries O_APPEND. *)
Definition excl_append_create_flags : Z :=
  (O_WRONLY + O_CREAT + O_EXCL + O_APPEND)%Z.

Definition is_excl_append_create (fl : Z) : bool :=
  Z.eqb fl excl_append_create_flags
  || Z.eqb fl (excl_append_create_flags + O_TRUNC).

(** Is bit [b] set in the flag residue [fl]?  Used only by the O_RDWR
    arms, which derive their behavior from the O_CREAT and O_TRUNC bits
    the way [build_open_flags] (fs/open.c, Linux v6.18.46) does, rather
    than from four separate word tests.  The ENVELOPE is still a word
    set ([rdwr_open_word]) and still fails closed outside it; only the
    behavior inside it is read off bits. *)
Definition flag_set (fl b : Z) : bool := Z.eqb (Z.land fl b) b.

(** The READ-WRITE open words the model interprets, other than the
    exclusive ones: O_RDWR alone, and O_RDWR beside O_CREAT, O_TRUNC or
    both.

    WHY ONE PREDICATE AND ONE ARM RATHER THAN FOUR.  The four words
    differ in exactly the two bits [do_open] (fs/namei.c, Linux
    v6.18.46) reads, and each bit changes one answer: O_CREAT decides
    what an ABSENT name gets (a fresh empty file, or the negative
    dentry's -ENOENT out of [lookup_open]), and O_TRUNC decides whether
    an EXISTING file keeps its bytes ([do_open]'s
    [d_is_reg(...) && open_flag & O_TRUNC] arms [handle_truncate]).
    Writing them out four times would repeat one table and let the
    copies drift; [openat_rdwr_spec] is that table.

    O_EXCL IS NOT IN HERE and gets its own arm, because it changes the
    answer to a DIRECTORY REFERENCE as well: [do_open] tests
    [(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)] ahead of
    [d_is_dir], so "." is -EEXIST under O_EXCL and -EISDIR without it —
    the same asymmetry [is_excl_create] already carries on the
    write-only side. *)
Definition rdwr_open_word (fl : Z) : bool :=
  Z.eqb fl O_RDWR
  || Z.eqb fl (O_RDWR + O_TRUNC)
  || Z.eqb fl (O_RDWR + O_CREAT)
  || Z.eqb fl (O_RDWR + O_CREAT + O_TRUNC).

(** The EXCLUSIVE read-write create words: O_RDWR|O_CREAT|O_EXCL, with
    or without O_TRUNC.  The two spellings denote the same behavior for
    the reason [is_excl_create] gives on the write-only side — O_EXCL
    fails outright on an existing path, so O_TRUNC can never fire beside
    it — and this is the word musl's [mkostemps] issues, which strips
    the caller's access mode and hardcodes O_RDWR (src/temp/mkostemps.c,
    musl 1.2.6). *)
Definition rdwr_excl_create_flags : Z := (O_RDWR + O_CREAT + O_EXCL)%Z.

Definition is_rdwr_excl_create (fl : Z) : bool :=
  Z.eqb fl rdwr_excl_create_flags || Z.eqb fl (rdwr_excl_create_flags + O_TRUNC).

(** The flag bits every modeled shape accepts and ignores.  Each is
    ignorable for its own reason, recorded at its own definition in
    [Uapi]; the mask exists so that every mirror of the flag test —
    [openat_resolved_spec], [Checks.Sys.Fs.Open.check_openat] and
    [Checks.Witness.Fs.Open.openat_witness] — strips exactly the same
    bits, and so that widening the set is one edit rather than a
    search. *)
Definition open_ignored_flags : Z := (O_CLOEXEC + O_LARGEFILE + O_NONBLOCK)%Z.

(** The O_PATH words, read past [open_ignored_flags]: O_PATH alone or
    beside O_DIRECTORY and O_NOFOLLOW.  [SYSCALL_DEFINE4(openat)] hands
    its word to [build_open_how] (fs/open.c), whose
    [if (how.flags & O_PATH) how.flags &= O_PATH_FLAGS] keeps only
    O_DIRECTORY, O_NOFOLLOW, O_PATH and O_CLOEXEC, so the O_LARGEFILE
    [SYSCALL_DEFINE4(openat)] adds and an O_NONBLOCK the caller passed
    are dropped before anything reads them (fs/open.c [build_open_how],
    [build_open_flags]: read at v6.18.44; identical at v6.18.46).  A
    word with any other bit set beside O_PATH is DECLINED, a narrowing:
    Linux drops those bits too. *)
Definition open_path_word (fl : Z) : bool :=
  Z.eqb (Z.ldiff fl (O_DIRECTORY + O_NOFOLLOW)) O_PATH.

(** The flag WORDS [openat_spec] interprets: O_RDONLY, the clobbering
    write-create shape, the exclusive write-create shapes, the
    read-a-directory shape O_RDONLY|O_DIRECTORY, the APPEND
    write-create shape, the READ-WRITE shapes ([rdwr_open_word] and
    [is_rdwr_excl_create]), the EXCLUSIVE APPEND shapes
    ([is_excl_append_create]), and the O_PATH words ([open_path_word]),
    each modulo the bits in [open_ignored_flags].
    Linux validates
    the flags in [build_open_flags()] BEFORE it fetches the pathname, so
    this test runs first in [openat_spec] too — see the ORDER paragraph
    there.

    THE O_PATH WORDS PASS THIS GATE AND ARE ANSWERED ONLY ON A PROCFS
    NAME.  [openat_body_spec] hands them to [openat_proc_spec] when
    [proc_open_target] finds one, and declines them everywhere else,
    before any of the arms below them is reached; so every arm written
    for the access-mode words still sees only those words.

    O_DIRECTORY IS INTERPRETED, NOT IGNORED, and outside the O_PATH words
    it is the only flag here that is neither an access mode nor a creation flag.  The reason it
    can be admitted at all is that its answer does not depend on WHICH
    non-directory the name turned out to be.  [do_open] (fs/namei.c)
    answers -ENOTDIR for a dentry [d_can_lookup] (include/linux/dcache.h)
    refuses, and does it before [may_open] (fs/namei.c) and [vfs_open]
    (fs/open.c) run, so the FIFO, device-node and socket cases all
    reach the same errno as a regular file.  The regular-file premise that arm rests on
    is therefore not load-bearing HERE — see [openat_dir_spec].  Linux
    v6.18.46.

    DELIBERATELY STILL DECLINED.  Two flags real programs reach for that
    this set does NOT admit, each for its own reason, and the O_APPEND
    SPELLINGS beside the admitted ones:

    - O_WRONLY|O_APPEND without O_CREAT is a different syscall answer,
      not a different name for the same one: the file must already
      exist, and an absent path is a deterministic -ENOENT rather than a
      creation.  The arm is small and is simply not written; a program
      reaching for it gets [unmodeled] rather than a guess.
    - O_WRONLY|O_CREAT|O_TRUNC|O_APPEND is declined because the two
      positioning rules would have to be composed: the file is emptied
      at open and then appended to.  The composition is easy to state
      and the resulting fd is indistinguishable from an append fd on a
      file the open just emptied — which is exactly why it is worth an
      arm of its own with its own test rather than being folded in
      here on the strength of that sentence.  The O_EXCL spelling is
      NOT this case and is admitted: there O_EXCL refuses every
      existing name before O_TRUNC could act, so nothing is composed
      ([is_excl_append_create]).

    - O_RDWR IS ADMITTED, in the six words [rdwr_open_word] and
      [is_rdwr_excl_create] name, and [State.FdFileRW] is its
      read-write kind.  What is declined is O_RDWR
      beside a flag whose own arm is missing rather than beside a bit
      this model cannot represent: O_RDWR|O_APPEND in any spelling
      (the append positioning rule and the read direction have no
      combined arm and no test), O_RDWR|O_DIRECTORY (which
      [build_open_flags] does not reject, and which is -EISDIR on a
      real directory through [may_open]'s MAY_WRITE test — an arm
      nothing here reaches, since [openat_dir_spec]'s guards were
      written for the read-only word), and O_RDWR|O_EXCL WITHOUT
      O_CREAT, which Linux treats as plain O_RDWR (open(2): O_EXCL
      "is undefined" without O_CREAT and [do_open] reads it only inside
      its [open_flag & O_CREAT] block) and which no reported program
      issues, so it is declined rather than aliased.

    - O_NOCTTY is declined because the single thing that makes it
      MEANINGFUL is a terminal, and this model has none.  A program that
      passes O_NOCTTY is opening something it believes is a tty;
      answering it with regular-file semantics would be a confident
      wrong answer where [unmodeled] is the true one.  [tty_open]
      (drivers/tty/tty_io.c) is the site that gives the flag that
      meaning, and [do_dentry_open] (fs/open.c) strips it from [f_flags]
      once the file's [->open] has run, so a program cannot read it back
      afterwards either.

      The reason is deliberately NOT "the flag is inert away from a
      terminal", which is very nearly true and not quite.  Grepping the
      v6.17 tree for O_NOCTTY turns up [v9fs_mapped_dotl_flags]
      (fs/9p/vfs_inode_dotl.c), which forwards it to the 9P server as
      P9_DOTL_NOCTTY on a REGULAR-file open, from a [dotl_oflag_map]
      table byte-identical at v4.9, v4.19, v5.4, v5.10, v5.15, v6.1,
      v6.6, v6.12 and v6.17.  Nothing this model can name is 9p, so the
      decision is unaffected — but an inertness claim ranges over the
      whole tree and would have to be re-established at every widening,
      where the terminal argument above does not.

    A SET HIGH HALF is declined too, and that is a narrowing rather than
    a disagreement: [flags] is [int] at the boundary
    ([SYSCALL_DEFINE4(openat, ...)], fs/open.c, Linux v6.18.46), so
    Linux discards bits 32-63 before [build_open_flags] reads the word,
    while this predicate reads all 64 and is false for anything above
    the interpreted bits, which [openat_spec] turns into [unmodeled].
    The arguments the model DOES truncate are exactly the callers of
    [Syscall.abi_low32]. *)
Definition modeled_open_flags (flags : word) : bool :=
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
  Z.eqb fl 0 || Z.eqb fl wr_create_flags || is_excl_create fl
  || Z.eqb fl O_DIRECTORY || Z.eqb fl append_create_flags
  || rdwr_open_word fl || is_rdwr_excl_create fl
  || is_excl_append_create fl || open_path_word fl.

(** One introduction lemma per modeled shape, so a proof that already
    knows which arm it is in can clear the flags guard. *)
Lemma modeled_open_flags_rd : forall flags,
  Z.ldiff (bv_unsigned flags) open_ignored_flags = 0%Z ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H. reflexivity.
Qed.

Lemma modeled_open_flags_wr : forall flags,
  Z.ldiff (bv_unsigned flags) open_ignored_flags = wr_create_flags ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r.
Qed.

Lemma modeled_open_flags_excl : forall flags,
  is_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags) = true ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r, Bool.orb_true_l.
Qed.

Lemma modeled_open_flags_append : forall flags,
  Z.ldiff (bv_unsigned flags) open_ignored_flags = append_create_flags ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r.
Qed.

Lemma modeled_open_flags_dir : forall flags,
  Z.ldiff (bv_unsigned flags) open_ignored_flags = O_DIRECTORY ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H. reflexivity.
Qed.

Lemma modeled_open_flags_rdwr : forall flags,
  rdwr_open_word (Z.ldiff (bv_unsigned flags) open_ignored_flags) = true ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r, Bool.orb_true_l.
Qed.

Lemma modeled_open_flags_rdwr_excl : forall flags,
  is_rdwr_excl_create (Z.ldiff (bv_unsigned flags) open_ignored_flags) = true ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r.
Qed.

Lemma modeled_open_flags_excl_append : forall flags,
  is_excl_append_create (Z.ldiff (bv_unsigned flags) open_ignored_flags) = true ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r.
Qed.

Lemma modeled_open_flags_path : forall flags,
  open_path_word (Z.ldiff (bv_unsigned flags) open_ignored_flags) = true ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r.
Qed.

(** The common result of opening an existing object: either an
    injectable failure, or the lowest free fd followed by [mk]'s model
    update.  The read-file and directory arms below share this exact
    success shape. *)
Definition open_result_spec (m : Model) (mk : word -> Model -> Model)
    : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)
      (fd <- lowest_fd (m_fds m) ;;
       modify (mk fd) ;;
       ret_only fd).

(** The effect a modeled WRITE-CREATE open records, shared by the
    clobbering (O_TRUNC) and the exclusive (O_EXCL) shapes so the two
    provably record the same thing: either an errno from
    [openat_errnos] (an environment condition the model does not track;
    this alternative also keeps the spec receptive when no free
    fd < 2^31 exists), or the lowest free fd bound to a write-only fd
    on [p], with [p] itself (re)created empty in the file system.

    THIS IS WHERE THE MODEL'S REGULAR-FILE PREMISE IS CREATED.  [p] is
    an uninterpreted byte string, so a name the kernel resolves to a
    character device, a FIFO or a kernfs attribute is recorded here as
    an ordinary file, and every later syscall that resolves the fd
    through [Fs.fs_lookup] — [read], [lseek], [ftruncate] and [fsync],
    and [write] for the base it splices onto — answers for a file that
    is not there. *)
Definition create_wronly (p : path) (m : Model) : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)  (* untracked env failure or no free fd *)
      (fd <- lowest_fd (m_fds m) ;;
       set_fs (fs_set (m_fs m) p []) ;;   (* (re)create the file empty *)
       set_fds (fd_insert (m_fds m) fd (FdFileW p (Z_to_bv 64 0))) ;;  (* write-only fd *)
       ret_only fd).

(** The two paths that name a DIRECTORY without consulting a file
    system, and so get the same answer on every arm below.

    The walk types the last component and answers both "." and ".."
    out of itself, never calling a filesystem's `->lookup`.  For the
    LAST component on the open path that is [open_last_lookups], which
    takes its `nd->last_type != LAST_NORM` branch straight to
    [handle_dots] before O_CREAT is considered at all; interior
    components go through [link_path_walk].  Both fs/namei.c, Linux
    v6.18.46.

    The three answers come from [do_open], not from [may_open]: with
    O_CREAT set it returns -EEXIST when O_EXCL is on and the file was
    not created, and -EISDIR on `d_is_dir(nd->path.dentry)`, both BEFORE
    [may_open] is reached.  [may_open]'s own S_IFDIR arm is what lets
    the plain O_RDONLY through.  So the read arm's directory fd, the
    clobbering shape's -EISDIR and O_EXCL's -EEXIST are the same three
    answers for both paths.

    THE ONE ANSWER ".." HAS THAT "." DOES NOT.  [follow_dotdot] ends by
    checking [path_connected], and returns -ENOENT when the parent has
    been disconnected from the mount — reachable only under a bind mount
    of a subdirectory that was since renamed out of the bind root, since
    [path_connected] short-circuits true whenever `mnt->mnt_root ==
    sb->s_root`.  That errno is not in [openat_errnos] and this arm does
    not admit it, so the arm is NARROWER than Linux by exactly that
    case — the same shape as the -ENOMEM approximation this file already
    carries, and a narrowing rather than a wrong answer.

    THE MODEL CAN AFFORD TO ANSWER, which is why this is an arm and not
    a decline: [State.FdDir] carries NO path, so nothing the model can
    then do to the fd distinguishes the two directories — read is
    -EISDIR for either, close is close, lseek is declined, and
    [Fs.Readdir.getdents64_spec] declines the listing and gives both the
    same -EINVAL where the buffer has no room for an entry.  A decline is
    for what the model cannot judge; it judges this correctly.  [Fs.Open.faccessat_body_spec] answers ".."
    the same way and for the same reason.

    THE CONDITION THAT WOULD FALSIFY THAT, written here because it is
    what a later directory change has to re-check.  The reason ".." is
    safe to answer is NOT that [FdDir] is nullary — it is that no
    modeled syscall can USE such an fd as a dirfd.  All five path-taking
    specs gate on [AT_FDCWD32] and decline everything else
    ([openat_body_spec], [faccessat_body_spec],
    [Fs.Namei.unlinkat_body_spec], [Fs.Stat.readlinkat_spec],
    [Fs.Stat.newfstatat_spec]), and nothing modeled moves the working
    directory or creates a directory (no chdir, fchdir, mkdirat,
    renameat or linkat).  If ANY of those gains a real-dirfd arm, then
    openat(fd_of_"..", "x") and openat(fd_of_".", "x") become
    distinguishable and this arm has to be revisited.

    ONE ANSWER IS ALREADY OBSERVABLE, and it is not this arm's doing:
    [Fs.Sync.fsync_spec] returns 0 for an [FdDir], which is wrong on a
    filesystem whose directories carry no [.fsync].  Answering ".."
    widened that divergence's precondition from "the cwd is on procfs or
    sysfs" to include a cwd whose PARENT is, which is a strictly larger
    set because a mount point's parent sits on another filesystem.

    ".." IS NOT [fs_lookup]-ABLE, and that is the point: without this
    arm the read shape would call it absent (-ENOENT, which Linux never
    returns for "..") and the create shape would MINT A KEY spelled "..". *)
Definition path_is_dirref (p : path) : bool :=
  path_eqb p dot_path || path_eqb p dotdot_path.

(** Resolve an O_RDONLY open after pathname fetch and dirfd validation. *)
Definition openat_read_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p then
    open_result_spec m
      (fun fd => with_fds (fd_insert (m_fds m) fd FdDir))
  else
    match fs_lookup (m_fs m) p with
    | None => err_ret ENOENT
    | Some _ =>
        open_result_spec m
          (fun fd => with_fds (fd_insert (m_fds m) fd
            (FdFile p (Z_to_bv 64 0))))
    end.

(** A name the flat map only IMPLIES is a directory: some key lives
    under it ([Fs.Namei.fs_under]).  On every write-create arm below it
    gets the answer a directory reference gets, and the test is written
    at each arm as [path_is_dirref p || fs_under (m_fs m) p] so that the
    directory the map implies and the directory reference the walk
    settles are answered by the same branch.

    THE DERIVATION IS THE ONE THE DOT ARMS ALREADY CARRY, with the
    dentry coming from a lookup instead of from [handle_dots].
    [open_last_lookups] (fs/namei.c) takes the LAST_NORM branch and
    reaches the existing name by either of the routes that agree on what
    matters: [lookup_fast_for_open] returns a cached POSITIVE dentry
    (under O_CREAT it discards a negative one, and under O_CREAT|O_EXCL
    it returns nothing at all), and when it returns nothing
    [lookup_open] runs under the parent's inode lock and hands back the
    positive dentry it finds.  On either route [FMODE_CREATED] stays
    clear: the fast route never touches it, and [lookup_open] clears it
    on entry and sets it only on the create path.  [do_open] then runs
    its [open_flag & O_CREAT]
    block: first [(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)]
    is -EEXIST, then [d_is_dir(nd->path.dentry)] is -EISDIR, and both
    are returned BEFORE [may_open] and before any [O_TRUNC] handling.
    So an O_CREAT open of a directory answers -EEXIST under O_EXCL and
    -EISDIR without it, for every access mode the word carries.
    ([may_open]'s own [case S_IFDIR: if (acc_mode & MAY_WRITE) return
    -EISDIR] is the derivation for a write open WITHOUT O_CREAT, which
    no arm below is: every admitted write-create word carries O_CREAT.)
    All fs/namei.c, Linux v6.18.46; each function named was read at
    that version for this arm.

    WHY THIS IS AN ANSWER AND NOT A DECLINE.  A decline is for what the
    model cannot judge, and this it can: the answer is deterministic, it
    does not depend on which filesystem the directory is on, and it
    leaves the model unchanged, so the same image drives a source and a
    target into the same branch.  Without this arm the create shapes
    would MINT a key [a] beside [a/b] — a file system no directory tree
    can be — and a later [unlinkat] of that key would hit
    [Fs.Namei.fs_under] and decline a run that Linux had already
    answered.  [Fs.valid_fs] admits such an image (its keys are only
    sorted and NUL-free), so the divergence would be reachable on the
    plain binary of every whole-program example.
    This leaves three cases open: the NAME_MAX component, the read
    arm's -ENOENT for the same name, and the EMPTY real directory,
    which no [fs_under] can see.

    THE ANSWER IS DETERMINISTIC, with no [openat_errnos] alternative
    beside it, so it joins the arms [openat_body_spec]'s APPROXIMATION
    paragraph lists.  No modeled syscall makes a directory, so the
    `reject` twin that paragraph asks of each such arm is a Rocq literal:
    [Checks.Cases.Fs.Open.openat_implied_directory_create_eisdir] shows
    the offered descriptor refused beside the -EISDIR accepted. *)

(** Resolve the clobbering O_WRONLY|O_CREAT|O_TRUNC open shape.  A
    directory reference, or a name the map implies is a directory, is
    -EISDIR ([do_open]'s [d_is_dir], above). *)
Definition openat_create_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else create_wronly p m.

(** The file system after an APPEND open: unchanged when the path is
    already there, and carrying a new empty file when it is not.

    THE DIFFERENCE FROM [create_wronly] IS THE WHOLE POINT OF THE ARM.
    [build_open_flags] turns O_TRUNC into [op->open_flag]'s O_TRUNC and
    [do_open] (fs/namei.c) then calls [handle_truncate], which empties an
    existing file; nothing on the O_APPEND path does, since O_APPEND is
    a file-STATUS flag [do_dentry_open] copies into [f_flags] and reads
    at write time (fs/open.c, mm/filemap.c [generic_write_checks], Linux
    v6.18.46).  So an append open of an existing file must leave the
    bytes exactly where they were — writing them back through [fs_set]
    would be a no-op only for a sorted image, and this expresses the
    intent instead of leaning on that. *)
Definition append_open_fs (fs : Fs.Fs) (p : path) : Fs.Fs :=
  match fs_lookup fs p with
  | Some _ => fs                        (* the file exists: O_APPEND never truncates *)
  | None => fs_set fs p []              (* O_CREAT mints it empty *)
  end.

(** The effect a modeled APPEND write-open records: either an errno from
    [openat_errnos] (the same untracked environment conditions the other
    write-open shapes admit, this alternative also keeping the spec
    receptive when no free fd < 2^31 exists), or the lowest free fd bound
    to a [State.FdFileA] on [p], with [p] created empty only if it was
    absent.

    THE OFFSET STARTS AT 0 AND THAT IS EXACT rather than a convenience.
    Linux gives every freshly opened description [f_pos = 0] —
    [alloc_empty_file] zeroes the [struct file] and no O_APPEND path
    assigns to [f_pos] at open time, which is why [fopen(p, "a")] has to
    be followed by an [ftell] that seeks to learn the size.  The append
    positioning happens per WRITE, in [generic_write_checks], and
    [ReadWrite.write_spec]'s [FdFileA] arm is where the model records
    it.

    THE REGULAR-FILE PREMISE OF [create_wronly] IS SHARED, unchanged: [p]
    is an uninterpreted byte string, so a name Linux would resolve to a
    device, FIFO or kernfs attribute is recorded here as an ordinary
    file. *)
Definition open_append (p : path) (m : Model) : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)  (* untracked env failure or no free fd *)
      (fd <- lowest_fd (m_fds m) ;;
       set_fs (append_open_fs (m_fs m) p) ;;
       set_fds (fd_insert (m_fds m) fd (FdFileA p (Z_to_bv 64 0))) ;;
       ret_only fd).

(** Resolve the two APPEND write-create open shapes: the plain word
    ([excl] false) and the exclusive one ([excl] true).  Both
    create an absent name with [open_append]; they differ in what an
    existing name gets.  The exclusive half is ported from main LPS
    (theorem-labs/linux-process-semantics) commit 4d80c33d83 (#1760).

    THE PLAIN WORD: A DIRECTORY REFERENCE IS -EISDIR, the clobbering
    shape's answer and not the exclusive shape's -EEXIST, and the reason
    is which test [do_open] (fs/namei.c) reaches first.  With O_CREAT set
    it returns -EEXIST only under O_EXCL, which this word does not carry;
    the next test is [d_is_dir(nd->path.dentry)], and that is -EISDIR.  So
    "." and ".." answer here exactly as they do for O_WRONLY|O_CREAT|O_TRUNC,
    ahead of [may_open], and O_APPEND changes nothing about it.  An
    IMPLIED directory ([fs_under]) takes the same branch for the reason
    given above [openat_create_spec]: the dentry the lookup finds is
    positive and [d_is_dir], and the word carries no O_EXCL.  An existing
    file is opened, and keeps its bytes ([append_open_fs]).

    THE EXCLUSIVE WORD: [openat_excl_spec]'s -EEXIST for every name that
    exists ([is_excl_append_create] gives the derivation), and the same
    creation as the plain word for one that does not.  The -EEXIST is
    deterministic, as the exclusive shape's is; only the creation admits
    an [openat_errnos] alternative.  One thing differs from
    [openat_excl_spec], and it is what that arm would do if no example
    already reached it: a name longer than [Uapi.NAME_MAX] declines,
    ahead of the implied-directory test and the lookup.  No such name
    can exist, so the create would reach the filesystem's own
    -ENAMETOOLONG, which [openat_dir_spec] declines for the same reason
    and the create arms answer by minting the key.

    A DIRECTORY REFERENCE IS -EEXIST, with no second answer.  Main LPS
    4d80c33d83 admits -EISDIR beside it, for kernels v4.17 through v5.6.
    This model describes Linux v6.18.46 alone
    (dispatch://OSSV-266/ask/9128d2b8), and an [alt] over two kernel
    versions is the same defect as an [alt] over two systems.  At
    v6.18.46 [do_open] (fs/namei.c) returns -EEXIST at
    [(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)], the test
    before [d_is_dir(nd->path.dentry)], so -EEXIST is the whole
    answer. *)
Definition openat_append_spec (excl : bool) (p : path) (m : Model)
    : Sys SyscallEffect :=
  if excl then
    (if path_is_dirref p then err_ret EEXIST
     else if Nat.ltb NAME_MAX (length p) then unmodeled  (* the filesystem's own -ENAMETOOLONG *)
     else if fs_under (m_fs m) p then err_ret EEXIST
     else
       match fs_lookup (m_fs m) p with
       | Some _ => err_ret EEXIST
       | None => open_append p m
       end)
  else if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else open_append p m.

(** Resolve an exclusive write-create open after pathname fetch.  A
    directory reference and an implied directory are -EEXIST, not
    -EISDIR: [do_open] tests O_EXCL against [FMODE_CREATED] before it
    tests [d_is_dir], and a name that exists — as a key, as ".", or as
    the directory some key lives under — was not created (see above
    [openat_create_spec]). *)
Definition openat_excl_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EEXIST
  else
    match fs_lookup (m_fs m) p with
    | Some _ => err_ret EEXIST
    | None => create_wronly p m
    end.

(** The effect a modeled READ-WRITE open records: either an errno from
    [openat_errnos], or the lowest free fd bound to a [State.FdFileRW]
    on [p], with the file system left as [fs'].

    THE OFFSET STARTS AT 0 for both directions, and it is the same
    [f_pos] both use: [alloc_empty_file] (fs/file_table.c) zeroes the
    [struct file], and nothing on the O_RDWR path assigns to [f_pos] at
    open time (Linux v6.18.46).  O_TRUNC does not move it either — it empties the file
    through [handle_truncate] and leaves the position alone, which is
    why a truncating open is [fs'] and not an offset.

    THE REGULAR-FILE PREMISE OF [create_wronly] IS SHARED, unchanged:
    [p] is an uninterpreted byte string, so a name Linux would resolve
    to a device, FIFO or kernfs attribute is recorded here as an
    ordinary file.
    This kind widens that premise's reach by one direction rather than
    by a new premise: a character device opened O_RDWR is readable AND
    writable in the model, where the other kinds open the same name one
    way at a time. *)
Definition open_rdwr (p : path) (fs' : Fs.Fs) (m : Model)
    : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)  (* untracked env failure or no free fd *)
      (fd <- lowest_fd (m_fds m) ;;
       set_fs fs' ;;
       set_fds (fd_insert (m_fds m) fd (FdFileRW p (Z_to_bv 64 0))) ;;
       ret_only fd).

(** Resolve one of the four non-exclusive READ-WRITE open words, with
    [creat] and [trunc] the two bits that separate them
    ([rdwr_open_word] says why they are one arm).

    THE FOUR ANSWERS, all of them [do_open]'s (fs/namei.c, Linux
    v6.18.46) and none of them new to this file:

    - a DIRECTORY REFERENCE, or an IMPLIED directory ([fs_under], see
      above [openat_create_spec]), is -EISDIR whatever the two bits say,
      and the two bit settings reach it at different sites.  With O_CREAT it
      is [do_open]'s own [d_is_dir(nd->path.dentry)], inside the
      [open_flag & O_CREAT] block; without it, nothing in that block
      runs and the answer comes from [may_open]'s [case S_IFDIR:
      if (acc_mode & MAY_WRITE) return -EISDIR], with MAY_WRITE present
      because [build_open_flags] (fs/open.c) sets
      [acc_mode = ACC_MODE(flags)] and [ACC_MODE] maps O_RDWR to
      MAY_READ|MAY_WRITE (include/linux/fs.h).  Same errno, two
      derivations, and the second is the one O_RDONLY never reaches —
      which is why the plain read arm hands "." a descriptor and this
      arm cannot.
    - an ABSENT name is a fresh empty file under O_CREAT and -ENOENT
      without it.  The -ENOENT is [lookup_open]'s negative dentry with
      no LOOKUP_CREATE, the same answer [openat_read_spec] gives.
    - an EXISTING file is emptied under O_TRUNC and keeps its bytes
      without it.  [do_open] arms [handle_truncate] on
      [d_is_reg(nd->path.dentry) && open_flag & O_TRUNC]; nothing else
      on this path touches the file's contents at open time.
    - a file the open just CREATED is empty either way, which is why
      [creat] and [trunc] do not have to be composed on that branch.
      Linux says the same thing rather than merely agreeing by
      arithmetic: [do_open] clears O_TRUNC from [open_flag] under
      [file->f_mode & FMODE_CREATED] before the truncate test, so a
      created file is never truncated at all. *)
Definition openat_rdwr_spec (creat trunc : bool) (p : path) (m : Model)
    : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else
    match fs_lookup (m_fs m) p with
    | None =>
        if creat then open_rdwr p (fs_set (m_fs m) p []) m
        else err_ret ENOENT
    | Some _ =>
        open_rdwr p (if trunc then fs_set (m_fs m) p [] else m_fs m) m
    end.

(** Resolve an exclusive READ-WRITE create open.  The shape of
    [openat_excl_spec] with the fd kind changed and no other
    difference: O_EXCL's -EEXIST is decided before any type test, so a
    directory reference or an implied directory answers -EEXIST here
    rather than the -EISDIR [openat_rdwr_spec] gives it. *)
Definition openat_rdwr_excl_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EEXIST
  else
    match fs_lookup (m_fs m) p with
    | Some _ => err_ret EEXIST
    | None => open_rdwr p (fs_set (m_fs m) p []) m
    end.

(** Resolve an O_RDONLY|O_DIRECTORY open after pathname fetch.

    THE ARM EXISTS BECAUSE -ENOTDIR IS TYPE-BLIND.  [build_open_flags]
    (fs/open.c) turns O_DIRECTORY into LOOKUP_DIRECTORY, and [do_open]
    (fs/namei.c) answers -ENOTDIR for any resolved dentry that
    [d_can_lookup] (include/linux/dcache.h) refuses.  That test runs
    after the O_CREAT block and before both [may_open] (fs/namei.c) and
    [vfs_open] (fs/open.c).  So the model does NOT have to know which
    kind of non-directory a key names: a FIFO, a socket, a character
    device and a regular file all answer -ENOTDIR, and none of them gets
    as far as the file operations that would make them differ.  This is
    the one openat arm that does not rest on the model's regular-file
    premise.  Linux v6.18.46.

    THE ANSWERS.

    - "." and ".." are directories the walk settles out of itself
      ([path_is_dirref]), so LOOKUP_DIRECTORY is satisfied and the open
      succeeds with the same [FdDir] the plain read arm hands back.  The
      whole argument for answering ".." — and the condition that would
      falsify it — is on [path_is_dirref]; nothing here weakens it,
      because this arm mints exactly the entry that arm already mints.
    - a name the map HOLDS is a non-directory, hence -ENOTDIR.
    - a name the map does not hold does not resolve, hence -ENOENT, the
      same deterministic answer the read arm gives for it.

    BOTH OF THOSE ERRNOS ARE DETERMINISTIC, with no [openat_errnos]
    alternative beside them, so they join the arms
    [openat_body_spec]'s APPROXIMATION paragraph enumerates: a real
    kernel out of descriptors answers -EMFILE before path resolution
    reaches either, and this arm insists on the resolution errno.  That
    paragraph carries the argument and the cost; this is the pointer to
    it.

    TWO GUARDS THIS ARM TAKES THAT THE READ ARM CANNOT, and the
    asymmetry is deliberate rather than an oversight.  A single component
    over [Uapi.NAME_MAX] is the FILESYSTEM'S -ENAMETOOLONG, which a model
    with no filesystem type cannot pick; a name some key lives UNDER
    ([Fs.Namei.fs_under]) is an implied directory, where this arm would
    answer -ENOENT and Linux would hand back a directory fd.  Both are
    real gaps in the read arm too, and the NAME_MAX one in the
    write-create arms, and neither can be GUARDED there: [Examples.cp_ns] and
    [Examples.headcp_ns] reach those arms with argv-derived paths of
    length 256..4095, and a new [unmodeled] an example reaches makes its
    [Equivalence.strong_universal_T] FALSE rather than narrower.  No
    example can reach THIS arm — it is selected by a flag word every
    example's opens leave clear — so the guards are free here and are
    taken.
    [Fs.Open.faccessat_body_spec] carries the same two for the same
    reasons.  The write-create arms ANSWER the implied directory instead
    of guarding it (see above [openat_create_spec]): their answer is
    deterministic and image-independent where this arm's would be a
    directory fd the model has no path for.

    WHAT IS STILL NOT ANSWERED, and it is the case the flag is usually
    reached for: a directory named by a path with a separator in it.
    [openat_resolved_spec]'s hoisted guard declines that before any flag
    is looked at, so `openat(AT_FDCWD, "/usr/share/x", O_RDONLY |
    O_DIRECTORY)` is [unmodeled] and this arm never sees it.  The only
    directories a plain name can denote in a flat map are "." and "..".

    WHAT THE -ENOENT RESTS ON is the WORLD [faccessat_spec] states in
    full: every key is a regular file directly in the working directory
    and the working directory holds nothing else.  A real directory the
    map does not hold — an EMPTY one, which no [fs_under] can see —
    answers 0 on Linux and -ENOENT here.  That is the flat-namespace
    false rejection [openat] already has, not a new one: the read arm
    answers the same -ENOENT for the same name. *)
Definition openat_dir_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p then
    open_result_spec m
      (fun fd => with_fds (fd_insert (m_fds m) fd FdDir))
  else if Nat.ltb NAME_MAX (length p) then unmodeled
    (* the filesystem's own -ENAMETOOLONG, which no filesystem type here
       can supply *)
  else if fs_under (m_fs m) p then unmodeled
    (* p names an implied directory: Linux resolves it, the map cannot *)
  else
    match fs_lookup (m_fs m) p with
    | None => err_ret ENOENT
    | Some _ => err_ret ENOTDIR   (* a key is never a directory *)
    end.

(** Dispatch a fetched, nonempty AT_FDCWD pathname by modeled flag shape. *)
(** THE ONE PATHNAME SHAPE [openat] CANNOT JUDGE: one with a separator
    in it.

    The interpreted file system is a FLAT map from whole byte strings to
    contents ([Fs]): it has no directory structure.  Without a walk the
    model cannot reach any of the answers a walk produces — the -ENOENT
    of a missing parent, the -ENOTDIR of a non-directory component, the
    -EISDIR of a trailing slash on a file — and it cannot tell that two
    spellings name one file.  Its flat key is not any of those answers,
    it is a fourth thing.  So it declines, using the guard
    [Fs.Namei.unlinkat_body_spec] and [faccessat_body_spec] below already
    carry; faccessat's own WORLD paragraph names openat as sharing the
    gap, and this closes openat's half of it.

    ".." IS NOT HERE, deliberately.  It has no separator and the model
    knows its answers exactly, so it is an ARM ([path_is_dirref] above)
    rather than a decline.  A decline is for what the model cannot
    judge.

    THE SEPARATOR-BEARING PATHS THAT ARE ANSWERED are the exceptions
    that state the rule.  "/etc/localtime" ([localtime_path]) answers
    -ENOENT under a declared assumption about the image: the
    model still cannot judge the path, what it has is a declaration
    about the environment, and the arm's comment says exactly what that
    declaration covers and what it does not.  "/dev/null"
    ([Uapi.devnull_path]) and "/dev/urandom" ([Uapi.urandom_path]) are
    DEVICES, whose every answer comes from a driver rather than from
    the file system, so the flat map's silence about directories costs
    nothing there.  [openat_sep_spec] is tested before the decline and
    dispatches all of them.
    WHAT IS NOT GUARDED HERE, and why this file's two syscalls differ.
    faccessat also declines a component over [NAME_MAX] and a name that
    [fs_under] shows is an implied directory.  Neither guard is added
    here because neither can be discharged in [Examples.cp_ns] and
    [Examples.headcp_ns]: their argv-derived paths range over lengths
    256..4095, and [Fs.valid_fs] permits an image whose keys live under
    an argv name.  Guarding either makes
    [Equivalence.strong_universal_T] FALSE for both examples rather than
    narrower, which is a different thing from the narrowing this guard
    does make (see [Run.valid_argv]).  The implied directory is instead
    ANSWERED on the write-create arms — a deterministic -EISDIR or
    -EEXIST that both examples' proofs carry as a lane of their own (see
    above [openat_create_spec]) — and stays a gap on the read arm, which
    answers -ENOENT where Linux opens the directory.  The [NAME_MAX]
    component cannot be answered on any arm: it is a property of the
    FILESYSTEM, not of fs/namei.c.  [link_path_walk] bounds nothing
    per-component; the -ENAMETOOLONG comes out of the filesystem's own
    `->lookup`: the EXT4_NAME_LEN test in [ext4_lookup] and
    [__ext4_find_entry], fs/ext4/namei.c, and the NAME_MAX test in
    [simple_lookup], fs/libfs.c (both Linux v6.18.46).  A model with no
    filesystem type that answered 255 would be inventing one, and would
    be wrong on a filesystem whose limit differs.

    DIRECTION.  This decline is for SOUNDNESS, not a coverage cost.
    Without it, the create shapes above would answer SUCCESS for every
    such path and mint a flat key for it: [openat(AT_FDCWD, "/no/such/file",
    O_WRONLY|O_CREAT|O_TRUNC, 0644)] would return an fd where Linux returns
    -ENOENT, and no [openat_errnos] alternative could rescue it, because
    neither ENOENT nor EISDIR is injectable.  That would be the model
    admitting a trace Linux refuses. *)

(** A pathname the read and write-create arms above resolve on their own
    terms: not a directory reference, and not slash-bearing.  This is the
    premise the whole-program examples carry about their argv-derived
    paths; [Run.valid_argv]'s fifth clause is what supplies it.

    IT DOES NOT SAY WHETHER THE NAME IS AN IMPLIED DIRECTORY.  That is a
    fact about the image, not the path, so the write-create arms test
    [fs_under] beside it and the examples split on that test where they
    reach those arms: a plain name some key lives under is the -EISDIR
    lane, and a plain name nothing lives under is the create.

    IT IS NOT ENOUGH FOR [openat_dir_spec], which is why that arm is not
    counted here: being plain does not get a name past that arm's
    [Uapi.NAME_MAX] and [Fs.Namei.fs_under] guards.  No example reaches
    it, so nothing needs it to. *)
Definition openat_plain_name (p : path) : bool :=
  negb (path_is_dirref p) && negb (path_has_slash p).

Lemma openat_plain_name_nodirref : forall p,
  openat_plain_name p = true -> path_is_dirref p = false.
Proof.
  intros p H. unfold openat_plain_name in H.
  apply andb_prop in H. destruct H as [H _].
  now apply negb_true_iff in H.
Qed.

Lemma openat_plain_name_noslash : forall p,
  openat_plain_name p = true -> path_has_slash p = false.
Proof.
  intros p H. unfold openat_plain_name in H.
  apply andb_prop in H. destruct H as [_ H].
  now apply negb_true_iff in H.
Qed.

(** A directory reference has no separator, so the dot arms get past the
    guard from the same hypothesis that selects them. *)
Lemma path_is_dirref_no_slash : forall p,
  path_is_dirref p = true -> path_has_slash p = false.
Proof.
  intros p H. unfold path_is_dirref in H.
  apply orb_true_elim in H. destruct H as [H|H];
    apply path_eqb_eq in H; subst p; reflexivity.
Qed.

(** "/etc/localtime", the file a C library's [tzset] opens to learn the
    local zone: musl 1.2.6 src/time/__tz.c, [do_tzset], takes it when
    TZ is unset and hands it to src/time/__map_file.c, which opens
    it O_RDONLY|O_CLOEXEC|O_NONBLOCK; glibc's tzfile reader opens the
    same path.  It is the ONE absolute path this file answers, and the
    answer is -ENOENT.

    THIS IS A DECLARED ENVIRONMENT ASSUMPTION: an O_CREAT-free open of
    /etc/localtime answers -ENOENT in the image.  Spelled out, /etc is a
    directory, and the walk of /etc/localtime reaches no inode: either
    there is no entry, or there is a symlink whose own target walk
    answers -ENOENT.  A dangling symlink at /etc/localtime is INSIDE
    that premise — every admitted word lacks O_NOFOLLOW, so the trailing
    [step_into] follows it and the target's walk answers the same
    -ENOENT — and a regular file at /etc is OUTSIDE it, where
    [link_path_walk] answers -ENOTDIR and the model would be wrong
    rather than declined.  Nothing in the model derives the premise,
    and no [in_fs] a caller supplies can state it, because the flat map
    has no way to say "this absolute path is absent" any more than it
    can say "this name is a device".  It is an assumption about the
    environment every run is launched in, of the same kind as the
    "working directory holds nothing else" world [faccessat_spec]
    states, and it is written down here, at the arm that consumes it,
    so that a reader who changes the image knows what to revisit.

    WHAT IT BUYS.  A program that calls [localtime], [ctime_r] or
    anything else that runs [tzset] opens this path before it does
    anything the model can see, often before [main]; with the separator
    decline alone that open would be [unmodeled] and the run would leave
    the modeled surface on its first timestamp.  For [tzset] a missing file
    is the ordinary case — the library falls back to UTC — so the
    -ENOENT is image-independent and needs no content model.

    THE KERNEL PATH.  Under a flag word WITHOUT O_CREAT the walk reaches
    the last component and finds no inode: [open_last_lookups]
    (fs/namei.c) takes the [lookup_fast_for_open] or [lookup_open]
    result, a negative dentry, into [step_into], whose [handle_mounts]
    calls [traverse_mounts], and that answers -ENOENT for a dentry
    [d_flags_negative] is true of (all fs/namei.c, Linux v6.18.46).
    This runs before [do_open], so neither the O_DIRECTORY -ENOTDIR test
    nor [may_open] is reached, and the answer does not turn on the
    access mode: O_RDONLY, O_RDWR, O_RDWR|O_TRUNC and O_RDONLY|O_DIRECTORY
    are -ENOENT alike.

    THE ARM IS FLAG-BLIND, AND THAT IS SOUND ONLY BECAUSE OF THE ORDER.
    It tests the O_CREAT bit and nothing else; read alone it would
    answer -ENOENT to O_TMPFILE, where [build_open_flags] is -EINVAL
    before any walk, and to O_NOFOLLOW on a dangling link, where the
    answer is -ELOOP.  Neither reaches it: [openat_core_spec] refuses
    every flag word [modeled_open_flags] does not admit BEFORE the
    pathname is fetched, so the O_CREAT-free residues that arrive here
    are exactly O_RDONLY, O_RDONLY|O_DIRECTORY, O_RDWR and
    O_RDWR|O_TRUNC, the words the paragraph above answers for.  A
    widening of [modeled_open_flags] has to revisit this arm.  The
    O_PATH words were that widening, and they do not reach it:
    [openat_body_spec] declines an O_PATH word on every name that is
    not a procfs one, ahead of [openat_resolved_spec].

    WHAT IT DOES NOT COVER, each fail-closed rather than answered:

    - Any word WITH O_CREAT.  [lookup_open] (fs/namei.c) would create the
      file under /etc, a directory the model has no representation of
      and no parent to create anything in; answering success would mint
      a key the map cannot mean, which is the unsoundness the separator
      decline exists to prevent.
    - An image whose map HOLDS the key "/etc/localtime", or a key under
      it.  A program that ships a zoneinfo file in its image is opening
      a file the model has under that key, and the assumption does not
      hold for that image.  It is declined, not answered from the map,
      for the reason [Checks.Cases.Fs.Open.openat_slash_key_in_image_unmodeled]
      pins for every slash-bearing key: the map does not say whether the
      key is the absolute path or a working-directory name spelled with
      separators, so it cannot judge the open.  (And a key UNDER it makes
      the path a directory Linux would open where -ENOENT is wrong.)
      This guard is a courtesy to an [in_fs] that contradicts the
      premise, not part of the soundness argument: [Fs.valid_fs] admits
      a key spelled "etc/localtime" with the working directory at "/",
      which names the same file, and the arm answers -ENOENT over it.
      Under the premise no such key exists in any spelling.

    THE MATCH IS ON THE EXACT BYTE STRING.  "/etc//localtime",
    "/etc/./localtime" and "//etc/localtime" name the same file on Linux
    and are all declined here: the assumption was declared for one
    spelling, and the model has no walk to identify the others with
    it. *)
Definition localtime_path : path :=
  [Z_to_bv 8 47; Z_to_bv 8 101; Z_to_bv 8 116; Z_to_bv 8 99; Z_to_bv 8 47;
   Z_to_bv 8 108; Z_to_bv 8 111; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 108;
   Z_to_bv 8 116; Z_to_bv 8 105; Z_to_bv 8 109; Z_to_bv 8 101].

Definition openat_localtime_spec (flags : word) (m : Model)
    : Sys SyscallEffect :=
  match fs_lookup (m_fs m) localtime_path with
  | Some _ => unmodeled   (* the image ships the file: the assumption fails *)
  | None =>
      if fs_under (m_fs m) localtime_path then unmodeled  (* ...or a directory there *)
      else if flag_set (Z.ldiff (bv_unsigned flags) open_ignored_flags) O_CREAT
      then unmodeled      (* Linux would create it; the model has no /etc *)
      else err_ret ENOENT
  end.

(** "/dev/null", the one DEVICE this file answers, and the descriptor
    kind [State.FdDevNull] it mints.

    THE ENVIRONMENT ASSUMPTION, stated here and consumed by every arm
    that answers for the kind: the image's /dev/null is the null
    device, character major 1 minor 3, whose operations are
    [null_fops] (drivers/char/mem.c, Linux v6.18.46).  That is what the
    name means on every Linux system — [devlist[3]] is "null" and
    devtmpfs, or the container runtime, creates the node from it — and
    it is the reason the arm is SOUND without a filesystem: nothing
    Linux does through this descriptor depends on the image, because
    [null_fops] never touches a page, a buffer or an inode's contents.
    The assumption does NOT reach an image whose map holds the key
    "/dev/null" or a key under it; that image is declined.  The guard
    on the map is a courtesy to a contradicting [in_fs], not part of
    the soundness argument.

    THE KERNEL PATH the flag words take, all fs/namei.c v6.18.46 and
    all decided before the device's own [open] runs:

    - O_RDONLY, and the READ-WRITE words without O_EXCL: [do_open]
      reaches [may_open], whose S_IFCHR arm passes
      ([may_open_dev] is the one thing it tests, and -EACCES from it is
      already an [openat_errnos] alternative), then [vfs_open] ->
      [do_dentry_open] (fs/open.c) -> [chrdev_open] (fs/char_dev.c)
      -> [memory_open] (drivers/char/mem.c), which installs
      [null_fops].  The descriptor carries the access mode
      [do_dentry_open] set: FMODE_READ, FMODE_WRITE or both.
    - O_WRONLY|O_CREAT|O_TRUNC: the same, because O_CREAT on an
      existing name creates nothing — [lookup_open] finds the positive
      dentry and [FMODE_CREATED] stays clear — and [do_open] arms
      [handle_truncate] only under [d_is_reg(nd->path.dentry)], which a
      character device fails, so the O_TRUNC is inert.
    - O_WRONLY|O_CREAT|O_APPEND: the same again.  O_APPEND reaches
      [f_flags] and nothing in [null_fops] reads it: [write_null] and
      [write_iter_null] return the count without consulting a position
      (mem.c's own comment on [null_lseek] says fopen with "a" is the
      point), and no modeled arm on this kind reads [f_flags]
      ([Fcntl.getfl_f_flags] and [Fcntl.setfl_noop_on] both decline it),
      so the append word mints the same write-only entry the clobbering
      word does.  That is exactly the O_APPEND-is-unobservable argument
      [State.FdFileA] exists because a REGULAR file breaks; here it
      holds.
    - O_CREAT|O_EXCL, in every admitted word that carries it (either
      access mode, with or without O_APPEND): [do_open]'s
      [(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)] is
      -EEXIST, before [may_open] — deterministic, as on every existing
      name.
    - O_RDONLY|O_DIRECTORY: [do_open]'s [(nd->flags & LOOKUP_DIRECTORY)
      && !d_can_lookup(...)] is -ENOTDIR; [openat_dir_spec] carries the
      same argument for a plain name.

    THE MATCH IS ON THE EXACT BYTE STRING, as for every answered
    absolute path: "/dev//null" and "/dev/./null" stay declined.

    WHY A DEVICE AND NOT A FILE.  If this name were a key, a read would
    hand back bytes a write had recorded, where [read_null] returns
    0.  [State.FdDevNull] carries no path and no contents, so no arm can
    make that mistake; each answers from [null_fops] or declines.

    The byte string itself is [Uapi.devnull_path], shared with
    [Fs.Stat.fstat_devnull_spec]. *)

(** The success shape every admitted word shares: the injectable errno,
    or the lowest free fd bound to the entry with the granted mode. *)
Definition open_devnull (m : Model) (rd wr : bool) : Sys SyscallEffect :=
  open_result_spec m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdDevNull rd wr))).

Definition openat_devnull_spec (flags : word) (m : Model)
    : Sys SyscallEffect :=
  match fs_lookup (m_fs m) devnull_path with
  | Some _ => unmodeled   (* the image ships a FILE under the name: outside the assumption *)
  | None =>
      if fs_under (m_fs m) devnull_path then unmodeled  (* ...or a directory there *)
      else
      let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
      if Z.eqb fl 0 then open_devnull m true false
      else if Z.eqb fl wr_create_flags then open_devnull m false true
      else if is_excl_create fl then err_ret EEXIST
      else if Z.eqb fl O_DIRECTORY then err_ret ENOTDIR
      else if Z.eqb fl append_create_flags then open_devnull m false true
      else if rdwr_open_word fl then open_devnull m true true
      else if is_rdwr_excl_create fl then err_ret EEXIST
      else if is_excl_append_create fl then err_ret EEXIST
      else unmodeled   (* unreachable: [modeled_open_flags] admitted the word *)
  end.

(** "/dev/urandom", the second DEVICE this file answers, and the
    descriptor kind [State.FdUrandom] it mints.

    THE ENVIRONMENT ASSUMPTION, stated here and consumed by every arm
    that answers for the kind: the image's /dev/urandom is the random
    device, character major 1 minor 9, whose operations are
    [urandom_fops] (drivers/char/random.c, Linux v6.18.46) —
    [devlist[9]] is "urandom" (drivers/char/mem.c) and devtmpfs, or the
    container runtime, creates the node from it.  The assumption does
    NOT reach an image whose map holds the key "/dev/urandom" or a key
    under it; that image is declined.

    WHAT THE BYTES ARE.  Not a choice: the run's [State.in_urandom]
    declares them, in order, and [ReadWrite.read_urandom] hands them
    out from the front.  So /dev/urandom is an ARBITRARY BUT FIXED
    stream, a parameter of the
    execution like argv and envp, the same stream on both sides of an
    equivalence — and it is what makes a program that seeds itself from
    the device provable at all: every equivalence is proved for every
    stream, and no statement quantifies over the generator.
    [getrandom] (278) is deliberately NOT drawn from it; the two stay
    unrelated in the model.

    THE KERNEL PATH the flag words take, all fs/namei.c v6.18.46 and
    all decided before the device's own [open] runs:

    - O_RDONLY: [do_open] reaches [may_open], whose S_IFCHR arm passes
      ([may_open_dev] is the one thing it tests, and -EACCES from it is
      already an [openat_errnos] alternative), then [vfs_open] ->
      [do_dentry_open] (fs/open.c) -> [chrdev_open] (fs/char_dev.c) ->
      [memory_open] (drivers/char/mem.c), which installs
      [urandom_fops].  The descriptor carries FMODE_READ, FMODE_PREAD
      and FMODE_LSEEK ([do_dentry_open] sets the latter two and
      [memory_open] clears nothing).
    - O_CREAT|O_EXCL, in every admitted word that carries it (either
      access mode, with or without O_APPEND): [do_open]'s
      [(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)] is
      -EEXIST, before [may_open] — deterministic, as on every existing
      name.  That is why the exclusive APPEND word is answered here
      although it is a write word: it never opens the device.
    - O_RDONLY|O_DIRECTORY: [do_open]'s [(nd->flags & LOOKUP_DIRECTORY)
      && !d_can_lookup(...)] is -ENOTDIR.
    - THE WRITE WORDS ARE DECLINED, not answered: O_WRONLY and O_RDWR,
      with or without O_CREAT, O_TRUNC and O_APPEND, and without
      O_EXCL.  Linux admits them
      — [may_open] passes, [may_open]'s [flag &= ~O_TRUNC] drops the
      truncation, and a write through the descriptor reaches
      [random_write_iter], which mixes the bytes into the input pool
      ([write_pool_user]) and returns the count — and the model does
      not model writes into the pool, nor a descriptor on this device
      that could carry them.  A program that opens the device for
      writing leaves the modeled surface at the open.

    THE MATCH IS ON THE EXACT BYTE STRING, as for every answered
    absolute path: "/dev//urandom" and "/dev/./urandom" stay declined,
    and so does "/dev/random", which is a different device
    ([random_fops] blocks until the pool is ready).

    The byte string itself is [Uapi.urandom_path], shared with
    [Fs.Stat.fstat_urandom_spec]. *)

(** The success shape: the injectable errno, or the lowest free fd
    bound to the read-only entry. *)
Definition open_urandom (m : Model) : Sys SyscallEffect :=
  open_result_spec m
    (fun fd => with_fds (fd_insert (m_fds m) fd FdUrandom)).

Definition openat_urandom_spec (flags : word) (m : Model)
    : Sys SyscallEffect :=
  match fs_lookup (m_fs m) urandom_path with
  | Some _ => unmodeled   (* the image ships a FILE under the name: outside the assumption *)
  | None =>
      if fs_under (m_fs m) urandom_path then unmodeled  (* ...or a directory there *)
      else
      let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
      if Z.eqb fl 0 then open_urandom m
      else if is_excl_create fl then err_ret EEXIST
      else if Z.eqb fl O_DIRECTORY then err_ret ENOTDIR
      else if is_rdwr_excl_create fl then err_ret EEXIST
      else if is_excl_append_create fl then err_ret EEXIST
      else unmodeled   (* the write words ([wr_create_flags],
                          [append_create_flags], [rdwr_open_word]):
                          admitted by Linux into the pool, declined here *)
  end.

(** "/tmp/<name>", the run's own PRIVATE temporary directory: the third
    absolute shape this file answers for, and the first that is a
    FILE rather than a device.

    THE ENVIRONMENT ASSUMPTION, stated here and consumed by the two
    arms below and by [Fs.Namei.unlinkat_tmp_spec]: /tmp is a distinct,
    WRITABLE directory PRIVATE to this run.  What that buys is the only
    thing the flat map needs — that the run's own table is the whole
    truth about the directory.  What the run holds there is
    [State.in_tmp], the environment's declaration, plus what
    [create_wronly] created, minus what [Fs.Namei.unlinkat_spec]
    removed, and nothing outside the run can add a name or take one
    away between two of its syscalls.  Without privacy a second process
    could create the name between the run's own -ENOENT and its create,
    and the model would be answering about a directory it does not
    have.

    THE NAME IS AN INPUT, not a choice: [State.in_tmp] is arbitrary but
    fixed, a parameter of the execution as argv and envp are, and the
    SAME directory is seen by the source and the target of a pair, so
    every equivalence is proved for every declared /tmp.
    [State.fs_seed_tmp] seeds it into the initial file system under the
    absolute keys this arm reads, which is why read, write, lseek,
    fstat, fsync and close on the descriptor are the EXISTING
    [FdFile]/[FdFileW] arms, untouched: nothing here mints a new
    descriptor kind.

    THE THREE SHAPES ANSWERED, and only these:

    - O_WRONLY|O_CREAT|O_TRUNC of "/tmp/<name>" goes to
      [openat_create_spec], which is what the plain arm does for a name
      in the working directory — the same arm, so the -EISDIR it
      answers for a directory the map implies is answered here too (see
      THE IMPLIED DIRECTORY below).  The mode argument is ignored there
      as it is here.
    - O_RDONLY of a "/tmp/<name>" whose key the run HOLDS goes to
      [openat_read_spec].
    - the removal is [Fs.Namei.unlinkat_spec]'s arm.

    EACH FLAG WORD IS MATCHED PAST THE FILE'S SHARED IGNORED MASK,
    [open_ignored_flags], and not past O_CLOEXEC alone: the mask is
    O_CLOEXEC, O_LARGEFILE and O_NONBLOCK, and [Z.ldiff] strips all
    three before the test, exactly as every other arm in this file does.
    So O_RDONLY|O_NONBLOCK and O_RDONLY|O_LARGEFILE reach the read arm
    and the create word reaches the create arm with any of the three
    set.  All three are inert on a regular file — O_CLOEXEC is a
    descriptor-table flag the model does not record, O_LARGEFILE is
    unconditional on a 64-bit ABI, and O_NONBLOCK on a regular file
    changes no answer any modeled operation gives — which is the
    argument the mask's own definition carries and the reason this arm
    does not narrow it.

    Every other word is DECLINED rather than answered: O_RDWR in either
    creating shape, O_APPEND, the O_EXCL words, O_DIRECTORY, and plain
    O_RDONLY of a name the run does not hold.  Linux answers all of
    them, and the model could derive several; this arm answers only
    the three shapes above and declines the rest, which is the narrower
    choice at every one of them.  A read of
    a name not held is the one worth naming twice: -ENOENT would follow
    from the privacy premise, and the decline is a choice, not a
    gap in the derivation.

    THE ONE GUARD AHEAD OF THE FLAG TEST.

    [Uapi.NAME_MAX] is the FILESYSTEM's own -ENAMETOOLONG, which
    fs/namei.c does not produce and a model with no filesystem type
    cannot invent (see [openat_plain_name]'s note, which explains why
    the plain arms cannot afford this guard and this one can: no
    example's argv reaches a /tmp path).

    THE IMPLIED DIRECTORY IS ANSWERED ON THE CREATE WORD AND DECLINED
    ON THE READ WORD, which is why [Fs.Namei.fs_under] is tested inside
    each word instead of ahead of both.  The declaration may name
    "a/b", and then "/tmp/a" is a DIRECTORY in the run's own /tmp: the
    flat map holds no directory, but a key living under the path is
    what says one is there, and that is the reading
    [openat_create_spec] already makes of a working-directory name.
    The two words part company because what Linux answers costs the
    model different things:

    - the create word IS [openat_create_spec], reached here rather than
      restated, so the /tmp arm and the working-directory arm cannot
      drift apart.  A name the map implies is a directory answers
      [do_open]'s deterministic -EISDIR, taken under O_CREAT without
      O_EXCL and before [may_open] ever runs; the derivation, and why
      an ANSWER rather than a decline is the faithful choice, is
      written out above [openat_create_spec] and none of it is special
      to the working directory.  [path_is_dirref] is inert on this arm
      — [tmp_name] admits only a path beginning "/tmp/" and refuses "."
      and ".." — and sharing the arm anyway costs a test that cannot
      fire and buys a restatement that cannot rot.
    - the read word DECLINES it, which is a choice and
      not a gap in the derivation: answering means handing back a
      DIRECTORY DESCRIPTOR, and the model has no directory semantics to
      hand one out of.  That is the same trade the working-directory
      read arm makes.  The test stays
      inside the read branch rather than being dropped, because
      [Fs.valid_fs] admits an image holding "/tmp/a" and "/tmp/a/b" at
      once, and without it the lookup would hand out an [FdFile] on a
      name reality makes a directory. *)
Definition openat_tmp_spec (n p : path) (flags : word) (m : Model)
    : Sys SyscallEffect :=
  if Nat.ltb NAME_MAX (length n) then unmodeled
  else
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
  if Z.eqb fl 0 then
    (if fs_under (m_fs m) p then unmodeled  (* a directory descriptor: deferred *)
     else match fs_lookup (m_fs m) p with
          | None => unmodeled     (* a key the run does not hold *)
          | Some _ => openat_read_spec p m
          end)
  else if Z.eqb fl wr_create_flags then openat_create_spec p m
  else unmodeled.   (* every other word: see the comment above *)

(** The pathnames with a separator that are ANSWERED, tested ahead of
    the separator decline.  Only a path with a separator can match, so
    the dispatch sits inside the true branch of [path_has_slash] in
    [openat_resolved_spec]: same answers as testing them first, and the
    slash-free arms and every proof that unfolds them are untouched.
    A path with a separator that no arm here names is the decline the
    paragraph above this one argues for. *)
Definition openat_sep_spec (p : path) (flags : word) (m : Model)
    : Sys SyscallEffect :=
  if path_eqb p localtime_path then openat_localtime_spec flags m
  else if path_eqb p devnull_path then openat_devnull_spec flags m
  else if path_eqb p urandom_path then openat_urandom_spec flags m
  else match tmp_name p with
       | Some n => openat_tmp_spec n p flags m
       | None => unmodeled
       end.

(** ORDER.  The guard is hoisted above the flag test rather than
    repeated inside each arm, and what makes that safe is a reachability
    fact about this file rather than an argument about Linux:
    [openat_core_spec] has ALREADY refused every flag word the model
    does not interpret, through [modeled_open_flags], before this
    definition is reached.  So the [else unmodeled] below is
    unreachable, both orders answer [unmodeled] on exactly the same
    inputs, and hoisting changes no answer the model gives — only which
    of two reasons it declines for.  The kernel's order agrees, which is
    why the hoisted position is also the faithful one:  The walk that cannot be
    modeled precedes the flag-dependent decision in Linux too
    ([link_path_walk] runs before [may_open]'s -EISDIR), so the hoisted
    position is the faithful one.

    THE ARMS ARE NOT ALL TOTAL.  All but one answer every
    pathname they are handed; [openat_dir_spec] does not, and its
    declines are on the path rather than on the flag word.  The FINAL
    [else unmodeled] here is still unreachable — the branches
    exhaust what [modeled_open_flags] admits — but this dispatcher does
    not decline only above an arm: it also declines inside one, and the
    [Checks] mirror carries a matching decline inside
    [check_openat_dir]. *)
Definition openat_resolved_spec (p : path) (flags : word) (m : Model)
    : Sys SyscallEffect :=
  if path_has_slash p then openat_sep_spec p flags m else
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
  if Z.eqb fl 0 then openat_read_spec p m
  else if Z.eqb fl wr_create_flags then openat_create_spec p m
  else if is_excl_create fl then openat_excl_spec p m
  else if Z.eqb fl O_DIRECTORY then openat_dir_spec p m
  else if Z.eqb fl append_create_flags then openat_append_spec false p m
  else if rdwr_open_word fl then
    openat_rdwr_spec (flag_set fl O_CREAT) (flag_set fl O_TRUNC) p m
  else if is_rdwr_excl_create fl then openat_rdwr_excl_spec p m
  else if is_excl_append_create fl then openat_append_spec true p m
  else unmodeled.

(* =========================================================================
   Paths under /proc: the O_PATH descriptor and the /proc/sys read
   ========================================================================= *)

(** "/proc": the five bytes '/', 'p', 'r', 'o', 'c'. *)
Definition proc_root_path : path :=
  [Z_to_bv 8 47; Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 111; Z_to_bv 8 99].

(** "/proc/sys/". *)
Definition proc_sys_prefix : path :=
  proc_root_path ++
    [slash_byte; Z_to_bv 8 115; Z_to_bv 8 121; Z_to_bv 8 115; slash_byte].

(** The components of a path, split at every separator: [link_path_walk]
    (fs/namei.c) walks exactly these, skipping the empty ones a doubled
    or leading separator makes.  [cur] is the current component,
    reversed. *)
Fixpoint path_components_aux (cur : path) (p : path) : list path :=
  match p with
  | [] => [rev cur]
  | b :: r =>
      if bv_eqb b slash_byte then rev cur :: path_components_aux [] r
      else path_components_aux (b :: cur) r
  end.

(** Does some component of [p] read ".."?  [link_path_walk] types such a
    component LAST_DOTDOT and [follow_dotdot] climbs to the parent, so a
    path that starts with "/proc/" and holds one can leave procfs
    ("/proc/../etc").  The two predicates below refuse it. *)
Definition path_has_dotdot (p : path) : bool :=
  existsb (fun c => path_eqb c dotdot_path) (path_components_aux [] p).

(** [p] names procfs: it is "/proc" or starts with "/proc/", and no
    component is "..".

    TWO ENVIRONMENT ASSUMPTIONS, stated in SCOPE.md ("Assumptions that
    the model does not check"): procfs is mounted at /proc in the
    process's root, and nothing under /proc/sys is a symbolic link.  The
    first is what makes "/proc" a procfs name at all.  A procfs name can
    still be a LINK out of procfs ("/proc/self/root", "/proc/self/fd/N",
    "/proc/self/cwd"); [openat_proc_spec] says why that costs precision
    and not soundness. *)
Definition proc_path_b (p : path) : bool :=
  negb (path_has_dotdot p)
  && (path_eqb p proc_root_path
      || match path_strip_prefix (proc_root_path ++ [slash_byte]) p with
         | Some _ => true
         | None => false
         end).

(** [p] names a file under /proc/sys: it starts with "/proc/sys/" and no
    component is "..".  With the assumption above (no symbolic link
    under /proc/sys) such a path resolves inside the sysctl tree, or to
    nothing. *)
Definition proc_sys_file_b (p : path) : bool :=
  negb (path_has_dotdot p)
  && match path_strip_prefix proc_sys_prefix p with
     | Some _ => true
     | None => false
     end.

(** The procfs name an [openat] reaches, or [None] where this section
    does not apply.

    - An ABSOLUTE path is resolved from the root whatever [dirfd] is:
      [path_init] (fs/namei.c) takes [nd_jump_root] for a leading '/'
      before it looks at [nd->dfd] at all.  So [dirfd] is not consulted.
    - A RELATIVE path is resolved from [dirfd]'s [f_path] ([path_init]'s
      [CLASS(fd_raw, f)], which accepts an O_PATH file), and when that
      descriptor is an [OProcPath q] the name is [q], a separator, and
      the path.
    - Anything else ([AT_FDCWD] with a relative path, or any other
      dirfd) is [None], and the existing arms decide it.  [AT_FDCWD] is
      tested before the table is read: it is not a descriptor, and the
      test keeps the answer for a relative name from depending on what
      the table holds at the number [AT_FDCWD32].

    fs/namei.c [path_init]: read at v6.18.44; identical at v6.18.46. *)
Definition proc_open_target (fds : list (word * FdEntry)) (dirfd : word)
    (p : path) : option path :=
  match p with
  | b :: _ =>
      if bv_eqb b slash_byte then
        (if proc_path_b p then Some p else None)
      else if bv_eqb dirfd AT_FDCWD32 then None
      else
        match fd_lookup fds dirfd with
        | Some (FdOpaque (OProcPath q)) =>
            let c := q ++ slash_byte :: p in
            if proc_path_b c then Some c else None
        | _ => None
        end
  | [] => None
  end.

(** A name with no separator, from [AT_FDCWD], is never a procfs
    target: the existing arms decide it whatever the table holds. *)
Lemma proc_open_target_cwd_noslash : forall fds p,
  path_has_slash p = false -> proc_open_target fds AT_FDCWD32 p = None.
Proof.
  intros fds [|b p] H; [reflexivity|].
  cbn [proc_open_target]. cbn [path_has_slash existsb] in H.
  apply orb_false_iff in H as [Hb _]. rewrite Hb, bv_eqb_refl. reflexivity.
Qed.

(** A fresh opaque descriptor at the lowest free fd, or any errno; see
    [openat_proc_spec] for why every errno. *)
Definition proc_open_result (m : Model) (o : OpaqueFd) : Sys SyscallEffect :=
  alt (e <- errno_any ;; err_ret e)
      (fd <- lowest_fd (m_fds m) ;;
       modify (with_fds (fd_insert (m_fds m) fd (FdOpaque o))) ;;
       ret_only fd).

(** [openat] of the procfs name [c] ([proc_open_target]), as bubblewrap's
    parent issues it: [openat(AT_FDCWD, "/proc", O_PATH)],
    [openat(AT_FDCWD, "/proc/sys/kernel/overflowuid", O_RDONLY|O_CLOEXEC)]
    and [openat(proc_fd, "<pid>/ns", O_PATH)].

    TWO SHAPES ARE ANSWERED:
    - an O_PATH word ([open_path_word]) on any procfs name: an
      [OProcPath c] descriptor, or an errno;
    - O_RDONLY (with [open_ignored_flags]) on a [proc_sys_file_b] name:
      an [OProcFile c] descriptor, or an errno.
    Every other word is declined, as it was before this arm.

    KERNEL PATH, read at v6.18.44:
      fs/open.c [SYSCALL_DEFINE4(openat)], [do_sys_openat2],
        [build_open_how], [build_open_flags], [do_dentry_open]: read at v6.18.44; identical at v6.18.46.
      fs/namei.c [do_filp_open], [path_openat], [path_init],
        [link_path_walk], [do_open]: read at v6.18.44; identical at v6.18.46.
      fs/file.c [get_unused_fd_flags], [alloc_fd]: read at v6.18.44; identical at v6.18.46.
      fs/proc/proc_sysctl.c [proc_sys_open], [proc_sys_permission]: read at v6.18.44; identical at v6.18.46.

    THE SUCCESS.  [do_sys_openat2] takes the lowest free descriptor
    ([get_unused_fd_flags]) before the walk and installs the file there.
    An O_PATH file gets [FMODE_PATH] and [empty_fops] in
    [do_dentry_open], which returns before any [->open] runs (the walk's
    and [may_open]'s refusals come earlier and are errnos);
    [proc_sys_open] (the O_RDONLY case) attaches a poll event and changes
    nothing the process
    can see.  Neither open writes user memory or changes any other
    state the model holds.

    WHY EVERY ERRNO ([Syscall.errno_any]).  The walk runs through
    procfs's own lookups ([proc_root_lookup], [proc_pid_lookup], the
    per-process directories, [proc_ns_dir], [proc_sys_lookup]), through
    every magic link's [get_link] and its [ptrace_may_access] test, and
    through the LSM's [inode_permission] and [inode_follow_link] hooks;
    then [do_open]'s -ENOTDIR and -ELOOP, [proc_sys_permission]'s
    -EACCES, the descriptor table's -EMFILE and the file table's
    -ENFILE.  No list written from that would be one this model could
    defend, and a missing errno would make it reject a real run.

    WHAT THE ARM COSTS IN PRECISION (SCOPE.md, "Known gaps in
    precision").  A success is admitted for every procfs name, including
    ones Linux refuses (a pid that does not exist) and names that are
    LINKS out of procfs ("/proc/self/root/etc", "/proc/self/fd/N"): the
    descriptor is then an [OProcPath] on an object outside procfs.
    That is still sound, because nothing the model does with an
    [OProcPath] reads the object: an [openat] or a [newfstatat] relative
    to it answers any errno or an opaque result, and every other arm
    declines the kind.  An O_RDONLY open is answered only under
    "/proc/sys/", where the assumption above rules the links out.

    A PIPE CANNOT GAIN A READER OR A WRITER HERE, although
    "/proc/self/fd/N" can name one: see [State.pipe_end_live]. *)
Definition openat_proc_spec (c : path) (flags : word) (m : Model)
    : Sys SyscallEffect :=
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
  if open_path_word fl then proc_open_result m (OProcPath c)
  else if Z.eqb fl 0 && proc_sys_file_b c then proc_open_result m (OProcFile c)
  else unmodeled.

(** [openat dirfd path flags mode].  Modeled shapes (the
    [open_ignored_flags] bits are accepted and ignored in all; [mode] is
    ignored):

    - O_RDONLY: open an existing file for reading (-ENOENT if absent),
      or a directory reference ("." or "..", [path_is_dirref]) for a
      directory fd (read on it is -EISDIR; see [FdEntry]);
    - O_WRONLY|O_CREAT|O_TRUNC: create or truncate, then write
      (-EISDIR on a directory reference, and on a name the map implies
      is a directory because some key lives under it — a directory
      cannot be opened for writing; [openat_create_spec] carries the
      derivation);
    - O_WRONLY|O_CREAT|O_EXCL (with or without O_TRUNC,
      [is_excl_create]): create, then write, but only if the path does
      NOT already exist — otherwise the deterministic real -EEXIST.
      The existence test comes BEFORE any type test, as Linux's does
      (fs/namei.c: O_EXCL on a positive dentry is -EEXIST whatever the
      dentry is), so a directory reference ("." or "..") and an implied
      directory are -EEXIST here, NOT the -EISDIR of the clobbering
      shape.
    - O_RDONLY|O_DIRECTORY: a directory reference gives the same [FdDir]
      the plain read shape gives it, a name the map holds gives
      -ENOTDIR, and a name it does not hold gives -ENOENT.  This is the
      only arm that declines on the PATH rather than only on the flags:
      it refuses a component over [Uapi.NAME_MAX] and a name some key
      lives under, which the read arm cannot and the write-create arms
      answer instead ([openat_dir_spec] says why the asymmetry is
      deliberate).
    - O_WRONLY|O_CREAT|O_APPEND ([append_create_flags]): open for
      writing, creating the file empty if it is absent and leaving an
      existing file's bytes ALONE, with every write through the fd
      landing at the then-current end of file (-EISDIR on a directory
      reference or an implied directory, the clobbering shape's answer —
      see [openat_append_spec]).  The fd is a [State.FdFileA], a different
      kind from the other two write shapes' [State.FdFileW]; what turns
      on that is set out at [append_create_flags].
    - the READ-WRITE words: O_RDWR alone, O_RDWR beside O_CREAT and/or
      O_TRUNC ([rdwr_open_word]), and O_RDWR|O_CREAT|O_EXCL with or
      without O_TRUNC ([is_rdwr_excl_create]).  The fd is a
      [State.FdFileRW], the one kind that answers in BOTH directions
      off one [f_pos]; [openat_rdwr_spec] carries the table of what the
      O_CREAT and O_TRUNC bits each decide, and
      [openat_rdwr_excl_spec] the -EEXIST that separates the exclusive
      words from them.
    - O_WRONLY|O_CREAT|O_EXCL|O_APPEND, with or without O_TRUNC
      ([is_excl_append_create]): the exclusive shape's deterministic
      -EEXIST on every name that exists, and otherwise the append
      shape's creation, an empty file and a [State.FdFileA]
      ([openat_append_spec] with [excl] true).

    ALL OF THEM ARE ON A PATHNAME WITH NO SEPARATOR IN IT.  One with a
    separator is declined ahead of the flag test and reaches none of the
    arms above — see the guard in [openat_resolved_spec], which also
    says what the create shapes would answer for such a path without it
    and why that is unsound — with the exceptions [openat_sep_spec] names:
    "/etc/localtime" is -ENOENT without O_CREAT, on a declared
    assumption about the image, and fails closed with it; "/dev/null"
    opens under every admitted access mode as a [State.FdDevNull],
    -EEXIST under O_EXCL and -ENOTDIR under O_DIRECTORY, on the
    assumption [openat_devnull_spec] states; "/dev/urandom" opens
    read-only as a [State.FdUrandom], with the same -EEXIST and
    -ENOTDIR, and declines the write words, on the assumption
    [openat_urandom_spec] states.  So "create" below always
    means "create the
    single-component name the program passed", never a name in a
    directory the model cannot see.  ".." is not declined: it is a
    directory reference and takes the same arm "." does
    ([path_is_dirref]).

    The EMPTY pathname always fails with -ENOENT, whatever the (modeled)
    flags (path_resolution(7); AT_EMPTY_PATH is not modeled) — in
    particular it never matches an empty-path key in the file-system
    image.

    ORDER.  The kernel's own order is [build_open_flags()], then
    [getname()], then [path_init]'s [fdget_raw] on the dirfd, and this
    spec follows it: a flag word the model does not interpret is
    unmodeled and yields [unmodeled] BEFORE any pathname is fetched (the kernel
    would never reach the pathname for a combination it rejects), while
    an over-long or unmapped path answers a real errno even when the
    dirfd is one the model declines.

    [dirfd] arrives already truncated to 32 bits (see [Syscall.fd32]), as
    openat declares it [int]: AT_FDCWD is recognized in the low half
    ([AT_FDCWD32]), so [openat(2^32 - 100, ...)] is AT_FDCWD.

    The pathname fetch has all three of [getname()]'s answers:
    -ENAMETOOLONG for a path with no NUL within PATH_MAX, -EFAULT for
    one with an unmapped byte, and the string itself otherwise.  Both
    failures are deterministic returns the model tracks, like -ENOENT —
    not injectable, so they are not in [openat_errnos].

    PROCFS NAMES ARE THE OTHER EXCEPTION, ahead of all of the above: an
    absolute name under "/proc", from any dirfd, or a name relative to
    an O_PATH descriptor on one ([State.OProcPath]), is
    [openat_proc_spec]'s, which answers the O_PATH words and O_RDONLY
    of a "/proc/sys/" name and declines the rest ([proc_open_target]).
    An O_PATH word on any other name is declined.

    Anything else — a dirfd other than AT_FDCWD, other flag
    combinations — is unmodeled: [unmodeled].  An open on an arm that can
    SUCCEED may instead fail with an errno from [openat_errnos]
    (environment conditions the model does not decide; this alternative
    also keeps the spec receptive when no free fd < 2^31 exists).  The
    -EMFILE among them is the one that is not purely an
    environment condition: the model holds the run's soft RLIMIT_NOFILE
    in [State.m_nofile], but [File.lowest_fd] ignores it,
    so this spec can hand out an fd Linux would have refused.  On
    success the kernel returns the lowest free fd ([File.lowest_fd]), as Linux
    does.  Flag arithmetic happens in [Z] on the unsigned flag word.

    APPROXIMATION (deliberate, and shared by every arm that reports a
    PATH-RESOLUTION errno deterministically — the empty-path and
    absent-file -ENOENT, the "." -EISDIR, the O_EXCL -EEXIST, the
    implied directory's -EISDIR and -EEXIST on the write-create arms
    (whose `reject` twin is the Rocq literal
    [Checks.Cases.Fs.Open.openat_implied_directory_create_eisdir]),
    [openat_dir_spec]'s own pair, the -ENOTDIR for a name the map holds
    beside the -ENOENT for one it does not, and
    [openat_localtime_spec]'s -ENOENT, whose `reject` twin is
    [Checks.Cases.Fs.Open.openat_localtime_enoent]): those
    arms admit that ONE answer and no [openat_errnos] alternative,
    whereas Linux can fail an openat with an errno raised BEFORE path
    resolution — [do_sys_openat2] calls [get_unused_fd_flags] before
    [do_filp_open], so at RLIMIT_NOFILE the real call answers -EMFILE (or
    -ENFILE at the system limit) where the model insists on the
    resolution errno.  Errnos the kernel can raise before path resolution
    are OUTSIDE the modeled resolutions.  (The -ENAMETOOLONG and -EFAULT
    arms are NOT approximate in this way: [getname()] runs before
    [get_unused_fd_flags], so those really do preempt fd exhaustion.)
    THE LIST IS HAND-MAINTAINED.
    This narrows the spec rather than widening it, so it admits nothing
    unsound; the cost is that a source and a target which diverge only
    under fd-table exhaustion are not distinguished by the proved
    theorem. *)
Definition openat_body_spec (i : SyscallInput) (m : Model)
    (dirfd pathp flags : word) : Sys SyscallEffect :=
  match read_cstr (in_mem i) pathp with
    | CstrTooLong => err_ret ENAMETOOLONG        (* no NUL within PATH_MAX *)
    | CstrFault => err_ret EFAULT                (* unmapped byte in the path string *)
    | CstrOk p =>
        if path_eqb p [] then err_ret ENOENT     (* empty pathname: always a real -ENOENT on Linux *)
        else
        (* a procfs name, absolute from any dirfd or relative to an
           [OProcPath] descriptor: [openat_proc_spec] *)
        match proc_open_target (m_fds m) dirfd p with
        | Some c => openat_proc_spec c flags m
        | None =>
        (* only now the dirfd ([path_init]'s [fdget_raw] runs after
           [getname]): the other relative-to-a-dirfd modes aren't
           modeled, so we can't judge the call — [unmodeled], NOT the
           program faulting. *)
        if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
        (* an O_PATH word off procfs: declined, so that every arm below
           sees only the access-mode words it was written for *)
        else if open_path_word (Z.ldiff (bv_unsigned flags) open_ignored_flags)
        then unmodeled
        else openat_resolved_spec p flags m
        end
  end.

Definition openat_core_spec (dirfd pathp flags : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  (* [build_open_flags()] first, as Linux does: a flag combination the
     model does not interpret is unmodeled, so we can't judge the call —
     [unmodeled], and in particular NOT one of the pathname errnos below,
     which the kernel would never reach for a combination it rejects. *)
  if negb (modeled_open_flags flags) then unmodeled
  else
    (* then [getname()]: all three of its answers are real errnos. *)
    openat_body_spec i m dirfd pathp flags.

Definition openat_spec (dirfd pathp flags : word) : Sys SyscallEffect :=
  i <- input ;;
  record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
    (openat_core_spec dirfd pathp flags).

(** [close fd]: 0 on a live fd (which is removed), -EBADF otherwise.
    [fd] arrives already truncated to 32 bits (see [Syscall.fd32]), so
    [close(2^32)] closes stdin.

    THE ARM IS KIND-BLIND ON PURPOSE, AND FOR A PIPE THAT IS
    LOAD-BEARING.  Removing the fd is the whole of what [pipe_release]
    does that a program can observe (fs/pipe.c:725-746, v6.18.46): it
    decrements [pipe->readers] or [pipe->writers] by the file's [f_mode]
    (:730-733), and the model reads that same fact back off the fd table
    ([State.pipe_end_live]) instead of keeping a counter.  So closing the
    last WRITE end is exactly what turns a
    later read of the drained pipe from a block into end-of-file, and
    closing the last READ end is what makes a later write raise SIGPIPE
    ([Fs.ReadWrite.raise_sigpipe]) — both without a line of
    pipe-specific code here.
    Buffered bytes are NOT dropped: the [m_pipes] entry stays (see
    [State.pipe_new_id]), and a reader whose end is still open still
    sees them, as it does on Linux. *)
Definition close_spec (fd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF
  | Some _ => set_fds (fd_remove (m_fds m) fd) ;; ret_only (Z_to_bv 64 0)
  end.

(** The region a GROWING [ftruncate] must zero-fill is one the model can
    represent.  The endpoint measured is the NEW LENGTH itself, and the
    comparison is [ReadWrite.modeled_zero_fill]'s — the same one [ReadWrite.modeled_file_gap]
    makes of a write's offset, for the same reason: Linux extends a file
    into a HOLE for free, while the model holds the file as a flat byte
    list and has to build the zeros ([Fs.file_truncate]).

    A SHRINK is always judged — for [len] at or below the current length
    the subtraction is negative, so the comparison holds outright.  Note
    what that does and does not buy: the bound is ONE-SIDED, an upper
    bound on [len], so it bounds [word_to_nat len] by
    [length data + rw_bytes_max] in BOTH directions.  A shrink is never
    free — [Fs.file_truncate] still builds [word_to_nat len] for its
    [repeat] argument, a unary numeral the size of the new length — it is
    merely never DECLINED. *)
Definition modeled_truncate_gap (data : list byte) (len : word) : bool :=
  modeled_zero_fill (bv_unsigned len) data.

(** [ftruncate fd len] (riscv64 nr 46, [SYSCALL_DEFINE2]).  Sets the
    file's length to exactly [len]: a shrink drops the tail, a grow
    zero-fills ([Fs.file_truncate]).

    THE FD'S OFFSET IS NOT TOUCHED, and that is the fact this spec most
    has to get right.  Linux resolves the descriptor with [fdget], not
    [fdget_pos] — it does not even take the [f_pos] lock, and no
    assignment to [f_pos] exists anywhere on the path
    ([do_sys_ftruncate] -> [do_ftruncate] -> [do_truncate] ->
    [notify_change], fs/open.c and fs/attr.c).  Contrast [ksys_write]
    (fs/read_write.c, Linux v6.1 through v6.12), which takes [fdget_pos]
    and writes the field back explicitly.  So a shrink can leave the
    offset PAST end-of-file, and the following write then re-grows the
    file with a hole in between — exactly what [Fs.file_write] already
    does for an lseek past the end.

    CHECK ORDER, from the kernel and not from the man page (fs/open.c;
    [inode_newsize_ok] in fs/attr.c is byte-identical across MAINLINE
    v6.1 through v6.12 — stable branches were not separately audited, so
    read every window here as mainline — and the entry point's only
    CHECK-ORDER changes in it
    are a Landlock hook swap, the v6.9 split of [do_ftruncate] out of
    [do_sys_ftruncate], and the v6.10 [unsigned long] -> [off_t]
    parameter retype, which is compat-only and changes nothing on a
    64-bit ABI):

    - [len] NEGATIVE as a signed 64-bit value is -EINVAL, and it is
      decided BEFORE THE FD IS LOOKED UP: [do_sys_ftruncate] tests
      [length < 0] ahead of its [fdget].  So [ftruncate(-1, -1)] is
      -EINVAL, not -EBADF — the ordering a spec written from the man
      page gets backwards;
    - an fd that is not open is -EBADF;
    - a channel, EITHER END OF A PIPE, a socket, a read-only file fd, or
      a directory fd is -EINVAL.  One kernel condition covers all five,
      [!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)], so a
      directory is -EINVAL and NOT -EISDIR (that errno belongs to
      [vfs_truncate], which only the path-based truncate(2) reaches) and
      a pipe is -EINVAL and NOT -ESPIPE (an lseek errno that appears
      nowhere in this path).  A channel answers -EINVAL whichever HALF
      of that condition it fails: /dev/null and a pipe are not S_ISREG,
      and a REGULAR file opened O_RDONLY fails on FMODE_WRITE instead.
      What this arm therefore assumes of the
      environment is the disjunction, not the pipe: no channel the model
      is handed is a writable regular file.  Nothing enforces that.

      THE WRITE END IS THE CASE WORTH SEPARATING OUT, because it is the
      one an access-mode reading of that condition gets wrong.  [fd[1]]
      really does hold FMODE_WRITE — [create_pipe_files] opens it
      O_WRONLY — so it passes the second half and fails only the first.
      An [FdPipe] arm that had copied [FdFile]'s "read-only, so no
      FMODE_WRITE" reasoning would therefore have reached the right
      errno on the read end for the wrong reason, and would have had
      nothing to say about the write end.  It is S_ISREG that decides
      here, for both ends, and the model consults the direction bit not
      at all;
    - a writable file fd whose path is absent from [m_fs] is
      [unmodeled]; an [FdFileW] always points into the fs (see openat),
      so this arm is unreachable rather than a judgement;
    - a grow larger than [modeled_truncate_gap] permits is [unmodeled],
      fail closed, decided after the fd checks Linux makes first.

    WHAT THIS SPEC DOES NOT MODEL, and therefore what it assumes of the
    environment.  Four failures are named below, each from state the
    model does not carry; the list is the set a caller could plausibly
    reach, NOT an exhaustive enumeration of what this path can return.
    [notify_change] (fs/attr.c), which [do_truncate] calls, adds at
    least -EOVERFLOW on an inode whose uid or gid does not map in the
    mount's idmapping, a second LSM veto in [security_inode_setattr],
    and -EWOULDBLOCK from [try_break_deleg], which [do_truncate] cannot
    retry because it passes a NULL [delegated_inode]; a filesystem's own
    [i_op->setattr] adds more still ([ext4_setattr] alone has -EIO on a
    shut-down superblock and a THIRD -EFBIG at [s_bitmap_maxbytes]).
    None of those is reachable on a file the run created through the
    modeled openat either, and none changes what this spec ADMITS.

    Each named failure is listed with the DIRECTION that reaches it,
    which is a fact about where the check sits rather than about what it
    means.  Only the two SIZE limits are grow-only, because
    [inode_newsize_ok] (fs/attr.c) consults them solely in its
    [inode->i_size < offset] branch.  -ETXTBSY is the exact COMPLEMENT
    of grow-only rather than direction-independent: it is that
    function's [else] arm, so it needs [i_size >= offset] and a strict
    grow never reaches it.  Only the append-only and LSM pair runs in
    either direction:

    - -EFBIG past RLIMIT_FSIZE, which ALSO raises SIGXFSZ, whose default
      action is to kill the process — GROW-ONLY;
    - -EFBIG past the filesystem's [s_maxbytes] — GROW-ONLY;
    - -EPERM from [IS_APPEND] and -EACCES from an LSM
      ([security_file_truncate], and [security_path_truncate] before
      v6.6) — EITHER DIRECTION, and the only two of the four decided in
      [do_ftruncate] itself, before [do_truncate] is called;
    - -ETXTBSY when the inode is an active swapfile
      ([inode_newsize_ok]'s [i_size >= offset] branch) — SHRINK OR
      EQUAL, never a grow.

    An immutable inode is -EPERM in either direction too, but it is NOT
    in the entry point: on ext4 it is [ext4_setattr]'s [IS_IMMUTABLE]
    test, reached through [notify_change] -> [i_op->setattr] INSIDE
    [do_truncate].  [may_setattr]'s own immutable test does not fire
    here, since it is gated on ATTR_MODE/UID/GID/TIMES_SET and
    [do_truncate] sets ATTR_SIZE | ATTR_MTIME | ATTR_CTIME.  Linux v6.1
    through v6.12.

    None is modeled, and no errno is invented for them: the spec commits
    to 0 on a grow it accepts.  The immutable and append-only cases
    cannot arise on a file the run itself created through the modeled
    openat.  The two size limits are assumptions about the environment,
    and the bound does NOT stand in for either: [modeled_truncate_gap]
    bounds the per-call DELTA, while [s_maxbytes] and RLIMIT_FSIZE bound
    the ABSOLUTE size, so they are not comparable quantities and no
    number of in-bound calls is inductively safe.

    RLIMIT_FSIZE is a PREMISE ON THE ENVIRONMENT.  [inode_newsize_ok]
    consults [rlimit(RLIMIT_FSIZE)], the soft limit, and skips its
    -EFBIG-plus-SIGXFSZ arm on exactly RLIM_INFINITY (fs/attr.c, Linux
    v6.18.46, commit 1f99e9ab748f); this spec's 0 on a grow is right
    under that value and only that value, so the run must start with
    the soft limit at RLIM_INFINITY.  It then stays there: the only writer that can LOWER it during the
    run is [do_prlimit] (kernel/sys.c) — reached through prlimit64,
    whose [Kernel.Sys.prlimit64_spec] declines every resource but
    RLIMIT_CORE, or through setrlimit (164), which has no arm — so a
    program that lowers the limit fails closed at that call and its later
    ftruncate is never judged against this 0.  The one other writer,
    [do_acct_process] (kernel/acct.c), raises the soft limit to
    RLIM_INFINITY around an accounting record and restores it, so it
    cannot make an unlimited process limited.  The
    model carries no rlimit, and that is on purpose: an injectable
    -EFBIG here would be wrong twice — it would admit -EFBIG on shrinks,
    where no kernel produces it, and it would drop the SIGXFSZ that makes
    the process die rather than see the errno.

    [s_maxbytes] is the half nothing checks.  Accumulation reaches it —
    32768 grows of exactly [Uaccess.rw_bytes_max] pass every guard here and
    put the file past vfat's 4 GiB [s_maxbytes], where the kernel answers
    -EFBIG and this spec says 0.  It is remote rather than closed when
    the cwd is tmpfs, whose [s_maxbytes] is MAX_LFS_FILESIZE =
    LLONG_MAX on a 64-bit kernel (mm/shmem.c shmem_fill_super,
    include/linux/fs.h), and no ftruncate length exceeds that.  It is the
    same shape [ReadWrite.write_spec] has — though the write
    side is the more forgiving of the two: [generic_write_check_limits]
    answers -EFBIG only when the START position is already at or past
    the limit, and CLAMPS a write that merely crosses it into a short
    write.  The model's regular-file write returns the full count
    ([ReadWrite.write_spec]'s [FdFileW] arm is deterministic), so the
    clamp is rejected there exactly as the -EFBIG is; both halves are
    shared.

    -EROFS is deliberately absent, and that is a source-grounded
    difference from truncate(2)'s documented error list: there is no
    [mnt_want_write] and no [inode_permission] on the ftruncate path at
    all. Write access was settled at open time, so a read-only mount
    gives -EROFS at the openat and an -EINVAL here on the O_RDONLY fd
    that results.

    NO -EFBIG CONSTANT IS AVAILABLE, which is why [modeled_truncate_gap]
    is the only thing standing at the top of the range.  [s_maxbytes] is
    a per-filesystem value, and the disagreement is not theoretical:
    measured under qemu-riscv64, [ftruncate(fd, 2^63-1)] answers 0 on
    tmpfs and on overlayfs, and -EFBIG on a virtiofs mount.  So the same
    call is a conforming success in one environment and a conforming
    -EFBIG in another, and a spec that picked either would be wrong in
    the other.  Declining above the bound is the only answer that is
    right in both — and it is a decline, not an errno, because the
    answer is the environment's to give.

    The kernel's fourth check, [small && length > MAX_NON_LFS] ->
    -EINVAL, is unreachable here rather than unmodeled.
    [SYSCALL_DEFINE2(ftruncate, ...)] passes [small = 1] down through
    [do_sys_ftruncate] (fs/open.c), but the O_LARGEFILE clear drops it —
    and every open on a 64-bit kernel sets that flag.  The clear moved
    with the v6.9 split noted above: it is in [do_sys_ftruncate] itself
    through v6.8, and in [do_ftruncate] from v6.9 on.  The flag is forced
    in the syscall entry points themselves, [SYSCALL_DEFINE4(openat, ...)]
    and its siblings in fs/open.c (NOT in [build_open_flags], which never
    mentions it), from
    [force_o_largefile()], a macro in include/linux/fcntl.h defined as
    [!IS_ENABLED(CONFIG_ARCH_32BIT_OFF_T)]; and ARCH_32BIT_OFF_T is
    declared in arch/Kconfig with [depends on !64BIT].  Linux v6.1
    through v6.12.  Measured: [ftruncate(fd, 2^31)] answers 0.

    The success arm is DETERMINISTIC on purpose — no [alt], no
    [Syscall.errno_from].  Every failure a real kernel can raise on a grow this
    small comes from state the model does not carry, and inventing an
    injectable set for it would let a source and a target that really
    behave differently share a trace set.  The narrowing is the same one
    [ReadWrite.write_spec] takes for short writes: fewer admitted outcomes, none
    of them unsound. *)
Definition ftruncate_spec (fd len : word) : Sys SyscallEffect :=
  if (bv_signed len <? 0)%Z then err_ret EINVAL
    (* negative length: real -EINVAL, and decided BEFORE the fd lookup *)
  else
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                        (* fd not open: real -EBADF *)
  | Some (FdChannel _) => err_ret EINVAL         (* no channel is a writable regular file: real -EINVAL, not -ESPIPE *)
  | Some (FdSocket _) => err_ret EINVAL          (* on an fd the model KNOWS is a socket: a socket
                                                    inode is S_ISSOCK, so [do_ftruncate]'s
                                                    !S_ISREG test answers -EINVAL before FMODE_WRITE
                                                    is consulted *)
  | Some (FdPipe _ _) => err_ret EINVAL          (* the same answer for the same reason, on an fd
                                                    the model KNOWS is a pipe — see the header *)
  | Some (FdDevNull _ _) => err_ret EINVAL       (* and on /dev/null: a character device is not
                                                    S_ISREG, so [do_ftruncate] (fs/open.c, v6.18.46)
                                                    answers -EINVAL whatever the access mode *)
  | Some FdUrandom => err_ret EINVAL             (* /dev/urandom is a character device too, and
                                                    read-only besides: [do_ftruncate]'s [!S_ISREG]
                                                    is the same -EINVAL, tested before FMODE_WRITE *)
  | Some (FdFile _ _) => err_ret EINVAL          (* fd open read-only: no FMODE_WRITE, real -EINVAL *)
  | Some FdDir => err_ret EINVAL                 (* a directory is not S_ISREG: real -EINVAL, not -EISDIR *)
  | Some (FdOpaque _) => unmodeled               (* FAIL-CLOSED: [do_sys_ftruncate]'s [CLASS(fd, f)]
                                                    refuses an O_PATH file (-EBADF), and the other
                                                    two objects take [do_ftruncate]'s -EINVAL; the
                                                    split is not written (fs/open.c, read at
                                                    v6.18.44) *)
  | Some (FdFileA p _) =>
      (* AN APPEND FD IS A WRITABLE REGULAR FILE, so it takes the arm
         below rather than the -EINVAL the five kinds above get:
         [do_ftruncate]'s condition is
         [!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)]
         (fs/open.c), and an [FdFileA] fails neither half — O_APPEND
         rides on O_WRONLY, which is what sets FMODE_WRITE.  The flag is
         read nowhere on this path: [do_truncate] sets the size
         outright, and O_APPEND is consulted only by the write path's
         [generic_write_checks].  The inode's APPEND-ONLY attribute is a
         different thing and does bite here — [IS_APPEND(inode)] is
         [do_ftruncate]'s own -EPERM — but it is an inode attribute this
         model does not carry, exactly as for [FdFileW], and the header's
         list of unmodeled failures already names it.

         THE OFFSET IS UNTOUCHED as it is for every other kind, so a
         shrink can leave [f_pos] past end-of-file — this arm writes no
         [set_fds] at all, exactly as the [FdFileW] one does not.  On an
         append fd that is not observable through a later WRITE, which
         repositions itself, but it IS observable through
         [lseek(fd, 0, SEEK_CUR)], so leaving the entry alone is a
         decision here rather than a spare line. *)
      match fs_lookup (m_fs m) p with
      | None => unmodeled                        (* an FdFileA always points into the fs; see openat *)
      | Some data =>
          if negb (modeled_truncate_gap data len) then unmodeled
          else
            set_fs (fs_set (m_fs m) p (file_truncate data len)) ;;
            ret_only (Z_to_bv 64 0)
      end
  | Some (FdFileW p _) | Some (FdFileRW p _) =>
      (* ONE ARM FOR TWO KINDS.  [do_ftruncate]'s test is
         [!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)]
         (fs/open.c, Linux v6.18.46), and an O_RDWR description passes
         both halves exactly as an O_WRONLY one does; nothing further
         down reads the access mode.  The read-only [FdFile] arm above
         is the -EINVAL half of that same test. *)
      match fs_lookup (m_fs m) p with
      | None => unmodeled                        (* a writable file fd always points into the fs; see openat *)
      | Some data =>
          if negb (modeled_truncate_gap data len) then unmodeled
            (* a zero-fill too large to build as a byte list; Linux makes
               the file sparse for free — see [modeled_truncate_gap] *)
          else
            set_fs (fs_set (m_fs m) p (file_truncate data len)) ;;
            ret_only (Z_to_bv 64 0)
            (* NO set_fds: the offset is untouched, see the header *)
      end
  end.

(** faccessat's injectable failures on the arm that can succeed:
    environment conditions the model does not track, both of them
    reachable on an F_OK probe of a path that really exists.

    - ENOMEM, from the allocations [getname_flags] makes before and
      while it copies: [__getname], and the [kzalloc] on the re-copy
      path a near-PATH_MAX name takes (fs/namei.c).
      [access_override_creds]'s [prepare_creds] is a third source, but
      it runs only when [access_need_override_creds] says so, and that
      is false for a caller whose fsuid equals its uid and fsgid its
      gid and whose capability set is the uninteresting one for its
      uid — clear for a non-root caller, or identical to the permitted
      set for a root one, both under [!issecure(SECURE_NO_SETUID_FIXUP)]
      (fs/open.c).
    - EACCES, from the path walk's own search-permission check, and from
      that alone.  [may_lookup] takes [inode_permission(..., MAY_EXEC)]
      on the directory the walk starts from — the working directory here
      — in the FIRST iteration of [link_path_walk], before the last
      component is even typed (fs/namei.c).  So it precedes every answer
      below, the "." and ".." ones included.
      NOT from an LSM: [security_inode_permission] is handed the mask
      with MAY_ACCESS set, and MAY_ACCESS is the bit filesystems branch
      on rather than the bit LSMs do.  The two in-tree hooks that could
      deny both refuse the mask before they compute anything, in the
      same shape and for the same stated reason: [selinux_inode_permission]
      opens with [mask &= MAY_READ|MAY_WRITE|MAY_EXEC|MAY_APPEND] and
      then [if (!mask) return 0;] under the comment "No permission to
      check.  Existence test." (security/selinux/hooks.c), and
      [smack_inode_permission] masks to the same four bits and returns 0
      outright when nothing is left (security/smack/smack_lsm.c).  So
      neither reaches its access-vector computation at all.

    ENOENT is NOT injectable: path existence IS tracked, and an absent
    name is a deterministic -ENOENT.

    WHAT A ZERO MASK EXCLUDES BY ITSELF (Linux fs/open.c,
    [do_faccessat], byte-identical v6.15 through v6.18.46 — the pinned
    tree — and unchanged in every decision it makes back to v6.6).  Each
    of these is gated on a bit F_OK does not set, so no environment
    reaches it:

    - EROFS.  The read-only test at the end of [do_faccessat] runs only
      when [mode & S_IWOTH], and [sb_permission]'s own EROFS only when
      [mask & MAY_WRITE].  A zero mode sets neither, so F_OK returns 0
      on a read-only filesystem.
    - EPERM (immutable) and the unmapped-id EACCES: both inside
      [inode_permission]'s [if (unlikely(mask & MAY_WRITE))].
    - EACCES from [path_noexec]: gated on [mode & MAY_EXEC] and
      [S_ISREG].
    - the DAC comparison itself, in every form.  Both of
      [acl_permission_check]'s tests narrow to the low three bits first
      — the fast path is [!((mask & 7) * 0111 & ~mode)] and the owner
      arm is [mask &= 7] then [(mask & ~mode) ? -EACCES : 0] — so a zero
      mask satisfies each outright; and [posix_acl_permission] opens
      with [want &= MAY_READ | MAY_WRITE | MAY_EXEC] and then finds
      every [(e_perm & 0) == 0] (fs/namei.c, fs/posix_acl.c).

    WHAT IS EXCLUDED BY THE ENVIRONMENT INSTEAD, and so is a precondition
    rather than a gate.  These reach a zero mask and can answer outside
    [faccessat_errnos]; the WORLD paragraph on [faccessat_spec] is what
    rules them out, and a run that leaves it is a false rejection rather
    than an unsound admission:

    - [do_inode_permission] dispatches to [inode->i_op->permission]
      ahead of [generic_permission] and passes the mask through
      unfiltered (fs/namei.c).  MAY_ACCESS is exactly the bit some
      filesystems read: [fuse_permission] turns it into a FUSE_ACCESS
      request whose errno the userspace server picks (fs/fuse/dir.c),
      and [proc_pid_permission] can answer -ESRCH or, under hidepid,
      -ENOENT/-EPERM with a zero mask (fs/proc/base.c).
    - [devcgroup_inode_permission] returns early only for a non-device
      inode; on a block or character node under a restrictive device
      cgroup it reaches [__devcgroup_check_permission] and can answer
      -EPERM even with an empty access set
      (include/linux/device_cgroup.h, security/device_cgroup.c).
    - [posix_acl_permission] and [check_acl] can answer -EIO on a
      malformed or unreadable on-disk ACL (fs/posix_acl.c).
    - -ESTALE, after [do_faccessat]'s own [retry_estale] loop has
      re-resolved once with LOOKUP_REVAL and failed again.

    ETXTBSY is not in either list because [do_faccessat] has no path to
    it at all: nothing in its body calls [get_write_access] or tests
    [IS_SWAPFILE]. *)
Definition faccessat_errnos : list Z := [ENOMEM; EACCES].

(** [mode] as [do_faccessat] reads it: the low 32 bits of the register,
    since the parameter is declared [int] ([Syscall.int32]). *)
Definition access_mode (mode : word) : Z := bv_unsigned (int32 mode).

(** The mode words the kernel accepts at all: [mode & ~S_IRWXO] zero.
    Like [Fs.Namei.modeled_unlink_flags] this is not a modeling choice —
    a word outside it is the kernel's own -EINVAL, not [unmodeled].
    Note that a NEGATIVE [mode] lands here: [access(p, -1)] truncates to
    0xffffffff, whose bits outside the mask are set, so it is -EINVAL. *)
Definition modeled_access_mode (mode : word) : bool :=
  Z.eqb (Z.ldiff (access_mode mode) S_IRWXO) 0.

(** F_OK — the empty mode, and the only one this model can answer. *)
Definition access_mode_f_ok (mode : word) : bool := Z.eqb (access_mode mode) 0.

(** The one outcome an F_OK probe of a path that RESOLVES admits: 0, or
    one of the untracked environment failures above.  Both take a bare
    return and every one of the five ledgers empty — faccessat writes
    nothing, zeroes nothing, unmaps nothing and copies out nothing, and
    the pathname copy-in is the wrapper's — and neither touches
    the model, which is what makes this syscall a pure observation. *)
Definition access_exists_spec : Sys SyscallEffect :=
  alt (e <- errno_from faccessat_errnos ;; err_ret e)  (* untracked env failure *)
      (ret_only (Z_to_bv 64 0)).

(** [faccessat dirfd path mode] (riscv64 nr 48, [SYSCALL_DEFINE3]),
    which is [do_faccessat(dfd, filename, mode, 0)] — the flags word is
    a CONSTANT ZERO here, not an argument.  AT_EACCESS,
    AT_SYMLINK_NOFOLLOW and AT_EMPTY_PATH are reachable only through
    [faccessat2] (nr 439, [SYSCALL_DEFINE4]), which [faccessat2_spec]
    below answers, so nothing in THIS spec interprets a flag: there is
    no flag to interpret.  That also fixes the empty pathname at
    -ENOENT, since AT_EMPTY_PATH is the only thing that would make
    [getname_flags] accept it, and no [faccessat] can pass it.

    ONLY F_OK IS MODELED, and the reason is the model's file system.
    [Fs] maps a path to its BYTES and holds nothing else — no mode bits,
    no owner, no mount.  R_OK, W_OK and X_OK are answered by
    [generic_permission] out of [inode->i_mode] against the caller's
    ids (fs/namei.c, [acl_permission_check]), and W_OK reaches
    [__mnt_is_readonly] besides.  None of that is a function of the byte
    map, so a mode with any of the low three bits set is [unmodeled].
    F_OK asks the one question the map can answer: does this path
    resolve.

    THE REAL-UID RULE IS WHAT MAKES THAT SLICE SOUND rather than merely
    convenient.  [access(2)] exists to check with the REAL ids, and
    [do_faccessat] implements that by installing an override cred whose
    fsuid/fsgid are copied from uid/gid ([access_override_creds]) — the
    historically delicate part of this syscall, and the part the model
    does not track, since [State] carries uid and euid but no fsuid.
    Under F_OK it is unobservable.  The mask handed to
    [inode_permission] is [0 | MAY_ACCESS], and MAY_ACCESS is outside
    the MAY_READ|MAY_WRITE|MAY_EXEC triple every DAC comparison narrows
    to: [acl_permission_check]'s test is [(mask & 7) * 0111 & ~mode],
    which is 0 for a zero mask, and [posix_acl_permission] opens with
    [want &= MAY_READ | MAY_WRITE | MAY_EXEC] and then finds every
    [(e_perm & 0) == 0] (fs/namei.c, fs/posix_acl.c).  So which cred is
    installed changes no answer F_OK gives, and the only trace the
    override leaves is the -ENOMEM already in [faccessat_errnos].
    THIS STOPS BEING TRUE the moment a nonzero mode is modeled: at that
    point fsuid is load-bearing and has to be carried in [State] first.

    ORDER, following the kernel's exactly (fs/open.c, [do_faccessat]):

    - the mode word first, and it really is first — [if (mode & ~S_IRWXO)
      return -EINVAL;] is the opening statement of the function, ahead of
      the flag test, ahead of [access_need_override_creds] and ahead of
      [user_path_at].  So [faccessat(AT_FDCWD, NULL, 8)] is -EINVAL and
      not -EFAULT: the user pointer is never dereferenced.  The spec
      records no pathname copy-in on that arm for the same reason.
    - then, for a mode this model declines, [unmodeled] — before the
      pathname, so the spec makes no claim about an -EFAULT it could not
      then judge anyway.
    - then [getname()] inside [user_path_at], with all three of its
      answers as [openat_spec] has them: -ENAMETOOLONG for no NUL within
      PATH_MAX, -ENOENT for the empty string, -EFAULT for an unmapped
      byte.
    - only then the dirfd, resolved in [path_init]: the relative-to-a-
      dirfd modes are not modeled, so any dirfd but AT_FDCWD is
      [unmodeled], the same treatment [openat_spec] and
      [Fs.Namei.unlinkat_spec] give it.

    THE ANSWERS, once the path is in hand.  "." and ".." resolve without
    consulting the byte map: "." is the working directory and ".." its
    parent, and both exist by construction, so both are the existence
    arm.  ([link_path_walk] types them LAST_DOT and LAST_DOTDOT and
    [handle_dots] answers them; neither reaches a filesystem lookup, and
    an UNLINKED working directory is still 0 — [complete_walk] has no
    [d_unlinked] test on this path.)  Every flag-gated failure the ".."
    walk can raise is unreachable here, because [do_faccessat] builds
    [lookup_flags] from a zero flag word and never sets one of them:
    [handle_dots]'s -EAGAIN under LOOKUP_IS_SCOPED, and both of
    [follow_dotdot]'s -EXDEVs, the LOOKUP_NO_XDEV one and the
    LOOKUP_BENEATH one on its [in_root] branch.  The failure that is NOT
    flag-gated is [path_connected]'s -ENOENT, raised when the working
    directory has been renamed out from under a bind-mount root; it is
    reachable and is not admitted here, and sits under the same world
    precondition as everything else below (fs/namei.c).  For an ordinary name the map is the answer: a
    key present is the existence arm, a key absent is -ENOENT.

    THE WORLD this is exact in is the one [openat_spec] and
    [Fs.Namei.unlinkat_spec] already depend on: every model key is a
    regular file directly in the working directory, and the working
    directory holds nothing but those keys.  The three guards
    [Fs.Namei.unlinkat_spec] uses to stay inside it are needed here for
    the same reasons, and one of them for a DIFFERENT reason worth
    stating:

    - a path containing "/" is [unmodeled].  The kernel resolves every
      component; the flat map's confident answer for "a/b" is "absent,
      -ENOENT" and reality may hold a directory "a" with a file "b" in
      it.  This is the same bound the slash guard puts on [unlinkat],
      and it bounds this spec exactly as hard: no absolute path, no
      trailing slash, no multi-component name.
    - a single component longer than [Uapi.NAME_MAX] is [unmodeled]:
      [getname()]'s PATH_MAX bound lets a 4095-byte component through
      and the FILESYSTEM then answers -ENAMETOOLONG, which the model has
      no filesystem type to ask.
    - a name some key lives UNDER ([Fs.Namei.fs_under]) is [unmodeled].
      For [unlinkat] that guard prevents a wrong ERRNO; here it prevents
      a wrong SUCCESS-OR-NOT.  A key "a/b" means reality has a directory
      "a", and F_OK of a directory returns 0 where the map would answer
      -ENOENT.

    WHAT NO GUARD RESTORES is the second half of that world: a real
    directory entry the map does not hold.  An EMPTY real directory has
    no key under it, so [fs_under] sees nothing, [fs_lookup] misses, and
    this spec answers -ENOENT where Linux answers 0.  The same holds for
    a symlink, a fifo, a socket or a device node in the working
    directory.  That is a false REJECTION rather than an unsound
    admission — the checker refuses a trace Linux really produced — and
    it is the flat-namespace gap [newfstatat] and [openat] already
    have.  It costs the most here, where an existence probe of a
    directory is a shape real programs reach for.  No modeled syscall
    creates a directory, so it is an environment precondition rather
    than something a guard could close.

    APPROXIMATION, the same one [openat_spec] carries, on every
    deterministic arm: they admit that ONE answer and no
    [faccessat_errnos] alternative, so they exclude the -ENOMEM
    [getname_flags] and [access_override_creds] can raise first, and the
    -ENOENT of an absent name additionally preempts the -EACCES a
    search-permission failure on the working directory would raise
    during resolution.  That narrows the spec rather than widening it,
    so it admits nothing unsound; the cost is that a source and a target
    diverging only under allocation failure are not distinguished by the
    proved theorem. *)
Definition faccessat_body_spec (dirfd pathp : word)
    (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => err_ret ENAMETOOLONG          (* no NUL within PATH_MAX *)
  | CstrFault => err_ret EFAULT                  (* unmapped byte in the path string *)
  | CstrOk p =>
      if path_eqb p [] then err_ret ENOENT       (* empty pathname: getname's own -ENOENT *)
      else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
      else if path_eqb p dot_path then access_exists_spec      (* the working directory *)
      else if path_eqb p dotdot_path then access_exists_spec   (* its parent *)
      else if path_has_slash p then unmodeled    (* no directory structure: see WORLD above *)
      else if Nat.ltb NAME_MAX (length p) then unmodeled  (* the filesystem's own -ENAMETOOLONG *)
      else if fs_under (m_fs m) p then unmodeled (* p names an implied directory *)
      else
      match fs_lookup (m_fs m) p with
      | None => err_ret ENOENT                   (* absent: real -ENOENT, not a modeling gap *)
      | Some _ => access_exists_spec
      end
  end.

(** The mode word, then the body under its copy-in ledger.

    THE PATHNAME COPY-IN is recorded exactly as [openat_spec] records
    it, and for the same reason: [read_cstr] is a read of user memory,
    and [State.syscall_effect_accesses] turns the ledger into a
    materialization charge, so an unrecorded read is a page the run
    never pays for.  Both mode arms sit OUTSIDE the wrapper, as
    [Fs.Namei.unlinkat_spec]'s flag arm does: the -EINVAL is a real
    answer the kernel reaches before [user_path_at] is called, so
    recording a copy there would claim a read Linux did not perform, and
    the [unmodeled] arm claims nothing at all. *)
Definition faccessat_spec (dirfd pathp mode : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (modeled_access_mode mode) then err_ret EINVAL
  else if negb (access_mode_f_ok mode) then unmodeled
  else
    record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
      (faccessat_body_spec dirfd pathp i m).

(** [flags] as [do_faccessat] reads it: the low 32 bits of the register,
    since [SYSCALL_DEFINE4(faccessat2, ...)] declares the parameter
    [int] ([Syscall.int32]), exactly as [access_mode] reads the mode. *)
Definition access_flags (flags : word) : Z := bv_unsigned (int32 flags).

(** The three flags [do_faccessat] accepts at all
    (include/uapi/linux/fcntl.h; the test is
    [if (flags & ~(AT_EACCESS | AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH))
     return -EINVAL;], fs/open.c). *)
Definition access_flags_mask : Z :=
  Z.lor AT_EACCESS (Z.lor AT_SYMLINK_NOFOLLOW AT_EMPTY_PATH).

(** The flag words the kernel accepts at all.  Like
    [modeled_access_mode] this is not a modeling choice: a word outside
    it is the kernel's own -EINVAL, not [unmodeled].  A NEGATIVE flags
    argument lands here too, for the reason [modeled_access_mode] gives
    for a negative mode: it truncates to 0xffffffff, whose bits outside
    the mask are set. *)
Definition valid_access_flags (flags : word) : bool :=
  Z.eqb (Z.ldiff (access_flags flags) access_flags_mask) 0.

(** The accepted flag words this model ANSWERS: the two that change no
    answer it can give.  AT_EMPTY_PATH is the one it declines, and the
    decline is a decline rather than an -EINVAL because the kernel
    accepts the bit.  See [faccessat2_spec] for both arguments. *)
Definition modeled_access_flags (flags : word) : bool :=
  Z.eqb (Z.land (access_flags flags) AT_EMPTY_PATH) 0.

(** [faccessat2 dirfd path mode flags] (riscv64 nr 439,
    [SYSCALL_DEFINE4]), which is [do_faccessat(dfd, filename, mode,
    flags)] — the same function [faccessat] reaches with a constant zero
    flag word (fs/open.c, v6.18.46).  So everything [faccessat_spec]
    says about the mode, the pathname, the dirfd and the answers holds
    here unchanged, and this spec adds exactly one thing: what the flag
    word does.

    ORDER, following the kernel's exactly (fs/open.c, [do_faccessat]).
    The two -EINVAL tests are the function's first two statements, in
    this order, both ahead of [access_need_override_creds] and ahead of
    [user_path_at]:

    - [if (mode & ~S_IRWXO) return -EINVAL;]
    - [if (flags & ~(AT_EACCESS | AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH))
       return -EINVAL;]

    THE SECOND ONE IS WHY THIS SPEC DOES NOT DECLINE ON THE MODE FIRST.
    A call with, say, [mode = R_OK] and a garbage flag word is a
    deterministic -EINVAL that Linux decides without ever consulting the
    permission machinery this model lacks; declining it would refuse a
    trace Linux really produces, and answering -EINVAL from the mode
    would name the wrong test.  So both -EINVAL arms come first, in the
    kernel's own order, and only then do the two declines.  Both -EINVAL
    arms sit OUTSIDE the copy-in wrapper, as [faccessat_spec]'s does:
    the pathname is never fetched on either.

    WHAT EACH ACCEPTED FLAG DOES, and why F_OK cannot see it.

    - AT_EACCESS is read once, by [access_need_override_creds], which
      returns false outright when it is set (fs/open.c).  The effect is
      that [access_override_creds] is not called and the walk runs with
      the caller's fsuid/fsgid rather than with uid/gid copied over
      them.  [faccessat_spec]'s REAL-UID paragraph already argues that
      which of the two creds is installed changes no answer F_OK gives:
      the mask handed to [inode_permission] is [0 | MAY_ACCESS], and
      MAY_ACCESS is outside the MAY_READ|MAY_WRITE|MAY_EXEC triple every
      DAC comparison narrows to ([acl_permission_check] and
      [posix_acl_permission], fs/namei.c and fs/posix_acl.c).  That
      argument is symmetric in the two creds, so it covers AT_EACCESS
      set exactly as it covers AT_EACCESS clear.  The one asymmetry is
      an errno the model already admits from elsewhere: with AT_EACCESS
      set, [prepare_creds] never runs, so its -ENOMEM cannot arise —
      but [__getname]'s can, and that is the -ENOMEM
      [faccessat_errnos] is there for.  Admitting the same set on both
      arms is therefore sound; it is not tighter than it could be
      because the tighter set is the same set.

    - AT_SYMLINK_NOFOLLOW clears LOOKUP_FOLLOW, so a TRAILING SYMLINK is
      not followed and the link itself is what F_OK asks about
      (fs/open.c builds [lookup_flags] from it; fs/namei.c walks with
      it).  Under the WORLD [faccessat_spec] states — every model key a
      regular file directly in the working directory, and the working
      directory holding nothing but those keys — there is no symlink for
      the bit to change, at the last component or at any other: a
      resolvable name is a regular file, which resolves identically with
      the bit set and clear, and "." and ".." are typed LAST_DOT and
      LAST_DOTDOT and answered by [handle_dots] without a link ever
      being read.  A multi-component path, where an INTERMEDIATE symlink
      would be followed whatever this bit says, is declined by the slash
      guard before the bit is reached; a trailing slash, which
      [lookup_last] answers by putting LOOKUP_FOLLOW back
      ([nd->last.name[nd->last.len]] nonzero, fs/namei.c), is declined
      by the same guard.  So this flag is admitted under the SAME
      precondition the rest of the spec already needs, and it widens
      nothing: leaving the world costs a false rejection here exactly as
      it does there.

    - AT_EMPTY_PATH is DECLINED, and the decline is the honest one
      rather than an -EINVAL: the kernel accepts the bit, turning it
      into LOOKUP_EMPTY so that [getname_flags] admits the empty string
      and the dirfd itself becomes the target (fs/namei.c).  That makes
      the empty pathname resolve to the working directory instead of
      answering -ENOENT — the opposite of the arm [faccessat_body_spec]
      carries — so the bit is not one this spec can pass through, and
      the model declines it BEFORE the pathname is read.  The decline is
      unconditional in the flag rather than conditioned on the pathname
      being empty, which costs the (equally answerable) case of
      AT_EMPTY_PATH beside a nonempty name and buys a bound a reader can
      check without re-deriving where LOOKUP_EMPTY is consulted.

    EVERY OTHER FLAG the kernel would accept is a bit outside the three,
    and the kernel's own -EINVAL. *)
Definition faccessat2_spec (dirfd pathp mode flags : word)
    : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (modeled_access_mode mode) then err_ret EINVAL
  else if negb (valid_access_flags flags) then err_ret EINVAL
  else if negb (modeled_access_flags flags) then unmodeled
  else if negb (access_mode_f_ok mode) then unmodeled
  else
    record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
      (faccessat_body_spec dirfd pathp i m).
