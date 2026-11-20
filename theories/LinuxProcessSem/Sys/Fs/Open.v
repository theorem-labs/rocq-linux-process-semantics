(** * LinuxProcessSem.Sys.Fs.Open — openat (56), close (57), ftruncate (46), faccessat (48), faccessat2 (439)

    This file answers to Linux [fs/open.c]: it holds what the kernel
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
  Syscall Uapi Fs.File Fs.ReadWrite Fs.Namei.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** openat's injectable failures: environment conditions the model does
    not track — kernel memory (ENOMEM, listed first as the canonical
    witness), permissions (EACCES), fd-table exhaustion (EMFILE/ENFILE)
    — beside every open that hands out a descriptor.  A table with no
    slot at all is answered before the walk instead
    ([openat_core_spec]).  ENOENT is NOT injectable: file existence IS
    tracked, and a missing file returns a deterministic -ENOENT. *)
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
    that answers -EISDIR.  So a name that exists -- any entry the walk
    finds, a folder and "." and ".." among them -- is -EEXIST before
    anything else is looked at: the answer [openat_excl_spec] gives, and
    the reason no append rule ever meets an existing tail.  A DIRECTORY
    REFERENCE IS -EEXIST AND NOTHING ELSE HERE, which is the one place
    this port differs from main LPS 4d80c33d83: that model admits
    -EISDIR beside it, the answer kernels v4.17 through v5.6 give in the
    function [do_open] replaced.  No supported kernel gives it: [do_open]
    and [do_dentry_open]'s flag clearing read the same at v6.16, v6.17,
    v6.16.12 and v6.17.13 (fs/namei.c, fs/open.c from git.kernel.org
    stable) as at v6.18.46, so each answers -EEXIST and the arm offers no
    alternative across them.  An absent name is created, and then
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
    [Uapi]; the mask exists so that every mirror of the flag test --
    [openat_resolved_spec], [Checks.Sys.Fs.Open.check_openat] and
    [Checks.Witness.Fs.Open.openat_witness] -- strips exactly the same
    bits, and so that widening the set is one edit rather than a
    search. *)
Definition open_ignored_flags : Z := (O_CLOEXEC + O_LARGEFILE + O_NONBLOCK)%Z.

(** The flag bits every modeled shape accepts that choose how the walk
    ENDS rather than which arm runs ([open_walk_mode]): O_NOFOLLOW. *)
Definition open_walk_flags : Z := O_NOFOLLOW.

(** THE SHAPE of a flag word: what is left once the ignored bits and the
    walk-ending bits are stripped.  Every arm is chosen by it. *)
Definition open_shape (flags : word) : Z :=
  Z.ldiff (Z.ldiff (bv_unsigned flags) open_ignored_flags) open_walk_flags.

(** HOW THE OPEN'S WALK ENDS, from the raw flag word, as
    [build_open_flags] sets it (fs/open.c, Linux v6.18.46):
    [LOOKUP_DIRECTORY] for O_DIRECTORY (:1337-1338); [LOOKUP_FOLLOW]
    unless O_NOFOLLOW (:1339-1340), and O_CREAT|O_EXCL sets O_NOFOLLOW
    itself (:1329-1334); and under O_CREAT a last name followed by a
    separator is -EISDIR before any lookup ([lookup_fast_for_open],
    fs/namei.c:3821-3823), which is [Fs.WalkCreate]. *)
Definition open_walk_mode (flags : word) : Fs.WalkMode :=
  let fl := bv_unsigned flags in
  let follow := negb (flag_set fl O_NOFOLLOW) in
  if flag_set fl O_CREAT then Fs.WalkCreate (follow && negb (flag_set fl O_EXCL))
  else Fs.WalkFull follow (flag_set fl O_DIRECTORY).

(** The flag WORDS [openat_spec] interprets: O_RDONLY, the clobbering
    write-create shape, the exclusive write-create shapes, the
    read-a-directory shape O_RDONLY|O_DIRECTORY, the APPEND
    write-create shape, the READ-WRITE shapes ([rdwr_open_word] and
    [is_rdwr_excl_create]), and the EXCLUSIVE APPEND shapes
    ([is_excl_append_create]), each modulo the bits in
    [open_ignored_flags].
    Linux validates
    the flags in [build_open_flags()] BEFORE it fetches the pathname, so
    this test runs first in [openat_spec] too — see the ORDER paragraph
    there.

    O_DIRECTORY IS INTERPRETED, NOT IGNORED, and it is the only flag here
    that is neither an access mode nor a creation flag.  The reason it
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
      nothing here reaches, since [openat_resolved_spec] selects
      [openat_dir_spec] for the read-only word alone), and O_RDWR|O_EXCL WITHOUT
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
  let fl := open_shape flags in
  Z.eqb fl 0 || Z.eqb fl wr_create_flags || is_excl_create fl
  || Z.eqb fl O_DIRECTORY || Z.eqb fl append_create_flags
  || rdwr_open_word fl || is_rdwr_excl_create fl
  || is_excl_append_create fl.

(** One introduction lemma per modeled shape, so a proof that already
    knows which arm it is in can clear the flags guard. *)
Lemma modeled_open_flags_rd : forall flags,
  open_shape flags = 0%Z ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H. reflexivity.
Qed.

Lemma modeled_open_flags_wr : forall flags,
  open_shape flags = wr_create_flags ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r.
Qed.

Lemma modeled_open_flags_excl : forall flags,
  is_excl_create (open_shape flags) = true ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r, Bool.orb_true_l.
Qed.

Lemma modeled_open_flags_append : forall flags,
  open_shape flags = append_create_flags ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r.
Qed.

Lemma modeled_open_flags_dir : forall flags,
  open_shape flags = O_DIRECTORY ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H. reflexivity.
Qed.

Lemma modeled_open_flags_rdwr : forall flags,
  rdwr_open_word (open_shape flags) = true ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r, Bool.orb_true_l.
Qed.

Lemma modeled_open_flags_rdwr_excl : forall flags,
  is_rdwr_excl_create (open_shape flags) = true ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r.
Qed.

Lemma modeled_open_flags_excl_append : forall flags,
  is_excl_append_create (open_shape flags) = true ->
  modeled_open_flags flags = true.
Proof.
  intros flags H. unfold modeled_open_flags. cbv zeta. rewrite H.
  now rewrite Bool.orb_true_r.
Qed.

(** The common result of opening an existing object: either an
    injectable failure, or the lowest free fd followed by [mk]'s model
    update.  Every arm below that hands back a descriptor shares this
    exact success shape. *)
Definition open_result_spec (m : Model) (mk : word -> Model -> Model)
    : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)
      (fd <- lowest_fd (m_fds m) ;;
       modify (mk fd) ;;
       ret_only fd).

(** The effect a modeled WRITE-CREATE open records, shared by the
    clobbering (O_TRUNC) and the exclusive (O_EXCL) shapes so the two
    provably record the same thing: either an errno from
    [openat_errnos] (an environment condition the model does not track),
    or the lowest free fd bound to a write-only fd on inode [i], with
    the file system left as [fs'].  A table with no free fd never
    reaches this ([openat_core_spec] answers it first).

    [fs'] AND [i] ARE ONE OF TWO PAIRS, and every caller computes which.
    A name the walk found as an [Fs.EFile i] keeps its inode and is
    emptied ([Fs.fs_set_ino_data]): O_TRUNC is [handle_truncate] on the
    inode the dentry holds ([do_open], fs/namei.c), so every other name
    and descriptor of the file sees the empty file.  A name the walk
    reports missing is a new inode ([create_file_fs]).

    THE KEY IS A RESOLVED KEY.  It comes off [Fs.resolve] — the
    [Fs.child_key] an [Fs.RMissing] names — so it is absolute and
    canonical, and [Fs.wf_fs] survives the creation
    ([Fs.resolve_missing_create]).

    THE REGULAR-FILE PREMISE.  Entries carry their kind: a device is an
    [Fs.EDev] and reaches the device arms instead, a directory is an
    [Fs.EDir] and is -EISDIR, and the only way to reach this definition
    is an entry that is an [Fs.EFile] or a name that is absent.  FIFOs,
    sockets and kernfs attributes are not entry kinds this model has, so
    an image that claimed one would be claiming a regular file — which
    is a statement about the IMAGE the run is given, not a silent
    reinterpretation of a pathname. *)
Definition create_wronly (fs' : Fs.Fs) (i : Fs.ino) (m : Model)
    : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)  (* untracked env failure or no free fd *)
      (fd <- lowest_fd (m_fds m) ;;
       set_fs fs' ;;
       set_fds (fd_insert (m_fds m) fd (FdFileW i (Z_to_bv 64 0))) ;;  (* write-only fd *)
       ret_only fd).

(** A NEW REGULAR FILE at the key [k] an [Fs.RMissing] names: a fresh
    inode ([Fs.fs_fresh_ino]), empty, with one name.  [create_file_ino]
    is the inode the descriptor then holds.

    THE FOLDER IS ON TMPFS OR RAMFS, and that is why the new name is an
    empty regular file.  The parent's [->create] decides what a create
    makes ([lookup_open], fs/namei.c:3788-3797, Linux v6.18.46):
    [shmem_create] and [ramfs_create] make an empty regular file
    ([shmem_dir_inode_operations], mm/shmem.c:5281-5284;
    [ramfs_dir_inode_operations], fs/ramfs/inode.c:191-192), while an
    mqueue folder's [mqueue_create] makes a queue whose [i_size] is 80
    and whose operations have no [.write] (ipc/mqueue.c:53, :307-312,
    :612-616, :1619-1624).  SCOPE.md's launch premise puts every folder
    the walk reaches on tmpfs or ramfs, so every creating arm answers
    for those two. *)
Definition create_file_fs (fs : Fs.Fs) (k : Fs.path) : Fs.Fs :=
  Fs.fs_create_file fs k [].

Definition create_file_ino (fs : Fs.Fs) : Fs.ino := Fs.fs_fresh_ino fs.

(** The effect a modeled APPEND write-open records: either an errno from
    [openat_errnos] (the same untracked environment conditions the other
    write-open shapes admit), or the lowest free fd bound to a
    [State.FdFileA] on inode [i], with the file system left as [fs'].

    AN EXISTING FILE KEEPS ITS BYTES, AND THAT IS THE WHOLE POINT OF THE
    ARM: the callers pass [m_fs m] unchanged for a name the walk found,
    and [create_file_fs] only for a missing one.  [build_open_flags]
    turns O_TRUNC into [op->open_flag]'s O_TRUNC and [do_open]
    (fs/namei.c) then calls [handle_truncate], which empties an existing
    file; nothing on the O_APPEND path does, since O_APPEND is a
    file-STATUS flag [do_dentry_open] copies into [f_flags] and reads at
    write time (fs/open.c, mm/filemap.c [generic_write_checks]).

    THE OFFSET STARTS AT 0 AND THAT IS EXACT rather than a convenience.
    Linux gives every freshly opened description [f_pos = 0] —
    [alloc_empty_file] zeroes the [struct file] and no O_APPEND path
    assigns to [f_pos] at open time, which is why [fopen(p, "a")] has to
    be followed by an [ftell] that seeks to learn the size.  The append
    positioning happens per WRITE, in [generic_write_checks], and
    [ReadWrite.write_spec]'s [FdFileA] arm is where the model records
    it. *)
Definition open_append (fs' : Fs.Fs) (i : Fs.ino) (m : Model)
    : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)  (* untracked env failure or no free fd *)
      (fd <- lowest_fd (m_fds m) ;;
       set_fs fs' ;;
       set_fds (fd_insert (m_fds m) fd (FdFileA i (Z_to_bv 64 0))) ;;
       ret_only fd).

(** The effect a modeled READ-WRITE open records: either an errno from
    [openat_errnos], or the lowest free fd bound to a [State.FdFileRW]
    on inode [i], with the file system left as [fs'].

    THE OFFSET STARTS AT 0 for both directions, and it is the same
    [f_pos] both use: [alloc_empty_file] (fs/file_table.c) zeroes the
    [struct file], and nothing on the O_RDWR path assigns to [f_pos] at
    open time.  O_TRUNC does not move it either — it empties the file
    through [handle_truncate] and leaves the position alone, which is
    why a truncating open is [fs'] and not an offset. *)
Definition open_rdwr (fs' : Fs.Fs) (i : Fs.ino) (m : Model)
    : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)  (* untracked env failure or no free fd *)
      (fd <- lowest_fd (m_fds m) ;;
       set_fs fs' ;;
       set_fds (fd_insert (m_fds m) fd (FdFileRW i (Z_to_bv 64 0))) ;;
       ret_only fd).

(** The inode a descriptor holds WRITE ACCESS to, or [None]: the three
    write kinds of a regular file.  [do_dentry_open] (fs/open.c:926-929,
    Linux v6.18.46) takes write access for every FMODE_WRITE open of a
    regular file, and the file keeps it until its last fput, where
    [__fput] (fs/file_table.c:512) drops it.  ENUMERATED, as
    [State.entry_ino] is, so that a later [FdEntry] constructor able to
    hold write access stops the build here. *)
Definition entry_write_ino (e : FdEntry) : option Fs.ino :=
  match e with
  | FdFileW i _ | FdFileA i _ | FdFileRW i _ => Some i
  | FdFile _ _ | FdChannel _ | FdDir _ | FdSocket _ | FdPipe _ _
  | FdDevNull _ _ | FdUrandom _ _ | FdStream _ _ _ | FdEventfd _
  | FdDgram _ => None
  end.

(** Does some descriptor of the model hold write access to inode [i]? *)
Definition ino_write_held (fds : list (word * FdEntry)) (i : Fs.ino) : bool :=
  existsb (fun p => match entry_write_ino (snd p) with
                    | Some j => Z.eqb j i
                    | None => false
                    end) fds.

(** -ETXTBSY BESIDE A WRITE OPEN OF A FILE THAT EXISTS: [s], or a bare
    -ETXTBSY that leaves the model, the file's bytes included, as it
    was, unless a descriptor of the model holds write access to the
    file's inode [i], and then [s] alone.

    LINUX DENIES WRITE ACCESS TO A FILE SOMETHING EXECUTES.  [execve]
    opens its file with [do_open_execat], which takes
    [exe_file_deny_write_access] (fs/exec.c:798, Linux v6.18.46; the
    same line at v6.16 and v6.17), and the process's [mm] keeps the
    deny for as long as the file is its executable ([set_mm_exe_file],
    kernel/fork.c:1214).  A later open with write access then fails in
    [file_get_write_access] (fs/open.c:883-885), which [do_dentry_open]
    calls for a writer (:925-928), through [get_write_access]
    (include/linux/fs.h:3215-3218), with
    -ETXTBSY.  That is [do_open]'s [vfs_open] (fs/namei.c:3974-3975),
    after [may_open] and BEFORE [handle_truncate] (:3978-3979), so an
    O_TRUNC open of the file empties nothing.  The [execve] that
    launched this process holds such a deny on the file its AT_EXECFN
    names, and SCOPE.md says the image may hold that file.

    A LIVE WRITER RULES IT OUT.  The deny and the writers share one
    counter, the inode's [i_writecount]: [get_write_access] fails only
    while it is negative (include/linux/fs.h:3217) and [deny_write_access]
    only takes a deny while it is not positive (:3222).  A descriptor of
    the model that holds write access to [i] ([ino_write_held]: an
    [FdFileW], [FdFileA] or [FdFileRW] on [i], whatever name or
    "/proc/self/fd/N" it was opened through) was opened successfully, so
    no deny was in place then, and while it stays open the count stays
    positive, so none can be taken since: no -ETXTBSY stands beside the
    open then.

    WHY BESIDE AND NOT INSTEAD otherwise.  The model cannot tell which
    inode is executed: the launch's exec name is not in the
    [State.Model], a name [Run.valid_execfn] admits may be "/dev/fd/N"
    (an [execveat] through a descriptor, which names no file of the
    image), and the inode numbers of a dropped file are handed out again
    ([Fs.fs_fresh_ino]).  Declining instead would make the released copy
    examples' theorems false, since an operand of theirs may name the
    executable.  So every write-access open of a REGULAR FILE THE WALK
    FOUND that no descriptor of the model writes admits -ETXTBSY beside
    its own answers, which admits it for files nothing executes too: a
    trace no supported kernel gives, an over-admission (AGENTS.md's
    second priority) and never a rejected answer.  A file the open
    CREATES is a fresh inode nothing can be executing, so the
    [Fs.RMissing] rows keep their answers alone; a read-only open takes
    no write access ([do_dentry_open] counts a reader instead), and an
    O_EXCL open of an existing name is [do_open]'s -EEXIST first
    (fs/namei.c:3949-3950).  The devices take no write access either
    ([special_file], fs/open.c:925).

    The rows: [openat_create_spec], [openat_append_spec] (the plain
    word), [openat_rdwr_spec] (all four words, O_RDWR alone included)
    and the two write words of [openat_procfd_spec]. *)
Definition open_write_existing (m : Model) (i : Fs.ino) (s : Sys SyscallEffect)
    : Sys SyscallEffect :=
  if ino_write_held (m_fds m) i then s else alt (err_ret ETXTBSY) s.

(** The success shape every admitted /dev/null word shares: the
    injectable errno, or the lowest free fd bound to the entry with the
    granted access mode.

    THE DEVICE IS AN ENTRY, not a name.  [Fs.resolve] reaches an
    [Fs.EDev DevNull] or it does not, "/dev//null" and "/dev/./null"
    reach the same entry as "/dev/null" because the walk consumes both
    spellings to one key, and an image that puts a regular file at that
    key simply has a file there and takes the file arms.  A null device
    at ANY key answers the same way: Linux opens a character device
    through its inode's device number, whatever the name
    ([init_special_inode], fs/inode.c:2552-2577, sets [def_chr_fops];
    [chrdev_open], fs/char_dev.c:373-424, Linux v6.18.46, finds the
    driver by [i_rdev]), and the descriptor carries no key, so [k] does
    not choose the answer.  What a stat of such a descriptor may then
    hold is [Fs.Stat.fstat_devnull_spec]'s concern; the descriptor
    number's old stat pin is dropped before the entry is installed
    ([State.with_fd_unpinned]), since the number may have held a
    descriptor on another node of the kind.

    THE ENVIRONMENT ASSUMPTION the kind carries, unchanged and now
    stated of the ENTRY rather than of the name: an [Fs.EDev DevNull] is
    the null device, character major 1 minor 3, whose operations are
    [null_fops] (drivers/char/mem.c).  That is what the kind means, and
    it is the reason the arm is sound without a filesystem: nothing
    Linux does through this descriptor depends on the image, because
    [null_fops] never touches a page, a buffer or an inode's contents.
    Issue #696 records the ruling and
    bugs/openat-devnull-assumed-null-device.md records the premise, what
    breaks it and who consumes it.

    THE KERNEL PATH each flag word takes, all fs/namei.c (Linux
    v6.18.46) and all decided before the device's own [open] runs:

    - O_RDONLY, and the READ-WRITE words without O_EXCL: [do_open]
      (3931) reaches [may_open] (3527), whose S_IFCHR arm passes
      ([may_open_dev] is the one thing it tests, and -EACCES from it is
      already an [openat_errnos] alternative), then [vfs_open] ->
      [do_dentry_open] (fs/open.c) -> [chrdev_open] (fs/char_dev.c) ->
      [memory_open] (drivers/char/mem.c), which installs [null_fops].
      The descriptor carries the access mode [do_dentry_open] set.
    - O_WRONLY|O_CREAT|O_TRUNC: the same, because O_CREAT on an existing
      name creates nothing — [lookup_open] finds the positive dentry and
      [FMODE_CREATED] stays clear — and [do_open] arms the truncate only
      under [d_is_reg(nd->path.dentry)] (3967), which a character device
      fails, so the O_TRUNC is inert.
    - O_WRONLY|O_CREAT|O_APPEND: the same again.  O_APPEND reaches
      [f_flags] and nothing in [null_fops] reads it ([write_null] and
      [write_iter_null] return the count without consulting a position),
      and no modeled arm on this kind reads [f_flags], so the append
      word mints the same write-only entry the clobbering word does.
    - O_CREAT|O_EXCL, in either access mode, with or without O_APPEND:
      [do_open]'s [(open_flag & O_EXCL) && !(file->f_mode &
      FMODE_CREATED)] is -EEXIST (3949-3950), before [may_open].  The
      excl arms below answer that for every found entry without asking
      its kind, which is the same answer.
    - O_RDONLY|O_DIRECTORY: [do_open]'s [(nd->flags & LOOKUP_DIRECTORY)
      && !d_can_lookup(...)] is -ENOTDIR, which the directory arm below
      answers for every non-directory entry.

    WHY A DEVICE AND NOT A FILE.  bugs/fs-paths-assumed-regular-files.md
    is the record of what went wrong when this name was a key: a read
    handed back bytes a write had recorded, where [read_null] returns 0.
    [State.FdDevNull] carries no path and no contents, so no arm can
    make that mistake again. *)
Definition open_devnull (k : Fs.path) (m : Model) (rd wr : bool)
    : Sys SyscallEffect :=
  open_result_spec m
    (fun fd m' => with_fds (fd_insert (m_fds m) fd (FdDevNull rd wr))
                    (with_fd_unpinned fd m')).

(** The success shape for /dev/urandom: the injectable errno, or the
    lowest free fd bound to the entry with the granted access mode.

    THE ENVIRONMENT ASSUMPTION the kind carries: an [Fs.EDev DevUrandom]
    is the random device, character major 1 minor 9, whose operations
    are [urandom_fops] (drivers/char/random.c).  Issue #696 records the
    ruling and bugs/openat-urandom-assumed-random-device.md records the
    premise.  A random device at any key answers the same way, as the
    null device does, and the descriptor number's old stat pin is
    dropped the same way.

    WHAT THE BYTES ARE.  Not a choice: the run's [State.in_urandom]
    declares them, in order, and [ReadWrite.read_urandom] hands them out
    from the front.  That is the maintainer's ruling on #696 —
    /dev/urandom is an ARBITRARY BUT FIXED stream, a parameter of the
    execution like argv and envp, the same stream on both sides of an
    equivalence — and it is what makes a program that seeds itself from
    the device provable at all.  [getrandom] (278) is deliberately NOT
    drawn from it; the two stay unrelated in the model.

    THE WRITE WORDS OPEN, as on Linux, and the access mode is what the
    descriptor carries.  [devlist] gives the node mode 0666
    (drivers/char/mem.c:690-702, the "urandom" row at :701), so
    [may_open]'s S_IFCHR arm (fs/namei.c:3546-3550) admits a write open
    as it admits a read one, and [do_dentry_open] sets FMODE_WRITE from
    O_WRONLY or O_RDWR.  [may_open]'s -EPERM for an append-only inode
    (fs/namei.c:3572-3577) is excluded by SCOPE.md's attribute premise.
    O_TRUNC is inert on a character device, as for /dev/null, and
    O_APPEND reaches [f_flags], which the descriptor does not record and
    no arm needs: the one answer it could change, [pwritev2]'s -EPERM
    under RWF_NOAPPEND, needs an append-only inode too.  What a WRITE
    through such a descriptor answers is [ReadWrite.random_write]; a
    read through a write-only one is [vfs_read]'s -EBADF. *)
Definition open_urandom (k : Fs.path) (m : Model) (rd wr : bool)
    : Sys SyscallEffect :=
  open_result_spec m
    (fun fd m' => with_fds (fd_insert (m_fds m) fd (FdUrandom rd wr))
                    (with_fd_unpinned fd m')).

(* -------------------------------------------------------------------------
   The argv premise, which outlives the arms that used to read it
   ------------------------------------------------------------------------- *)

(** "." or "..", the two pathnames the walk answers out of itself.

    NO ARM ABOVE READS THIS ANY MORE.  It was the test that selected a
    dot arm before there was a namespace; [Fs.resolve] settles both
    spellings itself — "." stays on the key the walk stands on and ".."
    pops to its parent, which is what [Fs.walk_comps]'s [LastDot] and
    [LastDotDot] rows are — so the open arms match on an [Fs.Resolved]
    and never on the spelling.

    IT SURVIVES AS PART OF THE ARGV PREMISE, which is a different thing
    and has a different lifetime: [Run.valid_argv]'s fifth clause says
    an argument past the zeroth holds no separator and is not "..", and
    [Common.CatExec.valid_argv_str_plain] delivers that clause to the
    two whole-program examples in exactly this shape.  Relaxing the
    clause is a named follow-on rather than part of R22 (issue #1011,
    section 5), so the shape stays until it is relaxed and this goes
    with it. *)
Definition path_is_dirref (p : path) : bool :=
  path_eqb p dot_path || path_eqb p dotdot_path.

(** A pathname [Run.valid_argv]'s fifth clause guarantees: not a
    directory reference, and not slash-bearing.  It is no longer a
    premise any openat arm carries — every pathname is resolved now —
    and it is not a claim about the IMAGE either: what it says is that
    the argument names something in the working directory, which is what
    lets a harness proof reach the entry in one rewrite.  [Common] and
    both examples are its only readers. *)
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

(** A directory reference has no separator, which is what makes the two
    halves of the clause independent. *)
Lemma path_is_dirref_no_slash : forall p,
  path_is_dirref p = true -> path_has_slash p = false.
Proof.
  intros p H. unfold path_is_dirref in H.
  apply orb_true_elim in H. destruct H as [H|H];
    apply path_eqb_eq in H; subst p; reflexivity.
Qed.

(* -------------------------------------------------------------------------
   The trailing separator is the walk's
   ------------------------------------------------------------------------- *)

(** THE WALK ALONE DECIDES WHAT A TRAILING SEPARATOR DOES, so no arm
    below reads the separator.  [lookup_fast_for_open]
    (fs/namei.c:3817-3846, Linux v6.18.46) has two branches:

    - with O_CREAT, [if (trailing_slashes(nd)) return ERR_PTR(-EISDIR);]
      (:3821-3823), before any lookup: the [Fs.WalkCreate] walk stops in
      front of such a name ([Fs.we_create_slash]) and answers
      [Fs.RParent], which every creating arm answers -EISDIR.  So an
      [Fs.RMissing] or [Fs.RFound] of that walk never carries the
      separator after a normal last name.
    - without it, [nd->flags |= LOOKUP_FOLLOW | LOOKUP_DIRECTORY]
      (:3830-3831), and [do_open]'s closing test
      [(nd->flags & LOOKUP_DIRECTORY) && !d_can_lookup(...)] is -ENOTDIR
      (:3958-3959): the [Fs.WalkFull] walk sets both itself and answers
      [Fs.RNotDir] on a non-folder at its end ([Fs.we_notdir_end]).

    [open_last_lookups] (:3848-3868) settles "." and ".." through
    [handle_dots] before either branch, so the separator after them
    changes nothing, which is how the walk treats them too.  The
    distinction stays observable through the walk: [openat("./",
    O_WRONLY|O_CREAT|O_EXCL)] is -EEXIST and [openat("d/", ...)] on a
    folder [d] is -EISDIR. *)


(* -------------------------------------------------------------------------
   The arms, each a match on [Fs.resolve] and its own flag ladder
   ------------------------------------------------------------------------- *)

(** THE PLAIN O_RDONLY OPEN.

    A DIRECTORY ANSWERS WITH A DESCRIPTOR ON ITS KEY.  [may_open]'s
    S_IFDIR arm refuses only MAY_WRITE, which O_RDONLY does not carry,
    so a read-only open of a directory succeeds on Linux and the model
    hands back a [State.FdDir] naming the resolved key.  That is where
    "." and ".." land now — the walk settles both out of itself, so
    [openat(".", O_RDONLY)] is a descriptor on the working directory and
    [openat("..", O_RDONLY)] one on its parent — and it is also where
    [openat("/work", O_RDONLY)] lands, which the pre-namespace arm could
    not answer at all.  The key is what [Fs.Stat.fstat_spec] and
    [Fs.Readdir.getdents64_spec] read.

    THE PREFIX OUTCOMES are the walk's own answers and do not depend on
    the flag word: [Fs.RNotDir] is -ENOTDIR, [Fs.RAbsent] is -ENOENT,
    [Fs.RLoop] is -ELOOP (the 41st link, [reserve_stack],
    fs/namei.c:1878-1879), and [Fs.ROutside] declines because /proc and
    /sys are outside the modeled surface (issue #1011, section 15,
    question 8): "proc" and "sys" looked up at the root, by any spelling
    or link.  A name the walk does not find under /dev is an ordinary
    absence ([Fs.RMissing] or [Fs.RAbsent]), since the image describes
    /dev completely at launch.  A component over [Fs.name_max] is no
    outcome: the walk goes on and -ENAMETOOLONG stands beside its answer
    ([Fs.Namei.walk_errnos]).

    [Fs.RMissing] IS -ENOENT HERE, not a create: without O_CREAT
    [lookup_fast_for_open] or [lookup_open] hands back a negative dentry,
    which [step_into] receives from [open_last_lookups] (fs/namei.c:3922);
    its [handle_mounts] calls [traverse_mounts], which answers -ENOENT
    for a negative dentry (:1537-1538), so [do_open] is never reached.

    A LINK AT THE LAST COMPONENT is one the walk did not follow, which
    is O_NOFOLLOW ([open_walk_mode]); [may_open] refuses it with -ELOOP
    ([case S_IFLNK: return -ELOOP], fs/namei.c:3538-3539).  A trailing
    separator still forces the follow and asks for a folder
    (fs/namei.c:3830-3831), so the walk has already answered that case.
    [Fs.RParent] is the [O_CREAT] walk's, and this walk never gives it. *)
Definition openat_read_spec (r : Fs.Resolved) (m : Model)
    : Sys SyscallEffect :=
  match r with
  | Fs.RFound k e =>
        match e with
        | EDir =>
            open_result_spec m
              (fun fd => with_fds (fd_insert (m_fds m) fd (FdDir k)))
        | EFile i =>
            open_result_spec m
              (fun fd => with_fds (fd_insert (m_fds m) fd
                                     (FdFile i (Z_to_bv 64 0))))
        | EDev DevNull => open_devnull k m true false
        | EDev DevUrandom => open_urandom k m true false
        | ELink _ => err_ret ELOOP   (* [may_open], fs/namei.c:3538-3539 *)
        end
  | Fs.RMissing _ _ => err_ret ENOENT
  | Fs.RNotDir _ => err_ret ENOTDIR
  | Fs.RAbsent _ => err_ret ENOENT
  | Fs.RLoop => err_ret ELOOP
  | Fs.ROutside => unmodeled   (* "proc" and "sys" at the root *)
  | Fs.RParent _ _ => unmodeled   (* the [O_CREAT] walk's end only *)
  end.

(** THE CLOBBERING O_WRONLY|O_CREAT|O_TRUNC OPEN.

    A DIRECTORY IS -EISDIR, from [do_open]'s [d_is_dir(nd->path.dentry)]
    inside the [open_flag & O_CREAT] block, which runs before [may_open]
    and before any O_TRUNC handling.  "." and ".." take that row through
    [handle_dots], and so does any other directory the walk reaches.

    AN ABSENT LAST COMPONENT IS CREATED at the key [Fs.RMissing] names,
    which is what [Fs.resolve_missing_create] makes safe: the parent
    resolved as a directory, the name is a nameable component, the child
    key is canonical with that parent, and nothing is there yet, so
    [Fs.wf_fs] survives and the same pathname then resolves to what was
    created.

    THE DEVICES TAKE THEIR WRITE-ONLY ROWS; [open_devnull] and
    [open_urandom] carry the access mode. *)
Definition openat_create_spec (r : Fs.Resolved) (m : Model)
    : Sys SyscallEffect :=
  match r with
  | Fs.RNotDir _ => err_ret ENOTDIR
  | Fs.RAbsent _ => err_ret ENOENT
  | Fs.RLoop => err_ret ELOOP
  | Fs.ROutside => unmodeled
  | Fs.RParent _ _ => err_ret EISDIR
      (* a last name with a separator: [lookup_fast_for_open]'s -EISDIR
         before any lookup, fs/namei.c:3821-3823 *)
  | Fs.RMissing par nm =>
      create_wronly (create_file_fs (m_fs m) (Fs.child_key par nm))
                    (create_file_ino (m_fs m)) m
  | Fs.RFound k e =>
        match e with
        | EDir => err_ret EISDIR
        | EFile i =>
            open_write_existing m i
              (create_wronly (Fs.fs_set_ino_data (m_fs m) i []) i m)
            (* O_TRUNC empties the inode, or -ETXTBSY first *)
        | EDev DevNull => open_devnull k m false true
        | EDev DevUrandom => open_urandom k m false true
        | ELink _ => err_ret ELOOP
            (* O_NOFOLLOW: not O_EXCL, not a folder, so [may_open]'s
               S_IFLNK row, fs/namei.c:3538-3539 *)
        end
  end.

(** THE EXCLUSIVE O_WRONLY|O_CREAT|O_EXCL OPEN.

    THE EXISTENCE TEST COMES BEFORE ANY TYPE TEST, as Linux's does:
    [do_open]'s [(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)]
    is -EEXIST for a positive dentry whatever it is, and it runs before
    the [d_is_dir] the clobbering shape answers on.  So a directory, a
    file and either device all answer -EEXIST here, and the arm does not
    ask the entry's kind at all.

    THE TRAILING SEPARATOR STILL PREEMPTS IT, because
    [lookup_fast_for_open]'s -EISDIR is the first statement of its
    O_CREAT block and the O_EXCL short-circuit ("Don't bother on an
    O_EXCL create") is the second (fs/namei.c:3821-3827): the walk's
    [Fs.RParent]. *)
Definition openat_excl_spec (r : Fs.Resolved) (m : Model)
    : Sys SyscallEffect :=
  match r with
  | Fs.RNotDir _ => err_ret ENOTDIR
  | Fs.RAbsent _ => err_ret ENOENT
  | Fs.RLoop => err_ret ELOOP
  | Fs.ROutside => unmodeled
  | Fs.RParent _ _ => err_ret EISDIR   (* fs/namei.c:3821-3823 *)
  | Fs.RMissing par nm =>
      create_wronly (create_file_fs (m_fs m) (Fs.child_key par nm))
                    (create_file_ino (m_fs m)) m
  | Fs.RFound _ _ => err_ret EEXIST
        (* a link too: O_EXCL sets O_NOFOLLOW ([build_open_flags],
           fs/open.c), so the link itself is the positive dentry
           [do_open] answers -EEXIST on (fs/namei.c:3949-3950) *)
  end.

(** THE APPEND O_WRONLY|O_CREAT|O_APPEND OPEN, and with [excl] its
    exclusive twin O_WRONLY|O_CREAT|O_EXCL|O_APPEND
    ([is_excl_append_create]).

    A DIRECTORY IS -EISDIR on the plain word, the clobbering shape's
    answer and not the exclusive shape's -EEXIST, and the reason is
    which test [do_open] reaches first (fs/namei.c:3948-3952, Linux
    v6.18.46): with O_CREAT set it returns -EEXIST only under O_EXCL,
    which the plain word does not carry, and the next test is
    [d_is_dir].

    UNDER [excl] EVERY FOUND ENTRY IS -EEXIST, before the type test, by
    that same [(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)]
    (3949-3950); the trailing separator's -EISDIR still preempts it,
    because [lookup_fast_for_open]'s -EISDIR is the first statement of
    its O_CREAT block (3821-3823) and the O_EXCL short-circuit the
    second (3825-3827), which is the walk's [Fs.RParent].  An absent
    name is created as on the plain word, so the exclusive append is
    the plain append's creation with the exclusive open's -EEXIST.

    AN EXISTING FILE KEEPS ITS BYTES, which is the whole point of the
    arm; [open_append] carries the derivation. *)
Definition openat_append_spec (excl : bool) (r : Fs.Resolved) (m : Model)
    : Sys SyscallEffect :=
  match r with
  | Fs.RNotDir _ => err_ret ENOTDIR
  | Fs.RAbsent _ => err_ret ENOENT
  | Fs.RLoop => err_ret ELOOP
  | Fs.ROutside => unmodeled
  | Fs.RParent _ _ => err_ret EISDIR   (* fs/namei.c:3821-3823 *)
  | Fs.RMissing par nm =>
      open_append (create_file_fs (m_fs m) (Fs.child_key par nm))
                  (create_file_ino (m_fs m)) m
  | Fs.RFound k e =>
      if excl then err_ret EEXIST
      else
        match e with
        | EDir => err_ret EISDIR
        | EFile i => open_write_existing m i (open_append (m_fs m) i m)
        | EDev DevNull => open_devnull k m false true
        | EDev DevUrandom => open_urandom k m false true
        | ELink _ => err_ret ELOOP   (* O_NOFOLLOW: fs/namei.c:3538-3539 *)
        end
  end.

(** THE FOUR NON-EXCLUSIVE READ-WRITE WORDS, with [creat] and [trunc]
    the two bits that separate them ([rdwr_open_word] says why they are
    one arm).

    A DIRECTORY IS -EISDIR whatever the two bits say, and the two bit
    settings reach it at different sites.  With O_CREAT it is
    [do_open]'s own [d_is_dir(nd->path.dentry)], inside the
    [open_flag & O_CREAT] block; without it, nothing in that block runs
    and the answer comes from [may_open]'s [case S_IFDIR: if (acc_mode &
    MAY_WRITE) return -EISDIR], with MAY_WRITE present because
    [build_open_flags] (fs/open.c) sets [acc_mode = ACC_MODE(flags)] and
    [ACC_MODE] maps O_RDWR to MAY_READ|MAY_WRITE (include/linux/fs.h).
    Same errno, two derivations, and the second is the one O_RDONLY
    never reaches — which is why the plain read arm hands a directory a
    descriptor and this arm cannot.

    THE TRAILING SEPARATOR depends on [creat], and that is the one
    place the two bits change more than the answer's value:
    [lookup_fast_for_open]'s -EISDIR is inside [if (open_flag &
    O_CREAT)] (fs/namei.c:3821-3823), so without O_CREAT a trailing
    separator instead sets LOOKUP_DIRECTORY (:3830-3831) and [do_open]
    answers -ENOTDIR on a non-directory (:3958-3959).  Both are the
    walk's ([open_walk_mode]): [Fs.RParent] under O_CREAT and
    [Fs.RNotDir] without it.

    AN ABSENT NAME is a fresh empty file under O_CREAT and -ENOENT
    without it.  AN EXISTING FILE is emptied under O_TRUNC and keeps its
    bytes without it.  A file the open just CREATED is empty either way,
    which is why [creat] and [trunc] are not composed on that branch —
    and Linux says the same thing rather than merely agreeing by
    arithmetic, since [do_open] clears O_TRUNC from [open_flag] under
    [file->f_mode & FMODE_CREATED] before the truncate test. *)
Definition openat_rdwr_spec (creat trunc : bool) (r : Fs.Resolved) (m : Model)
    : Sys SyscallEffect :=
  match r with
  | Fs.RNotDir _ => err_ret ENOTDIR
  | Fs.RAbsent _ => err_ret ENOENT
  | Fs.RLoop => err_ret ELOOP
  | Fs.ROutside => unmodeled
  | Fs.RParent _ _ => if creat then err_ret EISDIR else unmodeled
      (* only the [O_CREAT] walk ends there: fs/namei.c:3821-3823 *)
  | Fs.RMissing par nm =>
      if creat then
        open_rdwr (create_file_fs (m_fs m) (Fs.child_key par nm))
                  (create_file_ino (m_fs m)) m
      else err_ret ENOENT
  | Fs.RFound k e =>
        match e with
        | EDir => err_ret EISDIR
        | EFile i =>
            open_write_existing m i
              (open_rdwr (if trunc then Fs.fs_set_ino_data (m_fs m) i []
                          else m_fs m) i m)
        | EDev DevNull => open_devnull k m true true
        | EDev DevUrandom => open_urandom k m true true
        | ELink _ => err_ret ELOOP   (* O_NOFOLLOW: fs/namei.c:3538-3539 *)
        end
  end.

(** THE EXCLUSIVE READ-WRITE CREATE.  The shape of [openat_excl_spec]
    with the fd kind changed and no other difference: O_EXCL's -EEXIST
    is decided before any type test, so a directory answers -EEXIST here
    rather than the -EISDIR [openat_rdwr_spec] gives it.  A missing name
    becomes an empty regular file because its folder is on tmpfs or
    ramfs ([create_file_fs]; SCOPE.md's launch premise). *)
Definition openat_rdwr_excl_spec (r : Fs.Resolved) (m : Model)
    : Sys SyscallEffect :=
  match r with
  | Fs.RNotDir _ => err_ret ENOTDIR
  | Fs.RAbsent _ => err_ret ENOENT
  | Fs.RLoop => err_ret ELOOP
  | Fs.ROutside => unmodeled
  | Fs.RParent _ _ => err_ret EISDIR   (* fs/namei.c:3821-3823 *)
  | Fs.RMissing par nm =>
      open_rdwr (create_file_fs (m_fs m) (Fs.child_key par nm))
                (create_file_ino (m_fs m)) m
  | Fs.RFound _ _ => err_ret EEXIST
  end.

(** THE O_RDONLY|O_DIRECTORY OPEN.

    -ENOTDIR IS TYPE-BLIND, and that is still what makes the arm short.
    [build_open_flags] (fs/open.c) turns O_DIRECTORY into
    LOOKUP_DIRECTORY, and [do_open] answers -ENOTDIR for any resolved
    dentry that [d_can_lookup] refuses.  So the model does not have to
    know which kind of non-directory a key names: a file and both
    devices answer alike.

    THE IMPLIED-DIRECTORY GUARD this arm used to take was a flat-map
    artefact, and a directory is an [Fs.EDir] entry that this arm opens.

    THE TRAILING SEPARATOR CHANGES NOTHING HERE: LOOKUP_DIRECTORY is
    already set by the flag, and the walk answers [Fs.RNotDir] for a
    non-folder at its end (fs/namei.c:3958-3959).  So does a last link
    under O_NOFOLLOW|O_DIRECTORY: -ENOTDIR comes before [may_open]'s
    -ELOOP. *)
Definition openat_dir_spec (r : Fs.Resolved) (m : Model)
    : Sys SyscallEffect :=
  match r with
  | Fs.RFound k EDir =>
      open_result_spec m
        (fun fd => with_fds (fd_insert (m_fds m) fd (FdDir k)))
  | Fs.RFound _ (EFile _) => err_ret ENOTDIR
  | Fs.RFound _ (EDev _) => err_ret ENOTDIR
  | Fs.RFound _ (ELink _) => err_ret ENOTDIR   (* fs/namei.c:3958-3959 *)
  | Fs.RMissing _ _ => err_ret ENOENT
  | Fs.RNotDir _ => err_ret ENOTDIR
  | Fs.RAbsent _ => err_ret ENOENT
  | Fs.RLoop => err_ret ELOOP
  | Fs.ROutside => unmodeled
  | Fs.RParent _ _ => unmodeled   (* the [O_CREAT] walk's end only *)
  end.

(** Strip a fixed prefix off a path, or say it is not there. *)
Fixpoint path_strip_prefix (pre p : path) : option path :=
  match pre, p with
  | [], _ => Some p
  | _ :: _, [] => None
  | a :: pre', b :: p' =>
      if bv_eqb a b then path_strip_prefix pre' p' else None
  end.

Lemma path_strip_prefix_app : forall pre p n,
  path_strip_prefix pre p = Some n -> p = pre ++ n.
Proof.
  induction pre as [|a pre IH]; intros p n H; cbn in H.
  - now inversion H.
  - destruct p as [|b p]; [discriminate|].
    destruct (bv_eqb a b) eqn:Hab; [|discriminate].
    apply bv_eqb_eq in Hab; subst b.
    cbn. f_equal. now apply IH.
Qed.

(** "/proc/self/fd/", the directory part of the one procfs pathname
    [openat] answers ([openat_procfd_spec]). *)
Definition proc_self_fd_prefix : path :=
  [Z_to_bv 8 47; Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 111; Z_to_bv 8 99;
   Z_to_bv 8 47; Z_to_bv 8 115; Z_to_bv 8 101; Z_to_bv 8 108; Z_to_bv 8 102;
   Z_to_bv 8 47; Z_to_bv 8 102; Z_to_bv 8 100; Z_to_bv 8 47].

(** The value of a string of decimal digits, read from the left onto
    [acc]; [None] at the first byte that is not '0'..'9'. *)
Fixpoint dec_digits_value (acc : Z) (ds : list byte) : option Z :=
  match ds with
  | [] => Some acc
  | b :: r =>
      let c := (bv_unsigned b - 48)%Z in
      if ((0 <=? c) && (c <=? 9))%Z then dec_digits_value (acc * 10 + c)%Z r
      else None
  end.

(** THE LAST COMPONENT OF "/proc/self/fd/N" AS A DESCRIPTOR NUMBER, the
    way [name_to_int] (fs/proc/util.c, Linux v6.18.46) reads it for
    [proc_lookupfd_common] (fs/proc/fd.c): decimal digits only, and no
    leading zero unless the numeral is "0" itself
    ([if (len > 1 && *name == '0') goto out]).

    NARROWER THAN [name_to_int] in one place, on purpose: it accepts a
    value up to about 2^32 - 16 and answers -ENOENT for any it finds no
    descriptor at, and this accepts only values up to 2^31 - 1, the
    largest descriptor number Linux can hand out; a larger numeral is
    [None], so the path goes to the walk, which answers [Fs.ROutside]
    for "proc" at the root and every arm declines, where Linux would
    answer -ENOENT. *)
Definition proc_fd_numeral (n : path) : option Z :=
  match n with
  | [] => None
  | b :: r =>
      if (bv_eqb b (Z_to_bv 8 48) && negb (path_eqb r []))%bool then None
      else match dec_digits_value 0 n with
           | Some v => if (v <=? 2 ^ 31 - 1)%Z then Some v else None
           | None => None
           end
  end.

(** [Some fd] iff [p] is exactly "/proc/self/fd/" followed by a numeral
    [proc_fd_numeral] reads as [fd].  Every other spelling -- a trailing
    separator, "/proc/<pid>/fd/N", "/proc/self/fdinfo/N", a doubled
    separator, a "." or ".." component -- is [None], and every such
    path goes to the walk, whose [Fs.ROutside] for "proc" at the root
    every arm declines. *)
Definition proc_self_fd (p : path) : option word :=
  match path_strip_prefix proc_self_fd_prefix p with
  | None => None
  | Some n =>
      match proc_fd_numeral n with
      | Some v => Some (Z_to_bv 64 v)
      | None => None
      end
  end.

(** [openat(AT_FDCWD, "/proc/self/fd/N", flags)]: open AGAIN the regular
    file descriptor [N] holds, by its INODE, whether a name still reaches
    it or not.  A program handed that path for a [tmpfile()] opens it
    with one of three words — O_RDONLY to read the file back,
    O_WRONLY|O_CREAT|O_TRUNC to rewrite it, O_WRONLY|O_CREAT|O_APPEND to
    add to it — so those three are answered and every other word
    declines.  A FOURTH WORD IS DECLINED, NEVER READ AS ONE OF THE
    THREE: the test below compares the whole word, past
    [open_ignored_flags], with each of the three, and anything else is
    [unmodeled].  O_RDWR, O_EXCL, O_DIRECTORY, O_PATH, O_TMPFILE and
    O_NOFOLLOW are each a known hole of this arm, not an answer.

    THE ENVIRONMENT ASSUMPTION IT RESTS ON, stated here and in
    SCOPE.md: procfs is mounted at /proc for the run's own pid
    namespace, so "/proc/self" names this process.  Like every file arm
    of this model, this one checks no permission ([may_open]'s
    [inode_permission] is among [openat_errnos]' -EACCES and nothing
    else).

    THE PATH, Linux v6.18.46.  "self" is a symlink to the caller's tgid
    ([proc_self_get_link], fs/proc/self.c), and "fd" a directory whose
    [.permission], [proc_fd_permission] (fs/proc/fd.c), grants every
    access to the caller's own thread group.  The last component is
    looked up by [proc_lookupfd_common], which reads it with
    [name_to_int] ([proc_fd_numeral]) and returns -ENOENT unless
    [tid_fd_mode] finds a [struct file] at that number.  On a hit it
    makes a symlink whose [proc_fd_link] hands back the open file's own
    [f_path], and following it ([proc_pid_get_link], fs/proc/base.c)
    calls [nd_jump_link] (fs/namei.c), which makes that path the result
    of the walk: the open then runs [do_open] on the file's own dentry,
    so it opens the same inode -- the inode the descriptor carries
    ([State.FdFile]), whatever name now stands where the file's name
    stood, and also when no name is left (a removed name's dentry stays
    positive while the open file references it).

    THE ANSWERS, in [do_open]'s order (fs/namei.c):

    - no descriptor [N]: -ENOENT, with O_CREAT too.
      [lookup_open]'s lookup returns [proc_lookupfd_common]'s
      [ERR_PTR(-ENOENT)] and goes to [out_dput] before its
      [if (!dir_inode->i_op->create) error = -EACCES] can be reached;
      the fd directory has no [.create] and no [.atomic_open].  Like
      the other path-resolution errnos of this file it has no
      [openat_errnos] alternative ([openat_body_spec]'s APPROXIMATION).
    - a regular file at [N] (any of the four [State.FdFile] kinds): the
      [openat_errnos] alternatives, or the lowest free descriptor on the
      same inode, at [f_pos] 0 ([alloc_empty_file] zeroes the [struct
      file]), read-only for O_RDONLY, write-only for the two write
      words and appending for the append word.  O_CREAT finds the file
      there, so nothing is created and the mode is ignored; and
      [may_create_in_sticky] reads the mode of the directory the last
      lookup ran in, /proc/<pid>/fd, which is not sticky.  O_TRUNC
      empties the file for EVERY name and descriptor: [do_open] arms
      [handle_truncate] for a regular file and runs it after
      [vfs_open], on the inode.  The errno alternatives come before that
      and leave the file as it was, and so does the -ETXTBSY both write
      words admit beside them ([open_write_existing]): the inode may be
      the one an [execve] runs, which a read-only descriptor of it can
      hold, unless a descriptor of the model holds write access to it,
      the one at [N] included.
    - any other kind at [N]: declined.  A socket, a pipe end, an eventfd
      and a device each reach their own [->open] through [vfs_open]; a
      directory reached this way is not stated; and a channel is
      whatever the launcher put there. *)
Definition openat_procfd_spec (n flags : word) (m : Model)
    : Sys SyscallEffect :=
  let fl := Z.ldiff (bv_unsigned flags) open_ignored_flags in
  if negb (Z.eqb fl 0 || Z.eqb fl wr_create_flags
           || Z.eqb fl append_create_flags)%bool then unmodeled
    (* every other word, O_NOFOLLOW among them: the fd entry is a link
       that O_NOFOLLOW would stop on *)
  else
  match fd_lookup (m_fds m) n with
  | None => err_ret ENOENT
  | Some (FdFile i _) | Some (FdFileW i _) | Some (FdFileA i _)
  | Some (FdFileRW i _) =>
      if Z.eqb fl 0 then
        open_result_spec m (fun fd => with_fds (fd_insert (m_fds m) fd
                                                  (FdFile i (Z_to_bv 64 0))))
      else if Z.eqb fl wr_create_flags then
        open_write_existing m i
          (create_wronly (Fs.fs_set_ino_data (m_fs m) i []) i m)
      else open_write_existing m i (open_append (m_fs m) i m)
  | Some (FdChannel _) | Some (FdDir _)
  | Some (FdSocket _) | Some (FdPipe _ _) | Some (FdDevNull _ _)
  | Some (FdUrandom _ _) | Some (FdStream _ _ _) | Some (FdEventfd _)
  | Some (FdDgram _) => unmodeled
      (* each reopens differently: see above *)
  end.

(** "/proc/self/fd/N" FIRST, THEN ONE RESOLUTION, THEN THE FLAG LADDER.

    The procfs pathname is tested on the RAW pathname ahead of the walk
    ([proc_self_fd]), because [Fs.resolve] answers [Fs.ROutside] for
    "proc" looked up at the root and every arm declines that.

    Otherwise [Fs.resolve] is called once and its three results are
    handed to whichever arm the word selects, so no arm re-derives the
    walk and the [Checks] mirror can read every one of them through
    [Fs.resolve_spec].  The devices are entries the walk reaches, "/tmp/x"
    is an ordinary key, and "/etc/localtime" is whatever the image says:
    [Run.localtime_absent] is the validity clause that keeps it absent,
    so its open without O_CREAT and without O_NOFOLLOW is the walk's
    -ENOENT (under O_NOFOLLOW a dangling link there is [may_open]'s
    -ELOOP, fs/namei.c:3538-3539).

    THE FINAL [else unmodeled] IS UNREACHABLE: [openat_core_spec] has
    already refused every word [modeled_open_flags] does not admit. *)
Definition openat_resolved_spec (p : path) (flags : word) (m : Model)
    : Sys SyscallEffect :=
  match proc_self_fd p with
  | Some n => openat_procfd_spec n flags m
  | None =>
  let '(r, _, _) := Fs.resolve (open_walk_mode flags) (m_fs m) (m_cwd m) p in
  let fl := open_shape flags in
  if Z.eqb fl 0 then openat_read_spec r m
  else if Z.eqb fl wr_create_flags then openat_create_spec r m
  else if is_excl_create fl then openat_excl_spec r m
  else if Z.eqb fl O_DIRECTORY then openat_dir_spec r m
  else if Z.eqb fl append_create_flags then openat_append_spec false r m
  else if rdwr_open_word fl then
    openat_rdwr_spec (flag_set fl O_CREAT) (flag_set fl O_TRUNC) r m
  else if is_rdwr_excl_create fl then openat_rdwr_excl_spec r m
  else if is_excl_append_create fl then openat_append_spec true r m
  else unmodeled
  end.

(** [openat dirfd path flags mode].  Modeled shapes (the
    [open_ignored_flags] bits are accepted and ignored in all; [mode] is
    ignored):

    - O_RDONLY: a file opens for reading, a DIRECTORY opens as a
      [State.FdDir] on its key, /dev/null and /dev/urandom mint their
      device descriptors, and a name the walk cannot reach answers the
      walk's own errno;
    - O_WRONLY|O_CREAT|O_TRUNC: create or truncate at the RESOLVED key,
      -EISDIR on a directory and on a trailing separator, /dev/null
      write-only, /dev/urandom write-only;
    - O_WRONLY|O_CREAT|O_EXCL (with or without O_TRUNC,
      [is_excl_create]): create only if the name does not exist,
      otherwise the deterministic -EEXIST, whatever kind exists;
    - O_RDONLY|O_DIRECTORY: a directory opens, every other entry is
      -ENOTDIR;
    - O_WRONLY|O_CREAT|O_APPEND ([append_create_flags]): open for
      writing, creating the file empty if absent and leaving an existing
      file's bytes ALONE, with every write landing at the then-current
      end of file.  The fd is a [State.FdFileA];
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

    EVERY PATHNAME IS RESOLVED.  There is no separator gate and no magic
    name: [Fs.resolve] walks the components in [link_path_walk]'s order
    against the image, and the arms above match its six outcomes.  So
    "a/b" reads the key it names, "/dev/null" is the device because the
    image holds an [Fs.EDev] there, and "/no/such/file" under O_CREAT is
    the -ENOENT of a missing parent rather than a key minted out of the
    pathname.  ONE PATHNAME IS ANSWERED AHEAD OF THE WALK:
    "/proc/self/fd/N" ([proc_self_fd]) opens again the regular file
    descriptor N holds, by its inode, under three words, and is
    -ENOENT when no descriptor N is open, on the procfs assumption
    [openat_procfd_spec] states.  It is tested before [Fs.resolve]
    because the walk answers [Fs.ROutside] for "proc" at the root, which
    every arm declines.

    The EMPTY pathname fails with -ENOENT, whatever the (modeled) flags,
    and it is answered AHEAD of resolution as [getname_flags] answers it
    before any walk (fs/namei.c:167-171, Linux v6.18.46; AT_EMPTY_PATH
    is not modeled), with [__getname]'s -ENOMEM beside it (below).

    [dirfd] OTHER THAN AT_FDCWD IS STILL UNMODELED.  The kernel never
    reads [dfd] for an absolute pathname, so widening to "an absolute
    path under any dirfd" is free; it is a named follow-on rather than
    part of R22 (issue #1011, section 3).

    ORDER.  The kernel's own order is [build_open_flags()], then
    [getname()], then [get_unused_fd_flags()], then [do_filp_open],
    whose [path_init] reads the dirfd ([fdget_raw]) before the walk
    ([do_sys_openat2], fs/open.c:1427-1437, Linux v6.18.46), and this
    spec follows it: a flag word the model does not interpret yields
    [unmodeled] BEFORE any pathname is fetched, an over-long, unreadable
    or empty path answers a real errno even when the dirfd is one the
    model declines, and so does a table with no free descriptor
    ([openat_core_spec]).

    [dirfd] arrives already truncated to 32 bits (see [Syscall.fd32]), as
    openat declares it [int]: AT_FDCWD is recognized in the low half
    ([AT_FDCWD32]), so [openat(2^32 - 100, ...)] is AT_FDCWD.

    The pathname fetch has all three of [getname()]'s answers:
    -ENAMETOOLONG for a path with no NUL within PATH_MAX, -EFAULT for
    one with an unmapped byte, and the string itself otherwise.  Both
    failures are deterministic returns the model tracks, like -ENOENT —
    not injectable, so they are not in [openat_errnos].  Beside both
    failures, and beside the empty pathname's -ENOENT and every answer
    past them, stands the -ENOMEM of [getname_flags]' allocations
    (fs/namei.c:146-148, 189-193), which fail before the copy is done
    and so carry no copy-in or only the first one's
    ([Fs.Namei.getname_refusals], in [openat_spec]).

    Anything else — a dirfd other than AT_FDCWD, other flag
    combinations — is [unmodeled].  An open on an arm that can SUCCEED
    may instead fail with an errno from [openat_errnos] (environment
    conditions the model does not decide), and a write open of a
    regular file the walk found may instead answer -ETXTBSY
    ([open_write_existing]) while no descriptor of the model writes it.  The -EMFILE
    among [openat_errnos] is the one that is not purely an environment condition:
    the model holds the run's soft RLIMIT_NOFILE in [State.m_nofile],
    and [File.lowest_fd] ignores it, so this spec can hand out an fd
    Linux would have refused.  That is
    bugs/fd-allocation-ignores-rlimit-nofile.md.  On success the kernel
    returns the lowest free fd ([File.lowest_fd]), as Linux does.  Flag
    arithmetic happens in [Z] on the unsigned flag word.

    APPROXIMATION (deliberate, and shared by every arm that reports a
    PATH-RESOLUTION errno deterministically — every errno the walk's
    outcomes carry, the directory's -EISDIR, the
    O_EXCL -EEXIST, the trailing separator's -EISDIR and -ENOTDIR, the
    -ENOTDIR O_DIRECTORY gives a non-directory, and
    [openat_procfd_spec]'s -ENOENT for a descriptor that is not open):
    those arms admit no [openat_errnos] alternative, whereas Linux can
    fail an openat with an errno raised BEFORE path resolution —
    [do_sys_openat2] calls [get_unused_fd_flags] before [do_filp_open],
    and [path_openat] calls [alloc_empty_file] before its walk
    (fs/namei.c:4124-4126) — so where the table still has a slot below
    [State.alloc_fd]'s scan wall but the soft RLIMIT_NOFILE is reached,
    the real call answers -EMFILE, and at the system limit -ENFILE,
    where the model insists on the resolution errno.  A table with no
    free slot at all is not approximate: [openat_core_spec] answers it
    before the walk.
    What they DO admit beside their answer is the walk's own -EACCES and
    -ENOMEM ([Fs.Namei.walk_refusals], applied in [openat_core_spec];
    a "/proc/self/fd/N" pathname is walked by Linux like any other, so
    it takes them too).  The empty pathname is answered before the walk
    and takes neither of the walk's, like the -ENAMETOOLONG and -EFAULT
    arms.  Every arm takes [getname_flags]' -ENOMEM, with the copy-in
    made when its allocation failed ([Fs.Namei.getname_refusals]).
    (Those three fetch arms are NOT approximate in the fd-table way:
    [getname()] runs before [get_unused_fd_flags] (fs/open.c:1431-1435),
    so they really do preempt fd exhaustion.)
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
        (* only now the dirfd ([path_init]'s [fdget_raw] runs after
           [getname]): the relative-to-a-dirfd modes aren't modeled, so we
           can't judge the call — [unmodeled], NOT the program faulting. *)
        else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
        else openat_resolved_spec p flags m
  end.

(** [getname()] HANDED ON A NAME: the fetch neither faulted nor ran
    past PATH_MAX, and the name is not the empty one [getname_flags]
    refuses with -ENOENT (fs/namei.c:167-171).  These are exactly the
    fetches [openat_body_spec] carries past its own three answers. *)
Definition openat_name_fetched (i : SyscallInput) (pathp : word) : bool :=
  match read_cstr (in_mem i) pathp with
  | CstrOk p => negb (path_eqb p [])
  | CstrTooLong | CstrFault => false
  end.

(** THE DESCRIPTOR COMES BEFORE THE WALK.  [do_sys_openat2] takes it
    with [get_unused_fd_flags] after [getname] and before
    [do_filp_open] (fs/open.c:1431-1437, Linux v6.18.46, in the same
    order at v6.16 and v6.17), so on a table
    with no free descriptor ([File.lowest_fd_none], the test the success
    path's [File.lowest_fd] empties on) every fetched name answers what
    [get_unused_fd_flags] answers there ([File.unused_fd_none_spec]):
    -EMFILE alone, ahead of the dirfd, the walk and every answer the walk
    leads to, the walk's own refusals and -ETXTBSY included, or a
    decline where the soft limit lets Linux hand out a descriptor past
    the ones [State.alloc_fd] scans.  That covers every arm the flag word
    selects, "/proc/self/fd/N" too.  [getname]'s own answers come before
    it and stay where they are, in [openat_body_spec], and
    [getname_flags]' -ENOMEM still stands beside the -EMFILE
    ([openat_spec]), since [__getname] runs before the descriptor is
    taken. *)
Definition openat_core_spec (dirfd pathp flags : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  (* [build_open_flags()] first, as Linux does: a flag combination the
     model does not interpret is unmodeled, so we can't judge the call —
     [unmodeled], and in particular NOT one of the pathname errnos below,
     which the kernel would never reach for a combination it rejects. *)
  if negb (modeled_open_flags flags) then unmodeled
  (* then [getname()], and on a name it handed on, [get_unused_fd_flags()]
     where the table has no free descriptor *)
  else if openat_name_fetched i pathp && lowest_fd_none (m_fds m)
  then unused_fd_none_spec m
  else
    (* otherwise all three of [getname()]'s answers are real errnos; and
       beside everything the walk leads to, the walk's own refusals. *)
    walk_refusals (open_walk_mode flags) pathp (openat_body_spec i m dirfd pathp flags).

(** The pathname copy-in ledger around the core, and [getname_flags]'
    own -ENOMEM outside it ([Fs.Namei.getname_refusals]): its
    allocations fail before the copy is done, so that answer does not
    claim the whole name read.  The core's [unmodeled] flag arm keeps
    it out, since a call the core declines admits no refusal. *)
Definition openat_spec (dirfd pathp flags : word) : Sys SyscallEffect :=
  i <- input ;;
  getname_refusals [] pathp
    (record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
       (openat_core_spec dirfd pathp flags)).

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
    sees them, as it does on Linux.

    A STREAM-PAIR END ([State.FdStream]) IS KIND-BLIND TOO, by choice and
    at a price stated where it is paid.  [unix_release_sock] also writes
    into the PEER — [SHUTDOWN_MASK], and [sk_err = ECONNRESET] when this
    end held unread bytes — and the model does not copy that here, so
    that this arm stays "the entry goes and nothing else moves", which
    published proofs rely on (theories/Common/FileSim.v [tfo_close]).
    The survivor reads its peer's close off the table instead
    ([State.stream_peer] is [None]), and the error the close may have
    left is chosen by the survivor's first call that shows it and kept
    in the survivor's own entry ([State.se_reset]); [State.StreamEnd]'s
    note says how. *)
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
    - a grow larger than [modeled_truncate_gap] permits is [unmodeled],
      fail closed, decided after the fd checks Linux makes first.

    WHAT THIS SPEC DOES NOT MODEL, and therefore what it assumes of the
    environment.  Four failures are named below, each from state the
    model does not carry; the list is the set a caller could plausibly
    reach, NOT an exhaustive enumeration of what this path can return.
    [notify_change] (fs/attr.c), which [do_truncate] calls, adds at
    least -EOVERFLOW on an inode whose uid or gid does not map in the
    mount's idmapping (its LSM veto, [security_inode_setattr], is a
    stub that answers 0 in the configuration of record, which builds no
    LSM, SCOPE.md),
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
    grow never reaches it.  Only the append-only test runs in either
    direction:

    - -EFBIG past RLIMIT_FSIZE, which ALSO raises SIGXFSZ, whose default
      action is to kill the process — GROW-ONLY;
    - -EFBIG past the filesystem's [s_maxbytes] — GROW-ONLY;
    - -EPERM from [IS_APPEND] — EITHER DIRECTION, and the only one of
      the four decided in [do_ftruncate] itself, before [do_truncate] is
      called; the LSM hook beside it, [security_file_truncate], is a
      stub that answers 0 in the configuration of record (SCOPE.md);
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
    openat.  RLIMIT_FSIZE is a premise on the environment and
    [s_maxbytes] a fact of the configuration of record (both below),
    and the bound does NOT stand in for either: [modeled_truncate_gap]
    bounds the per-call DELTA, while [s_maxbytes] and RLIMIT_FSIZE bound
    the ABSOLUTE size, so they are not comparable quantities and no
    number of in-bound calls is inductively safe against a limit below
    LLONG_MAX.

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

    [s_maxbytes] is the half the configuration of record settles.  The
    file systems it builds whose regular files hold the bytes written
    to them are tmpfs and ramfs (it builds no block device, FUSE,
    overlayfs or network file system: SCOPE.md), and both set
    [s_maxbytes] to MAX_LFS_FILESIZE = LLONG_MAX on a 64-bit kernel
    (mm/shmem.c shmem_fill_super, fs/ramfs/inode.c ramfs_fill_super,
    include/linux/fs.h).  [inode_newsize_ok] answers -EFBIG only for an
    [offset] past that, and no length reaches this arm past it, so no
    number of grows meets that -EFBIG on a supported kernel, although
    [modeled_truncate_gap] bounds only the per-call DELTA.  The write
    side meets the same limit only at LLONG_MAX:
    [generic_write_check_limits] answers -EFBIG when the START position
    is already there, and CLAMPS a write that merely crosses it into a
    short write, which the model's full count ([ReadWrite.write_spec]'s
    [FdFileW] arm is deterministic) does not admit.  A non-append write
    reaches neither, since [rw_verify_area] answers -EINVAL first for a
    position plus count past LLONG_MAX (fs/read_write.c, v6.18.46); an
    append write, whose position becomes the file's length only after
    that test, reaches them on a file already within its count of
    LLONG_MAX, and the append arms of the write specs answer both there
    ([ReadWrite.append_room]).

    -EROFS is deliberately absent, and that is a source-grounded
    difference from truncate(2)'s documented error list: there is no
    [mnt_want_write] and no [inode_permission] on the ftruncate path at
    all. Write access was settled at open time, so a read-only mount
    gives -EROFS at the openat and an -EINVAL here on the O_RDONLY fd
    that results.

    THIS SPEC USES NO -EFBIG CONSTANT, and needs none: on tmpfs and ramfs
    [s_maxbytes] is LLONG_MAX (above), so [modeled_truncate_gap] is the
    only thing standing at the top of the range.  A measurement under
    qemu-riscv64, which is not a supported implementation, found
    [ftruncate(fd, 2^63-1)] answering 0 on tmpfs and on overlayfs and
    -EFBIG on a virtiofs mount of the host; the configuration of record
    builds neither overlayfs nor virtiofs (no [CONFIG_OVERLAY_FS], no
    [CONFIG_FUSE_FS]: testing/vm/kernel.fragment), so that pair is no
    supported kernel's.  Above the bound the arm declines a grow that
    tmpfs and ramfs perform as they perform one below it: a priority-3
    gap, fail-closed, the cost of holding the file as a flat byte list
    ([modeled_truncate_gap]).

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
  | Some (FdStream _ _ _) => err_ret EINVAL      (* a stream-pair end is a socket too: S_ISSOCK,
                                                    the same [!S_ISREG] -EINVAL *)
  | Some (FdDgram _) => err_ret EINVAL           (* and so is a datagram socket *)
  | Some (FdEventfd _) => err_ret EINVAL         (* an eventfd's anonymous inode has no type bits
                                                   at all ([alloc_anon_inode], fs/libfs.c,
                                                   v6.18.46), so it is not S_ISREG and takes the
                                                   same -EINVAL though FMODE_WRITE is set *)
  | Some (FdPipe _ _) => err_ret EINVAL          (* the same answer for the same reason, on an fd
                                                    the model KNOWS is a pipe — see the header *)
  | Some (FdDevNull _ _) => err_ret EINVAL       (* and on /dev/null: a character device is not
                                                    S_ISREG, so [do_ftruncate] (fs/open.c, v6.18.46)
                                                    answers -EINVAL whatever the access mode *)
  | Some (FdUrandom _ _) => err_ret EINVAL       (* /dev/urandom is a character device too:
                                                    [do_ftruncate]'s [!S_ISREG] is the same
                                                    -EINVAL, tested before FMODE_WRITE *)
  | Some (FdFile _ _) => err_ret EINVAL          (* fd open read-only: no FMODE_WRITE, real -EINVAL *)
  | Some (FdDir _) => err_ret EINVAL                 (* a directory is not S_ISREG: real -EINVAL, not -EISDIR *)
  | Some (FdFileA i _) | Some (FdFileW i _) | Some (FdFileRW i _) =>
      (* ONE ARM FOR THE THREE WRITABLE KINDS.  [do_ftruncate]'s test is
         [!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)]
         (fs/open.c, Linux v6.18.46), and an O_RDWR description passes
         both halves exactly as an O_WRONLY one does; nothing further
         down reads the access mode.  The read-only [FdFile] arm above
         is the -EINVAL half of that same test.

         AN APPEND FD IS A WRITABLE REGULAR FILE TOO: O_APPEND rides on
         O_WRONLY, which is what sets FMODE_WRITE.  The flag is read
         nowhere on this path: [do_truncate] sets the size outright, and
         O_APPEND is consulted only by the write path's
         [generic_write_checks].  The inode's APPEND-ONLY attribute is a
         different thing and does bite here — [IS_APPEND(inode)] is
         [do_ftruncate]'s own -EPERM — but it is an inode attribute this
         model does not carry, and the header's list of unmodeled
         failures already names it.

         THE SIZE IS THE INODE'S, so every name and every descriptor of
         the file sees the new contents, a file no name reaches any
         more included ([Fs.fs_set_ino_data]).

         THE OFFSET IS UNTOUCHED, so a shrink can leave [f_pos] past
         end-of-file — this arm writes no [set_fds] at all.  On an
         append fd that is not observable through a later WRITE, which
         repositions itself, but it IS observable through
         [lseek(fd, 0, SEEK_CUR)], so leaving the entry alone is a
         decision here rather than a spare line. *)
      if negb (modeled_truncate_gap (Fs.fs_ino_data (m_fs m) i) len) then unmodeled
        (* a zero-fill too large to build as a byte list; Linux makes
           the file sparse for free — see [modeled_truncate_gap] *)
      else
        set_fs (Fs.fs_set_ino_data (m_fs m) i
                  (file_truncate (Fs.fs_ino_data (m_fs m) i) len)) ;;
        ret_only (Z_to_bv 64 0)
  end.

(** The refusals an F_OK probe can take beside its answer, as
    [Run.injected_table] names them for [faccessat] and [faccessat2]:
    environment conditions the model does not track, both of them
    reachable on an F_OK probe of a path that really exists.  Every one
    is the walk's, and the spec takes them from the walk
    ([Fs.Namei.walk_refusals] around [faccessat_body_spec], which hands
    out [Fs.Namei.walk_errnos] of the walk's last kind) and from
    [getname_flags] ([Fs.Namei.getname_refusals]); no arm draws from
    this list itself ([access_exists_spec]).

    - ENOMEM, from the allocations the walk makes once [getname_flags]
      has copied the name: the dentry a lookup allocates on a cache
      miss and the nested link stack (fs/namei.c;
      [Fs.Namei.walk_errnos]), so it carries the copy-in, as the
      success does.  [getname_flags]' own allocations, and
      [access_override_creds]'s [prepare_creds] (fs/open.c:486-490,
      ahead of [user_path_at]), fail before the copy is done and stand
      outside the ledger ([Fs.Namei.getname_refusals]).
    - EACCES, from the path walk's own search-permission check, and from
      that alone.  [link_path_walk] calls [may_lookup], which takes
      [inode_permission(..., MAY_EXEC)] on the folder the walk stands
      on, at the top of its loop, once per component and before the
      component is even typed (fs/namei.c:2466-2468, Linux v6.18.46):
      the first time on the folder the walk starts from, the working
      directory for a relative pathname and "/" for an absolute one.
      So it precedes every answer below, the "." and ".." ones
      included, and it needs a component: a pathname that is nothing
      but separators ("/", "//") returns from [link_path_walk] before
      the loop (:2451-2458), so its walk checks nothing, and F_OK of it
      admits no -EACCES ([Fs.LastRoot] in [Fs.Namei.walk_errnos]).
      NOT from an LSM: the configuration of record builds none
      (SCOPE.md), so [security_inode_permission] is the stub of
      include/linux/security.h that answers 0.

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

    WHAT IS LEFT OUT BY OTHER MEANS, and so is not a gate.  These reach a
    zero mask and can answer outside [faccessat_errnos].  Facts stated
    elsewhere rule out the first three; the fourth is why the arm
    declines a device:

    - [do_inode_permission] dispatches to [inode->i_op->permission]
      ahead of [generic_permission] and passes the mask through
      unfiltered (fs/namei.c).  MAY_ACCESS is exactly the bit some
      filesystems read: [fuse_permission] turns it into a FUSE_ACCESS
      request whose errno the userspace server picks (fs/fuse/dir.c),
      and [proc_pid_permission] can answer -ESRCH or, under hidepid,
      -ENOENT/-EPERM with a zero mask (fs/proc/base.c).  The
      configuration of record builds no FUSE (SCOPE.md), and no walk
      this spec answers reaches a procfs inode: [Fs.ROutside] declines
      /proc, the working folder lies outside it
      ([Run.outside_proc_sysb]), and SCOPE.md's launch premise mounts no
      file system but tmpfs and ramfs on a folder of the launch tree
      outside /proc and /sys, so no procfs is mounted anywhere else.
      tmpfs and ramfs install no [->permission] (mm/shmem.c,
      fs/ramfs/inode.c).
    - [posix_acl_permission] and [check_acl] can answer -EIO on a
      malformed or unreadable on-disk ACL (fs/posix_acl.c).  tmpfs and
      ramfs read none: tmpfs keeps an ACL in the inode's cache
      ([simple_set_acl], fs/posix_acl.c) and has no [->get_inode_acl]
      to fail, and ramfs sets no SB_POSIXACL, so [check_acl] is not
      reached.
    - -ESTALE, after [do_faccessat]'s own [retry_estale] loop has
      re-resolved once with LOOKUP_REVAL and failed again.  It needs a
      [d_revalidate] or a [d_weak_revalidate] that refuses, and tmpfs
      and ramfs install neither.
    - A DEVICE CGROUP, WHICH CAN ANSWER ANY ERRNO FOR F_OK.
      [devcgroup_inode_permission] (include/linux/device_cgroup.h:17-39)
      returns early only for a non-device inode; on a block or character
      node it calls [devcgroup_check_permission], which returns what the
      cgroup BPF device programs answer before it asks the v1 devices
      controller (security/device_cgroup.c:860-865).
      Their answer is the [run_ctx.retval] of [bpf_prog_run_array_cg]
      (kernel/bpf/cgroup.c:84-115, called at :1787): -EPERM for a program
      that denies (:110), and otherwise whatever value a program set
      through [bpf_set_retval] (:1839-1846), a helper every device
      program is offered ([cgroup_dev_func_proto] at :1856 takes
      [cgroup_common_func_proto]'s, :2778-2794), and which
      include/uapi/linux/bpf.h:5504-5518 documents as the value handed
      to user space.  The v1 controller answers -EPERM even for an empty
      access set ([devcgroup_legacy_check_permission],
      security/device_cgroup.c:832-854), all Linux v6.18.46.  The
      configuration of record builds both (CONFIG_CGROUP_DEVICE=y,
      CONFIG_CGROUP_BPF=y and CONFIG_BPF_SYSCALL=y in
      arch/riscv/configs/defconfig).
      SCOPE.md's premise on device cgroups excludes a cgroup whose BPF
      device programs or v1 controller refuse the process an open of
      /dev/null or /dev/urandom, and that premise is what makes the
      opens of the two nodes sound ([open_devnull], [open_urandom]):
      [may_open] reaches the same hook through [inode_permission]
      (fs/namei.c), and those arms admit nothing beside the descriptor
      but [openat_errnos].
      The premise does not fix F_OK's answer, and so this arm keeps its
      decline.  An open asks the hook for read or write access or both
      ([devcgroup_inode_permission] turns MAY_READ and MAY_WRITE into
      DEVCG_ACC_READ and DEVCG_ACC_WRITE,
      include/linux/device_cgroup.h:32-35); F_OK asks it for an empty
      access set.  A BPF device program reads the access set
      ([access_type], kernel/bpf/cgroup.c:1779), so it can refuse the
      empty set alone, with any value, while it lets every open through.
      The v1 controller cannot: it refuses the empty set only where it
      refuses the opens too.  Under its default of allow no exception
      matches an empty set ([match_exception_partial],
      security/device_cgroup.c:388-389), and under deny the exception
      that lets an open through matches the empty set as well
      ([match_exception], :342-343).  So F_OK of a device can still
      answer any errno, no list could hold the answer, and
      [faccessat_body_spec] declines the [Fs.EDev] row: a sound decline,
      which costs precision only.  At the launch of the agreement checks
      no device program is attached, and F_OK of /dev/null answers 0
      (testing/syscall-check/tests/faccessat_spec.c, dev-null).

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

(** The answer an F_OK probe of a path that RESOLVES to anything but a
    device gets: 0, as a bare return with every one of the five ledgers
    empty — faccessat writes nothing, zeroes nothing, unmaps nothing and
    copies out nothing, and the pathname copy-in is the wrapper's — and
    the model untouched, which is what makes this syscall a pure
    observation.

    ITS REFUSALS ARE THE WALK'S, not a list of its own.  The final
    [inode_permission(..., MAY_ACCESS)] of [do_faccessat] (fs/open.c:509,
    Linux v6.18.46) cannot refuse a zero mask on tmpfs or ramfs (WHAT A
    ZERO MASK EXCLUDES, at [faccessat_errnos]), so beside the 0 stand
    only [Fs.Namei.walk_refusals]' members, which the specs wrap around
    [faccessat_body_spec]: [Fs.Namei.walk_errnos] of the walk's last
    kind.  That is what keeps -EACCES to the pathnames whose walk runs
    [may_lookup]: F_OK of "/" or "//" ([Fs.LastRoot]) admits 0 and the
    walk's -ENOMEM, the over-admission [Fs.Namei.walk_errnos] records
    for a walk that allocates nothing, and no -EACCES; "/.", "a" and
    ".." admit -EACCES as well. *)
Definition access_exists_spec : Sys SyscallEffect := ret_only (Z_to_bv 64 0).

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
    [Fs] holds the names, each entry's kind, a regular file's bytes and
    the link counts, and nothing else: no mode bits, no owner, no mount
    flags.  R_OK, W_OK and X_OK are answered by [generic_permission] out
    of [inode->i_mode] against the caller's ids (fs/namei.c,
    [acl_permission_check]), and W_OK reaches [__mnt_is_readonly]
    besides.  None of that is a function of the image, so a mode with
    any of the low three bits set is [unmodeled].  F_OK asks the one
    question the image can answer: does this path resolve.

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
    override leaves is an -ENOMEM with no copy-in, which
    [Fs.Namei.getname_refusals] already admits.
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

    THE ANSWERS, once the path is in hand.  "." and ".." are the walk's
    own rows ([Fs.walk_comps]'s [LastDot] and [LastDotDot] cases): "."
    is the working directory and ".." its parent, and both exist by
    construction, so both are the existence
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
    directory has been renamed out from under a bind-mount root
    (fs/namei.c); it is not admitted here, because it needs a rename,
    which no modeled call makes and SCOPE.md's assumption that no other
    process changes the modeled files rules out for every other
    process.  Every other name is the walk's answer, below.

    THE WORLD IS THE NAMESPACE NOW, and the three guards this arm used
    to take are gone with the flat map.  A path containing "/" was
    declined because the model could not walk it; [Fs.resolve] walks it,
    so "a/b" reads the key it names, an absolute path reads the key it
    names, and a trailing separator is the walk's own business.  A name
    some key lived UNDER was declined because the map only IMPLIED a
    directory there; a directory is an [Fs.EDir] entry now, and F_OK of
    one answers 0, which is what Linux answers.  A component over
    [Uapi.NAME_MAX] is no outcome of the walk: -ENAMETOOLONG stands
    beside its answer ([Fs.Namei.walk_errnos]), because the limit
    belongs to the filesystem's [->lookup].  No supported kernel gives
    the walk's answer there, since tmpfs and ramfs both refuse at
    [simple_lookup]: a priority-2 gap ([Fs.comp_too_long]).

    SO EXISTENCE IS RESOLUTION, BUT FOR A DEVICE.  [Fs.RFound] of a
    file, a directory or a link is 0 — each exists, and F_OK asks
    nothing else.  [Fs.RFound] of either device DECLINES: a cgroup BPF
    device program can answer any errno for F_OK of it, and SCOPE.md's
    premise on device cgroups covers the opens of the two nodes, not
    F_OK's empty access set (the device-cgroup paragraph of
    [faccessat_errnos]), so no list of answers would be sound.
    [Fs.RMissing] and [Fs.RAbsent] are -ENOENT,
    [Fs.RNotDir] is -ENOTDIR, [Fs.RLoop] is -ELOOP, and [Fs.ROutside]
    declines because /proc and /sys are outside the surface (question
    8).  A LINK the walk did not follow (AT_SYMLINK_NOFOLLOW) exists
    too, and F_OK of it is 0; a link the walk followed to a device is
    the device's row.  bugs/faccessat-sees-only-the-map.md is
    narrowed to what is left, which is a fifo and a socket -- kinds
    this model does not have -- and modes other than F_OK.

    THE TRAILING SEPARATOR IS THE WALK'S.  [do_faccessat] calls
    [user_path_at] with no LOOKUP_DIRECTORY, but [lookup_last]
    (fs/namei.c:2649-2650) adds LOOKUP_DIRECTORY for a LAST_NORM
    component whose [last.name[last.len]] is non-NUL, and
    [path_lookupat] then ends with

        if (nd->flags & LOOKUP_DIRECTORY)
                if (!d_can_lookup(nd->path.dentry))
                        err = -ENOTDIR;

    (:2685-2687), so "file/" is -ENOTDIR and "dir/" is 0.  The
    [Fs.WalkFull] walk sets the flag itself and answers [Fs.RNotDir];
    bugs/faccessat-sees-only-the-map.md records what was wrong before
    R22 and what closed it.

    THE PATHNAME FETCH'S OWN ARMS — the empty pathname, an unreadable
    pointer and an over-long one — admit no refusal of the walk, since
    none of them reaches it.  Every answer, theirs included, takes the
    -ENOMEM [getname_flags] raises when an allocation fails before its
    copy is done (fs/namei.c:146-148 and 189-193, Linux v6.18.46;
    [Fs.Namei.getname_refusals]), which is also the errno, and the
    copy-in, [access_override_creds]'s [prepare_creds] answers ahead of
    [user_path_at] when the override runs (fs/open.c:486-490).  Every
    answer past the fetch takes the walk's own refusals beside it
    ([Fs.Namei.walk_refusals], in [faccessat_spec] and
    [faccessat2_spec]): -ENOMEM on every walk, and -EACCES on a walk
    with a component, which is every one but that of a pathname made of
    separators alone. *)
Definition faccessat_body_spec (md : Fs.WalkMode) (dirfd pathp : word)
    (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  match read_cstr (in_mem i) pathp with
  | CstrTooLong => err_ret ENAMETOOLONG          (* no NUL within PATH_MAX *)
  | CstrFault => err_ret EFAULT                  (* unmapped byte in the path string *)
  | CstrOk p =>
      if path_eqb p [] then err_ret ENOENT       (* empty pathname: getname's own -ENOENT *)
      else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
      else
        let '(r, _, _) := Fs.resolve md (m_fs m) (m_cwd m) p in
        match r with
        | Fs.RFound _ (Fs.EDev _) => unmodeled  (* a device cgroup picks the errno *)
        | Fs.RFound _ _ => access_exists_spec   (* it exists, whatever else it is *)
          (* A trailing separator on a non-directory is the walk's
             [Fs.RNotDir]: [lookup_last] adds LOOKUP_DIRECTORY for a
             LAST_NORM component a separator follows
             (fs/namei.c:2649-2650), and [path_lookupat] then ends with
             -ENOTDIR (:2685-2687). *)
        | Fs.RMissing _ _ => err_ret ENOENT
        | Fs.RNotDir _ => err_ret ENOTDIR
        | Fs.RAbsent _ => err_ret ENOENT
        | Fs.RLoop => err_ret ELOOP               (* the 41st link, fs/namei.c:1878-1879 *)
        | Fs.ROutside => unmodeled                (* "proc" and "sys" at the root *)
        | Fs.RParent _ _ => unmodeled             (* the parent and [O_CREAT] ends only *)
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
    the [unmodeled] arm claims nothing at all.  The -ENOMEM that fails
    before the copy is done stands outside the wrapper too, behind the
    mode arms ([Fs.Namei.getname_refusals]). *)
Definition faccessat_spec (dirfd pathp mode : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (modeled_access_mode mode) then err_ret EINVAL
  else if negb (access_mode_f_ok mode) then unmodeled
  else
    getname_refusals [] pathp
      (record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
         (walk_refusals (Fs.WalkFull true false) pathp
            (faccessat_body_spec (Fs.WalkFull true false) dirfd pathp i m))).

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

(** The accepted flag words this model ANSWERS: AT_EACCESS changes no
    answer it can give, and AT_SYMLINK_NOFOLLOW chooses how the walk
    ends ([access_walk_mode]).  AT_EMPTY_PATH is the one it declines, and the
    decline is a decline rather than an -EINVAL because the kernel
    accepts the bit.  See [faccessat2_spec] for both arguments. *)
Definition modeled_access_flags (flags : word) : bool :=
  Z.eqb (Z.land (access_flags flags) AT_EMPTY_PATH) 0.

(** HOW [do_faccessat]'s WALK ENDS: [LOOKUP_FOLLOW] unless
    AT_SYMLINK_NOFOLLOW (fs/open.c:472, :481-482), never
    [LOOKUP_DIRECTORY]. *)
Definition access_walk_mode (flags : word) : Fs.WalkMode :=
  Fs.WalkFull (negb (Z.eqb (Z.land (access_flags flags) AT_SYMLINK_NOFOLLOW)
                           AT_SYMLINK_NOFOLLOW)) false.

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
      but [__getname]'s can, with the same copy-in, none
      ([Fs.Namei.getname_refusals]).  Admitting the same set on both
      arms is therefore sound; it is not tighter than it could be
      because the tighter set is the same set.

    - AT_SYMLINK_NOFOLLOW clears LOOKUP_FOLLOW ([do_faccessat]'s
      [lookup_flags], fs/open.c:481-482), so a TRAILING link is not
      followed and F_OK asks about the link itself, which exists
      ([access_walk_mode]).  An intermediate link is followed whatever
      the bit says, and a trailing separator puts LOOKUP_FOLLOW back
      ([lookup_last], fs/namei.c:2649-2650): both are the walk's.

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
    getname_refusals [] pathp
      (record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
         (walk_refusals (access_walk_mode flags) pathp
            (faccessat_body_spec (access_walk_mode flags) dirfd pathp i m))).
