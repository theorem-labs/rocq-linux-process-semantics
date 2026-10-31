(** * LinuxProcessSem.Sys.Fs.Namei — unlinkat (35)

    This file answers to Linux [fs/namei.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    "." is the only path constant more than one syscall file needs, so
    it does not live in any of them: [Uapi.dot_path] defines it, and
    [openat], [newfstatat] and the [unlinkat] here all read it from
    there rather than from each other.

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

(** ".." — the parent directory.  Like ".", it is a path the kernel
    answers without consulting any file system: [link_path_walk] types
    the last component, and both [do_unlinkat] and [do_rmdir] branch on
    that type before they look anything up.  Their answers differ, which
    is why the two paths are separate constants here rather than one
    "directory reference" class. *)
Definition dotdot_path : path := [Z_to_bv 8 46; Z_to_bv 8 46].

Definition slash_byte : byte := Z_to_bv 8 47.

(** The SAME byte is spelled in [Fs], as [Fs.path_slash_byte], because
    [Fs.key_is_relative] needs it at a rung below this one and this file
    sits above it.  The separator's MEANING stays here — the component
    tests below are what a separator is for — and the two spellings are
    pinned equal so that moving either is a compile error rather than a
    silent divergence. *)
Lemma slash_byte_is_path_slash_byte : slash_byte = path_slash_byte.
Proof. reflexivity. Qed.

(** Does the path contain a component separator? *)
Definition path_has_slash (p : path) : bool :=
  existsb (fun b => bv_eqb b slash_byte) p.

(** Used on a REVERSED path, which is what makes it strip trailing
    separators; nothing else calls it. *)
Fixpoint drop_leading_slashes (p : path) : path :=
  match p with
  | [] => []
  | b :: r => if bv_eqb b slash_byte then drop_leading_slashes r else b :: r
  end.

(** Drop the separators a path ENDS with.  [link_path_walk] hashes a
    component, then skips every following "/" and stops if the string
    ends there, so trailing separators never start a component and never
    change which component is the last one (Linux fs/namei.c,
    [link_path_walk], the [if (!*name) goto OK] / skip-slashes / [if
    (unlikely(!*name))] sequence just after the [LAST_NORM] arm).  What
    they DO change is the byte [do_unlinkat] tests as
    [last.name[last.len]]: see [path_trailing_slash]. *)
Definition path_strip_trailing_slashes (p : path) : path :=
  rev (drop_leading_slashes (rev p)).

(** Is the last component followed by a separator?  This is the kernel's
    own [last.name[last.len]] — the byte just past the component, which
    is "/" exactly when the path had trailing separators and NUL
    otherwise. *)
Definition path_trailing_slash (p : path) : bool :=
  negb (Nat.eqb (length (path_strip_trailing_slashes p)) (length p)).

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

(** Does any file in [fs] live UNDER [p]?  If one does then [p] names a
    directory — a thing the flat map only implies and cannot hold. *)
Fixpoint fs_under (fs : Fs) (p : path) : bool :=
  match fs with
  | [] => false
  | (q, _) :: r => dir_prefixb p q || fs_under r p
  end.

(** [dir_prefixb] read back: a [true] exhibits the rest of the key.
    This is what lets a caller holding a fact about the BYTES of a key
    rule the test out — [Run.absolute_divergent_not_seeded] is the one
    that does, for a key the seeding minted under "/tmp/". *)
Lemma dir_prefixb_app : forall p q,
  dir_prefixb p q = true -> exists r, q = p ++ slash_byte :: r.
Proof.
  induction p as [|a p IH]; intros q H.
  - destruct q as [|c q]; [discriminate|].
    cbn in H. apply bv_eqb_eq in H; subst c. now exists q.
  - destruct q as [|b q]; [discriminate|].
    cbn in H. apply Bool.andb_true_iff in H. destruct H as [Hab Hr].
    apply bv_eqb_eq in Hab; subst b.
    destruct (IH q Hr) as [r Hq]. exists r. cbn. now f_equal.
Qed.

(** Neither half of [fs_under] can fire on a list of keys none of which
    continues [p] with a separator. *)
Lemma fs_under_false_of_keys : forall fs p,
  Forall (fun qd => dir_prefixb p (fst qd) = false) fs ->
  fs_under fs p = false.
Proof.
  induction fs as [|[q d] fs IH]; intros p H; [reflexivity|].
  inversion H as [|? ? Hq Hr]; subst. cbn [fs_under].
  cbn [fst] in Hq. rewrite Hq. now apply IH.
Qed.

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

(** THE ONE PATHNAME SHAPE UNDER /tmp THE MODEL ANSWERS FOR: an
    ABSOLUTE path "/tmp/<name>" with exactly one further component.
    [Some name] is the component; [None] is every other spelling, and
    every other spelling is declined the way the separator gate declines
    today.

    WHAT IS REJECTED, and why each is rejected rather than answered:

    - a path that does not begin "/tmp/" at all — including a bare
      "/tmp", "/tmp/" with nothing after it, and "/tmpfoo": the run's
      declaration says nothing about them;
    - a name with a further separator in it ("a/b"): that is a second
      component, so the answer would come from a directory the flat map
      cannot hold.  The declaration may still MENTION such a name, and
      then some key lives under "/tmp/a" and the arms see it through
      [fs_under] — which is why they test it;
    - "." and "..", which name /tmp and its parent rather than a file in
      it.  [Open.path_is_dirref]'s arms answer those for a RELATIVE
      path off the working directory; under an absolute prefix they
      would be answers about directories as state, which this arm
      does not model.

    A NAME WITH A NUL IN IT CANNOT ARRIVE HERE: every pathname the specs
    see comes out of [Uaccess.read_cstr], which stops at the first NUL.
    So this predicate says nothing about NUL, and the seeding
    ([State.fs_seed_tmp]) drops the declared entries no program could
    name.

    The premise the arms rest on is [State.in_tmp]'s. *)
Definition tmp_name (p : path) : option path :=
  match path_strip_prefix tmp_prefix p with
  | None => None
  | Some n =>
      if path_eqb n [] then None
      else if path_has_slash n then None
      else if path_eqb n dot_path then None
      else if path_eqb n dotdot_path then None
      else Some n
  end.

(** The gate and the seeding agree on the key: a path this answers for
    is exactly the key [State.fs_seed_tmp] would have put its component
    under.  That is what makes "the name the program used" and "the key
    the run holds" the same thing. *)
Lemma tmp_name_key : forall p n, tmp_name p = Some n -> p = tmp_key n.
Proof.
  intros p n H. unfold tmp_name in H.
  destruct (path_strip_prefix tmp_prefix p) as [n'|] eqn:Hs; [|discriminate].
  apply path_strip_prefix_app in Hs.
  destruct (path_eqb n' []); [discriminate|].
  destruct (path_has_slash n'); [discriminate|].
  destruct (path_eqb n' dot_path); [discriminate|].
  destruct (path_eqb n' dotdot_path); [discriminate|].
  inversion H; subst n'. exact Hs.
Qed.

(** Is [p] the path of an open file fd?  A file fd records the PATH it
    was opened on ([FdFile]/[FdFileW]), not an inode, so the model cannot
    represent Linux's unlinked-but-still-open file — see [unlinkat_spec].

    THE NON-FILE ENTRIES ARE ENUMERATED rather than swept up by a
    [| _ :: r =>] catch-all, and the difference is invisible until an
    [FdEntry] constructor is added.  A catch-all here is extensionally
    right today and would still compile after the next constructor while
    silently answering "names no path" for it — the same unsound-accept
    shape [Select.bits_all_pollable] and
    [Net.Socket.sockfd_lookup_errno] enumerate to avoid, and the harder
    one to notice, because the constructors sit INSIDE a cons pattern
    rather than at the head of an arm. Listing them makes the next
    constructor a compile error.

    [FdPipe] answers [false] and that is exact rather than fail-closed:
    a pipe end names no filesystem path at all.  Both ends hang off one
    anonymous inode on the internal [pipe_mnt], and NEITHER is reached
    through path resolution: [create_pipe_files] builds the WRITE end
    with [alloc_file_pseudo(inode, pipe_mnt, "", O_WRONLY | ...)] and
    then the READ end with [alloc_file_clone] of that same file
    (fs/pipe.c, v6.18.46 — two different allocators, which is why this
    says "neither is a path" rather than naming one of them for both).
    So no [unlinkat] argument can ever denote a pipe end, and there is
    nothing for the decision to be derived from beyond that. *)
Fixpoint fd_names_path (fds : list (word * FdEntry)) (p : path) : bool :=
  match fds with
  | [] => false
  | (_, FdFile q _) :: r => path_eqb p q || fd_names_path r p
  | (_, FdFileW q _) :: r => path_eqb p q || fd_names_path r p
  | (_, FdFileA q _) :: r => path_eqb p q || fd_names_path r p
  | (_, FdFileRW q _) :: r => path_eqb p q || fd_names_path r p
  | (_, FdChannel _) :: r => fd_names_path r p
  | (_, FdDir) :: r => fd_names_path r p
  | (_, FdSocket _) :: r => fd_names_path r p
  | (_, FdPipe _ _) :: r => fd_names_path r p
  | (_, FdDevNull _ _) :: r => fd_names_path r p
    (* exact, like the pipe end: /dev/null is not a key of [Fs.Fs] —
       [Open.openat_spec] declines the open when the map holds one —
       so no descriptor of this kind names a path [unlinkat] can reach *)
  | (_, FdUrandom) :: r => fd_names_path r p
    (* the same for /dev/urandom, for the same reason *)
  | (_, FdOpaque _) :: r => fd_names_path r p
    (* exact as well: an opaque descriptor is on a procfs name or an
       anonymous inode, and the names [unlinkat_spec] answers for are a
       slash-free name or a "/tmp/" key, never a "/proc" one *)
  end.

(** unlinkat's injectable failures: environment conditions the model does
    not track, all of them documented for unlink(2) and all reachable on
    a directory entry this model cannot tell apart from an ordinary one
    — kernel memory (ENOMEM, listed first as the canonical witness), the
    parent directory's write and search permission (EACCES, from
    [may_delete]'s [inode_permission]), a sticky, append-only or
    immutable entry (EPERM, from the two clauses just after it), a
    read-only mount (EROFS, from [mnt_want_write], which runs before the
    lookup), and a mount point over the entry (EBUSY, from
    [vfs_unlink]'s [is_local_mountpoint] — the one member that needs
    more than an ordinary entry, since the victim has to be a bind-mount
    target in the caller's namespace)
    (Linux fs/namei.c, [may_delete] / [vfs_unlink], both byte-identical
    v6.10 through v6.16).
    ENOENT is NOT injectable: file existence IS tracked. *)
Definition unlinkat_errnos : list Z := [ENOMEM; EACCES; EPERM; EROFS; EBUSY].

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

(** THE REMOVAL ITSELF, once the key has been found: shared by the
    working-directory arm and the /tmp arm below so that the two
    provably do the same thing to the same key.  [p] is the pathname as
    the program spelled it, which is what [do_unlinkat]'s [slashes:]
    label reads; [c] is the key.

    The AT_REMOVEDIR answer sits here rather than at each caller because
    it is the same answer for both: a model file is never a directory,
    so [may_delete]'s -ENOTDIR is what Linux returns.  The /tmp arm
    never reaches it, having declined AT_REMOVEDIR above. *)
Definition unlink_found_spec (p c : path) (flags : word) (m : Model)
    : Sys SyscallEffect :=
  if unlink_rmdir flags then err_ret ENOTDIR  (* a model file is never a directory *)
  else if path_trailing_slash p then err_ret ENOTDIR  (* do_unlinkat's [slashes:] *)
  else if fd_names_path (m_fds m) c then unmodeled
  else
    alt (e <- errno_from unlinkat_errnos ;; err_ret e)  (* untracked env failure *)
        (set_fs (fs_remove (m_fs m) c) ;; ret_only (Z_to_bv 64 0)).

(** THE /tmp ARM: removing a file the run HOLDS in its own private
    temporary directory ([tmp_name], [State.in_tmp]).  It sits inside
    the separator branch below, tested before that branch declines, the
    way [Open.openat_sep_spec]'s arms sit inside openat's.

    WHAT IT ANSWERS BESIDE THE REMOVAL, FIRST: a name some key lives
    UNDER is -EISDIR.  The declaration may name "a/b", and then "/tmp/a"
    is a DIRECTORY in the run's own /tmp; Linux refuses to unlink a
    directory in [may_delete], which [vfs_unlink] calls before it
    removes anything, and the refusal is unconditional on the
    filesystem — [d_is_dir] on the victim with [isdir] clear is
    -EISDIR.  This is the one answer here that is LINUX-SPECIFIC rather
    than POSIX's: POSIX lets unlink of a directory be -EPERM, and Linux
    chose -EISDIR.  Every supported implementation is a Linux, and
    qemu-user's `unlinkat` is the host kernel's, so the intersection
    design priority 1 (README.md) asks about is -EISDIR on all of them.  The
    -EISDIR is right for a trailing-separator spelling too, by a
    different route: "/tmp/a/" strips to the same [c], and Linux reaches
    [do_unlinkat]'s [slashes:] label, whose [d_is_dir] test answers
    -EISDIR for a directory.  All fs/namei.c, Linux v6.18.46;
    [may_delete]'s test was read again in v6.12.1, where it stands
    unchanged, so the answer does not turn on the version.

    WHY AN ANSWER AND NOT A DECLINE, which is the [Open.openat_create_spec]
    argument moved one syscall over: the answer is deterministic, it
    does not depend on which filesystem /tmp is on, and it leaves the
    model unchanged, so one image drives a source and a target into the
    same branch.  The guard runs BEFORE the lookup, and because it
    answers, the order is load-bearing rather than tidy: an implied
    directory is not a key the run holds, so the -ENOENT below would
    claim the name is absent where Linux says it is a directory.
    [Checks.Cases.Fs.Namei.unlinkat_tmp_implied_directory_precedes_not_held]
    pins exactly that.  What the order also covers is the unrealizable
    image [Fs.valid_fs] admits, where "/tmp/a" and "/tmp/a/b" are both
    keys: no reality has both, and the arm answers the directory rather
    than removing the file.

    WHAT IT ANSWERS BESIDE THE REMOVAL: a key the run does NOT hold is
    -ENOENT.  The arm gives the real
    errno rather than leaving the last call of a run that cleans up after
    itself outside the modeled surface.  Linux reaches the same answer
    through [do_unlinkat]: [filename_parentat] walks to the parent, the
    lookup of the last component finds no entry there, and the NEGATIVE
    dentry that comes back is the -ENOENT the ANSWERS discussion below
    already records (Linux fs/namei.c; through v6.14 the test is
    [do_unlinkat]'s own [d_is_negative] at its [slashes:] label, and
    v6.15 moved it into [lookup_one_qstr_excl] — the same answer either
    way, which is what that note says).

    WHAT MAKES IT TRUE HERE, rather than the flat map's confident guess
    that [unlinkat_root_enoent_rejected] warns about, is the privacy
    premise: the run's /tmp is its OWN, so what the environment declared
    ([State.in_tmp]) plus what [Open.create_wronly] created minus what
    this arm removed is the whole truth about what exists there.
    The premise is the WHOLE of
    what carries this answer, and nothing else in the model corroborates
    it.  One thing that looks as though it might does not:
    [Stat.newfstatat_core_spec] answers -ENOENT for a /tmp name the run
    does not hold, but it reaches that off the FLAT MAP, having no /tmp
    arm, no separator guard and no reading of [State.in_tmp] at all — it
    answers the same way for any absent path, which makes it a
    FALSE REJECTION, and it is the confident wrong answer the WORLD note
    below warns about rather than a second reading of the premise.

    [Open.openat_tmp_spec]'s O_RDONLY of a name not held declines.
    Nothing structural keeps it declined — that branch would answer
    one errno and mint no descriptor, the same shape as the branch here —
    so it could be answered off this same premise.

    WHAT IT DECLINES, each for a reason of its own:

    - AT_REMOVEDIR.  Linux answers -ENOTDIR for a regular file, and for
      a directory -ENOTEMPTY or 0; which one it is depends on /tmp
      holding a DIRECTORY, which this arm does not model.  The arm
      declines the flag rather than answering the one case the
      model could judge, and that is the narrower choice.
    - a component over [Uapi.NAME_MAX].  That -ENAMETOOLONG comes out
      of the FILESYSTEM's own lookup rather than out of fs/namei.c, and
      the model has no filesystem type to ask.  The working-directory
      arm declines it for the same reason, and unlike [Open]'s plain
      arms (see [Open.openat_plain_name]'s note) nothing needs this one
      to answer.

    The name some key lives UNDER is the -EISDIR above.  The
    working-directory arm in [unlinkat_body_spec] declines that shape,
    and the asymmetry is one of SCOPE and nothing deeper: [may_delete] does not care
    which directory the victim is in, so the same derivation would carry
    the plain arm, and moving it there is a change of its own with its
    own examples to re-check.  Where the two arms DO have to agree is
    the key space, and they do — see the NAME_MAX note in
    [Checks.Cases.Fs.Namei.unlinkat_tmp_name_max_boundary].

    THERE IS NO IGNORED-FLAG MASK HERE, and none is wanted: unlike
    [Open.open_ignored_flags], which strips O_CLOEXEC, O_LARGEFILE and
    O_NONBLOCK before every openat arm sees the word, unlinkat's word
    has already been narrowed to exactly 0 or AT_REMOVEDIR by
    [modeled_unlink_flags] in the wrapper, which is the kernel's own
    [SYSCALL_DEFINE3(unlinkat)] test and runs before [getname()].  So
    the only distinction left for this arm to make is the one
    [unlink_rmdir] makes.

    [dirfd] is not tested here, and does not have to be: the caller
    below has already required AT_FDCWD.  Linux would ignore any dirfd
    for a path of this shape — [filename_parentat] hands an absolute
    name to [path_init], which sets [nd->path] from the root and never
    reads [dfd] (fs/namei.c) — so a later real-dirfd arm may drop that
    requirement without changing this arm's answers. *)
Definition unlinkat_tmp_spec (n p c : path) (flags : word) (m : Model)
    : Sys SyscallEffect :=
  if unlink_rmdir flags then unmodeled
  else if Nat.ltb NAME_MAX (length n) then unmodeled
  else if fs_under (m_fs m) c then err_ret EISDIR  (* may_delete's -EISDIR *)
  else
    match fs_lookup (m_fs m) c with
    | None => err_ret ENOENT     (* absent from the run's own /tmp: real -ENOENT *)
    | Some _ => unlink_found_spec p c flags m
    end.

(** [unlinkat dirfd path flags]: remove a directory entry.  This is the
    one modeled syscall that DELETES from the file system, and the final
    file system is observable ([ExitEv] carries it), so the removal is
    real: [Fs.fs_remove].  [Fs.fs_remove_sorted] proves that dropping an
    entry PRESERVES the canonical sorted form the [=] comparison needs —
    a property of the operation alone.  Nothing threads
    [Fs.fs_sorted (m_fs m)] along the model step, so that is not a
    property of the states an execution reaches; [Fs.valid_fs] requires
    it of the initial image and the header assumes the rest.

    ORDER, following the kernel's exactly:

    - the flag word first: anything but 0 or AT_REMOVEDIR is -EINVAL,
      before the pathname is fetched.  [SYSCALL_DEFINE3(unlinkat)] is

        if ((flag & ~AT_REMOVEDIR) != 0)
                return -EINVAL;
        if (flag & AT_REMOVEDIR)
                return do_rmdir(dfd, getname(pathname));
        return do_unlinkat(dfd, getname(pathname));

      so [getname] is an argument expression on the two return paths
      only and the -EINVAL genuinely precedes it (Linux fs/namei.c,
      byte-identical v5.9 through v6.18).  Note AT_EMPTY_PATH and
      AT_SYMLINK_NOFOLLOW are NOT accepted: they are -EINVAL like any
      other bit.
    - then [getname()], with all three of its answers, as [openat_spec]
      has them: -ENAMETOOLONG for no NUL within PATH_MAX, -ENOENT for
      the empty string, and -EFAULT for an unmapped byte — the last
      propagated out of [strncpy_from_user] rather than written in
      [getname_flags] itself (Linux fs/namei.c, [getname_flags]; the
      answers are unchanged v6.10 through v6.16, though the body is not
      byte-stable across it);
    - only then the dirfd, resolved in [path_init]: the relative-to-a-
      dirfd modes are not modeled, so any dirfd but AT_FDCWD is
      [unmodeled] — the same treatment [openat_spec] and
      [readlinkat_spec] give it.

    For an UNREADABLE pathname too: an illegal flag word with a NULL or
    unmapped path is -EINVAL, the pathname never fetched.

    THE ANSWERS, once the path is in hand.  What the kernel does first is
    TYPE the last component, in [link_path_walk], and three of the four
    types it can produce are settled without consulting any file system.
    So they are exact constants here (Linux fs/namei.c v6.18.46,
    [do_unlinkat] / [do_rmdir], both byte-identical v6.10 through v6.14;
    in v6.15 both changed for one reason, the negative-dentry -ENOENT
    moving into [lookup_one_qstr_excl], which changes no answer this spec
    gives):

      | last component | type        | flags = 0 | AT_REMOVEDIR |
      | "."            | LAST_DOT    | -EISDIR   | -EINVAL      |
      | ".."           | LAST_DOTDOT | -EISDIR   | -ENOTEMPTY   |
      | none at all    | LAST_ROOT   | -EISDIR   | -EBUSY       |

    -EISDIR on all three comes from [do_unlinkat]'s [type != LAST_NORM]
    test, which does not distinguish them; [do_rmdir] switches on the
    type and does, and its [case LAST_ROOT] is the -EBUSY.

    LAST_ROOT is "the path had no component" — a path that is nothing but
    separators, so "/" and "//" and "///" alike.  [link_path_walk] sets
    [nd->last_type = LAST_ROOT] before it looks at anything, skips the
    leading separators, and returns 0 the moment the string ends there,
    so it never enters the component loop.  That is what separates this
    arm from the "." and ".." ones, which look identical from the
    outside: the loop calls [may_lookup] before it types anything, so
    those two rest on the caller being able to search its own working
    directory and this one does not.  It is not unconditional: the
    APPROXIMATION note below has the condition each type is behind.

    TRAILING SEPARATORS do not change which component is last, and do not
    change its type; [path_strip_trailing_slashes] carries that argument.
    What they change is one byte: [do_unlinkat] tests [last.name[last.len]], the
    byte just past the component, and jumps to its [slashes:] label when
    that byte is not NUL.

    The two -ENOTDIRs an ordinary name can draw are DIFFERENT kernel
    answers reached down different
    paths, which is why they are separate arms below rather than one.
    The AT_REMOVEDIR one is [may_delete(..., isdir = 1)]'s
    [!d_is_dir(victim)], reached through [vfs_rmdir]; a model file is
    always a regular file, so rmdir of one never succeeds.  The
    trailing-separator one is [do_unlinkat]'s [slashes:] label, which
    [vfs_unlink] never gets near:

        if (last.name[last.len])
                goto slashes;
        ...
    slashes:
        if (d_is_dir(dentry))
                error = -EISDIR;
        else
                error = -ENOTDIR;

    The -ENOENT column is one answer for a different reason again: an
    absent name never reaches [slashes:] at all, because
    [lookup_one_qstr_excl] returns [ERR_PTR(-ENOENT)] for a negative
    dentry when the caller passed no LOOKUP_CREATE, and neither
    [do_unlinkat] nor [do_rmdir] does (Linux fs/namei.c v6.18.46,
    [lookup_one_qstr_excl], the [d_is_negative(dentry) && !(flags &
    LOOKUP_CREATE)] test).  That is why the trailing separator is tested
    only on the arm where the lookup FOUND something.

    NONE OF THIS TRANSFERS TO A PATH LOOKUP, and the reason is worth
    stating here because the byte is the same one.  [openat] and
    [newfstatat] reach the last component through [path_lookupat], which
    calls [lookup_last]:

        static inline const char *lookup_last(struct nameidata *nd)
        {
            if (nd->last_type == LAST_NORM && nd->last.name[nd->last.len])
                    nd->flags |= LOOKUP_FOLLOW | LOOKUP_DIRECTORY;
            return walk_component(nd, WALK_TRAILING);
        }

    [lookup_last] is called from [path_lookupat] and from nowhere else;
    [path_parentat], which is what [filename_parentat] and therefore both
    unlink callers use, stops at the parent and never invokes it (Linux
    fs/namei.c v6.18.46, [lookup_last] and its one caller).  So the very
    byte that sends [do_unlinkat] to [slashes:] makes a LOOKUP follow
    symlinks and demand a directory: "sym/" is -ENOTDIR to unlink
    whatever the link points at, because [slashes:] tests the dentry's
    own type, and is the link's TARGET to open.  A spec for a lookup must
    therefore not reuse the reasoning above, and must not reuse
    [path_strip_trailing_slashes] on the strength of it.

    THE WORLD this is exact in, and the three guards that keep the spec
    inside it.  The model's file system is a flat map from uninterpreted
    paths to bytes: there is no directory structure, and the only paths
    answered as directories without a lookup are the ones the path walk
    types — ".", "..", and the all-separator LAST_ROOT.  Reality is a
    tree.  The two
    agree exactly when every model key is a regular file directly in the
    working directory AND the working directory holds nothing but those
    keys — the first half is the correspondence [openat_spec] already
    depends on.  The
    SECOND half is the one no guard below can restore, because an EMPTY
    real directory has no key at all: [fs_under] sees nothing under it
    and [fs_lookup] misses, so unlinking it is -EISDIR on Linux and
    -ENOENT here, and an AT_REMOVEDIR of it really succeeds there.
    Trailing separators put MORE inputs behind that precondition without
    changing the precondition itself: "D/" reaches these arms rather
    than the separator decline, so a program that names an
    empty real directory with a trailing separator gets the same
    wrong -ENOENT that naming it plainly gets, instead of an
    honest [unmodeled].  That is a real cost of answering trailing
    separators, it is the reason those arms stop where they do, and
    it is a divergence kept rather than fixed.  No
    modeled syscall creates a directory — and it cannot, in the order that
    matters: [Fs] maps a path to a byte list, so there is no value a
    created directory could BE, which is why mkdirat is declined and why
    a mkdir cannot land before the representation changes.  What keeps
    this unreached is therefore an ENVIRONMENT precondition and not
    that fact: the run must not start with an empty real directory in
    the working directory.  Where the model
    would otherwise answer with confidence and be wrong, it declines:

    - a path with a "/" ANYWHERE BUT AT THE END is [unmodeled], once the
      trailing ones are stripped and something is left — leading
      separators included, so an absolute path WITH A COMPONENT is
      declined here.  ("/" and "//" strip to nothing and are the
      LAST_ROOT arm above, not this one.)  The bound is exactly
      "the last component's parent is the working directory": the model
      can type a last component and look it up in the map, and that is
      the whole of what it can do.  A path with a separator anywhere but
      at the end needs the kernel's walk, which resolves every component
      against a tree the flat map does not have — an intermediate name
      that is a regular file is -ENOTDIR, and a last component of "." or
      ".." is typed only after the parent walk succeeds.  An ABSOLUTE
      path is out of reach for a second reason on top of that one:
      nothing in the model records the working directory's own path, so
      "/tmp/x" and "x" cannot be related even when they name one file.
      None of this is a function of the flat map, and the flat map's own
      answer — "that key is absent, -ENOENT" — is the confident wrong
      one.  This is the same gap [Stat.newfstatat_spec] has on the
      stat side, where it is a false REJECTION rather than a decline.

      WHAT CLOSING IT WOULD COST, since "give [Fs] a directory structure"
      is three different jobs with three different prices, and only the
      cheapest is a reinterpretation of what the map already holds:

      - A relative walk that stays WITHIN the working directory's subtree
        is derivable from the existing keys and needs no new state.
        Which non-empty directories exist is already determined —
        [fs_under] is that predicate — so a component walk over it would
        answer "a/b", and the -ENOTDIR of a non-final regular file,
        without [Fs] changing type and so without re-opening any example
        proof.  A ".." that pops ABOVE the working directory is not
        derivable, and for a stronger reason than the next bullet's: not
        only is there no cwd path to resolve it against, [Fs] holds no
        keys outside the working directory at all, so there is nothing
        for the walk to land on.
      - An ABSOLUTE path is not derivable at any price.  It needs the
        working directory's own path, which nothing in the model records.
        Storing one is not the hard part — a cwd is a [Fs.path] like any
        other — the hard part is that the launching directory is chosen
        by the ENVIRONMENT, which makes it a parameter of
        [Equivalence.strong_universal_T] rather than a private field, and
        whoever adds one owes that theorem an accounting.
      - An EMPTY directory is not derivable either, and it is the one
        that cannot be fixed by adding a walk: it leaves NO key in the
        map, so nothing distinguishes it from an absent name.  That is
        why AT_REMOVEDIR can never correctly succeed here, and why
        closing it means directories become state in their own right —
        state a successful rmdir MUTATES, which [ExitEv] would then have
        to carry or the equivalence would quietly coarsen.

      No widening of this spec substitutes for any of the three.

      THE THREE DO NOT COMPOSE.  A program that unlinks the temporary
      file it writes names it absolutely, under a directory the working directory does
      not contain — and that shape is closed by none of the three in
      sequence.  The first answers a name inside the working directory's
      subtree and this name is not one; the second relates an absolute
      name to the working directory and this name's parent is a
      different directory entirely; so the map holds no key for it with
      both paid, and only the third — directories as state in their own
      right — reaches it.  This is a decline reached on every input of
      such a binary, so its [Equivalence.strong_equiv] statement
      is FALSE rather than narrowed, per the [modeled]-in-the-conclusion
      note above.  Widening THIS spec would not by itself make such a
      binary modeled either, while [Open.openat_spec] carries the same
      guard: the create that precedes the unlink leaves the modeled
      surface first on every input that reaches it.
      Checks/Cases/Fs/Namei.v checks that the guard runs ahead of the
      lookup, and that the name the walk would end at is answered rather
      than declined.
    - a name longer than [Uapi.NAME_MAX] is [unmodeled].  [getname()]'s
      PATH_MAX bound lets a 4095-byte single component through, and the
      FILESYSTEM then answers -ENAMETOOLONG; the model has no filesystem
      type to ask.
    - a name some key lives UNDER ([fs_under]) is [unmodeled].  A key
      "a/b" means reality has a DIRECTORY "a", which the map cannot hold;
      unlinking "a" is -EISDIR there and -ENOENT here.  The guard runs
      before the lookup, so it also covers the unrealizable images
      [Fs.valid_fs] admits, where "a" and "a/b" are both keys.

    THE OPEN-FD GUARD.  Linux keeps an unlinked file's contents reachable
    through an fd already open on it until the last close.  The model's
    file fds record a PATH ([FdFile]/[FdFileW]), not an inode, so after a
    removal they would name nothing — and the read, write, readv and
    writev specs all rest on "an [FdFile] always points into the fs".
    Rather than weaken that invariant in four places, unlinking a path
    some fd still names is [unmodeled] here.  Closing the fd first, which
    is what a program that publishes a file atomically does, stays inside
    the model.

    APPROXIMATION, the same one [openat_spec] carries, in two forms.

    First, and on EVERY deterministic arm: they are deterministic, so
    they exclude [getname_flags]'s own -ENOMEM, which it returns from
    [__getname] before it copies a byte and which is therefore a real
    answer to the empty path, to ".", to "..", to an unreadable pointer
    and to an over-long one.  That is the same shape as [openat_spec]'s
    pre-resolution -EMFILE.

    Second, three untracked conditions sit ahead of these arms, and which
    one reaches which arm follows the last component's TYPE rather than
    the answer:

    - [may_lookup]'s -EACCES: [link_path_walk] calls it at the TOP of the
      component loop, before it hashes anything, so it precedes any arm
      whose path HAS a component.
    - [complete_walk]'s -ESTALE, on a file system defining
      [d_weak_revalidate]: [path_parentat] runs it after the walk, and it
      returns 0 at once unless ND_JUMPED is still set.  [path_init] sets
      that flag, and on this route the LAST_NORM arm of
      [link_path_walk]'s switch is the only thing that clears it
      ([path_lookupat]'s LOOKUP_MOUNTPOINT block also clears it, but
      [filename_parentat] never passes LOOKUP_MOUNTPOINT, so that block
      is not on this route).
    - [mnt_want_write]'s -EROFS, which both [do_unlinkat] and [do_rmdir]
      raise after the type test and before the lookup.

      | arm                    | -EACCES | -ESTALE | -EROFS |
      | LAST_ROOT              | no      | yes     | no     |
      | LAST_DOT, LAST_DOTDOT  | yes     | yes     | no     |
      | LAST_NORM              | yes     | no      | yes    |

    The -ESTALE column runs OPPOSITE to the other two, which is what
    makes it easy to get backwards: the arms that consult no file system
    are the ones still carrying ND_JUMPED, and the LAST_NORM arms that do
    consult one are the arms that cleared it.

    Past those, the arms differ in what ELSE they preempt, because they
    sit at different depths.  The AT_REMOVEDIR -ENOTDIR comes out of
    [may_delete], so it also preempts the -EACCES and -EPERM that
    function reaches first.  The trailing-separator -ENOTDIR does not:
    [do_unlinkat] jumps to [slashes:] from ABOVE [vfs_unlink], so
    [may_delete] never runs on that path.  What does precede it is
    [lookup_one_qstr_excl].  That answers -ENOENT for a working directory
    already removed ([IS_DEADDIR]), and -ENOMEM when it cannot allocate
    the dentry.
    Each of these arms admits one answer and no [unlinkat_errnos]
    alternative, which narrows the spec rather than widening it.

    So LAST_ROOT escapes the first and the third, and is behind
    [complete_walk] alone.  "The answer to \"/\" is unconditional" would
    still be too strong; what is true is that it is the one arm here
    whose answer does not rest on the caller being able to search its own
    working directory. *)
Definition unlinkat_body_spec (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
    match read_cstr (in_mem i) pathp with
    | CstrTooLong => err_ret ENAMETOOLONG        (* no NUL within PATH_MAX *)
    | CstrFault => err_ret EFAULT                (* unmapped byte in the path string *)
    | CstrOk p =>
        if path_eqb p [] then err_ret ENOENT     (* empty pathname: getname's own -ENOENT *)
        else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
        else
          let c := path_strip_trailing_slashes p in
          if path_eqb c [] then                  (* nothing but separators: LAST_ROOT *)
            (if unlink_rmdir flags then err_ret EBUSY else err_ret EISDIR)
          else if path_has_slash c then
            (match tmp_name c with
             | Some n => unlinkat_tmp_spec n p c flags m
             | None => unmodeled  (* a separator not at the end: see WORLD above *)
             end)
          else if path_eqb c dot_path then
            (if unlink_rmdir flags then err_ret EINVAL else err_ret EISDIR)
          else if path_eqb c dotdot_path then
            (if unlink_rmdir flags then err_ret ENOTEMPTY else err_ret EISDIR)
          else if Nat.ltb NAME_MAX (length c) then unmodeled  (* the filesystem's own -ENAMETOOLONG *)
          else if fs_under (m_fs m) c then unmodeled (* c names an implied directory *)
          else
          match fs_lookup (m_fs m) c with
          | None => err_ret ENOENT               (* absent: real -ENOENT, not a modeling gap *)
          | Some _ => unlink_found_spec p c flags m
          end
    end.

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
    faulting byte, or PATH_MAX, as for openat. *)
Definition unlinkat_spec (dirfd pathp flags : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (modeled_unlink_flags flags) then err_ret EINVAL
  else
    record_copyins [(pathp, cstr_access_len_aux (in_mem i) pathp path_max)]
      (unlinkat_body_spec dirfd pathp flags i m).
