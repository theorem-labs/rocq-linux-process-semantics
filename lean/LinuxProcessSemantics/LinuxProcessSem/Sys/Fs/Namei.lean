import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: 6ab7557a684ee74d4862dd515a2f4bac1aa205fe -/

/-! # LinuxProcessSem.Sys.Fs.Namei — unlinkat (35)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Namei.v`, which answers to Linux
`fs/namei.c`: it holds what the kernel defines there, and nothing else.
"." is the one path constant more than one syscall file needs, so it is
`Uapi.dot_path` and is read from there; ".." is this file's, because
`do_unlinkat` and `do_rmdir` answer the two differently (fs/namei.c,
Linux v6.18.46, commit 1f99e9ab748f — every line number in this file
was read there and is labelled so).

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/Namei.lean`.  `Run.valid_argv` reads `path_has_slash`
and `dotdot_path` from here as well, which is why the two predate the
rest of the port.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 — and point at the Rocq definition for the
argument in full, so there is one place to correct it.  Rocq cites most of
these functions over a v6.10-v6.16 window with no line numbers.

Spellings that differ from Rocq without changing a value: Rocq's `Z.eqb`
on `bv_unsigned` is Lean's decidable `=` on `Int`, `Nat.ltb` is `<` on
`Nat`, `negb (Nat.eqb a b)` is `a != b`, `existsb` is `List.any`, and
`rev` is `List.reverse`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- ".." — the parent directory.  Like ".", it is a path the kernel
answers without consulting any file system: `link_path_walk` types the
last component from the word `hash_name` returns, `LAST_DOTDOT` at
fs/namei.c:2475-2478 and `LAST_DOT` at :2480-2482 (Linux v6.18.46), and
both `do_unlinkat` (:4720-4722) and `do_rmdir` (:4583-4592) branch on that
type before they look anything up.  Their answers differ — `do_rmdir`
gives ".." -ENOTEMPTY and "." -EINVAL — which is why the two paths are
separate constants rather than one "directory reference" class.  Rocq:
`Namei.dotdot_path`. -/
def dotdot_path : path := [Z_to_bv 8 46, Z_to_bv 8 46]

/-- The component separator `link_path_walk` splits on: the byte it skips
ahead of the first component (fs/namei.c:2450-2454, Linux v6.18.46) and
between components (:2502-2504). -/
def slash_byte : byte := Z_to_bv 8 47

/-- Does the path contain a component separator? -/
def path_has_slash (p : path) : Bool :=
  p.any (fun b => bv_eqb b slash_byte)

/-- Used on a REVERSED path, which is what makes it strip trailing
separators; nothing else calls it.  Rocq: `Namei.drop_leading_slashes`. -/
def drop_leading_slashes (p : path) : path :=
  match p with
  | [] => []
  | b :: r => if bv_eqb b slash_byte then drop_leading_slashes r else b :: r

/-- Drop the separators a path ENDS with.  `link_path_walk` hashes a
component, stops if the string ends there (`if (!*name) goto OK;`,
fs/namei.c:2496-2497, Linux v6.18.46), otherwise skips every following
"/" and stops if the string ends after them (:2502-2505), so trailing
separators never start a component and never change which component is
the last one.  What they DO change is the byte `do_unlinkat` tests as
`last.name[last.len]`: see `path_trailing_slash`.  Rocq:
`Namei.path_strip_trailing_slashes`. -/
def path_strip_trailing_slashes (p : path) : path :=
  (drop_leading_slashes p.reverse).reverse

/-- Is the last component followed by a separator?  This is the kernel's
own `last.name[last.len]` (`do_unlinkat`, fs/namei.c:4734-4735, Linux
v6.18.46) — the byte just past the component, which is "/" exactly when
the path had trailing separators and NUL otherwise. -/
def path_trailing_slash (p : path) : Bool :=
  (path_strip_trailing_slashes p).length != p.length

/-- `p` is a DIRECTORY COMPONENT of `q`: `q` is `p` followed by "/" and
then anything.  The base case is "`p` fully consumed", so the caller must
not pass the empty path — a stripped path of nothing is the LAST_ROOT arm,
answered before this is reached.  Rocq: `Namei.dir_prefixb`. -/
def dir_prefixb (p q : path) : Bool :=
  match p, q with
  | [], [] => false
  | [], c :: _ => bv_eqb c slash_byte
  | _ :: _, [] => false
  | a :: p', b :: q' => bv_eqb a b && dir_prefixb p' q'

/-- Does any file in `fs` live UNDER `p`?  If one does then `p` names a
directory — a thing the flat map only implies and cannot hold.  Rocq:
`Namei.fs_under`. -/
def fs_under (fs : Fs) (p : path) : Bool :=
  match fs with
  | [] => false
  | (q, _) :: r => dir_prefixb p q || fs_under r p

/-- Strip a fixed prefix off a path, or say it is not there.  Rocq:
`Namei.path_strip_prefix`. -/
def path_strip_prefix (pre p : path) : Option path :=
  match pre, p with
  | [], _ => some p
  | _ :: _, [] => none
  | a :: pre', b :: p' => if bv_eqb a b then path_strip_prefix pre' p' else none

/-- Twin of Rocq's `Namei.path_strip_prefix_app`: a stripped path is the
prefix followed by what is left. -/
theorem path_strip_prefix_app (pre : path) :
    ∀ p n, path_strip_prefix pre p = some n → p = pre ++ n := by
  induction pre with
  | nil =>
    intro p n h
    simp only [path_strip_prefix, Option.some.injEq] at h
    rw [h]; rfl
  | cons a pre ih =>
    intro p n h
    cases p with
    | nil => simp only [path_strip_prefix] at h; cases h
    | cons b p =>
      simp only [path_strip_prefix] at h
      cases hab : bv_eqb a b with
      | false => simp only [hab, Bool.false_eq_true, ↓reduceIte] at h; cases h
      | true =>
        simp only [hab, ↓reduceIte] at h
        rw [(bv_eqb_eq a b).1 hab, ih p n h]; rfl

/-- The first component of a path: the bytes before its first separator,
all of it when there is none.  Rocq: `Namei.path_first_component`. -/
def path_first_component (p : path) : path :=
  match p with
  | [] => []
  | b :: r => if bv_eqb b slash_byte then [] else b :: path_first_component r

/-- Drop the leading components of a path that leave the walk where it is:
the empty ones a run of separators makes, and ".".  "./b", "//b" and
".//./b" all become "b"; "." and "./" become nothing.  `link_path_walk`
skips every separator between components (fs/namei.c:2502-2504, Linux
v6.18.46), and a "." component is `LAST_DOT` (:2480-2482), which
`walk_component` hands to `handle_dots`, and that moves nowhere.  ".." and
a name that only starts with a dot (".b") are left in place.  Rocq:
`Namei.path_skip_noop_components`. -/
def path_skip_noop_components (p : path) : path :=
  match p with
  | [] => []
  | b :: r =>
    if bv_eqb b slash_byte then path_skip_noop_components r
    else if bv_eqb b (Z_to_bv 8 46) then
      match r with
      | [] => []
      | b' :: r' => if bv_eqb b' slash_byte then path_skip_noop_components r' else p
    else p

/-- Does a key of `fs` show an ENTRY inside the directory `c`: a key spelled
`c ++ "/" ++ …` whose first component that moves the walk
(`path_skip_noop_components`) is a name, not "..", and is there at all?
`fs_under` says only that `c` is a directory; this says it is not empty,
which a key "a/b" does (the walk finds "b" inside "a", `link_path_walk`,
fs/namei.c:2441-2537, Linux v6.18.46), and so do "a/./b" and "a//b".  A
key "a/../b" does not (the walk passes through "a" and back out, and an
empty "a" resolves it too), nor do "a/" and "a/.", which name "a" itself.
Rocq: `Namei.fs_entry_under`. -/
def fs_entry_under (fs : Fs) (c : path) : Bool :=
  match fs with
  | [] => false
  | (q, _) :: r =>
    match path_strip_prefix (c ++ [slash_byte]) q with
    | some rest =>
      let n := path_first_component (path_skip_noop_components rest)
      (!(path_eqb n []) && !(path_eqb n dotdot_path))
      || fs_entry_under r c
    | none => fs_entry_under r c

/-- The image once an implied directory `c` that shows no entry
(`fs_entry_under` is false) has been removed: rmdir's 0 in
`rmdir_implied_spec`.  A key that names `c` itself ("c/", "c/.", "c/./")
goes with it; a key that leaves `c` again by ".." ("c/../x", "c/./..//x")
becomes the path after the "..", here "x", the file the walk reaches
without `c`, with its contents; a ".." naming the working directory itself
("c/..", "c/../") goes too.  Every other key stays.  The result is rebuilt
with `fs_set`, so it is in the canonical form whatever it is built from
(Rocq's `Namei.fs_rmdir_implied_sorted`, which waits on the `fs_set_sorted`
port `Fs.lean`'s header names); where a renamed key meets one the image
already holds, the key earlier in the image wins.  Rocq:
`Namei.fs_rmdir_implied`. -/
def fs_rmdir_implied (fs : Fs) (c : path) : Fs :=
  match fs with
  | [] => []
  | (q, d) :: r =>
    let r' := fs_rmdir_implied r c
    match path_strip_prefix (c ++ [slash_byte]) q with
    | none => fs_set r' q d
    | some rest =>
      match path_strip_prefix (dotdot_path ++ [slash_byte]) (path_skip_noop_components rest) with
      | some x =>
        let x' := path_skip_noop_components x
        if path_eqb x' [] then r' else fs_set r' x' d
      | none => r'

/-- THE ONE PATHNAME SHAPE UNDER /tmp THE MODEL ANSWERS FOR: an ABSOLUTE
path "/tmp/<name>" with exactly one further component.  `some name` is
the component; `none` is every other spelling, and every other spelling
is declined the way the separator gate declines it.

What the kernel does with such a path, and why the shape is the one the
model can follow: `path_init` starts an absolute pathname at the root
(fs/namei.c:2582-2587, Linux v6.18.46), through `nd_jump_root`, which sets
`nd->path = nd->root` (:1042, :1050) without reading `nd->dfd`; then
`link_path_walk` walks "tmp" as a non-final component
(`walk_component(nd, WALK_MORE)`, :2517-2519) and types the last one as
it types a relative name (:2472-2486).  So "/tmp/<name>" reaches
`do_unlinkat` with the same `last` a relative "<name>" would, in a parent
that is the directory /tmp rather than the working directory — and the
flat map can answer for that parent only under the premise that the run's
own table is the whole truth about it (`State.in_tmp`, seeded under
absolute keys by `State.fs_seed_tmp`; bugs/tmp-assumed-private-directory.md).

REJECTED, each for the reason Rocq's `Namei.tmp_name` gives: a path that
does not begin "/tmp/" (a bare "/tmp", "/tmp/" with nothing after it,
"/tmpfoo"), because the declaration says nothing about them; a name with a
further separator ("a/b"), a second component whose answer would come
from a directory the flat map cannot hold — the declaration may still
mention such a name, and then some key lives under "/tmp/a", which the
arms see through `fs_under`; and "." and "..", which name /tmp and its
parent rather than a file in it.  A name with a NUL cannot arrive here:
every pathname comes out of `read_cstr`, which stops at the first NUL, and
the seeding drops the declared entries no program could name.  Issue
#562, rung 4 of #696. -/
def tmp_name (p : path) : Option path :=
  match path_strip_prefix tmp_prefix p with
  | none => none
  | some n =>
    if path_eqb n [] then none
    else if path_has_slash n then none
    else if path_eqb n dot_path then none
    else if path_eqb n dotdot_path then none
    else some n

/-- Twin of Rocq's `Namei.tmp_name_key`: the gate and the seeding agree on
the key — a path this answers for is exactly the key `State.fs_seed_tmp`
would have put its component under, so "the name the program used" and
"the key the run holds" are one thing. -/
theorem tmp_name_key (p n : path) : tmp_name p = some n → p = tmp_key n := by
  intro h
  unfold tmp_name at h
  cases hs : path_strip_prefix tmp_prefix p with
  | none => simp only [hs] at h; cases h
  | some n' =>
    simp only [hs] at h
    have hp : p = tmp_prefix ++ n' := path_strip_prefix_app tmp_prefix p n' hs
    cases h1 : path_eqb n' [] with
    | true => simp only [h1, ↓reduceIte] at h; cases h
    | false =>
    cases h2 : path_has_slash n' with
    | true => simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | false =>
    cases h3 : path_eqb n' dot_path with
    | true => simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | false =>
    cases h4 : path_eqb n' dotdot_path with
    | true => simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | false =>
      simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      rw [hp, h]; rfl

/-- Is `p` the path of an open file fd?  A file fd records the PATH it was
opened on, not an inode, so the model cannot
represent Linux's unlinked-but-still-open file — see `unlinkat_spec`.

THE NON-FILE ENTRIES ARE ENUMERATED rather than swept up by a catch-all,
for the reason Rocq's `Namei.fd_names_path` gives: a catch-all is right
today and stays green through the next constructor while silently
answering "names no path" for it.  Listing them makes the next
constructor a compile error.

`FdPipe` answers `false` and that is exact rather than fail-closed: a pipe
end names no filesystem path at all.  Both ends hang off one anonymous
inode on the internal `pipe_mnt`, and NEITHER is reached through path
resolution: `create_pipe_files` (fs/pipe.c:926, Linux v6.18.46) builds the
WRITE end with `alloc_file_pseudo(inode, pipe_mnt, "", O_WRONLY | …)`
(:944-946) and then the READ end with `alloc_file_clone` of that same file
(:956-957) — two different allocators, which is why this says "neither is
a path" rather than naming one of them for both.  `FdDevNull` and
`FdUrandom` are exact for the reason Rocq gives at those arms: neither
/dev/null nor /dev/urandom is a key of `Fs.Fs` — `Open.openat_spec`
declines the open when the map holds one — so no descriptor of either
kind names a path `unlinkat` can reach. -/
def fd_names_path (fds : List (word × FdEntry)) (p : path) : Bool :=
  match fds with
  | [] => false
  | (_, .FdFile q _) :: r => path_eqb p q || fd_names_path r p
  | (_, .FdFileW q _) :: r => path_eqb p q || fd_names_path r p
  | (_, .FdFileA q _) :: r => path_eqb p q || fd_names_path r p
  | (_, .FdFileRW q _) :: r => path_eqb p q || fd_names_path r p
  | (_, .FdChannel _) :: r => fd_names_path r p
  | (_, .FdDir) :: r => fd_names_path r p
  | (_, .FdSocket _) :: r => fd_names_path r p
  | (_, .FdPipe _ _) :: r => fd_names_path r p
  | (_, .FdDevNull _ _) :: r => fd_names_path r p
  | (_, .FdUrandom) :: r => fd_names_path r p

/-- unlinkat's injectable failures: environment conditions the model does
not track, all reachable on a directory entry this model cannot tell
apart from an ordinary one (Linux v6.18.46).  Kernel memory: ENOMEM, from
`getname_flags` (fs/namei.c:146-148) and `lookup_one_qstr_excl`'s
`d_alloc` (:1701-1703), listed first as the canonical witness.  The parent
directory's write and search permission: EACCES, from `may_delete`'s
`inode_permission(idmap, dir, MAY_WRITE | MAY_EXEC)` (:3274-3276), which
`generic_permission` answers (:485, the directory branch).  An append-only
parent, or a sticky, append-only, immutable or swap-file entry: EPERM, from
`may_delete`'s two clauses just after it (:3277-3278, :3280-3283).  A read-only mount: EROFS, from `mnt_want_write`
(fs/namespace.c:495-504, Linux v6.18.46), whose `mnt_get_write_access` answers it
(:476-478), and which `do_unlinkat` calls before the lookup
(fs/namei.c:4724-4726, Linux v6.18.46).  A mount point over the entry: EBUSY, from
`vfs_unlink`'s `is_local_mountpoint` (:4669-4670) — the one member that
needs more than an ordinary entry, since the victim has to be a bind-mount
target in the caller's namespace.  ENOENT is NOT injectable: file
existence IS tracked.  Rocq: `Namei.unlinkat_errnos`. -/
def unlinkat_errnos : List Int := [ENOMEM, EACCES, EPERM, EROFS, EBUSY]

/-- The flag words `unlinkat_spec` interprets: 0 and AT_REMOVEDIR, which
is every word the kernel accepts — `SYSCALL_DEFINE3(unlinkat, …)` answers
-EINVAL to `(flag & ~AT_REMOVEDIR) != 0` (fs/namei.c:4777-4778, Linux
v6.18.46).  Unlike Rocq's `Open.modeled_open_flags` this is not a modeling choice: a
word outside it is the kernel's own -EINVAL, not `unmodeled`.  Rocq:
`Namei.modeled_unlink_flags`. -/
def modeled_unlink_flags (flags : word) : Bool :=
  decide (bv_unsigned (flag32 flags) = 0)
  || decide (bv_unsigned (flag32 flags) = AT_REMOVEDIR)

/-- Which of the two calls this is: `do_rmdir` on `flag & AT_REMOVEDIR`
(fs/namei.c:4780-4781, Linux v6.18.46), `do_unlinkat` otherwise (:4782).
Rocq: `Namei.unlink_rmdir`. -/
def unlink_rmdir (flags : word) : Bool :=
  decide (bv_unsigned (flag32 flags) = AT_REMOVEDIR)

/-- THE REMOVAL ITSELF, once the key has been found: shared by the
working-directory arm and the /tmp arm so that the two provably do the
same thing to the same key.  `p` is the pathname as the program spelled
it, which is what `do_unlinkat`'s `slashes:` label reads; `c` is the key.

The AT_REMOVEDIR answer sits here rather than at each caller because it
is the same answer for both: a model file is never a directory, so
`may_delete(…, isdir = 1)`'s -ENOTDIR (fs/namei.c:3284-3286, Linux
v6.18.46), reached through `vfs_rmdir` (:4532), is what Linux returns; the
/tmp arm never reaches it, having declined AT_REMOVEDIR itself.  Then
`do_unlinkat`'s `last.name[last.len]` test (:4734-4735) and its `slashes:`
label (:4767-4772), the open-fd guard, and the removal by `vfs_unlink`
(:4741-4742) under the five failures of `unlinkat_errnos`.  Rocq:
`Namei.unlink_found_spec`. -/
def unlink_found_spec (p c : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if unlink_rmdir flags then err_ret ENOTDIR  -- a model file is never a directory
  else if path_trailing_slash p then err_ret ENOTDIR  -- do_unlinkat's `slashes:`
  else if fd_names_path (m_fds m) c then unmodeled
  else alt (e <- errno_from unlinkat_errnos ;; err_ret e)  -- untracked env failure
           (set_fs (fs_remove (m_fs m) c) ;; ret_only (Z_to_bv 64 0))

/-- Does an open descriptor name a key spelled through the directory `c`?
Those are the keys `fs_rmdir_implied` renames or drops.  Rocq:
`Namei.fd_names_key_under`. -/
def fd_names_key_under (fds : List (word × FdEntry)) (fs : Fs) (c : path) : Bool :=
  fs.any (fun qd => dir_prefixb c qd.1 && fd_names_path fds qd.1)

/-- AT_REMOVEDIR OF AN IMPLIED DIRECTORY `c`.  `do_rmdir` reaches
`vfs_rmdir` (fs/namei.c:4529-4567, Linux v6.18.46), which hands a directory
to the filesystem's `->rmdir`: -ENOTEMPTY for a non-empty one, and the
removal of an empty one.  A key that shows an entry in `c`
(`fs_entry_under`) makes it -ENOTEMPTY.  Keys that show none ("c/../x",
"c/") leave it open, since an empty directory inside `c` leaves no key:
both -ENOTEMPTY and the removal, 0, are admitted, the removal changing the
map the way it changes the tree (`fs_rmdir_implied`), after which nothing
lives under `c` and a second call is -ENOENT.  An open descriptor naming a
key the removal renames or drops would be left naming nothing, the reason
for `unlink_found_spec`'s open-fd guard, so that state declines; every path
with a separator `Open.openat_spec` opens is absolute, so no descriptor a
program opens names one.  Rocq: `Namei.rmdir_implied_spec`. -/
def rmdir_implied_spec (c : path) (m : Model) : Sys SyscallEffect :=
  if fs_entry_under (m_fs m) c then err_ret ENOTEMPTY  -- the filesystem's ->rmdir
  else if fd_names_key_under (m_fds m) (m_fs m) c then unmodeled
  else alt (err_ret ENOTEMPTY)  -- c holds only empty directories, which leave no key
           (set_fs (fs_rmdir_implied (m_fs m) c) ;; ret_only (Z_to_bv 64 0))  -- c was empty

/-- THE /tmp ARM: removing a file the run HOLDS in its own private
temporary directory (`tmp_name`, `State.in_tmp`).  It sits inside the
separator branch of `unlinkat_body_spec`, tested before that branch
declines.  `n` is the component, `p` the pathname as spelled, `c` the key.

What it declines, each for Rocq's reason (`Namei.unlinkat_tmp_spec`):
AT_REMOVEDIR — Linux answers -ENOTDIR for a regular file
(`may_delete`, fs/namei.c:3284-3286, Linux v6.18.46) and, for a directory,
-ENOTEMPTY or 0, and which of the three it is turns on /tmp holding a
DIRECTORY, the thing this rung defers, so the ruling on #562 declines the
flag rather than answering the one case the model could judge; a component
over NAME_MAX, whose -ENAMETOOLONG comes out of the filesystem's own lookup
(`simple_lookup`, fs/libfs.c:71-72, Linux v6.18.46, on tmpfs; `ext4_lookup`,
fs/ext4/namei.c:1768-1769, Linux v6.18.46) rather than out of fs/namei.c.

WHAT IT ANSWERS BESIDE THE REMOVAL, FIRST: a name some key lives UNDER is
-EISDIR.  A declaration naming "a/b" makes "/tmp/a" a DIRECTORY in the
run's own /tmp, and Linux refuses to unlink a directory in `may_delete`
(fs/namei.c:3289-3290, Linux v6.18.46), which `vfs_unlink` calls
(:4658) before it removes anything; the refusal is unconditional on the
filesystem.  The answer is LINUX-SPECIFIC where POSIX allows -EPERM, and
every supported implementation is a Linux.  The trailing-separator
spelling gets the same -EISDIR by another route, `do_unlinkat`'s
`slashes:` label (:4767-4772).  The guard runs BEFORE the lookup, and the
order is load-bearing: an implied directory is not a key the run holds, so
the -ENOENT below would otherwise claim the name is absent.  It also
covers the unrealizable image `Fs.valid_fs` admits, where "/tmp/a" and
"/tmp/a/b" are both keys.

WHAT IT ANSWERS BESIDE THE REMOVAL: a key the run does NOT hold is
-ENOENT, the ruling on #1136.  That is `lookup_one_qstr_excl`'s answer for
a negative dentry (:1713-1716), and what makes it true here rather than the
flat map's guess is the privacy premise — the run's /tmp is its own, so
what `State.in_tmp` declared plus what `Open.create_wronly` created minus
what this arm removed is the whole truth about the directory
(bugs/tmp-assumed-private-directory.md).  The premise is the WHOLE of what
carries this answer; `Stat.newfstatat_core_spec`'s -ENOENT for the same name
is NOT a second reading of it, being the flat map's answer for any absent
path and recorded as a false rejection
(bugs/newfstatat-flat-namespace-false-rejections.md).  `openat`'s /tmp arm
still declines an `O_RDONLY` of a name not held because the ruling did not
reach it, not for any structural reason.  Rocq: `Namei.unlinkat_tmp_spec`
carries the argument in full.

There is no ignored-flag mask here and none is wanted: the flag word has
already been narrowed to exactly 0 or AT_REMOVEDIR by `modeled_unlink_flags`
in the wrapper, the kernel's own `SYSCALL_DEFINE3(unlinkat)` test
(:4777-4778), so the only distinction left is `unlink_rmdir`'s.  The dirfd
is not tested here: the caller has already required AT_FDCWD, and Linux
would ignore any dirfd for a path of this shape (`path_init`, :2582-2587),
so a later real-dirfd arm may drop that requirement without changing this
arm's answers. -/
def unlinkat_tmp_spec (n p c : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if unlink_rmdir flags then unmodeled
  else if NAME_MAX < n.length then unmodeled
  else if fs_under (m_fs m) c then err_ret EISDIR  -- may_delete's -EISDIR
  else
    match fs_lookup (m_fs m) c with
    | none => err_ret ENOENT     -- absent from the run's own /tmp: real -ENOENT
    | some _ => unlink_found_spec p c flags m

/-- `unlinkat dirfd path flags`, once the flag word has passed: remove a
directory entry.  This is the one modeled syscall that DELETES from the
file system, and the final file system is observable, so the removal is
real: `Fs.fs_remove`, which `Fs.fs_remove_sorted` proves keeps the
canonical sorted form.  The argument in full — the world the flat map is
exact in, the two guards that keep the spec inside it, what closing
each would cost, and the approximation every deterministic arm carries —
is on Rocq's `Namei.unlinkat_body_spec`; what follows is the kernel each
arm rests on, read at Linux v6.18.46 (commit 1f99e9ab748f).

ORDER, following the kernel's.  `getname()` (include/linux/fs.h:2944-2947,
`getname_flags(name, 0)`) is evaluated first, on the two return paths of
`SYSCALL_DEFINE3(unlinkat)` (fs/namei.c:4780-4782), with its three answers
as Rocq's `Open.openat_spec` has them: `getname_flags` (:135-215) returns
`strncpy_from_user`'s negative result as it is (:161-164, :196-199), which
is -EFAULT for an unreadable byte (lib/strncpy_from_user.c:113-155, Linux v6.18.46, and
the `efault:` label of `do_strncpy_from_user`, :91-92); -ENOENT for the
empty string (fs/namei.c:168-171, :202-206, Linux v6.18.46); and -ENAMETOOLONG when the
copy reaches PATH_MAX with no NUL (:207-211).  Only then is the dirfd
resolved, in `path_init` (:2590 for AT_FDCWD, :2606-2622 for any other
fd): the relative-to-a-dirfd modes are not modeled, so any dirfd but
AT_FDCWD is `unmodeled` — the same treatment Rocq's `Open.openat_spec` gives it, and
a decline rather than the -EBADF (:2610-2611) or -ENOTDIR (:2621-2622)
the kernel can answer there.  For an ABSOLUTE path the dirfd is never
consulted at all — `path_init` returns at :2582-2587 before its `nd->dfd`
branch — so "/" under a foreign dirfd is -EISDIR or -EBUSY on Linux; the
decline there is sound and costs only those two answers.

THE ANSWERS, once the path is in hand.  `link_path_walk` (:2441-2537)
TYPES the last component before anything is looked up: it starts at
LAST_ROOT (:2446), skips leading separators (:2450-2454) and returns
at once if nothing follows them (:2455-2458), so "/" and "//" alike never
enter the component loop; otherwise `hash_name` (:2472) yields
LAST_DOTDOT (:2475-2478), LAST_DOT (:2480-2482) or LAST_NORM (:2484-2486).
`do_unlinkat` answers -EISDIR to every type but LAST_NORM without
distinguishing them (:4720-4722); `do_rmdir` switches on the type
(:4583-4592) — LAST_DOTDOT -ENOTEMPTY, LAST_DOT -EINVAL, LAST_ROOT -EBUSY.
Trailing separators do not change which component is last or how it is
typed (`path_strip_trailing_slashes`); what they change is the byte
`last.name[last.len]`, and `do_unlinkat` tests it only after
`lookup_one_qstr_excl` (:4729) FOUND something (:4734-4735), jumping to
`slashes:` (:4767-4772), which is -ENOTDIR for anything but a directory
and is reached from ABOVE `vfs_unlink`.  An absent name never gets there:
`lookup_one_qstr_excl` answers -ENOENT for a negative dentry when the
caller passed no LOOKUP_CREATE (:1713-1716), and neither `do_unlinkat`
(:4729) nor `do_rmdir` (:4600) does.  The AT_REMOVEDIR -ENOTDIR is a
different answer down a different path: `may_delete(…, isdir = 1)`'s
`!d_is_dir(victim)` (:3284-3286), reached through `vfs_rmdir` (:4532), and
a model file is always a regular file, so rmdir of one never succeeds.

NONE OF THIS TRANSFERS TO A PATH LOOKUP: `lookup_last` (:2647-2652) is
what turns the same trailing byte into LOOKUP_FOLLOW | LOOKUP_DIRECTORY,
and it is called from `path_lookupat` (:2675-2677) alone; `path_parentat`
(:2719-2732), which `filename_parentat` (:2761-2766) and therefore both
unlink callers use, never invokes it.  Rocq's `Namei.unlinkat_body_spec`
carries that argument, and the reason a spec for a lookup must not reuse
`path_strip_trailing_slashes` on the strength of this one.

THE TWO GUARDS, each an `unmodeled` where the flat map would answer with
confidence and be wrong, in Rocq's words and order: a path with a "/"
anywhere but at the end once the trailing ones are stripped, leading
separators included — with the one exception `unlinkat_tmp_spec` carves
out, an absolute "/tmp/<one component>" over the run's declared private
/tmp — because the last component's parent must be the
working directory for the map to be asked at all (an intermediate name
that is a regular file is `link_path_walk`'s -ENOTDIR, :2529-2535, and
nothing in the model records the working directory's own path);
a name longer than NAME_MAX (include/uapi/linux/limits.h:12, Linux v6.18.46), which
`getname()`'s PATH_MAX bound lets through and the FILESYSTEM then refuses
(`ext4_lookup`, fs/ext4/namei.c:1768-1769, Linux v6.18.46; on the harness's tmpfs
working directory `simple_lookup`, fs/libfs.c:71-72, Linux v6.18.46, which
mm/shmem.c:5285 installs).

A NAME SOME KEY LIVES UNDER (`fs_under`) is an implied directory, and it
is ANSWERED (#1753), where it used to be a third guard: flags 0 is
-EISDIR, `may_delete`'s refusal of a directory victim (fs/namei.c:3289-3290,
Linux v6.18.46), or `do_unlinkat`'s `slashes:` label for "a/"
(:4767-4772); AT_REMOVEDIR is -ENOTEMPTY when a key shows an entry in the
directory (`fs_entry_under`), which `vfs_rmdir` (:4529-4567) gets from the
filesystem's `->rmdir` — `ext4_rmdir` (fs/ext4/namei.c:3165-3167, Linux v6.18.46),
`simple_rmdir` (fs/libfs.c:801-802, Linux v6.18.46), `shmem_rmdir`
(mm/shmem.c:4034-4035, Linux v6.18.46) and `btrfs_rmdir`
(fs/btrfs/inode.c:4839-4840, Linux v6.18.46) all refuse a non-empty
directory that way — and is -ENOTEMPTY or the removal when the keys show
no entry ("a/../b", or a key "a/" or "a/." that names "a" itself), since
an empty directory is removed (`rmdir_implied_spec`).  The answers take
the image's directories to be real ones, not symlinks to directories,
whose unlink would remove the link
(bugs/unlinkat-implied-directory-assumed-real.md).  The answers allow no
`unlinkat_errnos` alternative, the narrowing the APPROXIMATION paragraph below
describes (here it also leaves out `vfs_rmdir`'s -EBUSY for a mount
point, :4543-4546).  The test runs before the lookup on purpose, so it
also covers the unrealizable images `Fs.valid_fs` allows, where "a" and
"a/b" are both keys.  The empty real directory, which no key implies, and
why it is an environment precondition today, is
bugs/unlinkat-empty-directory-premise-widened.md.  Rocq's
`Namei.unlinkat_body_spec` has the argument in full.

THE OPEN-FD GUARD.  Linux keeps an unlinked file's contents reachable
through an fd already open on it until the last close (`do_unlinkat`
holds the inode across `vfs_unlink` and drops it after, :4736-4737,
:4747-4749).  The model's file fds record a PATH, so after a removal they
would name nothing, and Rocq's read, write, readv and writev specs (none
ported yet) rest on "a file fd always points into the fs": unlinking a path
some fd still names is `unmodeled` here rather than weakening that
invariant.

THE APPROXIMATION on every deterministic arm: they exclude
`getname_flags`'s own -ENOMEM (:146-148), a real answer to the empty
path, to ".", to "..", to an unreadable pointer and to an over-long one;
and three untracked conditions sit ahead of these arms, which arm they
reach following the last component's TYPE — `may_lookup`'s -EACCES
(:2467, ahead of any arm whose path HAS a component), `complete_walk`'s
-ESTALE (:983-994, only while ND_JUMPED is still set, which `path_init`
sets at :2557 and only the LAST_NORM arm of `link_path_walk` clears at
:2486 on this route), and `mnt_want_write`'s -EROFS (:4724-4726, :4595,
after the type test and before the lookup).  Rocq's table has the
arm-by-arm answer.  Past those, the arms differ in what ELSE they exclude,
because they sit at different depths: the AT_REMOVEDIR -ENOTDIR comes out
of `may_delete` (:3284-3286), so it also excludes the -EACCES (:3274-3276)
and -EPERM (:3277-3283) that function reaches first and `do_rmdir`'s
mnt_want_write -EROFS (:4595-4597) ahead of its lookup; the
trailing-separator -ENOTDIR is jumped to from above `vfs_unlink`
(:4734-4735), so `may_delete` never runs on that path, and what precedes
it is `lookup_one_qstr_excl` alone — -ENOENT for a working directory
already removed (`IS_DEADDIR`, :1698-1699) and -ENOMEM when `d_alloc`
fails (:1701-1703).  Outside the model's environment altogether, and not
in `unlinkat_errnos` either: -EOVERFLOW for an unmapped uid or gid under
an idmapped mount (`may_delete`, :3268-3270) and the -ESTALE a
LOOKUP_REVAL retry can leave (`do_unlinkat`, :4758-4761).  Each of these
arms admits one answer and no `unlinkat_errnos` alternative, which
narrows the spec rather than widening it: exact in the harness's
writable, non-sticky, read-write tmpfs working directory, and a real
trace elsewhere may fall outside it. -/
def unlinkat_body_spec (dirfd pathp flags : word) (i : SyscallInput) (m : Model) :
    Sys SyscallEffect :=
  match read_cstr i.in_mem pathp with
  | CstrTooLong => err_ret ENAMETOOLONG        -- no NUL within PATH_MAX
  | CstrFault => err_ret EFAULT                -- unmapped byte in the path string
  | CstrOk p =>
    if path_eqb p [] then err_ret ENOENT       -- empty pathname: getname's own -ENOENT
    else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled
    else
      let c := path_strip_trailing_slashes p
      if path_eqb c [] then                    -- nothing but separators: LAST_ROOT
        (if unlink_rmdir flags then err_ret EBUSY else err_ret EISDIR)
      else if path_has_slash c then
        (match tmp_name c with
         | some n => unlinkat_tmp_spec n p c flags m
         | none => unmodeled)                  -- a separator not at the end: see the guards above
      else if path_eqb c dot_path then
        (if unlink_rmdir flags then err_ret EINVAL else err_ret EISDIR)
      else if path_eqb c dotdot_path then
        (if unlink_rmdir flags then err_ret ENOTEMPTY else err_ret EISDIR)
      else if NAME_MAX < c.length then unmodeled  -- the filesystem's own -ENAMETOOLONG
      else if fs_under (m_fs m) c then             -- c names an implied directory
        (if unlink_rmdir flags then rmdir_implied_spec c m
         else err_ret EISDIR)      -- may_delete's -EISDIR
      else
        (match fs_lookup (m_fs m) c with
         | none => err_ret ENOENT              -- absent: real -ENOENT, not a modeling gap
         | some _ => unlink_found_spec p c flags m)

/-- The flag word, then the body under its copy-in ledger.

`SYSCALL_DEFINE3(unlinkat, int, dfd, const char __user *, pathname, int,
flag)` (fs/namei.c:4775-4783, Linux v6.18.46) is

    if ((flag & ~AT_REMOVEDIR) != 0)
            return -EINVAL;
    if (flag & AT_REMOVEDIR)
            return do_rmdir(dfd, getname(pathname));
    return do_unlinkat(dfd, getname(pathname));

so `getname` is an argument expression on the two return paths only and
the -EINVAL genuinely precedes it: AT_EMPTY_PATH and AT_SYMLINK_NOFOLLOW
(include/uapi/linux/fcntl.h:126, :120, Linux v6.18.46) are -EINVAL like any other bit,
and an illegal flag word with a NULL or unmapped pathname is -EINVAL with
the pathname never fetched.  `flag` is an `int`, narrowed by
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-88, Linux v6.18.46)
through `__SC_CAST` (include/linux/syscalls.h:132, Linux v6.18.46) before the mask is
applied, which is what `flag32` in the two tests above is.

THE PATHNAME COPY-IN is recorded as Rocq's `Open.openat_spec` records it, and for
the same reason: `read_cstr` is a read of user memory, and
`State.syscall_effect_accesses` turns the ledger into a materialization
charge, so an unrecorded read is a page the run never pays for.  It goes
INSIDE the flag test rather than around the whole spec, because the flag
arm is a real -EINVAL the kernel reaches before `getname()` is evaluated —
recording a copy there would claim a read Linux did not perform.  The
range is the prefix through the first NUL, the first faulting byte, or
PATH_MAX (`State.cstr_access_len_aux`), which
bugs/openat-getname-word-at-a-time.md argues for openat.  Rocq:
`Namei.unlinkat_spec`. -/
def unlinkat_spec (dirfd pathp flags : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if !(modeled_unlink_flags flags) then err_ret EINVAL
  else
    record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (unlinkat_body_spec dirfd pathp flags i m)

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
