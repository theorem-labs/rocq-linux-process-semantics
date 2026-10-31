-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Fs/Open.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite

/-! rocq-baseline: 4d80c33d8337500eb6de1182578751cea75c4995 -/

/-! # LinuxProcessSem.Sys.Fs.Open — openat (56), faccessat (48), faccessat2 (439), close (57), ftruncate (46)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Open.v`, which answers to Linux
`fs/open.c`: it holds what the kernel defines there, and nothing else.
This file holds openat, the faccessat family, close and ftruncate.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/Open.lean`.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
Every line number below was read at v6.18.46; Rocq's prose cites the same
functions with no line numbers.

SPELLINGS THAT DIFFER FROM ROCQ WITHOUT CHANGING A VALUE.  The flag
residue Rocq computes in `Z` as `Z.ldiff (bv_unsigned flags)
open_ignored_flags` is computed on the `word` here, `bv_unsigned (bv_and
flags (bv_not (Z_to_bv 64 open_ignored_flags)))`, and `flag_set`'s
`Z.land` test is a `bv_and` on the words the two integers denote; the
constants are below `2^64` and the residue of a 64-bit word is below
`2^64`, so the two agree.  Rocq's `Z.eqb` is `==` on `Int`, its
`Nat.ltb` is the decidable `<` on `Nat`.

NO DECLARED DECLINE IS LEFT BEYOND THE SPLIT.  `modeled_open_flags` admits
the append word (`append_create_flags`) and the six read-write words
(`rdwr_open_word`, `is_rdwr_excl_create`) exactly as Rocq does, and
`openat_resolved_spec` answers each of them with the arm Rocq gives it:
`openat_append_spec`, `openat_rdwr_spec` and `openat_rdwr_excl_spec`,
which mint `State.FdFileA` and `State.FdFileRW`.  `ftruncate_spec` resizes
both kinds with the body it gives `FdFileW`, as Rocq does.

O_WRONLY|O_CREAT|O_EXCL|O_APPEND, with or without O_TRUNC, is OUTSIDE
`modeled_open_flags`, as it is in Rocq, so the flag gate answers
`unmodeled` for it before the pathname is fetched and no arm below sees
it — in particular neither device arm has an -EEXIST branch for it.  That
word is one Linux answers (`do_open`'s -EEXIST on a name that exists,
fs/namei.c:3949-3950, Linux v6.18.46), so declining it is a narrowing of
the modeled surface, not a wrong answer; it is Rocq's narrowing and this
file states it. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei

/-- openat's injectable failures: environment conditions the model does
not track.  -ENOMEM is `alloc_empty_file`'s (fs/file_table.c:258-260,
Linux v6.18.46, commit 1f99e9ab748f); -EACCES is `may_open`'s
(fs/namei.c:3527-3584) inode_permission call at :3565-3567 and its S_IFCHR
arm at :3546-3549; -EMFILE is `alloc_fd`'s `fd >= end` at
`rlimit(RLIMIT_NOFILE)` (fs/file.c:591-593, Linux v6.18.46); -ENFILE is
`alloc_empty_file`'s `files_stat.max_files` exit (fs/file_table.c:272-278, Linux v6.18.46).
The last two also keep the spec receptive when no free fd < 2^31 exists.
ENOENT is NOT here: file existence IS tracked, and a missing file is a
deterministic -ENOENT.  Rocq: `Open.openat_errnos`. -/
def openat_errnos : List Int := [ENOMEM, EACCES, EMFILE, ENFILE]

/-- The clobbering write-open combination the model covers:
O_WRONLY|O_CREAT|O_TRUNC (include/uapi/asm-generic/fcntl.h:20,23,32, Linux
v6.18.46, commit 1f99e9ab748f).  Rocq: `Open.wr_create_flags`. -/
def wr_create_flags : Int := O_WRONLY + O_CREAT + O_TRUNC

/-- The EXCLUSIVE write-open combinations the model covers:
O_WRONLY|O_CREAT|O_EXCL (include/uapi/asm-generic/fcntl.h:20,23,26, Linux
v6.18.46, commit 1f99e9ab748f), with or without O_TRUNC.  O_EXCL makes
the open fail outright when the path already exists — `do_open`
(fs/namei.c:3949-3950) — so O_TRUNC can never fire alongside it, and
`lookup_open` clears it under O_CREAT|O_EXCL anyway (fs/namei.c:3755-3756, Linux v6.18.46):
the two spellings denote the same kernel behavior.  Rocq:
`Open.excl_create_flags`, `Open.is_excl_create`. -/
def excl_create_flags : Int := O_WRONLY + O_CREAT + O_EXCL

def is_excl_create (fl : Int) : Bool :=
  fl == excl_create_flags || fl == excl_create_flags + O_TRUNC

/-- The APPEND write-open combination the model covers,
O_WRONLY|O_CREAT|O_APPEND (include/uapi/asm-generic/fcntl.h:20,23,35, Linux
v6.18.46, commit 1f99e9ab748f), the word C's `fopen(p, "a")` issues.  A
SINGLE word, not a mask test: the O_TRUNC and the O_EXCL spellings beside
it are declined, each for its own reason, and `modeled_open_flags`'s note
says which.  THIS IS THE ONE ADMITTED WORD WHOSE RESIDUE MEETS
`Fs.Fcntl.setfl_acted_on`, because O_APPEND is a bit F_SETFL acts on, and
that is why the fd it mints is a `State.FdFileA` rather than a
`State.FdFileW`: `Fs.Fcntl.setfl_noop_on` declines the new kind, and its
arm carries the argument.  Rocq: `Open.append_create_flags`. -/
def append_create_flags : Int := O_WRONLY + O_CREAT + O_APPEND

/-- Is bit `b` set in the flag residue `fl`?  Rocq tests
`Z.land fl b = b`; the two integers are read back as 64-bit words and the
mask is taken there (file header).  `build_open_flags` (fs/open.c:1329,
:1317, Linux v6.18.46, commit 1f99e9ab748f) reads O_CREAT and O_TRUNC off
the word the same way.  Rocq: `Open.flag_set`. -/
def flag_set (fl b : Int) : Bool :=
  bv_eqb (bv_and (Z_to_bv 64 fl) (Z_to_bv 64 b)) (Z_to_bv 64 b)

/-- The READ-WRITE open words the model interprets, other than the
exclusive ones: O_RDWR alone, and O_RDWR beside O_CREAT, O_TRUNC or both
(include/uapi/asm-generic/fcntl.h:21,23,32, Linux v6.18.46, commit
1f99e9ab748f).  Why one predicate rather than four, and why O_EXCL is not
in it, is on Rocq's `Open.rdwr_open_word`: the four differ in the two bits
`do_open` reads (fs/namei.c:3948, :3967), O_CREAT deciding an absent name
and O_TRUNC an existing file's bytes, while O_EXCL changes the answer to
a directory reference too (:3949-3952).  Rocq: `Open.rdwr_open_word`. -/
def rdwr_open_word (fl : Int) : Bool :=
  fl == O_RDWR
  || fl == O_RDWR + O_TRUNC
  || fl == O_RDWR + O_CREAT
  || fl == O_RDWR + O_CREAT + O_TRUNC

/-- The EXCLUSIVE read-write create words: O_RDWR|O_CREAT|O_EXCL
(include/uapi/asm-generic/fcntl.h:21,23,26, Linux v6.18.46, commit
1f99e9ab748f), with or without O_TRUNC, one behavior for the reason
`is_excl_create` gives.  Rocq: `Open.rdwr_excl_create_flags`,
`Open.is_rdwr_excl_create`. -/
def rdwr_excl_create_flags : Int := O_RDWR + O_CREAT + O_EXCL

def is_rdwr_excl_create (fl : Int) : Bool :=
  fl == rdwr_excl_create_flags || fl == rdwr_excl_create_flags + O_TRUNC

/-- The flag bits every modeled shape accepts and ignores: O_CLOEXEC,
which Linux HONOURS — `do_sys_openat2` hands the unstripped word to
get_unused_fd_flags (fs/open.c:1435, Linux v6.18.46) and `alloc_fd` records
the bit in the table's close-on-exec set (fs/file.c:606, Linux v6.18.46) —
while `build_open_flags` strips it only from the open flags it gives the
walk (`u64 strip = O_CLOEXEC`, fs/open.c:1241 and :1251, Linux v6.18.46,
commit 1f99e9ab748f).  The bit is ignorable HERE because no Lean entry
carries close-on-exec and no arm reads it, not because Linux discards it;
that stops holding the day an execve, fcntl F_GETFD or dup3 arm reads the
table's bit.  O_LARGEFILE, which `SYSCALL_DEFINE4(openat, …)` forces on every open of a
64-bit kernel (fs/open.c:1466-1467, Linux v6.18.46, through
`force_o_largefile`, include/linux/fcntl.h:24-25, Linux v6.18.46); and
O_NONBLOCK, which reaches `f_flags` and
nothing a modeled arm reads (the argument is on Rocq's
`Uapi.O_NONBLOCK` and `Fcntl.setfl_noop_on`).  One mask, so every mirror
of the flag test strips the same bits.  Rocq: `Open.open_ignored_flags`. -/
def open_ignored_flags : Int := O_CLOEXEC + O_LARGEFILE + O_NONBLOCK

/-- The flag WORDS `openat_spec` interprets, each modulo the bits in
`open_ignored_flags`: O_RDONLY, the clobbering write-create shape, the
exclusive write-create shapes, O_RDONLY|O_DIRECTORY, the append
write-create shape, and the read-write shapes.  Linux validates the flags
in `build_open_flags` (fs/open.c:1238-1361, Linux v6.18.46, commit
1f99e9ab748f) BEFORE `getname` fetches the pathname
(`do_sys_openat2`, fs/open.c:1427-1431), so this test runs first in
`openat_core_spec` too.

O_DIRECTORY is interpreted, not ignored: `do_open` answers -ENOTDIR for a
dentry `d_can_lookup` refuses (fs/namei.c:3958-3959, Linux v6.18.46; include/linux/dcache.h:427-430, Linux v6.18.46)
before `may_open` (:3973) and `vfs_open` (:3974-3975), so the answer does
not depend on which non-directory the name is (`openat_dir_spec`).

DECLINED, each for its own reason on Rocq's `Open.modeled_open_flags`:
O_WRONLY|O_APPEND without O_CREAT, the O_TRUNC and the O_EXCL spellings
of the append word, O_RDWR beside O_APPEND, O_RDWR|O_DIRECTORY (which
`build_open_flags` admits and `may_open`'s S_IFDIR arm answers -EISDIR,
fs/namei.c:3540-3542, Linux v6.18.46), O_RDWR|O_EXCL without O_CREAT (`do_open` reads
O_EXCL only inside its O_CREAT block, :3948-3950), and O_NOCTTY, whose
one meaning needs a terminal the model has none of.  EVERY BIT ABOVE THE
INTERPRETED ONES is declined too, a narrowing, and Linux drops them by two
different mechanisms: bits 32-63 never reach the kernel's C, because
`flags` is `int` at the boundary (`SYSCALL_DEFINE4(openat, …)`,
fs/open.c:1463-1464, Linux v6.18.46) and the register is cast to it; bits
23-31 arrive inside the `int` and `build_open_how` masks them off with
VALID_OPEN_FLAGS (fs/open.c:1225, Linux v6.18.46; the mask,
include/linux/fcntl.h:9-13, tops out at __O_TMPFILE, bit 22), silently
rather than with -EINVAL.  Either way Linux opens the word the low bits
spell, while this predicate reads all 64 and is false above the
interpreted bits — so `unmodeled`, never that open.  Rocq:
`Open.modeled_open_flags`. -/
def modeled_open_flags (flags : word) : Bool :=
  let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
  fl == 0 || fl == wr_create_flags || is_excl_create fl
  || fl == O_DIRECTORY || fl == append_create_flags
  || rdwr_open_word fl || is_rdwr_excl_create fl

/-! ### The introduction lemmas, twins of Rocq's

One per modeled shape, so a proof that already knows which arm it is in
can clear the flags guard.  Rocq: `Open.modeled_open_flags_rd` and its
siblings. -/

theorem modeled_open_flags_rd (flags : word)
    (h : bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = 0) :
    modeled_open_flags flags = true := by
  simp only [modeled_open_flags, h, beq_self_eq_true, Bool.true_or]

theorem modeled_open_flags_wr (flags : word)
    (h : bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = wr_create_flags) :
    modeled_open_flags flags = true := by
  simp only [modeled_open_flags, h, beq_self_eq_true, Bool.or_true, Bool.true_or]

theorem modeled_open_flags_excl (flags : word)
    (h : is_excl_create (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))) = true) :
    modeled_open_flags flags = true := by
  simp only [modeled_open_flags, h, Bool.or_true, Bool.true_or]

theorem modeled_open_flags_append (flags : word)
    (h : bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = append_create_flags) :
    modeled_open_flags flags = true := by
  simp only [modeled_open_flags, h, beq_self_eq_true, Bool.or_true, Bool.true_or]

theorem modeled_open_flags_dir (flags : word)
    (h : bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = O_DIRECTORY) :
    modeled_open_flags flags = true := by
  simp only [modeled_open_flags, h, beq_self_eq_true, Bool.or_true, Bool.true_or]

theorem modeled_open_flags_rdwr (flags : word)
    (h : rdwr_open_word (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))) = true) :
    modeled_open_flags flags = true := by
  simp only [modeled_open_flags, h, Bool.or_true, Bool.true_or]

theorem modeled_open_flags_rdwr_excl (flags : word)
    (h : is_rdwr_excl_create (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))) = true) :
    modeled_open_flags flags = true := by
  simp only [modeled_open_flags, h, Bool.or_true]

/-- The common result of opening an existing object: an injectable
failure, or the lowest free fd (`get_unused_fd_flags`, fs/file.c:620-623,
Linux v6.18.46, commit 1f99e9ab748f, through `File.lowest_fd`) followed by
`mk`'s model update, the way `fd_install` (fs/file.c:652-677) binds the
file `do_filp_open` returned (`do_sys_openat2`, fs/open.c:1435-1443).
Rocq: `Open.open_result_spec`. -/
def open_result_spec (m : Model) (mk : word → Model → Model) : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)
      (fd <- lowest_fd (m_fds m) ;;
       modify (mk fd) ;;
       ret_only fd)

/-- The effect a modeled WRITE-CREATE open records, shared by the
clobbering and the exclusive shapes: an errno from `openat_errnos`, or
the lowest free fd bound to a write-only fd on `p`, with `p` (re)created
empty.  The empty content is the kernel's on both routes: a created
file is empty and `do_open` clears O_TRUNC under FMODE_CREATED
(fs/namei.c:3963-3966, Linux v6.18.46, commit 1f99e9ab748f); an existing
regular file is emptied by `handle_truncate` (`do_truncate` to length 0,
fs/namei.c:3586-3602, armed at :3967-3972 and run at :3978-3979).  The
offset is 0 because `init_file` zeroes `f_pos` (fs/file_table.c:216, Linux v6.18.46).

THIS IS WHERE THE MODEL'S REGULAR-FILE PREMISE IS CREATED: `p` is an
uninterpreted byte string, so a name the kernel resolves to a device, a
FIFO or a kernfs attribute is recorded here as an ordinary file
(bugs/fs-paths-assumed-regular-files.md; the argument is on Rocq's
`Open.create_wronly`). -/
def create_wronly (p : path) (m : Model) : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)
      (fd <- lowest_fd (m_fds m) ;;
       set_fs (fs_set (m_fs m) p []) ;;
       set_fds (fd_insert (m_fds m) fd (.FdFileW p (Z_to_bv 64 0))) ;;
       ret_only fd)

/-- The two paths that name a DIRECTORY without consulting a file system,
"." and "..": `link_path_walk` types the last component LAST_DOT or
LAST_DOTDOT (fs/namei.c:2475-2482, Linux v6.18.46, commit 1f99e9ab748f)
and `open_last_lookups` takes its `nd->last_type != LAST_NORM` branch to
`handle_dots` (:3859-3863, :2096-2132) before O_CREAT is considered, so
both get the same three answers from `do_open` (:3948-3952): -EEXIST under
O_EXCL, -EISDIR under O_CREAT, and, under plain O_RDONLY, the directory
`may_open`'s S_IFDIR arm lets through (:3540-3545).  The one answer ".."
has that "." does not, `follow_dotdot`'s -ENOENT from `path_connected`
(:2084-2087, :719-728), is a bind-mount case this arm is narrower than
Linux by, not a wrong answer; the condition that would falsify answering
".." at all — a modeled real-dirfd arm — is on Rocq's
`Open.path_is_dirref`. -/
def path_is_dirref (p : path) : Bool :=
  path_eqb p dot_path || path_eqb p dotdot_path

/-- Resolve an O_RDONLY open after pathname fetch and dirfd validation.  A
directory reference is a directory fd; a name the map holds is a
read-only file fd at offset 0 (`init_file`, fs/file_table.c:216, Linux
v6.18.46, commit 1f99e9ab748f); a name it does not hold is the negative
dentry's -ENOENT out of `traverse_mounts` (fs/namei.c:1537-1538) on the
trailing `step_into` (:1989-1992, :3922), deterministic and admitting no
`openat_errnos` alternative.  Rocq: `Open.openat_read_spec`. -/
def openat_read_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p then
    open_result_spec m (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir))
  else
    match fs_lookup (m_fs m) p with
    | none => err_ret ENOENT
    | some _ =>
        open_result_spec m
          (fun fd => with_fds (fd_insert (m_fds m) fd (.FdFile p (Z_to_bv 64 0))))

/-- Resolve the clobbering O_WRONLY|O_CREAT|O_TRUNC open shape.  A
directory reference, or a name the map implies is a directory because
some key lives under it (`Namei.fs_under`), is -EISDIR: the dentry the
lookup finds is positive with FMODE_CREATED clear (`lookup_fast_for_open`,
fs/namei.c:3837-3845, and `lookup_open`, fs/namei.c:3714 and :3734-3737,
Linux v6.18.46, commit 1f99e9ab748f) and `do_open`'s O_CREAT block answers
`d_is_dir(nd->path.dentry)` with -EISDIR (:3951-3952) before `may_open`
and before any O_TRUNC handling.  Deterministic, with no `openat_errnos`
alternative; the derivation and the reason it is an answer and not a
decline are on Rocq's `Open.openat_create_spec`. -/
def openat_create_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else create_wronly p m

/-- The file system after an APPEND open: unchanged when the path is
already there, and carrying a new empty file when it is not.  Nothing on
the O_APPEND path truncates — O_TRUNC alone arms the truncation, in
`do_open` (fs/namei.c:3967-3972, Linux v6.18.46, commit 1f99e9ab748f),
and O_APPEND is a status flag `init_file` copies into `f_flags`
(fs/file_table.c:198) that is read at write time.  `open_append` is the
arm that reads it.  Rocq:
`Open.append_open_fs`. -/
def append_open_fs (fs : Fs.Fs) (p : path) : Fs.Fs :=
  match fs_lookup fs p with
  | some _ => fs
  | none => fs_set fs p []

/-- The effect a modeled APPEND write-open records: an errno from
`openat_errnos` (the same untracked environment conditions the other
write-open shapes admit, this alternative also keeping the spec receptive
when no free fd < 2^31 exists), or the lowest free fd bound to a
`State.FdFileA` on `p`, with `p` created empty only if it was absent
(`append_open_fs`).

THE OFFSET STARTS AT 0 AND THAT IS EXACT: `init_file` zeroes `f_pos`
(fs/file_table.c:216, Linux v6.18.46, commit 1f99e9ab748f) and no O_APPEND
path assigns to it at open time, which is why `fopen(p, "a")` has to be
followed by an `ftell` that seeks to learn the size.  The append
positioning happens per WRITE, in `generic_write_checks` (mm/filemap.c,
Linux v6.18.46), and `ReadWrite.write_spec`'s `FdFileA` arm is where the
model records it.

THE REGULAR-FILE PREMISE OF `create_wronly` IS SHARED, unchanged: `p` is
an uninterpreted byte string, so a name Linux would resolve to a device, a
FIFO or a kernfs attribute is recorded here as an ordinary file.  Rocq:
`Open.open_append`. -/
def open_append (p : path) (m : Model) : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)
      (fd <- lowest_fd (m_fds m) ;;
       set_fs (append_open_fs (m_fs m) p) ;;
       set_fds (fd_insert (m_fds m) fd (.FdFileA p (Z_to_bv 64 0))) ;;
       ret_only fd)

/-- Resolve the APPEND write-create open shape.

A DIRECTORY REFERENCE IS -EISDIR, the clobbering shape's answer and not
the exclusive shape's -EEXIST, and the reason is which test `do_open`
reaches first.  With O_CREAT set it returns -EEXIST only under O_EXCL
(fs/namei.c:3949-3950, Linux v6.18.46, commit 1f99e9ab748f), which this
word does not carry; the next test is `d_is_dir(nd->path.dentry)`
(:3951-3952), and that is -EISDIR.  So "." and ".." answer here exactly as
they do for O_WRONLY|O_CREAT|O_TRUNC, ahead of `may_open` (:3973), and
O_APPEND changes nothing about it.  An IMPLIED directory
(`Namei.fs_under`) takes the same branch for the reason given on
`openat_create_spec`: the dentry the lookup finds is positive and
`d_is_dir`, and the word carries no O_EXCL.  An existing file is opened
and keeps its bytes (`append_open_fs`).  Rocq: `Open.openat_append_spec`. -/
def openat_append_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else open_append p m

/-- Resolve an exclusive write-create open after pathname fetch.  A
directory reference, an implied directory and a name the map holds are
all -EEXIST, never -EISDIR: `do_open` tests `(open_flag & O_EXCL) &&
!(file->f_mode & FMODE_CREATED)` (fs/namei.c:3949-3950, Linux v6.18.46,
commit 1f99e9ab748f) BEFORE `d_is_dir` (:3951-3952), and a name that
exists was not created (`lookup_open` sets FMODE_CREATED only on the
create route, :3788-3789).  An absent name is created empty.  Rocq:
`Open.openat_excl_spec`. -/
def openat_excl_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EEXIST
  else
    match fs_lookup (m_fs m) p with
    | some _ => err_ret EEXIST
    | none => create_wronly p m

/-- The effect a modeled READ-WRITE open records: an errno from
`openat_errnos`, or the lowest free fd bound to a `State.FdFileRW` on `p`,
with the file system left as `fs'`.

THE OFFSET STARTS AT 0 for both directions, and it is the same `f_pos`
both use: `init_file` zeroes it (fs/file_table.c:216, Linux v6.18.46,
commit 1f99e9ab748f) and nothing on the O_RDWR path assigns to it at open
time.  O_TRUNC does not move it either — it empties the file through
`handle_truncate` (fs/namei.c:3967-3972 and :3978-3979, Linux v6.18.46)
and leaves the position alone, which is why a truncating open is `fs'` and
not an offset.

THE REGULAR-FILE PREMISE OF `create_wronly` IS SHARED, unchanged, and this
kind widens its reach by one direction rather than by a new premise: a
character device opened O_RDWR is readable AND writable in the model,
where the other kinds open the same name one way at a time.  Rocq:
`Open.open_rdwr`. -/
def open_rdwr (p : path) (fs' : Fs.Fs) (m : Model) : Sys SyscallEffect :=
  alt (e <- errno_from openat_errnos ;; err_ret e)
      (fd <- lowest_fd (m_fds m) ;;
       set_fs fs' ;;
       set_fds (fd_insert (m_fds m) fd (.FdFileRW p (Z_to_bv 64 0))) ;;
       ret_only fd)

/-- Resolve one of the four non-exclusive READ-WRITE open words, with
`creat` and `trunc` the two bits that separate them (`rdwr_open_word` says
why they are one arm).  All four answers are `do_open`'s (fs/namei.c,
Linux v6.18.46, commit 1f99e9ab748f):

- a DIRECTORY REFERENCE, or an IMPLIED directory (`Namei.fs_under`), is
  -EISDIR whatever the two bits say, and the two bit settings reach it at
  different sites: with O_CREAT it is `do_open`'s own
  `d_is_dir(nd->path.dentry)` (:3951-3952) inside the O_CREAT block;
  without it, nothing in that block runs and the answer is `may_open`'s
  `case S_IFDIR: if (acc_mode & MAY_WRITE) return -EISDIR` (:3540-3542),
  with MAY_WRITE present because `build_open_flags` sets
  `acc_mode = ACC_MODE(flags)` (fs/open.c:1243, Linux v6.18.46) and
  ACC_MODE maps O_RDWR to MAY_READ|MAY_WRITE (include/linux/fs.h:3980,
  Linux v6.18.46).  The second derivation is the one O_RDONLY never
  reaches, which is why the plain read arm hands "." a descriptor and this
  arm cannot;
- an ABSENT name is a fresh empty file under O_CREAT and -ENOENT without
  it, the negative dentry's -ENOENT out of `traverse_mounts`
  (fs/namei.c:1537-1538, Linux v6.18.46) on the trailing `step_into`
  (:1989-1992, :3922), the same answer `openat_read_spec` gives;
- an EXISTING file is emptied under O_TRUNC and keeps its bytes without
  it: `do_open` arms `handle_truncate` on
  `d_is_reg(nd->path.dentry) && open_flag & O_TRUNC` (:3967-3972);
- a file the open just CREATED is empty either way, which is why `creat`
  and `trunc` are not composed on that branch: `do_open` clears O_TRUNC
  under FMODE_CREATED (:3963-3966) before the truncate test, so a created
  file is never truncated at all.

Rocq: `Open.openat_rdwr_spec`. -/
def openat_rdwr_spec (creat trunc : Bool) (p : path) (m : Model)
    : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else
    match fs_lookup (m_fs m) p with
    | none =>
        if creat then open_rdwr p (fs_set (m_fs m) p []) m
        else err_ret ENOENT
    | some _ =>
        open_rdwr p (if trunc then fs_set (m_fs m) p [] else m_fs m) m

/-- Resolve an exclusive READ-WRITE create open.  The shape of
`openat_excl_spec` with the fd kind changed and no other difference:
O_EXCL's -EEXIST is decided before any type test (fs/namei.c:3949-3950,
Linux v6.18.46, commit 1f99e9ab748f), so a directory reference or an
implied directory answers -EEXIST here rather than the -EISDIR
`openat_rdwr_spec` gives it.  Rocq: `Open.openat_rdwr_excl_spec`. -/
def openat_rdwr_excl_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EEXIST
  else
    match fs_lookup (m_fs m) p with
    | some _ => err_ret EEXIST
    | none => open_rdwr p (fs_set (m_fs m) p []) m

/-- Resolve an O_RDONLY|O_DIRECTORY open after pathname fetch.

The arm exists because -ENOTDIR is type-blind: `build_open_flags` turns
O_DIRECTORY into LOOKUP_DIRECTORY (fs/open.c:1337-1338, Linux v6.18.46,
commit 1f99e9ab748f) and `do_open` answers -ENOTDIR for any resolved
dentry `d_can_lookup` refuses (fs/namei.c:3958-3959;
include/linux/dcache.h:427-430), after the O_CREAT block and before
`may_open` (:3973) and `vfs_open` (:3974-3975), so a FIFO, a socket, a
character device and a regular file all answer -ENOTDIR.  "." and ".."
give the same directory fd the plain read arm gives; an absent name is
`traverse_mounts`'s -ENOENT (:1537-1538) before the directory test is
reached.  Both errnos are deterministic.

TWO GUARDS THE READ ARM CANNOT TAKE, taken here because no example
reaches this arm: a component over NAME_MAX (include/uapi/linux/limits.h:12, Linux v6.18.46)
is the FILESYSTEM's -ENAMETOOLONG (`simple_lookup`, fs/libfs.c:71-72, Linux v6.18.46;
`ext4_lookup`, fs/ext4/namei.c:1768-1769, Linux v6.18.46), which a model with no
filesystem type cannot pick, and a name some key lives under is a
directory Linux would open where the map would answer -ENOENT.  The
asymmetry with the read arm, and what the -ENOENT rests on, are on Rocq's
`Open.openat_dir_spec` and bugs/openat-name-max-and-implied-directory.md. -/
def openat_dir_spec (p : path) (m : Model) : Sys SyscallEffect :=
  if path_is_dirref p then
    open_result_spec m (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir))
  else if NAME_MAX < p.length then unmodeled
  else if fs_under (m_fs m) p then unmodeled
  else
    match fs_lookup (m_fs m) p with
    | none => err_ret ENOENT
    | some _ => err_ret ENOTDIR

/-- A pathname the read and write-create arms resolve on their own terms:
not a directory reference, and not slash-bearing.  The premise the
whole-program examples carry about their argv-derived paths
(`Run.valid_argv`'s fifth clause in Rocq).  Rocq: `Open.openat_plain_name`. -/
def openat_plain_name (p : path) : Bool :=
  !path_is_dirref p && !path_has_slash p

theorem openat_plain_name_nodirref (p : path) (h : openat_plain_name p = true) :
    path_is_dirref p = false := by
  cases hd : path_is_dirref p
  · rfl
  · simp only [openat_plain_name, hd, Bool.not_true, Bool.false_and] at h
    cases h

theorem openat_plain_name_noslash (p : path) (h : openat_plain_name p = true) :
    path_has_slash p = false := by
  cases hs : path_has_slash p
  · rfl
  · simp only [openat_plain_name, hs, Bool.not_true, Bool.and_false] at h
    cases h

/-- A directory reference has no separator, so the dot arms get past the
separator guard from the same hypothesis that selects them.  Rocq:
`Open.path_is_dirref_no_slash`. -/
theorem path_is_dirref_no_slash (p : path) (h : path_is_dirref p = true) :
    path_has_slash p = false := by
  simp only [path_is_dirref, Bool.or_eq_true, path_eqb_eq] at h
  rcases h with rfl | rfl <;> decide

/-- "/etc/localtime", the file a C library's `tzset` opens; the one
absolute path this file answers -ENOENT, under the maintainer-declared
assumption (issue #696, bugs/openat-localtime-assumed-absent.md) that an
O_CREAT-free open of it finds no inode in the image.  Rocq:
`Open.localtime_path`. -/
def localtime_path : path :=
  [Z_to_bv 8 47, Z_to_bv 8 101, Z_to_bv 8 116, Z_to_bv 8 99, Z_to_bv 8 47,
   Z_to_bv 8 108, Z_to_bv 8 111, Z_to_bv 8 99, Z_to_bv 8 97, Z_to_bv 8 108,
   Z_to_bv 8 116, Z_to_bv 8 105, Z_to_bv 8 109, Z_to_bv 8 101]

/-- The "/etc/localtime" arm.  Under a word WITHOUT O_CREAT the walk
reaches a negative last component and `open_last_lookups`
(fs/namei.c:3919-3922, Linux v6.18.46, commit 1f99e9ab748f) hands it to
step_into, whose handle_mounts call reaches `traverse_mounts`
(fs/namei.c:1537-1538), which answers -ENOENT for a dentry
`d_flags_negative` (include/linux/dcache.h:468-471) is true of, before
`do_open` looks at any flag, so
the answer does not turn on the access mode.  The arm is flag-blind, and
that is sound only because `openat_core_spec` has already refused every
word `modeled_open_flags` does not accept, so the O_CREAT-free residues
that arrive are exactly O_RDONLY, O_RDONLY|O_DIRECTORY, O_RDWR and
O_RDWR|O_TRUNC.  Fail-closed: any word with O_CREAT (`lookup_open` would
create the file under a directory the model has no representation of,
:3788-3800), and an image whose map holds the key or a key under it (the
assumption was not declared for that image).  The match is on the exact
byte string.  The declaration and its edges are on Rocq's
`Open.openat_localtime_spec`. -/
def openat_localtime_spec (flags : word) (m : Model) : Sys SyscallEffect :=
  match fs_lookup (m_fs m) localtime_path with
  | some _ => unmodeled
  | none =>
      if fs_under (m_fs m) localtime_path then unmodeled
      else if flag_set (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))) O_CREAT
      then unmodeled
      else err_ret ENOENT

/-- The success shape every admitted "/dev/null" word shares: the
injectable errno, or the lowest free fd bound to the device entry with
the granted mode — FMODE_READ, FMODE_WRITE or both, which `init_file`
derives from the access mode (`OPEN_FMODE`, fs/file_table.c:199, Linux
v6.18.46, commit 1f99e9ab748f).  Rocq: `Open.open_devnull`. -/
def open_devnull (m : Model) (rd wr : Bool) : Sys SyscallEffect :=
  open_result_spec m (fun fd => with_fds (fd_insert (m_fds m) fd (.FdDevNull rd wr)))

/-- The "/dev/null" arm, on the assumption (issue #696,
bugs/openat-devnull-assumed-null-device.md) that the image's /dev/null is
the null device, character major 1 minor 3: `devlist[3]` is "null"
(drivers/char/mem.c:694, Linux v6.18.46, commit 1f99e9ab748f) and
`memory_open` installs `null_fops` (:707-727, :644-652) when
`chrdev_open` (fs/char_dev.c:373-424) runs the device's open out of
`do_dentry_open` (fs/open.c:963-965).  The kernel path each word takes,
all decided before that open runs:

- O_RDONLY, and the read-write words without O_EXCL: `do_open` reaches
  `may_open` (fs/namei.c:3546-3549, Linux v6.18.46), whose S_IFCHR arm tests may_open_dev
  and nothing else (its -EACCES is already an `openat_errnos` alternative)
  and drops O_TRUNC
  for a device (:3555), then `vfs_open` (:3974-3975).
- O_WRONLY|O_CREAT|O_TRUNC: the same — O_CREAT on an existing name creates
  nothing (`lookup_open` :3734-3737, FMODE_CREATED clear) and `do_open`
  arms `handle_truncate` only under `d_is_reg` (:3967), which a character
  device fails.
- O_WRONLY|O_CREAT|O_APPEND: the same again; nothing in `null_fops` reads
  `f_flags` (`write_null` :418-422 and `write_iter_null` :429-434 return
  the count without a position), so the append word mints the write-only
  entry the clobbering word does.
- O_CREAT|O_EXCL, in either access mode: `do_open`'s -EEXIST
  (:3949-3950).
- O_RDONLY|O_DIRECTORY: `do_open`'s -ENOTDIR (:3958-3959).

Fail-closed on an image whose map holds the key or a key under it; the
match is on the exact byte string.  Rocq: `Open.openat_devnull_spec`. -/
def openat_devnull_spec (flags : word) (m : Model) : Sys SyscallEffect :=
  match fs_lookup (m_fs m) devnull_path with
  | some _ => unmodeled
  | none =>
      if fs_under (m_fs m) devnull_path then unmodeled
      else
        let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
        if fl == 0 then open_devnull m true false
        else if fl == wr_create_flags then open_devnull m false true
        else if is_excl_create fl then err_ret EEXIST
        else if fl == O_DIRECTORY then err_ret ENOTDIR
        else if fl == append_create_flags then open_devnull m false true
        else if rdwr_open_word fl then open_devnull m true true
        else if is_rdwr_excl_create fl then err_ret EEXIST
        else unmodeled

/-- The success shape of the read-only "/dev/urandom" open: the injectable
errno, or the lowest free fd bound to `State.FdUrandom`, the read-only
device entry whose reads consume the run's declared stream.  The
descriptor Linux mints carries FMODE_READ from the access mode
(`OPEN_FMODE`, fs/file_table.c:199, Linux v6.18.46, commit 1f99e9ab748f).
Rocq: `Open.open_urandom`. -/
def open_urandom (m : Model) : Sys SyscallEffect :=
  open_result_spec m (fun fd => with_fds (fd_insert (m_fds m) fd .FdUrandom))

/-- The "/dev/urandom" arm (#712), the second device this file answers, on
the assumption (issue #696, bugs/openat-urandom-assumed-random-device.md)
that the image's /dev/urandom is the random device, character major 1
minor 9: `devlist[9]` is "urandom" (drivers/char/mem.c:701, Linux
v6.18.46, commit 1f99e9ab748f) and `memory_open` installs `urandom_fops`
(:707-727; drivers/char/random.c:1572-1581) when `chrdev_open`
(fs/char_dev.c:373-424) runs the device's open out of `do_dentry_open`
(fs/open.c:963-965).  What the bytes are is not this arm's choice: the
run's `State.in_urandom` declares them — the maintainer's ruling on #696,
an arbitrary but fixed stream, a parameter of the execution like argv and
envp — and the read arm hands them out from the front; `getrandom` (278)
is deliberately not drawn from it.  The kernel path each word takes, all
fs/namei.c at Linux v6.18.46 and all decided before the device's own open
runs:

- O_RDONLY, with or without the ignored bits: `do_open` reaches
  `may_open` (fs/namei.c:3546-3549), whose S_IFCHR arm tests may_open_dev
  and nothing else (its -EACCES is already an `openat_errnos` alternative)
  and drops O_TRUNC for a device (:3555), then `vfs_open` (:3974-3975).
- O_CREAT|O_EXCL, in either access mode: `do_open`'s -EEXIST
  (:3949-3950), before `may_open` — deterministic, as on every existing
  name.
- O_RDONLY|O_DIRECTORY: `do_open`'s -ENOTDIR (:3958-3959).
- THE WRITE WORDS ARE DECLINED, not answered: O_WRONLY and O_RDWR, with
  or without O_CREAT, O_TRUNC and O_APPEND.  Linux
  accepts them —
  `may_open` passes and drops the truncation, and a write through the
  descriptor reaches `random_write_iter` (drivers/char/random.c:1448,
  Linux v6.18.46), which mixes the bytes into the input pool
  (`write_pool_user`, :1420)
  and returns the count — and the model models neither writes into the
  pool nor a descriptor on this device that could carry them.  A program
  that opens the device for writing leaves the modeled surface at the
  open.

Fail-closed on an image whose map holds the key or a key under it; the
match is on the exact byte string, so "/dev//urandom" and "/dev/./urandom"
take the separator decline, and so does "/dev/random", a different device
(`random_fops`, drivers/char/random.c:1560, Linux v6.18.46, whose
`random_read_iter` blocks until the pool is ready) that the ruling on #696
does not name.  Rocq:
`Open.openat_urandom_spec`. -/
def openat_urandom_spec (flags : word) (m : Model) : Sys SyscallEffect :=
  match fs_lookup (m_fs m) urandom_path with
  | some _ => unmodeled
  | none =>
      if fs_under (m_fs m) urandom_path then unmodeled
      else
        let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
        if fl == 0 then open_urandom m
        else if is_excl_create fl then err_ret EEXIST
        else if fl == O_DIRECTORY then err_ret ENOTDIR
        else if is_rdwr_excl_create fl then err_ret EEXIST
        else unmodeled

/-- "/tmp/<name>", the run's own PRIVATE temporary directory: the third
absolute shape this file answers for, and the first that is a FILE rather
than a device.  `n` is the one component `Namei.tmp_name` stripped off
`p`, and `p` is the absolute key (`Namei.tmp_name_key`).

THE ENVIRONMENT ASSUMPTION, stated on Rocq's `Open.openat_tmp_spec` and
consumed here and by `Namei.unlinkat_tmp_spec`: /tmp is a distinct,
writable directory private to this run, so the run's own table is the
whole truth about it — `State.in_tmp`, the environment's declaration,
seeded under absolute keys by `State.fs_seed_tmp`, plus what
`create_wronly` created, minus what unlinkat removed
(bugs/tmp-assumed-private-directory.md).  The name is an input, not a
choice, and the same directory is seen by both sides of a pair.

THE TWO SHAPES ANSWERED (maintainer's ruling on issue #562, rung 4 of
#696), each matched past `open_ignored_flags` as every arm here is: the
create word O_WRONLY|O_CREAT|O_TRUNC goes to `openat_create_spec`, whose
success arm is the `create_wronly` that mirrors what `lookup_open` does
on the negative dentry — FMODE_CREATED, then the directory's create op
(fs/namei.c:3788-3800, Linux v6.18.46, commit 1f99e9ab748f) — and what
`do_open` does on an existing regular file, arming the truncation
(:3967-3972); O_RDONLY of a name the run HOLDS goes to
`openat_read_spec`, `may_open`'s S_IFREG arm (:3557-3560) with nothing
to refuse.  Every other word is DECLINED rather than answered, and so is
a read of a name the run does not hold, whose -ENOENT would follow from
the privacy premise alone: the ruling takes the shapes the reported
programs need and leaves the rest, the narrower choice at each.

THE ONE GUARD AHEAD OF THE FLAG TEST.  `NAME_MAX` is the FILESYSTEM's
own -ENAMETOOLONG, which fs/namei.c does not produce and a model with no
filesystem type cannot invent: tmpfs answers it from `simple_lookup`
(fs/libfs.c:71-72, Linux v6.18.46) and ext4 from `ext4_lookup`
(fs/ext4/namei.c:1768-1769, Linux v6.18.46), so a longer component is
declined on both words (the plain arms cannot afford this guard —
`openat_dir_spec`'s docstring says why, after Rocq's note on
`Open.openat_plain_name` — and this one can, since no example's argv
reaches a /tmp path).

THE IMPLIED DIRECTORY IS ANSWERED ON THE CREATE WORD AND DECLINED ON THE
READ WORD, which is why `Namei.fs_under` is tested inside each word
instead of ahead of both.  A declaration naming "a/b" seeds a key under
"/tmp/a", and that key is what says "/tmp/a" is a directory.  The create
word IS `openat_create_spec`, reached rather than restated, so the
-EISDIR of `do_open`'s O_CREAT block (fs/namei.c:3951-3952, Linux
v6.18.46) is the answer here as it is for a working-directory name;
`path_is_dirref` is inert on this arm, since `Namei.tmp_name` admits no
"." or "..".  The read word still declines, because answering it means
handing back a directory descriptor (`may_open`'s S_IFDIR arm, :3540-3545,
which permits the read) and the model has no directory semantics to give
one — bugs/openat-name-max-and-implied-directory.md prices that trade.
The test stays inside the read branch rather than being dropped, because
`Fs.valid_fs` admits an image holding "/tmp/a" and "/tmp/a/b" at once.
Rocq: `Open.openat_tmp_spec`. -/
def openat_tmp_spec (n p : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if NAME_MAX < n.length then unmodeled
  else
  let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
  if fl == 0 then
    (if fs_under (m_fs m) p then unmodeled
     else match fs_lookup (m_fs m) p with
          | none => unmodeled
          | some _ => openat_read_spec p m)
  else if fl == wr_create_flags then openat_create_spec p m
  else unmodeled

/-- The pathnames with a separator that are ANSWERED, tested ahead of
the separator decline: "/etc/localtime", "/dev/null", "/dev/urandom"
(`openat_urandom_spec`, #712), and the "/tmp/<name>" family through
`Namei.tmp_name`.  Only a path with a separator can match, so the
dispatch sits inside the true branch of `path_has_slash` in
`openat_resolved_spec`: same answers as testing them first, and the
slash-free arms are untouched.  Rocq: `Open.openat_sep_spec`. -/
def openat_sep_spec (p : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if path_eqb p localtime_path then openat_localtime_spec flags m
  else if path_eqb p devnull_path then openat_devnull_spec flags m
  else if path_eqb p urandom_path then openat_urandom_spec flags m
  else match tmp_name p with
       | some n => openat_tmp_spec n p flags m
       | none => unmodeled

/-- Dispatch a fetched, nonempty AT_FDCWD pathname by modeled flag shape.

THE SEPARATOR GUARD IS HOISTED above the flag test: the interpreted file
system is a flat map with no directory structure, so a pathname with a
separator in it is declined ahead of any arm, with the exceptions
`openat_sep_spec` names.  Linux walks the interior components in
`link_path_walk` (fs/namei.c:2441-2537, Linux v6.18.46, commit
1f99e9ab748f) before `open_last_lookups` and `do_open` read the flags, so
the hoisted position is the faithful one; the soundness argument for the
decline — without it the create shapes would mint a key spelled
"/no/such/file" where Linux answers -ENOENT — is on Rocq's
`Open.openat_resolved_spec`.

THE ARMS ARE NOT ALL TOTAL.  All but one answer every pathname they are
handed; `openat_dir_spec` does not, and its declines are on the path
rather than on the flag word.  The FINAL `unmodeled` is unreachable — the
branches exhaust what `modeled_open_flags` admits — but this dispatcher
does not decline only above an arm: it also declines inside one.  The
seven arms are Rocq's, in Rocq's order. -/
def openat_resolved_spec (p : path) (flags : word) (m : Model) : Sys SyscallEffect :=
  if path_has_slash p then openat_sep_spec p flags m else
  let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
  if fl == 0 then openat_read_spec p m
  else if fl == wr_create_flags then openat_create_spec p m
  else if is_excl_create fl then openat_excl_spec p m
  else if fl == O_DIRECTORY then openat_dir_spec p m
  else if fl == append_create_flags then openat_append_spec p m
  else if rdwr_open_word fl then
    openat_rdwr_spec (flag_set fl O_CREAT) (flag_set fl O_TRUNC) p m
  else if is_rdwr_excl_create fl then openat_rdwr_excl_spec p m
  else unmodeled

/-- `openat dirfd path flags mode` after the flag gate: the pathname fetch,
then the dirfd, then the arms.

THE PATHNAME FETCH has all three of `getname_flags`'s answers
(fs/namei.c:136-216, Linux v6.18.46, commit 1f99e9ab748f): -EFAULT is
`strncpy_from_user`'s error returned as it is (:157, :161-165, and :195-200
on the PATH_MAX re-copy), the empty path is -ENOENT (:167-171, :201-206;
`getname` passes no LOOKUP_EMPTY, include/linux/fs.h:2944-2947, Linux v6.18.46), and a
copy that reaches PATH_MAX is -ENAMETOOLONG (:207-210).  None of the three
is in `openat_errnos`: each is what the fetch decides from the bytes, not
an answer the environment injects.  What the fetch stage does NOT accept is
`getname_flags`'s fourth answer, -ENOMEM, which Linux can give AHEAD of all
three: the pathname buffer allocation failing before a byte is copied
(:146-148) and the PATH_MAX re-copy's kzalloc failing (:189-192, Linux
v6.18.46).  The three arms answer their errno deterministically and refuse
that -ENOMEM — the same deliberate narrowing as the APPROXIMATION below,
at the same cost to the theorem.

ONLY THEN THE DIRFD: `path_init` resolves it (fs/namei.c:2589-2632, Linux v6.18.46)
inside `path_openat` (:4133), after `getname` and after the descriptor is
allocated (`do_sys_openat2`, fs/open.c:1431-1437, Linux v6.18.46).  A dirfd
other than AT_FDCWD (:2590, include/uapi/linux/fcntl.h:94, Linux v6.18.46) is a
relative-to-a-directory walk the model has no directory for, so it is
`unmodeled` — not -EBADF, which `fd_empty` would answer only for a
closed fd (:2607-2611).  `dirfd` arrives truncated to 32 bits
(`Syscall.fd32`), so AT_FDCWD is recognized in the low half (`AT_FDCWD32`).

APPROXIMATION, deliberate and shared by every arm that reports a
path-resolution errno deterministically: Linux can fail an openat with
-EMFILE or -ENFILE raised BEFORE path resolution, since `do_sys_openat2`
calls get_unused_fd_flags (fs/open.c:1435, Linux v6.18.46) and `path_openat` calls
alloc_empty_file (fs/namei.c:4124, Linux v6.18.46) before the walk — and with
-ENOMEM from that same file allocation (`alloc_empty_file`,
fs/file_table.c:258-260, Linux v6.18.46; its -ENFILE is :272-278) — where
those arms insist on the resolution errno.  The flat map carries an
unspoken premise of the same shape: `link_path_walk` asks `may_lookup` for
MAY_EXEC on the directory it stands in before every component
(fs/namei.c:2467-2469, Linux v6.18.46), so a working directory the task
cannot search answers -EACCES where these arms answer the map's -ENOENT
or a fresh descriptor.  The arms that accept `openat_errnos` accept that
-EACCES; the deterministic ones refuse it, on the premise that the run's
working directory is searchable.  This narrows the spec rather than
widening it; the list of arms and their `reject` twins is on Rocq's
`Open.openat_body_spec`.  Rocq: `Open.openat_body_spec`. -/
def openat_body_spec (i : SyscallInput) (m : Model) (dirfd pathp flags : word)
    : Sys SyscallEffect :=
  match read_cstr i.in_mem pathp with
  | CstrTooLong => err_ret ENAMETOOLONG
  | CstrFault => err_ret EFAULT
  | CstrOk p =>
      if path_eqb p [] then err_ret ENOENT
      else if !bv_eqb dirfd AT_FDCWD32 then unmodeled
      else openat_resolved_spec p flags m

/-- The flag gate first, as Linux has it: `build_open_flags` runs before
`getname` (`do_sys_openat2`, fs/open.c:1427-1431, Linux v6.18.46, commit
1f99e9ab748f), so a flag word the model does not interpret is
`unmodeled` BEFORE any pathname is fetched — in particular never one of
the pathname errnos, which the kernel would not reach for a combination
it rejects.  Rocq: `Open.openat_core_spec`. -/
def openat_core_spec (dirfd pathp flags : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if !modeled_open_flags flags then unmodeled
  else openat_body_spec i m dirfd pathp flags

/-- `openat dirfd path flags mode` (`SYSCALL_DEFINE4(openat, …)`,
fs/open.c:1463-1469, Linux v6.18.46, commit 1f99e9ab748f); `mode` is
ignored on every modeled shape.  The copy-in ledger records the pathname
bytes `getname` read, through the NUL, the first unmapped byte or
PATH_MAX (`State.cstr_access_len_aux`), whatever the outcome.  Rocq:
`Open.openat_spec`. -/
def openat_spec (dirfd pathp flags : word) : Sys SyscallEffect :=
  i <- input ;;
  record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    (openat_core_spec dirfd pathp flags)

/-! ## faccessat (48) and faccessat2 (439)

Both are `do_faccessat` (fs/open.c:467-537, Linux v6.18.46, commit
1f99e9ab748f): `SYSCALL_DEFINE3(faccessat, …)` (fs/open.c:539-542, Linux
v6.18.46) calls it with a constant zero flag word, and
`SYSCALL_DEFINE4(faccessat2, …)` (fs/open.c:544-548, Linux v6.18.46)
passes the caller's through.  The two specs share `faccessat_body_spec`
from the pathname fetch on, where the kernel's two entry points have
already converged; the flag word is the one thing `faccessat2_spec` adds,
and it is decided before the pathname is read, where `do_faccessat`
decides it.

The full arguments live in the Rocq docstrings: the WORLD precondition
(every key a regular file directly in the working directory, which holds
nothing else), the REAL-UID rule that makes the F_OK slice sound, the
ORDER of the gates, and what each accepted flag does.  Each definition
below names the Rocq definition whose docstring holds its argument, cites
the kernel lines the decision rests on, and keeps the one sentence of the
argument a reader needs to follow that citation.

The spellings that differ from Rocq are the file header's: the two
`Z.ldiff` residues are computed on the word, the `Z.land` test is a
`bv_and` on the words, and the `Z.lor` of three constants below `2^13` is
the `Nat` `|||` `Uapi` already uses.  No value changes. -/

/-- The two failures an F_OK probe of a name that RESOLVES may take
instead of 0, both from state the model does not track: -ENOMEM from the
walk's own dentry allocation — `__lookup_slow` (fs/namei.c:1789-1824,
Linux v6.18.46) asks `d_alloc_parallel` for it at :1801, and the
allocation failing is -ENOMEM (fs/dcache.c:2549-2554, Linux v6.18.46),
after the pathname has been read — and -EACCES from the search-permission
test `may_lookup` (fs/namei.c:1852-1874, Linux v6.18.46) takes on the
working directory in the first step of the walk.  The -ENOMEMs that
PRECEDE the copy — `getname_flags`' own (fs/namei.c:146-148, Linux
v6.18.46; its :189-192 needs a name past EMBEDDED_NAME_MAX, which no
answered arm reaches) and `access_override_creds`' (fs/open.c:418-465,
Linux v6.18.46; its failure is the -ENOMEM `do_faccessat` returns at
:486-489) — carry a ledger no answered arm records, and are refused with
it: the narrowing `faccessat_body_spec` names.  -ENOENT is not among
them: existence IS tracked.  Every errno a nonzero mode could add is behind a bit F_OK does
not set, and every one the environment could add is behind the WORLD
precondition; Rocq's `Open.faccessat_errnos` docstring lists both groups
and where each is gated. -/
def faccessat_errnos : List Int := [ENOMEM, EACCES]

/-- `mode` as `do_faccessat` reads it: `SYSCALL_DEFINE3(faccessat, …)`
(fs/open.c:539-542, Linux v6.18.46) declares it `int`, so the register's
high half is dropped (`Syscall.int32`).  Rocq: `Open.access_mode`. -/
def access_mode (mode : word) : Int := bv_unsigned (int32 mode)

/-- `if (mode & ~S_IRWXO) return -EINVAL;`, the opening statement of
`do_faccessat` (fs/open.c:475-476, Linux v6.18.46): a bit outside the low
three is the kernel's own -EINVAL, decided before the flag test and before
the pathname.  A negative mode lands here too, since its truncation sets
every high bit.  Rocq's residue is `Z.ldiff (access_mode mode) S_IRWXO`;
this is the same residue on the word.  Rocq: `Open.modeled_access_mode`. -/
def modeled_access_mode (mode : word) : Bool :=
  bv_unsigned (bv_and (int32 mode) (bv_not (Z_to_bv 64 S_IRWXO))) == 0

/-- F_OK: the zero mode, and the only one this model answers.  The mask
handed to `inode_permission` (fs/namei.c:568-602, Linux v6.18.46) is then
`0 | MAY_ACCESS`, which no DAC comparison reads, so the answer is
existence alone; R_OK, W_OK and X_OK need the mode bits and ids the flat
map does not hold.  Rocq: `Open.access_mode_f_ok`. -/
def access_mode_f_ok (mode : word) : Bool := access_mode mode == 0

/-- The one answer for a name that resolves: 0, or an untracked
environment failure from `faccessat_errnos`.  Both take a bare return
with every ledger empty and neither touches the model — faccessat is a
pure observation.  Rocq: `Open.access_exists_spec`. -/
def access_exists_spec : Sys SyscallEffect :=
  alt (e <- errno_from faccessat_errnos ;; err_ret e)
      (ret_only (Z_to_bv 64 0))

/-- The pathname half of `do_faccessat`, shared by both entry points
once the mode and flag gates have passed.  The fetch is `user_path_at`
(fs/namei.c:3211-3219, Linux v6.18.46), whose `getname_flags`
(fs/namei.c:136-216, Linux v6.18.46) answers -EFAULT for an unreadable
byte, -ENAMETOOLONG past PATH_MAX and -ENOENT for the empty string,
the last because LOOKUP_EMPTY is set only under AT_EMPTY_PATH, which
is declined before this point (:168-170).  A dirfd other than AT_FDCWD
is declined: `path_init` (fs/namei.c:2540-2645, Linux v6.18.46) would
start the walk at that descriptor's object (:2605-2632), which the flat map
does not hold.  "." and ".." are the working directory and its parent,
answered by `handle_dots` (fs/namei.c:2096-2132, Linux v6.18.46) with no
filesystem lookup, so both exist.  A name with a separator, a component
over NAME_MAX, and a name some key lives under are declined for the
reasons `Namei.unlinkat_body_spec` gives, the last one here to avoid a
wrong success-or-not rather than a wrong errno: a key "a/b" means a real
directory "a", whose F_OK is 0 where the map says -ENOENT.  On the map
itself this spec keeps Rocq's APPROXIMATION: an absent name answers
-ENOENT alone, refusing the -ENOMEM and -EACCES Linux can raise on it as
well (`faccessat_errnos` says where), and the fetch arms refuse the
-ENOMEM that precedes the copy — a narrowing, at the cost
`openat_body_spec` states above.  Rocq:
`Open.faccessat_body_spec`, whose docstring also names what no guard
restores (a real directory entry the map does not hold is a false
rejection, bugs/faccessat-sees-only-the-map.md). -/
def faccessat_body_spec (dirfd pathp : word) (i : SyscallInput) (m : Model) :
    Sys SyscallEffect :=
  match read_cstr i.in_mem pathp with
  | CstrTooLong => err_ret ENAMETOOLONG
  | CstrFault => err_ret EFAULT
  | CstrOk p =>
      if path_eqb p [] then err_ret ENOENT
      else if !bv_eqb dirfd AT_FDCWD32 then unmodeled
      else if path_eqb p dot_path then access_exists_spec
      else if path_eqb p dotdot_path then access_exists_spec
      else if path_has_slash p then unmodeled
      else if NAME_MAX < p.length then unmodeled
      else if fs_under (m_fs m) p then unmodeled
      else
        match fs_lookup (m_fs m) p with
        | none => err_ret ENOENT
        | some _ => access_exists_spec

/-- `faccessat dirfd path mode` (`SYSCALL_DEFINE3(faccessat, …)`,
fs/open.c:539-542, Linux v6.18.46, commit 1f99e9ab748f) is `do_faccessat`
(fs/open.c:467-537, Linux v6.18.46) with a constant zero flag word, so the
mode gate is the only one before the pathname: a bit outside S_IRWXO is
-EINVAL (:475-476) with nothing read, and a permission mode is declined,
also with nothing read.  Both arms sit outside the copy-in wrapper for
that reason: the -EINVAL is answered before `user_path_at` runs, so
recording a copy there would claim a read Linux did not make.  On F_OK
the ledger records the pathname bytes `getname` read, as `openat_spec`
records them.  Rocq: `Open.faccessat_spec`. -/
def faccessat_spec (dirfd pathp mode : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if !modeled_access_mode mode then err_ret EINVAL
  else if !access_mode_f_ok mode then unmodeled
  else
    record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (faccessat_body_spec dirfd pathp i m)

/-- `flags` as `do_faccessat` reads it: `SYSCALL_DEFINE4(faccessat2, …)`
(fs/open.c:544-548, Linux v6.18.46) declares it `int`, exactly as
`access_mode` reads the mode.  Rocq: `Open.access_flags`. -/
def access_flags (flags : word) : Int := bv_unsigned (int32 flags)

/-- The three flags `do_faccessat` accepts at all: `if (flags &
~(AT_EACCESS | AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH)) return -EINVAL;`
(fs/open.c:478-479, Linux v6.18.46).  Rocq's `Z.lor` of the three,
spelled as `Uapi` spells its own unions.  Rocq: `Open.access_flags_mask`. -/
def access_flags_mask : Int :=
  ((AT_EACCESS.toNat ||| AT_SYMLINK_NOFOLLOW.toNat ||| AT_EMPTY_PATH.toNat : Nat) : Int)

/-- The flag words the kernel accepts at all: no bit outside
`access_flags_mask`.  Like `modeled_access_mode` this is the kernel's
own -EINVAL, not a decline, and a negative flags word lands here for the
same reason a negative mode does.  Rocq: `Open.valid_access_flags`. -/
def valid_access_flags (flags : word) : Bool :=
  bv_unsigned (bv_and (int32 flags) (bv_not (Z_to_bv 64 access_flags_mask))) == 0

/-- The accepted flag words this model ANSWERS: those without
AT_EMPTY_PATH.  AT_EACCESS is read once, by `access_need_override_creds`
(fs/open.c:391-416, Linux v6.18.46; the early false at :395-396), which
decides whether `do_faccessat` installs the override cred through
`access_override_creds` (:486-489), and under F_OK neither cred changes
an answer; AT_SYMLINK_NOFOLLOW only
clears LOOKUP_FOLLOW (fs/open.c:481-482, Linux v6.18.46), which changes nothing in a
world with no symlink.  AT_EMPTY_PATH is declined, not -EINVAL, because the
kernel accepts it: it becomes LOOKUP_EMPTY (fs/open.c:483-484, Linux v6.18.46), under which
the empty string names the dirfd itself instead of answering -ENOENT — the
opposite of the arm `faccessat_body_spec` carries — so the decline is
unconditional in the flag and precedes the pathname read.  Rocq's test is
`Z.land (access_flags flags) AT_EMPTY_PATH`; this is the same bit on the
word.  Rocq: `Open.modeled_access_flags`, argued on `Open.faccessat2_spec`. -/
def modeled_access_flags (flags : word) : Bool :=
  bv_unsigned (bv_and (int32 flags) (Z_to_bv 64 AT_EMPTY_PATH)) == 0

/-- `faccessat2 dirfd path mode flags` (`SYSCALL_DEFINE4(faccessat2, …)`,
fs/open.c:544-548, Linux v6.18.46, commit 1f99e9ab748f): `do_faccessat`
(fs/open.c:467-537, Linux v6.18.46) with the caller's flag word.  The
gates in the kernel's order: the mode -EINVAL (:475-476), then the flag
-EINVAL (:478-479), both before `user_path_at` and both outside the
copy-in wrapper; only then the two declines, AT_EMPTY_PATH and a
permission mode.  The -EINVALs come before the mode decline on purpose:
`faccessat2(…, R_OK, garbage)` is a deterministic -EINVAL Linux decides
without the permission machinery this model lacks, and declining it would
refuse a trace Linux produces.  Rocq: `Open.faccessat2_spec`. -/
def faccessat2_spec (dirfd pathp mode flags : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if !modeled_access_mode mode then err_ret EINVAL
  else if !valid_access_flags flags then err_ret EINVAL
  else if !modeled_access_flags flags then unmodeled
  else if !access_mode_f_ok mode then unmodeled
  else
    record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (faccessat_body_spec dirfd pathp i m)

/-! ## close (57) -/

/-- `close fd` (`SYSCALL_DEFINE1(close, unsigned int, fd)`, fs/open.c:1574-1602,
Linux v6.18.46, commit 1f99e9ab748f): 0 on an open descriptor, which
leaves the table, and -EBADF on any other number.  `fd` arrives already
narrowed to 32 bits (`Syscall.fd32`, the table's spelling of the kernel's
`unsigned int` parameter), so `close(2^32)` closes stdin.

THE ORDER, from the entry point down.  `file_close_fd` (fs/file.c:850-860, Linux v6.18.46)
takes the table lock and hands the number to `file_close_fd_locked`
(fs/file.c:692-709, Linux v6.18.46), which answers NULL for a number at or past `max_fds`
(:699-700) or with no file installed (:703-704) — the -EBADF of
fs/open.c:1580-1581 (Linux v6.18.46) — and otherwise clears the slot and returns the number
to the allocator (fs/file.c:705-706); `__put_unused_fd` (fs/file.c:626-632, Linux v6.18.46) also
lowers `next_fd` to it when it was above (:630-631), and `alloc_fd`
(fs/file.c:570, Linux v6.18.46) finds the lowest free bit from there, which is
why the next open reuses the number.  The slot is gone BEFORE `filp_flush` (fs/open.c:1538-1556, Linux v6.18.46) and
`fput_close_sync` (fs/file_table.c:607-611, Linux v6.18.46) run — the kernel's own comment
at fs/open.c:1594 says a close cannot be restarted for that reason — so the arm is
one lookup and one removal, in that order, and the entry is removed
whatever its kind.

KIND-BLIND, as Rocq's arm is, and for a pipe that is load-bearing: what
`pipe_release` (fs/pipe.c:725-746, Linux v6.18.46) does that a program can observe is to
decrement `pipe->readers` or `pipe->writers` by the file's `f_mode`
(:730-733), and the model reads that count back off the fd table
(`State.pipe_end_live`) instead of carrying one.  The buffered bytes stay:
`put_pipe_info` (fs/pipe.c:709-722, Linux v6.18.46) frees the pipe only when its last
FILE goes (`!--pipe->files`, :714), and the model's `m_pipes` entry stays
whichever end is closed (`Checks/Cases/State.lean`'s
`pipe_table_survives_fd_remove`) — and stays when both are, where Linux
frees the pipe, a difference no program observes (the argument is on
`State/Pipes.lean`'s `pipe_new_id`).

WHAT IS NOT MODELED, and why the success arm commits to 0.  `filp_flush`
returns what `f_op->flush` answers (fs/open.c:1548-1549, Linux v6.18.46); the entry point
maps the four restart codes to -EINTR (:1594-1599) and returns anything
else as is (:1601).  None of the file operations listed here, the tables
behind the descriptor kinds this model hands out, defines `.flush` — `ext4_file_operations`
(fs/ext4/file.c, Linux v6.18.46) and `shmem_file_operations` (mm/shmem.c, Linux v6.18.46)
for a regular file, `ext4_dir_operations` (fs/ext4/dir.c, Linux v6.18.46) and
`simple_offset_dir_operations` (fs/libfs.c, Linux v6.18.46) for a directory,
`pipeanon_fops` (fs/pipe.c:1257-1266, Linux v6.18.46) for a pipe end — the
anonymous pipe's table, the one `create_pipe_files` (fs/pipe.c:944-957,
Linux v6.18.46) installs on both files; `pipefifo_fops` (fs/pipe.c:1246-1255,
Linux v6.18.46) is the named FIFO's, and has none either — `socket_file_ops`
(net/socket.c), `null_fops` (drivers/char/mem.c) and `urandom_fops`
(drivers/char/random.c), all Linux v6.18.46 — so on them the answer is the
0 of the `retval == 0` branch at fs/open.c:1591-1592, and Rocq's arm commits
to it the same way.  Two things that rests on.  First, a premise about the
filesystem under the run: a regular file on one whose `.flush` can fail —
FUSE's `fuse_flush` (fs/fuse/file.c:463-514, Linux v6.18.46) returns -EIO on
a bad inode and the writeback's error otherwise, NFS's `nfs_file_flush`
(fs/nfs/file.c:140-156, Linux v6.18.46) returns the writeback error of a
file open for writing — closes to that errno, which this arm never
answers.  `Fs` records no filesystem type to check against, so the 0 is
an environment premise of the kind `bugs/write-file-never-falls-short.md`
records for write, carried unstated by Rocq's arm: the pinned guest builds
neither filesystem (`testing/vm/kernel.fragment` leaves CONFIG_FUSE_FS and
CONFIG_NFS_FS unset) and puts the run's files on tmpfs, while a run under
qemu-user hands the call to the host kernel over whatever holds the host's
files.  Second, one table that does define a flush forwards rather than
fails: `ovl_file_operations` (fs/overlayfs/file.c:664, Linux v6.18.46) sets
`.flush = ovl_flush` (:674), and `ovl_flush` (fs/overlayfs/file.c:645-662,
Linux v6.18.46) returns the lower file's `.flush` or its initial 0 when
there is none (:649, :655-661), so over the tables above an overlay is
still 0.  Its error branch (:651-653) returns what `ovl_real_file`
(fs/overlayfs/file.c:174-196, Linux v6.18.46) fails with — a lowerdata
verification, a reopen of the upper file after a copy-up, a flag change
the lower file refuses — each a permission or resource condition of the
class (-ENOMEM, -EMFILE) every arm here leaves out, not a branch a
program's arguments select.  Rocq: `Open.close_spec`. -/
def close_spec (fd : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none   => err_ret EBADF                                   -- no file at the number: fs/open.c:1580-1581, Linux v6.18.46
  | some _ => set_fds (fd_remove (m_fds m) fd) ;; ret_only (Z_to_bv 64 0)
                                                              -- the slot cleared, the flush inert: 0

/-! ## ftruncate (46) -/

/-- The region a GROWING `ftruncate` must zero-fill is one the model can
represent.  The endpoint measured is the NEW LENGTH itself, and the
comparison is `ReadWrite.modeled_zero_fill`'s — the same one
`ReadWrite.modeled_file_gap` makes of a write's offset, for the same
reason: Linux extends a file into a HOLE for free, while the model holds
the file as a flat byte list and has to build the zeros
(`Fs.file_truncate`).

A SHRINK is always judged — for `len` at or below the current length the
subtraction is negative, so the comparison holds outright.  Note what
that does and does not buy: the bound is ONE-SIDED, an upper bound on
`len`, so it bounds `word_to_nat len` by `data.length + rw_bytes_max` in
BOTH directions.  A shrink is never free — `Fs.file_truncate` still
builds `word_to_nat len` for its `replicate` argument, a unary numeral
the size of the new length — it is merely never DECLINED.

The test is on `bv_unsigned len`, an `Int`, never on the `Nat` the
truncation builds: `ftruncate_spec` has already refused a negative
`len`, so the unsigned reading is the length the kernel saw, and a spec
that converted it to a unary numeral before testing it would build 2^30
constructors on `ftruncate(fd, 2^30)` (the probe's `guard-z` case) before
declining.  Rocq: `Open.modeled_truncate_gap`. -/
def modeled_truncate_gap (data : List byte) (len : word) : Bool :=
  ReadWrite.modeled_zero_fill (bv_unsigned len) data

/-- `ftruncate fd len` (`SYSCALL_DEFINE2(ftruncate, unsigned int, fd, off_t,
length)`, fs/open.c:213-216, Linux v6.18.46, commit 1f99e9ab748f): sets
the file's length to exactly `len` — a shrink drops the tail, a grow
zero-fills (`Fs.file_truncate`) — and answers 0.  `fd` arrives narrowed
to 32 bits (`Syscall.fd32`, the table's spelling of the `unsigned int`
parameter); `len` is the whole register, the `off_t`.

THE FD'S OFFSET IS NOT TOUCHED, and that is the fact this spec most has
to get right.  The entry point resolves the descriptor with `fdget`, not
`fdget_pos` (both declared in include/linux/file.h, Linux v6.18.46):
`do_sys_ftruncate` (fs/open.c:202-211, Linux v6.18.46)
opens `CLASS(fd, f)(fd)` (:206), the class include/linux/file.h:83
(Linux v6.18.46) defines over `fdget`, where `fd_pos` (:85) is the one
over `fdget_pos` — so the `f_pos` lock is never taken, and no assignment
to `f_pos` exists on the path `do_sys_ftruncate` → `do_ftruncate`
(fs/open.c:163-200) → `do_truncate` (fs/open.c:39-71) → `notify_change`
(fs/attr.c, all Linux v6.18.46).  Contrast `ksys_write`
(fs/read_write.c, Linux v6.18.46), which takes `fdget_pos` and writes
the position back.  So a shrink can leave the offset PAST end-of-file,
and the following write re-grows the file with a hole in between —
exactly what `Fs.file_write` already does for an lseek past the end.
The success arm therefore writes NO `set_fds`: the descriptor's entry,
offset included, is the one the call found.

CHECK ORDER, from the kernel and not from the man page, every line
Linux v6.18.46:

- `len` NEGATIVE as a signed 64-bit value is -EINVAL, decided BEFORE THE
  FD IS LOOKED UP: `do_sys_ftruncate` tests `length < 0` (fs/open.c:204-205)
  ahead of its `CLASS(fd, f)(fd)` (:206).  So `ftruncate(-1, -1)` is
  -EINVAL and not -EBADF, the ordering a spec written from the man page
  gets backwards.  The arm tests `bv_signed len < 0` first and reads no
  model until it has passed;
- an fd that is not open is -EBADF: `fd_empty(f)` (fs/open.c:207-208,
  Linux v6.18.46; `fd_empty`, include/linux/file.h:45, Linux v6.18.46);
- a channel, EITHER END OF A PIPE, a socket, /dev/null, /dev/urandom, a
  read-only file fd, or a directory fd is -EINVAL.  One kernel condition
  covers all of them, `!S_ISREG(inode->i_mode) || !(file->f_mode &
  FMODE_WRITE)` in `do_ftruncate` (fs/open.c:175-176, Linux v6.18.46),
  so a directory is
  -EINVAL and NOT -EISDIR (that errno belongs to `vfs_truncate`,
  fs/open.c:73, Linux v6.18.46, -EISDIR at :81-83, which only the
  path-based truncate(2) reaches), a pipe is -EINVAL and NOT
  -ESPIPE (an lseek errno that appears nowhere on this path), and the
  read-only file is -EINVAL and NOT write's -EBADF.  A channel answers
  -EINVAL whichever HALF of that condition it fails; under the tracer
  the harness's three are 1 MiB pipes (testing/vm/README.md), none
  S_ISREG.  (Rocq's prose names a `create_process` in
  testing/syscall-check/main.ml and a read-only regular stdin, which
  would fail on FMODE_WRITE instead; neither is in that file now.  This
  parenthesis is a correction of `Open.v`'s copy and is owed a deletion
  the day that copy is fixed.)
  What this arm assumes of the environment is the disjunction, not the
  pipe: no channel the model is handed is a writable regular file.
  THE WRITE END OF A PIPE is the case an access-mode reading of the
  condition gets wrong — it really does hold FMODE_WRITE,
  `create_pipe_files` (fs/pipe.c, Linux v6.18.46) opens it O_WRONLY — so
  it fails only the S_ISREG half; the arm consults the direction bit not at
  all.  The two character devices fail S_ISREG whatever mode they were
  opened with, so `FdDevNull`'s two mode bits are not read either;
- a writable file fd whose path is absent from `m_fs` is `unmodeled`; an
  `FdFileW`, an `FdFileA` and an `FdFileRW` always point into the fs (see
  openat), so this arm is
  unreachable rather than a judgement;
- a grow larger than `modeled_truncate_gap` permits is `unmodeled`, fail
  closed, decided after the fd checks Linux makes first.  The gate is
  the model's, not a kernel test, and the probe's `kinds` mode pins that
  a huge length on a non-writable fd is still the kernel's -EINVAL: a
  spec that hoisted the bound above the kind dispatch would decline
  there instead.

ONE BODY FOR THREE CONSTRUCTORS.  `do_ftruncate`'s test passes an O_WRONLY
description and an O_RDWR or O_APPEND one alike — O_APPEND rides on
O_WRONLY, which is what sets FMODE_WRITE, and the flag is read nowhere on
this path (`do_truncate` sets the size outright; O_APPEND belongs to
`generic_write_checks_count` in fs/read_write.c, Linux v6.18.46, under
`generic_write_checks`) — so `FdFileA`, `FdFileW` and `FdFileRW` share one
body, written twice as Rocq writes it: an `FdFileA` arm and an
`FdFileW | FdFileRW` arm.  The inode's APPEND-ONLY attribute is a
different thing and does bite on an `FdFileA` — `IS_APPEND(inode)` is
`do_ftruncate`'s own -EPERM (fs/open.c:183-184, Linux v6.18.46) — but it
is an inode attribute this model does not carry, exactly as for
`FdFileW`, and the list below already names it.

WHAT THIS SPEC DOES NOT MODEL, and therefore what it assumes of the
environment.  Four failures are named, each from state the model does
not carry; the list is the set a caller could plausibly reach, NOT an
exhaustive enumeration of what this path can return (`notify_change`,
fs/attr.c, Linux v6.18.46, adds at least -EOVERFLOW on an unmapped uid
or gid and a second LSM veto in `security_inode_setattr`,
security/security.c, Linux v6.18.46; its -EWOULDBLOCK from
`try_break_deleg`, include/linux/filelock.h, Linux v6.18.46, does not
reach this caller: `do_truncate` passes a NULL `delegated_inode`
(fs/open.c:67-68, Linux v6.18.46), which `notify_change`'s own header
says is fine for a caller holding the file open for write, as there can
be no conflicting delegation then; a filesystem's own `i_op->setattr`
adds more).
Each is listed with the DIRECTION that reaches it, a fact about where
the check sits: `inode_newsize_ok` (fs/attr.c:244-271, Linux v6.18.46)
consults the two SIZE limits solely in its `inode->i_size < offset`
branch (:248-255), and -ETXTBSY is that function's `else` arm
(:256-264), the exact complement of grow-only:

- -EFBIG past RLIMIT_FSIZE (fs/attr.c:251-253, Linux v6.18.46), which
  ALSO raises SIGXFSZ (:267-268), whose default action kills the process
  — GROW-ONLY;
- -EFBIG past the filesystem's `s_maxbytes` (fs/attr.c:254-255 and
  :269-270, Linux v6.18.46) — GROW-ONLY;
- -EPERM from `IS_APPEND` (fs/open.c:183-184, Linux v6.18.46; the macro,
  include/linux/fs.h:2556, Linux v6.18.46) and -EACCES from an LSM —
  `do_ftruncate`'s call at fs/open.c:186-188 (Linux v6.18.46) into
  `security_file_truncate` (security/security.c, Linux v6.18.46) — EITHER
  DIRECTION, and the only two of the four decided in `do_ftruncate`
  itself, before `do_truncate` is called;
- -ETXTBSY when the inode is an active swapfile (fs/attr.c:262-263, Linux
  v6.18.46) — SHRINK OR EQUAL, never a grow.

An immutable inode is -EPERM in either direction too where the
FILESYSTEM tests it, and nothing in the entry point does: on ext4 the
test is `IS_IMMUTABLE` in `ext4_setattr` (fs/ext4/inode.c, Linux
v6.18.46), reached through `notify_change` → `i_op->setattr` INSIDE
`do_truncate` (fs/open.c:68, Linux v6.18.46).  The VFS's own test in
`may_setattr` (fs/attr.c, Linux v6.18.46) fires only under
ATTR_MODE/UID/GID/TIMES_SET or ATTR_TOUCH, and the attributes this path
sets are ATTR_SIZE with the caller's `time_attrs` (fs/open.c:50, Linux
v6.18.46) — ATTR_MTIME | ATTR_CTIME from `do_ftruncate` (fs/open.c:195-196,
Linux v6.18.46) — and ATTR_FILE (fs/open.c:51-54, Linux v6.18.46), so it
does not; tmpfs's `shmem_setattr` (mm/shmem.c, Linux v6.18.46) has no
such test, so there nothing on this path refuses a writable fd opened
before the flag was set (a flag tmpfs takes only under
CONFIG_TMPFS_XATTR, through `shmem_fileattr_set` in mm/shmem.c, Linux
v6.18.46).  None is modeled, and no errno is invented for them: the spec
commits to 0 on a grow it accepts.  The
immutable and append-only cases cannot arise on a file the run itself
created through the modeled openat.  The two size limits are
assumptions about the environment, and the bound does NOT stand in for
either: `modeled_truncate_gap` bounds the per-call DELTA, while
`s_maxbytes` and RLIMIT_FSIZE bound the ABSOLUTE size, so no number of
in-bound calls is inductively safe.

RLIMIT_FSIZE is a PREMISE THE HARNESS CHECKS.  `inode_newsize_ok` reads
`rlimit(RLIMIT_FSIZE)`, the soft limit, and skips its -EFBIG-plus-SIGXFSZ
arm on exactly RLIM_INFINITY (fs/attr.c:251-253, Linux v6.18.46); this
spec's 0 on a grow is right under that value and only that value.
testing/syscall-check/main.ml reads the limit off the process image at
the exec stop and refuses the run unless it is RLIM_INFINITY; the only
writer that can LOWER it during the run is `do_prlimit` (kernel/sys.c,
Linux v6.18.46), reached through prlimit64, whose `Kernel.Sys` arm
declines every resource but RLIMIT_CORE, or through setrlimit (164),
which has no arm, so a program that lowers the limit fails closed at
that call and its later ftruncate is never graded against this 0
(tests/ftruncate_fsize.c pins both halves).  The model carries no rlimit
on purpose: an injectable -EFBIG here would allow -EFBIG on shrinks,
where no kernel produces it, and drop the SIGXFSZ that makes the process
die rather than see the errno.

`s_maxbytes` is the half nothing checks: the conformance cwd is tmpfs,
whose `s_maxbytes` is MAX_LFS_FILESIZE = LLONG_MAX on a 64-bit kernel
(`shmem_fill_super`, mm/shmem.c; include/linux/fs.h:1279, Linux
v6.18.46), and no ftruncate length exceeds that; on vfat's 4 GiB it is
reachable by accumulation, and the kernel's -EFBIG there is a 0 here
(bugs/ftruncate-no-file-size-limit.md).

-EROFS is deliberately absent, a source-grounded difference from
truncate(2)'s documented list: there is no `mnt_want_write` and no
`inode_permission` on the ftruncate path at all.  Write access was
settled at open time, so a read-only mount gives -EROFS at the openat
and an -EINVAL here on the O_RDONLY fd that results.

NO -EFBIG CONSTANT IS AVAILABLE, which is why `modeled_truncate_gap` is
the only thing standing at the top of the range.  `s_maxbytes` is a
per-filesystem value: Rocq's prose records, measured under qemu-riscv64,
`ftruncate(fd, 2^63-1)` answering 0 on tmpfs and on overlayfs and -EFBIG
on a virtiofs mount (this tree's recorded trace of the probe's `huge`
case is the tmpfs 0 alone).  The virtiofs -EFBIG is not the guest
kernel's own test — a FUSE superblock takes MAX_LFS_FILESIZE
(`fuse_sb_defaults`, fs/fuse/inode.c, Linux v6.18.46) and fs/fuse spells
no -EFBIG — but the server's answer to FUSE_SETATTR, relayed; the
in-kernel -EFBIG is `inode_newsize_ok`'s on a filesystem whose
`s_maxbytes` the length exceeds — vfat's `0xffffffff`, `fat_fill_super`,
fs/fat/inode.c:1663, Linux v6.18.46, for one
(bugs/ftruncate-no-file-size-limit.md).  So a spec that picked either
answer would be wrong in the other environment, and declining above the
bound is the only answer right in both — a decline, not an errno,
because the answer is the environment's to give.

THE KERNEL'S FOURTH CHECK, `small && length > MAX_NON_LFS` → -EINVAL
(fs/open.c:179-180, Linux v6.18.46; `MAX_NON_LFS`, include/linux/fs.h:1272,
Linux v6.18.46, is 2^31 - 1), is unreachable here rather than unmodeled.
`SYSCALL_DEFINE2(ftruncate, …)` passes `small = 1` (fs/open.c:215, Linux
v6.18.46), but `do_ftruncate` clears it on `O_LARGEFILE` (fs/open.c:170-171,
Linux v6.18.46), and every open on a 64-bit kernel sets that flag:
`SYSCALL_DEFINE4(openat, …)` ORs it in from `force_o_largefile()`
(fs/open.c:1466-1467, Linux v6.18.46), a macro include/linux/fcntl.h:24-25
(Linux v6.18.46) defines as `!IS_ENABLED(CONFIG_ARCH_32BIT_OFF_T)`, and
`ARCH_32BIT_OFF_T` (arch/Kconfig:395-397, Linux v6.18.46) `depends on
!64BIT`.  Measured:
`ftruncate(fd, 2^31)` answers 0 (the probe's `big31` case; above the
bound, so the model declines it).

THE SUCCESS ARM IS DETERMINISTIC on purpose — no `alt`, no
`Syscall.errno_from`.  Every failure a real kernel can raise on a grow
this small comes from state the model does not carry, and inventing an
injectable set for it would let a source and a target that really behave
differently share a trace set.  The narrowing is the one
`ReadWrite.write_spec` takes for short writes: fewer admitted outcomes,
none of them unsound.  Rocq: `Open.ftruncate_spec`. -/
def ftruncate_spec (fd len : word) : Sys SyscallEffect :=
  if bv_signed len < 0 then err_ret EINVAL   -- negative length: real -EINVAL, decided BEFORE the fd lookup (fs/open.c:204-205, Linux v6.18.46)
  else
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF                     -- fd not open: real -EBADF (fs/open.c:207-208, Linux v6.18.46)
  | some (.FdChannel _) => err_ret EINVAL     -- no channel is a writable regular file: real -EINVAL, not -ESPIPE
  | some (.FdSocket _) => err_ret EINVAL      -- a socket inode is S_ISSOCK: `do_ftruncate`'s !S_ISREG half (fs/open.c:175-176, Linux v6.18.46)
  | some (.FdPipe _ _) => err_ret EINVAL      -- either end: S_ISFIFO fails the same half, the write end's FMODE_WRITE notwithstanding
  | some (.FdDevNull _ _) => err_ret EINVAL   -- a character device is not S_ISREG, whatever the access mode
  | some .FdUrandom => err_ret EINVAL         -- a character device too, and read-only besides
  | some (.FdFile _ _) => err_ret EINVAL      -- open read-only: the !FMODE_WRITE half, real -EINVAL and not write's -EBADF
  | some .FdDir => err_ret EINVAL             -- a directory is not S_ISREG: real -EINVAL, not -EISDIR
  | some (.FdFileA p _) =>
      -- AN APPEND FD IS A WRITABLE REGULAR FILE, so it takes this body
      -- rather than the -EINVAL the kinds above get: O_APPEND rides on
      -- O_WRONLY, which is what sets FMODE_WRITE, and `do_ftruncate`
      -- reads the flag nowhere.  THE OFFSET IS UNTOUCHED, as for every
      -- other kind, so a shrink can leave `f_pos` past end-of-file —
      -- observable through `lseek(fd, 0, SEEK_CUR)`, and a decision here.
      match fs_lookup (m_fs m) p with
      | none => unmodeled                     -- an FdFileA always points into the fs; see openat
      | some data =>
          if (!modeled_truncate_gap data len) then unmodeled
          else
            set_fs (fs_set (m_fs m) p (file_truncate data len)) ;;
            ret_only (Z_to_bv 64 0)
  | some (.FdFileW p _) | some (.FdFileRW p _) =>
      -- ONE ARM FOR TWO KINDS: `do_ftruncate`'s test is
      -- `!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)`
      -- (fs/open.c:175-176, Linux v6.18.46), and an O_RDWR description
      -- passes both halves exactly as an O_WRONLY one does; nothing
      -- further down reads the access mode.
      match fs_lookup (m_fs m) p with
      | none => unmodeled                     -- a writable file fd always points into the fs; see openat
      | some data =>
          if (!modeled_truncate_gap data len) then unmodeled
            -- a zero-fill too large to build as a byte list; Linux makes
            -- the file sparse for free — see `modeled_truncate_gap`
          else
            set_fs (fs_set (m_fs m) p (file_truncate data len)) ;;
            ret_only (Z_to_bv 64 0)
            -- NO set_fds: the offset is untouched, see the docstring

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
