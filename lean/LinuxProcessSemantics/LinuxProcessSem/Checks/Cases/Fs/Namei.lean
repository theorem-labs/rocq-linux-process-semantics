import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.PreludeCore
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.TacticCore

/-! rocq-cases: b22b2a23f1adb9c4468cc1dcb8f15e53edf17745
covers: unlinkat_implied_directory_answers -- implied_directory_unlink_is_eisdir, implied_directory_unlink_answers_rejected, implied_directory_rmdir_is_enotempty, implied_directory_rmdir_answers_rejected
covers: unlinkat_implied_directory_trailing_slash -- implied_directory_trailing_slash_answers
covers: unlinkat_implied_directory_unrealizable_image -- unrealizable_image_answers, unrealizable_image_removal_rejected
covers: unlinkat_implied_directory_emptiness_unknown -- implied_directory_emptiness_unknown, implied_directory_emptiness_unknown_rejected
covers: unlinkat_implied_directory_removal -- implied_directory_removal
covers: unlinkat_implied_directory_removal_fd_guard -- implied_directory_removal_fd_guard
covers: unlinkat_implied_directory_edges -- implied_directory_without_an_entry, byte_prefix_shows_no_entry, over_name_max_precedes_implied_directory
covers: unlinkat_implied_directory_noop_components -- noop_components_show_the_entry, noop_components_removal_rejected, noop_components_edges
covers: unlinkat_byte_prefix_is_not_a_directory -- byte_prefix_is_not_a_directory
covers: unlinkat_bad_flags_records_no_copyin -- bad_flag_ledger_rejected
covers: unlinkat_bad_flags_empty_ledger_ok -- bad_flag_is_einval
covers: unlinkat_removal_needs_the_copyin -- removal_needs_the_ledger
covers: unlinkat_copyin_extent_is_the_nul_terminated_prefix -- ledger_extent_is_the_nul_terminated_prefix
covers: unlinkat_trailing_slash_on_a_file_is_enotdir -- trailing_slash_on_a_file_is_enotdir
covers: unlinkat_trailing_slash_success_rejected -- trailing_slash_success_rejected
covers: unlinkat_root_removedir_is_ebusy -- root_rmdir_is_ebusy
covers: unlinkat_root_enoent_rejected -- root_enoent_rejected
covers: unlinkat_absolute_basename_success_rejected -- absolute_basename_success_rejected
covers: unlinkat_absolute_basename_is_enoent -- absolute_basename_is_enoent
covers: unlinkat_tmp_key_not_held_is_enoent -- tmp_key_not_held_is_enoent, tmp_key_not_held_success_rejected
covers: unlinkat_tmp_removed_key_second_unlink_is_enoent -- tmp_removed_key_second_unlink_is_enoent, tmp_second_unlink_success_rejected
covers: unlinkat_tmp_declared_key_removed -- tmp_declared_key_removed
covers: unlinkat_tmp_image_key_removed -- tmp_image_key_removed
covers: unlinkat_tmp_excluded_shapes_unmodeled -- tmp_rmdir_declines, tmp_second_component_declines, tmp_directory_itself_declines
covers: unlinkat_tmp_implied_directory_is_eisdir -- tmp_implied_directory_is_eisdir, tmp_implied_directory_removal_rejected
covers: unlinkat_tmp_implied_directory_rmdir_declines -- tmp_implied_directory_rmdir_declines
covers: unlinkat_tmp_implied_directory_precedes_not_held -- tmp_implied_directory_enoent_rejected, tmp_not_held_beside_a_directory_is_enoent
covers: unlinkat_tmp_implied_directory_sibling_still_unlinks -- tmp_sibling_of_a_directory_still_unlinks
covers: unlinkat_tmp_name_max_boundary -- tmp_name_max_component_removed, tmp_over_name_max_declines
covers: unlinkat_tmp_nul_name_is_not_seeded -- tmp_nul_name_is_not_seeded -/

/-! # Checks.Cases.Fs.Namei — what `unlinkat` answers, read off against Linux

Worked examples over `Sys.Fs.Namei.unlinkat_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/Namei.v`.  Not part of the
trusted specification: this file is QA on the definition, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f).

HOW THESE ARE STATED.  A check is stated on the relation itself, as an
`iff` over EVERY outcome `o`, so one theorem fixes what is admitted and
what is refused; beside it, the concrete lie a kernel could tell is refuted
on its own.  Every proof is `sys_norm` or `sys_refute`
(`Checks/Cases/Tactic.lean`), which read the spec off its primitives once
the fixtures below have been registered: for each memory map, the pathname
`read_cstr` yields, so the match reduces on the first pass, and the ledger
length `cstr_access_len_aux` charges, so the copy-in ledger is a literal on
the first pass too; and the equations of `fs_lookup` and `fs_remove`, so
the lookup and the removal reduce there as well.  With those the whole call
is read on the first pass and the injectable-errno arm is read enumeration
first, which is what lets a refutation of an errno OUTSIDE
`unlinkat_errnos` close without a hand proof (the two-pass note in
`Checks/Cases/Tactic.lean` says why the order matters).  The ledger
lemmas are load-bearing rather than decorative: a closed
`cstr_access_len_aux` term left to the second pass is unrolled fuel by
fuel over a `bytes_at` map the ground evaluator cannot finish, and the
pass dies at the recursion limit.

The pins are grouped by the kernel function that decides them, in the
order the kernel reaches them: the flag word in `SYSCALL_DEFINE3(unlinkat)`,
`getname_flags`, `path_init`'s dirfd, `link_path_walk`'s typing of the
last component, the guards that keep the flat map honest, the lookup, and
the removal.  Each section names the lines and then pins the pairs of
neighbours, so an earlier check's answer is shown to hold when a later
check's condition also holds.

WHAT THE ROCQ FILE PINS.  Rocq keeps its examples over the executable
checker — the implied-directory guard on both images, the byte-prefix
contrast, the copy-in boundary from both sides and its extent, the trailing
separator and the all-separator path from both sides, and the absolute
multi-component shape of issue #562 — and sends everything else to a probe
(`testing/syscall-check/tests/unlinkat_spec.c`).  Every one of them
has a twin here, named in the header; the probe's cases are pinned as well,
one pin per deciding call, since the Lean tree has no replay harness yet.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins prove
is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Namei

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register lines the spec owes `sys_simp`

`Checks/Cases/Tactic.lean`'s header asks each spec for its unfolding
equation in the set; they are registered here, beside the pins that read
them, rather than in that file's register, because this port edits only its
own two files.  `record_copyins` is a calling-convention wrapper of
`Sys/Syscall.lean`, and the equations of `fs_lookup`, `fs_remove` and
`fs_rmdir_implied` are what let the lookup and the two removals reduce on
the first pass; those, and
the `fixture_of` unfolding, are registered `local`, so that a file
importing this one does not inherit a choice made for these pins (the
fixture facts below are keyed on this file's own literals and inert
elsewhere).  The /tmp gate is never unfolded: `tmp_name` and the
trailing-separator strip enter through closed facts per path
(`tmp_literal_paths_typed`, `tmp_gif_typed`, `long_tmp_names_typed`), because
a generic unfolding would fire on the still-symbolic pathname inside the
`read_cstr` match's arms before the match reduces, and the closed fact a
long key needs would then find nothing to match. -/

attribute [sys_simp low] unlinkat_spec.eq_1 unlinkat_body_spec.eq_1 unlinkat_errnos.eq_1
attribute [sys_simp low] unlink_found_spec.eq_1 unlinkat_tmp_spec.eq_1 rmdir_implied_spec.eq_1
attribute [local sys_simp low] record_copyins.eq_1 fixture_of.eq_1
attribute [local sys_simp low] fs_lookup.eq_1 fs_lookup.eq_2 fs_remove.eq_1 fs_remove.eq_2
attribute [local sys_simp low] fs_rmdir_implied.eq_1 fs_rmdir_implied.eq_2

/-! ## The constants these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each one is. -/

/-- The `AT_` words the flag pins spell out — 512 is `AT_REMOVEDIR`, 4096
`AT_EMPTY_PATH`, 256 `AT_SYMLINK_NOFOLLOW` — are pinned to
include/uapi/linux/fcntl.h by `at_words` in `Checks/Cases/Sys/Uapi/Fs.lean`;
this restates the three numerals in one place.
model: the model's own constants at numerals; the header reading is `Checks.Cases.Sys.Uapi.Fs.at_words`. -/
example : AT_REMOVEDIR = 512 ∧ AT_EMPTY_PATH = 4096 ∧ AT_SYMLINK_NOFOLLOW = 256 := by decide
/-- `NAME_MAX` is 255 and `PATH_MAX` 4096, counting the NUL.
kernel: include/uapi/linux/limits.h:NAME_MAX,PATH_MAX@v6.18.46 -/
example : NAME_MAX = 255 ∧ path_max = 4096 := by decide

/-- The dirfd as the arm sees it: `AT_FDCWD` after the `int dfd` narrowing
the table applies (`Syscall.fd32`), the low 32 bits of -100.
model: the model's own constant at a numeral; the kernel reading is on `dirfd_2_pow_32_minus_100_is_at_fdcwd` below. -/
def cwd_fd : word := AT_FDCWD32

/-- …which is 2^32 - 100.
model: the model's own constant at a numeral; the kernel reading is on `dirfd_2_pow_32_minus_100_is_at_fdcwd` below. -/
theorem cwd_fd_is_2_pow_32_minus_100 : cwd_fd = 4294967196 := by decide

/-! ## The fixtures

Every pathname a check names is laid out at 8192, NUL-terminated, and
nothing else is readable; the spec reads no other memory.  The single-byte
names read as the letters they stand for: `a` = 97, `b` = 98, `c` = 99,
`.` = 46, `/` = 47. -/

/-- The bytes of `bs` at 8192 followed by a NUL, and nothing else readable. -/
def name_at (bs : List byte) : word → Option byte := bytes_at 8192 (bs ++ [0])

/-- No byte readable at all: a NULL or unmapped pathname pointer. -/
def unmapped : word → Option byte := fun _ => none

/-- One byte of name and then nothing readable: the byte where the NUL
would be is unreadable (the map is per byte; a process would see this at a
page end). -/
def unterminated : word → Option byte := bytes_at 8192 [97]

/-- Every byte readable and none of them NUL: a name with no end. -/
def endless : word → Option byte := fun _ => some 97

/-- A component of exactly `NAME_MAX` bytes, and one of `NAME_MAX + 1`. -/
def name255 : List byte := List.replicate 255 97
def name256 : List byte := List.replicate 256 97

/-- "/tmp/out.gif", the name the fuzz harness of issue #562 unlinks, and
its last component "out.gif". -/
def abs_gif_name : List byte := [47, 116, 109, 112, 47, 111, 117, 116, 46, 103, 105, 102]
def gif_basename : List byte := [111, 117, 116, 46, 103, 105, 102]

/-- `unlinkat(dirfd, 8192, flags)` as the dispatcher sees it: syscall 35,
the pathname pointer in a1, `mem` readable and nothing writable. -/
def unlink_in (dirfd flags : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 35 [dirfd, 8192, flags, 0, 0, 0] mem (fun _ => none)

/-- The input a spec-level pin hands the arm.  Only its memory is read
there — the arm takes dirfd, pathname and flags as arguments — so the
register values are the ones every such call would carry. -/
def mem_in (mem : word → Option byte) : SyscallInput := unlink_in AT_FDCWD 0 mem

attribute [sys_simp low] unlink_in.eq_1 mem_in.eq_1

/-- The process every check starts from, spelled through `fixture_of` so
that it enters the normal form by the same unfolding as every other
fixture here (`demo_model_eq_fixture_of` says it is `demo_model`). -/
def empty_model : Model := fixture_of

/-- A file `a` holding one byte, and the same process with it removed. -/
def unlink_model : Model := fixture_of (fs := [([97], [104])])
def unlinked_model : Model := fixture_of (fs := [])

/-- Rocq's byte-prefix image: `a` (empty) and `ab`, and the image after `a`
is removed.  `ab` does not live UNDER `a`. -/
def ab_model : Model := fixture_of (fs := [([97], []), ([97, 98], [104])])
def ab_unlinked_model : Model := fixture_of (fs := [([97, 98], [104])])

/-- A key living UNDER a name means reality has a DIRECTORY that the flat
map only implies.  This image holds `a/b` and NOT `a`, which is the
REALIZABLE shape: a real directory `a` containing a file `b` contributes
exactly the one key.  `unrealizable_model` holds both — a tree that cannot
exist, since `a` cannot be a regular file and a directory at once —
which `Fs.valid_fs` allows anyway. -/
def implied_dir_model : Model := fixture_of (fs := [([97, 47, 98], [104])])
def unrealizable_model : Model := fixture_of (fs := [([97], []), ([97, 47, 98], [104])])

/-- A key that says `a` is a directory and nothing about what is in it,
`a/../b`, alone and beside a key that does show an entry in `a`, `a/c`. -/
def dotdot_key_model : Model := fixture_of (fs := [([97, 47, 46, 46, 47, 98], [104])])
def dotdot_and_entry_model : Model :=
  fixture_of (fs := [([97, 47, 46, 46, 47, 98], [104]), ([97, 47, 99], [])])

/-- Keys that imply `a` and show nothing in it, `a/` and `a/.`; a key `ab/c`
beside `a/../b`, which shows nothing in `a` either; and a key under a
256-byte name. -/
def slash_key_model : Model := fixture_of (fs := [([97, 47], [104])])
def dot_key_model : Model := fixture_of (fs := [([97, 47, 46], [104])])
def byte_prefix_entry_model : Model :=
  fixture_of (fs := [([97, 47, 46, 46, 47, 98], [104]), ([97, 98, 47, 99], [])])
def long_key_model : Model := fixture_of (fs := [(name256 ++ [47, 98], [104])])

/-- Keys whose separator runs and "." components leave the walk inside `a`
(`path_skip_noop_components`): `a/./b`, `a//b` and `a/.//./b` show `b` in
`a`; `a/./../b` and `a/./` show nothing in it; `a/.b` shows the name `.b`. -/
def dot_entry_model : Model := fixture_of (fs := [([97, 47, 46, 47, 98], [104])])
def slash_entry_model : Model := fixture_of (fs := [([97, 47, 47, 98], [104])])
def mixed_entry_model : Model := fixture_of (fs := [([97, 47, 46, 47, 47, 46, 47, 98], [104])])
def dot_dotdot_key_model : Model := fixture_of (fs := [([97, 47, 46, 47, 46, 46, 47, 98], [104])])
def dot_slash_key_model : Model := fixture_of (fs := [([97, 47, 46, 47], [104])])
def dot_name_entry_model : Model := fixture_of (fs := [([97, 47, 46, 98], [104])])

/-- What the removal of an implied directory `a` that shows no entry leaves
(`fs_rmdir_implied`): `a/../b` becomes `b`; beside `ab/c`, which does not
pass through `a`, the same; and, from one image holding every shape, `a/`,
`a/..` and `a/../` go, `a/../../c` becomes `../c`, `a/./..//b` becomes `b`
and `ab` stays.  `clash_model` holds `a/../b` beside `b`, the same file
spelled twice; the removal keeps the earlier key's contents. -/
def dotdot_removed_model : Model := fixture_of (fs := [([98], [104])])
def byte_prefix_removed_model : Model := fixture_of (fs := [([97, 98, 47, 99], []), ([98], [104])])
def shapes_model : Model :=
  fixture_of (fs := [([97, 47], [1]), ([97, 47, 46, 46], [2]), ([97, 47, 46, 46, 47], [3]),
    ([97, 47, 46, 46, 47, 46, 46, 47, 99], [4]), ([97, 47, 46, 47, 46, 46, 47, 47, 98], [5]),
    ([97, 98], [6])])
def shapes_removed_model : Model :=
  fixture_of (fs := [([46, 46, 47, 99], [4]), ([97, 98], [6]), ([98], [5])])
def clash_model : Model := fixture_of (fs := [([97, 47, 46, 46, 47, 98], [104]), ([98], [105])])

/-- `a/../b` with the file held open through fd 3 under that key; and
`a/../b` beside `x`, with fd 3 on `x`, a key the removal leaves alone, and
that image after the removal. -/
def dotdot_held_model : Model :=
  fixture_of (fds := init_fds ++ [(3, .FdFile [97, 47, 46, 46, 47, 98] 0)])
    (fs := [([97, 47, 46, 46, 47, 98], [104])])
def dotdot_other_held_model : Model :=
  fixture_of (fds := init_fds ++ [(3, .FdFile [120] 0)])
    (fs := [([97, 47, 46, 46, 47, 98], [104]), ([120], [1])])
def dotdot_other_held_removed_model : Model :=
  fixture_of (fds := init_fds ++ [(3, .FdFile [120] 0)])
    (fs := [([98], [104]), ([120], [1])])

/-- `a/b`, which shows an entry in `a`, held open through fd 3. -/
def implied_dir_held_model : Model :=
  fixture_of (fds := init_fds ++ [(3, .FdFile [97, 47, 98] 0)]) (fs := [([97, 47, 98], [104])])

/-- A directory the name `a` has nothing to do with: the key `b/c`. -/
def bc_model : Model := fixture_of (fs := [([98, 47, 99], [104])])

/-- An image whose one key is the twelve bytes of "/tmp/out.gif" itself. -/
def abs_gif_model : Model := fixture_of (fs := [(abs_gif_name, [104])])

/-- The file `a` held open through fd 3, read-only and then for writing. -/
def open_fd_model : Model :=
  fixture_of (fds := init_fds ++ [(3, .FdFile [97] 0)]) (fs := [([97], [104])])
def open_wfd_model : Model :=
  fixture_of (fds := init_fds ++ [(3, .FdFileW [97] 5)]) (fs := [([97], [104])])

/-- Every fd kind that names NO path — a directory, a fresh socket, both
ends of one pipe, /dev/null, /dev/urandom — plus a read fd AND a write fd on the
OTHER file `b` (so both file arms are held to comparing the path), over an
image holding `a` and `b`; and the same process with `a` removed. -/
def kinds_fds : List (word × FdEntry) :=
  init_fds ++ [(3, .FdDir), (4, .FdSocket .SkFresh), (5, .FdPipe 0 false),
               (6, .FdPipe 0 true), (7, .FdDevNull true true), (8, .FdFile [98] 0),
               (9, .FdUrandom), (10, .FdFileW [98] 5)]
def kinds_model : Model :=
  fixture_of (fds := kinds_fds) (pipes := [(0, ([], 0))]) (fs := [([97], [104]), ([98], [104])])
def kinds_unlinked_model : Model :=
  fixture_of (fds := kinds_fds) (pipes := [(0, ([], 0))]) (fs := [([98], [104])])

/-- The same kinds placed AHEAD of a file fd on `a` ITSELF.  `fd_names_path`
is an or-fold down the table, so an arm that answered `true` would mask
nothing but an arm that short-circuited to `false` would hide the file fd
behind it and accept the removal; every other fixture puts the file fd first
or on another name, where the two shapes answer alike. -/
def kinds_before_open_fd : List (word × FdEntry) :=
  init_fds ++ [(3, .FdDir), (4, .FdSocket .SkFresh), (5, .FdPipe 0 false),
               (6, .FdPipe 0 true), (7, .FdDevNull true true), (8, .FdUrandom),
               (9, .FdFile [97] 0)]
def kinds_before_open_fd_model : Model :=
  fixture_of (fds := kinds_before_open_fd) (pipes := [(0, ([], 0))]) (fs := [([97], [104])])

/-- A name of the bytes 0xff 0x01, which no text encoding would call a name. -/
def hi_model : Model := fixture_of (fs := [([255, 1], [99])])

/-- The run's declared /tmp holding "out.gif", as `State.fs_seed_tmp` puts
it in the image: the same model as `abs_gif_model` (`tmp_declared_seeds_the_key`
says so), which is what makes a declared entry and an image key that spells
the same path one thing. -/
def tmp_declared_model : Model := fixture_of (fs := fs_seed_tmp [] [(gif_basename, [104])])

/-- "/tmp/d/f" and "/tmp/out.gif" held: the first is a second component,
and it makes "/tmp/d" an implied directory inside /tmp. -/
def tmp_shapes_model : Model :=
  fixture_of (fs := [([47, 116, 109, 112, 47, 100, 47, 102], [104]), (abs_gif_name, [104])])

/-- "/tmp/d/f" alone, as the Rocq case declares it: "/tmp/d" is implied and
nothing else is held, the image on which a not-held name is read beside an
implied directory and beside nothing else. -/
def tmp_only_dir_model : Model :=
  fixture_of (fs := [([47, 116, 109, 112, 47, 100, 47, 102], [104])])

/-- The UNREALIZABLE image inside /tmp: "/tmp/d" and "/tmp/d/f" both keys,
where the lookup of "/tmp/d" would succeed. -/
def tmp_unrealizable_model : Model :=
  fixture_of (fs := [([47, 116, 109, 112, 47, 100], [104]),
                     ([47, 116, 109, 112, 47, 100, 47, 102], [104])])

/-- The UNREALIZABLE image holding keys spelled "/tmp/." and "/tmp/.." beside
"/tmp/out.gif": no directory can hold an entry named "." or "..", so no
syscall builds it, and `Fs.valid_fs` allows it anyway.  It is the image on
which `tmp_name`'s two dot tests become observable — with a key at either
spelling, a gate that let "." or ".." through as a component would find the
key and remove it. -/
def tmp_dot_keys_model : Model :=
  fixture_of (fs := [([47, 116, 109, 112, 47, 46], [104]), ([47, 116, 109, 112, 47, 46, 46], [104]),
                     (abs_gif_name, [104])])

/-- A key spelling "/abc/x": five bytes of prefix that are not "/tmp/". -/
def abc_x_model : Model := fixture_of (fs := [([47, 97, 98, 99, 47, 120], [104])])

/-- "/tmp/out.gif" held open through fd 3. -/
def tmp_open_fd_model : Model :=
  fixture_of (fds := init_fds ++ [(3, .FdFile abs_gif_name 0)]) (fs := [(abs_gif_name, [104])])

/-- The two long keys under /tmp: "/tmp/" followed by 255 and by 256 bytes. -/
def tmp_name255_model : Model := fixture_of (fs := [(tmp_key name255, [104])])
def tmp_name256_model : Model := fixture_of (fs := [(tmp_key name256, [104])])

attribute [sys_simp low]
  empty_model.eq_1 unlink_model.eq_1 unlinked_model.eq_1 ab_model.eq_1 ab_unlinked_model.eq_1
  implied_dir_model.eq_1 unrealizable_model.eq_1 bc_model.eq_1 abs_gif_model.eq_1
  open_fd_model.eq_1 open_wfd_model.eq_1 kinds_model.eq_1 kinds_unlinked_model.eq_1
  kinds_before_open_fd_model.eq_1 hi_model.eq_1 tmp_declared_model.eq_1 tmp_shapes_model.eq_1
  tmp_unrealizable_model.eq_1 tmp_only_dir_model.eq_1 tmp_dot_keys_model.eq_1 abc_x_model.eq_1
  tmp_open_fd_model.eq_1 tmp_name255_model.eq_1
  tmp_name256_model.eq_1 dotdot_key_model.eq_1 dotdot_and_entry_model.eq_1
  slash_key_model.eq_1 dot_key_model.eq_1 byte_prefix_entry_model.eq_1 long_key_model.eq_1
  dot_entry_model.eq_1 slash_entry_model.eq_1 mixed_entry_model.eq_1 dot_dotdot_key_model.eq_1
  dot_slash_key_model.eq_1 dot_name_entry_model.eq_1 dotdot_removed_model.eq_1
  byte_prefix_removed_model.eq_1 shapes_model.eq_1 shapes_removed_model.eq_1 clash_model.eq_1
  dotdot_held_model.eq_1 dotdot_other_held_model.eq_1 dotdot_other_held_removed_model.eq_1
  implied_dir_held_model.eq_1

/-- The effect of an arm past the flag test: a return value under the
pathname ledger, `n` bytes read from 8192 — the NUL-terminated prefix, the
prefix through the first unreadable byte, or PATH_MAX. -/
def ledgered (r : word) (n : Nat) : SyscallEffect := with_copyins [(8192, n)] (mkEffect r [] [])

/-- What the removal arm admits besides the removal: one of the five
untracked environment failures of `unlinkat_errnos`, the model unchanged.
The kernel line behind each member is on the five `removal_*_admitted`
pins below. -/
def env_failure (o : outcome SyscallEffect) (n : Nat) (m : Model) : Prop :=
  o = Ok (ledgered (errno_ret ENOMEM) n) m []
  ∨ o = Ok (ledgered (errno_ret EACCES) n) m []
  ∨ o = Ok (ledgered (errno_ret EPERM) n) m []
  ∨ o = Ok (ledgered (errno_ret EROFS) n) m []
  ∨ o = Ok (ledgered (errno_ret EBUSY) n) m []

attribute [sys_simp low] ledgered.eq_1 env_failure.eq_1

/-! ### The fixtures' readings

Two closed facts per memory map, read off once and registered at the
default priority, ahead of the spec's unfolding: the pathname `read_cstr`
yields, so the match reduces on the first pass, and the ledger length
`cstr_access_len_aux` charges for it, so the copy-in ledger is a literal on
the first pass too.  The pathname argument of a dispatcher-level call is
read off the input the same way.

The long fixtures need a larger recursion budget than the default 512:
`decide` evaluates a 255-byte list, and the PATH_MAX walk of `endless`, by
structural recursion whose depth is the length, and the kernel's check of
a pin over such a fixture recurses as deep as the fixture is long even
though the pin rewrites with the closed fact.  The raised budget is scoped
by `set_option … in` to those lemmas and to the pins that use them, and
nowhere else — the arrangement `Checks/Cases/Sys/Uapi/Fs.lean` uses
for its 128-byte `stat` buffers. -/

/-- Reading "a", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_a : read_cstr (name_at [97]) 8192 = CstrOk [97] ∧
    cstr_access_len_aux (name_at [97]) 8192 path_max = 2 := by decide
/-- Reading "a/", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_a_slash : read_cstr (name_at [97, 47]) 8192 = CstrOk [97, 47] ∧
    cstr_access_len_aux (name_at [97, 47]) 8192 path_max = 3 := by decide
/-- Reading "a//", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_a_slash_slash : read_cstr (name_at [97, 47, 47]) 8192 = CstrOk [97, 47, 47] ∧
    cstr_access_len_aux (name_at [97, 47, 47]) 8192 path_max = 4 := by decide
/-- Reading "/", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_root : read_cstr (name_at [47]) 8192 = CstrOk [47] ∧
    cstr_access_len_aux (name_at [47]) 8192 path_max = 2 := by decide
/-- Reading "//", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_root2 : read_cstr (name_at [47, 47]) 8192 = CstrOk [47, 47] ∧
    cstr_access_len_aux (name_at [47, 47]) 8192 path_max = 3 := by decide
/-- Reading ".", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_dot : read_cstr (name_at [46]) 8192 = CstrOk [46] ∧
    cstr_access_len_aux (name_at [46]) 8192 path_max = 2 := by decide
/-- Reading "./", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_dot_slash : read_cstr (name_at [46, 47]) 8192 = CstrOk [46, 47] ∧
    cstr_access_len_aux (name_at [46, 47]) 8192 path_max = 3 := by decide
/-- Reading "..", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_dotdot : read_cstr (name_at [46, 46]) 8192 = CstrOk [46, 46] ∧
    cstr_access_len_aux (name_at [46, 46]) 8192 path_max = 3 := by decide
/-- Reading "../", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_dotdot_slash : read_cstr (name_at [46, 46, 47]) 8192 = CstrOk [46, 46, 47] ∧
    cstr_access_len_aux (name_at [46, 46, 47]) 8192 path_max = 4 := by decide
/-- Reading "", and its ledger: the NUL alone.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_empty : read_cstr (name_at []) 8192 = CstrOk [] ∧
    cstr_access_len_aux (name_at []) 8192 path_max = 1 := by decide
/-- Reading "a/b", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_a_slash_b : read_cstr (name_at [97, 47, 98]) 8192 = CstrOk [97, 47, 98] ∧
    cstr_access_len_aux (name_at [97, 47, 98]) 8192 path_max = 4 := by decide
/-- Reading "a/b/", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_a_slash_b_slash :
    read_cstr (name_at [97, 47, 98, 47]) 8192 = CstrOk [97, 47, 98, 47] ∧
    cstr_access_len_aux (name_at [97, 47, 98, 47]) 8192 path_max = 5 := by decide
/-- Reading "./a", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_dot_slash_a : read_cstr (name_at [46, 47, 97]) 8192 = CstrOk [46, 47, 97] ∧
    cstr_access_len_aux (name_at [46, 47, 97]) 8192 path_max = 4 := by decide
/-- Reading "/a", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_slash_a : read_cstr (name_at [47, 97]) 8192 = CstrOk [47, 97] ∧
    cstr_access_len_aux (name_at [47, 97]) 8192 path_max = 3 := by decide
/-- Reading "/tmp/out.gif", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_abs_gif : read_cstr (name_at abs_gif_name) 8192 = CstrOk abs_gif_name ∧
    cstr_access_len_aux (name_at abs_gif_name) 8192 path_max = 13 := by decide
/-- Reading "out.gif", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_gif_basename : read_cstr (name_at gif_basename) 8192 = CstrOk gif_basename ∧
    cstr_access_len_aux (name_at gif_basename) 8192 path_max = 8 := by decide
/-- Reading "...", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_dot3 : read_cstr (name_at [46, 46, 46]) 8192 = CstrOk [46, 46, 46] ∧
    cstr_access_len_aux (name_at [46, 46, 46]) 8192 path_max = 4 := by decide
/-- Reading "ab", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_ab : read_cstr (name_at [97, 98]) 8192 = CstrOk [97, 98] ∧
    cstr_access_len_aux (name_at [97, 98]) 8192 path_max = 3 := by decide
/-- Reading "b", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_b : read_cstr (name_at [98]) 8192 = CstrOk [98] ∧
    cstr_access_len_aux (name_at [98]) 8192 path_max = 2 := by decide
/-- Reading the two high bytes, and their ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_hi : read_cstr (name_at [255, 1]) 8192 = CstrOk [255, 1] ∧
    cstr_access_len_aux (name_at [255, 1]) 8192 path_max = 3 := by decide
/-- An unmapped pointer faults on its first byte, which is the one byte the
ledger charges.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_unmapped : read_cstr unmapped 8192 = CstrFault ∧
    cstr_access_len_aux unmapped 8192 path_max = 1 := by decide
/-- A name whose NUL is unreadable faults too, after the byte read and the
byte that faulted.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_unterminated : read_cstr unterminated 8192 = CstrFault ∧
    cstr_access_len_aux unterminated 8192 path_max = 2 := by decide

set_option maxRecDepth 8192 in
/-- Reading the 255-byte name, and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_name255 : read_cstr (name_at name255) 8192 = CstrOk name255 ∧
    cstr_access_len_aux (name_at name255) 8192 path_max = 256 := by decide
set_option maxRecDepth 8192 in
/-- Reading the 256-byte name, and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_name256 : read_cstr (name_at name256) 8192 = CstrOk name256 ∧
    cstr_access_len_aux (name_at name256) 8192 path_max = 257 := by decide
set_option maxRecDepth 32768 in
/-- A name with no NUL in PATH_MAX bytes is too long, and the ledger is the
whole PATH_MAX window.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_endless : read_cstr endless 8192 = CstrTooLong ∧
    cstr_access_len_aux endless 8192 path_max = 4096 := by decide

set_option maxRecDepth 8192 in
/-- The two long names as the gates see them: no separator to strip, none
inside, the byte past the component NUL, and the lengths that sit either
side of NAME_MAX.  The predicates mirror `link_path_walk`'s splitting
(fs/namei.c:2450-2505, Linux v6.18.46): no separator anywhere, so one
component, and NUL past it.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem long_names_typed :
    path_strip_trailing_slashes name255 = name255 ∧ path_has_slash name255 = false
      ∧ path_trailing_slash name255 = false ∧ name255.length = 255
      ∧ path_strip_trailing_slashes name256 = name256 ∧ path_has_slash name256 = false
      ∧ path_trailing_slash name256 = false ∧ name256.length = 256 := by decide

/-- Reading "/tmp", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_tmp_dir : read_cstr (name_at [47, 116, 109, 112]) 8192 = CstrOk [47, 116, 109, 112] ∧
    cstr_access_len_aux (name_at [47, 116, 109, 112]) 8192 path_max = 5 := by decide
/-- Reading "/tmp/", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_tmp_slash :
    read_cstr (name_at [47, 116, 109, 112, 47]) 8192 = CstrOk [47, 116, 109, 112, 47] ∧
    cstr_access_len_aux (name_at [47, 116, 109, 112, 47]) 8192 path_max = 6 := by decide
/-- Reading "/tmp/.", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_tmp_dot :
    read_cstr (name_at [47, 116, 109, 112, 47, 46]) 8192 = CstrOk [47, 116, 109, 112, 47, 46] ∧
    cstr_access_len_aux (name_at [47, 116, 109, 112, 47, 46]) 8192 path_max = 7 := by decide
/-- Reading "/tmp/..", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_tmp_dotdot :
    read_cstr (name_at [47, 116, 109, 112, 47, 46, 46]) 8192 = CstrOk [47, 116, 109, 112, 47, 46, 46] ∧
    cstr_access_len_aux (name_at [47, 116, 109, 112, 47, 46, 46]) 8192 path_max = 8 := by decide
/-- Reading "/tmp/d", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_tmp_d :
    read_cstr (name_at [47, 116, 109, 112, 47, 100]) 8192 = CstrOk [47, 116, 109, 112, 47, 100] ∧
    cstr_access_len_aux (name_at [47, 116, 109, 112, 47, 100]) 8192 path_max = 7 := by decide
/-- Reading "/tmp/d/f", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_tmp_df :
    read_cstr (name_at [47, 116, 109, 112, 47, 100, 47, 102]) 8192
      = CstrOk [47, 116, 109, 112, 47, 100, 47, 102] ∧
    cstr_access_len_aux (name_at [47, 116, 109, 112, 47, 100, 47, 102]) 8192 path_max = 9 := by decide
/-- Reading "/abc/x", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_abc_x :
    read_cstr (name_at [47, 97, 98, 99, 47, 120]) 8192 = CstrOk [47, 97, 98, 99, 47, 120] ∧
    cstr_access_len_aux (name_at [47, 97, 98, 99, 47, 120]) 8192 path_max = 7 := by decide
/-- Reading "/tmp/out.gif/", and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_abs_gif_slash :
    read_cstr (name_at (abs_gif_name ++ [47])) 8192 = CstrOk (abs_gif_name ++ [47]) ∧
    cstr_access_len_aux (name_at (abs_gif_name ++ [47])) 8192 path_max = 14 := by decide
set_option maxRecDepth 8192 in
/-- Reading "/tmp/" followed by the 255-byte name, and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_tmp_name255 :
    read_cstr (name_at (tmp_key name255)) 8192 = CstrOk (tmp_key name255) ∧
    cstr_access_len_aux (name_at (tmp_key name255)) 8192 path_max = 261 := by decide
set_option maxRecDepth 8192 in
/-- Reading "/tmp/" followed by the 256-byte name, and its ledger.
model: a closed `read_cstr` and `cstr_access_len_aux` over a fixture, rewrites for `sys_norm`. -/
theorem read_tmp_name256 :
    read_cstr (name_at (tmp_key name256)) 8192 = CstrOk (tmp_key name256) ∧
    cstr_access_len_aux (name_at (tmp_key name256)) 8192 path_max = 262 := by decide

/-- The /tmp names spelled through a definition rather than a literal, as
the gates see them: "/tmp/out.gif" has nothing to strip and is the one
component "out.gif" under the prefix; "/tmp/out.gif/" strips to it and
carries the byte `do_unlinkat` tests past the component.  The shape is
`path_init`'s absolute-path start (fs/namei.c:2582-2587, Linux v6.18.46)
followed by `link_path_walk`'s two components (:2517-2519, :2472-2486).
kernel: fs/namei.c:path_init,link_path_walk,do_unlinkat@v6.18.46 -/
theorem tmp_gif_typed :
    path_strip_trailing_slashes abs_gif_name = abs_gif_name
      ∧ tmp_name abs_gif_name = some gif_basename
      ∧ path_strip_trailing_slashes (abs_gif_name ++ [47]) = abs_gif_name
      ∧ path_trailing_slash (abs_gif_name ++ [47]) = true := by decide

set_option maxRecDepth 8192 in
/-- The two long keys under /tmp as the gates see them: nothing to strip,
one component each, NUL past it, equal to themselves, under no key of the
image that holds them.  The equalities are the closed facts the lookup and
the removal reduce with, kept here so that no pin evaluates a 260-byte
comparison inside `simp`.
kernel: fs/namei.c:path_init,link_path_walk,do_unlinkat@v6.18.46 -/
theorem long_tmp_names_typed :
    path_strip_trailing_slashes (tmp_key name255) = tmp_key name255
      ∧ tmp_name (tmp_key name255) = some name255
      ∧ path_trailing_slash (tmp_key name255) = false
      ∧ path_eqb (tmp_key name255) (tmp_key name255) = true
      ∧ fs_under [(tmp_key name255, [104])] (tmp_key name255) = false
      ∧ path_strip_trailing_slashes (tmp_key name256) = tmp_key name256
      ∧ tmp_name (tmp_key name256) = some name256
      ∧ path_trailing_slash (tmp_key name256) = false
      ∧ path_eqb (tmp_key name256) (tmp_key name256) = true
      ∧ fs_under [(tmp_key name256, [104])] (tmp_key name256) = false := by decide

/-- The literal paths that reach the separator branch, as the gates see
them: what the trailing-separator strip leaves, and what `tmp_name` makes
of it — `none` for a name whose parent is not the run's /tmp ("a/b",
"./a", "/a", "/abc/x"), for /tmp itself in its spellings, and for a second
component; the one component for "/tmp/d".  The shape follows
`link_path_walk`'s splitting (fs/namei.c:2450-2505, Linux v6.18.46) and
`path_init`'s absolute-path start (:2582-2587).
kernel: fs/namei.c:link_path_walk,path_init@v6.18.46 -/
theorem tmp_literal_paths_typed :
    path_strip_trailing_slashes [97, 47, 98] = [97, 47, 98] ∧ tmp_name [97, 47, 98] = none
      ∧ path_strip_trailing_slashes [97, 47, 98, 47] = [97, 47, 98]
      ∧ path_strip_trailing_slashes [46, 47, 97] = [46, 47, 97] ∧ tmp_name [46, 47, 97] = none
      ∧ path_strip_trailing_slashes [47, 97] = [47, 97] ∧ tmp_name [47, 97] = none
      ∧ path_strip_trailing_slashes [47, 116, 109, 112] = [47, 116, 109, 112]
      ∧ tmp_name [47, 116, 109, 112] = none
      ∧ path_strip_trailing_slashes [47, 116, 109, 112, 47] = [47, 116, 109, 112]
      ∧ path_strip_trailing_slashes [47, 116, 109, 112, 47, 46] = [47, 116, 109, 112, 47, 46]
      ∧ tmp_name [47, 116, 109, 112, 47, 46] = none
      ∧ path_strip_trailing_slashes [47, 116, 109, 112, 47, 46, 46] = [47, 116, 109, 112, 47, 46, 46]
      ∧ tmp_name [47, 116, 109, 112, 47, 46, 46] = none
      ∧ path_strip_trailing_slashes [47, 116, 109, 112, 47, 100] = [47, 116, 109, 112, 47, 100]
      ∧ tmp_name [47, 116, 109, 112, 47, 100] = some [100]
      ∧ path_strip_trailing_slashes [47, 116, 109, 112, 47, 100, 47, 102]
          = [47, 116, 109, 112, 47, 100, 47, 102]
      ∧ tmp_name [47, 116, 109, 112, 47, 100, 47, 102] = none
      ∧ path_strip_trailing_slashes [47, 97, 98, 99, 47, 120] = [47, 97, 98, 99, 47, 120]
      ∧ tmp_name [47, 97, 98, 99, 47, 120] = none := by decide

/-- The pathname argument of a dispatcher-level call is a1.
model: a projection of the concrete input, a rewrite for `sys_norm`. -/
theorem in_arg_1_of_unlink_in (dirfd flags : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput 35 [dirfd, 8192, flags, 0, 0, 0] mem wmem) 1 = 8192 := rfl

attribute [sys_simp]
  read_a read_a_slash read_a_slash_slash read_root read_root2 read_dot read_dot_slash read_dotdot
  read_dotdot_slash read_empty read_a_slash_b read_a_slash_b_slash read_dot_slash_a read_slash_a
  read_abs_gif read_gif_basename read_name255 read_name256 read_unmapped read_unterminated
  read_endless read_dot3 read_ab read_b read_hi long_names_typed in_arg_1_of_unlink_in
  read_tmp_dir read_tmp_slash read_tmp_dot read_tmp_dotdot read_tmp_d read_tmp_df read_abc_x
  read_abs_gif_slash read_tmp_name255 read_tmp_name256 tmp_gif_typed long_tmp_names_typed
  tmp_literal_paths_typed

/-- The fixture memory behind a short name reads back its bytes and then
the NUL, and nothing past it; the unterminated one stops after its byte.
model: closed facts about the fixtures, so a pin that names a length names the right one. -/
theorem short_fixtures_read_back :
    abs_gif_name.length = 12 ∧ gif_basename.length = 7
      ∧ name_at [97] 8192 = some 97 ∧ name_at [97] 8193 = some 0
      ∧ name_at [97] 8194 = none ∧ unterminated 8193 = none := by decide

/-! ## `SYSCALL_DEFINE3(unlinkat)`: the flag word, before anything is read

    if ((flag & ~AT_REMOVEDIR) != 0)
            return -EINVAL;
    if (flag & AT_REMOVEDIR)
            return do_rmdir(dfd, getname(pathname));
    return do_unlinkat(dfd, getname(pathname));

(fs/namei.c:4775-4783, Linux v6.18.46).  `getname` is an argument expression on the two
return paths only, so a bit outside AT_REMOVEDIR is -EINVAL with the
pathname never fetched and the dirfd never looked at — which is what the
empty copy-in ledger on these pins asserts.  `flag` is an `int`
(`__SYSCALL_DEFINEx`, arch/riscv/include/asm/syscall_wrapper.h:82-88,
through `__SC_CAST`, include/linux/syscalls.h:132, Linux v6.18.46), so the register's high
half never reaches the mask; the dispatcher section pins that. -/

/-- Bit 0 is not AT_REMOVEDIR: -EINVAL, nothing read, nothing else.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem bad_flag_is_einval (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 1 (mem_in (name_at [97])) unlink_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) unlink_model [] := by
  sys_norm

/-- A ledger on the -EINVAL arm is a read the kernel did not perform: the
same call with a two-byte ledger is refused.  A spec that wrapped the whole
call in `record_copyins` would EXPECT this range and accept, which is why
the boundary sits inside the flag test.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:smuggle-copyin:a1:1 -- flag-bad -/
theorem bad_flag_ledger_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 1 (mem_in (name_at [97])) unlink_model
        (Ok (ledgered (errno_ret EINVAL) 2) m' evs) := by
  sys_refute

/-- The pathname is NOT fetched first: with bit 0 set and an unmapped
pointer the answer is still -EINVAL.
kernel: fs/namei.c:unlinkat,getname_flags@v6.18.46 -/
theorem bad_flag_reads_no_pathname (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 1 (mem_in unmapped) unlink_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) unlink_model [] := by
  sys_norm

/-- The probe's own shape: AT_EMPTY_PATH (0x1000) with a pathname nothing
could read is -EINVAL, and nothing is read.
probe: testing/syscall-check/tests/unlinkat_spec.c#conform -- flag-first-fault -/
theorem at_empty_path_unmapped_is_einval (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 4096 (mem_in unmapped) unlink_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) unlink_model [] := by
  sys_norm

/-- …so a kernel answering -EFAULT there has evaluated `getname` before the
flag test, which fs/namei.c:4777-4782 (Linux v6.18.46) does not.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-EFAULT -- flag-first-fault -/
theorem bad_flag_efault_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 4096 (mem_in unmapped) unlink_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and beats an over-long pathname: AT_EMPTY_PATH with 4096 unterminated
bytes is -EINVAL with nothing read, not `getname`'s -ENAMETOOLONG.
probe: testing/syscall-check/tests/unlinkat_spec.c#conform -- flag-first -/
theorem bad_flag_beats_toolong (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 4096 (mem_in endless) unlink_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) unlink_model [] := by
  sys_norm

/-- …so a kernel that copied the pathname first, and answered its length, is
refused.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENAMETOOLONG -- flag-first -/
theorem bad_flag_toolong_enametoolong_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 4096 (mem_in endless) unlink_model
        (Ok (mkEffect (errno_ret ENAMETOOLONG) [] []) m' evs) := by
  sys_refute

/-- The dirfd is not looked at either: bit 0 with a dirfd of 3 is -EINVAL,
not the decline the dirfd alone would earn.
kernel: fs/namei.c:unlinkat,path_init@v6.18.46 -/
theorem bad_flag_beats_dirfd (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 1 (mem_in (name_at [97])) unlink_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) unlink_model [] := by
  sys_norm

/-- AT_EMPTY_PATH (0x1000) is a bit outside AT_REMOVEDIR like any other:
-EINVAL, even though the pathname is not empty.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem at_empty_path_is_einval (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 4096 (mem_in (name_at [97])) unlink_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) unlink_model [] := by
  sys_norm

/-- AT_SYMLINK_NOFOLLOW (0x100) too, though unlink never follows a symlink
anyway: `path_parentat` (fs/namei.c:2719-2733, Linux v6.18.46) stops at
the parent and never walks the last component.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem at_symlink_nofollow_is_einval (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 256 (mem_in (name_at [97])) unlink_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) unlink_model [] := by
  sys_norm

/-- AT_REMOVEDIR with an extra bit is refused whole: `~AT_REMOVEDIR`
masks the one bit out and 1 is left.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem removedir_with_a_bit_is_einval (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 513 (mem_in (name_at [97])) unlink_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) unlink_model [] := by
  sys_norm

/-- A bad flag word is never a decline: the kernel decides it.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem bad_flag_never_declines :
    ¬ unlinkat_spec cwd_fd 8192 1 (mem_in (name_at [97])) unlink_model Unmodeled := by
  sys_refute

/-! ## `getname_flags`: three answers, before the dirfd

`getname` (include/linux/fs.h:2944-2947, Linux v6.18.46) is `getname_flags(name, 0)`
(fs/namei.c:135-215, Linux v6.18.46).  It returns `strncpy_from_user`'s negative result as
it is (:161-164, :196-199): -EFAULT for an unreadable byte
(lib/strncpy_from_user.c:113-155, Linux v6.18.46, the `efault:` label of
`do_strncpy_from_user` at :91-92).  It answers -ENOENT itself for the
empty string (fs/namei.c:168-171, :202-206, Linux v6.18.46), LOOKUP_EMPTY being clear on
this call, and -ENAMETOOLONG when the copy reaches PATH_MAX with no NUL
(:207-211).  All three are decided inside the `getname(pathname)` argument
expression, before `do_unlinkat` or `do_rmdir` runs `filename_parentat`
(:4716, :4579), so they precede the dirfd — and the copy-in ledger of each
is what was read: one byte for a pointer that faults at once, the name and
the NUL otherwise, PATH_MAX for a name with no NUL. -/

/-- An unmapped pathname pointer is -EFAULT, after one attempted byte.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user,do_strncpy_from_user@v6.18.46 -/
theorem unmapped_pathname_is_efault (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in unmapped) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EFAULT) 1) unlink_model [] := by
  sys_norm

/-- A name whose NUL is unreadable is -EFAULT too — the copy stops at the
fault, not at the end of the readable part — and the ledger covers the byte
read and the byte that faulted.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user,do_strncpy_from_user@v6.18.46 -/
theorem unterminated_pathname_is_efault (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in unterminated) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EFAULT) 2) unlink_model [] := by
  sys_norm

/-- None of `getname`'s three answers admits an alternative: a kernel
reporting -ENOMEM for a faulting pointer would have to have failed
`__getname` (fs/namei.c:146-148, Linux v6.18.46), which is outside the model's
deterministic arm.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENOMEM -- fault -/
theorem efault_enomem_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in unmapped) unlink_model
        (Ok (ledgered (errno_ret ENOMEM) 1) m' evs) := by
  sys_refute

set_option maxRecDepth 100000 in
/-- No NUL within PATH_MAX bytes is -ENAMETOOLONG, and the ledger is the
whole PATH_MAX window the copy walked.
kernel: fs/namei.c:getname_flags; include/uapi/linux/limits.h:PATH_MAX@v6.18.46 -/
theorem no_nul_within_path_max_is_enametoolong (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in endless) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENAMETOOLONG) 4096) unlink_model [] := by
  sys_norm

set_option maxRecDepth 100000 in
/-- …and admits no -ENOMEM either.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENOMEM -- toolong -/
theorem toolong_enomem_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in endless) unlink_model
        (Ok (ledgered (errno_ret ENOMEM) 4096) m' evs) := by
  sys_refute

set_option maxRecDepth 100000 in
/-- …and so does an over-long one: -ENAMETOOLONG under a dirfd of 3, the
whole PATH_MAX window read, before the dirfd is resolved.
probe: testing/syscall-check/tests/unlinkat_spec.c#conform -- dirfd-order -/
theorem toolong_beats_dirfd (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 0 (mem_in endless) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENAMETOOLONG) 4096) unlink_model [] := by
  sys_norm

/-- The empty pathname is `getname_flags`'s own -ENOENT: one byte read,
the NUL.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_pathname_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 1) unlink_model [] := by
  sys_norm

/-- Decided before the AT_REMOVEDIR split: the same -ENOENT under rmdir.
kernel: fs/namei.c:getname_flags,unlinkat@v6.18.46 -/
theorem empty_pathname_rmdir_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 1) unlink_model [] := by
  sys_norm

/-- …and not -ENOMEM.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENOMEM -- empty -/
theorem empty_pathname_enomem_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [])) unlink_model
        (Ok (ledgered (errno_ret ENOMEM) 1) m' evs) := by
  sys_refute

/-- The pathname is fetched BEFORE the dirfd is resolved: an empty
pathname under a dirfd of 3 is -ENOENT, not the dirfd's decline.
kernel: fs/namei.c:getname_flags,do_unlinkat,path_init@v6.18.46 -/
theorem empty_pathname_beats_dirfd (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 0 (mem_in (name_at [])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 1) unlink_model [] := by
  sys_norm

/-- A pathname that cannot be fetched beats the dirfd the same way.
kernel: fs/namei.c:getname_flags,do_unlinkat,path_init; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem unmapped_pathname_beats_dirfd (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 0 (mem_in unmapped) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EFAULT) 1) unlink_model [] := by
  sys_norm

/-! ## `path_init`: only AT_FDCWD is modeled

A relative pathname starts at the working directory when `nd->dfd ==
AT_FDCWD` (fs/namei.c:2590, Linux v6.18.46) and otherwise at the directory the fd names
(:2606-2622), where a closed fd is -EBADF (:2610-2611) and a non-directory
-ENOTDIR (:2621-2622).  The model has no directory structure to start a
walk in, so every dirfd but AT_FDCWD declines: the real answers above are
not claimed, and neither is the flat map's.  For a RELATIVE pathname the
dirfd is resolved BEFORE the last component is typed (`path_init` runs
ahead of `link_path_walk` in `path_parentat`, :2722-2723), so "." under a
bad dirfd is -EBADF on Linux and not -EISDIR — the decline covers that too.
For an ABSOLUTE one `path_init` never reads the dirfd (:2582-2587), so "/"
under a bad dirfd is -EISDIR on Linux; the decline there is sound and costs
that answer. -/

/-- A dirfd of 3 declines, whatever the name.  Not -EBADF or -ENOTDIR,
which the kernel could answer, and not the map's own answer for the present
`a`, the removal (refuted next).
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- dirfd-bad -/
theorem other_dirfd_declines (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 0 (mem_in (name_at [97])) unlink_model o ↔ o = Unmodeled := by
  sys_norm

/-- The flat map's own answer — the key is present, remove it — is the
confident wrong one: fd 3 could name any directory.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem other_dirfd_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec 3 8192 0 (mem_in (name_at [97])) unlink_model
        (Ok (ledgered (Z_to_bv 64 0) 2) m' evs) := by
  sys_refute

/-- "." under a dirfd of 3 declines as well: the dirfd is resolved before
the component is typed.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- dot-dirfd -/
theorem dot_under_other_dirfd_declines (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 0 (mem_in (name_at [46])) unlink_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the -EISDIR that "." earns under AT_FDCWD is not claimed there.
kernel: fs/namei.c:path_init,do_unlinkat@v6.18.46 -/
theorem dot_under_other_dirfd_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec 3 8192 0 (mem_in (name_at [46])) unlink_model
        (Ok (ledgered (errno_ret EISDIR) 2) m' evs) := by
  sys_refute

/-- ".." under AT_REMOVEDIR and a dirfd of 3 declines the same way (the
probe's second call: -EBADF on Linux, never -ENOTEMPTY).
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- dot-dirfd -/
theorem dotdot_under_other_dirfd_declines (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 512 (mem_in (name_at [46, 46])) unlink_model o ↔ o = Unmodeled := by
  sys_norm

/-- The dirfd guard sits ahead of every later arm: a present "a/" under a
dirfd of 3 declines rather than answering `slashes:`'s -ENOTDIR (Linux:
-EBADF, :2610-2611, before the walk).
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem trailing_slash_under_other_dirfd_declines (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 0 (mem_in (name_at [97, 47])) unlink_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and so does AT_REMOVEDIR on a present file under it, rather than
`may_delete`'s -ENOTDIR.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem rmdir_under_other_dirfd_declines (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 512 (mem_in (name_at [97])) unlink_model o ↔ o = Unmodeled := by
  sys_norm

/-- "/" under a dirfd of 3 declines as well, and here the decline COSTS an
answer: for an absolute pathname `path_init` returns before its `nd->dfd`
branch (fs/namei.c:2582-2587, Linux v6.18.46), so Linux answers -EISDIR
whatever the dirfd; the guard is sound, not exact, on this shape.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem root_under_other_dirfd_declines (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 0 (mem_in (name_at [47])) unlink_model o ↔ o = Unmodeled := by
  sys_norm

/-- A dirfd open on a regular FILE declines as well — fd 3 is `a` itself here,
and the name asked for is another.  Linux answers -ENOTDIR from `path_init`
(fs/namei.c:2621-2622, Linux v6.18.46); the model has no directory to start
from either way.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- dirfd-file -/
theorem file_dirfd_declines (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 0 (mem_in (name_at [98])) open_fd_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the kernel's own -ENOTDIR is not claimed for it.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem file_dirfd_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec 3 8192 0 (mem_in (name_at [98])) open_fd_model
        (Ok (ledgered (errno_ret ENOTDIR) 2) m' evs) := by
  sys_refute

/-! ## `link_path_walk` types the last component; three types need no lookup

`link_path_walk` starts at LAST_ROOT (fs/namei.c:2446, Linux v6.18.46), skips leading
separators (:2450-2454) and returns at once if nothing follows them
(:2455-2458): "/" and "//" alike never enter the component loop.  A
component is typed by the word `hash_name` returns (:2472): LAST_DOTDOT
(:2475-2478), LAST_DOT (:2480-2482) or LAST_NORM (:2484-2486).
`do_unlinkat` answers -EISDIR to every type but LAST_NORM without
distinguishing them (:4720-4722); `do_rmdir` switches on the type
(:4583-4592): LAST_DOTDOT -ENOTEMPTY, LAST_DOT -EINVAL, LAST_ROOT -EBUSY.
None of the six consults a file system, so an empty map answers as any
other, and none admits an injectable errno. -/

/-- "/" has no component: LAST_ROOT, and `do_unlinkat`'s type test is
-EISDIR.  The image holds a file; it is not consulted.
kernel: fs/namei.c:link_path_walk,do_unlinkat@v6.18.46 -/
theorem root_unlink_is_eisdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EISDIR) 2) unlink_model [] := by
  sys_norm

/-- Under AT_REMOVEDIR, `do_rmdir`'s `case LAST_ROOT` is -EBUSY, on an
EMPTY map as on any other.
kernel: fs/namei.c:link_path_walk,do_rmdir@v6.18.46 -/
theorem root_rmdir_is_ebusy (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [47])) empty_model o
      ↔ o = Ok (ledgered (errno_ret EBUSY) 2) empty_model [] := by
  sys_norm

/-- The rejecting half that matters most: -ENOENT is what the flat map
would answer on its own — "no such key" — and Linux never answers -ENOENT
for "/".
rocq-twin: unlinkat_root_enoent_rejected
kernel: fs/namei.c:link_path_walk,do_rmdir@v6.18.46 -/
theorem root_enoent_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [47])) empty_model
        (Ok (ledgered (errno_ret ENOENT) 2) m' evs) := by
  sys_refute

/-- The same lie on the plain call, which is the one the probe's mutation
forges (its first `unlinkat` is the flags-0 one): unlink("/") is -EISDIR,
never -ENOENT.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENOENT -- root -/
theorem root_unlink_enoent_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47])) empty_model
        (Ok (ledgered (errno_ret ENOENT) 2) m' evs) := by
  sys_refute

/-- rmdir's LAST_ROOT is -EBUSY, which `do_unlinkat`'s type test does not
distinguish: -EISDIR under AT_REMOVEDIR is the other call's answer.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat#2:ret=-EISDIR -- root -/
theorem root_rmdir_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [47])) empty_model
        (Ok (ledgered (errno_ret EISDIR) 2) m' evs) := by
  sys_refute

/-- "//" is LAST_ROOT too: the leading separators are skipped as one run.
kernel: fs/namei.c:link_path_walk,do_unlinkat@v6.18.46 -/
theorem double_slash_is_last_root (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 47])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EISDIR) 3) unlink_model [] := by
  sys_norm

/-- …under AT_REMOVEDIR as well.
kernel: fs/namei.c:link_path_walk,do_rmdir@v6.18.46 -/
theorem double_slash_rmdir_is_ebusy (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [47, 47])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EBUSY) 3) unlink_model [] := by
  sys_norm

/-- "." is LAST_DOT: -EISDIR from `do_unlinkat`'s type test.
kernel: fs/namei.c:link_path_walk,do_unlinkat@v6.18.46 -/
theorem dot_unlink_is_eisdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EISDIR) 2) unlink_model [] := by
  sys_norm

/-- rmdir(".") is `do_rmdir`'s `case LAST_DOT`, -EINVAL.
kernel: fs/namei.c:link_path_walk,do_rmdir@v6.18.46 -/
theorem dot_rmdir_is_einval (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [46])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EINVAL) 2) unlink_model [] := by
  sys_norm

/-- The "." arms are deterministic: `__getname`'s -ENOMEM (:146-148) is the
approximation the Sys docstring names, and the model refuses it.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENOMEM -- dot -/
theorem dot_enomem_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46])) unlink_model
        (Ok (ledgered (errno_ret ENOMEM) 2) m' evs) := by
  sys_refute

/-- …the AT_REMOVEDIR one too.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat#2:ret=-ENOMEM -- dot -/
theorem dot_rmdir_enomem_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [46])) unlink_model
        (Ok (ledgered (errno_ret ENOMEM) 2) m' evs) := by
  sys_refute

/-- ".." is LAST_DOTDOT, and `do_unlinkat` does not tell it from ".":
-EISDIR.
kernel: fs/namei.c:link_path_walk,do_unlinkat@v6.18.46 -/
theorem dotdot_unlink_is_eisdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46, 46])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EISDIR) 3) unlink_model [] := by
  sys_norm

/-- rmdir("..") is `do_rmdir`'s `case LAST_DOTDOT`, -ENOTEMPTY.
kernel: fs/namei.c:link_path_walk,do_rmdir@v6.18.46 -/
theorem dotdot_rmdir_is_enotempty (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [46, 46])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOTEMPTY) 3) unlink_model [] := by
  sys_norm

/-- rmdir("..") is -ENOTEMPTY and that arm is deterministic: not the
-EISDIR of the unlink call.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat#2:ret=-EISDIR -- dotdot -/
theorem dotdot_rmdir_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [46, 46])) unlink_model
        (Ok (ledgered (errno_ret EISDIR) 3) m' evs) := by
  sys_refute

/-- …and the plain call admits no -ENOMEM.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENOMEM -- dotdot -/
theorem dotdot_enomem_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46, 46])) unlink_model
        (Ok (ledgered (errno_ret ENOMEM) 3) m' evs) := by
  sys_refute

/-- Trailing separators do not change the type: "./" is LAST_DOT, -EISDIR
to unlink and -EINVAL to rmdir.
kernel: fs/namei.c:link_path_walk,do_unlinkat,do_rmdir@v6.18.46 -/
theorem dot_slash_is_typed_dot (o o' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46, 47])) unlink_model o
       ↔ o = Ok (ledgered (errno_ret EISDIR) 3) unlink_model [])
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [46, 47])) unlink_model o'
       ↔ o' = Ok (ledgered (errno_ret EINVAL) 3) unlink_model []) := by
  constructor <;> sys_norm

/-- rmdir("./") is -EINVAL as for a bare ".": not -EISDIR.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat#2:ret=-EISDIR -- dot-slash -/
theorem dot_slash_rmdir_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [46, 47])) unlink_model
        (Ok (ledgered (errno_ret EISDIR) 3) m' evs) := by
  sys_refute

/-- unlink("../") is -EISDIR: LAST_DOTDOT, which `do_unlinkat`'s type test
does not tell from "..".
probe: testing/syscall-check/tests/unlinkat_spec.c#conform -- dot-slash -/
theorem dotdot_slash_unlink_is_eisdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46, 46, 47])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret EISDIR) 4) unlink_model [] := by
  sys_norm

/-- "../" is LAST_DOTDOT, not LAST_ROOT: rmdir answers -ENOTEMPTY.
kernel: fs/namei.c:link_path_walk,do_rmdir@v6.18.46 -/
theorem dotdot_slash_rmdir_is_enotempty (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [46, 46, 47])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOTEMPTY) 4) unlink_model [] := by
  sys_norm

/-- …so `do_rmdir`'s LAST_ROOT -EBUSY is not its answer.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat#4:ret=-EBUSY -- dot-slash -/
theorem dotdot_slash_rmdir_ebusy_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [46, 46, 47])) unlink_model
        (Ok (ledgered (errno_ret EBUSY) 4) m' evs) := by
  sys_refute

/-- unlink("../") is -EISDIR: `do_unlinkat`'s type test does not
distinguish LAST_DOTDOT, so -ENOTEMPTY is the other call's answer.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat#3:ret=-ENOTEMPTY -- dot-slash -/
theorem dotdot_slash_unlink_enotempty_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46, 46, 47])) unlink_model
        (Ok (ledgered (errno_ret ENOTEMPTY) 4) m' evs) := by
  sys_refute

/-- "..." is an ordinary name: `hash_name` types only the words 0x2e and
0x2e2e (fs/namei.c:2429-2430, Linux v6.18.46), so three dots are LAST_NORM,
looked up, and absent here — -ENOENT.
probe: testing/syscall-check/tests/unlinkat_spec.c#conform -- dot3 -/
theorem dot3_is_an_ordinary_name (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46, 46, 46])) empty_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 4) empty_model [] := by
  sys_norm

/-- A kernel typing "..." as a dot path — -EISDIR — is refused: the dot
words are whole components, not prefixes.
kernel: fs/namei.c:hash_name,link_path_walk@v6.18.46 -/
theorem dot3_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46, 46, 46])) empty_model
        (Ok (ledgered (errno_ret EISDIR) 4) m' evs) := by
  sys_refute

/-! ## The separator guard: a component whose parent is not the working directory

A path with a "/" anywhere but at the end, once the trailing ones are
stripped, needs `link_path_walk`'s component loop against a tree — an
intermediate name that is a regular file is its -ENOTDIR (fs/namei.c:2529-2535, Linux v6.18.46),
a "." or ".." at the end is typed only after the parent walk — and the
flat map has no tree.  An absolute path is out of reach for a second
reason: `path_init` starts it at the root (:2582-2587) and nothing in the
model records the working directory's own path, so "/tmp/x" and "x"
cannot be related even when they name one file.  The model declines; the
flat map's own answer, -ENOENT for an absent key or a removal for a
present one, is the confident wrong one, and the guard runs before the
lookup so that a key spelling the whole path is not removed.  The one
shape answered inside this branch is the next section's: `/tmp/<one
component>` over the run's declared private /tmp. -/

/-- "a/b" declines.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- slash-interior -/
theorem interior_separator_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47, 98])) unlink_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and its -ENOENT is not claimed: whether `a/b` exists is a question
the flat map cannot be asked.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem interior_separator_enoent_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47, 98])) unlink_model
        (Ok (ledgered (errno_ret ENOENT) 4) m' evs) := by
  sys_refute

/-- Stripping the trailing separator of "a/b/" does not save the interior one.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- slash-interior-trailing -/
theorem interior_separator_trailing_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47, 98, 47])) unlink_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- The guard runs ahead of the lookup: on an image whose key IS the bytes
"a/b", the lookup would succeed, and the key is still not removed.
kernel: fs/namei.c:link_path_walk,path_parentat@v6.18.46 -/
theorem interior_separator_key_present_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47, 98])) implied_dir_model
        (Ok (ledgered (Z_to_bv 64 0) 4) m' evs) := by
  sys_refute

/-- "./a" has an interior separator: the "." is a component to walk, not
the last one to type.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- dotslash -/
theorem dot_slash_name_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [46, 47, 97])) unlink_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- A LEADING separator with a component after it: "/a" declines, though
"/" alone is answered.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- slash-absolute -/
theorem absolute_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 97])) unlink_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …the AT_REMOVEDIR half too.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- slash-absolute-rmdir -/
theorem absolute_rmdir_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [47, 97])) unlink_model o
      ↔ o = Unmodeled := by
  sys_norm

/-! ## The /tmp arm: one component under the run's private directory

One family of paths WITH a separator is answered ahead of the decline
above: `/tmp/<one component>`, over the run's declared private /tmp
(`State.in_tmp`, seeded into the image under absolute keys by
`State.fs_seed_tmp`), on the premise that /tmp is a distinct, writable
directory PRIVATE to this run, so that the run's own table is the whole
truth about it (issue #562, rung 4 of #696;
bugs/tmp-assumed-private-directory.md).  What Linux does with such a
path: `path_init` starts an absolute pathname at the root
(fs/namei.c:2582-2587, Linux v6.18.46) through `nd_jump_root`, which sets
`nd->path = nd->root` (:1042, :1050), and never reads the dirfd; `link_path_walk` walks
"tmp" as a non-final component (:2517-2519) and types the last as it
types a relative name (:2472-2486); `do_unlinkat` then runs the same
lookup, `slashes:` test and `vfs_unlink` on it (:4729-4742).  So the
found-key tail is shared with the working-directory arm
(`unlink_found_spec`), and every decision below that the tail makes has
the pin its section above gives; what is pinned here is the gate that
admits the shape, the -ENOENT the arm answers for a key the run does not
hold (the ruling on #1136), and what it declines on its own account: the
flag, a component over NAME_MAX, and an implied directory inside /tmp. -/

/-- The declaration seeds the component under "/tmp/": the run that
declared "out.gif" holds the key "/tmp/out.gif", and nothing else.
model: a closed `State.fs_seed_tmp` over a one-entry declaration, the same image `abs_gif_model` holds. -/
theorem tmp_declared_seeds_the_key :
    fs_seed_tmp [] [(gif_basename, [104])] = [(abs_gif_name, [104])] := by decide

/-- A name the declaration could not put anywhere: a component with a NUL
byte in it.  `fs_seed_tmp` drops it, so the run holds nothing at that name,
and no pathname could reach it in any case — `read_cstr` stops at the NUL.
rocq-twin: unlinkat_tmp_nul_name_is_not_seeded
model: a closed `State.fs_seed_tmp` over a declaration no pathname can name. -/
theorem tmp_nul_name_is_not_seeded :
    fs_seed_tmp [] [([111, 0, 117, 116], [104])] = [] := by decide

/-- As the fuzz harness of issue #562 ships it, on the empty image the model
starts a run with and an EMPTY declared /tmp: the path is one the arm
names, so the separator gate is not what answers it.  The run holds no key
there, and the privacy premise makes its own table the whole truth about
the directory, so the answer is the -ENOENT `lookup_one_qstr_excl` gives
for a negative dentry (fs/namei.c:1713-1716, Linux v6.18.46) — the ruling
on #1136.  Nothing moves: the model handed back is the one handed in.
rocq-twin: unlinkat_tmp_key_not_held_is_enoent
kernel: fs/namei.c:path_init,lookup_one_qstr_excl@v6.18.46 -/
theorem tmp_key_not_held_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) empty_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 13) empty_model [] := by
  sys_norm

/-- …so the success a kernel holding the file would return is refused: the
answer above is a report of an absence, never a licence to remove.
rocq-twin: unlinkat_tmp_key_not_held_is_enoent
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem tmp_key_not_held_success_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) empty_model
        (Ok (ledgered (Z_to_bv 64 0) 13) m' evs) := by
  sys_refute

/-- THE SECOND UNLINK, over the model `tmp_declared_key_removed` below names
as the result of the first one.  DOCUMENTARY, and worth saying so: the
removal leaves the empty file system, `unlinked_model` is
`fixture_of (fs := [])` and `empty_model` is `fixture_of` with the same
default, so this is `tmp_key_not_held_is_enoent` at a definitionally equal
alias and it distinguishes no kernel that theorem does not.  What it records
is the composition a program that cleans up after itself makes; that the
removal really takes the key out is `tmp_declared_key_removed`'s right-hand
side and `tmp_removal_kept_entry_rejected`, not this.
rocq-twin: unlinkat_tmp_removed_key_second_unlink_is_enoent
kernel: fs/namei.c:path_init,lookup_one_qstr_excl@v6.18.46 -/
theorem tmp_removed_key_second_unlink_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) unlinked_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 13) unlinked_model [] := by
  sys_norm

/-- …and a second success is refused: the name is already gone, so
`lookup_one_qstr_excl` hands `do_unlinkat` the -ENOENT it gives a negative
dentry (fs/namei.c:1713-1716, Linux v6.18.46), and `do_unlinkat` never
reaches `vfs_unlink` — its `if (!IS_ERR(dentry))` (:4731) skips the block
that calls it (:4741).  Documentary in the same way as the theorem above,
and over the same fixture.
rocq-twin: unlinkat_tmp_removed_key_second_unlink_is_enoent
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem tmp_second_unlink_success_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) unlinked_model
        (Ok (ledgered (Z_to_bv 64 0) 13) m' evs) := by
  sys_refute

/-- THE REMOVAL ITSELF over a /tmp the run DECLARED: the call issue #562
was filed for.  The key is gone afterwards, and nothing else moved; the
five environment failures are the same five as for a name in the working
directory, because the tail is the same tail.
rocq-twin: unlinkat_tmp_declared_key_removed
kernel: fs/namei.c:path_init,do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem tmp_declared_key_removed (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) tmp_declared_model o
      ↔ (env_failure o 13 tmp_declared_model
          ∨ o = Ok (ledgered (Z_to_bv 64 0) 13) unlinked_model []) := by
  sys_norm

/-- The SAME image written as a raw key rather than as a declaration: the
arm cannot tell a declared entry from an image key that spells the same
path, and this is the case that says so.  It also records the reading this
rung introduced — a "/tmp/"-prefixed key IS the file in the run's private
/tmp; no earlier arm could observe such a key, so no earlier answer moved.
rocq-twin: unlinkat_tmp_image_key_removed
kernel: fs/namei.c:path_init,do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem tmp_image_key_removed (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) abs_gif_model o
      ↔ (env_failure o 13 abs_gif_model
          ∨ o = Ok (ledgered (Z_to_bv 64 0) 13) unlinked_model []) := by
  sys_norm

/-- A success that leaves the key in place is refused: `vfs_unlink`
removes the entry.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem tmp_removal_kept_entry_rejected (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) abs_gif_model
        (Ok (ledgered (Z_to_bv 64 0) 13) abs_gif_model evs) := by
  sys_refute

/-- The dirfd is still required to be AT_FDCWD, though Linux ignores it for
an absolute pathname (`path_init` returns at fs/namei.c:2582-2587 before its
`nd->dfd` branch): with a dirfd of 3 the arm declines, and the decline
costs the removal Linux would perform.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem tmp_under_other_dirfd_declines (o : outcome SyscallEffect) :
    unlinkat_spec 3 8192 0 (mem_in (name_at abs_gif_name)) abs_gif_model o ↔ o = Unmodeled := by
  sys_norm

/-- AT_REMOVEDIR at the very name the plain flag removes: declined.  Linux
answers -ENOTDIR for the regular file (`may_delete`, fs/namei.c:3284-3286,
Linux v6.18.46, through `vfs_rmdir`, :4532), and -ENOTEMPTY or 0 for a
directory; which of the three it is turns on /tmp holding a directory,
the thing this rung defers, so the ruling declines the flag rather than
answering the one case the model could judge.
rocq-twin: unlinkat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:do_rmdir,vfs_rmdir,may_delete@v6.18.46 -/
theorem tmp_rmdir_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at abs_gif_name)) abs_gif_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …so `may_delete`'s -ENOTDIR, the answer the working-directory arm gives
for the same file, is not claimed under /tmp.
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem tmp_rmdir_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at abs_gif_name)) abs_gif_model
        (Ok (ledgered (errno_ret ENOTDIR) 13) m' evs) := by
  sys_refute

/-- A second component, "/tmp/d/f", whose key the image holds: declined.
The answer would come from the directory "/tmp/d", which the flat map
cannot hold; `link_path_walk` would walk it as a component (:2517-2519).
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_second_component_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 100, 47, 102]))
        tmp_shapes_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and the key spelling it is not removed.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_second_component_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 100, 47, 102]))
        tmp_shapes_model (Ok (ledgered (Z_to_bv 64 0) 9) m' evs) := by
  sys_refute

/-- The directory itself, in its four spellings — "/tmp", "/tmp/",
"/tmp/." and "/tmp/.." — names /tmp or its parent rather than a file in
it: each declines, on an image whose /tmp is not empty.  On Linux the
first two are `do_unlinkat`'s -EISDIR for a directory, decided at two
different lines (fs/namei.c:4720-4722 does not fire — "tmp" is LAST_NORM;
Linux v6.18.46): "/tmp" reaches `vfs_unlink`, where `may_delete`'s
`d_is_dir` answers (:3289-3290), while "/tmp/" has a byte past its last
component, so `if (last.name[last.len]) goto slashes;` (:4734-4735) skips
`vfs_unlink` and the `slashes:` label's own `d_is_dir` answers
(:4768-4769, Linux v6.18.46); the last two are typed LAST_DOT and
LAST_DOTDOT (:2475-2482) and answered -EISDIR by the type test.
rocq-twin: unlinkat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:link_path_walk,do_unlinkat,may_delete@v6.18.46 -/
theorem tmp_directory_itself_declines (o o₂ o₃ o₄ : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112])) tmp_shapes_model o
       ↔ o = Unmodeled)
    ∧ (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47])) tmp_shapes_model o₂
       ↔ o₂ = Unmodeled)
    ∧ (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 46])) tmp_shapes_model o₃
       ↔ o₃ = Unmodeled)
    ∧ (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 46, 46])) tmp_shapes_model o₄
       ↔ o₄ = Unmodeled) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- …and Linux's -EISDIR for "/tmp" is not claimed.
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem tmp_directory_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112])) tmp_shapes_model
        (Ok (ledgered (errno_ret EISDIR) 5) m' evs) := by
  sys_refute

/-- "/tmp/." and "/tmp/.." decline BECAUSE they name the directory and its
parent, not because nothing is held at those bytes: on an image whose keys
spell them (`tmp_dot_keys_model`) the two still decline, so a gate that let
"." or ".." through as a component — `hash_name` types them LAST_DOT and
LAST_DOTDOT (fs/namei.c:2475-2482, Linux v6.18.46) and `do_unlinkat`
answers -EISDIR without any lookup (:4720-4722) — would be caught here.
kernel: fs/namei.c:link_path_walk,do_unlinkat@v6.18.46 -/
theorem tmp_dot_spellings_decline_even_when_a_key_spells_them (o o₂ : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 46])) tmp_dot_keys_model o
       ↔ o = Unmodeled)
    ∧ (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 46, 46])) tmp_dot_keys_model o₂
       ↔ o₂ = Unmodeled) := by
  constructor <;> sys_norm

/-- …and neither key is removed through those spellings.
kernel: fs/namei.c:link_path_walk,do_unlinkat@v6.18.46 -/
theorem tmp_dot_spellings_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 46])) tmp_dot_keys_model
        (Ok (ledgered (Z_to_bv 64 0) 7) m' evs)
    ∧ ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 46, 46])) tmp_dot_keys_model
        (Ok (ledgered (Z_to_bv 64 0) 8) m' evs) := by
  constructor <;> sys_refute

/-- A name some key lives UNDER inside /tmp: "/tmp/d" over an image holding
"/tmp/d/f" is an implied directory, and the answer is -EISDIR.  Linux
refuses a directory victim in `may_delete` (fs/namei.c:3289-3290, Linux
v6.18.46), which `vfs_unlink` calls (:4658) before it removes anything;
the answer is Linux's where POSIX allows -EPERM.  Nothing moves.
rocq-twin: unlinkat_tmp_implied_directory_is_eisdir
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem tmp_implied_directory_is_eisdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 100])) tmp_shapes_model o
      ↔ o = Ok (ledgered (errno_ret EISDIR) 7) tmp_shapes_model [] := by
  sys_norm

/-- …and the removal a flat map would have performed is refused.
rocq-twin: unlinkat_tmp_implied_directory_is_eisdir
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem tmp_implied_directory_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 100]))
        tmp_shapes_model (Ok (ledgered (Z_to_bv 64 0) 7) m' evs) := by
  sys_refute

/-- AT_REMOVEDIR of the implied directory "/tmp/d" declines: the ruling on
#562 keeps every AT_REMOVEDIR under /tmp declined, so the
working-directory arm's -ENOTEMPTY does not reach it.
rocq-twin: unlinkat_tmp_implied_directory_rmdir_declines
kernel: fs/namei.c:do_rmdir@v6.18.46 -/
theorem tmp_implied_directory_rmdir_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [47, 116, 109, 112, 47, 100]))
        tmp_only_dir_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE ORDER OF THE TWO /tmp RULES.  "/tmp/d" is not a key the run holds,
so the rule that answers -ENOENT for a name not held would claim the name
is absent; `unlinkat_tmp_spec` tests `fs_under` BEFORE the lookup, so the
directory wins.  This refuses the -ENOENT, which is what says the two
rules are in that order.
rocq-twin: unlinkat_tmp_implied_directory_precedes_not_held
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem tmp_implied_directory_enoent_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 100]))
        tmp_shapes_model (Ok (ledgered (errno_ret ENOENT) 7) m' evs) := by
  sys_refute

/-- …and the honest twin of that order: at a name with nothing under it the
not-held rule still answers -ENOENT.  Stated on the Rocq case's own image,
"/tmp/d/f" alone, at "/tmp/out.gif": the run holds nothing there and nothing
under it, so the guard passes and the lookup misses.
rocq-twin: unlinkat_tmp_implied_directory_precedes_not_held
kernel: fs/namei.c:lookup_one_qstr_excl@v6.18.46 -/
theorem tmp_not_held_beside_a_directory_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) tmp_only_dir_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 13) tmp_only_dir_model [] := by
  sys_norm

/-- The guard runs before the lookup here too: on the unrealizable image
holding both "/tmp/d" and "/tmp/d/f" the lookup of "/tmp/d" would succeed,
and the directory is still what answers.
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem tmp_unrealizable_image_is_eisdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 100]))
        tmp_unrealizable_model o
      ↔ o = Ok (ledgered (errno_ret EISDIR) 7) tmp_unrealizable_model [] := by
  sys_norm

/-- …and the removal is refused on it.
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem tmp_unrealizable_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 116, 109, 112, 47, 100]))
        tmp_unrealizable_model (Ok (ledgered (Z_to_bv 64 0) 7) m' evs) := by
  sys_refute

/-- A sibling in the same declared /tmp is untouched by the -EISDIR: the
plain key "/tmp/out.gif" is still removed beside the implied directory.
rocq-twin: unlinkat_tmp_implied_directory_sibling_still_unlinks
kernel: fs/namei.c:path_init,do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem tmp_sibling_of_a_directory_still_unlinks (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) tmp_shapes_model o
      ↔ (env_failure o 13 tmp_shapes_model
          ∨ o = Ok (ledgered (Z_to_bv 64 0) 13)
              (fixture_of (fs := [([47, 116, 109, 112, 47, 100, 47, 102], [104])])) []) := by
  sys_norm

/-- The prefix is compared byte for byte, not by length: "/abc/x" is five
bytes of prefix and one component, and it is not under /tmp, so it takes
the separator decline even over an image holding that very key.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_prefix_is_compared (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 97, 98, 99, 47, 120])) abc_x_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …so the key spelling "/abc/x" is not removed.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_prefix_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [47, 97, 98, 99, 47, 120])) abc_x_model
        (Ok (ledgered (Z_to_bv 64 0) 7) m' evs) := by
  sys_refute

/-- A trailing separator on the held key, "/tmp/out.gif/", reaches the
shared tail: `do_unlinkat` tests the byte past the component
(fs/namei.c:4734-4735, Linux v6.18.46) and its `slashes:` label answers
-ENOTDIR (:4767-4772); the key survives.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem tmp_trailing_slash_is_enotdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at (abs_gif_name ++ [47]))) abs_gif_model o
      ↔ o = Ok (ledgered (errno_ret ENOTDIR) 14) abs_gif_model [] := by
  sys_norm

/-- …and a kernel that removed the key through "/tmp/out.gif/" is refused.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem tmp_trailing_slash_success_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at (abs_gif_name ++ [47]))) abs_gif_model
        (Ok (ledgered (Z_to_bv 64 0) 14) m' evs) := by
  sys_refute

/-- The open-fd guard applies under /tmp as in the working directory: the
key held open through fd 3 declines rather than being removed.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem tmp_open_fd_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) tmp_open_fd_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and the removal Linux performs is not claimed there.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem tmp_open_fd_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at abs_gif_name)) tmp_open_fd_model
        (Ok (ledgered (Z_to_bv 64 0) 13) m' evs) := by
  sys_refute

set_option maxRecDepth 32768 in
/-- The declaration seeds the two long components as the keys the boundary
pins hold: `fs_seed_tmp` over a 255-byte and over a 256-byte declared name
is the one-key image `tmp_name255_model` and `tmp_name256_model` carry, so
the run that declared either name holds it just the same — `tmp_key` is the
whole of what the declaration does to a NUL-free name, at any length.
model: a closed `State.fs_seed_tmp` over the two one-entry long declarations, the images the boundary pins hold. -/
theorem tmp_long_names_seeded :
    fs_seed_tmp [] [(name255, [104])] = [(tmp_key name255, [104])]
      ∧ fs_seed_tmp [] [(name256, [104])] = [(tmp_key name256, [104])] := by decide

set_option maxRecDepth 32768 in
/-- The NAME_MAX boundary on this arm, from the admitting side: a component
of exactly 255 bytes, held as the key the declaration of that name seeds
(`tmp_long_names_seeded`), is REMOVED — `simple_lookup` on the harness's
tmpfs refuses only longer names (fs/libfs.c:71-72, Linux v6.18.46), as
`ext4_lookup` does (fs/ext4/namei.c:1768-1769) — under a ledger of the five
prefix bytes, the 255 and the NUL.  Both arms draw the line at the same
place, since "held" is one predicate over one key space: a component the
open can mint and the unlink cannot remove would be a file the run could
not get rid of.
rocq-twin: unlinkat_tmp_name_max_boundary
kernel: fs/namei.c:path_init,do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access; fs/libfs.c:simple_lookup@v6.18.46 -/
theorem tmp_name_max_component_removed (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at (tmp_key name255))) tmp_name255_model o
      ↔ (env_failure o 261 tmp_name255_model
          ∨ o = Ok (ledgered (Z_to_bv 64 0) 261) unlinked_model []) := by
  sys_norm

set_option maxRecDepth 32768 in
/-- …and from the declining side: 256 bytes declines, though the run holds
the key just the same (the declaration seeds it, `tmp_long_names_seeded`);
the filesystem's -ENAMETOOLONG is not the model's to claim.
rocq-twin: unlinkat_tmp_name_max_boundary
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup@v6.18.46 -/
theorem tmp_over_name_max_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at (tmp_key name256))) tmp_name256_model o
      ↔ o = Unmodeled := by
  sys_norm

set_option maxRecDepth 32768 in
/-- …so neither the removal nor -ENAMETOOLONG is claimed for it.
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup@v6.18.46 -/
theorem tmp_over_name_max_answers_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at (tmp_key name256))) tmp_name256_model
        (Ok (ledgered (Z_to_bv 64 0) 262) m' evs)
    ∧ ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at (tmp_key name256))) tmp_name256_model
        (Ok (ledgered (errno_ret ENAMETOOLONG) 262) m' evs) := by
  constructor <;> sys_refute

/-! ## Back in the working directory: the name the /tmp walk would end at -/

/-- Reached through the name the walk WOULD end at: "out.gif" carries no
separator, so it is answered rather than declined — and on the image above
it is answered -ENOENT, because `fs_under` is a COMPONENT prefix and
"/tmp/out.gif" does not live under "out.gif".
rocq-twin: unlinkat_absolute_basename_is_enoent
kernel: fs/namei.c:lookup_one_qstr_excl@v6.18.46 -/
theorem absolute_basename_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at gif_basename)) abs_gif_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 8) abs_gif_model [] := by
  sys_norm

/-- …so a kernel that removed something through it is not admitted.
Without this the two cases above are consistent with a model that reads
the flat map as a directory tree.
rocq-twin: unlinkat_absolute_basename_success_rejected
kernel: fs/namei.c:lookup_one_qstr_excl@v6.18.46 -/
theorem absolute_basename_success_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at gif_basename)) abs_gif_model
        (Ok (ledgered (Z_to_bv 64 0) 8) m' evs) := by
  sys_refute

/-! ## The NAME_MAX guard: the filesystem's own -ENAMETOOLONG

`getname_flags` bounds the whole path at PATH_MAX (fs/namei.c:207-211, Linux v6.18.46), so
a single component of 4095 bytes reaches the lookup, and it is the
FILESYSTEM that refuses it — `ext4_lookup` on `d_name.len > EXT4_NAME_LEN`
(fs/ext4/namei.c:1768-1769, Linux v6.18.46), 255 (fs/ext4/ext4.h:2399, Linux v6.18.46), and on
the tmpfs the harness runs every case in `simple_lookup` on `d_name.len >
NAME_MAX` (fs/libfs.c:71-72, Linux v6.18.46; mm/shmem.c:5285 installs it) — the
NAME_MAX of include/uapi/linux/limits.h:12 (Linux v6.18.46).  The model has no filesystem type to ask,
so a component longer than NAME_MAX declines; one of exactly NAME_MAX is
answered. -/

set_option maxRecDepth 32768 in
/-- 255 bytes is within NAME_MAX: the lookup runs, and an absent name is
-ENOENT, under a ledger of the 255 bytes and the NUL.
kernel: fs/namei.c:lookup_one_qstr_excl; include/uapi/linux/limits.h:NAME_MAX@v6.18.46 -/
theorem name_max_component_is_answered (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at name255)) empty_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 256) empty_model [] := by
  sys_norm

set_option maxRecDepth 32768 in
/-- …and -ENAMETOOLONG is not claimed for it: ext4 and tmpfs refuse only
names LONGER than 255.
kernel: fs/ext4/namei.c:ext4_lookup; fs/libfs.c:simple_lookup@v6.18.46 -/
theorem name_max_enametoolong_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at name255)) empty_model
        (Ok (ledgered (errno_ret ENAMETOOLONG) 256) m' evs) := by
  sys_refute

set_option maxRecDepth 32768 in
/-- 256 bytes declines: NAME_MAX belongs to the filesystem, not to
fs/namei.c.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- name256 -/
theorem over_name_max_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at name256)) empty_model o ↔ o = Unmodeled := by
  sys_norm

set_option maxRecDepth 32768 in
/-- Neither the filesystem's -ENAMETOOLONG nor the map's -ENOENT is
claimed for it.
kernel: fs/ext4/namei.c:ext4_lookup; fs/libfs.c:simple_lookup@v6.18.46 -/
theorem over_name_max_answers_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at name256)) empty_model
        (Ok (ledgered (errno_ret ENAMETOOLONG) 257) m' evs)
    ∧ ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at name256)) empty_model
        (Ok (ledgered (errno_ret ENOENT) 257) m' evs) := by
  constructor <;> sys_refute

/-! ## The implied directory: a key living under the name

A key "a/b" means reality has a DIRECTORY "a", and a non-empty one (#1753):
unlinking "a" is -EISDIR, from `may_delete`'s `d_is_dir(victim)`
(fs/namei.c:3289-3290, Linux v6.18.46) through `vfs_unlink` (:4658), and
removing it with AT_REMOVEDIR is -ENOTEMPTY, from the filesystem's
`->rmdir` through `vfs_rmdir` (:4552; on the harness's tmpfs that is
`shmem_rmdir`, mm/shmem.c:4034-4035, Linux v6.18.46).  The image's
directories are taken to be real ones, not symlinks to directories
(bugs/unlinkat-implied-directory-assumed-real.md).  The test runs before the lookup so that the
unrealizable image with both keys gets the directory's answers.  Only a
literal can set this up — the harness always starts from an empty
directory, and no syscall a probe can issue puts a separator in a key. -/

/-- The realizable image, `a/b` and not `a`: unlink is -EISDIR.
rocq-twin: unlinkat_implied_directory_answers
kernel: fs/namei.c:may_delete,vfs_unlink@v6.18.46 -/
theorem implied_directory_unlink_is_eisdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) implied_dir_model o
      ↔ o = Ok (ledgered (errno_ret EISDIR) 2) implied_dir_model [] := by
  sys_norm

/-- …and neither the map's -ENOENT nor a removal is claimed, nor an
injectable errno: the answer is deterministic.
rocq-twin: unlinkat_implied_directory_answers
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem implied_directory_unlink_answers_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) implied_dir_model
        (Ok (ledgered (errno_ret ENOENT) 2) m' evs)
    ∧ ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) implied_dir_model
        (Ok (ledgered (Z_to_bv 64 0) 2) m' evs)
    ∧ ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) implied_dir_model
        (Ok (ledgered (errno_ret EACCES) 2) m' evs) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute

/-- Under AT_REMOVEDIR the same image is -ENOTEMPTY: `b` is in `a`.
rocq-twin: unlinkat_implied_directory_answers
kernel: fs/namei.c:do_rmdir,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem implied_directory_rmdir_is_enotempty (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) implied_dir_model o
      ↔ o = Ok (ledgered (errno_ret ENOTEMPTY) 2) implied_dir_model [] := by
  sys_norm

/-- …refusing the regular file's -ENOTDIR, the other call's -EISDIR and a
removal.
rocq-twin: unlinkat_implied_directory_answers
kernel: fs/namei.c:may_delete,vfs_rmdir@v6.18.46 -/
theorem implied_directory_rmdir_answers_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) implied_dir_model
        (Ok (ledgered (errno_ret ENOTDIR) 2) m' evs)
    ∧ ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) implied_dir_model
        (Ok (ledgered (errno_ret EISDIR) 2) m' evs)
    ∧ ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) implied_dir_model
        (Ok (ledgered (Z_to_bv 64 0) 2) m' evs) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_refute

/-- The trailing-separator spelling `a/`: unlink reaches `do_unlinkat`'s
`slashes:` label (:4767-4772), whose `d_is_dir` is -EISDIR; rmdir has no
such label and is -ENOTEMPTY.
rocq-twin: unlinkat_implied_directory_trailing_slash
kernel: fs/namei.c:do_unlinkat,do_rmdir@v6.18.46 -/
theorem implied_directory_trailing_slash_answers (o o' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47])) implied_dir_model o
       ↔ o = Ok (ledgered (errno_ret EISDIR) 3) implied_dir_model [])
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97, 47])) implied_dir_model o'
       ↔ o' = Ok (ledgered (errno_ret ENOTEMPTY) 3) implied_dir_model []) := by
  constructor <;> sys_norm

/-- The UNREALIZABLE image, where `a` and `a/b` are both keys: here the
lookup of `a` would SUCCEED, so a test placed after it would remove the
file (flags 0) or answer the file's -ENOTDIR (AT_REMOVEDIR).
rocq-twin: unlinkat_implied_directory_unrealizable_image
kernel: fs/namei.c:may_delete,vfs_unlink,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem unrealizable_image_answers (o o' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unrealizable_model o
       ↔ o = Ok (ledgered (errno_ret EISDIR) 2) unrealizable_model [])
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) unrealizable_model o'
       ↔ o' = Ok (ledgered (errno_ret ENOTEMPTY) 2) unrealizable_model []) := by
  constructor <;> sys_norm

/-- …and the removal is refused on it.
rocq-twin: unlinkat_implied_directory_unrealizable_image
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem unrealizable_image_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unrealizable_model
        (Ok (ledgered (Z_to_bv 64 0) 2) m' evs) := by
  sys_refute

/-- A key `a/../b` says `a` is a directory and nothing about what is in it
(`fs_entry_under`): unlink is still -EISDIR, and rmdir is -ENOTEMPTY or the
removal, 0, since an empty directory inside `a` would leave no key; the
removal turns the key into `b` (`fs_rmdir_implied`).  Beside a key `a/c`
that does show an entry, rmdir is -ENOTEMPTY alone again.
rocq-twin: unlinkat_implied_directory_emptiness_unknown
kernel: fs/namei.c:link_path_walk,may_delete,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem implied_directory_emptiness_unknown (o o' o'' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) dotdot_key_model o
       ↔ o = Ok (ledgered (errno_ret EISDIR) 2) dotdot_key_model [])
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dotdot_key_model o'
       ↔ (o' = Ok (ledgered (errno_ret ENOTEMPTY) 2) dotdot_key_model []
          ∨ o' = Ok (ledgered (Z_to_bv 64 0) 2) dotdot_removed_model []))
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dotdot_and_entry_model o''
       ↔ o'' = Ok (ledgered (errno_ret ENOTEMPTY) 2) dotdot_and_entry_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- …refusing an injectable errno, and a removal that leaves the map as it
was.
rocq-twin: unlinkat_implied_directory_emptiness_unknown
kernel: fs/namei.c:vfs_rmdir@v6.18.46 -/
theorem implied_directory_emptiness_unknown_rejected (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dotdot_key_model
        (Ok (ledgered (errno_ret EBUSY) 2) dotdot_key_model evs)
    ∧ ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dotdot_key_model
        (Ok (ledgered (Z_to_bv 64 0) 2) dotdot_key_model evs) := by
  constructor <;> sys_refute

/-- The removal changes the map the way it changes the tree: from one image
holding every shape, `a/`, `a/..` and `a/../` go, `a/../../c` becomes
`../c`, `a/./..//b` becomes `b` and `ab` stays; beside a key `b` already
held, the renamed `a/../b` keeps its own contents; and after the removal a
second rmdir of `a` is -ENOENT, as on Linux.
rocq-twin: unlinkat_implied_directory_removal
kernel: fs/namei.c:link_path_walk,do_rmdir,vfs_rmdir,lookup_one_qstr_excl@v6.18.46 -/
theorem implied_directory_removal (o o' o'' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) shapes_model o
       ↔ (o = Ok (ledgered (errno_ret ENOTEMPTY) 2) shapes_model []
          ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) shapes_removed_model []))
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) clash_model o'
       ↔ (o' = Ok (ledgered (errno_ret ENOTEMPTY) 2) clash_model []
          ∨ o' = Ok (ledgered (Z_to_bv 64 0) 2) dotdot_removed_model []))
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dotdot_removed_model o''
       ↔ o'' = Ok (ledgered (errno_ret ENOENT) 2) dotdot_removed_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- A descriptor naming the key the removal would rename leaves the call
declined, rather than leave the descriptor naming nothing; a descriptor on
a key the removal leaves alone (`x`) does not.  A key that shows an entry
(`a/b`) makes the answer -ENOTEMPTY before the guard is read, held
descriptor or not.
rocq-twin: unlinkat_implied_directory_removal_fd_guard
kernel: fs/namei.c:do_rmdir,vfs_rmdir@v6.18.46 -/
theorem implied_directory_removal_fd_guard (o o' o'' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dotdot_held_model o
      ↔ o = Unmodeled)
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dotdot_other_held_model o'
      ↔ (o' = Ok (ledgered (errno_ret ENOTEMPTY) 2) dotdot_other_held_model []
         ∨ o' = Ok (ledgered (Z_to_bv 64 0) 2) dotdot_other_held_removed_model []))
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) implied_dir_held_model o''
      ↔ o'' = Ok (ledgered (errno_ret ENOTEMPTY) 2) implied_dir_held_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- Keys `a/` and `a/.` imply the directory `a` but name `a` itself and show
nothing in it (`fs_entry_under`'s empty test, which `a/.` reaches through
`path_skip_noop_components`): unlink is still -EISDIR, and rmdir is
-ENOTEMPTY or the removal, which drops the key.
rocq-twin: unlinkat_implied_directory_edges
kernel: fs/namei.c:may_delete,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem implied_directory_without_an_entry (o o' o'' o''' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) slash_key_model o
       ↔ o = Ok (ledgered (errno_ret EISDIR) 2) slash_key_model [])
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) slash_key_model o'
       ↔ (o' = Ok (ledgered (errno_ret ENOTEMPTY) 2) slash_key_model []
          ∨ o' = Ok (ledgered (Z_to_bv 64 0) 2) unlinked_model []))
    ∧ (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) dot_key_model o''
       ↔ o'' = Ok (ledgered (errno_ret EISDIR) 2) dot_key_model [])
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dot_key_model o'''
       ↔ (o''' = Ok (ledgered (errno_ret ENOTEMPTY) 2) dot_key_model []
          ∨ o''' = Ok (ledgered (Z_to_bv 64 0) 2) unlinked_model [])) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- `ab/c` shows nothing in `a`: beside `a/../b`, rmdir is still -ENOTEMPTY
or the removal, which keeps `ab/c`, so the entry test reads a component and
not a byte prefix.
rocq-twin: unlinkat_implied_directory_edges
kernel: fs/namei.c:link_path_walk,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem byte_prefix_shows_no_entry (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) byte_prefix_entry_model o
      ↔ (o = Ok (ledgered (errno_ret ENOTEMPTY) 2) byte_prefix_entry_model []
         ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) byte_prefix_removed_model []) := by
  sys_norm

/-- `a/./b`, `a//b` and `a/.//./b` each name `b` inside `a`: separator runs
and "." components do not move the walk (`path_skip_noop_components`), so
rmdir is -ENOTEMPTY, and unlink is still -EISDIR.
rocq-twin: unlinkat_implied_directory_noop_components
kernel: fs/namei.c:link_path_walk,handle_dots,may_delete,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem noop_components_show_the_entry (o o' o'' o''' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) dot_entry_model o
       ↔ o = Ok (ledgered (errno_ret EISDIR) 2) dot_entry_model [])
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dot_entry_model o'
       ↔ o' = Ok (ledgered (errno_ret ENOTEMPTY) 2) dot_entry_model [])
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) slash_entry_model o''
       ↔ o'' = Ok (ledgered (errno_ret ENOTEMPTY) 2) slash_entry_model [])
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) mixed_entry_model o'''
       ↔ o''' = Ok (ledgered (errno_ret ENOTEMPTY) 2) mixed_entry_model []) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sys_norm

/-- …and a removal is refused on `a/./b`.
rocq-twin: unlinkat_implied_directory_noop_components
kernel: fs/namei.c:vfs_rmdir@v6.18.46 -/
theorem noop_components_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dot_entry_model
        (Ok (ledgered (Z_to_bv 64 0) 2) m' evs) := by
  sys_refute

/-- `a/./../b` passes through `a` and back out, and `a/./` names `a` itself:
neither shows an entry, so rmdir is -ENOTEMPTY or the removal, which makes
the first `b` and drops the second.  `a/.b` shows the name `.b`, which only
starts with a dot, so rmdir is -ENOTEMPTY alone.
rocq-twin: unlinkat_implied_directory_noop_components
kernel: fs/namei.c:link_path_walk,handle_dots,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem noop_components_edges (o o' o'' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dot_dotdot_key_model o
       ↔ (o = Ok (ledgered (errno_ret ENOTEMPTY) 2) dot_dotdot_key_model []
          ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) dotdot_removed_model []))
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dot_slash_key_model o'
       ↔ (o' = Ok (ledgered (errno_ret ENOTEMPTY) 2) dot_slash_key_model []
          ∨ o' = Ok (ledgered (Z_to_bv 64 0) 2) unlinked_model []))
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) dot_name_entry_model o''
       ↔ o'' = Ok (ledgered (errno_ret ENOTEMPTY) 2) dot_name_entry_model []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

set_option maxRecDepth 32768 in
/-- A 256-byte name with a key under it declines ahead of the
implied-directory answers: the filesystem's -ENAMETOOLONG comes from its
lookup, before `may_delete` and `->rmdir` run.
rocq-twin: unlinkat_implied_directory_edges
kernel: fs/ext4/namei.c:ext4_lookup; fs/libfs.c:simple_lookup@v6.18.46 -/
theorem over_name_max_precedes_implied_directory (o o' : outcome SyscallEffect) :
    (unlinkat_spec cwd_fd 8192 0 (mem_in (name_at name256)) long_key_model o ↔ o = Unmodeled)
    ∧ (unlinkat_spec cwd_fd 8192 512 (mem_in (name_at name256)) long_key_model o'
         ↔ o' = Unmodeled) := by
  constructor <;> sys_norm

/-- The contrast, so the guard is a COMPONENT prefix and not a byte prefix:
`ab` does not live under `a`, and the removal goes through, leaving the
map in its canonical sorted form.
rocq-twin: unlinkat_byte_prefix_is_not_a_directory
kernel: fs/namei.c:do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem byte_prefix_is_not_a_directory (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) ab_model o
      ↔ (env_failure o 2 ab_model ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) ab_unlinked_model []) := by
  sys_norm

/-- …and the removal is of `a`, not of `ab`: a post-image that kept `a`
and dropped `ab` is refused.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem byte_prefix_wrong_entry_rejected (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) ab_model
        (Ok (ledgered (Z_to_bv 64 0) 2) (fixture_of (fs := [([97], [])])) evs) := by
  sys_refute

/-- A name that EXTENDS a key is not under it either: "ab" over an image
holding `a` is absent and -ENOENT — `dir_prefixb`'s arm for a path longer
than the key answers `false`.
kernel: fs/namei.c:lookup_one_qstr_excl@v6.18.46 -/
theorem name_extending_a_key_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 98])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 3) unlink_model [] := by
  sys_norm

/-- A directory the name has nothing to do with does not imply it: with
`b/c` the only key, `a` is absent and -ENOENT.  This is the pin that
holds `dir_prefixb` to comparing the bytes, not just the separator
position.
kernel: fs/namei.c:lookup_one_qstr_excl@v6.18.46 -/
theorem unrelated_directory_key_does_not_imply (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) bc_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 2) bc_model [] := by
  sys_norm

/-! ## `lookup_one_qstr_excl`: an absent name is -ENOENT, under either flag

The lookup answers -ENOENT for a negative dentry when the caller passed no
LOOKUP_CREATE (fs/namei.c:1713-1716, Linux v6.18.46), and neither `do_unlinkat` (:4729)
nor `do_rmdir` (:4600) does.  So an absent name never reaches
`do_unlinkat`'s `slashes:` label (:4734-4735) nor `may_delete` (:4658,
:4532): its -ENOENT precedes both -ENOTDIRs. -/

/-- An absent name is -ENOENT.
kernel: fs/namei.c:lookup_one_qstr_excl@v6.18.46 -/
theorem absent_name_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) empty_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 2) empty_model [] := by
  sys_norm

/-- …under AT_REMOVEDIR too, ahead of `may_delete`'s -ENOTDIR.
kernel: fs/namei.c:do_rmdir,lookup_one_qstr_excl@v6.18.46 -/
theorem absent_name_rmdir_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) empty_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 2) empty_model [] := by
  sys_norm

/-- An absent "a/" is -ENOENT: the trailing separator is tested only on
the arm where the lookup FOUND something.
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem absent_trailing_slash_is_enoent (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47])) empty_model o
      ↔ o = Ok (ledgered (errno_ret ENOENT) 3) empty_model [] := by
  sys_norm

/-- …so the `slashes:` -ENOTDIR is not its answer.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENOTDIR -- slash-absent -/
theorem absent_trailing_slash_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47])) empty_model
        (Ok (ledgered (errno_ret ENOTDIR) 3) m' evs) := by
  sys_refute

/-- …nor is `may_delete`'s under AT_REMOVEDIR.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat#2:ret=-ENOTDIR -- slash-absent -/
theorem absent_trailing_slash_rmdir_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97, 47])) empty_model
        (Ok (ledgered (errno_ret ENOTDIR) 3) m' evs) := by
  sys_refute

/-! ## `may_delete(…, isdir = 1)`: rmdir of a regular file

Under AT_REMOVEDIR `do_rmdir` (fs/namei.c:4607, Linux v6.18.46) hands the found dentry to
`vfs_rmdir` (:4529-4567), whose `may_delete(idmap, dir, dentry, 1)` (:4532)
answers -ENOTDIR to `!d_is_dir(victim)` (:3284-3286).  A model file is
always a regular file, so rmdir of one never succeeds, and the file
survives.  THE APPROXIMATION this arm carries is the one every
deterministic arm does (the table in `Sys/Fs/Namei.lean`): ahead of that
-ENOTDIR sit `do_rmdir`'s mnt_want_write -EROFS (:4595-4597) and
security_path_rmdir (:4604-4606), and inside `may_delete` itself the
`inode_permission` -EACCES (:3274-3276) and the two -EPERM clauses
(:3277-3283) come first.  The arm answers -ENOTDIR alone — exact in the
harness's writable, non-sticky, read-write working directory, and the
same narrowing Rocq's arm makes. -/

/-- rmdir of a file is -ENOTDIR, the file untouched.
kernel: fs/namei.c:do_rmdir,vfs_rmdir,may_delete@v6.18.46 -/
theorem rmdir_of_a_file_is_enotdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOTDIR) 2) unlink_model [] := by
  sys_norm

/-- The rmdir answer is decided before the open-fd guard: with `a` held open
through fd 3, AT_REMOVEDIR still answers `may_delete`'s -ENOTDIR (the fds
are irrelevant to it) rather than declining.  No probe case holds an fd open
across an rmdir of a file; the kernel reading is the evidence.
kernel: fs/namei.c:do_rmdir,may_delete@v6.18.46 -/
theorem rmdir_beats_open_fd (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) open_fd_model o
      ↔ o = Ok (ledgered (errno_ret ENOTDIR) 2) open_fd_model [] := by
  sys_norm

/-- AT_REMOVEDIR can never succeed here.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=0 -- rmdir-file -/
theorem rmdir_of_a_file_success_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) unlink_model
        (Ok (ledgered (Z_to_bv 64 0) 2) m' evs) := by
  sys_refute

/-- …and the arm is deterministic: -ENOMEM — `d_alloc` failing in
`lookup_one_qstr_excl` (:1701-1703), ahead of `may_delete` — is one of
the untracked conditions the section note names, and the model refuses it.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENOMEM -- rmdir-file -/
theorem rmdir_of_a_file_enomem_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97])) unlink_model
        (Ok (ledgered (errno_ret ENOMEM) 2) m' evs) := by
  sys_refute

/-- A trailing separator changes nothing under AT_REMOVEDIR: `do_rmdir` never
tests `last.name[last.len]`, and `may_delete(…, 1)` answers -ENOTDIR for the
regular file as for the bare name (fs/namei.c:3284-3286, Linux v6.18.46).
probe: testing/syscall-check/tests/unlinkat_spec.c#conform -- slash-multi -/
theorem rmdir_trailing_slash_on_a_file_is_enotdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97, 47])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOTDIR) 3) unlink_model [] := by
  sys_norm

/-- …and cannot succeed, separator or not.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat#3:ret=0 -- slash-multi -/
theorem rmdir_trailing_slash_success_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 512 (mem_in (name_at [97, 47])) unlink_model
        (Ok (ledgered (Z_to_bv 64 0) 3) m' evs) := by
  sys_refute

/-! ## `do_unlinkat`'s `slashes:`: a trailing separator on a present file

`do_unlinkat` tests `last.name[last.len]` — the byte just past the
component — once the lookup found something (fs/namei.c:4734-4735, Linux v6.18.46), and
jumps to `slashes:` (:4767-4772), which is -ENOTDIR for anything but a
directory.  The jump is from ABOVE `vfs_unlink` (:4741), so `may_delete`
never runs and the file survives.  What does precede the test is
`do_unlinkat`'s mnt_want_write call (:4724-4726, -EROFS) and
`lookup_one_qstr_excl` (:4729: -ENOENT for a dead parent, :1698-1699, and
-ENOMEM from `d_alloc`, :1701-1703); the arm answers -ENOTDIR alone, the
approximation the Sys docstring's table names. -/

/-- "a/" names the same component as "a", and the byte past it is "/":
-ENOTDIR, the file untouched.
rocq-twin: unlinkat_trailing_slash_on_a_file_is_enotdir
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem trailing_slash_on_a_file_is_enotdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOTDIR) 3) unlink_model [] := by
  sys_norm

/-- A kernel that removed the file through "a/" and returned 0 is a
kernel this model must refuse.  Without the `path_trailing_slash` test
this case is the ordinary removal and accepts.
rocq-twin: unlinkat_trailing_slash_success_rejected
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=0 -- slash -/
theorem trailing_slash_success_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47])) unlink_model
        (Ok (ledgered (Z_to_bv 64 0) 3) m' evs) := by
  sys_refute

/-- The arm is deterministic too: the -ENOMEM `d_alloc` can raise ahead of it
(:1701-1703) is the approximation the section note names, and the model
refuses it.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-ENOMEM -- slash -/
theorem trailing_slash_enomem_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47])) unlink_model
        (Ok (ledgered (errno_ret ENOMEM) 3) m' evs) := by
  sys_refute

/-- -EISDIR is `slashes:`'s answer for a DIRECTORY, which a model file
never is.
probe: testing/syscall-check/tests/unlinkat_spec.c#reject --mutate unlinkat:ret=-EISDIR -- slash -/
theorem trailing_slash_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47])) unlink_model
        (Ok (ledgered (errno_ret EISDIR) 3) m' evs) := by
  sys_refute

/-- Two trailing separators are one byte to `do_unlinkat`: "a//" is
-ENOTDIR as "a/" is.
kernel: fs/namei.c:link_path_walk,do_unlinkat@v6.18.46 -/
theorem double_trailing_slash_is_enotdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47, 47])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOTDIR) 4) unlink_model [] := by
  sys_norm

/-- `slashes:` is decided from the dentry alone: a file held open through
fd 3 still answers -ENOTDIR to "a/", ahead of the open-fd guard below.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem trailing_slash_beats_open_fd (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97, 47])) open_fd_model o
      ↔ o = Ok (ledgered (errno_ret ENOTDIR) 3) open_fd_model [] := by
  sys_norm

/-! ## The open-fd guard: an unlinked-but-open file has no image here

`do_unlinkat` (fs/namei.c:4736-4737, Linux v6.18.46) takes a reference to the inode
before it calls `vfs_unlink`, and drops it only after the directory entry
is gone (:4747-4749, "truncate the inode here"), so Linux keeps an unlinked file's
contents reachable through an fd already open on it until the last close.
The model's file fds record a PATH, not an inode, so after a removal they
would name nothing; rather than weaken the invariant the read and write
specs rest on, unlinking a path some fd still names declines. -/

/-- The file `a` open read-only through fd 3: declines.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- readfd -/
theorem open_fd_on_the_name_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) open_fd_model o ↔ o = Unmodeled := by
  sys_norm

/-- The removal Linux performs is not claimed, because its post-state — an
fd on an inode with no path — has no representation.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- readfd -/
theorem open_fd_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) open_fd_model
        (Ok (ledgered (Z_to_bv 64 0) 2) m' evs) := by
  sys_refute

/-- A file fd opened for writing names its path just as a read-only one
does: declines too (the probe's `openfd` creates its fd with `WR_CREATE`).
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- openfd -/
theorem open_write_fd_on_the_name_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) open_wfd_model o ↔ o = Unmodeled := by
  sys_norm

/-- The kinds that name NO path — a directory fd, a socket, both pipe ends,
/dev/null, /dev/urandom — and a file fd on ANOTHER file do not block the removal: `a` is
removed and `b`, still open, stays.
kernel: fs/namei.c:do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem other_kinds_do_not_name_the_path (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) kinds_model o
      ↔ (env_failure o 2 kinds_model ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) kinds_unlinked_model []) := by
  sys_norm

/-- Rocq's `fd_names_path_ignores_a_pipe_end` (theories/LinuxProcessSem/Checks/Cases/Fs/Pipe.v),
stated here because the predicate is this file's: neither pipe end names
the path, an `FdFileW` on the same path does, and a pipe end BESIDE that
file does not mask its answer — the pipe arm recurses rather than deciding.
Neither pipe end is reached through path resolution: `create_pipe_files`
(fs/pipe.c:926-957, Linux v6.18.46) allocates both on the anonymous
`pipe_mnt`.  Rocq's Checks/Cases/Fs/Pipe.v states this as
`fd_names_path_ignores_a_pipe_end`.
kernel: fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem fd_names_path_ignores_a_pipe_end :
    fd_names_path [(3, .FdPipe 0 false)] [102] = false
    ∧ fd_names_path [(4, .FdPipe 0 true)] [102] = false
    ∧ fd_names_path [(5, .FdFileW [102] 0)] [102] = true
    ∧ fd_names_path [(3, .FdPipe 0 false), (5, .FdFileW [102] 0)] [102] = true := by
  decide

/-- Every kind that names no path sits AHEAD of the file fd on `a` here, and
the removal still declines: each of those arms recurses past its entry.  A
short-circuiting arm would miss the `FdFile` behind it and accept the removal,
and no other fixture in this file would notice.
kernel: fs/namei.c:do_unlinkat,vfs_unlink; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem open_fd_behind_other_kinds_declines (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) kinds_before_open_fd_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and the removal such an arm would accept is refused.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem open_fd_behind_other_kinds_removal_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) kinds_before_open_fd_model
        (Ok (ledgered (Z_to_bv 64 0) 2) m' evs) := by
  sys_refute

/-! ## The removal, and what may fail it

Past every guard, `do_unlinkat` (fs/namei.c:4741-4742, Linux v6.18.46) calls `vfs_unlink`
(:4654-4696), which removes exactly the one directory entry the last
component names
(`Fs.fs_remove`; the general laws are `Checks/Cases/Fs.lean`'s), and the
process is otherwise unchanged.  Around it sit the five untracked
conditions of `unlinkat_errnos`, each real for an ordinary entry the model
cannot tell apart from this one: `getname_flags`'s and
`lookup_one_qstr_excl`'s -ENOMEM (:146-148, :1701-1703); `may_delete`'s
`inode_permission(idmap, dir, MAY_WRITE | MAY_EXEC)` (:3274-3276), answered
-EACCES by `generic_permission` (:485, the directory branch); `may_delete`'s -EPERM for an
append-only parent or a sticky, append-only, immutable or swap-file entry
(:3277-3283); -EROFS from `do_unlinkat`'s mnt_want_write call (:4724-4726),
answered by `mnt_get_write_access` (fs/namespace.c:476-478, Linux v6.18.46); and `vfs_unlink`'s -EBUSY
for a mount point over the entry (fs/namei.c:4669-4670, Linux v6.18.46).  -ENOENT is not
among them: file existence is tracked. -/

/-- The whole arm: one of the five failures, or the removal under the
two-byte ledger.
kernel: fs/namei.c:do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem present_name_is_removed (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model o
      ↔ (env_failure o 2 unlink_model ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) unlinked_model []) := by
  sys_norm

/-- Names are byte strings: a component of the bytes 0xff 0x01 is hashed and
compared as bytes (`hash_name`, fs/namei.c:2404-2424, Linux v6.18.46) and
removed like any other; the ledger is the two bytes and the NUL.
probe: testing/syscall-check/tests/unlinkat_spec.c#conform -- bytes -/
theorem high_bytes_are_an_ordinary_name (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [255, 1])) hi_model o
      ↔ (env_failure o 3 hi_model ∨ o = Ok (ledgered (Z_to_bv 64 0) 3) unlinked_model []) := by
  sys_norm

/-- Kernel memory: `__getname` (fs/namei.c:146-148) or `d_alloc`
(:1701-1703) can fail, and either is -ENOMEM.
kernel: fs/namei.c:getname_flags,lookup_one_qstr_excl@v6.18.46 -/
theorem removal_enomem_admitted :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model
      (Ok (ledgered (errno_ret ENOMEM) 2) unlink_model []) := by
  sys_norm

/-- The parent's write and search permission: `may_delete`'s
`inode_permission` (:3274-3276), -EACCES from `generic_permission`.
kernel: fs/namei.c:may_delete,generic_permission@v6.18.46 -/
theorem removal_eacces_admitted :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model
      (Ok (ledgered (errno_ret EACCES) 2) unlink_model []) := by
  sys_norm

/-- An append-only parent, or a sticky, append-only or immutable entry:
`may_delete`'s -EPERM (:3277-3283).
kernel: fs/namei.c:may_delete@v6.18.46 -/
theorem removal_eperm_admitted :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model
      (Ok (ledgered (errno_ret EPERM) 2) unlink_model []) := by
  sys_norm

/-- A read-only mount: `do_unlinkat` calls mnt_want_write ahead of the lookup
(fs/namei.c:4724-4726, Linux v6.18.46), and `mnt_get_write_access` answers -EROFS
(fs/namespace.c:476-478, Linux v6.18.46).
kernel: fs/namespace.c:mnt_want_write,mnt_get_write_access@v6.18.46 -/
theorem removal_erofs_admitted :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model
      (Ok (ledgered (errno_ret EROFS) 2) unlink_model []) := by
  sys_norm

/-- A mount point over the entry: `vfs_unlink`'s `is_local_mountpoint`
(:4669-4670), -EBUSY.
kernel: fs/namei.c:vfs_unlink@v6.18.46 -/
theorem removal_ebusy_admitted :
    unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model
      (Ok (ledgered (errno_ret EBUSY) 2) unlink_model []) := by
  sys_norm

/-- -ENOENT is NOT injectable on a present name: file existence is tracked,
and `lookup_one_qstr_excl` found the entry.
kernel: fs/namei.c:lookup_one_qstr_excl@v6.18.46 -/
theorem removal_enoent_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model
        (Ok (ledgered (errno_ret ENOENT) 2) m' evs) := by
  sys_refute

/-- A success that leaves the entry in place is refused: `vfs_unlink`
removes it.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem removal_kept_entry_rejected (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model
        (Ok (ledgered (Z_to_bv 64 0) 2) unlink_model evs) := by
  sys_refute

/-- Past the flag test the ledger is REQUIRED: the removal really did read
the path, so denying it is a rejection.  Contrast `bad_flag_ledger_rejected`
— the two differ in the flag word alone, and the ledger obligation flips
with it.
rocq-twin: unlinkat_removal_needs_the_copyin
kernel: fs/namei.c:getname_flags,do_unlinkat@v6.18.46 -/
theorem removal_needs_the_ledger (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- And the EXTENT is the NUL-terminated prefix — `a` and the NUL, two
bytes.  One byte short is the name without its terminator, which is not
what `getname()` reads.
rocq-twin: unlinkat_copyin_extent_is_the_nul_terminated_prefix
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem ledger_extent_is_the_nul_terminated_prefix (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model
        (Ok (ledgered (Z_to_bv 64 0) 1) m' evs) := by
  sys_refute

/-- The removal is never a decline: every guard has been passed.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem removal_never_declines :
    ¬ unlinkat_spec cwd_fd 8192 0 (mem_in (name_at [97])) unlink_model Unmodeled := by
  sys_refute

/-! ## The `int` narrowing, as the spec sees it

`SYSCALL_DEFINE3(unlinkat, int, dfd, const char __user *, pathname, int,
flag)` (fs/namei.c:4775, Linux v6.18.46) takes `dfd` and `flag` as `int`,
narrowed by `__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-88,
Linux v6.18.46) through `__SC_CAST` (include/linux/syscalls.h:132, Linux
v6.18.46).  The pins here state what `unlinkat_spec` answers for the flag word
the register carries; that the dispatcher hands the spec a0 narrowed and a1 as
the pathname is pinned beside `Checks.Cases.Checks.DispatchSurface`, which is
the module that imports `Specs`. -/

/-- a2 = 2^32 is a flag word of 0 to `int flag`: the removal, not -EINVAL.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:unlinkat,do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem flag_truncates_to_32_bits (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 4294967296 (mem_in (name_at [97])) unlink_model o
      ↔ (env_failure o 2 unlink_model ∨ o = Ok (ledgered (Z_to_bv 64 0) 2) unlinked_model []) := by
  sys_norm

/-- …and a model reading the whole register would answer -EINVAL there.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem flag_2_pow_32_einval_rejected (m' : Model) (evs : List event) :
    ¬ unlinkat_spec cwd_fd 8192 4294967296 (mem_in (name_at [97])) unlink_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- a2 = 2^32 + AT_REMOVEDIR is AT_REMOVEDIR: rmdir of a file, -ENOTDIR.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:unlinkat,do_rmdir,may_delete@v6.18.46 -/
theorem flag_2_pow_32_plus_removedir_is_rmdir (o : outcome SyscallEffect) :
    unlinkat_spec cwd_fd 8192 4294967808 (mem_in (name_at [97])) unlink_model o
      ↔ o = Ok (ledgered (errno_ret ENOTDIR) 2) unlink_model [] := by
  sys_norm

/-! ## A17: FdFileRW and FdFileA -/

/-- Rocq: `Namei.fd_names_path`, Namei.v:194 at 96c2debdb.
The read-write description retains the opened file:
fs/namei.c, do_unlinkat, Linux v6.18.46 removes the named directory entry;
the model declines unlinking a path still held by a description.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem a17_rdwr_names_its_path :
    fd_names_path [(3, .FdFileRW [102] 0)] [102] = true := by
  decide

/-- Rocq: `Namei.fd_names_path`, Namei.v:194 at 96c2debdb.
An unrelated read-write description does not hide the later opener:
fs/namei.c, do_unlinkat, Linux v6.18.46 removes the named directory entry;
the model declines unlinking a path still held by a description.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem a17_rdwr_searches_past_other_path :
    fd_names_path [(3, .FdFileRW [103] 0), (4, .FdFile [102] 0)] [102] = true := by
  decide

/-- Rocq: `Namei.fd_names_path`, Namei.v:194 at 96c2debdb.
An unrelated read-write description does not name the removed path:
fs/namei.c, do_unlinkat, Linux v6.18.46 removes the named directory entry;
the model declines unlinking a path still held by a description.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem a17_rdwr_does_not_name_other_path :
    fd_names_path [(3, .FdFileRW [103] 0)] [102] = false := by
  decide

/-- Rocq: `Namei.fd_names_path`, Namei.v:193 at 96c2debdb.
The append-mode description retains the opened file:
fs/namei.c, do_unlinkat, Linux v6.18.46 removes the named directory entry;
the model declines unlinking a path still held by a description.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem a17_append_names_its_path :
    fd_names_path [(3, .FdFileA [102] 0)] [102] = true := by
  decide

/-- Rocq: `Namei.fd_names_path`, Namei.v:193 at 96c2debdb.
An unrelated append-mode description does not hide the later opener:
fs/namei.c, do_unlinkat, Linux v6.18.46 removes the named directory entry;
the model declines unlinking a path still held by a description.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem a17_append_searches_past_other_path :
    fd_names_path [(3, .FdFileA [103] 0), (4, .FdFile [102] 0)] [102] = true := by
  decide

/-- Rocq: `Namei.fd_names_path`, Namei.v:193 at 96c2debdb.
An unrelated append-mode description does not name the removed path:
fs/namei.c, do_unlinkat, Linux v6.18.46 removes the named directory entry;
the model declines unlinking a path still held by a description.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem a17_append_does_not_name_other_path :
    fd_names_path [(3, .FdFileA [103] 0)] [102] = false := by
  decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Namei
