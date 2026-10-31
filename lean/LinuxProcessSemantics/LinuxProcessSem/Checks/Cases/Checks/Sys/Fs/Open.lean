-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/Open.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Open
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Pipe
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.Open — what the openat, faccessat, close and ftruncate checkers accept and refuse, and what their witnesses name

Pins over `Checks.Sys.Fs.Open.check_openat`, `check_faccessat`,
`check_faccessat2`, `check_close` and `check_ftruncate`, the twins of
`theories/LinuxProcessSem/Checks/Sys/Fs/Open.v`'s checkers for openat,
faccessat, faccessat2, close and ftruncate, and over their witnesses, the
twins of `theories/LinuxProcessSem/Checks/Witness/Fs/Open.v`'s.  Not part of the
trusted specification: this file is QA on the checkers, written to be READ.
Each pin carries one evidence line, and
`tools/check_lean_pin_evidence.py` holds the line to more than its form:
it resolves what the line cites and, by the rules its docstring states,
refuses some lines that do not fit their pin.  Whether a cited function
means what the pin says, beyond spelling the constants the pin names,
is among what that docstring says the checker cannot see, and is
review's to judge.  A
`model:` pin's statement is about the model alone.  So is any conjunct
that is the model's own choice, under a `kernel:` line as well, such as a
decline (`CheckUnmodeled`, or a witness's `Unmodeled`), since no kernel
answers `unmodeled`, or its absence (`check_close_never_declines`), a
refusal by a narrowing the spec records (the -EMFILE of
`read_absent_is_enoent`), or an answer resting on a premise of the spec's
(the channel pin under `# ftruncate (46)`).  Line numbers are Linux
v6.18.46 (commit 1f99e9ab748f).
The openat pins come first, under the headings below; the faccessat and
faccessat2 pins follow them under their own `# faccessat (48) and
faccessat2 (439)` heading, which says what they twin and how; the close
pins follow under `# close (57)`, and the ftruncate pins under
`# ftruncate (46)`; and two sections end the file,
`OpenatThroughTheTable` and then `CloseThroughTheTable`, which state
openat's and close's pins again through `check_syscall`.

WHAT THIS TWINS.  Rocq keeps the checker's worked cases for openat in
`Checks/Cases/Fs/Open.v`, beside the spec's, as `Example`s over
`check_syscall`: `openat_live_dirfd_still_unmodeled`,
`openat_empty_path_enoent`, `o_nonblock_is_an_ignored_open_flag`,
`openat_absolute_create_unmodeled`, `openat_plain_create_still_mints_the_key`,
`openat_implied_directory_create_eisdir`,
`openat_byte_prefix_and_exact_key_still_create`,
`openat_implied_directory_excl_eexist`,
`openat_implied_directory_other_write_words`,
`openat_slash_key_in_image_unmodeled`,
`openat_localtime_enoent`, `openat_localtime_in_image_unmodeled`,
`openat_localtime_match_is_exact`, `devnull_open_by_word`,
`devnull_open_declines`, `urandom_open_by_word`, `urandom_open_declines`,
`openat_dotdot_answers_as_dot_does`, `openat_dot3_is_an_ordinary_name`,
`openat_empty_path_beats_o_creat`, `openat_directory_answers`,
`openat_directory_ignores_largefile_and_cloexec`,
`openat_directory_implied_directory_unmodeled`,
`openat_directory_name_max_boundary`, `openat_tmp_create_read_unlink`,
`openat_tmp_declared_name_reads`, `openat_tmp_excluded_shapes_unmodeled`,
`openat_tmp_name_max_boundary`, `openat_tmp_implied_directory_create_eisdir`,
`openat_tmp_implied_directory_read_unmodeled` and
`openat_tmp_implied_directory_unrealizable_image`
(`openat_tmp_unsorted_declaration_is_canonical`, the section's remaining
example, runs no syscall — it is about `State.fs_seed_tmp` alone — and is
the spec pins' to restate, as is
`openat_tmp_implied_directory_sibling_still_creates`, whose accepted effect
is a minted key beside the implied directory).  The Lean tree keeps spec pins and
checker pins apart — `Checks/Cases/Fs/Open.lean` pins the spec, this file
the checker — and this file is where those land.  They are stated on
`check_openat_row`, which applies `check_openat` as the row for 56 in
`Sys/SyscallTable.lean` applies the spec — the dirfd through `fd32`, the
pathname pointer and the flag word as they arrive — and
`OpenatThroughTheTable`, the first of the two sections that end this
file, states their conjuncts on the row again through `check_syscall`,
on `check_syscall_openat_in'`, which proves that the checked table's row
for 56 (`Checks/Arms/Fs/Open.lean`) is that application for every
dirfd, pathname pointer, flag word and memory; `check_syscall_openat_in`
is its instance at the ordinary call, `AT_FDCWD` with the pathname at
8192.  Where a Rocq example runs a second syscall
through the dispatcher after the open — the read of `/tmp/out.gif` and its
`unlinkat` in `openat_tmp_create_read_unlink`, the `write`, `read`, `close`
and `fstat` legs of the device examples — only the openat leg lands here;
the rest is the other checkers' and the dispatcher's.  Four of Rocq's
examples are over the words this checker now has arms for —
`openat_append_flag_word`, `openat_rdwr_flag_words`, `openat_rdwr_errnos`
and `openat_rdwr_dirref` — and are twinned below under those names, with
`openat_implied_directory_other_write_words` beside them: the append word
(1089) mints `State.FdFileA` and leaves an existing file's bytes alone,
the four read-write words (2, 514, 66, 578) and the two exclusive
read-write words (194, 706) mint `State.FdFileRW`, and on a directory
reference or an implied directory each answers the errno Linux gives it,
-EISDIR for the five non-exclusive words and -EEXIST for the exclusive
one.  The words BESIDE those — O_WRONLY|O_CREAT|O_EXCL|O_APPEND (1217)
and the same with O_TRUNC (1729), O_WRONLY|O_CREAT|O_APPEND|O_TRUNC
(1601), O_RDWR|O_APPEND (1026), O_RDWR|O_EXCL without O_CREAT (130) —
have no arm in spec or checker and are declined by the flag gate, before
the pathname is read.

WHY A CHECKER NEEDS PINS OF ITS OWN.  The lemmas of the checker's file tie
`check_openat` to `openat_spec` in both directions, and a checker that
declined every input, or accepted every one, would still meet them if the
spec were changed to match.  What the lemmas cannot see is a lie told from
OUTSIDE: an errno the kernel would not return, a descriptor that is not the
lowest free one, a ledger that stops short of the NUL, offered to the
checker and required to be refused.  That is what most pins below do —
with one class of refusal marked as such wherever it appears: the
-EMFILE and -EACCES the deterministic arms refuse are answers Linux CAN
give (`do_sys_openat2` reserves the descriptor at fs/open.c:1435, Linux
v6.18.46, through `get_unused_fd_flags`, fs/file.c:620-623, and starts the
walk at fs/open.c:1437), and the checker refuses them because the spec
twin does,
by the deliberate narrowing `openat_body_spec`'s docstring in
`Sys/Fs/Open.lean` records.  Those conjuncts pin the narrowing, not an
impossibility —
beside the answer the kernel does give required to be `CheckOk` in the
model the arm builds; and the pins on `check_openat_read`,
`check_openat_dir` and `check_open_result` are stated on the arm itself,
with an errno offered and rejection required, so that a checker answering
`CheckUnmodeled` everywhere fails here by name.

WHAT MEASURES THESE PINS.  Nothing in the tree yet: `tools/lean_mutate.py`
builds a spec mutant against the spec's Cases file alone, so no mutant of
either twin is compiled against this file, and its kill-rate is unmeasured
until that tool lists a checker's pins beside the spec's.

THE FIXTURES are `Checks/Cases/Fs/Open.lean`'s — `openat_in`, the images
`have_fs` ("f" holding "hi"), `under_fs` ("a/b"), `sibling_fs` ("ab"),
`exact_fs` ("a"), the device, zone and `/tmp` keys, and the models built
from them — so that spec and checker are pinned on the same tables.  Flag
words are numerals, as the spec pins spell them: 577 is
O_WRONLY|O_CREAT|O_TRUNC, 193 O_WRONLY|O_CREAT|O_EXCL, 1089
O_WRONLY|O_CREAT|O_APPEND, 65536 O_DIRECTORY, 2 O_RDWR, 256 O_NOCTTY.
Errnos are spelled by NAME wherever the kernel would spell them — so that
`tools/check_lean_pin_evidence.py`'s KMENTION rule can hold each cited
function to the errno the pin claims — and as numerals only where the
value is a lie no kernel function spells: 1 (-EPERM, a foreign errno) and
4095 (the top of the error band, no errno of the set).
An accepted effect's model is written as the fixture it is, so that a
reader sees the table and the image the arm built, not the builder.

THE `-ENAMETOOLONG` FETCH needs no 4096-byte fixture: `endless_in` reads
every address as 'a', so the walk to `PATH_MAX` is the function's and
the pin closes by `rfl` under the raised `maxRecDepth`
`Checks/Cases/Fs/Namei.lean` gives its `endless` pins.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree on what is
accepted and what is refused, and that the witness names an outcome the
checker accepts. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Open

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Open

/-- `check_openat` as the row for 56 in `Sys/SyscallTable.lean` applies
the spec: the dirfd through `fd32`, the pathname pointer and the flag word
as they arrive in a1 and a2. -/
def check_openat_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

/-- `openat_witness` applied the same way. -/
def openat_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  openat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- The effect a kernel reports for a call over the pathname at 8192: `r`
in a0, no writes, and the one copy-in of `n` bytes the fetch performed. -/
def eff_ret (r : word) (n : Nat) : SyscallEffect := with_copyins [(8192, n)] (mkEffect r [] [])

/-- The same with an errno in a0. -/
def eff_errno (e : Int) (n : Nat) : SyscallEffect := eff_ret (errno_ret e) n

/-- `openat(AT_FDCWD, 8192, flags, 0644)` over a memory with nothing
mapped: the fetch faults on its first byte. -/
def unmapped_in (flags : word) : SyscallInput := openat_in' AT_FDCWD 8192 flags (fun _ => none)

/-- `openat(AT_FDCWD, a, flags, 0644)` over `bs` then a NUL at `a`: the
ordinary call with the pathname somewhere other than 8192. -/
def path_at (a : word) (bs : List byte) (flags : word) : SyscallInput :=
  openat_in' AT_FDCWD a flags (bytes_at a (bs ++ [0]))

/-- `openat(AT_FDCWD, 8192, flags, 0644)` over a memory in which every
byte is readable and none is NUL: a pathname with no end. -/
def endless_in (flags : word) : SyscallInput := openat_in' AT_FDCWD 8192 flags (fun _ => some 97)

/-- The same over an unending pathname, with the dirfd given. -/
def endless_in' (dirfd flags : word) : SyscallInput :=
  openat_in' dirfd 8192 flags (fun _ => some 97)

/-- The effect of a call over the pathname at `a`: `r` in a0 and the one
copy-in of `n` bytes there. -/
def eff_ret_at (a r : word) (n : Nat) : SyscallEffect := with_copyins [(a, n)] (mkEffect r [] [])

/-- `r` in a0 with the pathname copy-in, beside a ledger openat never
produces: a zero-fill, an unmap, a copy. -/
def eff_ret_with_zeros (r : word) (n : Nat) : SyscallEffect :=
  with_copyins [(8192, n)] (SyscallEffect.mkEffectU r [] [(4096, 8)] [] [] [])
def eff_ret_with_unmaps (r : word) (n : Nat) : SyscallEffect :=
  with_copyins [(8192, n)] (SyscallEffect.mkEffectU r [] [] [(4096, 4096)] [] [])
def eff_ret_with_copies (r : word) (n : Nat) : SyscallEffect :=
  with_copyins [(8192, n)] (SyscallEffect.mkEffectU r [] [] [] [MemCopy.mkCopy 4096 8192 8] [])

/-! ## The flag gate comes first

`do_sys_openat2` (fs/open.c:1420, Linux v6.18.46) calls `build_open_flags`
(:1427) before `getname` (:1431), so a flag word the model does not interpret is
declined before the pathname is read — even a pathname whose fetch would
fault.  The control beside it: under O_RDONLY the same unmapped pointer IS
-EFAULT, with the one attempted byte in the ledger. -/

/-- O_NOCTTY over an unmapped pathname is `CheckUnmodeled` whatever the
kernel reported: the -EFAULT the fetch would answer (`do_strncpy_from_user`,
lib/strncpy_from_user.c:91-92) and a descriptor alike.
kernel: fs/open.c:do_sys_openat2,build_open_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem noctty_declines_before_the_path_is_read :
    check_openat_row (unmapped_in 256) (eff_errno EFAULT 1) absent_model = CheckUnmodeled
    ∧ check_openat_row (unmapped_in 256) (eff_ret 3 1) absent_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- The words BESIDE the modeled ones decline, O_NONBLOCK or not: O_NOCTTY
with O_NONBLOCK (2304), O_APPEND alone (1024), O_RDWR|O_APPEND (1026),
O_RDWR|O_EXCL without O_CREAT (130) and O_RDWR|O_DIRECTORY (65538), each
over a held "f" with the descriptor Linux would hand out (`build_open_flags`
accepts every one of them: none has a bit outside VALID_OPEN_FLAGS,
fs/open.c:1258-1259, Linux v6.18.46).  Rocq: five of the six decline legs
of `o_nonblock_is_an_ignored_open_flag`, in its order; the leg before
them, O_NOCTTY alone (256), is `bare_o_noctty_declines_on_a_held_name`
below, kept apart so that this pin's statement stays the one it pinned.
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem neighbouring_words_decline_with_or_without_o_nonblock :
    check_openat_row (openat_in [102] 2304) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 1024) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 1026) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 130) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 65538) (eff_ret 3 2) have_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- …and O_NOCTTY alone (256) over the same held "f", with the same
descriptor, declines too: `build_open_flags` accepts the word (no bit
outside VALID_OPEN_FLAGS, fs/open.c:1258-1259, Linux v6.18.46), and
`modeled_open_flags` (`Sys/Fs/Open.lean`) declines it, for the reason its
docstring gives.  Rocq: the first decline leg of
`o_nonblock_is_an_ignored_open_flag`.
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem bare_o_noctty_declines_on_a_held_name :
    check_openat_row (openat_in [102] 256) (eff_ret 3 2) have_model = CheckUnmodeled :=
  rfl

/-- THE CONTROL: O_RDONLY over the same pointer is -EFAULT — `strncpy_from_user`
(lib/strncpy_from_user.c:113-155) faults on the first byte and
`getname_flags` (fs/namei.c:157 and :162-164) returns its answer as it is,
before `path_init` (:2590) reads the AT_FDCWD dirfd — accepted with the
model unchanged and the one attempted byte in the ledger; the same errno
with an empty ledger entry, or with no ledger at all, is refused.
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem rdonly_unmapped_path_is_efault :
    check_openat_row (unmapped_in 0) (eff_errno EFAULT 1) absent_model = CheckOk absent_model []
    ∧ check_openat_row (unmapped_in 0) (eff_errno EFAULT 0) absent_model = CheckReject
    ∧ check_openat_row (unmapped_in 0) (mkEffect (errno_ret EFAULT) [] []) absent_model = CheckReject
    ∧ check_openat_row (unmapped_in 0) (eff_ret 3 1) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A flags word with bit 32 set is declined: Linux takes `flags` as an `int`
(`SYSCALL_DEFINE4(openat, …)`, fs/open.c:1463-1464) and `build_open_how`
(:1222) keeps that int, so it would open "f" O_RDONLY, while the model
reads all 64 bits; the descriptor Linux hands out is refused rather than
admitted.
kernel: fs/open.c:build_open_how@v6.18.46 -/
theorem flags_high_half_declines :
    check_openat_row (openat_in [102] 4294967296) (eff_ret 3 2) have_model = CheckUnmodeled :=
  rfl

/-- THE APPEND WORD, O_WRONLY|O_CREAT|O_APPEND (1089), on a plain name:
the descriptor is `State.FdFileA` at offset 0, an ABSENT name is created
empty and an EXISTING one KEEPS its bytes — where the clobbering word
(577), stated beside it on the same image, empties the file.  O_NONBLOCK
beside the word (3137) changes no answer, an equality between two flag
words no probe can state.  A directory reference is -EISDIR, and the
-EEXIST a reader gets backwards there is refused.  The spellings next to
the word stay declined: with O_TRUNC (1601), with O_EXCL (1217),
O_WRONLY|O_APPEND (1025) and O_RDWR|O_CREAT|O_APPEND (1090);
`modeled_open_flags` (`Sys/Fs/Open.lean`) names each and says why.
`lookup_open` creates the absent name (fs/namei.c:3787-3798, Linux
v6.18.46), `do_open` leaves an existing file's bytes alone with no
O_TRUNC (:3967-3970) and answers -EISDIR for the directory inside its
O_CREAT block (:3951-3952), and O_APPEND itself reaches `f_flags` and
nothing an arm reads (`init_file`, fs/file_table.c:198).  Rocq:
`openat_append_flag_word`.
kernel: fs/namei.c:lookup_open,do_open; fs/file_table.c:init_file@v6.18.46 -/
theorem openat_append_flag_word :
    check_openat_row (openat_in [102] 3137) (eff_ret 3 2) have_model
      = check_openat_row (openat_in [102] 1089) (eff_ret 3 2) have_model
    ∧ check_openat_row (openat_in [102] 1089) (eff_ret 3 2) have_model
        = CheckOk (fixture_of (fds := (3, .FdFileA [102] 0) :: init_fds) (fs := have_fs)) []
    ∧ check_openat_row (openat_in [102] 1089) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileA [102] 0) :: init_fds)
                              (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [102] 577) (eff_ret 3 2) have_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [102] 0) :: init_fds)
                              (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [46] 1089) (eff_errno EISDIR 2) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [46] 1089) (eff_errno EEXIST 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [102] 1601) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 1217) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 1025) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 1090) (eff_ret 3 2) have_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE SIX READ-WRITE WORDS, as the table the two bits decide.  Every
one of them mints `State.FdFileRW` at offset 0; O_TRUNC decides whether
an EXISTING file keeps its bytes (2 and 66 keep, 514 and 578 empty), and
O_CREAT what an ABSENT name gets (66, 578, 194 and 706 create it empty).
O_NONBLOCK beside O_RDWR (2050) changes no answer — an equality between
two flag words no probe can state.  The spellings beside them stay
declined: O_RDWR|O_APPEND (1026), O_RDWR|O_CREAT|O_APPEND (1090),
O_RDWR|O_EXCL without O_CREAT (130), the same with O_TRUNC (642) and
O_RDWR|O_DIRECTORY (65538).  `lookup_open` creates the absent name
(fs/namei.c:3787-3798, Linux v6.18.46), `do_open` truncates an existing
one only under O_TRUNC (:3967-3970), and `OPEN_FMODE` gives the
description both FMODE_READ and FMODE_WRITE (fs/file_table.c:199).
Rocq: `openat_rdwr_flag_words`.
kernel: fs/namei.c:lookup_open,do_open; fs/file_table.c:init_file@v6.18.46 -/
theorem openat_rdwr_flag_words :
    check_openat_row (openat_in [102] 2050) (eff_ret 3 2) have_model
      = check_openat_row (openat_in [102] 2) (eff_ret 3 2) have_model
    ∧ check_openat_row (openat_in [102] 2) (eff_ret 3 2) have_model
        = CheckOk (fixture_of (fds := (3, .FdFileRW [102] 0) :: init_fds) (fs := have_fs)) []
    ∧ check_openat_row (openat_in [102] 66) (eff_ret 3 2) have_model
        = CheckOk (fixture_of (fds := (3, .FdFileRW [102] 0) :: init_fds) (fs := have_fs)) []
    ∧ check_openat_row (openat_in [102] 514) (eff_ret 3 2) have_model
        = CheckOk (fixture_of (fds := (3, .FdFileRW [102] 0) :: init_fds)
                              (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [102] 578) (eff_ret 3 2) have_model
        = CheckOk (fixture_of (fds := (3, .FdFileRW [102] 0) :: init_fds)
                              (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [102] 66) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileRW [102] 0) :: init_fds)
                              (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [102] 578) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileRW [102] 0) :: init_fds)
                              (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [102] 194) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileRW [102] 0) :: init_fds)
                              (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [102] 706) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileRW [102] 0) :: init_fds)
                              (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [102] 1026) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 1090) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 130) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 642) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [102] 65538) (eff_ret 3 2) have_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE ERRNO HALF OF THE SAME TABLE, and the -EMFILE refusals that pin
two of its branches as DETERMINISTIC.  A read-write word with no O_CREAT
on a name that is not there is the walk's own -ENOENT (`traverse_mounts`,
fs/namei.c:1537-1538, Linux v6.18.46), and an exclusive read-write word
on a name that IS there is `do_open`'s -EEXIST (:3949-3950); neither
admits an `openat_errnos` alternative, so the -EMFILE a real kernel can
raise first (`do_sys_openat2` reserves the descriptor at fs/open.c:1435
through `get_unused_fd_flags`, fs/file.c:591-593) is REFUSED — the
narrowing `openat_body_spec`'s docstring records, not an impossibility.
An open that can SUCCEED admits it, and admits -ENOMEM with it.  Rocq:
`openat_rdwr_errnos`.
kernel: fs/namei.c:traverse_mounts,do_open; fs/open.c:do_sys_openat2; fs/file.c:alloc_fd@v6.18.46 -/
theorem openat_rdwr_errnos :
    check_openat_row (openat_in [102] 2) (eff_errno ENOENT 2) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [102] 514) (eff_errno ENOENT 2) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [102] 194) (eff_errno EEXIST 2) have_model
        = CheckOk have_model []
    ∧ check_openat_row (openat_in [102] 2) (eff_errno EMFILE 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [102] 194) (eff_errno EMFILE 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 2) (eff_errno EMFILE 2) have_model
        = CheckOk have_model []
    ∧ check_openat_row (openat_in [102] 66) (eff_errno ENOMEM 2) absent_model
        = CheckOk absent_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A DIRECTORY REFERENCE under the read-write words, whose two answers
come from two different kernel tests reached in the same call.  Without
O_CREAT nothing in `do_open`'s O_CREAT block runs and the -EISDIR is
`may_open`'s S_IFDIR arm under `acc_mode & MAY_WRITE`, which O_RDWR
carries through `ACC_MODE` (fs/namei.c:3540-3542, Linux v6.18.46); with
O_CREAT it is `do_open`'s own `d_is_dir` (:3951-3952) — unless O_EXCL is
set, which is tested first and answers -EEXIST (:3949-3950).  No real run
separates the two -EISDIRs; the -EEXIST is the one a reader gets
backwards, so the last two conjuncts refuse each errno under the other's
word.  Rocq: `openat_rdwr_dirref`.
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem openat_rdwr_dirref :
    check_openat_row (openat_in [46] 2) (eff_errno EISDIR 2) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [46] 514) (eff_errno EISDIR 2) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [46] 66) (eff_errno EISDIR 2) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [46] 578) (eff_errno EISDIR 2) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [46] 194) (eff_errno EEXIST 2) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [46] 194) (eff_errno EISDIR 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [46] 2) (eff_errno EEXIST 2) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- O_NONBLOCK, O_CLOEXEC and O_LARGEFILE are masked before the word is
read.  `build_open_flags` strips O_CLOEXEC from the flags it hands the
walk (`u64 strip = O_CLOEXEC`, fs/open.c:1241 and :1251);
`SYSCALL_DEFINE4(openat, …)` forces O_LARGEFILE on every open of a 64-bit
kernel (:1466-1467); and O_NONBLOCK reaches `f_flags` and nothing an arm
reads.  So the read word with all three set is the read word: "f" opens
at 3 as a `FdFile`; and O_NONBLOCK beside the create word (2625), the
exclusive word (2241) and the exclusive word with O_TRUNC (2753) lands
where each bare word lands — equalities between two flag words, which a
probe cannot state, with the first two shown to be successes.  Rocq:
`o_nonblock_is_an_ignored_open_flag`.
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem ignored_bits_land_where_read_does :
    check_openat_row (openat_in [102] 559104) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs)) []
    ∧ check_openat_row (openat_in [102] 2625) (eff_ret 3 2) have_model
      = check_openat_row (openat_in [102] 577) (eff_ret 3 2) have_model
    ∧ check_openat_row (openat_in [97] 2241) (eff_ret 3 2) absent_model
      = check_openat_row (openat_in [97] 193) (eff_ret 3 2) absent_model
    ∧ check_openat_row (openat_in [97] 2753) (eff_ret 3 2) absent_model
      = check_openat_row (openat_in [97] 705) (eff_ret 3 2) absent_model
    ∧ check_openat_row (openat_in [102] 2625) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFileW [102] 0) :: init_fds) (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [97] 2241) (eff_ret 3 2) absent_model
      = CheckOk (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])])) [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- …and O_RDONLY|O_NONBLOCK (2048) on "." and on an absent name lands where
the read word does.  "." opens at 3 as a directory descriptor (`may_open`
accepts a directory for reading, fs/namei.c:3540-3545, Linux v6.18.46),
and an absent "a" is the -ENOENT of the negative dentry
(`traverse_mounts`, :1537-1538).  A descriptor above the lowest free one
(`alloc_fd`, fs/file.c:570-613, Linux v6.18.46), the -EISDIR of a write
open of a directory, and a descriptor for the absent name are refused.
The corpus passes these two shapes under 2048 only under a probe
`tools/lean_replay_declared/56-openat.json` lists (`openat_nonblock`, its
`dot` and `absent` cases), and that register forgives every openat
decline under it, so the replay would file a regression that declined
them there as declared; this pin is what refuses it.
kernel: fs/namei.c:may_open,traverse_mounts; fs/file.c:alloc_fd@v6.18.46 -/
theorem o_nonblock_dot_and_absent_name_land_where_read_does :
    check_openat_row (openat_in [46] 2048) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) []
    ∧ check_openat_row (openat_in [46] 2048) (eff_ret 4 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [46] 2048) (eff_errno EISDIR 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [97] 2048) (eff_errno ENOENT 2) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [97] 2048) (eff_ret 3 2) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## `getname_flags`: the fetch answers, before the dirfd

`getname_flags` (fs/namei.c:135-216, Linux v6.18.46) turns the empty path
into -ENOENT (:168-170; `getname` passes no LOOKUP_EMPTY,
include/linux/fs.h:2944-2947, Linux v6.18.46) and returns
`strncpy_from_user`'s -EFAULT as it is (:162-164); both are decided in
`do_sys_openat2` (fs/open.c:1431-1433, Linux v6.18.46) before `path_init`
(fs/namei.c:2590-2622, Linux v6.18.46) reads the dirfd.  The ledger records the bytes the
fetch read, NUL included, so an empty pathname records one byte. -/

/-- The empty pathname is -ENOENT with one byte in the ledger; a descriptor
is refused, and so is the errno with the NUL missing from the ledger.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_is_enoent :
    check_openat_row (openat_in [] 0) (eff_errno ENOENT 1) absent_model = CheckOk absent_model []
    ∧ check_openat_row (openat_in [] 0) (eff_ret 3 1) absent_model = CheckReject
    ∧ check_openat_row (openat_in [] 0) (eff_errno ENOENT 0) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- …and it is the FETCH's -ENOENT, not a miss in the map: over an image
that holds the EMPTY key, the same -ENOENT is accepted and the reader a
lookup of that key would have minted is refused.  Rocq's
`openat_empty_path_enoent` runs over exactly that image, so that a
checker consulting the map before the empty-string gate fails here.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_is_the_fetch_enoent_not_a_lookup :
    check_openat_row (openat_in [] 0) (eff_errno ENOENT 1) empty_key_model
        = CheckOk empty_key_model []
    ∧ check_openat_row (openat_in [] 0) (eff_ret 3 1) empty_key_model = CheckReject :=
  ⟨rfl, rfl⟩

/-! ### The over-long pathname

A pathname with no NUL within `PATH_MAX` is -ENAMETOOLONG (`getname_flags`,
fs/namei.c:207-210, Linux v6.18.46: `len == PATH_MAX` after the copy), with
the whole 4096-byte window in the ledger — `strncpy_from_user` is asked
for `PATH_MAX` bytes and reads them all before the length test
(lib/strncpy_from_user.c:113-155).  Each pin below walks those 4096 bytes
in the elaborator AND in the kernel, so they are stated one conjunct per
theorem, under the recursion budget `Checks/Cases/Fs/Namei.lean` gives
its `endless` pins: six conjuncts in one theorem exhaust the kernel's
heartbeat budget where six theorems do not. -/

set_option maxRecDepth 100000 in
/-- The answer, with the whole window in the ledger.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem too_long_is_enametoolong :
    check_openat_row (endless_in 0) (eff_errno ENAMETOOLONG 4096) absent_model
        = CheckOk absent_model [] :=
  rfl

set_option maxRecDepth 100000 in
/-- -EFAULT over a memory every byte of which is readable is refused: the
copy hit no unmapped byte (`strncpy_from_user`, lib/strncpy_from_user.c:113-155).
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem too_long_refuses_efault :
    check_openat_row (endless_in 0) (eff_errno EFAULT 4096) absent_model = CheckReject :=
  rfl

set_option maxRecDepth 100000 in
/-- A descriptor is refused: nothing was opened.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem too_long_refuses_a_descriptor :
    check_openat_row (endless_in 0) (eff_ret 3 4096) absent_model = CheckReject :=
  rfl

set_option maxRecDepth 100000 in
/-- The right errno with a ledger one byte short is refused: the copy
read `PATH_MAX` bytes, not `PATH_MAX - 1`.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem too_long_refuses_a_short_ledger :
    check_openat_row (endless_in 0) (eff_errno ENAMETOOLONG 4095) absent_model = CheckReject :=
  rfl

set_option maxRecDepth 100000 in
/-- The create word lands on the same answer: the fetch decides before
any flag beyond the gate is read (`do_sys_openat2`, fs/open.c:1431-1437).
kernel: fs/namei.c:getname_flags; fs/open.c:do_sys_openat2@v6.18.46 -/
theorem too_long_under_the_create_word :
    check_openat_row (endless_in 577) (eff_errno ENAMETOOLONG 4096) absent_model
        = CheckOk absent_model [] :=
  rfl

set_option maxRecDepth 100000 in
/-- …and so does a dirfd the model cannot judge (1): `getname` runs
before `path_init` (fs/namei.c:2590) reads the dirfd, so the decline the
dirfd would earn never fires.
kernel: fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem too_long_beats_the_dirfd :
    check_openat_row (endless_in' 1 0) (eff_errno ENAMETOOLONG 4096) absent_model
        = CheckOk absent_model [] :=
  rfl

/-- …and O_CREAT does not rescue it: the fetch answers before any flag is
read, so the create word on the empty path is the same -ENOENT and the
descriptor is refused.  Rocq: `openat_empty_path_beats_o_creat`.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_beats_o_creat :
    check_openat_row (openat_in [] 577) (eff_errno ENOENT 1) absent_model = CheckOk absent_model []
    ∧ check_openat_row (openat_in [] 577) (eff_ret 3 1) absent_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- …and neither does any of the four flag words the corpus passes with the
empty path only under probes `tools/lean_replay_declared/56-openat.json`
lists: O_RDWR (2), O_WRONLY|O_CREAT|O_APPEND (1089),
O_WRONLY|O_CREAT|O_EXCL|O_TRUNC (705) and O_RDONLY|O_NONBLOCK (2048) all
land on the fetch's -ENOENT.  A descriptor is refused under each word,
since the fetch answers before any open is attempted.  The errnos refused
are the ones a checker that resolved "" to the directory `AT_FDCWD` names
would give in its place: -EISDIR under 2, from `may_open`'s test for a
write open of a directory (fs/namei.c:3540-3542, Linux v6.18.46); -EISDIR
under 1089, from `do_open`'s O_CREAT block (:3951-3952); and -EEXIST under
705, from the same block's O_EXCL test (:3949-3950).  Under 2048 such a
checker would open the directory, and the refused descriptor is its
answer.  That register forgives every openat decline under those probes,
so the replay would file a regression that declined this shape there as
declared; this pin is what refuses it.
kernel: fs/namei.c:getname_flags,do_open,may_open@v6.18.46 -/
theorem empty_path_beats_rdwr_append_excl_and_nonblock :
    check_openat_row (openat_in [] 2) (eff_errno ENOENT 1) absent_model = CheckOk absent_model []
    ∧ check_openat_row (openat_in [] 2) (eff_errno EISDIR 1) absent_model = CheckReject
    ∧ check_openat_row (openat_in [] 2) (eff_ret 3 1) absent_model = CheckReject
    ∧ check_openat_row (openat_in [] 1089) (eff_errno ENOENT 1) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [] 1089) (eff_errno EISDIR 1) absent_model = CheckReject
    ∧ check_openat_row (openat_in [] 1089) (eff_ret 3 1) absent_model = CheckReject
    ∧ check_openat_row (openat_in [] 705) (eff_errno ENOENT 1) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [] 705) (eff_errno EEXIST 1) absent_model = CheckReject
    ∧ check_openat_row (openat_in [] 705) (eff_ret 3 1) absent_model = CheckReject
    ∧ check_openat_row (openat_in [] 2048) (eff_errno ENOENT 1) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [] 2048) (eff_ret 3 1) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- …nor does a dirfd the model cannot judge: the fetch answers before
`path_init` reads it, so the empty path with dirfd 1 is still -ENOENT.
kernel: fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem empty_path_beats_the_dirfd :
    check_openat_row (openat_in' 1 8192 0 (open_path_mem [])) (eff_errno ENOENT 1) absent_model
      = CheckOk absent_model [] :=
  rfl

/-- A live dirfd (1, an open channel) with a non-empty plain name is
`CheckUnmodeled`: `path_init` (fs/namei.c:2607-2622) would answer -ENOTDIR
for a non-directory dirfd (:2621-2622), and the model, which resolves only from
`AT_FDCWD`, declines rather than judges — refusing the -ENOENT Rocq's case
offers, the kernel's -ENOTDIR, and a descriptor alike.  Rocq:
`openat_live_dirfd_still_unmodeled`.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem live_dirfd_declines :
    check_openat_row (openat_in' 1 8192 0 (open_path_mem [102])) (eff_errno ENOENT 2) have_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in' 1 8192 0 (open_path_mem [102])) (eff_errno ENOTDIR 2) have_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in' 1 8192 0 (open_path_mem [102])) (eff_ret 3 2) have_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- A CLOSED dirfd (7) is `CheckUnmodeled` too, not the -EBADF `path_init`
answers for one (fs/namei.c:2610-2611): the model declines every dirfd but
`AT_FDCWD` before asking whether it is open, so the kernel's -EBADF and a
descriptor are refused alike.  And the decline covers an ABSOLUTE
pathname, where Linux never reads the dirfd at all — `path_init` jumps to
the root on a leading '/' (:2582-2587) — so "/dev/null" under dirfd 7 is
declined and the reader Linux mints is refused: a fail-closed the spec
twin's dirfd argument, stated for relative walks, does not name, and the
cost of it is this conjunct.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem other_dirfds_decline_closed_or_open_relative_or_absolute :
    check_openat_row (openat_in' 7 8192 0 (open_path_mem [102])) (eff_errno EBADF 2) have_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in' 7 8192 0 (open_path_mem [102])) (eff_ret 3 2) have_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in' 7 8192 0 (open_path_mem devnull_path)) (eff_ret 3 10)
        absent_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- The dirfd is read as the kernel's `int` (`SYSCALL_DEFINE4(openat, int
dfd, …)`, fs/open.c:1463): -100 as a 32-bit word (4294967196) and with
bit 32 set beside it (8589934492) are both `AT_FDCWD` through the row's
`fd32`, and land where the 64-bit -100 lands.
kernel: fs/open.c:openat; fs/namei.c:path_init@v6.18.46 -/
theorem dirfd_is_narrowed_to_int :
    check_openat_row (openat_in' 4294967196 8192 0 (open_path_mem [102])) (eff_ret 3 2) have_model
      = check_openat_row (openat_in [102] 0) (eff_ret 3 2) have_model
    ∧ check_openat_row (openat_in' 8589934492 8192 0 (open_path_mem [102])) (eff_ret 3 2) have_model
      = check_openat_row (openat_in [102] 0) (eff_ret 3 2) have_model
    ∧ check_openat_row (openat_in' 4294967196 8192 0 (open_path_mem [102])) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs)) [] :=
  ⟨rfl, rfl, rfl⟩

/-! ## The read word on a plain name

A name the map holds opens read-only at offset 0 (`init_file`,
fs/file_table.c:216, Linux v6.18.46) at the lowest free descriptor
(`alloc_fd`, fs/file.c:570-613, Linux v6.18.46, starts the scan at
`max(start, files->next_fd)`, :580-585, with `start` 0 from
`__get_unused_fd_flags`, :615-618, and `find_next_fd` reports the first
clear bit at or above it — the lowest free one because `__put_unused_fd`
lowers `next_fd` on every close, :630-631), or answers one of the four
environment errnos with nothing changed.  An absent name is the
deterministic -ENOENT of the negative dentry (`traverse_mounts`,
fs/namei.c:1537-1538, Linux v6.18.46). -/

/-- "f" held: descriptor 3 as a `FdFile` at offset 0, image untouched.  A
non-lowest descriptor (4), a held one (0), the -ENOENT of an absent name
(`traverse_mounts`, fs/namei.c:1537-1538), and a foreign errno (-EPERM, 1)
are refused; -ENOMEM, an environment errno (`alloc_empty_file`,
fs/file_table.c:258-260), is accepted with the model unchanged.
kernel: fs/file.c:alloc_fd; fs/file_table.c:init_file,alloc_empty_file; fs/namei.c:traverse_mounts@v6.18.46 -/
theorem read_held_mints_the_reader :
    check_openat_row (openat_in [102] 0) (eff_ret 3 2) have_model
        = CheckOk (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs)) []
    ∧ check_openat_row (openat_in [102] 0) (eff_ret 4 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (eff_ret 0 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (eff_errno ENOENT 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (eff_errno 1 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (eff_errno ENOMEM 2) have_model = CheckOk have_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The ledger is compared at the pathname's ADDRESS, not at a fixed one:
with the pathname at 8200, the two-byte copy-in recorded at 8200 is
accepted and the same copy-in recorded at 8192 is refused.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem ledger_is_compared_at_the_pathname_address :
    check_openat_row (path_at 8200 [102] 0) (eff_ret_at 8200 3 2) have_model
        = CheckOk (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs)) []
    ∧ check_openat_row (path_at 8200 [102] 0) (eff_ret_at 8192 3 2) have_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- openat zero-fills, unmaps and copies nothing: a descriptor or an
environment errno beside any of the three ledgers is refused
(`do_sys_openat2`, fs/open.c:1435-1445, installs the descriptor or
returns the error and touches no user memory).
kernel: fs/open.c:do_sys_openat2; fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem other_ledgers_beside_the_return_rejected :
    check_openat_row (openat_in [102] 0) (eff_ret_with_zeros 3 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (eff_ret_with_unmaps 3 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (eff_ret_with_copies 3 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (eff_ret_with_zeros (errno_ret ENOMEM) 2) have_model
        = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (eff_ret_with_unmaps (errno_ret ENOMEM) 2) have_model
        = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (eff_ret_with_copies (errno_ret ENOMEM) 2) have_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The ledger is compared, not merely present: a descriptor with the
copy-in stopping before the NUL, with no copy-in at all, or with a write
beside it, is refused.  `strncpy_from_user` (lib/strncpy_from_user.c:113-155)
copies through the NUL by way of `do_strncpy_from_user`'s zero mask
(:54-59), and `openat` writes nothing to user memory.
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/open.c:do_sys_openat2@v6.18.46 -/
theorem read_ledger_lies_rejected :
    check_openat_row (openat_in [102] 0) (eff_ret 3 1) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 0) (mkEffect 3 [] []) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 0)
        (with_copyins [(8192, 2)] (mkEffect 3 [(4096, [0])] [])) have_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- An absent "a" under O_RDONLY is -ENOENT with the model untouched; a
descriptor is refused, and so is -EMFILE — an answer Linux CAN give here,
since `do_sys_openat2` reserves the descriptor (fs/open.c:1435) before it
starts the walk (:1437) and `alloc_fd` answers -EMFILE at the limit
(fs/file.c:591-593), refused by the
deliberate narrowing `openat_body_spec`'s docstring records (the header
above).
kernel: fs/namei.c:traverse_mounts; fs/file.c:alloc_fd@v6.18.46 -/
theorem read_absent_is_enoent :
    check_openat_row (openat_in [97] 0) (eff_errno ENOENT 2) absent_model = CheckOk absent_model []
    ∧ check_openat_row (openat_in [97] 0) (eff_ret 3 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [97] 0) (eff_errno EMFILE 2) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- A relative name with a separator, "a/b", is declined even when the
image holds that very key: the model resolves one component from the
working directory, and `link_path_walk` (fs/namei.c:2450-2505) would walk
two.  The descriptor Linux would hand out for the file, and the -ENOENT
of a missing "b" (`traverse_mounts`, :1537-1538), are refused alike.
Rocq: `openat_slash_key_in_image_unmodeled`.
kernel: fs/namei.c:link_path_walk,traverse_mounts@v6.18.46 -/
theorem slash_key_in_image_declines :
    check_openat_row (openat_in [97, 47, 98] 0) (eff_ret 3 4) under_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [97, 47, 98] 0) (eff_errno ENOENT 4) under_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- "." and ".." open as directory descriptors at the lowest free slot —
`link_path_walk` classes both without a lookup (fs/namei.c:2474-2481,
`LAST_DOTDOT` and `LAST_DOT`) and `may_open` accepts a directory for
reading (:3540-3545) — and "..." is an
ordinary absent name, -ENOENT.  Rocq: `openat_dotdot_answers_as_dot_does`,
`openat_dot3_is_an_ordinary_name`.
kernel: fs/namei.c:link_path_walk,may_open@v6.18.46 -/
theorem dot_and_dotdot_read_as_directory_fds :
    check_openat_row (openat_in [46] 0) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) []
    ∧ check_openat_row (openat_in [46, 46] 0) (eff_ret 3 3) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) []
    ∧ check_openat_row (openat_in [46] 0) (eff_ret 4 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [46] 0) (eff_errno EISDIR 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [46, 46, 46] 0) (eff_errno ENOENT 4) absent_model
        = CheckOk absent_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ".." under the create word is the -EISDIR "." gets, a descriptor
refused (`do_open`, fs/namei.c:3951-3952); "..." under it is an ordinary
name and MINTS the key "..." — `path_is_dirref` is an equality against two
constants, and a prefix test would turn "..." into a directory reference.
Rocq: `openat_dotdot_answers_as_dot_does`, `openat_dot3_is_an_ordinary_name`.
kernel: fs/namei.c:do_open,link_path_walk,lookup_open@v6.18.46 -/
theorem dotdot_creates_as_dot_does_and_dot3_is_a_name :
    check_openat_row (openat_in [46, 46] 577) (eff_errno EISDIR 3) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in [46, 46] 577) (eff_ret 3 3) absent_model = CheckReject
    ∧ check_openat_row (openat_in [46, 46, 46] 577) (eff_ret 3 4) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [46, 46, 46] 0) :: init_fds)
                              (fs := [([46, 46, 46], [])])) []
    ∧ check_openat_row (openat_in [46, 46, 46] 577) (eff_errno EISDIR 4) absent_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## The create word, O_WRONLY|O_CREAT|O_TRUNC

`lookup_open` creates the absent name (fs/namei.c:3787-3798, Linux
v6.18.46), `do_open` clears O_TRUNC under FMODE_CREATED (:3963-3965), and
the descriptor is write-only at offset 0; a held regular file is truncated
(`do_open`, :3967-3979, through `handle_truncate`).  A name that is a directory — "." or an
implied one, "a" over a held "a/b" — is -EISDIR: `do_open`'s `d_is_dir`
inside its O_CREAT block (:3951-3952). -/

/-- Absent "a": the key minted EMPTY and a write-only descriptor at 3.  A
non-lowest descriptor and the -ENOENT the name would get without O_CREAT
are refused.  Rocq: `openat_plain_create_still_mints_the_key`.
kernel: fs/namei.c:lookup_open,do_open; fs/file.c:alloc_fd@v6.18.46 -/
theorem create_absent_mints_the_key :
    check_openat_row (openat_in [97] 577) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])])) []
    ∧ check_openat_row (openat_in [97] 577) (eff_ret 4 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [97] 577) (eff_errno ENOENT 2) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- Held "f": truncated to empty, write-only descriptor at 3; -EEXIST is
refused — no O_EXCL in the word.
kernel: fs/namei.c:do_open,handle_truncate@v6.18.46 -/
theorem create_held_empties_the_key :
    check_openat_row (openat_in [102] 577) (eff_ret 3 2) have_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [102] 0) :: init_fds) (fs := [([102], [])])) []
    ∧ check_openat_row (openat_in [102] 577) (eff_errno EEXIST 2) have_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- An implied directory ("a" over a held "a/b") and "." are -EISDIR with the
model untouched; a descriptor is refused, and so is -EEXIST — the word has
no O_EXCL, so `do_open`'s O_EXCL test (fs/namei.c:3949-3950) cannot fire
and its `d_is_dir` (:3951-3952) answers.  The control beside it: "c" over
the same image is an ordinary absent name and creates.  Rocq:
`openat_implied_directory_create_eisdir`.
kernel: fs/namei.c:do_open,lookup_open@v6.18.46 -/
theorem implied_directory_create_is_eisdir :
    check_openat_row (openat_in [97] 577) (eff_errno EISDIR 2) under_model = CheckOk under_model []
    ∧ check_openat_row (openat_in [97] 577) (eff_ret 3 2) under_model = CheckReject
    ∧ check_openat_row (openat_in [97] 577) (eff_errno EEXIST 2) under_model = CheckReject
    ∧ check_openat_row (openat_in [46] 577) (eff_errno EISDIR 2) absent_model = CheckOk absent_model []
    ∧ check_openat_row (openat_in [46] 577) (eff_ret 3 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [99] 577) (eff_ret 3 2) under_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [99] 0) :: init_fds)
                              (fs := [([97, 47, 98], [104]), ([99], [])])) [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A byte prefix ("a" beside a held "ab") and an exact held key ("a" beside
"a") are NOT implied directories: both create, and -EISDIR is refused on
each.  Rocq: `openat_byte_prefix_and_exact_key_still_create`.
kernel: fs/namei.c:lookup_open,do_open@v6.18.46 -/
theorem byte_prefix_and_exact_key_still_create :
    check_openat_row (openat_in [97] 577) (eff_errno EISDIR 2) sibling_model = CheckReject
    ∧ check_openat_row (openat_in [97] 577) (eff_ret 3 2) sibling_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds)
                              (fs := [([97], []), ([97, 98], [104])])) []
    ∧ check_openat_row (openat_in [97] 577) (eff_errno EISDIR 2) exact_model = CheckReject
    ∧ check_openat_row (openat_in [97] 577) (eff_ret 3 2) exact_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])])) [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## The exclusive words, O_WRONLY|O_CREAT|O_EXCL with and without O_TRUNC

`do_open` answers -EEXIST for O_EXCL on a name that exists
(fs/namei.c:3949-3950, Linux v6.18.46), one test before the -EISDIR its
`d_is_dir` check gives a directory (:3951-3952), so an implied directory
under O_EXCL is -EEXIST; an absent name is created as the create word
creates it. -/

/-- Absent "a" under the exclusive word: created, write-only at 3; -EEXIST
and -ENOENT are refused.
kernel: fs/namei.c:lookup_open,do_open@v6.18.46 -/
theorem excl_absent_creates :
    check_openat_row (openat_in [97] 193) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])])) []
    ∧ check_openat_row (openat_in [97] 193) (eff_errno EEXIST 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [97] 193) (eff_errno ENOENT 2) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- Held "f" under the exclusive word, with and without O_TRUNC (705): -EEXIST
with the model untouched; a descriptor is refused, and so is -EMFILE — a
real answer here, `do_sys_openat2` reserving the descriptor before the
walk (fs/open.c:1435 and :1437; `alloc_fd`, fs/file.c:591-593), refused by
the narrowing the header names.
kernel: fs/namei.c:do_open; fs/file.c:alloc_fd@v6.18.46 -/
theorem excl_held_is_eexist :
    check_openat_row (openat_in [102] 193) (eff_errno EEXIST 2) have_model = CheckOk have_model []
    ∧ check_openat_row (openat_in [102] 705) (eff_errno EEXIST 2) have_model = CheckOk have_model []
    ∧ check_openat_row (openat_in [102] 193) (eff_ret 3 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 193) (eff_errno EMFILE 2) have_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- An implied directory under the exclusive word is -EEXIST, not -EISDIR:
the errno order of `do_open`'s O_CREAT block.  Rocq:
`openat_implied_directory_excl_eexist`.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem implied_directory_excl_is_eexist :
    check_openat_row (openat_in [97] 193) (eff_errno EEXIST 2) under_model = CheckOk under_model []
    ∧ check_openat_row (openat_in [97] 193) (eff_errno EISDIR 2) under_model = CheckReject
    ∧ check_openat_row (openat_in [97] 193) (eff_ret 3 2) under_model = CheckReject
    ∧ check_openat_row (openat_in [99] 193) (eff_ret 3 2) under_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [99] 0) :: init_fds)
                              (fs := [([97, 47, 98], [104]), ([99], [])])) [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The other write-capable words on an implied directory ("a" over a held
"a/b").  Each answers the errno Linux gives it: -EISDIR for the append
word and for the read-write words with and without O_CREAT and O_TRUNC —
through `do_open`'s `d_is_dir` inside its O_CREAT block
(fs/namei.c:3948-3952, Linux v6.18.46) for the O_CREAT words, through
`may_open`'s S_IFDIR arm (:3540-3542) for the rest, the same errno by a
different route — and -EEXIST for the exclusive read-write word
(:3949-3950).  The last conjunct refuses the descriptor under the create
word, so that the arms are seen to answer the errno and not to open the
implied directory.  Rocq: `openat_implied_directory_other_write_words`.
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem openat_implied_directory_other_write_words :
    check_openat_row (openat_in [97] 1089) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_openat_row (openat_in [97] 66) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_openat_row (openat_in [97] 578) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_openat_row (openat_in [97] 2) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_openat_row (openat_in [97] 514) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_openat_row (openat_in [97] 194) (eff_errno EEXIST 2) under_model
        = CheckOk under_model []
    ∧ check_openat_row (openat_in [97] 66) (eff_ret 3 2) under_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## O_DIRECTORY

`do_open`'s LOOKUP_DIRECTORY test answers -ENOTDIR for a name that is not a
directory (fs/namei.c:3958-3959, Linux v6.18.46); an absent name never
reaches it and is
-ENOENT; "." is a directory descriptor.  A name over `NAME_MAX` and an
implied directory are the arm's own declines. -/

/-- "." under O_DIRECTORY: a directory descriptor at 3, 4 refused.  Held "f":
-ENOTDIR, a descriptor refused, and -EMFILE refused — a real answer here
(`do_sys_openat2` reserves the descriptor at fs/open.c:1435, before the
walk at :1437; `alloc_fd`, fs/file.c:591-593), refused by the narrowing
the header names.
Absent "a": -ENOENT, a descriptor refused.
kernel: fs/namei.c:do_open,traverse_mounts; fs/file.c:alloc_fd@v6.18.46 -/
theorem dir_word_answers :
    check_openat_row (openat_in [46] 65536) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) []
    ∧ check_openat_row (openat_in [46] 65536) (eff_ret 4 2) absent_model = CheckReject
    ∧ check_openat_row (openat_in [102] 65536) (eff_errno ENOTDIR 2) have_model = CheckOk have_model []
    ∧ check_openat_row (openat_in [102] 65536) (eff_ret 3 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [102] 65536) (eff_errno EMFILE 2) have_model = CheckReject
    ∧ check_openat_row (openat_in [97] 65536) (eff_errno ENOENT 2) absent_model = CheckOk absent_model []
    ∧ check_openat_row (openat_in [97] 65536) (eff_ret 3 2) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The ignored bits are ignored HERE too, which is an equality between
two flag words and so cannot be a probe: 622592 is O_DIRECTORY with
O_CLOEXEC and O_LARGEFILE set, the bits `build_open_flags` strips
(`u64 strip = O_CLOEXEC`, fs/open.c:1241 and :1251) and
`SYSCALL_DEFINE4(openat, …)` forces (fs/open.c:1466-1467), and it lands
where 65536 lands on all four of the arm's answers — "." and ".." as
directory descriptors, held "f" as -ENOTDIR (`do_open`), absent "a" as
-ENOENT (`traverse_mounts`) — so a mask applied in one branch and not
another fails here.  Rocq: `openat_directory_ignores_largefile_and_cloexec`.
kernel: fs/open.c:build_open_flags; fs/namei.c:do_open,traverse_mounts@v6.18.46 -/
theorem dir_word_ignores_largefile_and_cloexec :
    check_openat_row (openat_in [46] 622592) (eff_ret 3 2) absent_model
        = check_openat_row (openat_in [46] 65536) (eff_ret 3 2) absent_model
    ∧ check_openat_row (openat_in [46, 46] 622592) (eff_ret 3 3) absent_model
        = check_openat_row (openat_in [46, 46] 65536) (eff_ret 3 3) absent_model
    ∧ check_openat_row (openat_in [102] 622592) (eff_errno ENOTDIR 2) have_model
        = check_openat_row (openat_in [102] 65536) (eff_errno ENOTDIR 2) have_model
    ∧ check_openat_row (openat_in [97] 622592) (eff_errno ENOENT 2) absent_model
        = check_openat_row (openat_in [97] 65536) (eff_errno ENOENT 2) absent_model
    ∧ check_openat_row (openat_in [46] 622592) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An implied directory ("a" over a held "a/b") under O_DIRECTORY is
declined — Linux opens it, and the flat map has no directory entry to
mint — refusing the descriptor and the -ENOENT of an absent name
(`traverse_mounts`, fs/namei.c:1537-1538) alike.
kernel: fs/namei.c:link_path_walk,traverse_mounts@v6.18.46 -/
theorem dir_word_implied_directory_declines :
    check_openat_row (openat_in [97] 65536) (eff_ret 3 2) under_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [97] 65536) (eff_errno ENOENT 2) under_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- Stated on the arm: a name of 256 bytes is declined under O_DIRECTORY
(the -ENAMETOOLONG is the filesystem's own — `simple_lookup`,
fs/libfs.c:71-72, and `ext4_lookup`, fs/ext4/namei.c:1768-1769 — which a
model with no filesystem type cannot pick, so the arm stops short of it),
while 255
bytes is the ordinary -ENOENT of an absent name, so the bound is
`NAME_MAX` itself.  The arm sees the effect with the ledger cleared, so it
is offered bare; the same two names through the row, with the 257- and
256-byte fetch in the ledger, close the last two conjuncts.
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup; fs/namei.c:traverse_mounts@v6.18.46 -/
theorem check_openat_dir_name_max_bound :
    check_openat_dir name256 (mkEffect (errno_ret ENOENT) [] []) absent_model = CheckUnmodeled
    ∧ check_openat_dir name255 (mkEffect (errno_ret ENOENT) [] []) absent_model
        = CheckOk absent_model []
    ∧ check_openat_dir name255 (mkEffect 3 [] []) absent_model = CheckReject
    ∧ check_openat_row (openat_in name256 65536) (eff_errno ENOENT 257) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in name255 65536) (eff_errno ENOENT 256) absent_model
        = CheckOk absent_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The arms, offered an errno and required to refuse

A checker answering `CheckUnmodeled` on every input meets every lemma of
its file against a spec that declines everywhere.  These pins are on the
arms by name, with a kernel-shaped answer offered and `CheckReject`
required, so that shape fails here. -/

/-- `check_openat_read` refuses -ENOENT on a held name and a descriptor on
an absent one; `check_openat_create` refuses a descriptor on an implied
directory; `check_openat_excl` refuses one on a held name.
kernel: fs/namei.c:may_open,traverse_mounts,do_open@v6.18.46 -/
theorem plain_name_arms_refuse_lies :
    check_openat_read [102] (mkEffect (errno_ret ENOENT) [] []) have_model = CheckReject
    ∧ check_openat_read [97] (mkEffect 3 [] []) absent_model = CheckReject
    ∧ check_openat_create [97] (mkEffect 3 [] []) under_model = CheckReject
    ∧ check_openat_excl [102] (mkEffect 3 [] []) have_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `check_open_result` on the standard table: the lowest free descriptor
(3) is accepted in the model the builder makes, an environment errno with
the model unchanged; a non-lowest descriptor (4), a held one (0), a foreign
errno (-EPERM), a return in the error band that is no errno of the set
(-4095), and a write beside either answer are refused: openat writes
nothing to user memory on either path (`do_sys_openat2`,
fs/open.c:1435-1445, installs the descriptor or returns the error and
does nothing else), so a write is a lie whatever a0 says.
kernel: fs/file.c:alloc_fd; fs/open.c:do_sys_openat2@v6.18.46 -/
theorem check_open_result_on_the_standard_table :
    check_open_result (mkEffect 3 [] []) absent_model
        (fun fd => with_fds (fd_insert init_fds fd .FdDir) absent_model)
      = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) []
    ∧ check_open_result (mkEffect (errno_ret EMFILE) [] []) absent_model
        (fun fd => with_fds (fd_insert init_fds fd .FdDir) absent_model)
      = CheckOk absent_model []
    ∧ check_open_result (mkEffect 4 [] []) absent_model
        (fun fd => with_fds (fd_insert init_fds fd .FdDir) absent_model) = CheckReject
    ∧ check_open_result (mkEffect 0 [] []) absent_model
        (fun fd => with_fds (fd_insert init_fds fd .FdDir) absent_model) = CheckReject
    ∧ check_open_result (mkEffect (errno_ret 1) [] []) absent_model
        (fun fd => with_fds (fd_insert init_fds fd .FdDir) absent_model) = CheckReject
    ∧ check_open_result (mkEffect (errno_ret 4095) [] []) absent_model
        (fun fd => with_fds (fd_insert init_fds fd .FdDir) absent_model) = CheckReject
    ∧ check_open_result (mkEffect 3 [(4096, [0])] []) absent_model
        (fun fd => with_fds (fd_insert init_fds fd .FdDir) absent_model) = CheckReject
    ∧ check_open_result (mkEffect (errno_ret EMFILE) [(4096, [0])] []) absent_model
        (fun fd => with_fds (fd_insert init_fds fd .FdDir) absent_model) = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## "/etc/localtime"

`openat_localtime_spec` answers -ENOENT for exactly this byte string under
the assumption the spec twin argues (bugs/openat-localtime-assumed-absent.md):
the last component finds no inode, so the walk answers -ENOENT
(`traverse_mounts`, fs/namei.c:1537-1538, Linux v6.18.46) for every admitted
word without O_CREAT — O_CREAT would create the file instead (`lookup_open`,
:3787-3798), so those words are declined, as is every image that holds the
key or a key under it. -/

/-- O_RDONLY: -ENOENT, model untouched; a descriptor refused, and -EACCES
refused — an answer Linux can give when a component is not searchable
(`may_lookup`, fs/namei.c:1852, called from `link_path_walk` at :2467,
asks `inode_permission` for MAY_EXEC and `generic_permission` answers
-EACCES, :464-506), refused because the arm's premise
(bugs/openat-localtime-assumed-absent.md) is a world where the walk
reaches the last component and misses.
kernel: fs/namei.c:traverse_mounts,link_path_walk,inode_permission,generic_permission@v6.18.46 -/
theorem localtime_rdonly_is_enoent :
    check_openat_row (openat_in localtime_path 0) (eff_errno ENOENT 15) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in localtime_path 0) (eff_ret 3 15) absent_model = CheckReject
    ∧ check_openat_row (openat_in localtime_path 0) (eff_errno EACCES 15) absent_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- Every admitted word without O_CREAT is the same -ENOENT: musl's
`__map_file` word (O_RDONLY|O_CLOEXEC|O_NONBLOCK, 526336 — the call the
arm exists for), O_RDWR, O_RDWR|O_TRUNC and O_DIRECTORY, the walk failing
at the last component before `do_open` reads the access mode; and the
O_CREAT spellings beyond the two pinned below — the append word, the
read-write create word and the exclusive read-write word — decline like
them.  Rocq: `openat_localtime_enoent`.
kernel: fs/namei.c:traverse_mounts,lookup_open@v6.18.46 -/
theorem localtime_every_read_word_is_enoent :
    check_openat_row (openat_in localtime_path 526336) (eff_errno ENOENT 15) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in localtime_path 2) (eff_errno ENOENT 15) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in localtime_path 514) (eff_errno ENOENT 15) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in localtime_path 65536) (eff_errno ENOENT 15) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in localtime_path 2) (eff_ret 3 15) absent_model = CheckReject
    ∧ check_openat_row (openat_in localtime_path 1089) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in localtime_path 66) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in localtime_path 194) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE MATCH IS EXACT: "/etc//localtime", "//etc/localtime",
"/etc/localtim" and "/etc/localtimes" are the ordinary separator decline,
the -ENOENT (`traverse_mounts`, fs/namei.c:1537-1538) refused on each —
the first two name the same file on Linux (`link_path_walk` skips repeated
separators, :2504), and a prefix or a normalising comparison would answer
for them.  Rocq: `openat_localtime_match_is_exact`.
kernel: fs/namei.c:link_path_walk,traverse_mounts@v6.18.46 -/
theorem localtime_match_is_exact :
    check_openat_row (openat_in [47, 101, 116, 99, 47, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] 0)
        (eff_errno ENOENT 16) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] 0)
        (eff_errno ENOENT 16) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109] 0)
        (eff_errno ENOENT 14) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in (localtime_path ++ [115]) 0) (eff_errno ENOENT 16) absent_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The create and exclusive words decline: Linux would create the file
(`lookup_open`, fs/namei.c:3787-3798), refusing the -ENOENT and the
descriptor alike.  So does an image holding the key, or a key under it.
kernel: fs/namei.c:lookup_open,link_path_walk@v6.18.46 -/
theorem localtime_declines :
    check_openat_row (openat_in localtime_path 577) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in localtime_path 577) (eff_ret 3 15) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in localtime_path 193) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in localtime_path 0) (eff_errno ENOENT 15) localtime_key_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in localtime_path 0) (eff_ret 3 15) localtime_key_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in localtime_path 0) (eff_errno ENOENT 15) localtime_under_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## "/dev/null"

`may_open`'s S_IFCHR arm (fs/namei.c:3546-3550, Linux v6.18.46) admits the
device, and `memory_open` (drivers/char/mem.c:707, Linux v6.18.46) installs
its operations; every word
below is decided in `do_open` before that open runs.  Rocq:
`devnull_open_by_word`, `devnull_open_declines`. -/

/-- By word: O_RDONLY mints the reader, the create and append words the
writer, O_RDWR both halves, each at 3; the exclusive words are -EEXIST and
O_DIRECTORY -ENOTDIR, with a descriptor refused under each; a non-lowest
descriptor is refused under the read word.
kernel: fs/namei.c:may_open,do_open; drivers/char/mem.c:memory_open; fs/file.c:alloc_fd@v6.18.46 -/
theorem devnull_open_by_word :
    check_openat_row (openat_in devnull_path 0) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true false) :: init_fds)) []
    ∧ check_openat_row (openat_in devnull_path 577) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull false true) :: init_fds)) []
    ∧ check_openat_row (openat_in devnull_path 1089) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull false true) :: init_fds)) []
    ∧ check_openat_row (openat_in devnull_path 2) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true true) :: init_fds)) []
    ∧ check_openat_row (openat_in devnull_path 193) (eff_errno EEXIST 10) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in devnull_path 194) (eff_errno EEXIST 10) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in devnull_path 193) (eff_ret 3 10) absent_model = CheckReject
    ∧ check_openat_row (openat_in devnull_path 65536) (eff_errno ENOTDIR 10) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in devnull_path 65536) (eff_ret 3 10) absent_model = CheckReject
    ∧ check_openat_row (openat_in devnull_path 0) (eff_ret 4 10) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The rest of the word table, and the exact match.  O_RDWR with O_TRUNC,
with O_CREAT and with both (514, 66, 578) mint both halves as bare O_RDWR
does; the exclusive words with O_TRUNC (705, 706) are -EEXIST; O_RDONLY
with O_CLOEXEC is the reader.  "/dev/nul" and "/dev//null" are the
separator decline, the reader refused.  Rocq: the remaining legs of
`devnull_open_by_word` and `devnull_open_declines`.
kernel: fs/namei.c:may_open,do_open,link_path_walk@v6.18.46 -/
theorem devnull_rest_of_the_word_table_and_exact_match :
    check_openat_row (openat_in devnull_path 514) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true true) :: init_fds)) []
    ∧ check_openat_row (openat_in devnull_path 66) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true true) :: init_fds)) []
    ∧ check_openat_row (openat_in devnull_path 578) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true true) :: init_fds)) []
    ∧ check_openat_row (openat_in devnull_path 705) (eff_errno EEXIST 10) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in devnull_path 706) (eff_errno EEXIST 10) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in devnull_path 524288) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true false) :: init_fds)) []
    ∧ check_openat_row (openat_in [47, 100, 101, 118, 47, 110, 117, 108] 0) (eff_ret 3 9)
        absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 100, 101, 118, 47, 47, 110, 117, 108, 108] 0) (eff_ret 3 11)
        absent_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An image that ships a file under the name, or a key under it, is
declined whatever the kernel said — a descriptor or the -ENOENT of an
absent name (`traverse_mounts`, fs/namei.c:1537-1538).
kernel: fs/namei.c:link_path_walk,traverse_mounts@v6.18.46 -/
theorem devnull_open_declines :
    check_openat_row (openat_in devnull_path 0) (eff_ret 3 10) devnull_key_model = CheckUnmodeled
    ∧ check_openat_row (openat_in devnull_path 0) (eff_errno ENOENT 10) devnull_key_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in devnull_path 0) (eff_ret 3 10) devnull_under_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-! ## "/dev/urandom"

The same device path, with the write words declined: the model has one
`FdUrandom` kind, a reader, and the harness cannot declare the generator's
bytes (`testing/syscall-check/tests/dev_urandom_decline.c`).  Rocq:
`urandom_open_by_word`, `urandom_open_declines`. -/

/-- O_RDONLY mints the reader at 3, 4 refused; the exclusive words are
-EEXIST and O_DIRECTORY -ENOTDIR, a descriptor refused under each.
kernel: fs/namei.c:may_open,do_open; drivers/char/mem.c:memory_open; fs/file.c:alloc_fd@v6.18.46 -/
theorem urandom_open_by_word :
    check_openat_row (openat_in urandom_path 0) (eff_ret 3 13) absent_model
        = CheckOk (fixture_of (fds := (3, .FdUrandom) :: init_fds)) []
    ∧ check_openat_row (openat_in urandom_path 0) (eff_ret 4 13) absent_model = CheckReject
    ∧ check_openat_row (openat_in urandom_path 193) (eff_errno EEXIST 13) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in urandom_path 193) (eff_ret 3 13) absent_model = CheckReject
    ∧ check_openat_row (openat_in urandom_path 65536) (eff_errno ENOTDIR 13) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in urandom_path 65536) (eff_ret 3 13) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The exclusive read-write words (194, 706) are -EEXIST on the device as
the write-only exclusive words are, a descriptor refused — the one arm of
`check_openat_urandom` no other pin reaches; O_RDONLY|O_CLOEXEC is the
reader; and the read-write words with O_TRUNC or with O_CREAT (514, 578)
decline as bare O_RDWR does.  Rocq: the remaining legs of
`urandom_open_by_word`.
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem urandom_rdwr_excl_is_eexist_and_the_rest_declines :
    check_openat_row (openat_in urandom_path 194) (eff_errno EEXIST 13) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in urandom_path 706) (eff_errno EEXIST 13) absent_model
        = CheckOk absent_model []
    ∧ check_openat_row (openat_in urandom_path 194) (eff_ret 3 13) absent_model = CheckReject
    ∧ check_openat_row (openat_in urandom_path 524288) (eff_ret 3 13) absent_model
        = CheckOk (fixture_of (fds := (3, .FdUrandom) :: init_fds)) []
    ∧ check_openat_row (openat_in urandom_path 514) (eff_ret 3 13) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in urandom_path 578) (eff_ret 3 13) absent_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The exclusive append words (1217, and 1729 with O_TRUNC) are
DECLINED on both devices, whatever the kernel is offered as having said:
`do_open`'s O_EXCL test does refuse the existing device node with
-EEXIST (fs/namei.c:3949-3950), but neither spec nor checker has an arm
for the word — `modeled_open_flags` refuses it before the pathname is
read — so the errno is refused rather than guessed at, and so is the
descriptor.  The arms beside it answer: the exclusive read-write words
above are -EEXIST on both devices.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem excl_append_word_on_the_devices :
    check_openat_row (openat_in devnull_path 1217) (eff_errno EEXIST 10) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in devnull_path 1729) (eff_errno EEXIST 10) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in devnull_path 1217) (eff_ret 3 10) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in urandom_path 1217) (eff_errno EEXIST 13) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in urandom_path 1729) (eff_errno EEXIST 13) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in urandom_path 1217) (eff_ret 3 13) absent_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The create, append and read-write words decline — Linux opens each
(`may_open`, fs/namei.c:3546-3550) — and so does an image holding the key.
kernel: fs/namei.c:may_open,link_path_walk@v6.18.46 -/
theorem urandom_open_declines :
    check_openat_row (openat_in urandom_path 577) (eff_ret 3 13) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in urandom_path 1089) (eff_ret 3 13) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in urandom_path 2) (eff_ret 3 13) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in urandom_path 0) (eff_ret 3 13) urandom_key_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in urandom_path 0) (eff_ret 3 13) urandom_under_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## "/tmp/<name>"

One component under /tmp, under the privacy premise the spec twin
argues: the create word mints the key as the plain-name create does, and
the read word opens a name the run HOLDS; a name the run does not hold, a
second component, /tmp itself, and every other word are declined. -/

/-- The create word on "/tmp/x": the key minted empty, write-only at 3, the
-ENOENT refused.  The read word on the held key: a reader at 3, -ENOENT
refused.
kernel: fs/namei.c:lookup_open,do_open,may_open; fs/file_table.c:init_file@v6.18.46 -/
theorem tmp_create_and_read :
    check_openat_row (openat_in [47, 116, 109, 112, 47, 120] 577) (eff_ret 3 7) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [47, 116, 109, 112, 47, 120] 0) :: init_fds)
                              (fs := [([47, 116, 109, 112, 47, 120], [])])) []
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 120] 577) (eff_errno ENOENT 7) absent_model
        = CheckReject
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 120] 0) (eff_ret 3 7) tmp_held_model
        = CheckOk (fixture_of (fds := (3, .FdFile [47, 116, 109, 112, 47, 120] 0) :: init_fds)
                              (fs := tmp_held_fs)) []
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 120] 0) (eff_errno ENOENT 7) tmp_held_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A read of a name the ENVIRONMENT declared rather than the run created:
the declaration is keyed by the component "x" and the program names
"/tmp/x"; `State.fs_seed_tmp` is what makes those the same file, and the
reader is minted on the seeded key.  Rocq: `openat_tmp_declared_name_reads`.
kernel: fs/namei.c:may_open; fs/file_table.c:init_file@v6.18.46 -/
theorem tmp_declared_name_reads :
    check_openat_row (openat_in (tmp_key [120]) 0) (eff_ret 3 7) tmp_seeded_model
        = CheckOk (fixture_of (fds := (3, .FdFile (tmp_key [120]) 0) :: init_fds)
                              (fs := [(tmp_key [120], [104])])) []
    ∧ check_openat_row (openat_in (tmp_key [120]) 0) (eff_errno ENOENT 7) tmp_seeded_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The create word carrying O_CLOEXEC (524865), O_NONBLOCK (2625) or
O_LARGEFILE (33345) reaches the same arm and mints the same key — the arm
masks `open_ignored_flags` itself (`build_open_flags` strips O_CLOEXEC,
fs/open.c:1241 and :1251; `openat` forces O_LARGEFILE, :1466-1467), so a
mask dropped in this arm alone fails here — and the read word with
O_CLOEXEC opens the held key as the bare word does.  Rocq: the ignored-bit
legs of `openat_tmp_create_read_unlink`.
kernel: fs/open.c:build_open_flags,openat@v6.18.46 -/
theorem tmp_ignored_bits_reach_the_arm :
    check_openat_row (openat_in (tmp_key [120]) 524865) (eff_ret 3 7) absent_model
      = check_openat_row (openat_in (tmp_key [120]) 577) (eff_ret 3 7) absent_model
    ∧ check_openat_row (openat_in (tmp_key [120]) 2625) (eff_ret 3 7) absent_model
      = check_openat_row (openat_in (tmp_key [120]) 577) (eff_ret 3 7) absent_model
    ∧ check_openat_row (openat_in (tmp_key [120]) 33345) (eff_ret 3 7) absent_model
      = check_openat_row (openat_in (tmp_key [120]) 577) (eff_ret 3 7) absent_model
    ∧ check_openat_row (openat_in (tmp_key [120]) 524865) (eff_ret 3 7) absent_model
      = CheckOk (fixture_of (fds := (3, .FdFileW (tmp_key [120]) 0) :: init_fds)
                            (fs := [(tmp_key [120], [])])) []
    ∧ check_openat_row (openat_in (tmp_key [120]) 524288) (eff_ret 3 7) tmp_held_model
      = CheckOk (fixture_of (fds := (3, .FdFile (tmp_key [120]) 0) :: init_fds)
                            (fs := tmp_held_fs)) [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- The `NAME_MAX` boundary from both sides, at both words the arm takes: a
255-byte component is answered — the create mints the key, the read of a
held one mints the reader — and a 256-byte component is declined at the
create word and at the read word, with the -ENAMETOOLONG a filesystem gives
it (`simple_lookup`, fs/libfs.c:71-72; `ext4_lookup`, fs/ext4/namei.c:1768-1769)
declined too rather than picked.  Rocq: `openat_tmp_name_max_boundary`.
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup; fs/namei.c:lookup_open@v6.18.46 -/
theorem tmp_name_max_boundary :
    check_openat_row (openat_in (tmp_key name255) 577) (eff_ret 3 261) absent_model
      = CheckOk (fixture_of (fds := (3, .FdFileW (tmp_key name255) 0) :: init_fds)
                            (fs := [(tmp_key name255, [])])) []
    ∧ check_openat_row (openat_in (tmp_key name255) 0) (eff_ret 3 261) tmp_name255_held_model
      = CheckOk (fixture_of (fds := (3, .FdFile (tmp_key name255) 0) :: init_fds)
                            (fs := tmp_name255_held_fs)) []
    ∧ check_openat_row (openat_in (tmp_key name256) 577) (eff_ret 3 262) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in (tmp_key name256) 0) (eff_errno ENOENT 262) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in (tmp_key name256) 577) (eff_errno ENAMETOOLONG 262) absent_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A directory inside /tmp the flat map only implies: "/tmp/d" over a held
"/tmp/d/f".  The create word ANSWERS: the -EISDIR `do_open` gives a
directory under O_CREAT without O_EXCL (fs/namei.c:3951-3952) is accepted
with the model untouched, and the descriptor the arm would otherwise have
minted is refused, as is the -ENOENT a flat map would have reached for —
which is what separates this answer from a lookup miss.
Rocq: `openat_tmp_implied_directory_create_eisdir`.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_implied_directory_create_eisdir :
    check_openat_row (openat_in (tmp_key [100]) 577) (eff_errno EISDIR 7) tmp_dir_model
        = CheckOk tmp_dir_model []
    ∧ check_openat_row (openat_in (tmp_key [100]) 577) (eff_ret 3 7) tmp_dir_model = CheckReject
    ∧ check_openat_row (openat_in (tmp_key [100]) 577) (eff_errno 2 7) tmp_dir_model
        = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- …and the read word at the same name, on the same image, still declines:
at the directory descriptor `may_open` permits (fs/namei.c:3540-3545), which
the map has nothing to mint, and at the create's -EISDIR, so the decline is
the arm's and not a disagreement about the errno.  The nested "/tmp/d/f"
itself carries a second component, which `tmp_name` refuses, so at both
words it is the separator gate's decline and not this rung's.
Rocq: `openat_tmp_implied_directory_read_unmodeled`.
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_implied_directory_read_unmodeled :
    check_openat_row (openat_in (tmp_key [100]) 0) (eff_ret 3 7) tmp_dir_model = CheckUnmodeled
    ∧ check_openat_row (openat_in (tmp_key [100]) 0) (eff_errno EISDIR 7) tmp_dir_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in (tmp_key [100, 47, 102]) 0) (eff_ret 3 9) tmp_dir_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in (tmp_key [100, 47, 102]) 577) (eff_ret 3 9) tmp_dir_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The read branch's guard where it decides.  On `tmp_dir_model` "/tmp/d"
is not a key, so the read above declines through the not-held branch with
or without the guard; on the unrealizable image `Fs.valid_fs` admits, both
"/tmp/d" and "/tmp/d/f" keys, the lookup of "/tmp/d" would succeed and the
read still declines — at the descriptor and at a lookup miss's -ENOENT —
while the create answers -EISDIR ahead of the lookup that would otherwise
have truncated the held key, and refuses the descriptor.
Rocq: `openat_tmp_implied_directory_unrealizable_image`.
kernel: fs/namei.c:may_open,do_open@v6.18.46 -/
theorem tmp_implied_directory_unrealizable_image :
    check_openat_row (openat_in (tmp_key [100]) 0) (eff_ret 3 7) tmp_unreal_model = CheckUnmodeled
    ∧ check_openat_row (openat_in (tmp_key [100]) 0) (eff_errno 2 7) tmp_unreal_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in (tmp_key [100]) 577) (eff_errno EISDIR 7) tmp_unreal_model
        = CheckOk tmp_unreal_model []
    ∧ check_openat_row (openat_in (tmp_key [100]) 577) (eff_ret 3 7) tmp_unreal_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The shapes the ruling left out: the read-write create word (578) on a
held name; "/tmp/", "/tmp/." and "/tmp/.." — the directory and the two
references inside it; and "/tmpfoo", which merely begins like the prefix
and is not under /tmp at all.  Rocq: `openat_tmp_excluded_shapes_unmodeled`.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_excluded_shapes_decline :
    check_openat_row (openat_in (tmp_key [120]) 578) (eff_ret 3 7) tmp_held_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47] 0) (eff_ret 3 6) tmp_held_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 46] 0) (eff_ret 3 7) tmp_held_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 46, 46] 0) (eff_ret 3 8) tmp_held_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 102, 111, 111] 577) (eff_ret 3 8) absent_model
        = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The read word on a name the run does not hold declines (Linux would
answer -ENOENT or open a file another process made); the exclusive,
directory and append words decline on a held name — the first two at the
-EEXIST and -ENOTDIR `do_open` answers them with (fs/namei.c:3949-3950 and
:3958-3959), the append word at the descriptor; a second component
("/tmp/d/f") and "/tmp" itself decline; and an absolute plain key ("/a")
under the create word declines — Rocq's `openat_absolute_create_unmodeled`.
kernel: fs/namei.c:traverse_mounts,link_path_walk,do_open@v6.18.46 -/
theorem tmp_and_slash_declines :
    check_openat_row (openat_in [47, 116, 109, 112, 47, 120] 0) (eff_errno ENOENT 7) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 120] 0) (eff_ret 3 7) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 120] 193) (eff_errno EEXIST 7) tmp_held_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 120] 65536) (eff_errno ENOTDIR 7)
        tmp_held_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 120] 1089) (eff_ret 3 7) tmp_held_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112, 47, 100, 47, 102] 0) (eff_ret 3 9)
        tmp_dir_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 116, 109, 112] 0) (eff_ret 3 5) absent_model
        = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 97] 577) (eff_ret 3 3) absent_model = CheckUnmodeled
    ∧ check_openat_row (openat_in [47, 97] 577) (eff_errno ENOENT 3) absent_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The witness: which outcome it names

`openat_witness_ok` says the witness is an outcome the spec admits; what it
cannot say is WHICH.  Each pin below names the outcome for one call, and
where the outcome is an effect, the pin beside it offers that effect to the
checker and requires `CheckOk` — the receptiveness field of the arm, closed
by hand on the fixtures. -/

/-- On a descriptor-minting call the witness draws `witness_errno`, -ENOMEM,
WITH the pathname copy-in recorded — so the -ENOMEM it names is
`alloc_empty_file`'s (fs/file_table.c:258-260), failing in `path_openat`
(fs/namei.c:4124) after `getname` has copied the pathname in
(`do_sys_openat2`, fs/open.c:1431), and not `getname_flags`'s own
(fs/namei.c:146-148), which fails before any byte is read and would leave
the ledger empty.  The checker accepts that effect with the model
unchanged.  "f" held under the read word, "/dev/null" under it, "a"
under the create word, and the three arms that mint the two new kinds:
"f" held under the append word and under O_RDWR, and "a" absent under
the exclusive read-write word.
kernel: fs/file_table.c:alloc_empty_file; fs/namei.c:path_openat@v6.18.46 -/
theorem witness_draws_enomem_where_a_descriptor_is_minted :
    openat_witness_row (openat_in [102] 0) have_model = Ok (eff_errno ENOMEM 2) have_model []
    ∧ check_openat_row (openat_in [102] 0) (eff_errno ENOMEM 2) have_model = CheckOk have_model []
    ∧ openat_witness_row (openat_in devnull_path 0) absent_model
        = Ok (eff_errno ENOMEM 10) absent_model []
    ∧ check_openat_row (openat_in devnull_path 0) (eff_errno ENOMEM 10) absent_model
        = CheckOk absent_model []
    ∧ openat_witness_row (openat_in [97] 577) absent_model = Ok (eff_errno ENOMEM 2) absent_model []
    ∧ check_openat_row (openat_in [97] 577) (eff_errno ENOMEM 2) absent_model
        = CheckOk absent_model []
    ∧ openat_witness_row (openat_in [102] 1089) have_model
        = Ok (eff_errno ENOMEM 2) have_model []
    ∧ check_openat_row (openat_in [102] 1089) (eff_errno ENOMEM 2) have_model
        = CheckOk have_model []
    ∧ openat_witness_row (openat_in [102] 2) have_model = Ok (eff_errno ENOMEM 2) have_model []
    ∧ check_openat_row (openat_in [102] 2) (eff_errno ENOMEM 2) have_model
        = CheckOk have_model []
    ∧ openat_witness_row (openat_in [97] 194) absent_model
        = Ok (eff_errno ENOMEM 2) absent_model []
    ∧ check_openat_row (openat_in [97] 194) (eff_errno ENOMEM 2) absent_model
        = CheckOk absent_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- On a deterministic branch the witness is that branch's errno: -ENOENT
for an absent name, the empty path, "/etc/localtime" and a read-write
word with no O_CREAT on a name that is not there; -EEXIST for the
exclusive word on a held name and for the exclusive read-write word on
one; -ENOTDIR for O_DIRECTORY on a held name; -EISDIR for the create
word, the append word and the read-write words on an implied directory;
-EFAULT for an unmapped pathname.
kernel: fs/namei.c:traverse_mounts,getname_flags,do_open,path_init; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem witness_names_the_deterministic_errno :
    openat_witness_row (openat_in [97] 0) absent_model = Ok (eff_errno ENOENT 2) absent_model []
    ∧ openat_witness_row (openat_in [] 0) absent_model = Ok (eff_errno ENOENT 1) absent_model []
    ∧ openat_witness_row (openat_in localtime_path 0) absent_model
        = Ok (eff_errno ENOENT 15) absent_model []
    ∧ openat_witness_row (openat_in [102] 193) have_model = Ok (eff_errno EEXIST 2) have_model []
    ∧ openat_witness_row (openat_in [102] 65536) have_model = Ok (eff_errno ENOTDIR 2) have_model []
    ∧ openat_witness_row (openat_in [97] 577) under_model = Ok (eff_errno EISDIR 2) under_model []
    ∧ openat_witness_row (unmapped_in 0) absent_model = Ok (eff_errno EFAULT 1) absent_model []
    ∧ openat_witness_row (openat_in [97] 2) absent_model = Ok (eff_errno ENOENT 2) absent_model []
    ∧ openat_witness_row (openat_in [102] 194) have_model = Ok (eff_errno EEXIST 2) have_model []
    ∧ openat_witness_row (openat_in [97] 1089) under_model = Ok (eff_errno EISDIR 2) under_model []
    ∧ openat_witness_row (openat_in [97] 2) under_model = Ok (eff_errno EISDIR 2) under_model []
    ∧ openat_witness_row (openat_in [97] 194) under_model = Ok (eff_errno EEXIST 2) under_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Where the spec declines, the witness is `Unmodeled`: the O_NOCTTY word
before the fetch, a live dirfd, the exclusive append word (1217) on a
plain name — the flag gate refuses it, where the append word beside it
now draws -ENOMEM — an absolute plain key, and "/tmp/x" the run does not
hold.
kernel: fs/open.c:build_open_flags; fs/namei.c:path_init,link_path_walk@v6.18.46 -/
theorem witness_is_unmodeled_where_the_spec_declines :
    openat_witness_row (unmapped_in 256) absent_model = Unmodeled
    ∧ openat_witness_row (openat_in' 1 8192 0 (open_path_mem [102])) have_model = Unmodeled
    ∧ openat_witness_row (openat_in [102] 1217) have_model = Unmodeled
    ∧ openat_witness_row (openat_in [47, 97] 577) absent_model = Unmodeled
    ∧ openat_witness_row (openat_in [47, 116, 109, 112, 47, 120] 0) absent_model = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! # faccessat (48) and faccessat2 (439)

Pins over `Checks.Sys.Fs.Open.check_faccessat` and `check_faccessat2`, the
twins of the faccessat half of `Checks/Sys/Fs/Open.v`, and over their
witnesses.  Rocq keeps nine worked cases for the pair in
`Checks/Cases/Fs/Open.v`, every one through `check_syscall`:
`faccessat_implied_directory_unmodeled`,
`faccessat_byte_prefix_is_not_a_directory`,
`faccessat_bad_mode_beats_an_unreadable_path`,
`faccessat_bad_mode_records_no_copyin`,
`faccessat_existence_needs_the_copyin`,
`faccessat2_accepted_flags_change_no_answer`,
`faccessat2_empty_path_flag_declined_either_way`,
`faccessat2_bad_flag_records_no_copyin` and
`faccessat2_implied_directory_unmodeled`.  They are restated here on
`check_faccessat_row` and `check_faccessat2_row`, which apply the checker
as the rows for 48 and 439 in `Sys/SyscallTable.lean` apply the spec —
the dirfd through `fd32`, the pathname pointer, the mode and (for 439)
the flag word as they arrive — rather than through `check_syscall`,
because the checked table has no row for 48 or 439 to state them
through: those arm records and their table rows belong to the
registration that takes 48 and 439, which this file does not anticipate.
When that registration adds the rows, these pins are restated through
`check_syscall` as the openat and close pins are in the two sections
that end this file.  The fixtures are the spec pins' faccessat ones,
`faccessat_in`, `faccessat2_in`, `fa_model` ("a" held, Rocq's
`fa2_model`), `fa_under_model` ("a" and "a/b"), `fa_sibling_model` ("a"
and "ab"), `fa_x_model`, `fa_bytes_model` and `fa_file3_model`, so that
spec and checker are pinned on the same tables.

THE ONE THING FACCESSAT ADDS to the openat pattern is that the accepting
arm builds nothing: `check_access_exists` accepts 0 and the two
environment errnos alike, with the model unchanged, so every accepted
effect here is `CheckOk` in the fixture it was offered.  What the lemmas
of the checker's file cannot see is the same as for openat — a lie told
from outside — and it is what most pins below offer: an -ENOENT on a held
name, a 0 on an absent one, an -EROFS or a positive return where F_OK
never produces one, a ledger short of the NUL or grown past it, a ledger
on the -EINVAL arms that read no memory, and the kernel's answer under a
decline.  One class of refusal is marked as such where it appears: the
-ENOMEM and -EACCES the deterministic -ENOENT arm refuses on an ABSENT
name arrive WITH the pathname ledger, so they are the lookup's own —
`__lookup_slow` (fs/namei.c:1789-1824, Linux v6.18.46) asks
`d_alloc_parallel` for the dentry at :1801, and the allocation failing is
-ENOMEM (fs/dcache.c:2549-2554, Linux v6.18.46); `may_lookup`
(fs/namei.c:1852-1874) can answer -EACCES on the walk's first step — and
the checker refuses them because the spec twin does, by the narrowing
`faccessat_body_spec`'s docstring in `Sys/Fs/Open.lean` records.  Those
conjuncts pin the narrowing, not an impossibility.  The -ENOMEMs that
PRECEDE the copy — `__getname` failing in `getname_flags`
(fs/namei.c:146-148, Linux v6.18.46), and `access_override_creds`
(fs/open.c:418-465, Linux v6.18.46) failing where `do_faccessat` calls it
(fs/open.c:486-489), before `user_path_at` at :493 — arrive with NO
ledger, and the ledger rule refuses them on every answered arm; the
-ENOMEM the -EFAULT and empty-path pins refuse carries their one-byte
ledger, which no kernel path produces: nothing allocates between the
copy `getname_flags` makes at fs/namei.c:157 (Linux v6.18.46) and the
-ENOENT at :167-171, and the `kzalloc` at :189-192 needs a name of
EMBEDDED_NAME_MAX bytes.

Mode words and flag words are numerals except where an `AT_` constant is
the point: 8 is a bit outside `S_IRWXO`, 4/2/1/7 are R_OK, W_OK, X_OK and
their union, 1024 is AT_SYMLINK_FOLLOW, a real `AT_` bit outside the
three faccessat2 accepts, and 4294967296 is 2^32, the bit the kernel's
`int` drops. -/

/-- `check_faccessat` as the row for 48 in `Sys/SyscallTable.lean`
applies the spec: the dirfd through `fd32`, the pathname pointer and the
mode as they arrive in a1 and a2. -/
def check_faccessat_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_faccessat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

/-- `check_faccessat2` as the row for 439 applies the spec: the flag word
arrives in a3. -/
def check_faccessat2_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_faccessat2 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m

/-- `faccessat_witness` applied the same way. -/
def faccessat_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  faccessat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- `faccessat2_witness` applied the same way. -/
def faccessat2_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  faccessat2_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- `faccessat(AT_FDCWD, 8192, mode)` over a memory with nothing mapped:
the fetch, if it happens, faults on its first byte. -/
def fa_unmapped_in (mode : word) : SyscallInput := faccessat_in' AT_FDCWD 8192 mode (fun _ => none)

/-- `faccessat(AT_FDCWD, 8192, F_OK)` over a memory in which every byte is
readable and none is NUL: a pathname with no end. -/
def fa_endless_in : SyscallInput := faccessat_in' AT_FDCWD 8192 0 (fun _ => some 97)

/-- `faccessat(AT_FDCWD, NULL, F_OK)`, with "a" at 8192 where nobody reads it. -/
def fa_null_in : SyscallInput := faccessat_in' AT_FDCWD 0 0 (open_path_mem [97])

/-- `faccessat2(AT_FDCWD, 8192, mode, flags)` over a memory with nothing mapped. -/
def fa2_unmapped_in (mode flags : word) : SyscallInput :=
  faccessat2_in' AT_FDCWD 8192 mode flags (fun _ => none)

/-! ## Rocq's five faccessat examples, restated on the row -/

/-- A key living UNDER a name means reality has a DIRECTORY the flat map
only implies, and F_OK of a directory is 0 where the map would answer
-ENOENT: `do_faccessat` (fs/open.c:509, Linux v6.18.46) asks
`inode_permission` for `MAY_ACCESS` alone, which every inode grants.  So
`fs_under` declines it, and the checker declines the 0 Linux would answer
rather than agreeing with it.  Rocq: `faccessat_implied_directory_unmodeled`.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat_implied_directory_unmodeled :
    check_faccessat_row (faccessat_in [97] 0) (eff_ret 0 2) fa_under_model = CheckUnmodeled :=
  rfl

/-- The contrast, so the guard is a COMPONENT prefix and not a byte
prefix: "ab" does not live under "a" — `link_path_walk` (fs/namei.c:2441,
Linux v6.18.46) cuts components at '/' alone — so "a" is an ordinary
present key, F_OK of it is 0, and the model is left exactly as it was.
Rocq: `faccessat_byte_prefix_is_not_a_directory`.
kernel: fs/open.c:do_faccessat; fs/namei.c:link_path_walk@v6.18.46 -/
theorem faccessat_byte_prefix_is_not_a_directory :
    check_faccessat_row (faccessat_in [97] 0) (eff_ret 0 2) fa_sibling_model
      = CheckOk fa_sibling_model [] :=
  rfl

/-- THE MODE BEATS THE PATHNAME FETCH: `do_faccessat` (fs/open.c:475-476,
Linux v6.18.46) tests `mode & ~S_IRWXO` before `user_path_at` (:493), so
a bad mode with an UNREADABLE path is -EINVAL and never -EFAULT.  Here
the pathname is at an address no byte answers at, and the answer is
still -EINVAL with an empty ledger; the -EFAULT a fetch-first kernel
would give (`do_strncpy_from_user`, lib/strncpy_from_user.c:91-92) is refused.
Rocq: `faccessat_bad_mode_beats_an_unreadable_path`.
kernel: fs/open.c:do_faccessat; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem faccessat_bad_mode_beats_an_unreadable_path :
    check_faccessat_row (fa_unmapped_in 8) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat_row (fa_unmapped_in 8) (mkEffect (errno_ret EFAULT) [] []) fa_model
      = CheckReject
    ∧ check_faccessat_row (fa_unmapped_in 8) (eff_errno EFAULT 1) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- ...and because the mode is decided before `user_path_at`, that arm
reads NO user memory: a ledger claimed there is a read the kernel did not
perform, and a ledger of one byte is too.  Rocq:
`faccessat_bad_mode_records_no_copyin`.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat_bad_mode_records_no_copyin :
    check_faccessat_row (faccessat_in [97] 8) (eff_errno EINVAL 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 8) (eff_errno EINVAL 1) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 8) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- Past the mode test the ledger is REQUIRED: the F_OK call really did
read the path (`getname_flags`, fs/namei.c:157, Linux v6.18.46), so
denying it is a rejection.  This and the previous pin differ in the mode
word alone, and the ledger obligation flips with it.  Rocq:
`faccessat_existence_needs_the_copyin`.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem faccessat_existence_needs_the_copyin :
    check_faccessat_row (faccessat_in [97] 0) (mkEffect 0 [] []) fa_model = CheckReject :=
  rfl

/-! ## Rocq's four faccessat2 examples, restated on the row -/

/-- ACCEPTED FLAGS CHANGE NO ANSWER, the claim no probe reaches because it
is an equality between flag words: the same F_OK call under 0,
AT_EACCESS, AT_SYMLINK_NOFOLLOW and both lands in exactly the same place.
Under F_OK neither bit reaches anything the model holds — `do_faccessat`
(fs/open.c:481-482 and :486-489, Linux v6.18.46) lets AT_SYMLINK_NOFOLLOW
clear `LOOKUP_FOLLOW` and AT_EACCESS skip the credential override, and
a zero mask asks `inode_permission` for nothing either way.  Rocq:
`faccessat2_accepted_flags_change_no_answer`.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat2_accepted_flags_change_no_answer :
    check_faccessat2_row (faccessat2_in [97] 0 0) (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_ret 0 2) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW)) (eff_ret 0 2)
        fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW)))
        (eff_ret 0 2) fa_model = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- AT_EMPTY_PATH IS DECLINED, AND THE DECLINE DOES NOT DEPEND ON WHAT THE
KERNEL SAID: the kernel really answers 0 here (`do_faccessat`,
fs/open.c:483-484, Linux v6.18.46, sets `LOOKUP_EMPTY`, and a nonempty
pathname resolves as usual), and the checker declines whichever of 0 and
-ENOENT is offered rather than quietly agreeing with one.  The pathname is
present and resolvable, so nothing but the flag can be what the decline
is about.  Rocq: `faccessat2_empty_path_flag_declined_either_way`.
kernel: fs/open.c:do_faccessat; fs/namei.c:getname_flags@v6.18.46 -/
theorem faccessat2_empty_path_flag_declined_either_way :
    check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EMPTY_PATH)) (eff_ret 0 2) fa_model
      = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EMPTY_PATH)) (eff_errno ENOENT 2)
        fa_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- THE FLAG -EINVAL READS NO USER MEMORY, for the reason the mode -EINVAL
does not: `do_faccessat` (fs/open.c:478-479, Linux v6.18.46) tests the
flag word in its second statement, before `user_path_at` (:493), so a
ledger claimed on that arm is a read Linux did not perform.  1024 is
AT_SYMLINK_FOLLOW, a real `AT_` constant outside the three faccessat2
accepts, so the -EINVAL is the kernel's own answer and not a decline;
the pair differs in the ledger alone.  Rocq:
`faccessat2_bad_flag_records_no_copyin`.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat2_bad_flag_records_no_copyin :
    check_faccessat2_row (faccessat2_in [97] 0 1024) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 1024) (eff_errno EINVAL 2) fa_model
      = CheckReject :=
  ⟨rfl, rfl⟩

/-- The implied-directory decline reaches the 439 arm too: `do_faccessat`
(fs/open.c:467-537, Linux v6.18.46) is the one function behind both entry
points, so the real directory "a" that "a/b" implies has F_OK 0 through
either — `inode_permission` for `MAY_ACCESS` alone (:509) — where the
flat map says -ENOENT; `check_faccessat2` shares `check_faccessat_body`
for that reason, and the decline fires under AT_EACCESS as under no flag.
Rocq: `faccessat2_implied_directory_unmodeled`.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat2_implied_directory_unmodeled :
    check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_ret 0 2)
        fa_under_model = CheckUnmodeled :=
  rfl

/-! ## The accepting arm, offered the answers Linux gives and the ones it does not

F_OK of a held name is 0, or one of the two environment errnos
`faccessat_errnos` lists, both after the pathname has been read: -ENOMEM
where `__lookup_slow` (fs/namei.c:1789-1824, Linux v6.18.46) asks
`d_alloc_parallel` for the dentry at :1801 and the allocation fails
(fs/dcache.c:2549-2554, Linux v6.18.46), -EACCES from `may_lookup` on the
walk (fs/namei.c:1852-1874).  The -ENOMEMs before the copy —
`getname_flags` (fs/namei.c:146-148), and `access_override_creds`
(fs/open.c:418-465) where `do_faccessat` calls it (fs/open.c:486-489) —
carry no ledger and are refused by the ledger rule.  Nothing
else: `do_faccessat` asks `inode_permission` for `MAY_ACCESS` alone
(fs/open.c:509, Linux v6.18.46), and its -EROFS (:523-524) sits behind the `S_IWOTH` test
(:511), which F_OK fails. -/

/-- The three answers the arm accepts on the held "a", each with the
model unchanged and no events; the same three on the six-byte name
"fa a\x80", whose space and high byte are bytes like any other to
`getname_flags`, and whose -ENOMEM is the lookup's as much as "a"'s.
kernel: fs/open.c:do_faccessat; fs/namei.c:getname_flags@v6.18.46 -/
theorem present_key_accepts_zero_and_the_environment_errnos :
    check_faccessat_row (faccessat_in [97] 0) (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno ENOMEM 2) fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno EACCES 2) fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [102, 97, 32, 97, 128] 0) (eff_ret 0 6) fa_bytes_model
      = CheckOk fa_bytes_model []
    ∧ check_faccessat_row (faccessat_in [102, 97, 32, 97, 128] 0) (eff_errno ENOMEM 6)
        fa_bytes_model = CheckOk fa_bytes_model []
    ∧ check_faccessat_row (faccessat_in [102, 97, 32, 97, 128] 0) (eff_errno EACCES 6)
        fa_bytes_model = CheckOk fa_bytes_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What the arm refuses on the held "a": -ENOENT, which the walk answers
for a NEGATIVE dentry only — `step_into` (fs/namei.c:2001-2002, Linux
v6.18.46) on an RCU walk that finds it cached, `traverse_mounts`
(:1537-1538) through `handle_mounts` (:1644) otherwise; -EROFS, which `do_faccessat` (fs/open.c:511 and :523-524) reaches
only with `S_IWOTH` in the mode; -EINVAL, decided on the mode and flags
before the walk; -EPERM (1), which the F_OK path CAN reach —
`proc_pid_permission` (fs/proc/base.c:745-772, Linux v6.18.46) answers it
at :769 for a pid hidden by hidepid=1, and `devcgroup_inode_permission`
(include/linux/device_cgroup.h:17-39, Linux v6.18.46), which
`inode_permission` asks at fs/namei.c:597, answers
`devcgroup_legacy_check_permission`'s -EPERM
(security/device_cgroup.c:832-855, Linux v6.18.46) on a device node under
a restrictive device cgroup; Rocq's `faccessat_errnos` comment lists both — but only outside
the world
`faccessat_spec` is exact in, so its refusal is that precondition's and
not an impossibility; -4095, the top of the error band and no errno of
the set; a positive return, which `access` never produces; and the two
errnos that separate `openat_errnos` from `faccessat_errnos`, -EMFILE and
-ENFILE, which are `alloc_fd`'s (fs/file.c:591) and `alloc_empty_file`'s
(fs/file_table.c:278) on the descriptor path `access` never enters.
kernel: fs/open.c:do_faccessat; fs/namei.c:step_into,traverse_mounts,inode_permission; fs/proc/base.c:proc_pid_permission; include/linux/device_cgroup.h:devcgroup_inode_permission; security/device_cgroup.c:devcgroup_legacy_check_permission; fs/file.c:alloc_fd; fs/file_table.c:alloc_empty_file@v6.18.46 -/
theorem present_key_refuses_the_answers_outside_the_set :
    check_faccessat_row (faccessat_in [97] 0) (eff_errno ENOENT 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno EROFS 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno EINVAL 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno 1 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno 4095 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret 1 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno EMFILE 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno ENFILE 2) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An absent name is -ENOENT — `step_into` (fs/namei.c:2001-2002, Linux
v6.18.46) on an RCU walk that finds the negative dentry cached, or
`traverse_mounts` (:1537-1538) through `handle_mounts` (:1644) once
`lookup_slow` has made it and the walk has left RCU mode — with the model
unchanged; 0 is refused.  The -ENOMEM and -EACCES conjuncts pin the
NARROWING the section header names: both are answers the lookup can give
on this name with the ledger offered here — `d_alloc_parallel`'s -ENOMEM
(fs/dcache.c:2549-2554, Linux v6.18.46) through `__lookup_slow`
(fs/namei.c:1789-1824), `may_lookup`'s -EACCES (:1852-1874) — and the spec
twin allows neither on this arm.
kernel: fs/namei.c:step_into,traverse_mounts; fs/open.c:do_faccessat@v6.18.46 -/
theorem absent_key_is_enoent :
    check_faccessat_row (faccessat_in [97] 0) (eff_errno ENOENT 2) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret 0 2) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno ENOMEM 2) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno EACCES 2) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The ledger on a held name is the one two-byte range `getname_flags`
(fs/namei.c:157, Linux v6.18.46) read, exactly: a range one byte short of
the NUL, one byte past it, the range twice over, and no range at all are
refused alike, and so is a write, a zero-fill, an unmap or a copy beside
the 0 — `access` touches no user memory but the pathname.
kernel: fs/namei.c:getname_flags; fs/open.c:do_faccessat@v6.18.46 -/
theorem present_key_ledger_is_exactly_the_pathname :
    check_faccessat_row (faccessat_in [97] 0) (eff_ret 0 1) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret 0 3) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0)
        (with_copyins [(8192, 2), (8192, 2)] (mkEffect 0 [] [])) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0)
        (with_copyins [(8192, 2)] (mkEffect 0 [(8192, [0])] [])) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret_with_zeros 0 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret_with_unmaps 0 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret_with_copies 0 2) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The mode gate: first, and on the kernel's `int` -/

/-- `SYSCALL_DEFINE3(faccessat, …)` (fs/open.c:539-542, Linux v6.18.46)
takes the mode as an `int`, so bit 32 is dropped before `do_faccessat`
sees it: 2^32 is F_OK and answered 0 with the ledger, 2^32 + 8 is the
bad mode and -EINVAL without one.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem mode_is_the_kernels_int :
    check_faccessat_row (faccessat_in [97] 4294967296) (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 4294967304) (mkEffect (errno_ret EINVAL) [] [])
        fa_model = CheckOk fa_model [] :=
  ⟨rfl, rfl⟩

/-- The mode -EINVAL beats everything after it: the dirfd `path_init`
(fs/namei.c:2590-2611, Linux v6.18.46) would refuse with -EBADF, the
absent name the walk would refuse with -ENOENT, and a 0 the caller might
hope for.  Each is refused with and without the ledger; -EINVAL is
accepted on every one of those inputs.
kernel: fs/open.c:do_faccessat; fs/namei.c:path_init,traverse_mounts@v6.18.46 -/
theorem bad_mode_beats_the_dirfd_and_the_lookup :
    check_faccessat_row (faccessat_in' 5 8192 8 (open_path_mem [97])) (mkEffect (errno_ret EINVAL) [] [])
        fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in' 5 8192 8 (open_path_mem [97])) (mkEffect (errno_ret EBADF) [] [])
        fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in' 5 8192 8 (open_path_mem [97])) (eff_errno EBADF 2)
        fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 8) (mkEffect (errno_ret EINVAL) [] []) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [97] 8) (mkEffect (errno_ret ENOENT) [] []) absent_model
      = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 8) (eff_errno ENOENT 2) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 8) (mkEffect 0 [] []) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 8) (eff_ret 0 2) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The permission modes: declined after the gate, before the pathname

R_OK, W_OK and X_OK pass the `S_IRWXO` test and reach `inode_permission`
(fs/namei.c:568-602, Linux v6.18.46) with a real mask, whose answer
depends on the file's mode bits, the caller's credentials and the mount
— none of which the model holds.  So the spec declines them, and the
checker declines whatever the kernel said: the 0 a readable file gives,
the -EACCES an unreadable one gives, the -ENOENT of an absent name.  The
decline sits BEFORE the pathname, where the spec puts it, so no ledger is
required or refused on it; a bad mode still beats it. -/

/-- The four permission words each decline, at 0 and at -EACCES, on the
held "a"; R_OK declines the -ENOENT of an absent name too; and mode 12
(8 | R_OK) is the kernel's -EINVAL, not a decline.
kernel: fs/open.c:do_faccessat; fs/namei.c:inode_permission,traverse_mounts@v6.18.46 -/
theorem permission_modes_decline_either_answer :
    check_faccessat_row (faccessat_in [97] 4) (eff_ret 0 2) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 4) (eff_errno EACCES 2) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 2) (eff_ret 0 2) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 1) (eff_errno EACCES 2) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 7) (eff_ret 0 2) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 4) (eff_errno ENOENT 2) absent_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 4) (mkEffect 0 [] []) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 12) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `getname_flags`: the three fetch answers, before the dirfd

`user_path_at` (fs/namei.c:3211-3219, Linux v6.18.46) calls
`getname_flags` (:136-216) before `filename_lookup` reaches `path_init`
(:2540), so the fetch's three answers come before the dirfd is looked
at: -EFAULT from `do_strncpy_from_user` (lib/strncpy_from_user.c:91-92)
with the bytes through the fault in the ledger — `cstr_access_len_aux`'s
count, the model's convention (bugs/openat-getname-word-at-a-time.md), not
the words the kernel loads — -ENAMETOOLONG at
`len == PATH_MAX` (fs/namei.c:207-210, Linux v6.18.46) with the whole
window, and the empty string's -ENOENT (:167-171) with the one NUL byte. -/

/-- An unmapped pathname is -EFAULT with the one attempted byte in the
ledger, model unchanged; the same errno with an empty range, with no
ledger, or with two bytes is refused, and so are -ENOMEM, -ENAMETOOLONG
and 0 in its place.  The NULL pointer answers the same way, with the
range at 0.
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags@v6.18.46 -/
theorem unmapped_path_is_efault :
    check_faccessat_row (fa_unmapped_in 0) (eff_errno EFAULT 1) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (fa_unmapped_in 0) (eff_errno EFAULT 0) absent_model = CheckReject
    ∧ check_faccessat_row (fa_unmapped_in 0) (mkEffect (errno_ret EFAULT) [] []) absent_model
      = CheckReject
    ∧ check_faccessat_row (fa_unmapped_in 0) (eff_errno EFAULT 2) absent_model = CheckReject
    ∧ check_faccessat_row (fa_unmapped_in 0) (eff_errno ENOMEM 1) absent_model = CheckReject
    ∧ check_faccessat_row (fa_unmapped_in 0) (eff_errno ENAMETOOLONG 1) absent_model = CheckReject
    ∧ check_faccessat_row (fa_unmapped_in 0) (eff_ret 0 1) absent_model = CheckReject
    ∧ check_faccessat_row fa_null_in (eff_ret_at 0 (errno_ret EFAULT) 1) absent_model
      = CheckOk absent_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fetch beats the dirfd: with dirfd 5, nothing open there, the NULL
pointer is still -EFAULT and the -EBADF `path_init` (fs/namei.c:2610-2611,
Linux v6.18.46) would answer is refused; the empty pathname is still
-ENOENT (`getname_flags`, :167-171).
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem fetch_answers_beat_the_dirfd :
    check_faccessat_row (faccessat_in' 5 0 0 (open_path_mem [97]))
        (eff_ret_at 0 (errno_ret EFAULT) 1) absent_model = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in' 5 0 0 (open_path_mem [97]))
        (eff_ret_at 0 (errno_ret EBADF) 1) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in' 5 8192 0 (open_path_mem [])) (eff_errno ENOENT 1)
        absent_model = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in' 5 8192 0 (open_path_mem [])) (eff_errno EBADF 1)
        absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The empty pathname is -ENOENT with the one NUL byte in the ledger,
whatever the image holds; -ENOMEM, 0, and the errno without its ledger
are refused.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem access_empty_path_is_enoent :
    check_faccessat_row (faccessat_in [] 0) (eff_errno ENOENT 1) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [] 0) (eff_errno ENOENT 1) fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [] 0) (eff_errno ENOMEM 1) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [] 0) (eff_ret 0 1) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [] 0) (mkEffect (errno_ret ENOENT) [] []) absent_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### The over-long pathname

Stated one conjunct per theorem under the recursion budget the openat
section's `too_long_*` pins use, and for the same reason: each walks the
4096-byte window in the elaborator. -/

set_option maxRecDepth 100000 in
/-- The answer, with the whole window in the ledger.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem too_long_path_is_enametoolong :
    check_faccessat_row fa_endless_in (eff_errno ENAMETOOLONG 4096) absent_model
      = CheckOk absent_model [] :=
  rfl

set_option maxRecDepth 100000 in
/-- -EFAULT in its place is refused: every byte of the window was readable.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem too_long_path_refuses_efault :
    check_faccessat_row fa_endless_in (eff_errno EFAULT 4096) absent_model = CheckReject :=
  rfl

set_option maxRecDepth 100000 in
/-- A ledger one byte short of the window is refused: `strncpy_from_user`
is asked for `PATH_MAX` bytes and reads them all.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem too_long_path_refuses_a_short_ledger :
    check_faccessat_row fa_endless_in (eff_errno ENAMETOOLONG 4095) absent_model = CheckReject :=
  rfl

set_option maxRecDepth 100000 in
/-- 0 in its place is refused: no name was ever looked up.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem too_long_path_refuses_success :
    check_faccessat_row fa_endless_in (eff_ret 0 4096) absent_model = CheckReject :=
  rfl

/-! ## `path_init`: the dirfd

`path_init` (fs/namei.c:2540-2645, Linux v6.18.46) is the first to read
the dirfd, and only for a relative pathname: AT_FDCWD (:2590) starts the
walk at the working directory, and any other value is a descriptor
lookup — -EBADF for nothing there (:2610-2611), -ENOTDIR for a
non-directory (:2621-2622), and otherwise a directory the model has no
image of.  The spec answers AT_FDCWD alone and declines the rest, after
the fetch and before "." is recognised. -/

/-- dirfd 5 with nothing open there declines at 0 and at -EBADF; dirfd 3
open on the held file "a" declines at 0 and at -ENOTDIR; and "." under
dirfd 5 declines, since the dirfd is read before the dots.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem access_live_dirfd_declines :
    check_faccessat_row (faccessat_in' 5 8192 0 (open_path_mem [97])) (eff_ret 0 2) fa_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' 5 8192 0 (open_path_mem [97])) (eff_errno EBADF 2) fa_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' 3 8192 0 (open_path_mem [120])) (eff_ret 0 2) fa_file3_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' 3 8192 0 (open_path_mem [120])) (eff_errno ENOTDIR 2)
        fa_file3_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' 5 8192 0 (open_path_mem [46])) (eff_ret 0 2) fa_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The dirfd is the kernel's `int`: 0xFFFFFF9C is AT_FDCWD, and so is its
sign extension to 64 bits and 2^32 + 0xFFFFFF9C, whose high bits `fd32`
drops as the syscall's `int dfd` does; each is answered 0 on the held
"a" with the ledger.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem dirfd_is_the_kernels_int :
    check_faccessat_row (faccessat_in' 4294967196 8192 0 (open_path_mem [97])) (eff_ret 0 2)
        fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in' 18446744073709551516 8192 0 (open_path_mem [97]))
        (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in' 8589934492 8192 0 (open_path_mem [97])) (eff_ret 0 2)
        fa_model = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl⟩

/-! ## `handle_dots`: "." and "..", and the separator, and NAME_MAX -/

/-- "." and ".." exist in every directory — `handle_dots` (fs/namei.c:
2096-2132, Linux v6.18.46) answers them with no lookup — so F_OK of
either is 0 or -EACCES from the walk.  The -ENOENT refused on ".." is
`follow_dotdot`'s (fs/namei.c:2084-2087, Linux v6.18.46), answered when
`path_connected` (fs/namei.c:719-728) finds the parent outside the bind
mount the walk is in — the working directory renamed out from under a
bind-mount root: reachable, and outside the world `faccessat_spec` is
exact in, so the refusal is that precondition's.
"..." is an ordinary name, absent here, so -ENOENT with 0 refused.
kernel: fs/namei.c:handle_dots,follow_dotdot,path_connected,step_into,traverse_mounts; fs/open.c:do_faccessat@v6.18.46 -/
theorem dot_and_dotdot_exist :
    check_faccessat_row (faccessat_in [46] 0) (eff_ret 0 2) absent_model = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [46] 0) (eff_errno EACCES 2) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [46] 0) (eff_errno ENOENT 2) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [46, 46] 0) (eff_ret 0 3) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [46, 46] 0) (eff_errno ENOENT 3) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [46, 46, 46] 0) (eff_errno ENOENT 4) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [46, 46, 46] 0) (eff_ret 0 4) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A separator anywhere declines, whatever the kernel said: "/a" at
-ENOENT and at 0, "a/b" at 0 over an image that holds that very key, "/"
at 0, and "./x" at 0 over an image holding "x".  `link_path_walk`
(fs/namei.c:2441-2537, Linux v6.18.46) cuts the name into components at
'/' (the leading run at :2450-2453, each component ended by `hash_name` at
:2472, the separator run skipped at :2499-2504) and resolves every one but
the last through `walk_component` (:2519), against a directory tree the
flat map does not have.
kernel: fs/namei.c:link_path_walk,hash_name,walk_component,path_init@v6.18.46 -/
theorem separator_declines_either_answer :
    check_faccessat_row (faccessat_in [47, 97] 0) (eff_errno ENOENT 3) absent_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [47, 97] 0) (eff_ret 0 3) absent_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97, 47, 98] 0) (eff_ret 0 4) fa_under_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [47] 0) (eff_ret 0 2) absent_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [46, 47, 120] 0) (eff_ret 0 4) fa_x_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- The `NAME_MAX` boundary: a 255-byte absent name is the ordinary
-ENOENT with its 256-byte ledger; a 256-byte one declines, with the
-ENAMETOOLONG a filesystem gives it (`simple_lookup`, fs/libfs.c:71-72;
`ext4_lookup`, fs/ext4/namei.c:1768-1769, Linux v6.18.46) declined rather
than picked, and -ENOENT and 0 declined alike.
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup; fs/namei.c:step_into,traverse_mounts@v6.18.46 -/
theorem name_max_boundary :
    check_faccessat_row (faccessat_in name255 0) (eff_errno ENOENT 256) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in name255 0) (eff_ret 0 256) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in name256 0) (eff_errno ENAMETOOLONG 257) absent_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in name256 0) (eff_errno ENOENT 257) absent_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in name256 0) (eff_ret 0 257) absent_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## faccessat2: the flag gate, second, and the two declines after it -/

/-- The flag -EINVAL is second: with a bad mode AND a bad flag the answer
is the mode's -EINVAL (the same value, so the order shows in the ledger
alone: none); with F_OK and a bad flag it is the flag's, on an unmapped
pathname (never -EFAULT) and with dirfd 5 (never -EBADF); a bad flag
with R_OK is -EINVAL, not the decline.
kernel: fs/open.c:do_faccessat; lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:path_init@v6.18.46 -/
theorem bad_flag_is_einval_before_the_pathname :
    check_faccessat2_row (fa2_unmapped_in 0 1024) (mkEffect (errno_ret EINVAL) [] []) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat2_row (fa2_unmapped_in 0 1024) (mkEffect (errno_ret EFAULT) [] []) absent_model
      = CheckReject
    ∧ check_faccessat2_row (faccessat2_in' 5 8192 0 1024 (open_path_mem [97]))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in' 5 8192 0 1024 (open_path_mem [97]))
        (mkEffect (errno_ret EBADF) [] []) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 1024) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 8 1024) (eff_errno EINVAL 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 4 1024) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 1024) (eff_ret 0 2) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The flag word is the kernel's `int` too: 2^32 is 0 and answered on
the held "a"; 2^32 | AT_SYMLINK_FOLLOW is the bad flag's -EINVAL; 2^32 |
AT_EACCESS is answered as AT_EACCESS is.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem flags_are_the_kernels_int :
    check_faccessat2_row (faccessat2_in [97] 0 4294967296) (eff_ret 0 2) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 4294968320) (mkEffect (errno_ret EINVAL) [] [])
        fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 4294967808) (eff_ret 0 2) fa_model
      = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- The two declines after the gates, and their order against each other
and against the gates: AT_EMPTY_PATH on the empty pathname declines at 0
(the answer `LOOKUP_EMPTY` really produces) and at -ENOENT, with no
ledger required; R_OK under AT_EACCESS declines at 0 and at -EACCES; a
bad mode beats the AT_EMPTY_PATH decline, a bad flag beats the R_OK one.
kernel: fs/open.c:do_faccessat; fs/namei.c:getname_flags@v6.18.46 -/
theorem faccessat2_declines_after_both_gates :
    check_faccessat2_row (faccessat2_in [] 0 (Z_to_bv 64 AT_EMPTY_PATH)) (mkEffect 0 [] [])
        absent_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [] 0 (Z_to_bv 64 AT_EMPTY_PATH)) (eff_errno ENOENT 1)
        absent_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [97] 4 (Z_to_bv 64 AT_EACCESS)) (eff_ret 0 2) fa_model
      = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [97] 4 (Z_to_bv 64 AT_EACCESS)) (eff_errno EACCES 2)
        fa_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [97] 8 (Z_to_bv 64 AT_EMPTY_PATH))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 4 (Z_to_bv 64 (AT_EMPTY_PATH + 1024)))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The shared body, reached through the 439 arm: an absent name is
-ENOENT under AT_EACCESS and under AT_SYMLINK_NOFOLLOW with 0 refused;
the empty pathname is -ENOENT with its ledger; the unmapped one -EFAULT;
"." exists under AT_SYMLINK_NOFOLLOW; and the ledger lies the 48 arm
refuses are refused here.
kernel: fs/open.c:do_faccessat; fs/namei.c:traverse_mounts,getname_flags,handle_dots; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem faccessat2_reaches_the_shared_body :
    check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_errno ENOENT 2)
        absent_model = CheckOk absent_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_ret 0 2)
        absent_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW))
        (eff_errno ENOENT 2) absent_model = CheckOk absent_model []
    ∧ check_faccessat2_row (faccessat2_in [] 0 0) (eff_errno ENOENT 1) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat2_row (fa2_unmapped_in 0 0) (eff_errno EFAULT 1) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat2_row (faccessat2_in [46] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW)) (eff_ret 0 2)
        absent_model = CheckOk absent_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 0) (mkEffect 0 [] []) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 0) (eff_ret 0 3) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 0) (eff_ret_with_zeros 0 2) fa_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The arms, offered an errno and required to refuse

A checker answering `CheckUnmodeled` on every input meets every lemma of
its file against a spec that declines everywhere.  These pins are on the
arms by name, with a kernel-shaped answer offered and `CheckReject`
required, so that shape fails here. -/

/-- `check_access_exists` on the bare effect the wrapper hands it: 0,
-ENOMEM and -EACCES accepted with the model unchanged; -ENOENT, -EPERM
(1), -4095, a positive return, a ledger entry that survived the
wrapper's clearing, and a zero-fill refused.
kernel: fs/open.c:do_faccessat; fs/namei.c:traverse_mounts@v6.18.46 -/
theorem check_access_exists_accepts_the_set_and_refuses_the_rest :
    check_access_exists (mkEffect 0 [] []) fa_model = CheckOk fa_model []
    ∧ check_access_exists (mkEffect (errno_ret ENOMEM) [] []) fa_model = CheckOk fa_model []
    ∧ check_access_exists (mkEffect (errno_ret EACCES) [] []) fa_model = CheckOk fa_model []
    ∧ check_access_exists (mkEffect (errno_ret ENOENT) [] []) fa_model = CheckReject
    ∧ check_access_exists (mkEffect (errno_ret 1) [] []) fa_model = CheckReject
    ∧ check_access_exists (mkEffect (errno_ret 4095) [] []) fa_model = CheckReject
    ∧ check_access_exists (mkEffect 1 [] []) fa_model = CheckReject
    ∧ check_access_exists (with_copyins [(8192, 2)] (mkEffect 0 [] [])) fa_model = CheckReject
    ∧ check_access_exists (SyscallEffect.mkEffectU 0 [] [(4096, 8)] [] [] []) fa_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `check_faccessat_body` on the effect with the ledger cleared, the
dirfd as the row's `fd32` delivers AT_FDCWD (0xFFFFFF9C): 0 on the held
"a" accepted, -ENOENT on it refused, -ENOENT on the absent one accepted
and 0 refused, and a ledger the wrapper failed to clear refused — the
body claims no copy-in of its own.
kernel: fs/namei.c:path_init,traverse_mounts@v6.18.46 -/
theorem check_faccessat_body_by_name :
    check_faccessat_body (faccessat_in [97] 0) 4294967196 8192 (mkEffect 0 [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat_body (faccessat_in [97] 0) 4294967196 8192 (mkEffect (errno_ret ENOENT) [] [])
        fa_model = CheckReject
    ∧ check_faccessat_body (faccessat_in [97] 0) 4294967196 8192 (mkEffect (errno_ret ENOENT) [] [])
        absent_model = CheckOk absent_model []
    ∧ check_faccessat_body (faccessat_in [97] 0) 4294967196 8192 (mkEffect 0 [] []) absent_model
      = CheckReject
    ∧ check_faccessat_body (faccessat_in [97] 0) 4294967196 8192 (eff_ret 0 2) fa_model
      = CheckReject
    ∧ check_faccessat_body (faccessat_in [97] 0) 5 8192 (mkEffect 0 [] []) fa_model
      = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The local review's cases: one-line mutations the sections above let through -/

/-- THE LEDGER'S ADDRESS is the pathname pointer and no neighbour of it:
`getname_flags` (fs/namei.c:157, Linux v6.18.46) hands `filename` itself
to `strncpy_from_user`, so a ledger starting one byte on either side of
`pathp` records a read Linux did not make and is refused, the return
being right.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem ledger_address_is_the_pathname_pointer :
    check_faccessat_row (faccessat_in [97] 0) (eff_ret_at 8193 0 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret_at 8191 0 2) fa_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- A NEGATIVE dirfd other than AT_FDCWD, and dirfd 0, are declined like
the positive ones: `path_init` (fs/namei.c:2590, Linux v6.18.46) tests
`dfd == AT_FDCWD` and nothing else, so -1 and -101 are descriptor lookups
of nothing, -EBADF (:2610-2611), and 0 is a descriptor that is no
directory, -ENOTDIR (:2621-2622); the model answers none of them, in
either polarity.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem negative_dirfd_declines_like_a_positive_one :
    check_faccessat_row (faccessat_in' (Z_to_bv 64 (-1)) 8192 0 (open_path_mem [97]))
        (eff_errno EBADF 2) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' (Z_to_bv 64 (-1)) 8192 0 (open_path_mem [97]))
        (eff_ret 0 2) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' (Z_to_bv 64 (-101)) 8192 0 (open_path_mem [97]))
        (eff_errno EBADF 2) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' 0 8192 0 (open_path_mem [97])) (eff_errno ENOTDIR 2)
        fa_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- THE IMPLIED DIRECTORY declines the map's -ENOENT as much as Linux's 0:
with "a/b" held and "a" itself absent from the map, the flat map would
answer -ENOENT for "a", but reality has the directory "a", whose F_OK is
0 — `do_faccessat` (fs/open.c:509, Linux v6.18.46) asks
`inode_permission` for `MAY_ACCESS` alone.  `fs_under` fires before the
lookup, so a checker that looked the name up first and answered the map
is refused in both polarities; the -ENOENT a negative dentry earns
(`step_into`, fs/namei.c:2001-2002, or `traverse_mounts`, :1537-1538,
Linux v6.18.46) is for a name that is nowhere, which this one is not.
kernel: fs/open.c:do_faccessat; fs/namei.c:step_into,traverse_mounts@v6.18.46 -/
theorem implied_directory_declines_the_maps_answer_too :
    check_faccessat_row (faccessat_in [97] 0) (eff_errno ENOENT 2) fa_under_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno ENOENT 2) under_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret 0 2) under_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- A TRAILING separator is a separator: "a/" names a directory "a" must
be — `lookup_last` (fs/namei.c:2647-2653, Linux v6.18.46) sets
`LOOKUP_DIRECTORY` for a trailing slash and `path_lookupat`
(fs/namei.c:2685-2687) answers -ENOTDIR when the last component cannot
be looked up in — and the regular file "a" of the model is no directory.
The separator decline fires first, so neither -ENOTDIR nor 0 is judged.
kernel: fs/namei.c:lookup_last,path_lookupat@v6.18.46 -/
theorem trailing_separator_declines_either_answer :
    check_faccessat_row (faccessat_in [97, 47] 0) (eff_errno ENOTDIR 3) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97, 47] 0) (eff_ret 0 3) fa_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- "ab" at 8192 with the byte after it unmapped: a pathname that faults
past its first byte. -/
def fa_partial_in : SyscallInput := faccessat_in' AT_FDCWD 8192 0 (bytes_at 8192 [97, 98])

/-- A pathname that FAULTS PAST ITS FIRST BYTE: `do_strncpy_from_user`
(lib/strncpy_from_user.c:28-93, Linux v6.18.46) loads a word at a time
(:41) and falls to single bytes (:68-78) only on an unaligned source or
after a word faults, answering -EFAULT (:91-92), which `getname_flags`
(fs/namei.c:162-164) returns; the ledger is `cstr_access_len_aux`'s count
— every byte through the first unreadable one, the model's convention
(bugs/openat-getname-word-at-a-time.md), three here and not the two that
answered — and a checker that took the fault for the end
of the string and looked "ab" up would answer the -ENOENT refused here.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem partially_mapped_path_is_efault_with_the_bytes_attempted :
    check_faccessat_row fa_partial_in (eff_errno EFAULT 3) absent_model = CheckOk absent_model []
    ∧ check_faccessat_row fa_partial_in (eff_errno EFAULT 2) absent_model = CheckReject
    ∧ check_faccessat_row fa_partial_in (eff_errno ENOENT 3) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- THE -EINVAL ARMS carry no effect at all, not only no copy-in: the
returns at fs/open.c:475-476 and :478-479 (`do_faccessat`, Linux
v6.18.46) touch no user memory, so a write or a zero-fill beside the
errno is refused on both entry points.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem einval_arms_carry_no_write :
    check_faccessat_row (faccessat_in [97] 8) (mkEffect (errno_ret EINVAL) [(8192, [0])] [])
        fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 8)
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 8)] [] [] []) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 1024)
        (mkEffect (errno_ret EINVAL) [(8192, [0])] []) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- `check_access_exists` BY NAME refuses a write, an unmap and a copy
beside the return as it refuses a zero-fill and a copy-in: `do_faccessat`
(fs/open.c:467-537, Linux v6.18.46) reads the pathname and writes
nothing, on 0 and on -EACCES alike.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem check_access_exists_refuses_every_other_ledger :
    check_access_exists (mkEffect 0 [(8192, [0])] []) fa_model = CheckReject
    ∧ check_access_exists (mkEffect (errno_ret EACCES) [(8192, [0])] []) fa_model = CheckReject
    ∧ check_access_exists (SyscallEffect.mkEffectU 0 [] [] [(4096, 4096)] [] []) fa_model
      = CheckReject
    ∧ check_access_exists (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 4096 8192 8] [])
        fa_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- AT_EMPTY_PATH is declined as a BIT, beside an accepted flag as much
as alone, and before the pathname is fetched: `do_faccessat`
(fs/open.c:478-479, Linux v6.18.46) passes the word, :483-484 sets
`LOOKUP_EMPTY`, and the model stops there — so the -EFAULT
`do_strncpy_from_user` (lib/strncpy_from_user.c:91-92) would give an
unmapped pathname is never judged either.  Beside it, a permission mode
under an accepted flag is the mode decline, not the flag's answer.
kernel: fs/open.c:do_faccessat; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem empty_path_bit_declines_beside_an_accepted_flag :
    check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EMPTY_PATH + AT_EACCESS)))
        (eff_ret 0 2) fa_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EMPTY_PATH + AT_SYMLINK_NOFOLLOW)))
        (mkEffect 0 [] []) fa_model = CheckUnmodeled
    ∧ check_faccessat2_row (fa2_unmapped_in 0 (Z_to_bv 64 AT_EMPTY_PATH)) (eff_errno EFAULT 1)
        absent_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [97] 4 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW)) (eff_ret 0 2)
        fa_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- THE KERNEL'S `int` IS SIGNED: a mode of -1, or of bit 31 alone, has
bits outside `S_IRWXO` and is -EINVAL at fs/open.c:475-476
(`do_faccessat`, Linux v6.18.46); a flags word of -1 has bits outside
the three accepted and is -EINVAL at :478-479.  Both with no effect
beside the errno, and 0 refused.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem negative_mode_and_flags_are_einval :
    check_faccessat_row (faccessat_in [97] (Z_to_bv 64 (-1))) (mkEffect (errno_ret EINVAL) [] [])
        fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [97] (Z_to_bv 64 (-1))) (eff_ret 0 2) fa_model
      = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 2147483648) (mkEffect (errno_ret EINVAL) [] [])
        fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 (-1)))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- THE FETCH ERRNOS are refused where the fetch SUCCEEDED: "a" read
whole and absent is -ENOENT, and neither the -EFAULT of
`do_strncpy_from_user` (lib/strncpy_from_user.c:91-92, Linux v6.18.46)
nor the -ENAMETOOLONG of `getname_flags` (fs/namei.c:207-210), whose
conditions did not hold.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem fetch_errnos_refused_where_the_fetch_succeeded :
    check_faccessat_row (faccessat_in [97] 0) (eff_errno EFAULT 2) absent_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno ENAMETOOLONG 2) absent_model
      = CheckReject :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- ...and -ENOENT in the over-long pathname's place is refused: nothing
was looked up, `getname_flags` (fs/namei.c:207-210, Linux v6.18.46)
having answered -ENAMETOOLONG at `len == PATH_MAX`.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem too_long_path_refuses_enoent :
    check_faccessat_row fa_endless_in (eff_errno ENOENT 4096) absent_model = CheckReject :=
  rfl

/-- The 255-byte name, held. -/
def fa_name255_model : Model := fixture_of (fs := [(name255, [])])

set_option maxRecDepth 8192 in
/-- The NAME_MAX boundary from the accepting side: a 255-byte name that
IS held is looked up — `ext4_lookup` (fs/ext4/namei.c:1768-1769, Linux
v6.18.46) refuses only `len > EXT4_NAME_LEN` — and its F_OK is 0, with
the model unchanged.
kernel: fs/ext4/namei.c:ext4_lookup; fs/open.c:do_faccessat@v6.18.46 -/
theorem name_max_name_held_is_zero :
    check_faccessat_row (faccessat_in name255 0) (eff_ret 0 256) fa_name255_model
      = CheckOk fa_name255_model [] :=
  rfl

/-- ".." under a live dirfd is the dirfd's decline, not `handle_dots`'s
answer: `path_init` (fs/namei.c:2590, Linux v6.18.46) is read before the
first component.  And "." under a bad mode is the mode's -EINVAL
(fs/open.c:475-476), before any of it.
kernel: fs/namei.c:path_init; fs/open.c:do_faccessat@v6.18.46 -/
theorem dotdot_under_a_live_dirfd_and_dot_under_a_bad_mode :
    check_faccessat_row (faccessat_in' 5 8192 0 (open_path_mem [46, 46])) (eff_ret 0 3) fa_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [46] 8) (mkEffect (errno_ret EINVAL) [] []) absent_model
      = CheckOk absent_model [] :=
  ⟨rfl, rfl⟩

/-! ## The witness names an outcome the checker accepts

`faccessat_witness` takes the SUCCESS branch where the path resolves —
the alt's right branch, unlike `openat_witness`, because faccessat builds
no state and 0 is the outcome a real run produces — the deterministic
errno on the deterministic arms, and `Unmodeled` where the spec
declines.  Each outcome below is paired with the checker's acceptance of
the effect it names. -/

/-- On a held name, the witness is 0 with the pathname in the ledger; on
an absent one, -ENOENT; on "." and "..", 0; on "fa a\x80" held, 0 with
the six-byte ledger.  The checker accepts every one with the model
unchanged.
kernel: fs/open.c:do_faccessat; fs/namei.c:traverse_mounts,handle_dots@v6.18.46 -/
theorem witness_is_success_where_the_path_resolves :
    faccessat_witness_row (faccessat_in [97] 0) fa_model = Ok (eff_ret 0 2) fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ faccessat_witness_row (faccessat_in [97] 0) absent_model
      = Ok (eff_errno ENOENT 2) absent_model []
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno ENOENT 2) absent_model
      = CheckOk absent_model []
    ∧ faccessat_witness_row (faccessat_in [46] 0) absent_model = Ok (eff_ret 0 2) absent_model []
    ∧ faccessat_witness_row (faccessat_in [46, 46] 0) absent_model
      = Ok (eff_ret 0 3) absent_model []
    ∧ faccessat_witness_row (faccessat_in [102, 97, 32, 97, 128] 0) fa_bytes_model
      = Ok (eff_ret 0 6) fa_bytes_model []
    ∧ check_faccessat_row (faccessat_in [102, 97, 32, 97, 128] 0) (eff_ret 0 6) fa_bytes_model
      = CheckOk fa_bytes_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- On the deterministic arms the witness is that arm's errno: -EINVAL
for a bad mode with NO ledger, -EFAULT for an unmapped pathname with the
one byte, -ENOENT for the empty pathname with its NUL; and for
faccessat2, -EINVAL for the bad flag with no ledger.  The checker accepts
each.
kernel: fs/open.c:do_faccessat; fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem witness_names_the_deterministic_errno_for_access :
    faccessat_witness_row (faccessat_in [97] 8) fa_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 8) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ faccessat_witness_row (fa_unmapped_in 0) absent_model
      = Ok (eff_errno EFAULT 1) absent_model []
    ∧ faccessat_witness_row (faccessat_in [] 0) absent_model
      = Ok (eff_errno ENOENT 1) absent_model []
    ∧ faccessat2_witness_row (faccessat2_in [97] 0 1024) fa_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 1024) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ faccessat2_witness_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) fa_model
      = Ok (eff_ret 0 2) fa_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Where the spec declines, the witness is `Unmodeled`: a permission
mode, a live dirfd, a separator, an implied directory; and for
faccessat2, AT_EMPTY_PATH and R_OK under AT_EACCESS.
kernel: fs/open.c:do_faccessat; fs/namei.c:path_init,link_path_walk@v6.18.46 -/
theorem witness_is_unmodeled_where_access_declines :
    faccessat_witness_row (faccessat_in [97] 4) fa_model = Unmodeled
    ∧ faccessat_witness_row (faccessat_in' 5 8192 0 (open_path_mem [97])) fa_model = Unmodeled
    ∧ faccessat_witness_row (faccessat_in [47, 97] 0) absent_model = Unmodeled
    ∧ faccessat_witness_row (faccessat_in [97] 0) fa_under_model = Unmodeled
    ∧ faccessat2_witness_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EMPTY_PATH)) fa_model = Unmodeled
    ∧ faccessat2_witness_row (faccessat2_in [97] 4 (Z_to_bv 64 AT_EACCESS)) fa_model = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- ...and for the 256-byte name, stated apart under its recursion budget.
kernel: fs/libfs.c:simple_lookup@v6.18.46 -/
theorem witness_is_unmodeled_past_name_max :
    faccessat_witness_row (faccessat_in name256 0) absent_model = Unmodeled :=
  rfl

set_option maxRecDepth 100000 in
/-- Past PATH_MAX the witness names -ENAMETOOLONG with the whole window in
its ledger, the answer `getname_flags` (fs/namei.c:207-210, Linux
v6.18.46) gives at `len == PATH_MAX` — and not the -EFAULT of a fetch
that never faulted: every byte of the window was readable.  The first
mutation pass let a witness naming -EFAULT here through; this pins it.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem witness_names_enametoolong_past_path_max :
    faccessat_witness_row fa_endless_in absent_model
      = Ok (eff_errno ENAMETOOLONG 4096) absent_model [] :=
  rfl


/-! ## The deep review's cases: the 439 rows, "..", the pass-through, the masks, PATH_MAX-1

Each pin below closes a gap the fresh-context review found between what the
sections above pin and what the checker decides: the faccessat2 rows were
pinned on their flag gates but never on a bad mode under an ACCEPTED flag word
or on the body's declines; ".." was pinned at 0 and -ENOENT only; no decline
past the fetch was offered a wrong ledger; the two masks were pinned from the
refused side by one bit each; and the 4095-byte name, the longest
`getname_flags` (fs/namei.c:207-210, Linux v6.18.46) accepts, was pinned at
the reader and nowhere else.  Where a pin fixes a fact about the model rather
than about Linux — the ledger is not compared under a decline — its evidence
line says `model:`. -/

/-- `faccessat2(AT_FDCWD, 8192, F_OK, 0)` over a memory in which every byte is
readable and none is NUL: the 439 twin of `fa_endless_in`. -/
def fa2_endless_in : SyscallInput := faccessat2_in' AT_FDCWD 8192 0 0 (fun _ => some 97)

/-- `faccessat(AT_FDCWD, 8192, F_OK)` over a memory of 'a' everywhere but a NUL
at 8192 + 4095: a 4095-byte pathname, the longest `getname_flags`
(fs/namei.c:207-210, Linux v6.18.46) accepts, in constant-time memory so the
walk is linear like `fa_endless_in`'s. -/
def fa_path_max_minus_one_in : SyscallInput :=
  faccessat_in' AT_FDCWD 8192 0 (fun a => if bv_eqb a 12287 then some 0 else some 97)

/-- The 439 mode gate under every accepted flag word: `do_faccessat`
(fs/open.c:475-476, Linux v6.18.46) refuses `mode & ~S_IRWXO` before it reads
the flags (:478-479) or the pathname (:493), so -EINVAL with nothing read is
the answer under 0, AT_EACCESS, AT_SYMLINK_NOFOLLOW and both, and 0, -ENOENT
or a ledger beside the -EINVAL is refused on each.  The sections above pinned
this gate only beside a bad flag word, where the flag gate answers the same.
kernel: fs/open.c:do_faccessat; fs/namei.c:step_into@v6.18.46 -/
theorem faccessat2_bad_mode_is_einval_under_every_accepted_flag :
    check_faccessat2_row (faccessat2_in [97] 8 0) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 8 0) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 0) (mkEffect 0 [] []) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 0) (eff_errno EINVAL 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 0) (eff_errno ENOENT 2) absent_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 0) (eff_errno ENOENT 0) absent_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 0) (mkEffect (errno_ret ENOENT) [] []) absent_model
      = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 (Z_to_bv 64 AT_EACCESS))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 8 (Z_to_bv 64 AT_EACCESS)) (eff_ret 0 2) fa_model
      = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 (Z_to_bv 64 AT_EACCESS)) (eff_errno ENOENT 2)
        absent_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 8 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW)) (eff_ret 0 2)
        fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 8 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW)))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 8 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW)))
        (eff_ret 0 2) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- On the 439 row too, the mode's -EINVAL (fs/open.c:475-476, Linux v6.18.46)
beats the -EBADF `path_init` (fs/namei.c:2610-2611) would give a dead dirfd and
the -EFAULT `do_strncpy_from_user` (lib/strncpy_from_user.c:91-92) would give an
unmapped pathname: neither is reached, so neither is accepted, with or without
a ledger.
kernel: fs/open.c:do_faccessat; fs/namei.c:path_init; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem faccessat2_bad_mode_beats_the_dirfd_and_the_fetch :
    check_faccessat2_row (faccessat2_in' 5 8192 8 0 (open_path_mem [97]))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in' 5 8192 8 0 (open_path_mem [97]))
        (mkEffect (errno_ret EBADF) [] []) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in' 5 8192 8 0 (open_path_mem [97])) (eff_errno EBADF 2)
        fa_model = CheckReject
    ∧ check_faccessat2_row (fa2_unmapped_in 8 0) (mkEffect (errno_ret EINVAL) [] []) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat2_row (fa2_unmapped_in 8 0) (mkEffect (errno_ret EFAULT) [] []) absent_model
      = CheckReject
    ∧ check_faccessat2_row (fa2_unmapped_in 8 (Z_to_bv 64 AT_EACCESS)) (eff_errno EFAULT 1)
        absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Under the accepted flag words a held name never earns -EINVAL: `do_faccessat`
(fs/open.c:475-479, Linux v6.18.46) decides it on the two words alone, before
the pathname is read, and 0, AT_EACCESS, AT_SYMLINK_NOFOLLOW and both pass
that test.  Nor -ENOENT, which `step_into` (fs/namei.c:2001-2002) gives a
NEGATIVE dentry only; nor -EROFS, behind the `S_IWOTH` test (fs/open.c:511)
F_OK fails; nor a positive return.  -EACCES and -ENOMEM with the ledger stay
accepted under the flags as under none: the probes `faccessat2_spec.c` refuse
-EINVAL under `eaccess` and `both-flags` by `--mutate`, and this is the same
claim on the checker.
kernel: fs/open.c:do_faccessat; fs/namei.c:step_into,traverse_mounts@v6.18.46 -/
theorem faccessat2_accepted_flags_refuse_the_answers_outside_the_set :
    check_faccessat2_row (faccessat2_in [97] 0 0) (eff_errno EINVAL 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_errno EINVAL 2)
        fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW))
        (eff_errno EINVAL 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW)))
        (eff_errno EINVAL 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_errno ENOENT 2)
        fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW))
        (eff_errno EROFS 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW)))
        (eff_ret 1 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_errno EACCES 2)
        fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW))
        (eff_errno ENOMEM 2) fa_model = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The 439 witness on the mode arm, which no pin above reached: it names the
-EINVAL `do_faccessat` (fs/open.c:475-476, Linux v6.18.46) gives a bad mode
with no ledger, whatever the flag word beside it — accepted, bad, or
AT_EMPTY_PATH, since the mode is tested first — and whatever the pathname,
unmapped included; the checker accepts that outcome.
kernel: fs/open.c:do_faccessat; fs/namei.c:path_init@v6.18.46 -/
theorem faccessat2_witness_names_the_mode_einval :
    faccessat2_witness_row (faccessat2_in [97] 8 0) fa_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 8 0) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ faccessat2_witness_row (faccessat2_in [97] 8 (Z_to_bv 64 AT_EACCESS)) fa_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fa_model []
    ∧ faccessat2_witness_row (faccessat2_in [97] 8 1024) fa_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fa_model []
    ∧ faccessat2_witness_row (faccessat2_in [97] 8 (Z_to_bv 64 AT_EMPTY_PATH)) fa_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fa_model []
    ∧ faccessat2_witness_row (fa2_unmapped_in 8 0) absent_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) absent_model []
    ∧ faccessat2_witness_row (faccessat2_in' 5 8192 8 0 (open_path_mem [97])) fa_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fa_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The shared body through the 439 witness: 0 on ".", ".." and a held name
under the accepted words — `do_faccessat` (fs/open.c:467-537, Linux v6.18.46)
is the one function behind both entry points — -ENOENT on an absent one, the
fetch's -EFAULT (lib/strncpy_from_user.c:91-92) and the empty pathname's
-ENOENT (fs/namei.c:167-171) with their ledgers, and `Unmodeled` on the dirfd
`path_init` reads (fs/namei.c:2590), on a separator `link_path_walk`
(:2441-2537) would cut at, and on the implied directory.
kernel: fs/open.c:do_faccessat; fs/namei.c:getname_flags,path_init,handle_dots,link_path_walk; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem faccessat2_witness_reaches_the_shared_body :
    faccessat2_witness_row (faccessat2_in [46] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW)) absent_model
      = Ok (eff_ret 0 2) absent_model []
    ∧ faccessat2_witness_row (faccessat2_in [46, 46] 0 (Z_to_bv 64 AT_EACCESS)) fa_model
      = Ok (eff_ret 0 3) fa_model []
    ∧ faccessat2_witness_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW)) fa_model
      = Ok (eff_ret 0 2) fa_model []
    ∧ faccessat2_witness_row (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW)))
        fa_model = Ok (eff_ret 0 2) fa_model []
    ∧ faccessat2_witness_row (faccessat2_in [97] 0 0) absent_model
      = Ok (eff_errno ENOENT 2) absent_model []
    ∧ faccessat2_witness_row (fa2_unmapped_in 0 0) absent_model
      = Ok (eff_errno EFAULT 1) absent_model []
    ∧ faccessat2_witness_row (fa2_unmapped_in 0 (Z_to_bv 64 AT_EACCESS)) absent_model
      = Ok (eff_errno EFAULT 1) absent_model []
    ∧ faccessat2_witness_row (faccessat2_in [] 0 0) absent_model
      = Ok (eff_errno ENOENT 1) absent_model []
    ∧ faccessat2_witness_row (faccessat2_in' 5 8192 0 0 (open_path_mem [97])) fa_model = Unmodeled
    ∧ faccessat2_witness_row (faccessat2_in' 5 8192 0 (Z_to_bv 64 AT_EACCESS) (open_path_mem [97]))
        fa_model = Unmodeled
    ∧ faccessat2_witness_row (faccessat2_in [47, 97] 0 0) absent_model = Unmodeled
    ∧ faccessat2_witness_row (faccessat2_in [97] 0 0) fa_under_model = Unmodeled
    ∧ faccessat2_witness_row (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW)))
        fa_under_model = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- Past PATH_MAX the 439 witness names -ENAMETOOLONG with the whole window, the
answer `getname_flags` (fs/namei.c:207-210, Linux v6.18.46) gives at
`len == PATH_MAX`, as the 48 witness does.
kernel: fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem faccessat2_witness_names_enametoolong_past_path_max :
    faccessat2_witness_row fa2_endless_in absent_model
      = Ok (eff_errno ENAMETOOLONG 4096) absent_model [] :=
  rfl

set_option maxRecDepth 8192 in
/-- ...and past NAME_MAX it declines, as the 48 witness does: the
-ENAMETOOLONG is the filesystem's (`simple_lookup`, fs/libfs.c:71-72, Linux
v6.18.46), not the VFS's, and the flat map has no filesystem.
kernel: fs/libfs.c:simple_lookup@v6.18.46 -/
theorem faccessat2_witness_is_unmodeled_past_name_max :
    faccessat2_witness_row (faccessat2_in name256 0 0) absent_model = Unmodeled :=
  rfl

/-- ".." accepts the environment errnos as "." and a held name do: `may_lookup`
(fs/namei.c:1852-1874, Linux v6.18.46) tests search permission on the working
directory in `link_path_walk`'s first iteration (:2441-2537), before
`handle_dots` (:2096-2132) answers the component, so -EACCES is real on "..";
-ENOMEM is admitted because `access_exists_spec` admits one set on every name
it resolves.  -ENOTDIR, a ledger short of the NUL and a positive return are
refused, and the same holds through the 439 row.
kernel: fs/namei.c:may_lookup,handle_dots,link_path_walk,step_into; fs/open.c:do_faccessat@v6.18.46 -/
theorem dotdot_accepts_the_environment_errnos :
    check_faccessat_row (faccessat_in [46, 46] 0) (eff_errno EACCES 3) fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [46, 46] 0) (eff_errno ENOMEM 3) fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [46, 46] 0) (eff_errno EACCES 3) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [46, 46] 0) (eff_errno ENOMEM 3) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [46, 46] 0) (eff_errno ENOTDIR 3) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [46, 46] 0) (eff_errno EACCES 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [46, 46] 0) (eff_ret 1 3) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [46] 0) (eff_errno ENOMEM 2) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat_row (faccessat_in [46] 0) (eff_errno ENOTDIR 2) absent_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [46, 46] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW))
        (eff_errno EACCES 3) fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [46, 46] 0 0) (eff_errno ENOENT 3) fa_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A decline past the fetch is a decline whatever ledger came with it: the
K1 wrapper passes `CheckUnmodeled` through before it compares the ledger, as
`record_copyins` leaves an `unmodeled` alone, so the dirfd, the separator and
the implied directory decline on a missing, short, long or foreign ledger
alike.  The openat half pins this on its NAME_MAX arm; the faccessat half did
not, so a wrapper that compared the ledger first and refused on a mismatch
would have passed every pin above.
model: `check_copyins_after` in `Checks/Sys/Prelude.lean` and `record_copyins`'s `unmodeled` arm; no kernel behaviour is claimed -/
theorem access_declines_pass_through_a_wrong_ledger :
    check_faccessat_row (faccessat_in [97] 0) (mkEffect 0 [] []) fa_under_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret 0 1) fa_under_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret_with_zeros 0 2) fa_under_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [47, 97] 0) (eff_errno ENOENT 1) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [47, 97] 0) (mkEffect 0 [] []) absent_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in [47, 97] 0) (eff_errno ENOENT 4) absent_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' 5 8192 0 (open_path_mem [97]))
        (mkEffect (errno_ret EBADF) [] []) fa_model = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' 5 8192 0 (open_path_mem [97])) (eff_ret 0 7) fa_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in' 5 8192 0 (open_path_mem [97]))
        (eff_ret_at 4096 (errno_ret EBADF) 2) fa_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (mkEffect 0 [] [])
        fa_under_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- ...and the NAME_MAX decline likewise, with a one-byte ledger and with none.
model: `check_copyins_after` in `Checks/Sys/Prelude.lean` passes `CheckUnmodeled` through before the ledger is compared -/
theorem name_max_decline_passes_through_a_wrong_ledger :
    check_faccessat_row (faccessat_in name256 0) (eff_errno ENAMETOOLONG 1) absent_model
      = CheckUnmodeled
    ∧ check_faccessat_row (faccessat_in name256 0) (mkEffect (errno_ret ENAMETOOLONG) [] [])
        absent_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- The body's declines reached through the 439 row, which the sections above
restated only for the implied directory: the dirfd `path_init` reads
(fs/namei.c:2590-2622, Linux v6.18.46) — dead, a file, -1 — the separator
`link_path_walk` (:2441-2537) would cut at, and the trailing separator
`lookup_last` (:2647-2653) would turn into LOOKUP_DIRECTORY, each declined in
both polarities under 0 and under an accepted flag; ".." through 439 is
answered, and "." under a live dirfd is the dirfd's decline, not the dot's
answer.
kernel: fs/namei.c:path_init,link_path_walk,lookup_last; fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat2_reaches_the_declines_after_the_fetch :
    check_faccessat2_row (faccessat2_in' 5 8192 0 0 (open_path_mem [97])) (eff_errno EBADF 2)
        fa_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in' 5 8192 0 0 (open_path_mem [97])) (eff_ret 0 2) fa_model
      = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in' 5 8192 0 (Z_to_bv 64 AT_EACCESS) (open_path_mem [97]))
        (eff_errno EBADF 2) fa_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in' 3 8192 0 0 (open_path_mem [120])) (eff_errno ENOTDIR 2)
        fa_file3_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in' 3 8192 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW)
        (open_path_mem [120])) (eff_ret 0 2) fa_file3_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [47, 97] 0 0) (eff_errno ENOENT 3) fa_model
      = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [47, 97] 0 0) (eff_ret 0 3) absent_model
      = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [47, 97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_ret 0 3)
        absent_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [97, 47] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW))
        (eff_errno ENOTDIR 3) fa_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [97, 47, 98] 0 0) (eff_ret 0 4) fa_under_model
      = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in [46, 46] 0 0) (eff_ret 0 3) absent_model
      = CheckOk absent_model []
    ∧ check_faccessat2_row (faccessat2_in [46, 46] 0 0) (eff_errno ENOENT 3) absent_model
      = CheckReject
    ∧ check_faccessat2_row (faccessat2_in' 5 8192 0 0 (open_path_mem [46])) (eff_ret 0 2) fa_model
      = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in' (Z_to_bv 64 (-1)) 8192 0 0 (open_path_mem [97]))
        (eff_errno EBADF 2) fa_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- The NAME_MAX boundary through 439: 256 bytes decline whatever was said —
the filesystem's -ENAMETOOLONG (`simple_lookup`, fs/libfs.c:71-72;
`ext4_lookup`, fs/ext4/namei.c:1768-1769, Linux v6.18.46), 0, -ENOENT under
AT_EACCESS — and 255 are the ordinary -ENOENT.
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup; fs/namei.c:step_into; fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat2_name_max_boundary :
    check_faccessat2_row (faccessat2_in name256 0 0) (eff_errno ENAMETOOLONG 257) absent_model
      = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in name256 0 0) (eff_ret 0 257) absent_model
      = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in name256 0 (Z_to_bv 64 AT_EACCESS))
        (eff_errno ENOENT 257) absent_model = CheckUnmodeled
    ∧ check_faccessat2_row (faccessat2_in name255 0 0) (eff_errno ENOENT 256) absent_model
      = CheckOk absent_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Returns outside the errno band on a held name: the pins above refuse -4095
and +1, the band's two edges; -4096, one below -MAX_ERRNO
(include/linux/err.h:18, Linux v6.18.46) and so no errno at all, the sign bit
alone, the largest positive word and a positive `int`-sized return are
refused as well, on both rows and by the acceptor directly, since
`check_access_exists` tests membership of {0, -ENOMEM, -EACCES} and never
computes a band.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem present_key_refuses_returns_outside_the_errno_band :
    check_faccessat_row (faccessat_in [97] 0) (eff_errno 4096 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret 9223372036854775808 2) fa_model
      = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret 9223372036854775807 2) fa_model
      = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_ret 2147483648 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (eff_errno 4096 2) absent_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 0) (eff_errno 4096 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS))
        (eff_ret 9223372036854775808 2) fa_model = CheckReject
    ∧ check_access_exists (mkEffect (errno_ret 4096) [] []) fa_model = CheckReject
    ∧ check_access_exists (mkEffect 9223372036854775808 [] []) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The mode mask is `S_IRWXO` exactly: `mode & ~S_IRWXO` (fs/open.c:475-476,
Linux v6.18.46) refuses bits 4 and 5, 8|7, 0x7fffffff and 0xffffffff alike,
with no ledger, and 0 with the ledger is refused on each.  The sections above
pinned the mask from the refused side by bit 3 and the sign bit only, so a
mask widened by one bit would have passed them.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem mode_mask_is_s_irwxo_exactly :
    check_faccessat_row (faccessat_in [97] 16) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 16) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 32) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 32) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 15) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 15) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 2147483647) (mkEffect (errno_ret EINVAL) [] [])
        fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 2147483647) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 4294967295) (mkEffect (errno_ret EINVAL) [] [])
        fa_model = CheckOk fa_model []
    ∧ check_faccessat_row (faccessat_in [97] 4294967295) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 16 0) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 2147483647 0) (eff_ret 0 2) fa_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The flag mask is the three accepted bits exactly: `flags & ~(AT_EACCESS |
AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH)` (fs/open.c:478-479, Linux v6.18.46)
refuses bit 0, AT_NO_AUTOMOUNT (2048), AT_STATX_FORCE_SYNC (8192), the sign
bit, 0x7fffffff, every bit below AT_EMPTY_PATH at once (4095) and
AT_EACCESS|1, each with no ledger and 0 refused; the three accepted bits
together (4864) pass the test and are declined for AT_EMPTY_PATH (:483-484),
not refused.  The sections above pinned the mask by AT_SYMLINK_FOLLOW and the
sign bit only.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem flags_mask_is_the_three_accepts_exactly :
    check_faccessat2_row (faccessat2_in [97] 0 1) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 1) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 2048) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 2048) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 8192) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 8192) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 2147483648) (mkEffect (errno_ret EINVAL) [] [])
        fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 2147483648) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 2147483647) (mkEffect (errno_ret EINVAL) [] [])
        fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 2147483647) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 4095) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 4095) (eff_ret 0 2) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + 1)))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckOk fa_model []
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + 1))) (eff_ret 0 2)
        fa_model = CheckReject
    ∧ check_faccessat2_row
        (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW + AT_EMPTY_PATH)))
        (eff_ret 0 2) fa_model = CheckUnmodeled
    ∧ check_faccessat2_row
        (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW + AT_EMPTY_PATH)))
        (mkEffect (errno_ret EINVAL) [] []) fa_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The pre-copy -ENOMEM, refused without its ledger: `__getname` failing in
`getname_flags` (fs/namei.c:146-148, Linux v6.18.46) and `access_override_creds`
(fs/open.c:418-465) failing where `do_faccessat` calls it (fs/open.c:486-489),
before `user_path_at` at :493, both return -ENOMEM having read no byte of the
pathname; the model records the ledger on every arm past the two -EINVALs, so
the bare answer is refused on a held name, an absent one, ".", an unmapped
pathname and through 439 — the narrowing `faccessat_body_spec`'s docstring
records, pinned here from the refusing side.  A bare -EACCES is refused too:
`may_lookup` runs after the fetch, so its answer always carries the ledger.
kernel: fs/open.c:do_faccessat,access_override_creds; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem bare_enomem_before_the_fetch_is_refused :
    check_faccessat_row (faccessat_in [97] 0) (mkEffect (errno_ret ENOMEM) [] []) fa_model
      = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (mkEffect (errno_ret ENOMEM) [] []) absent_model
      = CheckReject
    ∧ check_faccessat_row (faccessat_in [97] 0) (mkEffect (errno_ret EACCES) [] []) fa_model
      = CheckReject
    ∧ check_faccessat_row (faccessat_in [46] 0) (mkEffect (errno_ret ENOMEM) [] []) absent_model
      = CheckReject
    ∧ check_faccessat_row (fa_unmapped_in 0) (mkEffect (errno_ret ENOMEM) [] []) absent_model
      = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS))
        (mkEffect (errno_ret ENOMEM) [] []) fa_model = CheckReject
    ∧ check_faccessat2_row (faccessat2_in [97] 0 0) (mkEffect (errno_ret ENOMEM) [] []) fa_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The 4095-byte pathname: `getname_flags` (fs/namei.c:207-210, Linux
v6.18.46) accepts it — `len` is 4095, below PATH_MAX — with a 4096-byte
ledger, and the filesystem then refuses the one 4095-byte component with
-ENAMETOOLONG (`simple_lookup`, fs/libfs.c:71-72; `ext4_lookup`,
fs/ext4/namei.c:1768-1769), which the NAME_MAX decline declines rather than
picks.  A reader whose window shrank to 4095 would turn this input into the
fetch's -ENAMETOOLONG and accept it, the kernel's errno by coincidence, while
refusing the -EACCES below.
kernel: fs/namei.c:getname_flags,path_init; fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup@v6.18.46 -/
theorem path_max_minus_one_declines_enametoolong :
    check_faccessat_row fa_path_max_minus_one_in (eff_errno ENAMETOOLONG 4096) absent_model
      = CheckUnmodeled :=
  rfl

set_option maxRecDepth 100000 in
/-- ...and `may_lookup`'s -EACCES (fs/namei.c:1852-1874, Linux v6.18.46) in
its place is declined too, as is 0.
kernel: fs/namei.c:getname_flags,may_lookup,path_init; fs/open.c:do_faccessat@v6.18.46 -/
theorem path_max_minus_one_declines_eacces_and_success :
    check_faccessat_row fa_path_max_minus_one_in (eff_errno EACCES 4096) absent_model
      = CheckUnmodeled
    ∧ check_faccessat_row fa_path_max_minus_one_in (eff_ret 0 4096) absent_model
      = CheckUnmodeled :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- ...and the witness declines it as well.
kernel: fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem path_max_minus_one_witness_is_unmodeled :
    faccessat_witness_row fa_path_max_minus_one_in absent_model = Unmodeled :=
  rfl

/-! # close (57)

Pins over `Checks.Sys.Fs.Open.check_close`, the twin of the close half of
`Checks/Sys/Fs/Open.v`, and over `close_witness`.  Rocq keeps no worked
case stated against `check_close`: its two examples that close a
descriptor, `devnull_open_write_read_close` and `urandom_open_read_close`
(`Checks/Cases/Fs/Open.v`), run whole programs through `check_syscall`,
and the close legs of both are restated here on the fixtures the spec
pins built for them.  The other fixtures are the spec pins' close ones
(`Checks/Cases/Fs/Open.lean`, part two) — `close_model`, one descriptor
of every kind with 10 closed, and `after_close_N`, the same table without
descriptor N — so that spec and checker are pinned on the same tables.

WHAT A CHECKER PIN ADDS to the spec's `iff`: a `CheckOk` names the model
the checker built, so the equality fixes the table it hands back and no
"keeps the neighbour" refutation is needed beside it; and a `CheckReject`
is a lie offered from outside, the kernel's answer the lemmas of the
checker's file cannot see.  The lies offered here are the ones `close`
could tell if it were another syscall: 0 on a closed number, -EBADF on a
held one, the -EINVAL of a signed reading of the argument, the -ENOTSOCK
and -EISDIR of the calls that DO test the kind, the -EINTR the entry
point rewrites a restart code to (fs/open.c:1594-1599, Linux v6.18.46)
and the -EIO a flush could carry, neither of which `close_spec` admits
for the reasons its docstring gives, and a ledger — a write, a copy-in, a
zero-fill, an unmap, a copy — beside a return that touches no user
memory.  Errnos the cited functions spell are by name, the rest by
numeral: 22 (-EINVAL), 21 (-EISDIR), 5 (-EIO), and -ENOTSOCK by name
only where the probe that injected it is the evidence.

The dispatcher-shaped rows apply `check_close` as `close_arm`
(`Sys/Registry/Fs/Open.lean`) applies the spec — the descriptor through
`fd32`.  `CloseThroughTheTable`, at the end of this file, states the two
pins of the row section below, `row_57_closes_the_fd` and
`row_57_fd_truncates_to_32_bits`, again through `check_syscall`, as the
openat pins are; the two probe pins stated on the row,
`dir_close_is_zero` and `socket_close_is_not_enotsock`, stay on it. -/

/-- `check_close` as `close_arm` (`Sys/Registry/Fs/Open.lean`) applies the
spec: the descriptor through `fd32`, as it arrives in a0. -/
def check_close_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_close (fd32 (in_arg i 0)) eff m

/-- `close_witness` applied the same way. -/
def close_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  close_witness (fd32 (in_arg i 0)) m

/-- `close(fd)` as syscall 57 arrives: the descriptor in a0, the other
registers clear, nothing mapped. -/
def close_call (fd : word) : SyscallInput :=
  SyscallInput.mkInput 57 [fd, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- 0 in a0 beside a ledger `close` never produces: a zero-fill, an
unmap, a copy. -/
def close_zero_with_zeros : SyscallEffect := SyscallEffect.mkEffectU 0 [] [(4096, 8)] [] [] []
def close_zero_with_unmaps : SyscallEffect := SyscallEffect.mkEffectU 0 [] [] [(4096, 4096)] [] []
def close_zero_with_copies : SyscallEffect :=
  SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 4096 8192 8] []

/-! ## A closed number -/

/-- The NULL `file_close_fd` returns for an empty slot is `-EBADF` with
nothing changed (fs/open.c:1579-1581): the checker accepts that effect
over the model it was given, and refuses the 0 a kernel that skipped the
test would return, the -EINVAL (22) of a syscall with a second argument
to reject, and the errno beside a write.
kernel: fs/open.c:close; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem closed_number_is_ebadf :
    check_close 10 (mkEffect (errno_ret EBADF) [] []) close_model = CheckOk close_model []
    ∧ check_close 10 (mkEffect 0 [] []) close_model = CheckReject
    ∧ check_close 10 (mkEffect (errno_ret 22) [] []) close_model = CheckReject
    ∧ check_close 10 (mkEffect (errno_ret EBADF) [(4096, [0])] []) close_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `close(-1)`: the register narrows to 4294967295, at or past every
`max_fds` — the test at fs/file.c:699-700, against a table `alloc_fdtable`
(fs/file.c:194-195, Linux v6.18.46) clamps to `sysctl_nr_open`, which the
`nr_open` sysctl entry (fs/file_table.c:150-158) holds at or below its
`.extra2`, `sysctl_nr_open_max` (fs/file.c:100-101), `INT_MAX` rounded
down to a multiple of `BITS_PER_LONG`, through `proc_douintvec_minmax`
(kernel/sysctl.c); and independently
of the sysctl, `alloc_fdtable` refuses -EMFILE above `INT_MAX / sizeof(struct
file *)` (fs/file.c:212-213) before setting `max_fds` (:218), while the
embedded table is `NR_OPEN_DEFAULT` slots (fs/file.c:401, :534) — the same
-EBADF as an empty slot's; a signed reading's -EINVAL (22) is refused, the
argument being `unsigned int`.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked,alloc_fdtable@v6.18.46 -/
theorem close_of_minus_one_is_ebadf :
    check_close 4294967295 (mkEffect (errno_ret EBADF) [] []) close_model = CheckOk close_model []
    ∧ check_close 4294967295 (mkEffect (errno_ret 22) [] []) close_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- 2^31 and 2^31 - 1, the numbers a signed reading flips on and stops
at: both -EBADF by the one bound at fs/file.c:699-700, since no table
reaches `INT_MAX` — `alloc_fdtable` stops at `INT_MAX / sizeof(struct file
*)` (fs/file.c:212-213, Linux v6.18.46), and the sysctl ceiling
`sysctl_nr_open_max` (fs/file.c:100-101, bound through fs/file_table.c:150-158)
rounds `INT_MAX` down to a multiple of `BITS_PER_LONG` — and both refused
a 0.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked,alloc_fdtable@v6.18.46 -/
theorem close_of_2_pow_31_and_int_max_are_ebadf :
    check_close 2147483648 (mkEffect (errno_ret EBADF) [] []) close_model = CheckOk close_model []
    ∧ check_close 2147483648 (mkEffect 0 [] []) close_model = CheckReject
    ∧ check_close 2147483647 (mkEffect (errno_ret EBADF) [] []) close_model = CheckOk close_model []
    ∧ check_close 2147483647 (mkEffect 0 [] []) close_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## A held descriptor, of every kind

`close` never looks at the kind: `file_close_fd_locked` clears whichever
slot is held (fs/file.c:703-706, Linux v6.18.46) and the entry point
returns 0 unless the flush objected (fs/open.c:1591-1592).  So one pin
per kind, each with the -EBADF a kernel that had lost the descriptor
would answer refused, and where another syscall tests that kind, its
errno refused too. -/

/-- A channel closes to 0; `after_close_0` is `close_model` without 0.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem channel_close_is_zero :
    check_close 0 (mkEffect 0 [] []) close_model = CheckOk after_close_0 []
    ∧ check_close 0 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- stderr the same, with -EBADF refused.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem stderr_close_is_zero :
    check_close 2 (mkEffect 0 [] []) close_model = CheckOk after_close_2 []
    ∧ check_close 2 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- A read-only file closes to 0.  Its entry alone leaves the table
(`fd_remove` is the one slot `file_close_fd_locked` clears,
fs/file.c:703-706) and the image behind it stays: `after_close_3` is
built on `close_fs`.  Refused beside -EBADF: the -EINTR a restart code is
rewritten to (fs/open.c:1594-1599) and the -EIO (5) a flush could carry
(:1583, :1601) — neither is in `close_spec`, whose docstring in
`Sys/Fs/Open.lean` says why, and the checker follows the spec.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem file_close_is_zero :
    check_close 3 (mkEffect 0 [] []) close_model = CheckOk after_close_3 []
    ∧ check_close 3 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject
    ∧ check_close 3 (mkEffect (errno_ret EINTR) [] []) close_model = CheckReject
    ∧ check_close 3 (mkEffect (errno_ret 5) [] []) close_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A write-only file closes to 0 and its image is kept: `after_close_4`
holds `close_fs` whole.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem write_file_close_is_zero :
    check_close 4 (mkEffect 0 [] []) close_model = CheckOk after_close_4 []
    ∧ check_close 4 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- Success is inert on user memory: `close` takes an int and returns
one, and nothing under it copies to user space, so a write, a copy-in, a
zero-fill, an unmap or a copy beside the 0 is refused.  (An event beside
it is not an effect the checker is offered: `check_ret_only` answers with
no events, which the `CheckOk … []` of every pin above fixes.)
kernel: fs/open.c:close@v6.18.46 -/
theorem close_ledger_is_empty :
    check_close 4 (mkEffect 0 [(4096, [0])] []) close_model = CheckReject
    ∧ check_close 4 (with_copyins [(4096, 1)] (mkEffect 0 [] [])) close_model = CheckReject
    ∧ check_close 4 close_zero_with_zeros close_model = CheckReject
    ∧ check_close 4 close_zero_with_unmaps close_model = CheckReject
    ∧ check_close 4 close_zero_with_copies close_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A directory descriptor closes to 0; dirfd_spec's `close` case is this
call on a real ".", so the pin is stated through the row, as syscall 57,
where the probe's recorded return is read against it.
probe: testing/syscall-check/tests/dirfd_spec.c#conform -- close -/
theorem dir_close_is_zero :
    check_close_row (close_call 5) (mkEffect 0 [] []) close_model = CheckOk after_close_5 [] :=
  rfl

/-- -EISDIR (21) is the errno of the calls that refuse a directory;
`close` has no such test, and a kernel answering it is refused, as is
-EBADF.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem dir_close_is_not_eisdir :
    check_close 5 (mkEffect (errno_ret 21) [] []) close_model = CheckReject
    ∧ check_close 5 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- A socket closes to 0; `after_close_6` is `close_model` without 6.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem socket_close_is_zero :
    check_close 6 (mkEffect 0 [] []) close_model = CheckOk after_close_6 []
    ∧ check_close 6 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- -ENOTSOCK is the socket calls' errno on a descriptor that is not a
socket; `close` has no such test in either direction, and the mutated
run that claims it is refused for every model and event list it could
name — the shape in which the probe's `reject` verdict is stated.  What
this leaves open,
`CheckUnmodeled`, is closed for every input by `check_close_never_declines`
below, so the two together are the `CheckReject`.  Stated through the row,
as syscall 57, so the probe's recorded return is read against it.
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate close#1:ret=-ENOTSOCK -- rw -/
theorem socket_close_is_not_enotsock (m' : Model) (evs : List event) :
    check_close_row (close_call 6) (mkEffect (errno_ret ENOTSOCK) [] []) close_model
      ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- Either end of a pipe closes to 0 and the pipe's bytes stay: the
descriptor leaves the table, and `close_pipes` is `after_close_7`'s and
`after_close_8`'s alike; closing the second end after the first
(`after_close_7_8`) keeps the buffer too.  What the last reference's
release does to the buffer is the spec twin's account and the spec
pins'.  -EBADF is refused on either end, and on the last end standing:
`file_close_fd_locked` reads the slot, not the pipe's reference count.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem pipe_close_is_zero :
    check_close 7 (mkEffect 0 [] []) close_model = CheckOk after_close_7 []
    ∧ check_close 8 (mkEffect 0 [] []) close_model = CheckOk after_close_8 []
    ∧ check_close 8 (mkEffect 0 [] []) after_close_7 = CheckOk after_close_7_8 []
    ∧ check_close 7 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject
    ∧ check_close 8 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject
    ∧ check_close 8 (mkEffect (errno_ret EBADF) [] []) after_close_7 = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- /dev/null closes to 0; `after_close_9` is `close_model` without 9.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem devnull_close_is_zero :
    check_close 9 (mkEffect 0 [] []) close_model = CheckOk after_close_9 []
    ∧ check_close 9 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- Rocq's `devnull_open_write_read_close`, close leg, on the checker:
the /dev/null open minted at 3 (write-only) is closed, and the model the
checker hands back is the one the open started from — on which this
file's `create_absent_mints_the_key` (the spec pins'
`plain_create_mints_the_key`) mints 3 again, since `__put_unused_fd`
(fs/file.c:630-631, Linux v6.18.46) lowered `next_fd` to the freed
number.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked,__put_unused_fd@v6.18.46 -/
theorem devnull_close_restores_the_model :
    check_close 3 (mkEffect 0 [] []) (fixture_of (fds := (3, .FdDevNull false true) :: init_fds))
      = CheckOk absent_model [] :=
  rfl

/-- /dev/urandom closes to 0 and leaves the table; the -EBADF of a model
that treated a descriptor with no offset as no descriptor is refused.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem urandom_close_is_zero :
    check_close 11 (mkEffect 0 [] []) close_model = CheckOk after_close_11 []
    ∧ check_close 11 (mkEffect (errno_ret EBADF) [] []) close_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- Rocq's `urandom_open_read_close`, close leg, on the checker: the
reader minted at 3 is closed and the model is the one the open started
from, with the declared stream — the run's, not the descriptor's —
coming through untouched, whatever it holds: `file_close_fd_locked`
touches the fd table alone (fs/file.c:705).
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked,__put_unused_fd@v6.18.46 -/
theorem urandom_close_restores_the_model (s : InputStream) :
    check_close 3 (mkEffect 0 [] [])
        (with_urandom s (fixture_of (fds := (3, .FdUrandom) :: init_fds)))
      = CheckOk (with_urandom s absent_model) [] :=
  rfl

/-- A second close of the same number is -EBADF with the table as it was,
and a 0 is refused: the slot was cleared by the first (fs/file.c:705), so
`file_close_fd` finds NULL there (fs/open.c:1579-1581).
kernel: fs/open.c:close; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem second_close_is_ebadf :
    check_close 3 (mkEffect (errno_ret EBADF) [] []) after_close_3 = CheckOk after_close_3 []
    ∧ check_close 3 (mkEffect 0 [] []) after_close_3 = CheckReject :=
  ⟨rfl, rfl⟩

/-! ## The row: syscall 57 and its 32-bit fd

`SYSCALL_DEFINE1(close, unsigned int, fd)` (fs/open.c:1574, Linux
v6.18.46): the fd is `unsigned int`, narrowed by `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88, Linux v6.18.46) through
`__SC_CAST` (include/linux/syscalls.h:132, Linux v6.18.46), which the
row's `fd32` mirrors. -/

/-- Through the row, fd 3 closes the file and the closed 10 is -EBADF;
only a0 is read, so garbage in the other five registers — the flags a
`close_range` would read — changes nothing.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem row_57_closes_the_fd :
    check_close_row (close_call 3) (mkEffect 0 [] []) close_model = CheckOk after_close_3 []
    ∧ check_close_row (close_call 10) (mkEffect (errno_ret EBADF) [] []) close_model
        = CheckOk close_model []
    ∧ check_close_row (SyscallInput.mkInput 57 [3, 7, 7, 7, 7, 7] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) close_model = CheckOk after_close_3 [] :=
  ⟨rfl, rfl, rfl⟩

/-- `close(2^32 + 3)` IS `close(3)`: the register's high half is dropped
by the `unsigned int` cast, so the call aliases onto the file at 3 and
closes it, and the -EBADF a model reading all 64 bits would answer is
refused; `close(2^32 + 10)` is the closed 10's -EBADF, and `close(2^32)`
closes 0.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:close@v6.18.46 -/
theorem row_57_fd_truncates_to_32_bits :
    check_close_row (close_call (Z_to_bv 64 (2 ^ 32 + 3))) (mkEffect 0 [] []) close_model
        = CheckOk after_close_3 []
    ∧ check_close_row (close_call (Z_to_bv 64 (2 ^ 32 + 3))) (mkEffect (errno_ret EBADF) [] [])
        close_model = CheckReject
    ∧ check_close_row (close_call (Z_to_bv 64 (2 ^ 32 + 10))) (mkEffect (errno_ret EBADF) [] [])
        close_model = CheckOk close_model []
    ∧ check_close_row (close_call (Z_to_bv 64 (2 ^ 32))) (mkEffect 0 [] []) close_model
        = CheckOk after_close_0 [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Never a decline, and the witness -/

/-- The checker never declines, for any descriptor, effect or model: both
arms are `check_ret_only`, which answers `CheckOk` or `CheckReject`.
This is what Rocq's two vacuous `_unmodeled` lemmas rest on, stated on
the checker's own terms; `close` has no arm the model leaves open.
kernel: fs/open.c:close@v6.18.46 -/
theorem check_close_never_declines (fd : word) (eff : SyscallEffect) (m : Model) :
    check_close fd eff m ≠ CheckUnmodeled := by
  unfold check_close
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact check_ret_only_no_unmodeled _ _ _ _
  | some e => exact check_ret_only_no_unmodeled _ _ _ _

/-- …nor does the witness: on every table it names the errno or the zero.
kernel: fs/open.c:close@v6.18.46 -/
theorem close_witness_never_declines (fd : word) (m : Model) :
    close_witness fd m ≠ Unmodeled := by
  unfold close_witness
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => intro h; simp only [ret_outcome, reduceCtorEq] at h
  | some e => intro h; simp only [ret_outcome, reduceCtorEq] at h

/-- The witness names the checker's answers: -EBADF with the model
unchanged on the closed number, 0 over the shrunk table on the held one,
and through the row the aliased 2^32 + 3 closes 3.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem close_witness_names_the_answer :
    close_witness 10 close_model = Ok (mkEffect (errno_ret EBADF) [] []) close_model []
    ∧ close_witness 3 close_model = Ok (mkEffect 0 [] []) after_close_3 []
    ∧ close_witness_row (close_call (Z_to_bv 64 (2 ^ 32 + 3))) close_model
        = Ok (mkEffect 0 [] []) after_close_3 [] :=
  ⟨rfl, rfl, rfl⟩

/-- …and whatever it names, the checker accepts, on every table and for
every descriptor: `close_witness_ok` puts the outcome in the spec and
`check_close_complete_ok` carries it to the checker.
model: `close_witness` fed to `check_close`, no spec named -/
theorem close_witness_is_accepted (fd : word) (m m' : Model) (eff : SyscallEffect)
    (evs : List event) (i : SyscallInput) (h : close_witness fd m = Ok eff m' evs) :
    check_close fd eff m = CheckOk m' evs := by
  have hw := close_witness_ok fd i m
  rw [h] at hw
  exact check_close_complete_ok fd eff m m' evs i hw


/-! # ftruncate (46)

Pins over `Checks.Sys.Fs.Open.check_ftruncate`, the twin of the ftruncate
half of `Checks/Sys/Fs/Open.v`, and over `ftruncate_witness`, the twin of
the ftruncate half of `Checks/Witness/Fs/Open.v`.  Rocq states five
ftruncate claims against the checker, each over `check_syscall`.  Three
are worked cases of their own: `ftruncate_on_a_dangling_fd_is_unmodeled`
(`Checks/Cases/Fs/Open.v`), restated below on the row and through
`check_syscall` itself in the last part; and
`ftruncate_on_a_pipe_end_is_einval` and
`ftruncate_on_a_pipe_write_end_rejects_success` (`Checks/Cases/Fs/Pipe.v`),
restated in the last part over that file's `pipe_model`, since a pin
through the table needs the arm this ticket registers.  The other two are
the 46 legs of `devnull_dispatch_sites` and `urandom_dispatch_sites`
(`Checks/Cases/Fs/Open.v`), restated on the checker in
`ftruncate_device_fixtures_are_einval` and through `check_syscall` in the
last part.  The fixture is the spec pins' (`Checks/Cases/Fs/Open.lean`,
part three): `ft_model`, whose table `ft_fds` leaves 10 closed and holds
two write-only files to resize (4 over "yz{" at offset 9, 13 over an empty
file at offset 4) and a write-only descriptor on a path the file system
does not hold (12), so that spec and checker are pinned on the same table.
The `probe:` lines of this part cite
`testing/syscall-check/tests/ftruncate_spec.c`; an `ftruncate#n` there is
the n-th ftruncate call of the run its mode names.  The spec pins'
part-three header lists those calls for `kinds` and `order`, and each
`data` and `zero` pin that cites one names its call in its docstring.
Line numbers are Linux v6.18.46 (commit 1f99e9ab748f).

WHAT A CHECKER PIN ADDS to the spec's `iff`, as in the close pins: a
`CheckOk` names the model the checker built, and the models below spell
the file system whole and keep `ft_fds` as the table, so the one equality
fixes the new file, its neighbours and the descriptor's offset at once;
and a `CheckReject` is a lie offered from outside.  The lies offered here
are the ones a wrong ORDER tells — the -EBADF of a kernel that looked the
number up before testing the length (`do_sys_ftruncate`, fs/open.c:202-211,
Linux v6.18.46, tests `length < 0` at :204-205 before `CLASS(fd, f)(fd)`
at :206), and the -EINVAL of one that tested the kind before the empty
slot (:207-208) — the 0 of a kernel that skipped `do_ftruncate`'s
kind-and-mode test (`!S_ISREG || !FMODE_WRITE`, fs/open.c:175-176, Linux
v6.18.46), the -ESPIPE, -EISDIR and -EBADF of calls that DO test those
kinds, the new length returned as `write` returns a count, and a ledger
beside a call that takes two integers.  Errnos are by name where
`State/Errno.lean` defines one and the pin's evidence spells it — for a
`kernel:` pin the functions it cites, read together; for a `conform` pin
the `expect`s of the mode it names; for a `reject` pin the errno its case
injects — and by numeral otherwise: 21 (-EISDIR) and 29 (-ESPIPE) in
positive `kernel:` pins whose cited functions do not spell them, and 27
(-EFBIG), which `inode_newsize_ok` spells and `State/Errno.lean` lacks.

THE BOUND.  Past the sign test, `check_ftruncate` declines on a held
write-only file where `modeled_truncate_gap` does, and the spec pins say
why that decline is the model's and not a kernel test.  The pins past the
bound are closed by evaluating the real checker (`rfl`, or a
`have … : CheckUnmodeled = … := h` and `cases`), which declines before
any zero-fill is built, and `check_ftruncate_declines_past_the_bound` states
that decline for every held write-only file and every non-negative length
past it.  The pins AT the bound are closed through the universal
`check_ftruncate_judged_within_the_bound` and the spec pins' `decide`d
guard values, and the shrink over any length through the same pin and the
spec pins' universal `shrink_is_modeled_for_every_length`, so that no pin
here evaluates a 131072-byte `replicate` —
the spec pins' bound section records the stack overflow that costs under a
mutated gate.

The rows apply `check_ftruncate` as `ftruncate_arm`
(`Sys/Registry/Fs/Open.lean`) applies the spec — the descriptor through
`fd32`, the length as the whole of a1 — which is how `arm_ftruncate`
(`Checks/Arms/Fs/Open.lean`) applies the checker.  The last part pins
that the real table answers a call to 46 as the row does
(`check_syscall_at_46_is_the_row`), so each row pin below is a pin on
`check_syscall` as well. -/

/-- `check_ftruncate` as `ftruncate_arm` (`Sys/Registry/Fs/Open.lean`)
applies the spec: the descriptor through `fd32`, the length as a1 whole. -/
def check_ftruncate_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_ftruncate (fd32 (in_arg i 0)) (in_arg i 1) eff m

/-- `ftruncate_witness` applied the same way. -/
def ftruncate_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  ftruncate_witness (fd32 (in_arg i 0)) (in_arg i 1) m

/-- `ftruncate(fd, len)` as syscall 46 arrives: the descriptor in a0, the
length in a1, the other registers clear, nothing mapped. -/
def ftruncate_call (fd len : word) : SyscallInput :=
  SyscallInput.mkInput 46 [fd, len, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- `ft_model` with the file behind 4 holding `data` and nothing else
changed: the table is `ft_fds`, offset 9 on 4 included, and the other two
files are as they were. -/
def ft_with_4 (data : List byte) : Model :=
  fixture_of (fds := ft_fds) (pipes := ft_pipes)
    (fs := [([102], [120]), ([103], data), ([105], [])])

/-- `ft_model` with the file behind 13 holding `data`, offset 4 on 13
kept. -/
def ft_with_13 (data : List byte) : Model :=
  fixture_of (fds := ft_fds) (pipes := ft_pipes)
    (fs := [([102], [120]), ([103], [121, 122, 123]), ([105], data)])

/-! ## The length, before the descriptor -/

/-- A negative length is -EINVAL whatever the descriptor is, since
`do_sys_ftruncate` tests it (fs/open.c:204-205) before the descriptor is
resolved (:206): on the closed 10, on the 4294967295 that `ftruncate(-1,
…)` narrows to, on the writable 4, on the directory, and on the dangling
12, where a checker that looked the descriptor up first would decline
instead.  The model is handed back unchanged each time; refused are the
-EBADF an fd-first checker answers on the closed numbers, and a 0 on the
writable 4 — as `CheckReject`, not a decline, which also kills a checker
reading the length unsigned: to it 2^64 - 1 is a grow past
`modeled_truncate_gap`, and it would decline.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem ftruncate_negative_length_is_einval_first :
    check_ftruncate 10 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate 10 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EBADF) [] []) ft_model
        = CheckReject
    ∧ check_ftruncate 4294967295 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EINVAL) [] [])
        ft_model = CheckOk ft_model []
    ∧ check_ftruncate 4294967295 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EBADF) [] [])
        ft_model = CheckReject
    ∧ check_ftruncate 4 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate 4 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 5 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate 12 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 2^63 is NEGATIVE as an `off_t`: -EINVAL on the writable file, and a
0 there is refused rather than declined: a model reading the register
unsigned would take it for a huge grow and decline (the spec pins'
`two_pow_63_is_not_a_huge_grow`), which `= CheckReject` refuses too.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem ftruncate_two_pow_63_is_negative :
    check_ftruncate 13 (Z_to_bv 64 (2 ^ 63)) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate 13 (Z_to_bv 64 (2 ^ 63)) (mkEffect 0 [] []) ft_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- `ftruncate(-1, -1)` through the row, the probe's first `order` call:
the all-ones a0 narrows to 4294967295, the all-ones a1 stays negative, and
the answer is -EINVAL with the model as it was.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- order -/
theorem ftruncate_row_minus_one_minus_one_is_einval :
    check_ftruncate_row (ftruncate_call (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model [] :=
  rfl

/-- …and the -EBADF of an fd-first kernel there is refused for every model
and event list, the shape in which the probe's `reject` verdict is
stated; `check_ftruncate_declines_only_on_a_held_writable_file` below
closes the `CheckUnmodeled` this leaves open.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#1:ret=-EBADF -- order -/
theorem ftruncate_row_minus_one_minus_one_is_not_ebadf (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EBADF) [] []) ft_model ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- `ftruncate(<closed>, -1)`, the probe's second `order` call, on the
closed 10: -EBADF is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#2:ret=-EBADF -- order -/
theorem ftruncate_negative_length_on_a_closed_fd_is_not_ebadf (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 10 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EBADF) [] []) ft_model ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- With a length that passes, the descriptor IS consulted: the probe's
third `order` call, `ftruncate(<closed>, 0)`, answered -EINVAL by a kernel
that tested the kind before the empty slot, is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#3:ret=-EINVAL -- order -/
theorem ftruncate_closed_fd_with_a_fine_length_is_not_einval (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 10 0) (mkEffect (errno_ret EINVAL) [] []) ft_model
      ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- `ftruncate(wfd, 2^63)`, the probe's `zero` call with its length
rewritten: the 0 the kernel returned for the length it was really given
is refused, the rewritten one being negative.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#1:arg1=0x8000000000000000 -- zero -/
theorem ftruncate_row_two_pow_63_success_rejected (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 13 (Z_to_bv 64 (2 ^ 63))) (mkEffect 0 [] []) ft_model
      ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-! ## A closed number -/

/-- A length that passes, on a number with no file behind it, is -EBADF
with the model unchanged (fs/open.c:207-208, Linux v6.18.46, whose test
is `fd_empty` at include/linux/file.h:45-48), for a small
length and for 2^40 alike, and on 4294967295 as well; the 0
of a kernel that skipped the test, the -EINVAL of one that tested the
kind first, and the -EBADF beside a write are refused.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem ftruncate_closed_number_is_ebadf :
    check_ftruncate 10 0 (mkEffect (errno_ret EBADF) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 10 (Z_to_bv 64 (2 ^ 40)) (mkEffect (errno_ret EBADF) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate 4294967295 0 (mkEffect (errno_ret EBADF) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate 10 0 (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 10 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckReject
    ∧ check_ftruncate 10 0 (mkEffect (errno_ret EBADF) [(4096, [0])] []) ft_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The probe's closed-number calls through the row: `ftruncate(<closed>,
0)` and `ftruncate(<closed>, 2^40)` are -EBADF.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- order -/
theorem ftruncate_row_closed_number_is_ebadf :
    check_ftruncate_row (ftruncate_call 10 0) (mkEffect (errno_ret EBADF) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate_row (ftruncate_call 10 (Z_to_bv 64 (2 ^ 40)))
        (mkEffect (errno_ret EBADF) [] []) ft_model = CheckOk ft_model [] :=
  ⟨rfl, rfl⟩

/-- The `kinds` mode's closed number, its eighth call: -EINVAL there is
refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#8:ret=-EINVAL -- kinds -/
theorem ftruncate_closed_number_is_not_einval (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 10 0) (mkEffect (errno_ret EINVAL) [] []) ft_model
      ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-! ## The kinds `do_ftruncate` refuses

A descriptor that is not a writable regular file fails the test at
fs/open.c:175-176 (Linux v6.18.46), `!S_ISREG(inode->i_mode) ||
!(file->f_mode & FMODE_WRITE)` — of those the Lean `FdEntry` holds only
the write-only `FdFileW`, and the channels fail it by the spec's premise
that none is a writable regular file — and answers -EINVAL with nothing
changed; the length is not read on that path, so 2^40 answers as 0
does. -/

/-- The three channels are -EINVAL, stderr at 2^40 too; the 0 on stdin
and on stdout, stdout's at 2^40 too, and the -EBADF and the -ESPIPE (29)
on stderr, are refused.  `do_ftruncate`'s test (fs/open.c:175-176, Linux v6.18.46) gives
-EINVAL only to an object that is not a writable regular file.  That a
channel is not one is the spec's premise (`ftruncate_spec`: "no channel
the model is handed is a writable regular file").  It holds of the
tracer's pipes and fails for `prog > out.txt`, where fd 1 is a writable
regular file, the kernel can answer 0, and this pin refuses that 0 at
lengths 0 and 2^40.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem ftruncate_channels_are_einval :
    check_ftruncate 0 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 1 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 2 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 2 (Z_to_bv 64 (2 ^ 40)) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate 0 0 (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 1 0 (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 1 (Z_to_bv 64 (2 ^ 40)) (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 2 0 (mkEffect (errno_ret EBADF) [] []) ft_model = CheckReject
    ∧ check_ftruncate 2 0 (mkEffect (errno_ret 29) [] []) ft_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- stdin, the `kinds` mode's first call: the 0 of a kernel that truncated
it is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#1:ret=0 -- kinds -/
theorem ftruncate_stdin_success_rejected (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 0 0) (mkEffect 0 [] []) ft_model ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- stdout, the second call, the same.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#2:ret=0 -- kinds -/
theorem ftruncate_stdout_success_rejected (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 1 0) (mkEffect 0 [] []) ft_model ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- stderr, the third call, the same.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#3:ret=0 -- kinds -/
theorem ftruncate_stderr_success_rejected (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 2 0) (mkEffect 0 [] []) ft_model ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- …and not the -ESPIPE `lseek` answers on a pipe or terminal: ftruncate
has no such test.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#3:ret=-ESPIPE -- kinds -/
theorem ftruncate_stderr_is_not_espipe (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 2 0) (mkEffect (errno_ret ESPIPE) [] []) ft_model
      ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- A directory is -EINVAL, at 0 and at 2^40: `S_ISREG` fails.  Refused:
the 0, and the -EISDIR (21) of the calls that refuse a directory by name.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem ftruncate_directory_is_einval :
    check_ftruncate 5 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 5 (Z_to_bv 64 (2 ^ 40)) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate 5 0 (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 5 0 (mkEffect (errno_ret 21) [] []) ft_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The directory, the `kinds` mode's fifth call: -EISDIR is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#5:ret=-EISDIR -- kinds -/
theorem ftruncate_directory_is_not_eisdir (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 5 0) (mkEffect (errno_ret EISDIR) [] []) ft_model
      ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- A read-only regular file is -EINVAL — `FMODE_WRITE` fails — and the
file behind it is untouched: the model handed back is `ft_model`.  The 0
of a kernel that truncated through a read-only descriptor, and the
-EBADF of one that took the missing write mode for a bad descriptor, are
refused.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem ftruncate_readonly_file_is_einval :
    check_ftruncate 3 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 3 0 (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 3 0 (mkEffect (errno_ret EBADF) [] []) ft_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- The read-only file, the `kinds` mode's seventh call: -EBADF is
refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#7:ret=-EBADF -- kinds -/
theorem ftruncate_readonly_file_is_not_ebadf (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 3 0) (mkEffect (errno_ret EBADF) [] []) ft_model
      ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- The `kinds` mode's own answers through the row: stdin, stdout and
stderr at 0, stderr at 2^40 too, the directory at 0 and at 2^40, the
read-only file at 0, all -EINVAL; the number closed after it, -EBADF at 0
and at 2^40.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- kinds -/
theorem ftruncate_row_kinds :
    check_ftruncate_row (ftruncate_call 0 0) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate_row (ftruncate_call 1 0) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate_row (ftruncate_call 2 0) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate_row (ftruncate_call 2 (Z_to_bv 64 (2 ^ 40)))
        (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate_row (ftruncate_call 5 0) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate_row (ftruncate_call 5 (Z_to_bv 64 (2 ^ 40)))
        (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate_row (ftruncate_call 3 0) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate_row (ftruncate_call 10 0) (mkEffect (errno_ret EBADF) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_ftruncate_row (ftruncate_call 10 (Z_to_bv 64 (2 ^ 40)))
        (mkEffect (errno_ret EBADF) [] []) ft_model = CheckOk ft_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The socket, both ends of the pipe, /dev/null read-write and
/dev/urandom are -EINVAL with the model unchanged — the pipe's bytes
included — and each refuses the 0.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem ftruncate_socket_pipe_and_devices_are_einval :
    check_ftruncate 6 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 7 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 8 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 9 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 11 0 (mkEffect (errno_ret EINVAL) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 6 0 (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 7 0 (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 8 0 (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 9 0 (mkEffect 0 [] []) ft_model = CheckReject
    ∧ check_ftruncate 11 0 (mkEffect 0 [] []) ft_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The device tables of Rocq's `devnull_model` and `urandom_model`, whose
`devnull_dispatch_sites` and `urandom_dispatch_sites`
(`Checks/Cases/Fs/Open.v`) each carry a 46 leg — 4 and 3 respectively —
restated here on the checker and through `check_syscall` in the last
part: /dev/null read-only, write-only and read-write, and /dev/urandom,
are each -EINVAL; the write-only /dev/null is a character device, so
`FMODE_WRITE` passing does not save it, and its 0 is refused.
`fs_path_not_regular.c`'s `conform --no-fs-check -- trunc` run records the
write-only /dev/null's -EINVAL on a real kernel; at this head no run
offers the refused 0, and none calls ftruncate on /dev/urandom.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem ftruncate_device_fixtures_are_einval :
    check_ftruncate 3 0 (mkEffect (errno_ret EINVAL) [] []) ft_devnull_model
        = CheckOk ft_devnull_model []
    ∧ check_ftruncate 4 0 (mkEffect (errno_ret EINVAL) [] []) ft_devnull_model
        = CheckOk ft_devnull_model []
    ∧ check_ftruncate 5 0 (mkEffect (errno_ret EINVAL) [] []) ft_devnull_model
        = CheckOk ft_devnull_model []
    ∧ check_ftruncate 4 0 (mkEffect 0 [] []) ft_devnull_model = CheckReject
    ∧ check_ftruncate 3 0 (mkEffect (errno_ret EINVAL) [] []) ft_urandom_model
        = CheckOk ft_urandom_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The write-only file: the size is set, the offset is not

The one arm that changes anything: the file behind the descriptor is set
to exactly the length — the prefix kept, a grow zero-filled — through
`do_truncate` (fs/open.c:39-71, Linux v6.18.46), and the call answers 0.
The descriptor's offset is on no part of that path: `CLASS(fd, f)`
(include/linux/file.h:83, Linux v6.18.46) is over `fdget`, not
`fdget_pos`, so the table the checker hands back is `ft_fds`, the one it
was given. -/

/-- A shrink keeps the prefix: "yz{" to 0 is empty and to 1 is "y", with
offset 9 on 4 kept past the new end.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- data -/
theorem ftruncate_shrink_keeps_the_prefix :
    check_ftruncate 4 0 (mkEffect 0 [] []) ft_model = CheckOk (ft_with_4 []) []
    ∧ check_ftruncate 4 1 (mkEffect 0 [] []) ft_model = CheckOk (ft_with_4 [121]) []
    ∧ check_ftruncate 4 2 (mkEffect 0 [] []) ft_model = CheckOk (ft_with_4 [121, 122]) [] :=
  ⟨rfl, rfl, rfl⟩

/-- The `seeded` case's shape — a three-byte file cut to one — is the
shrink to "y" above, stated through the row.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform --seed-file ft-s=616263 -- seeded -/
theorem ftruncate_row_shrink_to_one :
    check_ftruncate_row (ftruncate_call 4 1) (mkEffect 0 [] []) ft_model
      = CheckOk (ft_with_4 [121]) [] :=
  rfl

/-- The current length is a real 0 and the file is unchanged, so the model
handed back is `ft_model`; so is 0 on the empty file.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- data -/
theorem ftruncate_current_length_is_zero :
    check_ftruncate 4 3 (mkEffect 0 [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate 13 0 (mkEffect 0 [] []) ft_model = CheckOk ft_model [] :=
  ⟨rfl, rfl⟩

/-- A grow zero-fills the tail: "yz{" to five bytes is "yz{" and two
zeros, and the empty file to four is four zeros.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- data -/
theorem ftruncate_grow_zero_fills :
    check_ftruncate 4 5 (mkEffect 0 [] []) ft_model
        = CheckOk (ft_with_4 [121, 122, 123, 0, 0]) []
    ∧ check_ftruncate 13 4 (mkEffect 0 [] []) ft_model = CheckOk (ft_with_13 [0, 0, 0, 0]) [] :=
  ⟨rfl, rfl⟩

/-- The plain `ftruncate(wfd, 0)` of the `zero` mode, through the row.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- zero -/
theorem ftruncate_row_zero_on_the_empty_file :
    check_ftruncate_row (ftruncate_call 13 0) (mkEffect 0 [] []) ft_model = CheckOk ft_model [] :=
  rfl

/-- The offset survives the shrink: for every accepted call, on every
model, the table the checker hands back is the one it was given — the
fact the probe's `offset` mode reads back with `lseek(SEEK_CUR)` after a
shrink.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- offset -/
theorem ftruncate_accepted_keeps_the_table (fd len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_ftruncate fd len eff m = CheckOk m' evs) :
    m_fds m' = m_fds m := by
  unfold m_fds
  rw [check_ftruncate_fd_state_frame fd len eff m m' evs h]

/-- …and past a grow: the empty file at offset 4 grown to six bytes keeps
offset 4 on 13.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- grow-offset -/
theorem ftruncate_grow_keeps_the_offset :
    check_ftruncate 13 6 (mkEffect 0 [] []) ft_model
      = CheckOk (ft_with_13 [0, 0, 0, 0, 0, 0]) [] :=
  rfl

/-- Success is a bare 0, not `write`'s count: the shape of the probe's
third `data` call (it cuts "hello" to 3), here "yz{" cut to 1 answering
1, is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#3:ret=3 -- data -/
theorem ftruncate_shrink_does_not_return_the_length (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 4 1) (mkEffect 1 [] []) ft_model ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- The current length is not -EINVAL: the -EINVALs on this path test the
length's sign, the descriptor's kind and — unreachably, `small` being
cleared at fs/open.c:170-171, Linux v6.18.46 — the length against
`MAX_NON_LFS`, not against the size.  Where the length IS compared with
the size — `inode_newsize_ok` (fs/attr.c:248) and `shmem_setattr`
(mm/shmem.c:1322-1336), Linux v6.18.46 — an equal length raises nothing
(-ETXTBSY only on a swapfile).  The shape of the probe's fourth `data`
call ("hello" at its current length 5), here "yz{" at 3 answering
-EINVAL, is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#4:ret=-EINVAL -- data -/
theorem ftruncate_current_length_is_not_einval (m' : Model) (evs : List event) :
    check_ftruncate_row (ftruncate_call 4 3) (mkEffect (errno_ret EINVAL) [] []) ft_model
      ≠ CheckOk m' evs := by
  intro h
  have h' : CheckReject = CheckOk m' evs := h
  cases h'

/-- Success carries no ledger: a write, a copy-in, a zero-fill, an unmap
or a copy beside the 0 is refused.  `ftruncate` takes two integers and
returns one, so it names no user memory.  What a shrink does to the
file's mappings on Linux, and why the model's ledger stays as it was, is
said beside the ledger fact in `Checks/Arms/Fs/Open.lean`.  The last
three ledgers are the close pins' `close_zero_with_*`.
kernel: fs/open.c:ftruncate,do_sys_ftruncate@v6.18.46 -/
theorem ftruncate_ledger_is_empty :
    check_ftruncate 4 1 (mkEffect 0 [(4096, [0])] []) ft_model = CheckReject
    ∧ check_ftruncate 4 1 (with_copyins [(4096, 1)] (mkEffect 0 [] [])) ft_model = CheckReject
    ∧ check_ftruncate 4 1 close_zero_with_zeros ft_model = CheckReject
    ∧ check_ftruncate 4 1 close_zero_with_unmaps ft_model = CheckReject
    ∧ check_ftruncate 4 1 close_zero_with_copies ft_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- …and so do the refusals pinned here: beside the -EINVAL of a
negative length, and beside that of a descriptor of each kind
`do_ftruncate` refuses, a ledger is offered and refused;
`ftruncate_closed_number_is_ebadf` refuses a write beside the closed
number's -EBADF in the same way.  All three refusals return before any
user memory could be named, and the call names none: the length test and
the descriptor test in `do_sys_ftruncate` (fs/open.c:204-205 and
207-208), and the kind test in `do_ftruncate` (fs/open.c:175-176), Linux
v6.18.46.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem ftruncate_refusals_carry_no_ledger :
    check_ftruncate 4 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EINVAL) [(4096, [0])] [])
        ft_model = CheckReject
    ∧ check_ftruncate 0 0 (mkEffect (errno_ret EINVAL) [(4096, [0])] []) ft_model = CheckReject
    ∧ check_ftruncate 3 0 (with_copyins [(4096, 1)] (mkEffect (errno_ret EINVAL) [] [])) ft_model
        = CheckReject
    ∧ check_ftruncate 5 0 (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [(4096, 8)] [] [] [])
        ft_model = CheckReject
    ∧ check_ftruncate 6 0 (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [(4096, 4096)] [] [])
        ft_model = CheckReject
    ∧ check_ftruncate 7 0
        (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [MemCopy.mkCopy 4096 8192 8] [])
        ft_model = CheckReject
    ∧ check_ftruncate 8 0 (mkEffect (errno_ret EINVAL) [(4096, [0])] []) ft_model = CheckReject
    ∧ check_ftruncate 9 0 (mkEffect (errno_ret EINVAL) [(4096, [0])] []) ft_model = CheckReject
    ∧ check_ftruncate 11 0 (mkEffect (errno_ret EINVAL) [(4096, [0])] []) ft_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## A writable descriptor on a path the file system does not hold

The arm reads the file before it can build the new one, and a write-only
descriptor whose path `fs_lookup` does not find leaves it nothing to
read: at length 0 the checker declines whatever the kernel answered
(`ftruncate_dangling_fd_declines` below), as the spec does (the spec
pins' `dangling_writable_fd_declines`). -/

/-- Rocq's `ftruncate_on_a_dangling_fd_is_unmodeled` (`Checks/Cases/Fs/Open.v`),
on the row: fd 12 declines whatever the kernel answered, the witness
declines with it, and Rocq's own table — one write-only descriptor at 3
on an absent path — declines the 0 it offers, in a `fixture_of` model
whose credentials and urandom stream are not Rocq's `mkModel`'s, which
`check_ftruncate` does not read.  The evidence is `model:`
because the Rocq example is not in this file's mirror, and because the
decline is the model's own: Linux resizes the inode behind the open file
(`do_ftruncate` takes it from `file->f_path.dentry`, fs/open.c:173-174,
Linux v6.18.46), while the model keeps a file's bytes under its path and
holds none under this one.
model: a write-only descriptor on a path the fs does not hold; the model keeps bytes by path, so the decline is the model's -/
theorem ftruncate_dangling_fd_declines (eff : SyscallEffect) :
    check_ftruncate_row (ftruncate_call 12 0) eff ft_model = CheckUnmodeled
    ∧ ftruncate_witness_row (ftruncate_call 12 0) ft_model = Unmodeled
    ∧ check_ftruncate_row (ftruncate_call 3 0) (mkEffect 0 [] [])
        (fixture_of (fds := [(3, .FdFileW [102] 0)])) = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-! ## The append and the read-write descriptor take the write-only body

`do_ftruncate`'s test is `!S_ISREG(inode->i_mode) || !(file->f_mode &
FMODE_WRITE)` (fs/open.c:175-176, Linux v6.18.46), and an O_APPEND or an
O_RDWR description passes both halves exactly as an O_WRONLY one does:
O_APPEND rides on O_WRONLY, which is what sets FMODE_WRITE, and
`do_ftruncate` reads the flag nowhere.  So the two kinds `openat` mints
for the append word and the read-write words take the write-only arm's
body — the image lookup, the `modeled_truncate_gap` guard, the resized
image and 0 — and leave the offset alone, which a shrink can therefore
leave past end-of-file.  `ft_model` holds neither kind, so this section
brings its own table. -/

/-- An append descriptor at 3 on "f" and a read-write one at 4 on "g",
each file three bytes long, and each offset past what a shrink leaves. -/
def ft_new_fds : List (word × FdEntry) :=
  [ (3, .FdFileA [102] 9), (4, .FdFileRW [103] 2) ]
def ft_new_fs : Fs.Fs := [([102], [120, 121, 122]), ([103], [121, 122, 123])]
def ft_new_model : Model := fixture_of (fds := ft_new_fds) (fs := ft_new_fs)

/-- `ft_new_model` with the file behind 3 holding `data`, the other kept. -/
def ft_new_with_3 (data : List byte) : Model :=
  fixture_of (fds := ft_new_fds) (fs := [([102], data), ([103], [121, 122, 123])])

/-- …and with the file behind 4 holding it. -/
def ft_new_with_4 (data : List byte) : Model :=
  fixture_of (fds := ft_new_fds) (fs := [([102], [120, 121, 122]), ([103], data)])

/-- THE APPEND DESCRIPTOR resizes its file: a shrink keeps the prefix, a
grow zero-fills, the current length changes nothing, and the answer is 0
— not the -EINVAL the kinds `do_ftruncate` refuses get, and not the
length.  The descriptor table is untouched, the offset at 9 with it.  The
witness names the same 0 over the same model.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate,do_truncate@v6.18.46 -/
theorem ftruncate_append_fd_resizes_the_file :
    check_ftruncate 3 1 (mkEffect 0 [] []) ft_new_model = CheckOk (ft_new_with_3 [120]) []
    ∧ check_ftruncate 3 0 (mkEffect 0 [] []) ft_new_model = CheckOk (ft_new_with_3 []) []
    ∧ check_ftruncate 3 5 (mkEffect 0 [] []) ft_new_model
        = CheckOk (ft_new_with_3 [120, 121, 122, 0, 0]) []
    ∧ check_ftruncate 3 3 (mkEffect 0 [] []) ft_new_model
        = CheckOk (ft_new_with_3 [120, 121, 122]) []
    ∧ check_ftruncate 3 1 (mkEffect (errno_ret EINVAL) [] []) ft_new_model = CheckReject
    ∧ check_ftruncate 3 1 (mkEffect 1 [] []) ft_new_model = CheckReject
    ∧ ftruncate_witness 3 1 ft_new_model = Ok (mkEffect 0 [] []) (ft_new_with_3 [120]) []
    ∧ check_ftruncate_row (ftruncate_call 3 1) (mkEffect 0 [] []) ft_new_model
        = CheckOk (ft_new_with_3 [120]) [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE READ-WRITE DESCRIPTOR does the same, through the arm it shares
with the write-only kind: the shrink, the grow, the 0, the -EINVAL
refused, the witness and the row.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate,do_truncate@v6.18.46 -/
theorem ftruncate_rdwr_fd_resizes_the_file :
    check_ftruncate 4 1 (mkEffect 0 [] []) ft_new_model = CheckOk (ft_new_with_4 [121]) []
    ∧ check_ftruncate 4 5 (mkEffect 0 [] []) ft_new_model
        = CheckOk (ft_new_with_4 [121, 122, 123, 0, 0]) []
    ∧ check_ftruncate 4 1 (mkEffect (errno_ret EINVAL) [] []) ft_new_model = CheckReject
    ∧ check_ftruncate 4 1 (mkEffect (errno_ret EBADF) [] []) ft_new_model = CheckReject
    ∧ ftruncate_witness 4 1 ft_new_model = Ok (mkEffect 0 [] []) (ft_new_with_4 [121]) []
    ∧ check_ftruncate_row (ftruncate_call 4 1) (mkEffect 0 [] []) ft_new_model
        = CheckOk (ft_new_with_4 [121]) [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- …and they decline where the write-only kind declines, and only there:
on a path the image does not hold, and on a grow past
`modeled_truncate_gap` (131075 is the last length a three-byte file is
judged at).  A negative length is still the -EINVAL decided before the
descriptor is looked at.  Both declines are the model's own — Linux
resizes the inode behind the open file and leaves a hole for free — so
the evidence is `model:`.
model: `fs_lookup` by path and `modeled_truncate_gap`, the model's zero-fill bound; neither decline is a kernel test -/
theorem ftruncate_new_kinds_decline_where_the_write_only_kind_does (eff : SyscallEffect) :
    check_ftruncate 5 0 eff (fixture_of (fds := [(5, .FdFileA [104] 0)])) = CheckUnmodeled
    ∧ ftruncate_witness 5 0 (fixture_of (fds := [(5, .FdFileA [104] 0)])) = Unmodeled
    ∧ check_ftruncate 6 0 eff (fixture_of (fds := [(6, .FdFileRW [104] 0)])) = CheckUnmodeled
    ∧ ftruncate_witness 6 0 (fixture_of (fds := [(6, .FdFileRW [104] 0)])) = Unmodeled
    ∧ check_ftruncate 3 (Z_to_bv 64 131076) eff ft_new_model = CheckUnmodeled
    ∧ check_ftruncate 4 (Z_to_bv 64 131076) eff ft_new_model = CheckUnmodeled
    ∧ check_ftruncate 3 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect (errno_ret EINVAL) [] []) ft_new_model
        = CheckOk ft_new_model []
    ∧ check_ftruncate 4 (Z_to_bv 64 (2 ^ 64 - 1)) (mkEffect 0 [] []) ft_new_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The bound: judged up to it, declined past it -/

/-- Wherever the guard holds on a held write-only file, the checker
answers: whatever the kernel returned, it is accepted or refused, never
declined.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem check_ftruncate_judged_within_the_bound (fd len : word) (eff : SyscallEffect) (m : Model)
    (p : path) (pos : word) (data : List byte)
    (hfd : fd_lookup (m_fds m) fd = some (.FdFileW p pos))
    (hfs : fs_lookup (m_fs m) p = some data)
    (hgap : modeled_truncate_gap data len = true) :
    check_ftruncate fd len eff m ≠ CheckUnmodeled := by
  unfold check_ftruncate
  by_cases hneg : bv_signed len < 0
  · rw [ite_eq_left hneg]
    exact check_ret_only_no_unmodeled _ _ _ _
  rw [ite_eq_right hneg, hfd]
  dsimp only
  rw [hfs]
  dsimp only
  have hg : ¬ ((!modeled_truncate_gap data len) = true) := by
    rw [hgap]
    decide
  rw [ite_eq_right hg]
  exact check_ret_only_no_unmodeled _ _ _ _

/-- …and past it, a length that passes the sign test declines, whatever
the kernel returned: the zero-fill `file_truncate` would build is larger
than `modeled_truncate_gap` lets the model hold as a byte list, where Linux
leaves a hole for free.  The decline is the model's, not a kernel test: at
131073 on the probe's empty tmpfs file the kernel answers 0 (`bound-over`).
model: `modeled_truncate_gap`, the model's zero-fill bound; the decline is the model's, not a kernel test -/
theorem check_ftruncate_declines_past_the_bound (fd len : word) (eff : SyscallEffect)
    (m : Model) (p : path) (pos : word) (data : List byte)
    (hneg : ¬ bv_signed len < 0)
    (hfd : fd_lookup (m_fds m) fd = some (.FdFileW p pos))
    (hfs : fs_lookup (m_fs m) p = some data)
    (hgap : ¬ modeled_truncate_gap data len = true) :
    check_ftruncate fd len eff m = CheckUnmodeled := by
  unfold check_ftruncate
  rw [ite_eq_right hneg, hfd]
  dsimp only
  rw [hfs]
  dsimp only
  have hg : (!modeled_truncate_gap data len) = true := by
    cases h : modeled_truncate_gap data len
    · rfl
    · exact absurd h hgap
  rw [ite_eq_left hg]

/-- A shrink is judged, for every length that does not grow the file and
whatever the file's size: the spec pins' `shrink_is_modeled_for_every_length`
carried to the checker.  The probe's `bound-shrink` case is the shape a
guard on the absolute difference would decline.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem check_ftruncate_shrink_is_judged (fd len : word) (eff : SyscallEffect) (m : Model)
    (p : path) (pos : word) (data : List byte)
    (hfd : fd_lookup (m_fds m) fd = some (.FdFileW p pos))
    (hfs : fs_lookup (m_fs m) p = some data)
    (hlen : bv_unsigned len ≤ data.length) :
    check_ftruncate fd len eff m ≠ CheckUnmodeled :=
  check_ftruncate_judged_within_the_bound fd len eff m p pos data hfd hfs
    (shrink_is_modeled_for_every_length data len hlen)

/-- A grow to the bound is judged: 131072 on the empty 13, the probe's
`bound-at` call, and 131075 on "yz{".  What the call leaves — 131072 zero
bytes — is not spelled out here, for the reason the section header gives;
its length is, by `file_truncate_length` below.
kernel: fs/open.c:do_ftruncate,do_truncate@v6.18.46 -/
theorem ftruncate_grow_to_the_bound_is_judged (eff : SyscallEffect) :
    check_ftruncate 13 (Z_to_bv 64 131072) eff ft_model ≠ CheckUnmodeled
    ∧ check_ftruncate 4 (Z_to_bv 64 131075) eff ft_model ≠ CheckUnmodeled :=
  ⟨check_ftruncate_judged_within_the_bound 13 _ eff ft_model [105] 4 [] rfl rfl
      grow_from_empty_at_the_bound_is_modeled,
   check_ftruncate_judged_within_the_bound 4 _ eff ft_model [103] 9 [121, 122, 123] rfl rfl
      grow_at_the_bound_is_modeled⟩

/-- What the accepted 0 leaves is exactly `len` bytes long, for every file
and every length: the prefix `List.take` keeps and the zeros
`List.replicate` adds sum to `word_to_nat len`, shrink or grow — the size
`do_truncate` hands on as `ia_size` (fs/open.c:49, Linux v6.18.46) and
tmpfs stores as the inode's new size (`shmem_setattr`, mm/shmem.c:1331,
Linux v6.18.46).  Stated over the definition rather than a literal list, so
that the grow to the bound is fixed without any pin building it: a
`file_truncate` that capped its count, as `file_read` caps with
`word_to_nat_bounded`, fails here.
kernel: fs/open.c:do_truncate; mm/shmem.c:shmem_setattr@v6.18.46 -/
theorem file_truncate_length (data : List byte) (len : word) :
    (file_truncate data len).length = word_to_nat len := by
  unfold file_truncate
  simp only [List.length_append, List.length_take, List.length_replicate]
  omega

/-- …so the grow to the bound on "yz{" leaves 131075 bytes, not a capped
count.
kernel: fs/open.c:do_truncate; mm/shmem.c:shmem_setattr@v6.18.46 -/
theorem ftruncate_grow_to_the_bound_leaves_len_bytes :
    (file_truncate [121, 122, 123] (Z_to_bv 64 131075)).length = 131075 := by
  rw [file_truncate_length]
  rfl

/-- One byte past the bound declines, checker and witness alike: 131073 on
the empty 13, the probe's `bound-over` call, and 131076 on "yz{".
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- bound-over -/
theorem ftruncate_past_the_bound_declines (eff : SyscallEffect) :
    check_ftruncate 13 (Z_to_bv 64 131073) eff ft_model = CheckUnmodeled
    ∧ check_ftruncate 4 (Z_to_bv 64 131076) eff ft_model = CheckUnmodeled
    ∧ ftruncate_witness 13 (Z_to_bv 64 131073) ft_model = Unmodeled
    ∧ ftruncate_witness 4 (Z_to_bv 64 131076) ft_model = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- 2^31 is a huge POSITIVE length — the `small = 0` that `O_LARGEFILE`
triggers at fs/open.c:170-171 (Linux v6.18.46), a flag `openat` sets
where `force_o_largefile` holds, as on riscv64 (fs/open.c:1466-1467),
makes `MAX_NON_LFS` unreachable — and declines, checker and witness
alike.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- big31 -/
theorem ftruncate_two_pow_31_declines (eff : SyscallEffect) :
    check_ftruncate 13 (Z_to_bv 64 (2 ^ 31)) eff ft_model = CheckUnmodeled
    ∧ ftruncate_witness 13 (Z_to_bv 64 (2 ^ 31)) ft_model = Unmodeled :=
  ⟨rfl, rfl⟩

/-- …and is not -EINVAL: a checker reading the length as a 32-bit `off_t`,
or keeping the `MAX_NON_LFS` test that `small = 0` disables, would accept
that.
kernel: fs/open.c:do_ftruncate; include/linux/fcntl.h:force_o_largefile@v6.18.46 -/
theorem ftruncate_two_pow_31_is_not_einval (m' : Model) (evs : List event) :
    check_ftruncate 13 (Z_to_bv 64 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] []) ft_model
      ≠ CheckOk m' evs := by
  intro h
  have h' : CheckUnmodeled = CheckOk m' evs := h
  cases h'

/-- 2^30 from empty declines too: the guard reads the gap on `Int`.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- guard-z -/
theorem ftruncate_two_pow_30_declines (eff : SyscallEffect) :
    check_ftruncate 13 (Z_to_bv 64 (2 ^ 30)) eff ft_model = CheckUnmodeled
    ∧ ftruncate_witness 13 (Z_to_bv 64 (2 ^ 30)) ft_model = Unmodeled :=
  ⟨rfl, rfl⟩

/-- 2^63 - 1, the largest `off_t`, declines on both files.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- huge -/
theorem ftruncate_largest_off_t_declines (eff : SyscallEffect) :
    check_ftruncate 13 (Z_to_bv 64 (2 ^ 63 - 1)) eff ft_model = CheckUnmodeled
    ∧ check_ftruncate 4 (Z_to_bv 64 (2 ^ 63 - 1)) eff ft_model = CheckUnmodeled
    ∧ ftruncate_witness 13 (Z_to_bv 64 (2 ^ 63 - 1)) ft_model = Unmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- The `zero` mode's call with 2^63 - 1 written into its length: the row
declines, checker and witness alike, and is not the -EINVAL that 2^63
one above it is.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed --mutate ftruncate#1:arg1=0x7fffffffffffffff -- zero -/
theorem ftruncate_row_largest_off_t_declines (eff : SyscallEffect) :
    check_ftruncate_row (ftruncate_call 13 (Z_to_bv 64 (2 ^ 63 - 1))) eff ft_model
        = CheckUnmodeled
    ∧ ftruncate_witness_row (ftruncate_call 13 (Z_to_bv 64 (2 ^ 63 - 1))) ft_model
        = Unmodeled :=
  ⟨rfl, rfl⟩

/-- Neither 0 nor -EFBIG (27) is accepted at the largest `off_t`, though
each is an answer a real kernel gives there: 0 where the filesystem's
`s_maxbytes` reaches it (tmpfs), -EFBIG from `inode_newsize_ok`
(fs/attr.c:269-270, Linux v6.18.46) where it does not.  They are not the
only ones: `do_ftruncate` (fs/open.c:190-192, Linux v6.18.46) asks the
pre-content hook `fsnotify_truncate_perm`
(include/linux/fsnotify.h:186-199, Linux v6.18.46), through which a
fanotify listener can deny the call, and a FUSE server's errno comes
back through `fuse_do_setattr` (fs/fuse/dir.c:2048-2053, Linux
v6.18.46).  Which one a run sees is the environment's, which the model
does not hold, so the decline is the answer.
kernel: fs/attr.c:inode_newsize_ok; fs/open.c:do_ftruncate@v6.18.46 -/
theorem ftruncate_largest_off_t_is_neither_zero_nor_efbig (m' : Model) (evs : List event) :
    check_ftruncate 13 (Z_to_bv 64 (2 ^ 63 - 1)) (mkEffect 0 [] []) ft_model ≠ CheckOk m' evs
    ∧ check_ftruncate 13 (Z_to_bv 64 (2 ^ 63 - 1)) (mkEffect (errno_ret 27) [] []) ft_model
        ≠ CheckOk m' evs := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : CheckUnmodeled = CheckOk m' evs := h
    cases h'
  · have h' : CheckUnmodeled = CheckOk m' evs := h
    cases h'

/-! ## The row: syscall 46, its 32-bit fd and its 64-bit length

`SYSCALL_DEFINE2(ftruncate, unsigned int, fd, off_t, length)`
(fs/open.c:213-216, Linux v6.18.46): the fd is `unsigned int`, narrowed
by `__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-88,
Linux v6.18.46) through `__SC_CAST` (include/linux/syscalls.h:132, Linux
v6.18.46), which the row's `fd32` mirrors; the length is `off_t`, the
whole register. -/

/-- `ftruncate(2^32 + 4, 1)` IS `ftruncate(4, 1)`: the high half of a0 is
dropped, the call shrinks the file behind 4, and the -EBADF of a checker
reading all 64 bits is refused; `ftruncate(2^32 + 10, 0)` is the closed
10's -EBADF; garbage in a2..a5 changes nothing.  `fd_truncation.c`'s
`conform --stdin hi` run records answers of the first and third kinds on
a real kernel — 0 from `ftruncate(tfd | HI_NEG, 2)`, which resizes the
low half's file, and -EBADF once `tfd` is closed; at this head no run
offers the refused -EBADF.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:ftruncate,do_sys_ftruncate@v6.18.46 -/
theorem ftruncate_row_fd_truncates_to_32_bits :
    check_ftruncate_row (ftruncate_call (Z_to_bv 64 (2 ^ 32 + 4)) 1) (mkEffect 0 [] []) ft_model
        = CheckOk (ft_with_4 [121]) []
    ∧ check_ftruncate_row (ftruncate_call (Z_to_bv 64 (2 ^ 32 + 4)) 1)
        (mkEffect (errno_ret EBADF) [] []) ft_model = CheckReject
    ∧ check_ftruncate_row (ftruncate_call (Z_to_bv 64 (2 ^ 32 + 10)) 0)
        (mkEffect (errno_ret EBADF) [] []) ft_model = CheckOk ft_model []
    ∧ check_ftruncate_row (SyscallInput.mkInput 46 [4, 1, 7, 7, 7, 7] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) ft_model = CheckOk (ft_with_4 [121]) [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The length is NOT narrowed: `ftruncate(4, 2^32)` is a grow of about
4 GiB.  The witness declines it, and the checker declines the 0 over an
emptied file that a checker reading the low 32 bits would accept.  Both
declines are THE BOUND's, not a kernel test: a tmpfs file can grow to
2^32 bytes, and the kernel then answers 0.  `shmem_fill_super`
(mm/shmem.c:5118, Linux v6.18.46) sets tmpfs's s_maxbytes to
MAX_LFS_FILESIZE, which is LLONG_MAX on a 64-bit kernel
(include/linux/fs.h:1278-1279, Linux v6.18.46), so the grow passes
`inode_newsize_ok` (fs/attr.c:251-255, Linux v6.18.46) unless
RLIMIT_FSIZE is below 2^32.  The kernel half of this pin is only that
the length reaches `do_sys_ftruncate` whole.
kernel: fs/open.c:ftruncate,do_sys_ftruncate@v6.18.46 -/
theorem ftruncate_row_length_is_the_whole_register :
    ftruncate_witness_row (ftruncate_call 4 (Z_to_bv 64 (2 ^ 32))) ft_model = Unmodeled
    ∧ check_ftruncate_row (ftruncate_call 4 (Z_to_bv 64 (2 ^ 32))) (mkEffect 0 [] []) ft_model
        = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-! ## Where it declines, and the witness -/

/-- The checker declines only past the sign test and only on a writable
descriptor — a write-only, an append or a read-write one, and only where
the image does not hold its path or the grow is past
`modeled_truncate_gap`: every other input is accepted or refused.  The
three kinds share one body, so the disjunction below is over the kinds
and not over three answers.
This is the `CheckUnmodeled` the refutations above leave open, closed on
the checker's own terms.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem check_ftruncate_declines_only_on_a_held_writable_file (fd len : word)
    (eff : SyscallEffect) (m : Model) (h : check_ftruncate fd len eff m = CheckUnmodeled) :
    ¬ bv_signed len < 0 ∧ ∃ p pos, fd_lookup (m_fds m) fd = some (.FdFileW p pos)
      ∨ fd_lookup (m_fds m) fd = some (.FdFileA p pos)
      ∨ fd_lookup (m_fds m) fd = some (.FdFileRW p pos) := by
  unfold check_ftruncate at h
  by_cases hneg : bv_signed len < 0
  · rw [ite_eq_left hneg] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  rw [ite_eq_right hneg] at h
  refine ⟨hneg, ?_⟩
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
    cases e
    case FdFileW p pos => exact ⟨p, pos, Or.inl rfl⟩
    case FdFileA p pos => exact ⟨p, pos, Or.inr (Or.inl rfl)⟩
    case FdFileRW p pos => exact ⟨p, pos, Or.inr (Or.inr rfl)⟩
    all_goals exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- The witness names the checker's answers: -EINVAL on a negative length
before the closed number is looked at, -EBADF on the closed number, -EINVAL
on the kinds `do_ftruncate`'s test at fs/open.c:175-176 refuses — the
directory, stdin (by the spec's premise that no channel is a writable
regular file), the read-only file, the socket, both pipe ends, /dev/null
and /dev/urandom — 0 over the shrunk file, and through the row the aliased
2^32 + 4 shrinks 4.  The spec admits one outcome on each of those kinds,
so `ftruncate_witness_ok` fixes the witness there as well; the conjuncts
say which outcome it is.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem ftruncate_witness_names_the_answer :
    ftruncate_witness 10 (Z_to_bv 64 (2 ^ 64 - 1)) ft_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model []
    ∧ ftruncate_witness 10 0 ft_model = Ok (mkEffect (errno_ret EBADF) [] []) ft_model []
    ∧ ftruncate_witness 5 0 ft_model = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model []
    ∧ ftruncate_witness 0 0 ft_model = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model []
    ∧ ftruncate_witness 3 0 ft_model = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model []
    ∧ ftruncate_witness 6 0 ft_model = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model []
    ∧ ftruncate_witness 7 0 ft_model = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model []
    ∧ ftruncate_witness 8 0 ft_model = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model []
    ∧ ftruncate_witness 9 0 ft_model = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model []
    ∧ ftruncate_witness 11 0 ft_model = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model []
    ∧ ftruncate_witness 4 1 ft_model = Ok (mkEffect 0 [] []) (ft_with_4 [121]) []
    ∧ ftruncate_witness_row (ftruncate_call (Z_to_bv 64 (2 ^ 32 + 4)) 1) ft_model
        = Ok (mkEffect 0 [] []) (ft_with_4 [121]) [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Whatever the witness names, the checker accepts, on every table and
for every descriptor and length: `ftruncate_witness_ok` puts the outcome
in the spec and `check_ftruncate_complete_ok` carries it to the checker.
model: `ftruncate_witness` fed to `check_ftruncate`, no spec named -/
theorem ftruncate_witness_is_accepted (fd len : word) (m m' : Model) (eff : SyscallEffect)
    (evs : List event) (i : SyscallInput) (h : ftruncate_witness fd len m = Ok eff m' evs) :
    check_ftruncate fd len eff m = CheckOk m' evs := by
  have hw := ftruncate_witness_ok fd len i m
  rw [h] at hw
  exact check_ftruncate_complete_ok fd len eff m m' evs i hw

/-- …and where the witness declines, the checker declines too, for every
effect: `check_ftruncate_complete_unmodeled` carries the spec's
`Unmodeled` to it.
model: `ftruncate_witness` fed to `check_ftruncate`, no spec named -/
theorem ftruncate_witness_declines_with_the_checker (fd len : word) (m : Model)
    (eff : SyscallEffect) (i : SyscallInput) (h : ftruncate_witness fd len m = Unmodeled) :
    check_ftruncate fd len eff m = CheckUnmodeled := by
  have hw := ftruncate_witness_ok fd len i m
  rw [h] at hw
  exact check_ftruncate_complete_unmodeled fd len m i eff hw

section RealTable

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress (syscall_spec_witness)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Pipe (pipe_model)

/-! ## Over the real table

`checked_table` holds `arm_ftruncate` (`Checks/Arms/Fs/Open.lean`), so a
call to 46 reaches the checker through the dispatcher itself.  What a pin
here adds to the rows above is the ARM's claim: that the lookup at 46
finds `arm_ftruncate` rather than the dispatcher's own decline, and that
the arm hands the checker `fd32 (in_arg i 0)` and `in_arg i 1`.
`lookup_ftruncate_input` and `check_syscall_at_46_is_the_row` state both
for every input, which is what makes each row pin above a pin on
`check_syscall`; the pins after them spell the register reading out at
one call, for the checker and for the witness `receptive` asks for; and
the pins after those restate Rocq's five ftruncate claims through the
dispatcher, as Rocq does — the dangling descriptor, the two pipe cases,
and the 46 legs of the two device `*_dispatch_sites` in one pin.  They
are not Rocq's terms verbatim: the models are `fixture_of`'s, which
differ from Rocq's models (`mkModel` terms, the urandom one under
`with_urandom`) in fields `check_ftruncate` does not read — the
credentials (`demo_creds`, not `overflow_id`) and the urandom stream
among them — and the urandom leg's call carries no `urandom_wmem`;
`check_ftruncate` decides on `m_fds` and `m_fs` alone, so no verdict
depends on either. -/

/-- The lookup the dispatcher performs on a call to 46 finds
`arm_ftruncate`, whatever the six words and the two memory views hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_ftruncate_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 46 args mem wmem).in_sysno)
      = some arm_ftruncate :=
  lookup_ca_checked_table_ftruncate

/-- …so the real table's answer to a call to 46 IS the row's, for every
input, effect and model.
model: `check_syscall` at 46 against `check_ftruncate_row`; the table's own
contents, not a kernel claim. -/
theorem check_syscall_at_46_is_the_row (args : List word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 46 args mem wmem) eff m
      = check_ftruncate_row (SyscallInput.mkInput 46 args mem wmem) eff m :=
  rfl

/-- `ftruncate(5, 10)` through the table: the descriptor is a0, the
directory, and its -EINVAL (`do_ftruncate`, fs/open.c:175-176, Linux
v6.18.46) is accepted; the -EBADF of an arm that read the two registers
the other way round, and so looked up the closed 10, is refused.
kernel: fs/open.c:ftruncate,do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem ftruncate_reads_a0_then_a1_over_the_real_table :
    check_syscall (ftruncate_call 5 10) (mkEffect (errno_ret EINVAL) [] []) ft_model
        = CheckOk ft_model []
    ∧ check_syscall (ftruncate_call 5 10) (mkEffect (errno_ret EBADF) [] []) ft_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- `syscall_spec_witness` dispatches over the same table, so the arm's
`ca_witness` is what it answers at 46: the aliased 2^32 + 4 is 4 to the
witness as to the checker, and the shrink to 1 is what it exhibits.  An
arm that handed the witness all 64 bits of a0 would look up 2^32 + 4, a
key `ft_fds` does not hold, and exhibit -EBADF.
kernel: include/linux/syscalls.h:__SC_CAST; fs/open.c:do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem ftruncate_aliased_fd_witnesses_the_shrink_over_the_real_table :
    syscall_spec_witness (ftruncate_call (Z_to_bv 64 (2 ^ 32 + 4)) 1) ft_model
      = Ok (mkEffect 0 [] []) (ft_with_4 [121]) [] :=
  rfl

/-- …and a0 is the descriptor to the witness too: `ftruncate(5, 10)`
exhibits the directory's -EINVAL, where an arm handing it the registers
the other way round would look up the closed 10 and exhibit -EBADF.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem ftruncate_witness_reads_a0_then_a1_over_the_real_table :
    syscall_spec_witness (ftruncate_call 5 10) ft_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] :=
  rfl

/-- Rocq's `ftruncate_on_a_dangling_fd_is_unmodeled` (`Checks/Cases/Fs/Open.v`)
through `check_syscall`, as Rocq does, over Rocq's own table (in a
`fixture_of` model, as the section header says): one write-only
descriptor at 3 on a path the file system does not hold, where the 0 it
offers is declined.
model: a write-only descriptor on a path the fs does not hold; the model keeps bytes by path, so the decline is the model's -/
theorem ftruncate_on_a_dangling_fd_is_unmodeled_over_the_real_table :
    check_syscall (ftruncate_call 3 0) (mkEffect 0 [] [])
        (fixture_of (fds := [(3, .FdFileW [102] 0)])) = CheckUnmodeled :=
  rfl

/-- Rocq's `ftruncate_on_a_pipe_end_is_einval` (`Checks/Cases/Fs/Pipe.v`)
through `check_syscall`, as Rocq does, over Rocq's `pipe_model`, whose
twin is `Checks/Cases/Fs/Pipe.lean`'s: 3 is a pipe's read end and 4 its
write end, and each answers -EINVAL.  A pipe's inode is `S_IFIFO`
(`get_pipe_inode`, fs/pipe.c:912, Linux v6.18.46), so `do_ftruncate`'s
`!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)` (fs/open.c:175-176)
holds on its first disjunct at both ends.  The write end is allocated
`O_WRONLY` (`create_pipe_files`, fs/pipe.c:944-945), which `init_file` turns
into `FMODE_WRITE` (fs/file_table.c:199), and is refused all the same: the
answer comes from the file type, not the mode.  `pipe2_spec.c`'s
`conform -- kinds` run records both answers on a real kernel, at these
two numbers and length 0.
kernel: fs/open.c:do_ftruncate; fs/pipe.c:get_pipe_inode,create_pipe_files@v6.18.46 -/
theorem ftruncate_on_a_pipe_end_is_einval :
    check_syscall (ftruncate_call 3 0) (mkEffect (errno_ret EINVAL) [] []) pipe_model
        = CheckOk pipe_model []
    ∧ check_syscall (ftruncate_call 4 0) (mkEffect (errno_ret EINVAL) [] []) pipe_model
        = CheckOk pipe_model [] :=
  ⟨rfl, rfl⟩

/-- Rocq's `ftruncate_on_a_pipe_write_end_rejects_success`
(`Checks/Cases/Fs/Pipe.v`), the negative half, through `check_syscall` over
the same model: the write end at 4 is refused a 0, which `do_ftruncate`
reaches only past its `S_ISREG` test (fs/open.c:175-176, Linux v6.18.46),
so a writable descriptor is told apart from a writable regular file; and
it is refused the -EBADF of an empty slot, since `do_sys_ftruncate`'s
`fd_empty` test (fs/open.c:207-208) passes an installed pipe end.  The 0
is the one `pipe2_spec.c`'s `reject --mutate ftruncate#2:ret=0 -- kinds`
run offers the checker, which refuses it; at this head no run offers the
-EBADF.
kernel: fs/open.c:do_ftruncate,do_sys_ftruncate@v6.18.46 -/
theorem ftruncate_on_a_pipe_write_end_rejects_success :
    check_syscall (ftruncate_call 4 0) (mkEffect 0 [] []) pipe_model = CheckReject
    ∧ check_syscall (ftruncate_call 4 0) (mkEffect (errno_ret EBADF) [] []) pipe_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The 46 legs of Rocq's `devnull_dispatch_sites` and
`urandom_dispatch_sites` (`Checks/Cases/Fs/Open.v`) through
`check_syscall`, as Rocq does: the write-only /dev/null at 4 and
/dev/urandom at 3 each answer -EINVAL with the model unchanged, since a
character device fails `do_ftruncate`'s `!S_ISREG(inode->i_mode)`
(fs/open.c:175-176, Linux v6.18.46) whatever its access mode.  The tables
are `ftruncate_device_fixtures_are_einval`'s.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem ftruncate_device_dispatch_legs_over_the_real_table :
    check_syscall (ftruncate_call 4 0) (mkEffect (errno_ret EINVAL) [] []) ft_devnull_model
        = CheckOk ft_devnull_model []
    ∧ check_syscall (ftruncate_call 3 0) (mkEffect (errno_ret EINVAL) [] []) ft_urandom_model
        = CheckOk ft_urandom_model [] :=
  ⟨rfl, rfl⟩

end RealTable

-- lean-port sentinel: ticket V-Fs-Open-faccessat appends below this line

section V_Fs_Open_faccessat

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress (syscall_spec_witness)

/-! ## V-Fs-Open-faccessat — faccessat and faccessat2 over the real table

`checked_table` holds `arm_faccessat` and `arm_faccessat2`
(`Checks/Arms/Fs/Open.lean`), so a call to 48 or 439 reaches the checker
through the dispatcher.  What a pin here adds to the row pins above is
the ARM's claim: that the lookup finds the arm, and which register the
arm hands the checker as what.  `check_syscall_at_48_is_the_row` and
`check_syscall_at_439_is_the_row` state that for every input, which is
what makes every pin on `check_faccessat_row` or `check_faccessat2_row`
in the `# faccessat (48) and faccessat2 (439)` section a pin on
`check_syscall`; the section's witness-row pins are tied to the table
only at the calls `witness_over_the_real_table` names.  The pins after
them separate the arms'
register reading from a wrong one at one call, for the checker and for
the witness; and the last restate Rocq's examples (named in that
section's header) through `check_syscall`, as Rocq states them. -/

/-- The lookup on a call to 48 finds `arm_faccessat`, whatever the
six words and the two memory views hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_faccessat_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 48 args mem wmem).in_sysno)
      = some arm_faccessat :=
  lookup_ca_checked_table_faccessat

/-- The lookup on a call to 439 finds `arm_faccessat2`, whatever the
six words and the two memory views hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_faccessat2_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 439 args mem wmem).in_sysno)
      = some arm_faccessat2 :=
  lookup_ca_checked_table_faccessat2

/-- The real table's answer at 48 is the row's, for every input,
effect and model.
model: `check_syscall` at 48 against `check_faccessat_row`; the table's own
contents, not a kernel claim. -/
theorem check_syscall_at_48_is_the_row (args : List word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 48 args mem wmem) eff m
      = check_faccessat_row (SyscallInput.mkInput 48 args mem wmem) eff m :=
  rfl

/-- The real table's answer at 439 is the row's, for every input,
effect and model.
model: `check_syscall` at 439 against `check_faccessat2_row`; the table's own
contents, not a kernel claim. -/
theorem check_syscall_at_439_is_the_row (args : List word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 439 args mem wmem) eff m
      = check_faccessat2_row (SyscallInput.mkInput 439 args mem wmem) eff m :=
  check_syscall_of_found _ _ _ _ (lookup_faccessat2_input args mem wmem)

/-- The dirfd is a0 cut to its low 32 bits, the `int dfd` of
`SYSCALL_DEFINE3(faccessat)` (fs/open.c:539, Linux v6.18.46).  2^32 - 100
is the probe's `dirfd-cwd` word, already `AT_FDCWD32` whole, so it holds
under either reading; 2^33 - 100 sets a bit of a0's high half, which only
the cut drops: an arm handing the checker all 64 bits would see neither
`AT_FDCWD32` nor `AT_FDCWD` there and decline the 0.  At both,
`path_init` starts the walk at the working directory (fs/namei.c:2590,
Linux v6.18.46), the held name's 0 is accepted, and the -ENOENT that
`traverse_mounts` gives a negative dentry (fs/namei.c:1537-1538) is refused.
kernel: include/linux/syscalls.h:__SC_CAST; fs/open.c:faccessat,do_faccessat; fs/namei.c:path_init,traverse_mounts@v6.18.46 -/
theorem faccessat_dirfd_is_a0_cut_to_32_bits_over_the_real_table :
    check_syscall (faccessat_in' 4294967196 8192 0 (open_path_mem [97]))
        (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_syscall (faccessat_in' 4294967196 8192 0 (open_path_mem [97]))
        (eff_errno ENOENT 2) fa_model = CheckReject
    ∧ check_syscall (faccessat_in' 8589934492 8192 0 (open_path_mem [97]))
        (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_syscall (faccessat_in' 8589934492 8192 0 (open_path_mem [97]))
        (eff_errno ENOENT 2) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- a2 = 8 is a bad mode, -EINVAL before any pathname read
(fs/open.c:475-476, Linux v6.18.46).  With a2 = 0 the same answer is
refused, so the mode is not read from a1 (8192, a bad mode too) or a3 (0).
kernel: fs/open.c:faccessat,do_faccessat@v6.18.46 -/
theorem faccessat_mode_is_a2_over_the_real_table :
    check_syscall (faccessat_in [97] 8) (mkEffect (errno_ret EINVAL) [] []) fa_model
        = CheckOk fa_model []
    ∧ check_syscall (faccessat_in [97] 0) (mkEffect (errno_ret EINVAL) [] []) fa_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `mode-trunc`: the `int` mode drops 2^32, so 2^32 is
F_OK and 2^32 + 8 is -EINVAL.  The checker narrows the whole a2 word.
kernel: include/linux/syscalls.h:__SC_CAST; fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat_mode_is_a2_whole_over_the_real_table :
    check_syscall (faccessat_in [97] 4294967296) (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_syscall (faccessat_in [97] 4294967304) (mkEffect (errno_ret EINVAL) [] []) fa_model
        = CheckOk fa_model [] :=
  ⟨rfl, rfl⟩

/-- `SYSCALL_DEFINE3(faccessat)` passes flags 0 (fs/open.c:539-542,
Linux v6.18.46).  An arm reading a3 as faccessat2's flag word would
answer 1024's -EINVAL (fs/open.c:478-479, Linux v6.18.46); here, with
a0 the `AT_FDCWD` `path_init` reads (fs/namei.c:2590), 0 is accepted and
that -EINVAL is refused.
kernel: fs/open.c:faccessat,do_faccessat; fs/namei.c:path_init@v6.18.46 -/
theorem faccessat_ignores_a3_over_the_real_table :
    check_syscall (SyscallInput.mkInput 48 [AT_FDCWD, 8192, 0, 1024, 0, 0]
        (open_path_mem [97]) (fun _ => none)) (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_syscall (SyscallInput.mkInput 48 [AT_FDCWD, 8192, 0, 1024, 0, 0]
        (open_path_mem [97]) (fun _ => none)) (mkEffect (errno_ret EINVAL) [] []) fa_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The bad flag word is a3: 1024 answers -EINVAL and success is refused.
An arm reading flags from a4 (0) would accept the 0.
kernel: fs/open.c:faccessat2,do_faccessat@v6.18.46 -/
theorem faccessat2_flags_is_a3_over_the_real_table :
    check_syscall (faccessat2_in [97] 0 1024) (mkEffect (errno_ret EINVAL) [] []) fa_model
        = CheckOk fa_model []
    ∧ check_syscall (faccessat2_in [97] 0 1024) (eff_ret 0 2) fa_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The probe's `flags-trunc`: 2^32 is a zero flag word to the `int`
flags, so the held name accepts 0 and refuses the flag -EINVAL.
kernel: include/linux/syscalls.h:__SC_CAST; fs/open.c:faccessat2,do_faccessat@v6.18.46 -/
theorem faccessat2_flags_is_a3_whole_over_the_real_table :
    check_syscall (faccessat2_in [97] 0 4294967296) (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_syscall (faccessat2_in [97] 0 4294967296) (mkEffect (errno_ret EINVAL) [] []) fa_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The same cut at 439, the `int dfd` of `SYSCALL_DEFINE4(faccessat2)`
(fs/open.c:544, Linux v6.18.46): the probe's 2^32 - 100, which holds
under either reading, and 2^33 - 100, which holds only under the cut.
At both `path_init` starts at the working directory (fs/namei.c:2590),
the held name's 0 is accepted and `traverse_mounts`'s -ENOENT
(fs/namei.c:1537-1538) refused.
kernel: include/linux/syscalls.h:__SC_CAST; fs/open.c:faccessat2,do_faccessat; fs/namei.c:path_init,traverse_mounts@v6.18.46 -/
theorem faccessat2_dirfd_is_a0_cut_to_32_bits_over_the_real_table :
    check_syscall (faccessat2_in' 4294967196 8192 0 0 (open_path_mem [97]))
        (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_syscall (faccessat2_in' 4294967196 8192 0 0 (open_path_mem [97]))
        (eff_errno ENOENT 2) fa_model = CheckReject
    ∧ check_syscall (faccessat2_in' 8589934492 8192 0 0 (open_path_mem [97]))
        (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_syscall (faccessat2_in' 8589934492 8192 0 0 (open_path_mem [97]))
        (eff_errno ENOENT 2) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `syscall_spec_witness` dispatches over the same table, so the arms'
`ca_witness` reads the registers as the checker does: F_OK of the held
name exhibits 0, at the dirfd 2^33 - 100 that only the cut makes AT_FDCWD
and under the flag word 2^32 that the `int` makes zero; the bad mode and
the bad flag word exhibit -EINVAL with no copy-in.
kernel: fs/open.c:faccessat,faccessat2,do_faccessat@v6.18.46 -/
theorem witness_over_the_real_table :
    syscall_spec_witness (faccessat_in [97] 0) fa_model = Ok (eff_ret 0 2) fa_model []
    ∧ syscall_spec_witness (faccessat_in' 8589934492 8192 0 (open_path_mem [97])) fa_model
        = Ok (eff_ret 0 2) fa_model []
    ∧ syscall_spec_witness (faccessat_in [97] 8) fa_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) fa_model []
    ∧ syscall_spec_witness (faccessat2_in [97] 0 1024) fa_model
        = Ok (mkEffect (errno_ret EINVAL) [] []) fa_model []
    ∧ syscall_spec_witness (faccessat2_in [97] 0 4294967296) fa_model
        = Ok (eff_ret 0 2) fa_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Rocq's `faccessat_implied_directory_unmodeled`
(`Checks/Cases/Fs/Open.v`) through `check_syscall`, as Rocq states it;
the row pin `faccessat_implied_directory_unmodeled` above says why.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat_implied_directory_unmodeled_over_the_real_table :
    check_syscall (faccessat_in [97] 0) (eff_ret 0 2) fa_under_model = CheckUnmodeled :=
  rfl

/-- Rocq's `faccessat_byte_prefix_is_not_a_directory`
(`Checks/Cases/Fs/Open.v`) through `check_syscall`, at Rocq's input,
effect and model; Rocq pins the accepted model's `m_fs`, this the whole
model, so it implies Rocq's statement;
the row pin `faccessat_byte_prefix_is_not_a_directory` above says why.
kernel: fs/open.c:do_faccessat; fs/namei.c:link_path_walk@v6.18.46 -/
theorem faccessat_byte_prefix_is_not_a_directory_over_the_real_table :
    check_syscall (faccessat_in [97] 0) (eff_ret 0 2) fa_sibling_model
      = CheckOk fa_sibling_model [] :=
  rfl

/-- Rocq's `faccessat_bad_mode_beats_an_unreadable_path`
(`Checks/Cases/Fs/Open.v`) through `check_syscall`: the first conjunct is
Rocq's statement, and the two -EFAULT refusals are added;
the row pin `faccessat_bad_mode_beats_an_unreadable_path` above says why.
kernel: fs/open.c:do_faccessat; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem faccessat_bad_mode_beats_an_unreadable_path_over_the_real_table :
    check_syscall (fa_unmapped_in 8) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_syscall (fa_unmapped_in 8) (mkEffect (errno_ret EFAULT) [] []) fa_model
      = CheckReject
    ∧ check_syscall (fa_unmapped_in 8) (eff_errno EFAULT 1) fa_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- Rocq's `faccessat_bad_mode_records_no_copyin`
(`Checks/Cases/Fs/Open.v`) through `check_syscall`: the first conjunct is
Rocq's statement, and the other two are added;
the row pin `faccessat_bad_mode_records_no_copyin` above says why.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat_bad_mode_records_no_copyin_over_the_real_table :
    check_syscall (faccessat_in [97] 8) (eff_errno EINVAL 2) fa_model = CheckReject
    ∧ check_syscall (faccessat_in [97] 8) (eff_errno EINVAL 1) fa_model = CheckReject
    ∧ check_syscall (faccessat_in [97] 8) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- Rocq's `faccessat_existence_needs_the_copyin`
(`Checks/Cases/Fs/Open.v`) through `check_syscall`, as Rocq states it;
the row pin `faccessat_existence_needs_the_copyin` above says why.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem faccessat_existence_needs_the_copyin_over_the_real_table :
    check_syscall (faccessat_in [97] 0) (mkEffect 0 [] []) fa_model = CheckReject :=
  rfl

/-- Rocq's `faccessat2_accepted_flags_change_no_answer`
(`Checks/Cases/Fs/Open.v`) through `check_syscall`, as Rocq states it;
the row pin `faccessat2_accepted_flags_change_no_answer` above says why.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat2_accepted_flags_change_no_answer_over_the_real_table :
    check_syscall (faccessat2_in [97] 0 0) (eff_ret 0 2) fa_model = CheckOk fa_model []
    ∧ check_syscall (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_ret 0 2) fa_model
      = CheckOk fa_model []
    ∧ check_syscall (faccessat2_in [97] 0 (Z_to_bv 64 AT_SYMLINK_NOFOLLOW)) (eff_ret 0 2)
        fa_model = CheckOk fa_model []
    ∧ check_syscall (faccessat2_in [97] 0 (Z_to_bv 64 (AT_EACCESS + AT_SYMLINK_NOFOLLOW)))
        (eff_ret 0 2) fa_model = CheckOk fa_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Rocq's `faccessat2_empty_path_flag_declined_either_way`
(`Checks/Cases/Fs/Open.v`) through `check_syscall`, as Rocq states it;
the row pin `faccessat2_empty_path_flag_declined_either_way` above says why.
kernel: fs/open.c:do_faccessat; fs/namei.c:getname_flags@v6.18.46 -/
theorem faccessat2_empty_path_flag_declined_either_way_over_the_real_table :
    check_syscall (faccessat2_in [97] 0 (Z_to_bv 64 AT_EMPTY_PATH)) (eff_ret 0 2) fa_model
      = CheckUnmodeled
    ∧ check_syscall (faccessat2_in [97] 0 (Z_to_bv 64 AT_EMPTY_PATH)) (eff_errno ENOENT 2)
        fa_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- Rocq's `faccessat2_bad_flag_records_no_copyin`
(`Checks/Cases/Fs/Open.v`) through `check_syscall`, as Rocq states it;
the row pin `faccessat2_bad_flag_records_no_copyin` above says why.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat2_bad_flag_records_no_copyin_over_the_real_table :
    check_syscall (faccessat2_in [97] 0 1024) (mkEffect (errno_ret EINVAL) [] []) fa_model
      = CheckOk fa_model []
    ∧ check_syscall (faccessat2_in [97] 0 1024) (eff_errno EINVAL 2) fa_model
      = CheckReject :=
  ⟨rfl, rfl⟩

/-- Rocq's `faccessat2_implied_directory_unmodeled`
(`Checks/Cases/Fs/Open.v`) through `check_syscall`, as Rocq states it;
the row pin `faccessat2_implied_directory_unmodeled` above says why.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem faccessat2_implied_directory_unmodeled_over_the_real_table :
    check_syscall (faccessat2_in [97] 0 (Z_to_bv 64 AT_EACCESS)) (eff_ret 0 2)
        fa_under_model = CheckUnmodeled :=
  rfl

end V_Fs_Open_faccessat


section OpenatThroughTheTable

/-! ## The openat pins through the real table

The pins above apply `check_openat_row`, the row for 56 written out.
This section states again through `check_syscall` the ones that stand
for the Rocq openat examples of the header's first list, as Rocq states
them, and three pins that stand for none of them:
`dirfd_is_narrowed_to_int`;
`empty_path_beats_rdwr_append_excl_and_nonblock`, whose flag words the
corpus passes with the empty path only under probes the openat register
forgives every decline under, so that the replay would file a
regression declining that shape as declared; and
`o_nonblock_dot_and_absent_name_land_where_read_does`, for the same
reason, on "." and an absent name under 2048.  The other pins above stay
on the row, among them `openat_append_flag_word`,
`openat_rdwr_flag_words`, `openat_rdwr_errnos` and `openat_rdwr_dirref`,
the four the header names, whose errno halves the last section of this
file states again through the dispatcher.  `check_syscall_openat_in'` finds
`arm_openat` (`Checks/Arms/Fs/Open.lean`) at 56 and unfolds its
`ca_check` to `check_openat_row`, and `check_syscall_openat_in` is the
same over the ordinary call.  Each twin is its pin's statement with the
dispatch in place of the row, named `<pin>_over_the_real_table`, with
three exceptions.  `check_openat_dir_name_max_bound`'s restates only the
conjuncts stated on the row (its docstring says why).
`neighbouring_words_decline_with_or_without_o_nonblock_over_the_real_table`
states two pins as one, `bare_o_noctty_declines_on_a_held_name`'s leg
and then `neighbouring_words_decline_with_or_without_o_nonblock`'s
five, which together are the six decline legs of Rocq's
`o_nonblock_is_an_ignored_open_flag` in its order, and is named for the
second.  And `openat_dirfd_whole_word_lie_rejected_over_the_real_table`
restates no pin on the row (the next paragraph).  Where the pin names
the Rocq example it restates, the twin's docstring names it too.

The row's narrowing of the dirfd is pinned both ways through the table.
`dirfd_is_narrowed_to_int_over_the_real_table` answers the dirfd with
bit 32 set as `AT_FDCWD`, and
`openat_dirfd_whole_word_lie_rejected_over_the_real_table`, which no
pin on the row stands behind, refuses a non-lowest descriptor there.  A
row handing the dirfd over whole would decline that call
(`the_openat_checker_itself_reads_the_whole_dirfd`). -/

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table (arm_openat ca_check_arm_openat)
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs (check_syscall check_syscall_of_found)

/-- The dispatch at 56 is the openat row: `lookup_ca` finds `arm_openat`
for the number `openat_in'` carries, and `arm_openat.ca_check` is
`check_openat` at `fd32 a0`, `a1`, `a2`, which is `check_openat_row`.
This is the table-side reading of `SYSCALL_DEFINE4(openat, int, dfd, …)`
(fs/open.c:1463-1464, Linux v6.18.46).
kernel: fs/open.c:openat@v6.18.46 -/
theorem check_syscall_openat_in' (dirfd pathp flags : word) (mem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (openat_in' dirfd pathp flags mem) eff m
      = check_openat_row (openat_in' dirfd pathp flags mem) eff m := by
  rw [check_syscall_of_found _ _ _ arm_openat rfl, ca_check_arm_openat]
  rfl

/-- The same over the ordinary call, `openat(AT_FDCWD, 8192, flags, 0644)`.
kernel: fs/open.c:openat@v6.18.46 -/
theorem check_syscall_openat_in (bs : List byte) (flags : word) (eff : SyscallEffect)
    (m : Model) :
    check_syscall (openat_in bs flags) eff m = check_openat_row (openat_in bs flags) eff m :=
  check_syscall_openat_in' _ _ _ _ eff m

/-- `bare_o_noctty_declines_on_a_held_name` and
`neighbouring_words_decline_with_or_without_o_nonblock` through
`check_syscall`: their statements with the dispatch in place of
`check_openat_row`, closed by `check_syscall_openat_in`. Rocq: the six
decline legs of `o_nonblock_is_an_ignored_open_flag`, in its order.
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem neighbouring_words_decline_with_or_without_o_nonblock_over_the_real_table :
    check_syscall (openat_in [102] 256) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_syscall (openat_in [102] 2304) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_syscall (openat_in [102] 1024) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_syscall (openat_in [102] 1026) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_syscall (openat_in [102] 130) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_syscall (openat_in [102] 65538) (eff_ret 3 2) have_model = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact ⟨bare_o_noctty_declines_on_a_held_name,
    neighbouring_words_decline_with_or_without_o_nonblock⟩

/-- `ignored_bits_land_where_read_does` through `check_syscall`: its statement
with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `o_nonblock_is_an_ignored_open_flag`.
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem ignored_bits_land_where_read_does_over_the_real_table :
    check_syscall (openat_in [102] 559104) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs)) []
    ∧ check_syscall (openat_in [102] 2625) (eff_ret 3 2) have_model
      = check_syscall (openat_in [102] 577) (eff_ret 3 2) have_model
    ∧ check_syscall (openat_in [97] 2241) (eff_ret 3 2) absent_model
      = check_syscall (openat_in [97] 193) (eff_ret 3 2) absent_model
    ∧ check_syscall (openat_in [97] 2753) (eff_ret 3 2) absent_model
      = check_syscall (openat_in [97] 705) (eff_ret 3 2) absent_model
    ∧ check_syscall (openat_in [102] 2625) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFileW [102] 0) :: init_fds) (fs := [([102], [])])) []
    ∧ check_syscall (openat_in [97] 2241) (eff_ret 3 2) absent_model
      = CheckOk (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])])) [] := by
  simp only [check_syscall_openat_in]
  exact ignored_bits_land_where_read_does

/-- `o_nonblock_dot_and_absent_name_land_where_read_does` through
`check_syscall`: its statement with the dispatch in place of
`check_openat_row`, closed by `check_syscall_openat_in`.  The replay
reaches these two shapes under 2048 only under a probe the openat
register forgives every decline under, so this is the pin on them
through the table.
kernel: fs/namei.c:may_open,traverse_mounts; fs/file.c:alloc_fd@v6.18.46 -/
theorem o_nonblock_dot_and_absent_name_land_where_read_does_over_the_real_table :
    check_syscall (openat_in [46] 2048) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) []
    ∧ check_syscall (openat_in [46] 2048) (eff_ret 4 2) absent_model = CheckReject
    ∧ check_syscall (openat_in [46] 2048) (eff_errno EISDIR 2) absent_model = CheckReject
    ∧ check_syscall (openat_in [97] 2048) (eff_errno ENOENT 2) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in [97] 2048) (eff_ret 3 2) absent_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact o_nonblock_dot_and_absent_name_land_where_read_does

/-- `empty_path_is_the_fetch_enoent_not_a_lookup` through `check_syscall`: its
statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq's `openat_empty_path_enoent` runs over
exactly that image, so that a checker consulting the map before the
empty-string gate fails here.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_is_the_fetch_enoent_not_a_lookup_over_the_real_table :
    check_syscall (openat_in [] 0) (eff_errno ENOENT 1) empty_key_model
        = CheckOk empty_key_model []
    ∧ check_syscall (openat_in [] 0) (eff_ret 3 1) empty_key_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact empty_path_is_the_fetch_enoent_not_a_lookup

/-- `empty_path_beats_o_creat` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_empty_path_beats_o_creat`.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_beats_o_creat_over_the_real_table :
    check_syscall (openat_in [] 577) (eff_errno ENOENT 1) absent_model = CheckOk absent_model []
    ∧ check_syscall (openat_in [] 577) (eff_ret 3 1) absent_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact empty_path_beats_o_creat

/-- `empty_path_beats_rdwr_append_excl_and_nonblock` through `check_syscall`:
its statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.  The replay reaches this shape only under
probes the openat register forgives every decline under, so this is the
pin on it through the table.
kernel: fs/namei.c:getname_flags,do_open,may_open@v6.18.46 -/
theorem empty_path_beats_rdwr_append_excl_and_nonblock_over_the_real_table :
    check_syscall (openat_in [] 2) (eff_errno ENOENT 1) absent_model = CheckOk absent_model []
    ∧ check_syscall (openat_in [] 2) (eff_errno EISDIR 1) absent_model = CheckReject
    ∧ check_syscall (openat_in [] 2) (eff_ret 3 1) absent_model = CheckReject
    ∧ check_syscall (openat_in [] 1089) (eff_errno ENOENT 1) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in [] 1089) (eff_errno EISDIR 1) absent_model = CheckReject
    ∧ check_syscall (openat_in [] 1089) (eff_ret 3 1) absent_model = CheckReject
    ∧ check_syscall (openat_in [] 705) (eff_errno ENOENT 1) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in [] 705) (eff_errno EEXIST 1) absent_model = CheckReject
    ∧ check_syscall (openat_in [] 705) (eff_ret 3 1) absent_model = CheckReject
    ∧ check_syscall (openat_in [] 2048) (eff_errno ENOENT 1) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in [] 2048) (eff_ret 3 1) absent_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact empty_path_beats_rdwr_append_excl_and_nonblock

/-- `live_dirfd_declines` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in'`. A live dirfd (1, an open channel) with a
non-empty plain name is `CheckUnmodeled`: `path_init` (fs/namei.c:2607-2622)
would answer -ENOTDIR for a non-directory dirfd (:2621-2622), and the model,
which resolves only from `AT_FDCWD`, declines rather than judges — refusing
the -ENOENT Rocq's case offers, the kernel's -ENOTDIR, and a descriptor
alike.  Rocq: `openat_live_dirfd_still_unmodeled`.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem live_dirfd_declines_over_the_real_table :
    check_syscall (openat_in' 1 8192 0 (open_path_mem [102])) (eff_errno ENOENT 2) have_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in' 1 8192 0 (open_path_mem [102])) (eff_errno ENOTDIR 2) have_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in' 1 8192 0 (open_path_mem [102])) (eff_ret 3 2) have_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in']
  exact live_dirfd_declines

/-- `dirfd_is_narrowed_to_int` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`, `check_syscall_openat_in'`.
kernel: fs/open.c:openat; fs/namei.c:path_init@v6.18.46 -/
theorem dirfd_is_narrowed_to_int_over_the_real_table :
    check_syscall (openat_in' 4294967196 8192 0 (open_path_mem [102])) (eff_ret 3 2) have_model
      = check_syscall (openat_in [102] 0) (eff_ret 3 2) have_model
    ∧ check_syscall (openat_in' 8589934492 8192 0 (open_path_mem [102])) (eff_ret 3 2) have_model
      = check_syscall (openat_in [102] 0) (eff_ret 3 2) have_model
    ∧ check_syscall (openat_in' 4294967196 8192 0 (open_path_mem [102])) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs)) [] := by
  simp only [check_syscall_openat_in, check_syscall_openat_in']
  exact dirfd_is_narrowed_to_int

/-- `slash_key_in_image_declines` through `check_syscall`: its statement with
the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_slash_key_in_image_unmodeled`.
kernel: fs/namei.c:link_path_walk,traverse_mounts@v6.18.46 -/
theorem slash_key_in_image_declines_over_the_real_table :
    check_syscall (openat_in [97, 47, 98] 0) (eff_ret 3 4) under_model = CheckUnmodeled
    ∧ check_syscall (openat_in [97, 47, 98] 0) (eff_errno ENOENT 4) under_model = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact slash_key_in_image_declines

/-- `dot_and_dotdot_read_as_directory_fds` through `check_syscall`: its
statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_dotdot_answers_as_dot_does`,
`openat_dot3_is_an_ordinary_name`.
kernel: fs/namei.c:link_path_walk,may_open@v6.18.46 -/
theorem dot_and_dotdot_read_as_directory_fds_over_the_real_table :
    check_syscall (openat_in [46] 0) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) []
    ∧ check_syscall (openat_in [46, 46] 0) (eff_ret 3 3) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) []
    ∧ check_syscall (openat_in [46] 0) (eff_ret 4 2) absent_model = CheckReject
    ∧ check_syscall (openat_in [46] 0) (eff_errno EISDIR 2) absent_model = CheckReject
    ∧ check_syscall (openat_in [46, 46, 46] 0) (eff_errno ENOENT 4) absent_model
        = CheckOk absent_model [] := by
  simp only [check_syscall_openat_in]
  exact dot_and_dotdot_read_as_directory_fds

/-- `dotdot_creates_as_dot_does_and_dot3_is_a_name` through `check_syscall`: its
statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_dotdot_answers_as_dot_does`,
`openat_dot3_is_an_ordinary_name`.
kernel: fs/namei.c:do_open,link_path_walk,lookup_open@v6.18.46 -/
theorem dotdot_creates_as_dot_does_and_dot3_is_a_name_over_the_real_table :
    check_syscall (openat_in [46, 46] 577) (eff_errno EISDIR 3) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in [46, 46] 577) (eff_ret 3 3) absent_model = CheckReject
    ∧ check_syscall (openat_in [46, 46, 46] 577) (eff_ret 3 4) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [46, 46, 46] 0) :: init_fds)
                              (fs := [([46, 46, 46], [])])) []
    ∧ check_syscall (openat_in [46, 46, 46] 577) (eff_errno EISDIR 4) absent_model
        = CheckReject := by
  simp only [check_syscall_openat_in]
  exact dotdot_creates_as_dot_does_and_dot3_is_a_name

/-- `create_absent_mints_the_key` through `check_syscall`: its statement with
the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_plain_create_still_mints_the_key`.
kernel: fs/namei.c:lookup_open,do_open; fs/file.c:alloc_fd@v6.18.46 -/
theorem create_absent_mints_the_key_over_the_real_table :
    check_syscall (openat_in [97] 577) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])])) []
    ∧ check_syscall (openat_in [97] 577) (eff_ret 4 2) absent_model = CheckReject
    ∧ check_syscall (openat_in [97] 577) (eff_errno ENOENT 2) absent_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact create_absent_mints_the_key

/-- `implied_directory_create_is_eisdir` through `check_syscall`: its statement
with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_implied_directory_create_eisdir`.
kernel: fs/namei.c:do_open,lookup_open@v6.18.46 -/
theorem implied_directory_create_is_eisdir_over_the_real_table :
    check_syscall (openat_in [97] 577) (eff_errno EISDIR 2) under_model = CheckOk under_model []
    ∧ check_syscall (openat_in [97] 577) (eff_ret 3 2) under_model = CheckReject
    ∧ check_syscall (openat_in [97] 577) (eff_errno EEXIST 2) under_model = CheckReject
    ∧ check_syscall (openat_in [46] 577) (eff_errno EISDIR 2) absent_model = CheckOk absent_model []
    ∧ check_syscall (openat_in [46] 577) (eff_ret 3 2) absent_model = CheckReject
    ∧ check_syscall (openat_in [99] 577) (eff_ret 3 2) under_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [99] 0) :: init_fds)
                              (fs := [([97, 47, 98], [104]), ([99], [])])) [] := by
  simp only [check_syscall_openat_in]
  exact implied_directory_create_is_eisdir

/-- `byte_prefix_and_exact_key_still_create` through `check_syscall`: its
statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq:
`openat_byte_prefix_and_exact_key_still_create`.
kernel: fs/namei.c:lookup_open,do_open@v6.18.46 -/
theorem byte_prefix_and_exact_key_still_create_over_the_real_table :
    check_syscall (openat_in [97] 577) (eff_errno EISDIR 2) sibling_model = CheckReject
    ∧ check_syscall (openat_in [97] 577) (eff_ret 3 2) sibling_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds)
                              (fs := [([97], []), ([97, 98], [104])])) []
    ∧ check_syscall (openat_in [97] 577) (eff_errno EISDIR 2) exact_model = CheckReject
    ∧ check_syscall (openat_in [97] 577) (eff_ret 3 2) exact_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])])) [] := by
  simp only [check_syscall_openat_in]
  exact byte_prefix_and_exact_key_still_create

/-- `implied_directory_excl_is_eexist` through `check_syscall`: its statement
with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_implied_directory_excl_eexist`.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem implied_directory_excl_is_eexist_over_the_real_table :
    check_syscall (openat_in [97] 193) (eff_errno EEXIST 2) under_model = CheckOk under_model []
    ∧ check_syscall (openat_in [97] 193) (eff_errno EISDIR 2) under_model = CheckReject
    ∧ check_syscall (openat_in [97] 193) (eff_ret 3 2) under_model = CheckReject
    ∧ check_syscall (openat_in [99] 193) (eff_ret 3 2) under_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [99] 0) :: init_fds)
                              (fs := [([97, 47, 98], [104]), ([99], [])])) [] := by
  simp only [check_syscall_openat_in]
  exact implied_directory_excl_is_eexist

/-- `openat_implied_directory_other_write_words` through `check_syscall`:
its statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.  Rocq:
`openat_implied_directory_other_write_words`.
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem implied_directory_other_write_words_over_the_real_table :
    check_syscall (openat_in [97] 1089) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_syscall (openat_in [97] 66) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_syscall (openat_in [97] 578) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_syscall (openat_in [97] 2) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_syscall (openat_in [97] 514) (eff_errno EISDIR 2) under_model
        = CheckOk under_model []
    ∧ check_syscall (openat_in [97] 194) (eff_errno EEXIST 2) under_model
        = CheckOk under_model []
    ∧ check_syscall (openat_in [97] 66) (eff_ret 3 2) under_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact openat_implied_directory_other_write_words

/-- `dir_word_answers` through `check_syscall`: its statement with the dispatch
in place of `check_openat_row`, closed by `check_syscall_openat_in`.  Its
-EMFILE conjunct is the class of refusal the header marks: a real answer
here (`do_sys_openat2` reserves the descriptor at fs/open.c:1435, Linux
v6.18.46, before the walk at :1437; `alloc_fd`, fs/file.c:591-593),
refused by the narrowing the header names, so it pins that narrowing and
not an impossibility.
kernel: fs/namei.c:do_open,traverse_mounts; fs/file.c:alloc_fd@v6.18.46 -/
theorem dir_word_answers_over_the_real_table :
    check_syscall (openat_in [46] 65536) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) []
    ∧ check_syscall (openat_in [46] 65536) (eff_ret 4 2) absent_model = CheckReject
    ∧ check_syscall (openat_in [102] 65536) (eff_errno ENOTDIR 2) have_model = CheckOk have_model []
    ∧ check_syscall (openat_in [102] 65536) (eff_ret 3 2) have_model = CheckReject
    ∧ check_syscall (openat_in [102] 65536) (eff_errno EMFILE 2) have_model = CheckReject
    ∧ check_syscall (openat_in [97] 65536) (eff_errno ENOENT 2) absent_model = CheckOk absent_model []
    ∧ check_syscall (openat_in [97] 65536) (eff_ret 3 2) absent_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact dir_word_answers

/-- `dir_word_ignores_largefile_and_cloexec` through `check_syscall`: its
statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq:
`openat_directory_ignores_largefile_and_cloexec`.
kernel: fs/open.c:build_open_flags; fs/namei.c:do_open,traverse_mounts@v6.18.46 -/
theorem dir_word_ignores_largefile_and_cloexec_over_the_real_table :
    check_syscall (openat_in [46] 622592) (eff_ret 3 2) absent_model
        = check_syscall (openat_in [46] 65536) (eff_ret 3 2) absent_model
    ∧ check_syscall (openat_in [46, 46] 622592) (eff_ret 3 3) absent_model
        = check_syscall (openat_in [46, 46] 65536) (eff_ret 3 3) absent_model
    ∧ check_syscall (openat_in [102] 622592) (eff_errno ENOTDIR 2) have_model
        = check_syscall (openat_in [102] 65536) (eff_errno ENOTDIR 2) have_model
    ∧ check_syscall (openat_in [97] 622592) (eff_errno ENOENT 2) absent_model
        = check_syscall (openat_in [97] 65536) (eff_errno ENOENT 2) absent_model
    ∧ check_syscall (openat_in [46] 622592) (eff_ret 3 2) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDir) :: init_fds)) [] := by
  simp only [check_syscall_openat_in]
  exact dir_word_ignores_largefile_and_cloexec

/-- `dir_word_implied_directory_declines` through `check_syscall`: its statement
with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.
kernel: fs/namei.c:link_path_walk,traverse_mounts@v6.18.46 -/
theorem dir_word_implied_directory_declines_over_the_real_table :
    check_syscall (openat_in [97] 65536) (eff_ret 3 2) under_model = CheckUnmodeled
    ∧ check_syscall (openat_in [97] 65536) (eff_errno ENOENT 2) under_model = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact dir_word_implied_directory_declines

set_option maxRecDepth 8192 in
/-- `check_openat_dir_name_max_bound`'s last two conjuncts through
`check_syscall`: the two names with the dispatch in place of
`check_openat_row`, closed by `check_syscall_openat_in`.  Its first three
are stated on the arm `check_openat_dir`, which the table reaches only
through the row, so they have no statement over the table to restate.
Rocq: `openat_directory_name_max_boundary`.
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup; fs/namei.c:traverse_mounts@v6.18.46 -/
theorem check_openat_dir_name_max_bound_over_the_real_table :
    check_syscall (openat_in name256 65536) (eff_errno ENOENT 257) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in name255 65536) (eff_errno ENOENT 256) absent_model
        = CheckOk absent_model [] := by
  simp only [check_syscall_openat_in]
  exact check_openat_dir_name_max_bound.2.2.2

/-- `localtime_every_read_word_is_enoent` through `check_syscall`: its statement
with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_localtime_enoent`.
kernel: fs/namei.c:traverse_mounts,lookup_open@v6.18.46 -/
theorem localtime_every_read_word_is_enoent_over_the_real_table :
    check_syscall (openat_in localtime_path 526336) (eff_errno ENOENT 15) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in localtime_path 2) (eff_errno ENOENT 15) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in localtime_path 514) (eff_errno ENOENT 15) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in localtime_path 65536) (eff_errno ENOENT 15) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in localtime_path 2) (eff_ret 3 15) absent_model = CheckReject
    ∧ check_syscall (openat_in localtime_path 1089) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in localtime_path 66) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in localtime_path 194) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact localtime_every_read_word_is_enoent

/-- `localtime_match_is_exact` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_localtime_match_is_exact`.
kernel: fs/namei.c:link_path_walk,traverse_mounts@v6.18.46 -/
theorem localtime_match_is_exact_over_the_real_table :
    check_syscall (openat_in [47, 101, 116, 99, 47, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] 0)
        (eff_errno ENOENT 16) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] 0)
        (eff_errno ENOENT 16) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109] 0)
        (eff_errno ENOENT 14) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in (localtime_path ++ [115]) 0) (eff_errno ENOENT 16) absent_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact localtime_match_is_exact

/-- `localtime_declines` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.
kernel: fs/namei.c:lookup_open,link_path_walk@v6.18.46 -/
theorem localtime_declines_over_the_real_table :
    check_syscall (openat_in localtime_path 577) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in localtime_path 577) (eff_ret 3 15) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in localtime_path 193) (eff_errno ENOENT 15) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in localtime_path 0) (eff_errno ENOENT 15) localtime_key_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in localtime_path 0) (eff_ret 3 15) localtime_key_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in localtime_path 0) (eff_errno ENOENT 15) localtime_under_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact localtime_declines

/-- `devnull_open_by_word` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.
kernel: fs/namei.c:may_open,do_open; drivers/char/mem.c:memory_open; fs/file.c:alloc_fd@v6.18.46 -/
theorem devnull_open_by_word_over_the_real_table :
    check_syscall (openat_in devnull_path 0) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true false) :: init_fds)) []
    ∧ check_syscall (openat_in devnull_path 577) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull false true) :: init_fds)) []
    ∧ check_syscall (openat_in devnull_path 1089) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull false true) :: init_fds)) []
    ∧ check_syscall (openat_in devnull_path 2) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true true) :: init_fds)) []
    ∧ check_syscall (openat_in devnull_path 193) (eff_errno EEXIST 10) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in devnull_path 194) (eff_errno EEXIST 10) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in devnull_path 193) (eff_ret 3 10) absent_model = CheckReject
    ∧ check_syscall (openat_in devnull_path 65536) (eff_errno ENOTDIR 10) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in devnull_path 65536) (eff_ret 3 10) absent_model = CheckReject
    ∧ check_syscall (openat_in devnull_path 0) (eff_ret 4 10) absent_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact devnull_open_by_word

/-- `devnull_rest_of_the_word_table_and_exact_match` through `check_syscall`:
its statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: the remaining legs of
`devnull_open_by_word` and `devnull_open_declines`.
kernel: fs/namei.c:may_open,do_open,link_path_walk@v6.18.46 -/
theorem devnull_rest_of_the_word_table_and_exact_match_over_the_real_table :
    check_syscall (openat_in devnull_path 514) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true true) :: init_fds)) []
    ∧ check_syscall (openat_in devnull_path 66) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true true) :: init_fds)) []
    ∧ check_syscall (openat_in devnull_path 578) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true true) :: init_fds)) []
    ∧ check_syscall (openat_in devnull_path 705) (eff_errno EEXIST 10) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in devnull_path 706) (eff_errno EEXIST 10) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in devnull_path 524288) (eff_ret 3 10) absent_model
        = CheckOk (fixture_of (fds := (3, .FdDevNull true false) :: init_fds)) []
    ∧ check_syscall (openat_in [47, 100, 101, 118, 47, 110, 117, 108] 0) (eff_ret 3 9)
        absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 100, 101, 118, 47, 47, 110, 117, 108, 108] 0) (eff_ret 3 11)
        absent_model = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact devnull_rest_of_the_word_table_and_exact_match

/-- `devnull_open_declines` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.
kernel: fs/namei.c:link_path_walk,traverse_mounts@v6.18.46 -/
theorem devnull_open_declines_over_the_real_table :
    check_syscall (openat_in devnull_path 0) (eff_ret 3 10) devnull_key_model = CheckUnmodeled
    ∧ check_syscall (openat_in devnull_path 0) (eff_errno ENOENT 10) devnull_key_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in devnull_path 0) (eff_ret 3 10) devnull_under_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact devnull_open_declines

/-- `urandom_open_by_word` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.
kernel: fs/namei.c:may_open,do_open; drivers/char/mem.c:memory_open; fs/file.c:alloc_fd@v6.18.46 -/
theorem urandom_open_by_word_over_the_real_table :
    check_syscall (openat_in urandom_path 0) (eff_ret 3 13) absent_model
        = CheckOk (fixture_of (fds := (3, .FdUrandom) :: init_fds)) []
    ∧ check_syscall (openat_in urandom_path 0) (eff_ret 4 13) absent_model = CheckReject
    ∧ check_syscall (openat_in urandom_path 193) (eff_errno EEXIST 13) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in urandom_path 193) (eff_ret 3 13) absent_model = CheckReject
    ∧ check_syscall (openat_in urandom_path 65536) (eff_errno ENOTDIR 13) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in urandom_path 65536) (eff_ret 3 13) absent_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact urandom_open_by_word

/-- `urandom_rdwr_excl_is_eexist_and_the_rest_declines` through `check_syscall`:
its statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: the remaining legs of
`urandom_open_by_word`.
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem urandom_rdwr_excl_is_eexist_and_the_rest_declines_over_the_real_table :
    check_syscall (openat_in urandom_path 194) (eff_errno EEXIST 13) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in urandom_path 706) (eff_errno EEXIST 13) absent_model
        = CheckOk absent_model []
    ∧ check_syscall (openat_in urandom_path 194) (eff_ret 3 13) absent_model = CheckReject
    ∧ check_syscall (openat_in urandom_path 524288) (eff_ret 3 13) absent_model
        = CheckOk (fixture_of (fds := (3, .FdUrandom) :: init_fds)) []
    ∧ check_syscall (openat_in urandom_path 514) (eff_ret 3 13) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in urandom_path 578) (eff_ret 3 13) absent_model = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact urandom_rdwr_excl_is_eexist_and_the_rest_declines

/-- `excl_append_word_on_the_devices` through `check_syscall`: its statement
with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem excl_append_word_on_the_devices_over_the_real_table :
    check_syscall (openat_in devnull_path 1217) (eff_errno EEXIST 10) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in devnull_path 1729) (eff_errno EEXIST 10) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in devnull_path 1217) (eff_ret 3 10) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in urandom_path 1217) (eff_errno EEXIST 13) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in urandom_path 1729) (eff_errno EEXIST 13) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in urandom_path 1217) (eff_ret 3 13) absent_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact excl_append_word_on_the_devices

/-- `urandom_open_declines` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.
kernel: fs/namei.c:may_open,link_path_walk@v6.18.46 -/
theorem urandom_open_declines_over_the_real_table :
    check_syscall (openat_in urandom_path 577) (eff_ret 3 13) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in urandom_path 1089) (eff_ret 3 13) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in urandom_path 2) (eff_ret 3 13) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in urandom_path 0) (eff_ret 3 13) urandom_key_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in urandom_path 0) (eff_ret 3 13) urandom_under_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact urandom_open_declines

/-- `tmp_create_and_read` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`.
kernel: fs/namei.c:lookup_open,do_open,may_open; fs/file_table.c:init_file@v6.18.46 -/
theorem tmp_create_and_read_over_the_real_table :
    check_syscall (openat_in [47, 116, 109, 112, 47, 120] 577) (eff_ret 3 7) absent_model
        = CheckOk (fixture_of (fds := (3, .FdFileW [47, 116, 109, 112, 47, 120] 0) :: init_fds)
                              (fs := [([47, 116, 109, 112, 47, 120], [])])) []
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 120] 577) (eff_errno ENOENT 7) absent_model
        = CheckReject
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 120] 0) (eff_ret 3 7) tmp_held_model
        = CheckOk (fixture_of (fds := (3, .FdFile [47, 116, 109, 112, 47, 120] 0) :: init_fds)
                              (fs := tmp_held_fs)) []
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 120] 0) (eff_errno ENOENT 7) tmp_held_model
        = CheckReject := by
  simp only [check_syscall_openat_in]
  exact tmp_create_and_read

/-- `tmp_declared_name_reads` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_tmp_declared_name_reads`.
kernel: fs/namei.c:may_open; fs/file_table.c:init_file@v6.18.46 -/
theorem tmp_declared_name_reads_over_the_real_table :
    check_syscall (openat_in (tmp_key [120]) 0) (eff_ret 3 7) tmp_seeded_model
        = CheckOk (fixture_of (fds := (3, .FdFile (tmp_key [120]) 0) :: init_fds)
                              (fs := [(tmp_key [120], [104])])) []
    ∧ check_syscall (openat_in (tmp_key [120]) 0) (eff_errno ENOENT 7) tmp_seeded_model
        = CheckReject := by
  simp only [check_syscall_openat_in]
  exact tmp_declared_name_reads

/-- `tmp_ignored_bits_reach_the_arm` through `check_syscall`: its statement with
the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: the ignored-bit legs of
`openat_tmp_create_read_unlink`.
kernel: fs/open.c:build_open_flags,openat@v6.18.46 -/
theorem tmp_ignored_bits_reach_the_arm_over_the_real_table :
    check_syscall (openat_in (tmp_key [120]) 524865) (eff_ret 3 7) absent_model
      = check_syscall (openat_in (tmp_key [120]) 577) (eff_ret 3 7) absent_model
    ∧ check_syscall (openat_in (tmp_key [120]) 2625) (eff_ret 3 7) absent_model
      = check_syscall (openat_in (tmp_key [120]) 577) (eff_ret 3 7) absent_model
    ∧ check_syscall (openat_in (tmp_key [120]) 33345) (eff_ret 3 7) absent_model
      = check_syscall (openat_in (tmp_key [120]) 577) (eff_ret 3 7) absent_model
    ∧ check_syscall (openat_in (tmp_key [120]) 524865) (eff_ret 3 7) absent_model
      = CheckOk (fixture_of (fds := (3, .FdFileW (tmp_key [120]) 0) :: init_fds)
                            (fs := [(tmp_key [120], [])])) []
    ∧ check_syscall (openat_in (tmp_key [120]) 524288) (eff_ret 3 7) tmp_held_model
      = CheckOk (fixture_of (fds := (3, .FdFile (tmp_key [120]) 0) :: init_fds)
                            (fs := tmp_held_fs)) [] := by
  simp only [check_syscall_openat_in]
  exact tmp_ignored_bits_reach_the_arm

set_option maxRecDepth 8192 in
/-- `tmp_name_max_boundary` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_tmp_name_max_boundary`.
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup; fs/namei.c:lookup_open@v6.18.46 -/
theorem tmp_name_max_boundary_over_the_real_table :
    check_syscall (openat_in (tmp_key name255) 577) (eff_ret 3 261) absent_model
      = CheckOk (fixture_of (fds := (3, .FdFileW (tmp_key name255) 0) :: init_fds)
                            (fs := [(tmp_key name255, [])])) []
    ∧ check_syscall (openat_in (tmp_key name255) 0) (eff_ret 3 261) tmp_name255_held_model
      = CheckOk (fixture_of (fds := (3, .FdFile (tmp_key name255) 0) :: init_fds)
                            (fs := tmp_name255_held_fs)) []
    ∧ check_syscall (openat_in (tmp_key name256) 577) (eff_ret 3 262) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in (tmp_key name256) 0) (eff_errno ENOENT 262) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in (tmp_key name256) 577) (eff_errno ENAMETOOLONG 262) absent_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact tmp_name_max_boundary

/-- `tmp_implied_directory_create_eisdir` through `check_syscall`: its statement
with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq:
`openat_tmp_implied_directory_create_eisdir`.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_implied_directory_create_eisdir_over_the_real_table :
    check_syscall (openat_in (tmp_key [100]) 577) (eff_errno EISDIR 7) tmp_dir_model
        = CheckOk tmp_dir_model []
    ∧ check_syscall (openat_in (tmp_key [100]) 577) (eff_ret 3 7) tmp_dir_model = CheckReject
    ∧ check_syscall (openat_in (tmp_key [100]) 577) (eff_errno 2 7) tmp_dir_model
        = CheckReject := by
  simp only [check_syscall_openat_in]
  exact tmp_implied_directory_create_eisdir

/-- `tmp_implied_directory_read_unmodeled` through `check_syscall`: its
statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq:
`openat_tmp_implied_directory_read_unmodeled`.
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_implied_directory_read_unmodeled_over_the_real_table :
    check_syscall (openat_in (tmp_key [100]) 0) (eff_ret 3 7) tmp_dir_model = CheckUnmodeled
    ∧ check_syscall (openat_in (tmp_key [100]) 0) (eff_errno EISDIR 7) tmp_dir_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in (tmp_key [100, 47, 102]) 0) (eff_ret 3 9) tmp_dir_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in (tmp_key [100, 47, 102]) 577) (eff_ret 3 9) tmp_dir_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact tmp_implied_directory_read_unmodeled

/-- `tmp_implied_directory_unrealizable_image` through `check_syscall`: its
statement with the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq:
`openat_tmp_implied_directory_unrealizable_image`.
kernel: fs/namei.c:may_open,do_open@v6.18.46 -/
theorem tmp_implied_directory_unrealizable_image_over_the_real_table :
    check_syscall (openat_in (tmp_key [100]) 0) (eff_ret 3 7) tmp_unreal_model = CheckUnmodeled
    ∧ check_syscall (openat_in (tmp_key [100]) 0) (eff_errno 2 7) tmp_unreal_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in (tmp_key [100]) 577) (eff_errno EISDIR 7) tmp_unreal_model
        = CheckOk tmp_unreal_model []
    ∧ check_syscall (openat_in (tmp_key [100]) 577) (eff_ret 3 7) tmp_unreal_model
        = CheckReject := by
  simp only [check_syscall_openat_in]
  exact tmp_implied_directory_unrealizable_image

/-- `tmp_excluded_shapes_decline` through `check_syscall`: its statement with
the dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. Rocq: `openat_tmp_excluded_shapes_unmodeled`.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_excluded_shapes_decline_over_the_real_table :
    check_syscall (openat_in (tmp_key [120]) 578) (eff_ret 3 7) tmp_held_model = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47] 0) (eff_ret 3 6) tmp_held_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 46] 0) (eff_ret 3 7) tmp_held_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 46, 46] 0) (eff_ret 3 8) tmp_held_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112, 102, 111, 111] 577) (eff_ret 3 8) absent_model
        = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact tmp_excluded_shapes_decline

/-- `tmp_and_slash_declines` through `check_syscall`: its statement with the
dispatch in place of `check_openat_row`, closed by
`check_syscall_openat_in`. The read word on a name the run does not hold
declines (Linux would answer -ENOENT or open a file another process made);
the exclusive, directory and append words decline on a held name — the
first two at the -EEXIST and -ENOTDIR `do_open` answers them with
(fs/namei.c:3949-3950 and :3958-3959), the append word at the descriptor;
a second component ("/tmp/d/f") and "/tmp" itself decline; and an
absolute plain key ("/a") under the create word declines — Rocq's
`openat_absolute_create_unmodeled`.
kernel: fs/namei.c:traverse_mounts,link_path_walk,do_open@v6.18.46 -/
theorem tmp_and_slash_declines_over_the_real_table :
    check_syscall (openat_in [47, 116, 109, 112, 47, 120] 0) (eff_errno ENOENT 7) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 120] 0) (eff_ret 3 7) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 120] 193) (eff_errno EEXIST 7) tmp_held_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 120] 65536) (eff_errno ENOTDIR 7)
        tmp_held_model = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 120] 1089) (eff_ret 3 7) tmp_held_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112, 47, 100, 47, 102] 0) (eff_ret 3 9)
        tmp_dir_model = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 116, 109, 112] 0) (eff_ret 3 5) absent_model
        = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 97] 577) (eff_ret 3 3) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in [47, 97] 577) (eff_errno ENOENT 3) absent_model = CheckUnmodeled := by
  simp only [check_syscall_openat_in]
  exact tmp_and_slash_declines

/-- THE NARROWING IS THE ROW'S, NOT THE CHECKER'S: handed the dirfd word
with bit 32 set as it is, `check_openat` compares it with `AT_FDCWD32`
(`fd32 AT_FDCWD`, the low half of `AT_FDCWD` zero-extended), finds another
word, and declines.  `check_openat_body` declines every dirfd but
`AT_FDCWD32` once the pathname is fetched, so the bare checker declines the
64-bit -100, `AT_FDCWD` itself, as well: the second conjunct.
`SYSCALL_DEFINE4(openat, int, dfd, …)` (fs/open.c:1463-1464, Linux
v6.18.46) reads the low 32 bits of either word, which are `AT_FDCWD`'s.
model: `check_openat` compares its dirfd argument, unnarrowed, with `AT_FDCWD32` (`fd32 AT_FDCWD`), and the row's `fd32` does the narrowing; a claim about this tree, not about Linux -/
theorem the_openat_checker_itself_reads_the_whole_dirfd :
    check_openat (openat_in' 8589934492 8192 0 (open_path_mem [102])) 8589934492 8192 0
        (eff_ret 4 2) have_model
      = CheckUnmodeled
    ∧ check_openat (openat_in [102] 0) AT_FDCWD 8192 0 (eff_ret 3 2) have_model
      = CheckUnmodeled := ⟨rfl, rfl⟩

/-- THE NARROWING'S REFUSAL: through the dispatch, the dirfd with bit 32
set is `AT_FDCWD`, so "f" opens at the lowest free descriptor, 3, and a
kernel answering 4 is refused — `alloc_fd` (fs/file.c:570-613, Linux
v6.18.46) hands out the lowest free descriptor, and 3 is the lowest
descriptor `have_model` leaves free.  A row that handed the dirfd to
`check_openat` whole would decline this call
(`the_openat_checker_itself_reads_the_whole_dirfd`), so this pin fails
when the row drops `fd32`.  Lean-only.
kernel: fs/open.c:openat; fs/file.c:alloc_fd@v6.18.46 -/
theorem openat_dirfd_whole_word_lie_rejected_over_the_real_table :
    check_syscall (openat_in' 8589934492 8192 0 (open_path_mem [102])) (eff_ret 4 2) have_model
      = CheckReject := by
  simp only [check_syscall_openat_in']
  rfl

end OpenatThroughTheTable

section CloseThroughTheTable

/-! ## The close row pins through the real table

`check_syscall_close_in` finds `arm_close` (`Checks/Arms/Fs/Open.lean`) at
57 and unfolds its `ca_check` to `check_close_row`; the two pins of the
row section above, `row_57_closes_the_fd` and
`row_57_fd_truncates_to_32_bits`, are restated on it.
`row_57_fd_truncates_to_32_bits_over_the_real_table`
refuses, at a0 = 2^32 + 3, the -EBADF that a row handing a0 over whole
would accept (`the_close_checker_itself_reads_the_whole_word`). -/

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table (arm_close ca_check_arm_close)
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs (check_syscall check_syscall_of_found)

/-- The dispatch at 57 is the close row: `lookup_ca` finds `arm_close` for
the number the input carries, and `arm_close.ca_check` is `check_close` at
`fd32 a0`, which is `check_close_row`.  This is the table-side reading of
`SYSCALL_DEFINE1(close, unsigned int, fd)` (fs/open.c:1574, Linux
v6.18.46).
kernel: fs/open.c:close@v6.18.46 -/
theorem check_syscall_close_in (a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 57 [a0, a1, a2, a3, a4, a5] mem wmem) eff m
      = check_close_row (SyscallInput.mkInput 57 [a0, a1, a2, a3, a4, a5] mem wmem) eff m := by
  rw [check_syscall_of_found _ _ _ arm_close rfl, ca_check_arm_close]
  rfl

/-- The same over `close_call`.
kernel: fs/open.c:close@v6.18.46 -/
theorem check_syscall_close_call (fd : word) (eff : SyscallEffect) (m : Model) :
    check_syscall (close_call fd) eff m = check_close_row (close_call fd) eff m :=
  check_syscall_close_in _ _ _ _ _ _ _ _ eff m

/-- `row_57_closes_the_fd` through `check_syscall`: its statement with the
dispatch in place of `check_close_row`, closed by
`check_syscall_close_call`, `check_syscall_close_in`.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem row_57_closes_the_fd_over_the_real_table :
    check_syscall (close_call 3) (mkEffect 0 [] []) close_model = CheckOk after_close_3 []
    ∧ check_syscall (close_call 10) (mkEffect (errno_ret EBADF) [] []) close_model
        = CheckOk close_model []
    ∧ check_syscall (SyscallInput.mkInput 57 [3, 7, 7, 7, 7, 7] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) close_model = CheckOk after_close_3 [] := by
  simp only [check_syscall_close_call, check_syscall_close_in]
  exact row_57_closes_the_fd

/-- `row_57_fd_truncates_to_32_bits` through `check_syscall`: its statement with
the dispatch in place of `check_close_row`, closed by
`check_syscall_close_call`.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:close@v6.18.46 -/
theorem row_57_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (close_call (Z_to_bv 64 (2 ^ 32 + 3))) (mkEffect 0 [] []) close_model
        = CheckOk after_close_3 []
    ∧ check_syscall (close_call (Z_to_bv 64 (2 ^ 32 + 3))) (mkEffect (errno_ret EBADF) [] [])
        close_model = CheckReject
    ∧ check_syscall (close_call (Z_to_bv 64 (2 ^ 32 + 10))) (mkEffect (errno_ret EBADF) [] [])
        close_model = CheckOk close_model []
    ∧ check_syscall (close_call (Z_to_bv 64 (2 ^ 32))) (mkEffect 0 [] []) close_model
        = CheckOk after_close_0 [] := by
  simp only [check_syscall_close_call]
  exact row_57_fd_truncates_to_32_bits

/-- THE NARROWING IS THE ROW'S, NOT THE CHECKER'S: handed the whole word
2^32 + 3, `check_close` looks it up as it is, finds no descriptor, and
accepts -EBADF with the model unchanged, where `close` itself
(fs/open.c:1574, Linux v6.18.46) takes the `unsigned int` 3 and closes the
file there.  So a row that skipped `fd32` accepts the -EBADF that
`row_57_fd_truncates_to_32_bits_over_the_real_table` refuses.
model: `check_close` looks its descriptor argument up unnarrowed and the row's `fd32` does the narrowing; a claim about this tree, not about Linux -/
theorem the_close_checker_itself_reads_the_whole_word :
    check_close (Z_to_bv 64 (2 ^ 32 + 3)) (mkEffect (errno_ret EBADF) [] []) close_model
      = CheckOk close_model [] := rfl

end CloseThroughTheTable

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Open

-- lean-port sentinel: ticket V-Fs-Open-openat appends below this line
namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Open
section V_Fs_Open_openat_Rederived

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress (syscall_spec_witness)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Open

/-- The checked table finds openat at 56 for any argument list and either
memory function. This pins lookup itself, independently of an effect.
model: lookup_ca checked_table at syscall number 56 -/
theorem lookup_openat_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 56 args mem wmem).in_sysno)
      = some arm_openat := rfl

/-- The row equality also holds for arbitrary argument lists and writable
memory, beyond the six-register fixture of `check_syscall_openat_in'`.
This is a dispatch claim; the row's separate bounds remain its own.
model: check_syscall at 56 equals check_openat_row for arbitrary input payloads -/
theorem check_syscall_at_56_is_the_row (args : List word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 56 args mem wmem) eff m
      = check_openat_row (SyscallInput.mkInput 56 args mem wmem) eff m := rfl

/-- The witness lookup uses the same openat row for arbitrary input
payloads. The row reads dfd from a0, pathname from a1 and flags from a2, corresponding
to fs/open.c:1463-1468 (v6.18.46); this equality concerns the model's
witness, not which of the kernel's possible outcomes occurs.
kernel: fs/open.c:openat; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem syscall_spec_witness_at_56_is_the_row (args : List word)
    (mem wmem : word → Option byte) (m : Model) :
    syscall_spec_witness (SyscallInput.mkInput 56 args mem wmem) m
      = openat_witness_row (SyscallInput.mkInput 56 args mem wmem) m := rfl

/-- fs/open.c:1463-1468 puts filename in a1 and flags in a2. The ordinary
read opens the held file; exchanging those registers presents flag 8192,
which Rocq's and Lean's `modeled_open_flags` decline before the pathname
fetch. That decline is a model bound, not Linux's answer to flag 8192.
kernel: fs/open.c:openat,do_sys_openat2; fs/file.c:alloc_fd; fs/namei.c:path_init@v6.18.46 -/
theorem openat_path_and_flags_registers_over_the_real_table :
    check_syscall (openat_in [102] 0) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs)) []
    ∧ check_syscall (openat_in' AT_FDCWD 0 8192 (open_path_mem [102]))
        (eff_ret 3 2) have_model = CheckUnmodeled := ⟨rfl, rfl⟩

/-- For this read, a3's mode is cleared by build_open_how
(fs/open.c:1233-1234); openat consumes only four arguments (:1463-1468),
so a4 and a5 do not participate. Rocq's arm and this row read only a0-a2.
The held file still opens at the lowest free descriptor, 3.
kernel: fs/open.c:openat,build_open_how; fs/file.c:alloc_fd; fs/namei.c:path_init@v6.18.46 -/
theorem openat_unused_registers_over_the_real_table :
    check_syscall (SyscallInput.mkInput 56
        [AT_FDCWD, 8192, 0, 4095, Z_to_bv 64 (2^63), Z_to_bv 64 (2^64-1)]
        (open_path_mem [102]) (fun _ => none)) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs)) [] := rfl

/-- Both current checkers pass the whole flags word to modeled_open_flags
and decline 2^32. Linux instead casts int flags to zero at
include/linux/syscalls.h:132 and fs/open.c:1463-1468 (v6.18.46).
This pins the documented whole-word bound, not a kernel refusal.
model: modeled_open_flags reads all 64 flag bits; arm_openat narrows only dirfd -/
theorem flags_high_half_declines_over_the_real_table :
    check_syscall (openat_in [102] (Z_to_bv 64 (2^32))) (eff_ret 3 2) have_model
      = CheckUnmodeled := rfl

/-- Rocq: openat_rdwr_errnos, through the dispatcher. A missing
non-create name reaches -ENOENT (fs/namei.c:traverse_mounts:1537-1538),
and an existing exclusive name reaches -EEXIST (do_open:3949-3950).
Both branches are deterministic, so the -EMFILE Linux can raise before
the walk (fs/open.c:1435; fs/file.c:591-593) is refused on them, the
narrowing openat_body_spec records; an open that can succeed admits it.
The row pin `openat_rdwr_errnos` states the same conjuncts on
`check_openat_row`.
kernel: fs/namei.c:traverse_mounts,do_open; fs/open.c:do_sys_openat2; fs/file.c:alloc_fd@v6.18.46 -/
theorem openat_rdwr_errnos_over_the_real_table :
    check_syscall (openat_in [102] 2) (eff_errno ENOENT 2) absent_model = CheckOk absent_model []
    ∧ check_syscall (openat_in [102] 194) (eff_errno EEXIST 2) have_model = CheckOk have_model []
    ∧ check_syscall (openat_in [102] 2) (eff_errno EMFILE 2) absent_model = CheckReject
    ∧ check_syscall (openat_in [102] 194) (eff_errno EMFILE 2) have_model = CheckReject
    ∧ check_syscall (openat_in [102] 2) (eff_errno EMFILE 2) have_model = CheckOk have_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Rocq: openat_rdwr_dirref, through the dispatcher. At v6.18.46
do_open's O_EXCL test precedes its directory test (fs/namei.c:3949-3952);
without O_CREAT, may_open's S_IFDIR write test answers -EISDIR
(:3540-3542). The arms answer each errno under its own word and refuse
the swapped pair.
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem openat_rdwr_dirref_over_the_real_table :
    check_syscall (openat_in [46] 194) (eff_errno EEXIST 2) absent_model = CheckOk absent_model []
    ∧ check_syscall (openat_in [46] 2) (eff_errno EISDIR 2) absent_model = CheckOk absent_model []
    ∧ check_syscall (openat_in [46] 194) (eff_errno EISDIR 2) absent_model = CheckReject
    ∧ check_syscall (openat_in [46] 2) (eff_errno EEXIST 2) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Rocq: openat_localtime_enoent, its two O_RDONLY reject conjuncts.
A walk reaching the absent final component fails at traverse_mounts
(fs/namei.c:1537-1538). The -EACCES refusal is the model's existing
assumption, not an impossible Linux answer: link_path_walk calls may_lookup
(:2467, :1858), and generic_permission can fail with -EACCES (:485, :506).
This adds the O_RDONLY errno refusal absent from the base table pins.
kernel: fs/namei.c:traverse_mounts,link_path_walk,may_lookup,generic_permission@v6.18.46 -/
theorem openat_localtime_enoent_over_the_real_table :
    check_syscall (openat_in localtime_path 0) (eff_errno ENOENT 15) absent_model
      = CheckOk absent_model []
    ∧ check_syscall (openat_in localtime_path 0) (eff_ret 3 15) absent_model = CheckReject
    ∧ check_syscall (openat_in localtime_path 0) (eff_errno EACCES 15) absent_model = CheckReject := by
  simp only [check_syscall_openat_in]
  exact localtime_rdonly_is_enoent

/-- Rocq: openat_directory_answers, the descriptor refusal under the
combined O_DIRECTORY|O_LARGEFILE|O_CLOEXEC word 622592. At v6.18.46
build_open_flags sets LOOKUP_DIRECTORY (fs/open.c:1337-1338) and do_open
refuses the regular file (fs/namei.c:3958-3959). Rocq's check_openat_dir
returns only -ENOTDIR on this exact regular key. The base pins refusal
under 65536, but its ignored-bit equality offers -ENOTDIR, not this fd.
kernel: fs/open.c:build_open_flags; fs/namei.c:do_open@v6.18.46 -/
theorem openat_directory_answers_over_the_real_table :
    check_syscall (openat_in [97] 622592) (eff_errno ENOTDIR 2) exact_model
      = CheckOk exact_model []
    ∧ check_syscall (openat_in [97] 622592) (eff_ret 3 2) exact_model = CheckReject := ⟨rfl, rfl⟩

/-- Rocq had `openat_excl_append_flag_word` before f1006fe8 and has it no
longer; the word it is about, O_WRONLY|O_CREAT|O_EXCL|O_APPEND (1217),
has no arm in spec or checker, so the pin stays as a decline.  At
v6.18.46 do_open refuses an existing exclusive name with -EEXIST
(fs/namei.c:3949-3950) and the non-exclusive create on dot with -EISDIR
(:3951-3952); the flag gate refuses the word before the pathname is
read, so each offer is declined.  The last conjunct is the control: the
append word WITHOUT O_EXCL on dot is answered, -EISDIR, so the -EEXIST
offered there is refused and not declined.
kernel: fs/namei.c:do_open,traverse_mounts; fs/open.c:do_sys_openat2; fs/file.c:alloc_fd@v6.18.46 -/
theorem openat_excl_append_flag_word_over_the_real_table :
    check_syscall (openat_in [102] 1217) (eff_errno EEXIST 2) have_model = CheckUnmodeled
    ∧ check_syscall (openat_in [102] 1217) (eff_ret 3 2) have_model = CheckUnmodeled
    ∧ check_syscall (openat_in [102] 1217) (eff_errno EMFILE 2) have_model = CheckUnmodeled
    ∧ check_syscall (openat_in [46] 1217) (eff_ret 3 2) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in [46] 1217) (eff_errno ENOENT 2) absent_model = CheckUnmodeled
    ∧ check_syscall (openat_in [46] 1089) (eff_errno EEXIST 2) absent_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The same word on an IMPLIED DIRECTORY ("a" over a held "a/b"): the
flag gate refuses it before the pathname is read, so the -EEXIST
`do_open`'s O_EXCL test would give (fs/namei.c:3949-3952, v6.18.46), the
-EISDIR behind it and a descriptor are all declined.  The five words
beside it ANSWER there, in
`implied_directory_other_write_words_over_the_real_table`.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem openat_implied_directory_other_write_words_over_the_real_table :
    check_syscall (openat_in [97] 1217) (eff_errno EEXIST 2) under_model = CheckUnmodeled
    ∧ check_syscall (openat_in [97] 1217) (eff_errno EISDIR 2) under_model = CheckUnmodeled
    ∧ check_syscall (openat_in [97] 1217) (eff_ret 3 2) under_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- Rocq's openat_core_witness selects witness_errno (-ENOMEM) on this
held-file read. alloc_empty_file can return it at fs/file_table.c:258-260,
called by path_openat at fs/namei.c:4124 after the pathname fetch at
fs/open.c:1431. Through the real table the witness names that effect and
the checker accepts it; the same call also accepts the lowest fd, 3
(fs/file.c:580-585). This identifies one witness choice, not a forced errno.
kernel: fs/file_table.c:alloc_empty_file; fs/namei.c:path_openat; fs/open.c:do_sys_openat2; fs/file.c:alloc_fd@v6.18.46 -/
theorem openat_minting_path_witness_over_the_real_table :
    syscall_spec_witness (openat_in [102] 0) have_model
      = Ok (eff_errno ENOMEM 2) have_model []
    ∧ check_syscall (openat_in [102] 0) (eff_errno ENOMEM 2) have_model = CheckOk have_model []
    ∧ check_syscall (openat_in [102] 0) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs)) [] :=
  ⟨rfl, rfl, rfl⟩

/-- Rocq's openat_core_witness draws witness_errno (-ENOMEM) on the
append word over a held name, as it does on the read word: the arm can
succeed, so the alternative the witness takes is an openat_errnos one
(alloc_empty_file, fs/file_table.c:258-260, v6.18.46). Through the real
table the witness names that effect and the checker accepts it; the same
call also accepts the descriptor, minted as State.FdFileA at the lowest
free number with the file's bytes kept.
kernel: fs/file_table.c:alloc_empty_file; fs/namei.c:do_open; fs/file.c:alloc_fd@v6.18.46 -/
theorem openat_append_witness_over_the_real_table :
    syscall_spec_witness (openat_in [102] 1089) have_model
      = Ok (eff_errno ENOMEM 2) have_model []
    ∧ check_syscall (openat_in [102] 1089) (eff_errno ENOMEM 2) have_model
      = CheckOk have_model []
    ∧ check_syscall (openat_in [102] 1089) (eff_ret 3 2) have_model
      = CheckOk (fixture_of (fds := (3, .FdFileA [102] 0) :: init_fds) (fs := have_fs)) [] :=
  ⟨rfl, rfl, rfl⟩

end V_Fs_Open_openat_Rederived
end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Open
