import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.StreamLaws
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs

/-! # Checks.Cases.Fs.Open — what `openat`, `faccessat`, `close` and `ftruncate` answer, read off against Linux

Worked examples over `Sys.Fs.Open.openat_spec`, the openat half of the
twin of `theories/LinuxProcessSem/Checks/Cases/Fs/Open.v`; the faccessat
half — `faccessat_spec` and `faccessat2_spec` — follows it under its own
heading, with its own register of Rocq cases, the close half —
`close_spec` — is headed "Part two", and the ftruncate half —
`ftruncate_spec` and `modeled_truncate_gap` — "Part three" at the end of
the file.  Not part of
the trusted specification: this file is QA on the definitions, written to
be READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  Line numbers are Linux v6.18.46 (commit
1f99e9ab748f).

HOW THESE ARE STATED.  A call goes through the dispatcher — `syscall_spec`
on a `SyscallInput` numbered 56 built by `openat_in`, so the table's `fd32`
narrowing of `dirfd` is under test with the arm — or, where a pin is about
the arm's own arguments, through `openat_spec` with `AT_FDCWD32` spelled
as its numeral.  A decision is pinned twice: an `iff` over EVERY outcome
`o`, which fixes the admitted answer and refuses every other one,
`Unmodeled` included; and a refutation of the concrete answer a wrong
model or a lying kernel would give — the errno of the neighbouring arm, the
descriptor a resolution errno forbids, the non-lowest fd no kernel hands
out.  Both close by `sys_norm` / `sys_refute`; the pins over a SYMBOLIC
pathname (the NAME_MAX boundary, the too-long and faulting fetches) hand
the reader's result to `simp` first and say so where they occur.

THE SECTIONS FOLLOW THE KERNEL'S ORDER, and each pins the pair of
neighbours: `SYSCALL_DEFINE4(openat, …)` and `build_open_how` (the `int`
arguments), `build_open_flags` (the flag gate, before any pathname is
read), `getname_flags` (the three fetch answers, before the dirfd),
`path_init` (the dirfd), `link_path_walk` (the separator decline),
`handle_dots` (the two directory references), `lookup_open` and `do_open`
(the plain names, by word), and the two device paths and the "/tmp/<name>"
family answered ahead of the separator decline.

A DECLINE HERE IS A COVERAGE GAP, NOT AN EMPTY INTERSECTION, unless the pin
says otherwise.  Two groups of `Unmodeled` below are declines Rocq does not
make (the header of `Sys/Fs/Open.lean` names them): the append word and the
read-write words on a plain name, whose arms mint `FdFileA` and `FdFileRW`,
kinds every spec arm that would write or resize either descriptor, or read
the read-write one, declines so far.  Each is pinned with the kernel's real
answer REFUSED beside the `Unmodeled`, so a later arm has to land the state
before it can answer.  The rest are Rocq's own declines: a flag word outside
the interpreted set, a dirfd other than AT_FDCWD, a separator-bearing path,
the O_DIRECTORY arm's two guards, the two device arms' image guards, and the
`/tmp` arm's ruling (issue #562): every word but the create word and a read
of a held name, a second component, a component over NAME_MAX, and a READ of
an implied directory (whose create word now answers -EISDIR instead).

THE ROCQ WORKED CASES, and where each lives here.  This is a prose
register that no tool reads: `check_lean_cases_parity.py` (T9) judges only
the coverage block of the shape its docstring gives (a tagged module doc
naming the Rocq commit), which this file does not carry yet, so the tool
lists the twin as unclaimed and nothing in this list is machine-checked.
That block is owed once every line below can be a `covers:` line naming
Lean theorems or an `unpinned:` line whose reason cites the kernel (the
PARTLY PINNED groups are the `unpinned:` ones, and their remaining legs
belong to other twins' Cases files).
Every case of the Rocq file about openat or close is covered or listed with
its reason:

- `openat_live_dirfd_still_unmodeled` → `dirfd_1_declines_the_read`
- `openat_empty_path_enoent` → `empty_path_is_enoent`
- `o_nonblock_is_an_ignored_open_flag` → `nonblock_read_lands_where_read_does`
  and siblings under "build_open_flags: the ignored bits"; its
  `O_RDWR|O_NONBLOCK = O_RDWR` conjunct is `rdwr_nonblock_declines`, and its
  append and read-write conjuncts are the declared declines pinned under
  "the declared declines"
- `openat_append_flag_word`, `openat_rdwr_flag_words`, `openat_rdwr_errnos`,
  `openat_rdwr_dirref`, `openat_implied_directory_other_write_words`:
  UNPINNED — their arms are the declared declines; what is pinned is that
  each such word is `Unmodeled` and that the kernel's success is refused
- `openat_absolute_create_unmodeled` → `absolute_create_declines_a_success`,
  `absolute_create_declines_an_enoent`
- `openat_plain_create_still_mints_the_key` → `plain_create_mints_the_key`
- `openat_implied_directory_create_eisdir` →
  `implied_directory_create_is_eisdir`, `implied_directory_create_fd_rejected`,
  `implied_directory_control_creates`
- `openat_byte_prefix_and_exact_key_still_create` →
  `byte_prefix_is_not_a_directory`, `byte_prefix_eisdir_rejected`,
  `exact_key_is_the_truncating_create`, `exact_key_eisdir_rejected`
- `openat_implied_directory_excl_eexist` →
  `implied_directory_excl_is_eexist`, `implied_directory_excl_fd_rejected`,
  `implied_directory_excl_control_creates`
- `openat_slash_key_in_image_unmodeled` → `slash_key_in_image_declines`
- `openat_localtime_enoent` → the "/etc/localtime" section
- `openat_localtime_in_image_unmodeled` → `localtime_key_in_image_declines`
  and siblings
- `openat_localtime_match_is_exact` → `localtime_match_is_exact_*`
- `devnull_open_by_word`, `devnull_open_declines` → the "/dev/null" section
- `devnull_open_write_read_close`, `devnull_dispatch_sites`,
  `devnull_fstat_asserts_the_device`: PARTLY PINNED — not openat cases.
  They read the descriptor through other arms: the close (57) leg is
  `devnull_close_restores_the_model` in the close part and the ftruncate
  (46) leg is `devnull_ftruncate_is_einval` in the ftruncate part; the
  read (63), write (64), lseek (62), pread64 (67) and pwrite64 (68) legs
  belong to the ReadWrite twin's Cases file, and the fstat, dup, fcntl,
  flock, fsync, ioctl and getdents64 legs to those twins' own.  The open
  half is pinned here
- `openat_dotdot_answers_as_dot_does` → the "handle_dots" section
- `openat_dot3_is_an_ordinary_name` → `dot3_is_an_ordinary_name`
- `openat_empty_path_beats_o_creat` → `empty_path_beats_o_creat`,
  `empty_path_create_fd_rejected`
- `openat_directory_answers` → the "O_DIRECTORY" section
- `openat_directory_ignores_largefile_and_cloexec` →
  `dir_word_ignores_largefile_and_cloexec_*`
- `openat_directory_implied_directory_unmodeled` →
  `dir_implied_directory_declines_*`
- `openat_directory_name_max_boundary` → `dir_name_max_256_declines`,
  `dir_name_max_255_answers`
- `urandom_open_by_word`, `urandom_open_declines` → the "/dev/urandom" section
- `urandom_open_read_close`, `urandom_stream_runs_out`, `urandom_dispatch_sites`,
  `urandom_fstat_asserts_the_device`, `urandom_same_bytes_on_both_sides`:
  PARTLY PINNED — not openat cases, the same way: the close (57) leg is
  `urandom_close_restores_the_model` and `urandom_close_keeps_the_stream`
  in the close part and the ftruncate (46) leg is
  `urandom_ftruncate_is_einval` in the ftruncate part; the read (63),
  write (64), lseek (62), pread64 (67) and pwrite64 (68) legs belong to
  the ReadWrite twin's Cases file, and the fstat, dup, fcntl, flock,
  fsync, ioctl and getdents64 legs to those twins' own.  The open half is
  pinned here
- `openat_tmp_create_read_unlink` → `tmp_create_mints_the_key`,
  `tmp_create_on_held_key_empties_it`, `tmp_read_held_mints_the_reader`,
  `tmp_create_cloexec_lands_where_create_does`,
  `tmp_create_nonblock_lands_where_create_does`,
  `tmp_create_largefile_lands_where_create_does`,
  `tmp_read_cloexec_is_the_same_open` (the unlink leg is
  `Checks/Cases/Fs/Namei.lean`'s)
- `openat_tmp_declared_name_reads` → `tmp_declared_name_reads`
- `openat_tmp_unsorted_declaration_is_canonical` → `tmp_seed_unsorted_is_canonical`
- `openat_tmp_excluded_shapes_unmodeled` → `tmp_read_not_held_declines`,
  `tmp_rdwr_create_trunc_declines`, `tmp_append_declines`, `tmp_excl_declines`,
  `tmp_directory_word_declines`, `tmp_second_component_declines`,
  `tmp_directory_itself_declines`, `tmp_directory_slash_declines`,
  `tmp_dot_declines`, `tmp_dotdot_declines`, `tmpfoo_declines`
- `openat_tmp_name_max_boundary` → `tmp_name_max_256_declines_the_create`,
  `tmp_name_max_256_declines_the_read`, `tmp_name_max_255_answers`
- `openat_tmp_implied_directory_create_eisdir` →
  `tmp_implied_directory_create_is_eisdir`,
  `tmp_implied_directory_create_fd_rejected`,
  `tmp_implied_directory_create_enoent_rejected`
- `openat_tmp_implied_directory_read_unmodeled` →
  `tmp_implied_directory_declines_the_read`,
  `tmp_implied_directory_fd_rejected`
- `openat_tmp_implied_directory_unrealizable_image` →
  `tmp_unrealizable_image_holds_both`, `tmp_unrealizable_read_declines`,
  `tmp_unrealizable_read_fd_rejected`, `tmp_unrealizable_read_enoent_rejected`,
  `tmp_unrealizable_create_is_eisdir`, `tmp_unrealizable_create_fd_rejected`
- `openat_tmp_implied_directory_sibling_still_creates` →
  `tmp_implied_directory_sibling_still_creates`
- the faccessat and faccessat2 cases are registered under the faccessat
  heading below; the close cases are in Part two.
- `ftruncate_on_a_dangling_fd_is_unmodeled` →
  `dangling_writable_fd_declines`, `dangling_writable_fd_success_rejected`
  in Part three; the ftruncate legs of the two `*_dispatch_sites` cases
  are named beside those cases above.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Open

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs

/-! ## The register lines the spec owes `sys_simp`

`Checks/Cases/Tactic.lean`'s header asks each spec for its unfolding
equation and each post-state builder's; they are registered here, beside
the pins that read them, because this port edits only its own two files.
`lowest_fd` is `Sys/Fs/File.lean`'s and `record_copyins` is
`Sys/Syscall.lean`'s; each is registered here as well, so these pins do not
depend on another Cases file having done it.  The gates
(`modeled_open_flags`, `path_is_dirref`, `is_excl_create`, …) are decided,
never unfolded, as that header prescribes. -/

attribute [sys_simp low]
  openat_spec.eq_1 openat_core_spec.eq_1 openat_body_spec.eq_1 openat_resolved_spec.eq_1
  openat_sep_spec.eq_1 openat_read_spec.eq_1 openat_create_spec.eq_1 openat_excl_spec.eq_1
  openat_dir_spec.eq_1 openat_localtime_spec.eq_1 openat_devnull_spec.eq_1
  openat_urandom_spec.eq_1 openat_tmp_spec.eq_1
  open_result_spec.eq_1 create_wronly.eq_1 open_devnull.eq_1 open_urandom.eq_1 openat_errnos.eq_1
  lowest_fd.eq_1 record_copyins.eq_1

/-! ## The constants these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes; these pins say what each one is. -/

/-- The clobbering create word: 1 + 64 + 512.
kernel: include/uapi/asm-generic/fcntl.h:O_WRONLY,O_CREAT,O_TRUNC@v6.18.46 -/
theorem wr_create_flags_is_577 : wr_create_flags = 577 := by decide
/-- The exclusive create word: 1 + 64 + 128.
kernel: include/uapi/asm-generic/fcntl.h:O_WRONLY,O_CREAT,O_EXCL@v6.18.46 -/
theorem excl_create_flags_is_193 : excl_create_flags = 193 := by decide
/-- The append create word: 1 + 64 + 1024.
kernel: include/uapi/asm-generic/fcntl.h:O_WRONLY,O_CREAT,O_APPEND@v6.18.46 -/
theorem append_create_flags_is_1089 : append_create_flags = 1089 := by decide
/-- The exclusive read-write create word: 2 + 64 + 128.
kernel: include/uapi/asm-generic/fcntl.h:O_RDWR,O_CREAT,O_EXCL@v6.18.46 -/
theorem rdwr_excl_create_flags_is_194 : rdwr_excl_create_flags = 194 := by decide
/-- The exclusive append create word: 1 + 64 + 128 + 1024.
kernel: include/uapi/asm-generic/fcntl.h:O_WRONLY,O_CREAT,O_EXCL,O_APPEND@v6.18.46 -/
theorem excl_append_create_flags_is_1217 : excl_append_create_flags = 1217 := by decide
/-- The ignored bits: 524288 + 32768 + 2048.
kernel: include/uapi/asm-generic/fcntl.h:O_CLOEXEC,O_LARGEFILE,O_NONBLOCK@v6.18.46 -/
theorem open_ignored_flags_is_559104 : open_ignored_flags = 559104 := by decide
/-- The directory word, interpreted rather than ignored.
kernel: include/uapi/asm-generic/fcntl.h:O_DIRECTORY@v6.18.46 -/
example : O_DIRECTORY = 65536 := by decide
/-- The four injectable errnos, in the order `errno_from` enumerates them.
kernel: include/uapi/asm-generic/errno-base.h:ENOMEM,EACCES,EMFILE,ENFILE@v6.18.46 -/
theorem openat_errnos_are_the_four : openat_errnos = [12, 13, 24, 23] := by decide
/-- `AT_FDCWD` (-100, include/uapi/linux/fcntl.h:94, Linux v6.18.46) as the low 32 bits the
table hands the arm: 2^32 - 100.
model: the model's own 32-bit spelling of the kernel constant; the kernel reading is on the `path_init` pins below. -/
theorem at_fdcwd32_is_the_low_half : AT_FDCWD32 = 4294967196 := by decide
/-- NAME_MAX, the O_DIRECTORY arm's component bound.
kernel: include/uapi/linux/limits.h:NAME_MAX@v6.18.46 -/
example : NAME_MAX = 255 := by decide
/-- The bytes of "/etc/localtime".
model: the model's own path constant at its bytes; the kernel reading is on the localtime pins below. -/
theorem localtime_path_bytes :
    localtime_path = [47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] := by decide
/-- The bytes of "/dev/null".
model: the model's own path constant at its bytes; the kernel reading is on the devnull pins below. -/
theorem devnull_path_bytes : devnull_path = [47, 100, 101, 118, 47, 110, 117, 108, 108] := by decide
/-- The bytes of "/dev/urandom".
model: the model's own path constant at its bytes; the kernel reading is on the urandom pins below. -/
theorem urandom_path_bytes :
    urandom_path = [47, 100, 101, 118, 47, 117, 114, 97, 110, 100, 111, 109] := by decide

/-! ## The fixtures and the call

Rocq's `open_path_mem bs` lays `bs` then a NUL at 8192 and maps nothing
else; `openat_in bs flags` is `openat(AT_FDCWD, 8192, flags, 0644)` on it.
The models are `fixture_of` over one file system each, unfolded by their
equations at `low` as `Checks/Cases/Prelude.lean` prescribes; the file
systems themselves stay names, so the closed `fs_lookup` facts below meet
them in the first pass and every `match` on a lookup is decided before the
errno alternatives are read (the reason is `Checks/Cases/Tactic.lean`'s
two-pass note). -/

/-- Rocq's `open_path_mem`: `bs` then a NUL from 8192, nothing else mapped. -/
def open_path_mem (bs : List byte) : word → Option byte := bytes_at 8192 (bs ++ [0])

/-- `openat(dirfd, pathp, flags, 0644)` as the dispatcher sees it, over the
memory `mem`; nothing writable. -/
def openat_in' (dirfd pathp flags : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 56 [dirfd, pathp, flags, 420, 0, 0] mem (fun _ => none)

/-- The ordinary call: `AT_FDCWD`, the pathname `bs` at 8192. -/
def openat_in (bs : List byte) (flags : word) : SyscallInput :=
  openat_in' AT_FDCWD 8192 flags (open_path_mem bs)

attribute [sys_simp low] openat_in'.eq_1 openat_in.eq_1

/-- The table reads its arguments through `in_arg`; on a six-argument
literal input the three openat reads are these, so the first pass sees
the literal and the fetch is decided before the alternatives are read.
model: `in_arg` on a literal argument list, a rewrite for `sys_norm`. -/
theorem in_arg_mkInput_0 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 0 = a0 := rfl
/-- The pathname pointer.
model: `in_arg` on a literal argument list, a rewrite for `sys_norm`. -/
theorem in_arg_mkInput_1 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 1 = a1 := rfl
/-- The flags word.
model: `in_arg` on a literal argument list, a rewrite for `sys_norm`. -/
theorem in_arg_mkInput_2 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 2 = a2 := rfl

/-- The result an arm returns: `r` in a0 with the pathname copy-in of `n`
bytes recorded, the model `m` after it. -/
def ret (r : word) (n : Nat) (m : Model) : outcome SyscallEffect :=
  Ok (with_copyins [(8192, n)] (mkEffect r [] [])) m []

/-- An errno return, the same way. -/
def errno (e : Int) (n : Nat) (m : Model) : outcome SyscallEffect := ret (errno_ret e) n m

/-- The four environment errnos an open that can succeed may answer
instead, with nothing changed: -ENOMEM, -EACCES, -EMFILE, -ENFILE, in the
order `openat_errnos` lists them. -/
def env_errnos (n : Nat) (m : Model) (o : outcome SyscallEffect) : Prop :=
  o = errno 12 n m ∨ o = errno 13 n m ∨ o = errno 24 n m ∨ o = errno 23 n m

attribute [sys_simp low] ret.eq_1 errno.eq_1 env_errnos.eq_1

/-- "f" holding "hi": Rocq's `have` image. -/
def have_fs : Fs.Fs := [([102], [104, 105])]
/-- "a/b" holding one byte: the image whose key IMPLIES a directory "a". -/
def under_fs : Fs.Fs := [([97, 47, 98], [104])]
/-- "ab": a BYTE prefix of which "a" is not a directory component. -/
def sibling_fs : Fs.Fs := [([97, 98], [104])]
/-- "a" itself, holding one byte. -/
def exact_fs : Fs.Fs := [([97], [104])]
/-- One byte under the EMPTY key: Rocq's `openat_empty_path_enoent` image. -/
def empty_key_fs : Fs.Fs := [([], [104])]
/-- The image that SHIPS "/etc/localtime" as a key. -/
def localtime_key_fs : Fs.Fs := [(localtime_path, [104])]
/-- The image with a key UNDER "/etc/localtime" ("/etc/localtime/x"). -/
def localtime_under_fs : Fs.Fs := [(localtime_path ++ [47, 120], [104])]
/-- The image that ships a FILE under the name "/dev/null". -/
def devnull_key_fs : Fs.Fs := [(devnull_path, [104])]
/-- The image with a key under "/dev/null" ("/dev/null/x"). -/
def devnull_under_fs : Fs.Fs := [(devnull_path ++ [47, 120], [104])]
/-- The image that ships a FILE under the name "/dev/urandom". -/
def urandom_key_fs : Fs.Fs := [(urandom_path, [104])]
/-- The image with a key under "/dev/urandom" ("/dev/urandom/x"). -/
def urandom_under_fs : Fs.Fs := [(urandom_path ++ [47, 120], [104])]
/-- The run holds "/tmp/x", one byte, under the absolute key `State.fs_seed_tmp`
would have put the component "x" at. -/
def tmp_held_fs : Fs.Fs := [([47, 116, 109, 112, 47, 120], [104])]
/-- The run holds "/tmp/d/f", so "/tmp/d" is a directory the flat map only implies. -/
def tmp_dir_fs : Fs.Fs := [([47, 116, 109, 112, 47, 100, 47, 102], [104])]
/-- The UNREALIZABLE image `Fs.valid_fs` admits: "/tmp/d" a key AND "/tmp/d/f"
held under it.  No reality has both; it is the one image on which the read
branch's `Namei.fs_under` test changes an answer. -/
def tmp_unreal_fs : Fs.Fs :=
  [([47, 116, 109, 112, 47, 100], [104]), ([47, 116, 109, 112, 47, 100, 47, 102], [104])]
/-- 255 and 256 copies of 'a': the two sides of `NAME_MAX`. -/
def name255 : List byte := List.replicate 255 97
def name256 : List byte := List.replicate 256 97

def absent_model : Model := fixture_of
def empty_key_model : Model := fixture_of (fs := empty_key_fs)
def have_model : Model := fixture_of (fs := have_fs)
def under_model : Model := fixture_of (fs := under_fs)
def sibling_model : Model := fixture_of (fs := sibling_fs)
def exact_model : Model := fixture_of (fs := exact_fs)
def localtime_key_model : Model := fixture_of (fs := localtime_key_fs)
def localtime_under_model : Model := fixture_of (fs := localtime_under_fs)
def devnull_key_model : Model := fixture_of (fs := devnull_key_fs)
def devnull_under_model : Model := fixture_of (fs := devnull_under_fs)
def urandom_key_model : Model := fixture_of (fs := urandom_key_fs)
def urandom_under_model : Model := fixture_of (fs := urandom_under_fs)
def tmp_held_model : Model := fixture_of (fs := tmp_held_fs)
def tmp_dir_model : Model := fixture_of (fs := tmp_dir_fs)
def tmp_unreal_model : Model := fixture_of (fs := tmp_unreal_fs)
/-- The run whose ENVIRONMENT declared "x" with one byte, as `State.fs_seed_tmp`
seeds it — the component, not the absolute key. -/
def tmp_seeded_model : Model := fixture_of (fs := fs_seed_tmp [] [([120], [104])])
/-- The run holds "/tmp/ab", a byte-prefix sibling of "/tmp/a": the control that
`Namei.fs_under` asks for the separator, not the prefix. -/
def tmp_sibling_fs : Fs.Fs := [([47, 116, 109, 112, 47, 97, 98], [104])]
def tmp_sibling_model : Model := fixture_of (fs := tmp_sibling_fs)
/-- The run holds the 255-byte name under /tmp: the read side of `NAME_MAX`. -/
def tmp_name255_held_fs : Fs.Fs := [(tmp_key name255, [104])]
def tmp_name255_held_model : Model := fixture_of (fs := tmp_name255_held_fs)

attribute [sys_simp low]
  absent_model.eq_1 empty_key_model.eq_1 have_model.eq_1 under_model.eq_1 sibling_model.eq_1 exact_model.eq_1
  localtime_key_model.eq_1 localtime_under_model.eq_1 devnull_key_model.eq_1
  devnull_under_model.eq_1 urandom_key_model.eq_1 urandom_under_model.eq_1
  tmp_held_model.eq_1 tmp_dir_model.eq_1 tmp_unreal_model.eq_1 tmp_sibling_model.eq_1
  tmp_name255_held_model.eq_1

/-! ### The closed readings the first pass needs

One fact per pathname fetch and per file-system lookup the pins reach, so
the `match` on each is decided in the first pass; all `rfl`. -/

/-- The empty file system holds nothing, whatever the name.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem fs_lookup_nil (p : path) : fs_lookup [] p = none := rfl
/-- "f" is in the `have` image, with "hi".
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_have_f : fs_lookup have_fs [102] = some [104, 105] := rfl
/-- "a" is not.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_have_a : fs_lookup have_fs [97] = none := rfl
/-- "a" is not a KEY of the `under` image (only "a/b" is).
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_under_a : fs_lookup under_fs [97] = none := rfl
/-- "c" is not a key of the `under` image.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_under_c : fs_lookup under_fs [99] = none := rfl
/-- "a/b" IS a key of the `under` image.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_under_ab : fs_lookup under_fs [97, 47, 98] = some [104] := rfl
/-- "a" is not a key of the `sibling` image ("ab" is).
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_sibling_a : fs_lookup sibling_fs [97] = none := rfl
/-- "a" is the key of the `exact` image.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_exact_a : fs_lookup exact_fs [97] = some [104] := rfl
/-- The shipped "/etc/localtime" key.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_localtime_key : fs_lookup localtime_key_fs localtime_path = some [104] := rfl
/-- A key under "/etc/localtime" is not the key itself.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_localtime_under : fs_lookup localtime_under_fs localtime_path = none := rfl
/-- The shipped "/dev/null" key.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_devnull_key : fs_lookup devnull_key_fs devnull_path = some [104] := rfl
/-- A key under "/dev/null" is not the key itself.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_devnull_under : fs_lookup devnull_under_fs devnull_path = none := rfl
/-- The shipped "/dev/urandom" key.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_urandom_key : fs_lookup urandom_key_fs urandom_path = some [104] := rfl
/-- A key under "/dev/urandom" is not the key itself.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_urandom_under : fs_lookup urandom_under_fs urandom_path = none := rfl
/-- The `exact` image does not hold "/etc/localtime" (the control image).
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_exact_localtime : fs_lookup exact_fs localtime_path = none := rfl
/-- "/tmp/x" is a key of the held image.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_tmp_held_x : fs_lookup tmp_held_fs [47, 116, 109, 112, 47, 120] = some [104] := rfl
/-- "/tmp/d" is not a KEY of the implied-directory image (only "/tmp/d/f" is).
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_tmp_dir_d : fs_lookup tmp_dir_fs [47, 116, 109, 112, 47, 100] = none := rfl
/-- The /tmp gate on every path the pins below send it, closed so that the
`match` in `openat_sep_spec` is decided in the first pass and `tmp_name` is
never unfolded on a still-symbolic pathname: "/tmp/x" and "/tmp/d" are one
component each; "/tmp", "/tmp/", "/tmp/.", "/tmp/..", "/tmp/d/f" and
"/tmpfoo" are not.
model: a closed `Namei.tmp_name`, a rewrite for `sys_norm`. -/
theorem tmp_name_literals :
    tmp_name [47, 116, 109, 112, 47, 120] = some [120]
    ∧ tmp_name [47, 116, 109, 112, 47, 100] = some [100]
    ∧ tmp_name [47, 116, 109, 112] = none
    ∧ tmp_name [47, 116, 109, 112, 47] = none
    ∧ tmp_name [47, 116, 109, 112, 47, 46] = none
    ∧ tmp_name [47, 116, 109, 112, 47, 46, 46] = none
    ∧ tmp_name [47, 116, 109, 112, 47, 100, 47, 102] = none
    ∧ tmp_name [47, 116, 109, 112, 102, 111, 111] = none := by decide
set_option maxRecDepth 8192 in
/-- The two long keys under /tmp as the gate sees them: one component each,
of 255 and 256 bytes.
model: a closed `Namei.tmp_name`, a rewrite for `sys_norm`. -/
theorem tmp_name_long :
    tmp_name (tmp_key name255) = some name255 ∧ tmp_name (tmp_key name256) = some name256 := by
  decide
/-- The seeding of the one declared component "x" IS the held image: what
`tmp_declared_name_reads` rests on.
model: a closed `State.fs_seed_tmp`, a rewrite for `tmp_seeded_is_held`. -/
theorem seed_x : fs_seed_tmp [] [([120], [104])] = tmp_held_fs := by decide
/-- …so the two models are one.
model: `seed_x` under `fixture_of`. -/
theorem tmp_seeded_is_held : tmp_seeded_model = tmp_held_model := by
  unfold tmp_seeded_model tmp_held_model; rw [seed_x]

/-- The pathname fetch of each literal the pins use, and its copy-in
length (the bytes through the NUL).  `read_cstr` walks at most PATH_MAX
bytes and stops at the NUL, so each is a closed computation.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_a : read_cstr (open_path_mem [97]) 8192 = CstrOk [97] := rfl
/-- "f".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_f : read_cstr (open_path_mem [102]) 8192 = CstrOk [102] := rfl
/-- "c".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_c : read_cstr (open_path_mem [99]) 8192 = CstrOk [99] := rfl
/-- ".".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_dot : read_cstr (open_path_mem [46]) 8192 = CstrOk [46] := rfl
/-- "..".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_dotdot : read_cstr (open_path_mem [46, 46]) 8192 = CstrOk [46, 46] := rfl
/-- "...".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_dot3 : read_cstr (open_path_mem [46, 46, 46]) 8192 = CstrOk [46, 46, 46] := rfl
/-- "".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_empty : read_cstr (open_path_mem []) 8192 = CstrOk [] := rfl
/-- "/a".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_slash_a : read_cstr (open_path_mem [47, 97]) 8192 = CstrOk [47, 97] := rfl
/-- "a/b".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_a_slash_b : read_cstr (open_path_mem [97, 47, 98]) 8192 = CstrOk [97, 47, 98] := rfl
/-- "/etc/localtime".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_localtime : read_cstr (open_path_mem localtime_path) 8192 = CstrOk localtime_path := rfl
/-- "/etc//localtime".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_localtime_double_slash :
    read_cstr (open_path_mem [47, 101, 116, 99, 47, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101]) 8192
      = CstrOk [47, 101, 116, 99, 47, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] := rfl
/-- "//etc/localtime".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_localtime_double_root :
    read_cstr (open_path_mem [47, 47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101]) 8192
      = CstrOk [47, 47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] := rfl
/-- "/etc/localtim", one byte short.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_localtime_prefix :
    read_cstr (open_path_mem [47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109]) 8192
      = CstrOk [47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109] := rfl
/-- "/etc/localtimes", one byte long.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_localtime_extended :
    read_cstr (open_path_mem (localtime_path ++ [115])) 8192 = CstrOk (localtime_path ++ [115]) := rfl
/-- "/dev/null".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_devnull : read_cstr (open_path_mem devnull_path) 8192 = CstrOk devnull_path := rfl
/-- "/dev//null".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_devnull_double_slash :
    read_cstr (open_path_mem [47, 100, 101, 118, 47, 47, 110, 117, 108, 108]) 8192
      = CstrOk [47, 100, 101, 118, 47, 47, 110, 117, 108, 108] := rfl
/-- "/dev/nul", one byte short.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_devnull_prefix :
    read_cstr (open_path_mem [47, 100, 101, 118, 47, 110, 117, 108]) 8192
      = CstrOk [47, 100, 101, 118, 47, 110, 117, 108] := rfl
/-- "/dev/urandom".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_urandom : read_cstr (open_path_mem urandom_path) 8192 = CstrOk urandom_path := rfl
/-- "/dev//urandom".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_urandom_double_slash :
    read_cstr (open_path_mem [47, 100, 101, 118, 47, 47, 117, 114, 97, 110, 100, 111, 109]) 8192
      = CstrOk [47, 100, 101, 118, 47, 47, 117, 114, 97, 110, 100, 111, 109] := rfl
/-- "/dev/random", the next device over.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_dev_random :
    read_cstr (open_path_mem [47, 100, 101, 118, 47, 114, 97, 110, 100, 111, 109]) 8192
      = CstrOk [47, 100, 101, 118, 47, 114, 97, 110, 100, 111, 109] := rfl
/-- "/tmp/x", the one-component name the /tmp arm answers.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_x : read_cstr (open_path_mem [47, 116, 109, 112, 47, 120]) 8192
    = CstrOk [47, 116, 109, 112, 47, 120] := rfl
/-- "/tmp/d", the implied directory.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_d : read_cstr (open_path_mem [47, 116, 109, 112, 47, 100]) 8192
    = CstrOk [47, 116, 109, 112, 47, 100] := rfl
/-- "/tmp/d/f", a second component.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_d_f : read_cstr (open_path_mem [47, 116, 109, 112, 47, 100, 47, 102]) 8192
    = CstrOk [47, 116, 109, 112, 47, 100, 47, 102] := rfl
/-- "/tmp", the directory itself.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_dir : read_cstr (open_path_mem [47, 116, 109, 112]) 8192
    = CstrOk [47, 116, 109, 112] := rfl
/-- "/tmp/", the directory with a trailing separator.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_slash : read_cstr (open_path_mem [47, 116, 109, 112, 47]) 8192
    = CstrOk [47, 116, 109, 112, 47] := rfl
/-- "/tmp/.".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_dot : read_cstr (open_path_mem [47, 116, 109, 112, 47, 46]) 8192
    = CstrOk [47, 116, 109, 112, 47, 46] := rfl
/-- "/tmp/..".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_dotdot : read_cstr (open_path_mem [47, 116, 109, 112, 47, 46, 46]) 8192
    = CstrOk [47, 116, 109, 112, 47, 46, 46] := rfl
/-- "/tmpfoo", a name that merely begins like the prefix.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmpfoo : read_cstr (open_path_mem [47, 116, 109, 112, 102, 111, 111]) 8192
    = CstrOk [47, 116, 109, 112, 102, 111, 111] := rfl
set_option maxRecDepth 8192 in
/-- "/tmp/" followed by the 255-byte name.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_name255 : read_cstr (open_path_mem (tmp_key name255)) 8192
    = CstrOk (tmp_key name255) := by decide
set_option maxRecDepth 8192 in
/-- "/tmp/" followed by the 256-byte name.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_name256 : read_cstr (open_path_mem (tmp_key name256)) 8192
    = CstrOk (tmp_key name256) := by decide
/-- A NULL pathname pointer over the ordinary memory: nothing is mapped at 0.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_null_pointer : read_cstr (open_path_mem [97]) 0 = CstrFault := rfl
/-- "a" whose NUL is unmapped: the fetch runs off the mapping.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_runoff : read_cstr (bytes_at 8192 [97]) 8192 = CstrFault := rfl

/-- The copy-in ledger of each fetch: the bytes through the NUL, the one
attempted byte of a NULL pointer, the two of a run-off.
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_a : cstr_access_len_aux (open_path_mem [97]) 8192 path_max = 2 := rfl
/-- "f".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_f : cstr_access_len_aux (open_path_mem [102]) 8192 path_max = 2 := rfl
/-- "c".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_c : cstr_access_len_aux (open_path_mem [99]) 8192 path_max = 2 := rfl
/-- ".".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_dot : cstr_access_len_aux (open_path_mem [46]) 8192 path_max = 2 := rfl
/-- "..".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_dotdot : cstr_access_len_aux (open_path_mem [46, 46]) 8192 path_max = 3 := rfl
/-- "...".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_dot3 : cstr_access_len_aux (open_path_mem [46, 46, 46]) 8192 path_max = 4 := rfl
/-- "".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_empty : cstr_access_len_aux (open_path_mem []) 8192 path_max = 1 := rfl
/-- "/a".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_slash_a : cstr_access_len_aux (open_path_mem [47, 97]) 8192 path_max = 3 := rfl
/-- "a/b".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_a_slash_b : cstr_access_len_aux (open_path_mem [97, 47, 98]) 8192 path_max = 4 := rfl
/-- "/etc/localtime".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_localtime : cstr_access_len_aux (open_path_mem localtime_path) 8192 path_max = 15 := rfl
/-- "/etc//localtime".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_localtime_double_slash :
    cstr_access_len_aux (open_path_mem [47, 101, 116, 99, 47, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101])
      8192 path_max = 16 := rfl
/-- "//etc/localtime".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_localtime_double_root :
    cstr_access_len_aux (open_path_mem [47, 47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101])
      8192 path_max = 16 := rfl
/-- "/etc/localtim".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_localtime_prefix :
    cstr_access_len_aux (open_path_mem [47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109])
      8192 path_max = 14 := rfl
/-- "/etc/localtimes".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_localtime_extended :
    cstr_access_len_aux (open_path_mem (localtime_path ++ [115])) 8192 path_max = 16 := rfl
/-- "/dev/null".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_devnull : cstr_access_len_aux (open_path_mem devnull_path) 8192 path_max = 10 := rfl
/-- "/dev//null".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_devnull_double_slash :
    cstr_access_len_aux (open_path_mem [47, 100, 101, 118, 47, 47, 110, 117, 108, 108]) 8192 path_max
      = 11 := rfl
/-- "/dev/nul".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_devnull_prefix :
    cstr_access_len_aux (open_path_mem [47, 100, 101, 118, 47, 110, 117, 108]) 8192 path_max = 9 := rfl
/-- "/dev/urandom".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_urandom : cstr_access_len_aux (open_path_mem urandom_path) 8192 path_max = 13 := rfl
/-- "/dev//urandom".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_urandom_double_slash :
    cstr_access_len_aux (open_path_mem [47, 100, 101, 118, 47, 47, 117, 114, 97, 110, 100, 111, 109]) 8192
      path_max = 14 := rfl
/-- "/dev/random".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_dev_random :
    cstr_access_len_aux (open_path_mem [47, 100, 101, 118, 47, 114, 97, 110, 100, 111, 109]) 8192
      path_max = 12 := rfl
/-- "/tmp/x".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_x : cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 47, 120]) 8192 path_max = 7 := rfl
/-- "/tmp/d".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_d : cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 47, 100]) 8192 path_max = 7 := rfl
/-- "/tmp/d/f".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_d_f : cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 47, 100, 47, 102]) 8192 path_max = 9 := rfl
/-- "/tmp".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_dir : cstr_access_len_aux (open_path_mem [47, 116, 109, 112]) 8192 path_max = 5 := rfl
/-- "/tmp/".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_slash : cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 47]) 8192 path_max = 6 := rfl
/-- "/tmp/.".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_dot : cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 47, 46]) 8192 path_max = 7 := rfl
/-- "/tmp/..".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_dotdot : cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 47, 46, 46]) 8192 path_max = 8 := rfl
/-- "/tmpfoo".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmpfoo : cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 102, 111, 111]) 8192 path_max = 8 := rfl
set_option maxRecDepth 8192 in
/-- "/tmp/" and the 255-byte name: 261 bytes with the NUL.
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_name255 : cstr_access_len_aux (open_path_mem (tmp_key name255)) 8192 path_max = 261 := by decide
set_option maxRecDepth 8192 in
/-- "/tmp/" and the 256-byte name: 262 bytes with the NUL.
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_name256 : cstr_access_len_aux (open_path_mem (tmp_key name256)) 8192 path_max = 262 := by decide
/-- The NULL pointer: one attempted byte.
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_null_pointer : cstr_access_len_aux (open_path_mem [97]) 0 path_max = 1 := rfl
/-- The run-off: the mapped byte and the faulting one.
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_runoff : cstr_access_len_aux (bytes_at 8192 [97]) 8192 path_max = 2 := rfl

/-- "/tmp/a" is not in the sibling image…
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_tmp_sibling_a : fs_lookup tmp_sibling_fs [47, 116, 109, 112, 47, 97] = none := rfl
/-- …nor is the byte-prefix sibling "/tmp/ab" UNDER it: `dir_prefixb` wants
the separator.
model: a closed `Namei.fs_under`, a rewrite for `sys_norm`. -/
theorem under_tmp_sibling_a : fs_under tmp_sibling_fs [47, 116, 109, 112, 47, 97] = false := by decide
set_option maxRecDepth 8192 in
/-- The 255-byte key is held.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_tmp_name255_held : fs_lookup tmp_name255_held_fs (tmp_key name255) = some [104] := by decide
set_option maxRecDepth 8192 in
/-- …and nothing lies under it.
model: a closed `Namei.fs_under`, a rewrite for `sys_norm`. -/
theorem under_tmp_name255_held : fs_under tmp_name255_held_fs (tmp_key name255) = false := by decide
/-- The gate on "/tmp/a", "/tmp//x" and "/tmp/x/": one name, and two
separator edges after the prefix that are no name.
model: a closed `Namei.tmp_name`, a rewrite for `sys_norm`. -/
theorem tmp_name_edges :
    tmp_name [47, 116, 109, 112, 47, 97] = some [97]
    ∧ tmp_name [47, 116, 109, 112, 47, 47, 120] = none
    ∧ tmp_name [47, 116, 109, 112, 47, 120, 47] = none := by decide
/-- "/tmp/a".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_a : read_cstr (open_path_mem [47, 116, 109, 112, 47, 97]) 8192
    = CstrOk [47, 116, 109, 112, 47, 97] := rfl
/-- "/tmp//x".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_double_slash_x : read_cstr (open_path_mem [47, 116, 109, 112, 47, 47, 120]) 8192
    = CstrOk [47, 116, 109, 112, 47, 47, 120] := rfl
/-- "/tmp/x/".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_tmp_x_slash : read_cstr (open_path_mem [47, 116, 109, 112, 47, 120, 47]) 8192
    = CstrOk [47, 116, 109, 112, 47, 120, 47] := rfl
/-- "/tmp/a".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_a : cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 47, 97]) 8192 path_max = 7 := rfl
/-- "/tmp//x".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_double_slash_x :
    cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 47, 47, 120]) 8192 path_max = 8 := rfl
/-- "/tmp/x/".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_tmp_x_slash :
    cstr_access_len_aux (open_path_mem [47, 116, 109, 112, 47, 120, 47]) 8192 path_max = 8 := rfl

attribute [sys_simp]
  lookup_tmp_sibling_a under_tmp_sibling_a lookup_tmp_name255_held under_tmp_name255_held
  tmp_name_edges read_tmp_a read_tmp_double_slash_x read_tmp_x_slash
  len_tmp_a len_tmp_double_slash_x len_tmp_x_slash

attribute [sys_simp]
  in_arg_mkInput_0 in_arg_mkInput_1 in_arg_mkInput_2
  fs_lookup_nil lookup_have_f lookup_have_a lookup_under_a lookup_under_c lookup_under_ab
  lookup_sibling_a lookup_exact_a lookup_localtime_key lookup_localtime_under
  lookup_devnull_key lookup_devnull_under lookup_urandom_key lookup_urandom_under
  lookup_exact_localtime lookup_tmp_held_x lookup_tmp_dir_d
  tmp_name_literals tmp_name_long
  read_a read_f read_c read_dot read_dotdot read_dot3 read_empty read_slash_a read_a_slash_b
  read_localtime read_localtime_double_slash read_localtime_double_root read_localtime_prefix
  read_localtime_extended read_devnull read_devnull_double_slash read_devnull_prefix
  read_urandom read_urandom_double_slash read_dev_random
  read_null_pointer read_runoff read_tmp_x read_tmp_d read_tmp_d_f read_tmp_dir read_tmp_slash
  read_tmp_dot read_tmp_dotdot read_tmpfoo read_tmp_name255 read_tmp_name256
  len_a len_f len_c len_dot len_dotdot len_dot3 len_empty len_slash_a len_a_slash_b
  len_localtime len_localtime_double_slash len_localtime_double_root len_localtime_prefix
  len_localtime_extended len_devnull len_devnull_double_slash len_devnull_prefix
  len_urandom len_urandom_double_slash len_dev_random
  len_null_pointer len_runoff len_tmp_x len_tmp_d len_tmp_d_f len_tmp_dir len_tmp_slash
  len_tmp_dot len_tmp_dotdot len_tmpfoo len_tmp_name255 len_tmp_name256

/-! ### The readings a forged errno leaves behind an errno alternation

A refutation of a wrong errno against an arm that alternates over
`openat_errnos` normalises to a chain `∀ e, ret = errno_ret e → m' = m →
evs = [] → ¬ e = errno` per admitted errno; when the arm is reached only in
the ground pass, the chain survives it.  These two readings (the socket
port's) turn each into the conjunction the same pass decides. -/

/-- The three-antecedent chain a forged `Ok` leaves behind the errno.
model: a propositional reading for the normal form; no kernel claim -/
theorem forall_imp3_not_eq {α : Sort _} {p q r : α → Prop} {b : α} :
    (∀ a, p a → q a → r a → ¬ a = b) ↔ ¬ (p b ∧ q b ∧ r b) := by
  constructor
  · intro h hc
    exact h b hc.1 hc.2.1 hc.2.2 rfl
  · intro h a hp hq hr hab
    subst hab
    exact h ⟨hp, hq, hr⟩

/-- The two-antecedent chain, when one equation was already decided.
model: a propositional reading for the normal form; no kernel claim -/
theorem forall_imp2_not_eq {α : Sort _} {p q : α → Prop} {b : α} :
    (∀ a, p a → q a → ¬ a = b) ↔ ¬ (p b ∧ q b) := by
  constructor
  · intro h hc
    exact h b hc.1 hc.2 rfl
  · intro h a hp hq hab
    subst hab
    exact h ⟨hp, hq⟩

attribute [sys_simp] forall_imp3_not_eq forall_imp2_not_eq

/-- A forged outcome: return `r`, the pathname ledger of `n` bytes, and
whatever model and events a lying kernel might claim. -/
def forged (r : word) (n : Nat) (m' : Model) (evs : List event) : outcome SyscallEffect :=
  Ok (with_copyins [(8192, n)] (mkEffect r [] [])) m' evs

/-- The same with an errno in a0. -/
def forged_errno (e : Int) (n : Nat) (m' : Model) (evs : List event) : outcome SyscallEffect :=
  forged (errno_ret e) n m' evs

attribute [sys_simp low] forged.eq_1 forged_errno.eq_1

/-! ## `SYSCALL_DEFINE4(openat, …)` and `build_open_how`: the `int` arguments

`dfd` and `flags` are `int` at the boundary (fs/open.c:1463-1464, Linux
v6.18.46, commit 1f99e9ab748f), so bits 32-63 of both registers are gone
before anything reads them.  The table narrows `dirfd` with `fd32`, so
AT_FDCWD is recognized in either 64-bit spelling; the flags word is read
whole by `modeled_open_flags`, so every bit above the interpreted ones is
declined — a narrowing on both sides of the `int`: bits 32-63 are gone at
the cast, and bits 23-31 survive it only for `build_open_how`
(fs/open.c:1222-1236, Linux v6.18.46) to mask off with VALID_OPEN_FLAGS
(include/linux/fcntl.h:9-13), after which Linux opens the low bits' word. -/

/-- AT_FDCWD as the 64-bit -100 and as its low 32 bits, 2^32 - 100, are the
same call: `path_init` compares the `int` (fs/namei.c:2590), and the table's
`fd32` is that narrowing.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem at_fdcwd_low_half_is_at_fdcwd (o : outcome SyscallEffect) :
    syscall_spec (openat_in' 4294967196 8192 0 (open_path_mem [102])) have_model o ↔
      syscall_spec (openat_in [102] 0) have_model o := by
  sys_norm

/-- …and a high half above it is dropped too: 2^32 + (2^32 - 100) is
AT_FDCWD to an `int` parameter.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem at_fdcwd_high_half_dropped (o : outcome SyscallEffect) :
    syscall_spec (openat_in' 8589934492 8192 0 (open_path_mem [102])) have_model o ↔
      syscall_spec (openat_in [102] 0) have_model o := by
  sys_norm

/-- A flags word with bit 32 set is declined, whatever the low half says:
Linux would truncate it to O_RDONLY and open the file, and the model reads
all 64 bits instead of the `int` (the narrowing named on
`modeled_open_flags`).  A gap, not an empty intersection.
kernel: fs/open.c:build_open_how@v6.18.46 -/
theorem flags_high_half_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 4294967296) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the descriptor Linux hands out for it is refused rather than
admitted: the decline is fail-closed, not a guess at O_RDONLY.
kernel: fs/open.c:build_open_how@v6.18.46 -/
theorem flags_high_half_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 4294967296) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- Bit 31 (2147483648) is declined too, and Linux drops it by the OTHER
mechanism: it survives the `int` cast, and `build_open_how` masks it off
with VALID_OPEN_FLAGS (fs/open.c:1225, Linux v6.18.46; the mask,
include/linux/fcntl.h:9-13, tops out at bit 22), so Linux opens "f"
O_RDONLY where the model, reading all 64 bits, declines.
kernel: fs/open.c:build_open_how@v6.18.46 -/
theorem flags_bit_31_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 2147483648) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …its descriptor refused…
kernel: fs/open.c:build_open_how@v6.18.46 -/
theorem flags_bit_31_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 2147483648) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- …and bit 23 (8388608), the first bit above the mask, the same way.
kernel: fs/open.c:build_open_how@v6.18.46 -/
theorem flags_bit_23_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 8388608) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …descriptor refused.
kernel: fs/open.c:build_open_how@v6.18.46 -/
theorem flags_bit_23_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 8388608) have_model (forged 3 2 m' evs) := by
  sys_refute

/-! ## `build_open_flags`: the flag gate, before any pathname is read

`do_sys_openat2` (fs/open.c:1420-1447, Linux v6.18.46, commit
1f99e9ab748f) runs build_open_flags at :1427-1429 and only then getname
at :1431, so a
combination the kernel rejects never reaches the pathname.  The model's
gate is `modeled_open_flags`, tested in `openat_core_spec` before
`openat_body_spec` fetches the path; the pins below pass an UNMAPPED
pathname pointer, which the fetch would answer -EFAULT, and require the
decline to come first. -/

/-- O_NOCTTY (256) over an unmapped pathname is `Unmodeled`, not -EFAULT:
the gate fires before the fetch.  The bit is declined because its one
meaning needs a terminal (`tty_open`, drivers/tty/tty_io.c, Linux v6.18.46) the model has
none of.
probe: testing/syscall-check/tests/openat_nonblock.c#fail-closed -- noctty -/
theorem noctty_declines_before_the_path_is_read (o : outcome SyscallEffect) :
    syscall_spec (openat_in' AT_FDCWD 8192 256 (fun _ => none)) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the -EFAULT the fetch would have answered is refused for that word.
kernel: fs/open.c:do_sys_openat2@v6.18.46 -/
theorem noctty_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in' AT_FDCWD 8192 256 (fun _ => none)) absent_model
        (forged_errno 14 1 m' evs) := by
  sys_refute

/-- THE CONTROL: the same unmapped pointer under O_RDONLY IS -EFAULT, with
the one attempted byte in the ledger — `strncpy_from_user` faults on the
first byte and `getname_flags` returns that error as it is
(fs/namei.c:157-165).  So the decline above is the gate's doing, not the
memory's.  AT_FDCWD is `path_init`'s to read (fs/namei.c:2590), and this
call ends in the fetch before `path_init` runs; the function is on the
evidence line for the constant, not the answer.
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem rdonly_unmapped_path_is_efault (o : outcome SyscallEffect) :
    syscall_spec (openat_in' AT_FDCWD 8192 0 (fun _ => none)) absent_model o ↔
      o = errno 14 1 absent_model := by
  sys_norm

/-- The declined words, each `Unmodeled` on a name the map holds, so that
the kernel's real answer — an open descriptor on most of them — is the
thing refused.  O_WRONLY|O_APPEND without O_CREAT (1025): a different
answer on an absent path, not a spelling of the append word.
probe: testing/syscall-check/tests/openat_append.c#fail-closed -- no-creat -/
theorem wronly_append_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 1025) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- O_WRONLY alone (1): Linux opens an existing file for writing; no arm
answers it (a gap, not an empty intersection).
probe: testing/syscall-check/tests/openat_path_errnos.c#fail-closed -- short-wronly -/
theorem wronly_alone_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 1) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the write descriptor Linux hands out for O_WRONLY on the existing "f": refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem wronly_alone_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 1) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- Bare O_CREAT (64), O_RDONLY|O_CREAT: Linux opens the existing "f" for
reading, and would create an absent name; no arm answers it (a gap, not an
empty intersection).
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem bare_creat_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 64) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the read descriptor Linux hands out for bare O_CREAT on the existing "f": refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem bare_creat_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 64) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_RDONLY|O_APPEND (1024): Linux reads the file and the bit is inert; no
arm answers it (a gap, not an empty intersection).
probe: testing/syscall-check/tests/openat_append.c#fail-closed -- rdonly-append -/
theorem rdonly_append_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 1024) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the read descriptor Linux hands out, the append bit inert: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdonly_append_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 1024) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- The append word with O_TRUNC (1601): truncate-then-append is its own
arm, not written.
probe: testing/syscall-check/tests/openat_append.c#fail-closed -- trunc-append -/
theorem append_trunc_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 1601) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor Linux hands out after truncating "f": refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem append_trunc_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 1601) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- The append word with O_EXCL (1217), the exclusive append word (#1752),
on the existing "f": Linux answers -EEXIST (`do_open`, fs/namei.c:3949-3950,
Linux v6.18.46), and Rocq's arm for the word (`Open.openat_append_spec`)
answers it too; this twin declines the word before that arm, which is
unported because its creation mints `FdFileA` (file header).
The probe's `exists` case (openat_excl_append.c) is the kernel's -EEXIST.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem append_excl_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 1217) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …refusing the -EEXIST `do_open`'s O_CREAT block answers for the existing "f" (fs/namei.c:3949-3950, Linux v6.18.46)
as well, so the decline is one on the WORD, not a guess at the existing name's answer.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem append_excl_eexist_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 1217) have_model (forged_errno 17 2 m' evs) := by
  sys_refute

/-- O_RDWR|O_APPEND (1026) and O_RDWR|O_CREAT|O_APPEND (1090).
probe: testing/syscall-check/tests/openat_rdwr.c#fail-closed -- append -/
theorem rdwr_append_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 1026) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the read-write descriptor Linux hands out for O_RDWR|O_APPEND: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_append_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 1026) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- …the O_CREAT spelling too.
probe: testing/syscall-check/tests/openat_rdwr.c#fail-closed -- creat-append -/
theorem rdwr_creat_append_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 1090) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the read-write descriptor Linux hands out for the O_CREAT spelling on the existing "f": refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_creat_append_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 1090) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_RDWR|O_EXCL without O_CREAT (130): Linux reads O_EXCL only inside
`do_open`'s O_CREAT block (fs/namei.c:3948-3950, Linux v6.18.46) and opens the file as
plain O_RDWR; declined rather than aliased.
probe: testing/syscall-check/tests/openat_rdwr.c#fail-closed -- excl-nocreat -/
theorem rdwr_excl_without_creat_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 130) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the plain O_RDWR descriptor Linux hands out, O_EXCL unread without O_CREAT: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_excl_without_creat_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 130) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_WRONLY|O_EXCL without O_CREAT (129), likewise.
probe: testing/syscall-check/tests/openat_excl.c#fail-closed -- no-creat -/
theorem wronly_excl_without_creat_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 129) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the write descriptor Linux hands out, O_EXCL unread without O_CREAT: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem wronly_excl_without_creat_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 129) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_RDONLY|O_EXCL (128): Linux ignores O_EXCL without O_CREAT and reads the
file; no arm answers it (a gap, not an empty intersection).
probe: testing/syscall-check/tests/openat_excl.c#fail-closed -- rdonly-excl -/
theorem rdonly_excl_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 128) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the read descriptor Linux hands out, O_EXCL unread without O_CREAT: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdonly_excl_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 128) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_RDWR|O_DIRECTORY (65538): `build_open_flags` admits it; on a directory
`may_open`'s S_IFDIR arm answers -EISDIR (fs/namei.c:3540-3542, Linux
v6.18.46), and on the regular "f" this pin names, `do_open`'s
LOOKUP_DIRECTORY test answers -ENOTDIR (:3958-3959).  Neither arm is
written.
probe: testing/syscall-check/tests/openat_rdwr.c#fail-closed -- directory -/
theorem rdwr_directory_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 65538) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -ENOTDIR `do_open` answers for the regular "f" under LOOKUP_DIRECTORY (fs/namei.c:3958-3959, Linux v6.18.46): refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_directory_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 65538) have_model (forged_errno 20 2 m' evs) := by
  sys_refute

/-- …and the open descriptor Linux hands out for O_WRONLY|O_APPEND on an
existing file is refused, so the decline is not quietly agreeing with it.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem wronly_append_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 1025) have_model (forged 3 2 m' evs) := by
  sys_refute

/-! ### The ignored bits

`build_open_flags` strips O_CLOEXEC from the open flags it gives the walk
(`u64 strip = O_CLOEXEC`, fs/open.c:1241, Linux v6.18.46 and :1251), though
Linux still records the bit in the descriptor table (`alloc_fd`,
fs/file.c:606, Linux v6.18.46) — ignorable here only because no Lean entry
carries close-on-exec; `SYSCALL_DEFINE4(openat, …)` ORs O_LARGEFILE
into every open (fs/open.c:1466-1467, Linux v6.18.46); and O_NONBLOCK reaches `f_flags`
(fs/file_table.c:198, Linux v6.18.46) and nothing a modeled arm reads.  An open with any
of them lands EXACTLY where the same open without them lands — an
equality between two flag words, which a probe (one word per run) cannot
state. -/

/-- O_RDONLY|O_NONBLOCK is O_RDONLY.
rocq-twin: o_nonblock_is_an_ignored_open_flag
probe: testing/syscall-check/tests/openat_nonblock.c#conform -- rdonly -/
theorem nonblock_read_lands_where_read_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 2048) have_model o ↔ syscall_spec (openat_in [102] 0) have_model o := by
  sys_norm

/-- All three bits at once, on the read word.
probe: testing/syscall-check/tests/openat_nonblock.c#conform -- all-ignored -/
theorem all_ignored_bits_land_where_read_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 559104) have_model o ↔ syscall_spec (openat_in [102] 0) have_model o := by
  sys_norm

/-- The clobbering create with O_NONBLOCK.
rocq-twin: o_nonblock_is_an_ignored_open_flag
probe: testing/syscall-check/tests/openat_nonblock.c#conform -- create -/
theorem nonblock_create_lands_where_create_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 2625) absent_model o ↔ syscall_spec (openat_in [97] 577) absent_model o := by
  sys_norm

/-- The exclusive create with O_NONBLOCK, and with O_TRUNC beside it.
rocq-twin: o_nonblock_is_an_ignored_open_flag
probe: testing/syscall-check/tests/openat_nonblock.c#conform -- excl -/
theorem nonblock_excl_lands_where_excl_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 2241) absent_model o ↔ syscall_spec (openat_in [97] 193) absent_model o := by
  sys_norm

/-- …with O_TRUNC beside it as well.
probe: testing/syscall-check/tests/openat_nonblock.c#conform -- excl-trunc -/
theorem nonblock_excl_trunc_lands_where_excl_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 2753) absent_model o ↔ syscall_spec (openat_in [97] 193) absent_model o := by
  sys_norm

/-- The two exclusive spellings are ONE branch: O_EXCL fails outright on an
existing path (`do_open`, fs/namei.c:3949-3950, Linux v6.18.46) and `lookup_open` drops
O_TRUNC under O_CREAT|O_EXCL (:3755-3756), so O_TRUNC never fires beside
it.
probe: testing/syscall-check/tests/openat_excl.c#conform -- create-notrunc -/
theorem excl_trunc_spelling_is_the_excl_word (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 705) absent_model o ↔ syscall_spec (openat_in [97] 193) absent_model o := by
  sys_norm

/-- …on an existing path too.
probe: testing/syscall-check/tests/openat_excl.c#conform -- exists-notrunc -/
theorem excl_trunc_spelling_is_the_excl_word_on_existing (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 705) have_model o ↔ syscall_spec (openat_in [102] 193) have_model o := by
  sys_norm

/-- …and on ".", where the O_CREAT block's -EEXIST (`do_open`,
fs/namei.c:3949-3950, Linux v6.18.46) fires before O_TRUNC is read: the
bridge that lets the probe openat_excl.c's "dot" cases, whose word is
705, stand beside the 193 pins on ".".
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem dot_excl_trunc_spelling_is_the_excl_word (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46] 705) absent_model o ↔ syscall_spec (openat_in [46] 193) absent_model o := by
  sys_norm

/-- O_CLOEXEC|O_LARGEFILE on the exclusive create.
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem cloexec_largefile_excl_lands_where_excl_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 557249) absent_model o ↔ syscall_spec (openat_in [97] 193) absent_model o := by
  sys_norm

/-- …and with O_TRUNC beside them: the word the probe's "create-cloexec"
case passes.
probe: testing/syscall-check/tests/openat_excl.c#conform -- create-cloexec -/
theorem excl_trunc_cloexec_largefile_lands_where_excl_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 557761) absent_model o ↔ syscall_spec (openat_in [97] 193) absent_model o := by
  sys_norm

/-- …and O_NONBLOCK beside O_NOCTTY does not rescue it: the gate is a set
of WORDS modulo the ignored bits, not a bit test.
probe: testing/syscall-check/tests/openat_nonblock.c#fail-closed -- noctty-nb -/
theorem noctty_nonblock_still_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 2304) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the read descriptor Linux hands out, O_NOCTTY meaningless off a terminal and O_NONBLOCK inert: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem noctty_nonblock_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 2304) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_DIRECTORY|O_CREAT (65600) is declined: at v6.18.46 `build_open_flags`
answers -EINVAL for the pair (fs/open.c:1283-1284, Linux v6.18.46; commit
43b450632676 "open: return EINVAL for O_DIRECTORY | O_CREAT", v6.4, in stable
6.1 from 6.1.30), where the kernels its own comment recalls (:1279-1282)
created a regular file and either handed it back, `do_last` jumping past the
directory test once the file was created (fs/namei.c:3295-3302 and
:3348-3350, Linux v4.17; so through v5.6), or failed that test on it with
-ENOTDIR (`do_open`, fs/namei.c:3958-3959, Linux v6.18.46: the test v5.7
introduced, at fs/namei.c:3212-3213 there, and the pair reached through v6.3).
Three answers across the supported range, so the arm is `unmodeled` and
agrees with none.
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem creat_directory_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 65600) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -EINVAL refused…
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem creat_directory_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 65600) absent_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- …as is the regular file the older kernels created…
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem creat_directory_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 65600) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- …and the -ENOTDIR the kernels from v5.7 through v6.3 answered after
creating it.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem creat_directory_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 65600) absent_model (forged_errno 20 2 m' evs) := by
  sys_refute

/-! ## `getname_flags`: the three fetch answers, before the dirfd

`getname_flags` (fs/namei.c:136-216, Linux v6.18.46, commit 1f99e9ab748f)
returns `strncpy_from_user`'s -EFAULT as it is (:157, :161-165), turns the
empty path into -ENOENT (:167-171; `getname` passes no LOOKUP_EMPTY,
include/linux/fs.h:2944-2947) and a copy that reaches PATH_MAX into
-ENAMETOOLONG (:207-210).  All three are decided in `do_sys_openat2`
(fs/open.c:1431-1435, Linux v6.18.46) before the descriptor is allocated and before `path_init`
looks at the dirfd (fs/namei.c:2589-2632, Linux v6.18.46, inside `path_openat` :4133), so
they are deterministic AND they beat the dirfd. -/

/-- The empty pathname is -ENOENT with the one NUL byte in the ledger, and
the model is untouched.
probe: testing/syscall-check/tests/openat_empty_enoent.c#conform -/
theorem empty_path_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (openat_in [] 0) absent_model o ↔ o = errno 2 1 absent_model := by
  sys_norm

/-- …and it never matches an empty-path KEY in the image: Rocq's case holds
one byte under the key `[]`, and the answer is the same -ENOENT, the key
untouched — `getname_flags` answers before any lookup (fs/namei.c:167-171,
Linux v6.18.46).
rocq-twin: openat_empty_path_enoent
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_is_enoent_with_an_empty_key (o : outcome SyscallEffect) :
    syscall_spec (openat_in [] 0) empty_key_model o ↔ o = errno 2 1 empty_key_model := by
  sys_norm

/-- …and a descriptor for it is refused.
probe: testing/syscall-check/tests/openat_empty_enoent.c#reject --mutate openat#1:ret=3 -/
theorem empty_path_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [] 0) absent_model (forged 3 1 m' evs) := by
  sys_refute

/-- THE EMPTY PATHNAME BEATS O_CREAT: the fetch answers before any arm runs,
so no key spelled "" is ever minted.
rocq-twin: openat_empty_path_beats_o_creat
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_beats_o_creat (o : outcome SyscallEffect) :
    syscall_spec (openat_in [] 577) absent_model o ↔ o = errno 2 1 absent_model := by
  sys_norm

/-- …a kernel claiming the create SUCCEEDED is refused.
rocq-twin: openat_empty_path_beats_o_creat
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [] 577) absent_model (forged 3 1 m' evs) := by
  sys_refute

/-- The O_TRUNC spelling of the exclusive word on the empty path is the same
-ENOENT from the fetch, never -EEXIST and never a create: the exact shape
the probe's "empty" cases run.
probe: testing/syscall-check/tests/openat_excl.c#conform -- empty -/
theorem empty_path_excl_trunc_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (openat_in [] 705) absent_model o ↔ o = errno 2 1 absent_model := by
  sys_norm

/-- …a claimed create refused…
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat:ret=3 -- empty -/
theorem empty_path_excl_trunc_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [] 705) absent_model (forged 3 1 m' evs) := by
  sys_refute

/-- …and -EEXIST refused: the empty path is not "already there".
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat:ret=-EEXIST -- empty -/
theorem empty_path_excl_trunc_eexist_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [] 705) absent_model (forged_errno 17 1 m' evs) := by
  sys_refute

/-- …and the two exclusive spellings are one answer on "": the fetch decides
before any flag but the gate's is read, so the author's 193 pins and the
probe's 705 cases above are the same claim.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_excl_trunc_spelling_is_the_excl_word (o : outcome SyscallEffect) :
    syscall_spec (openat_in [] 705) absent_model o ↔ syscall_spec (openat_in [] 193) absent_model o := by
  sys_norm

/-- …and the exclusive word does not make "" "already there": -ENOENT, not
-EEXIST.
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat:ret=-EEXIST -- empty -/
theorem empty_path_excl_eexist_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [] 193) absent_model (forged_errno 17 1 m' evs) := by
  sys_refute

/-- The empty path is not a directory either: -EISDIR is refused on the
append word, where "." would answer it.
probe: testing/syscall-check/tests/openat_append.c#reject --mutate openat:ret=-EISDIR -- empty -/
theorem empty_path_append_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [] 1089) absent_model (forged_errno 21 1 m' evs) := by
  sys_refute

/-- …and the answer the append word gets on the empty path is stated, not
only fenced: -ENOENT from the fetch, ahead of the flag dispatch, the shape
the probe's "empty" case runs.
probe: testing/syscall-check/tests/openat_append.c#conform -- empty -/
theorem empty_path_append_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (openat_in [] 1089) absent_model o ↔ o = errno 2 1 absent_model := by
  sys_norm

/-- …with a claimed descriptor refused: `getname_flags` returns -ENOENT on
the empty copy before any arm could create (fs/namei.c:167-171).
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem empty_path_append_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [] 1089) absent_model (forged 3 1 m' evs) := by
  sys_refute

/-- A NULL pathname pointer is -EFAULT, with the one attempted byte at 0
recorded: `strncpy_from_user` faults at once and `getname_flags` returns
the error (fs/namei.c:157-165, Linux v6.18.46).
probe: testing/syscall-check/tests/openat_path_errnos.c#conform -- fault-null -/
theorem null_pointer_is_efault (o : outcome SyscallEffect) :
    syscall_spec (openat_in' AT_FDCWD 0 0 (open_path_mem [97])) absent_model o ↔
      o = Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 14) [] [])) absent_model [] := by
  sys_norm

/-- …not -ENOENT, the other fetch failure.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:ret=-ENOENT -- fault-null -/
theorem null_pointer_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in' AT_FDCWD 0 0 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 2) [] [])) m' evs) := by
  sys_refute

/-- …nor -ENAMETOOLONG.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:ret=-ENAMETOOLONG -- fault-null -/
theorem null_pointer_enametoolong_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in' AT_FDCWD 0 0 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 36) [] [])) m' evs) := by
  sys_refute

/-- …and the ledger cannot be dropped: an -EFAULT that recorded no read is
refused, since the kernel issued the access.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:drop-copyins -- fault-null -/
theorem null_pointer_without_the_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in' AT_FDCWD 0 0 (open_path_mem [97])) absent_model
        (Ok (mkEffect (errno_ret 14) [] []) m' evs) := by
  sys_refute

/-- Mapped bytes whose NUL is unmapped: -EFAULT after the mapped byte and
the faulting one, two bytes in the ledger.
probe: testing/syscall-check/tests/openat_path_errnos.c#conform -- fault-runoff -/
theorem runoff_is_efault (o : outcome SyscallEffect) :
    syscall_spec (openat_in' AT_FDCWD 8192 0 (bytes_at 8192 [97])) absent_model o ↔
      o = errno 14 2 absent_model := by
  sys_norm

/-- …on the create arm too, minting nothing: the fetch fails before any arm.
probe: testing/syscall-check/tests/openat_path_errnos.c#conform -- fault-runoff-create -/
theorem runoff_create_is_efault (o : outcome SyscallEffect) :
    syscall_spec (openat_in' AT_FDCWD 8192 577 (bytes_at 8192 [97])) absent_model o ↔
      o = errno 14 2 absent_model := by
  sys_norm

/-- …and a claimed success on the run-off path is refused.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat#1:ret=3 -- fault-runoff -/
theorem runoff_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in' AT_FDCWD 8192 0 (bytes_at 8192 [97])) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- The ledger ends at the NUL: a two-byte fetch of ".\0" that claims three
bytes is refused (`getname` reads no further than the string, whatever
word `strncpy_from_user` loads; bugs/openat-getname-word-at-a-time.md).
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:grow-copyins:1 -- ok-dot-open -/
theorem ledger_ends_at_the_nul (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 0) absent_model (forged 3 3 m' evs) := by
  sys_refute

/-- …and cannot be omitted on a success either.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:drop-copyins -- ok-dot-open -/
theorem ledger_cannot_be_dropped (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 0) absent_model (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-- A pathname with no NUL within PATH_MAX is -ENAMETOOLONG, whatever bytes
it holds: stated over any memory whose fetch says so, since a 4096-step
walk is not a thing to evaluate.  The ledger is whatever `getname` read,
recorded symbolically.  The proof reads the spec off its primitives, then
hands the fetch result to `simp` and reads the rest.
probe: testing/syscall-check/tests/openat_path_errnos.c#conform -- toolong -/
theorem too_long_is_enametoolong (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (o : outcome SyscallEffect) :
    openat_spec 4294967196 8192 0 i absent_model o ↔
      o = Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
               (mkEffect (errno_ret 36) [] [])) absent_model [] := by
  sys_simp_pass +decide
  simp only [hp]
  sys_norm

/-- …not -EFAULT: the two fetch failures are not interchangeable.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:ret=-EFAULT -- toolong -/
theorem too_long_efault_rejected (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (m' : Model) (evs : List event) :
    ¬ openat_spec 4294967196 8192 0 i absent_model
        (Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
              (mkEffect (errno_ret 14) [] [])) m' evs) := by
  intro h
  sys_simp_pass +decide at h
  simp only [hp] at h
  sys_refute at h

/-- …and not a success.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:ret=3 -- toolong -/
theorem too_long_fd_rejected (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (m' : Model) (evs : List event) :
    ¬ openat_spec 4294967196 8192 0 i absent_model
        (Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
              (mkEffect 3 [] [])) m' evs) := by
  intro h
  sys_simp_pass +decide at h
  simp only [hp] at h
  sys_refute at h

/-- -ENAMETOOLONG is never injectable: it is the fetch's deterministic
answer, and the plain "." open that CAN take an injected -ENOMEM refuses
it.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:ret=-ENAMETOOLONG -- ok-dot-open -/
theorem enametoolong_not_injectable (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 0) absent_model (forged_errno 36 2 m' evs) := by
  sys_refute

/-- …while -ENOMEM is, on that same open.
probe: testing/syscall-check/tests/openat_path_errnos.c#conform --mutate openat:ret=-ENOMEM -- ok-dot-open -/
theorem dot_open_enomem_admitted :
    syscall_spec (openat_in [46] 0) absent_model (errno 12 2 absent_model) := by
  sys_norm

/-! ### The fetch beats the dirfd

`path_init` resolves the dirfd (fs/namei.c:2589-2632, Linux v6.18.46) after `getname`
has answered (fs/open.c:1431, Linux v6.18.46), so an over-long, faulting or empty path
answers its errno even when the dirfd is one the model declines — and
never the -EBADF `fd_empty` would answer for a closed dirfd (:2610-2611),
which comes later. -/

/-- The empty path with a closed dirfd (5) is -ENOENT, ahead of the dirfd.
probe: testing/syscall-check/tests/openat_path_errnos.c#conform -- empty-dirfd -/
theorem empty_path_beats_the_dirfd (o : outcome SyscallEffect) :
    syscall_spec (openat_in' 5 8192 0 (open_path_mem [])) absent_model o ↔ o = errno 2 1 absent_model := by
  sys_norm

/-- …and the dirfd's -EBADF is refused there.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:ret=-EBADF -- empty-dirfd -/
theorem empty_path_dirfd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in' 5 8192 0 (open_path_mem [])) absent_model (forged_errno 9 1 m' evs) := by
  sys_refute

/-- A NULL pointer with a closed dirfd: -EFAULT wins over the dirfd.
probe: testing/syscall-check/tests/openat_path_errnos.c#conform -- fault-null-dirfd -/
theorem null_pointer_beats_the_dirfd (o : outcome SyscallEffect) :
    syscall_spec (openat_in' 5 0 0 (open_path_mem [97])) absent_model o ↔
      o = Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 14) [] [])) absent_model [] := by
  sys_norm

/-- An over-long path with a closed dirfd: -ENAMETOOLONG, ahead of the dirfd.
probe: testing/syscall-check/tests/openat_path_errnos.c#conform -- toolong-dirfd -/
theorem too_long_beats_the_dirfd (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (o : outcome SyscallEffect) :
    openat_spec 5 8192 0 i absent_model o ↔
      o = Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
               (mkEffect (errno_ret 36) [] [])) absent_model [] := by
  sys_simp_pass +decide
  simp only [hp]
  sys_norm

/-- …and the -EBADF is refused for it.
probe: testing/syscall-check/tests/openat_path_errnos.c#reject --mutate openat:ret=-EBADF -- toolong-dirfd -/
theorem too_long_dirfd_ebadf_rejected (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (m' : Model) (evs : List event) :
    ¬ openat_spec 5 8192 0 i absent_model
        (Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
              (mkEffect (errno_ret 9) [] [])) m' evs) := by
  intro h
  sys_simp_pass +decide at h
  simp only [hp] at h
  sys_refute at h

/-- The flag gate beats even the over-long path: O_WRONLY|O_APPEND is
`Unmodeled` over ANY memory — the probe's is one whose fetch would be
-ENAMETOOLONG — because the MODEL's `modeled_open_flags` gate fires before
its fetch, so no fact about the pathname bytes is needed to state it.  Linux
itself accepts the word (1025 is inside VALID_OPEN_FLAGS,
include/linux/fcntl.h:9-13, Linux v6.18.46, and no -EINVAL exit of
`build_open_flags`, fs/open.c:1258-1301, Linux v6.18.46, fires on it), does
fetch, and answers -ENAMETOOLONG; the probe grades that answer beside the
fail-closed verdict.
probe: testing/syscall-check/tests/openat_path_errnos.c#fail-closed -- toolong-append -/
theorem too_long_append_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    openat_spec 4294967196 8192 1025 i absent_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## `path_init`: the dirfd

`path_init` (fs/namei.c:2540-2645, Linux v6.18.46) starts a relative walk at the working
directory for AT_FDCWD (:2590-2604) and otherwise at the dirfd's file
(:2605-2632): -EBADF on a closed fd (:2610-2611), -ENOTDIR on an open one
that is not a directory (:2621-2622), and a walk under a directory the
flat map cannot represent otherwise.  The model answers AT_FDCWD only and
declines the rest — never with one of those errnos, which it cannot judge
without knowing what the fd names. -/

/-- dirfd 1 (an open channel) with a plain name is `Unmodeled`, not the
-ENOTDIR Linux answers for a non-directory dirfd.
rocq-twin: openat_live_dirfd_still_unmodeled
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem dirfd_1_declines_the_read (o : outcome SyscallEffect) :
    syscall_spec (openat_in' 1 8192 0 (open_path_mem [102])) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …refusing the -ENOENT Rocq's case offers, the kernel's -ENOTDIR, and a
descriptor alike.
rocq-twin: openat_live_dirfd_still_unmodeled
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem dirfd_1_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in' 1 8192 0 (open_path_mem [102])) have_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- The kernel's own -ENOTDIR for it is refused too: the model declines
rather than answers.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem dirfd_1_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in' 1 8192 0 (open_path_mem [102])) have_model (forged_errno 20 2 m' evs) := by
  sys_refute

/-- A closed dirfd (5) with a plain name declines rather than answering
`fd_empty`'s -EBADF.
probe: testing/syscall-check/tests/openat_path_errnos.c#fail-closed -- short-dirfd -/
theorem dirfd_5_declines_the_read (o : outcome SyscallEffect) :
    syscall_spec (openat_in' 5 8192 0 (open_path_mem [102])) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the -EBADF is refused, as is a descriptor.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem dirfd_5_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in' 5 8192 0 (open_path_mem [102])) have_model (forged_errno 9 2 m' evs) := by
  sys_refute

/-- A dirfd of 2^32 is fd 0 to the `int` parameter, an open channel: the
same decline as dirfd 1, not AT_FDCWD.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem dirfd_2_32_is_fd_0_and_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in' 4294967296 8192 0 (open_path_mem [102])) have_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## `link_path_walk`: the separator decline

The interpreted file system is a flat map with no directory structure.
`link_path_walk` (fs/namei.c:2441-2537, Linux v6.18.46) walks every interior component
through the filesystem before `open_last_lookups` and `do_open` read a
flag, and none of its answers — the -ENOENT of a missing parent, the
-ENOTDIR of a non-directory component (:2529-2535), the directory a
trailing slash names — is something a flat key can stand for.  So a
pathname with a separator is declined ahead of the flag test, with the
device and localtime exceptions pinned in their own sections. -/

/-- The write-create open of "/a" is `Unmodeled`, whether the kernel is
offered as having succeeded at fd 3 or as having failed -ENOENT: the
decline does not depend on what the kernel said.
rocq-twin: openat_absolute_create_unmodeled
probe: testing/syscall-check/tests/openat_flat_namespace.c#fail-closed --expect-unmodeled openat -- abs-create -/
theorem absolute_create_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 97] 577) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the success refused: before the guard the create arm minted a key
spelled "/a" and answered fd 3 where Linux resolves a directory it never
looked in.
rocq-twin: openat_absolute_create_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem absolute_create_declines_a_success (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 97] 577) absent_model (forged 3 3 m' evs) := by
  sys_refute

/-- …and the -ENOENT refused as well.
rocq-twin: openat_absolute_create_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem absolute_create_declines_an_enoent (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 97] 577) absent_model (forged_errno 2 3 m' evs) := by
  sys_refute

/-- The read of "/a" declines too, refusing the -ENOENT Linux answers for a
missing file under the root.
probe: testing/syscall-check/tests/openat_flat_namespace.c#fail-closed --expect-unmodeled openat -- abs-read -/
theorem absolute_read_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 97] 0) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE CONTROL: the identical call on a slash-free name is not declined; it
succeeds at the lowest free fd and the key appears in the model's file
system.  So the guard discriminates on the path SHAPE.
rocq-twin: openat_plain_create_still_mints_the_key
probe: testing/syscall-check/tests/openat_flat_namespace.c#conform -- plain-create -/
theorem plain_create_mints_the_key (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 577) absent_model o ↔
      (env_errnos 2 absent_model o ∨
       o = ret 3 2 (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])]))) := by
  sys_norm

/-- A KEY SPELLED WITH A SEPARATOR is declined even when the map holds it:
whether "a/b" is reachable depends on "a" being a directory, which the map
does not say.
rocq-twin: openat_slash_key_in_image_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem slash_key_in_image_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97, 47, 98] 0) under_model o ↔ o = Unmodeled := by
  sys_norm

/-- …refusing the descriptor a "just return the key" model would hand out.
rocq-twin: openat_slash_key_in_image_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem slash_key_in_image_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97, 47, 98] 0) under_model (forged 3 4 m' evs) := by
  sys_refute

/-! ## `handle_dots`: "." and ".."

`link_path_walk` types the last component LAST_DOT or LAST_DOTDOT
(fs/namei.c:2475-2482, Linux v6.18.46, commit 1f99e9ab748f) and
`open_last_lookups` takes them to `handle_dots` (:3859-3863) before O_CREAT
is considered, so the dentry `do_open` sees is a directory with
FMODE_CREATED clear.  Its three answers (:3948-3952): -EEXIST under O_EXCL,
-EISDIR under O_CREAT, and under O_RDONLY the directory `may_open`'s
S_IFDIR arm admits (:3540-3545) — the same for both spellings. -/

/-- "." under O_RDONLY: a directory fd at the lowest free slot, or an
environment errno with nothing changed.
rocq-twin: openat_dotdot_answers_as_dot_does
probe: testing/syscall-check/tests/dirfd_spec.c#conform -- open -/
theorem dot_read_is_a_directory_fd (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46] 0) absent_model o ↔
      (env_errnos 2 absent_model o ∨ o = ret 3 2 (fixture_of (fds := (3, .FdDir) :: init_fds))) := by
  sys_norm

/-- ".." the same, with three bytes in the ledger.
rocq-twin: openat_dotdot_answers_as_dot_does
probe: testing/syscall-check/tests/openat_flat_namespace.c#conform -- dotdot-read -/
theorem dotdot_read_is_a_directory_fd (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46, 46] 0) absent_model o ↔
      (env_errnos 3 absent_model o ∨ o = ret 3 3 (fixture_of (fds := (3, .FdDir) :: init_fds))) := by
  sys_norm

/-- ".." is never absent: the -ENOENT a flat map would answer for it is
refused (the answer the model used to give).
probe: testing/syscall-check/tests/openat_flat_namespace.c#reject --mutate openat:ret=-ENOENT -- dotdot-read -/
theorem dotdot_read_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46, 46] 0) absent_model (forged_errno 2 3 m' evs) := by
  sys_refute

/-- "." under O_RDONLY is not -EISDIR: `may_open` refuses a directory only
under MAY_WRITE (fs/namei.c:3541-3542), which O_RDONLY does not carry.
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem dot_read_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 0) absent_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-- The directory fd is the lowest free one: 4 is refused.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem dot_read_non_lowest_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 0) absent_model (forged 4 2 m' evs) := by
  sys_refute

/-- The clobbering create of "." is -EISDIR — `do_open`'s `d_is_dir`
inside its O_CREAT block (fs/namei.c:3951-3952, Linux v6.18.46) — deterministic, and the
model is untouched.
rocq-twin: openat_dotdot_answers_as_dot_does
probe: testing/syscall-check/tests/dirfd_spec.c#conform -- create -/
theorem dot_create_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46] 577) absent_model o ↔ o = errno 21 2 absent_model := by
  sys_norm

/-- ".." likewise.
rocq-twin: openat_dotdot_answers_as_dot_does
probe: testing/syscall-check/tests/openat_flat_namespace.c#conform -- dotdot-create -/
theorem dotdot_create_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46, 46] 577) absent_model o ↔ o = errno 21 3 absent_model := by
  sys_norm

/-- A claimed success on the create shape is REFUSED for ".", which is what
makes the -EISDIR real rather than a model that declines everything.
rocq-twin: openat_dotdot_answers_as_dot_does
probe: testing/syscall-check/tests/dirfd_spec.c#reject --mutate openat:ret=3 -- create -/
theorem dot_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 577) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- …and for "..", which the create arm used to answer by minting a key
spelled "..".
rocq-twin: openat_dotdot_answers_as_dot_does
probe: testing/syscall-check/tests/openat_flat_namespace.c#reject --mutate openat:ret=3 -- dotdot-create -/
theorem dotdot_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46, 46] 577) absent_model (forged 3 3 m' evs) := by
  sys_refute

/-- The clobbering word does not answer -EEXIST for ".": that errno is
O_EXCL's (fs/namei.c:3949-3950, Linux v6.18.46), tested first and only under O_EXCL.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem dot_create_eexist_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 577) absent_model (forged_errno 17 2 m' evs) := by
  sys_refute

/-- The exclusive create of "." is -EEXIST: O_EXCL against FMODE_CREATED
(fs/namei.c:3949-3950, Linux v6.18.46) is decided before `d_is_dir`, and "." exists.
probe: testing/syscall-check/tests/openat_excl.c#conform -- dot -/
theorem dot_excl_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46] 193) absent_model o ↔ o = errno 17 2 absent_model := by
  sys_norm

/-- ".." likewise.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem dotdot_excl_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46, 46] 193) absent_model o ↔ o = errno 17 3 absent_model := by
  sys_norm

/-- …NOT -EISDIR: existence is resolved first.
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat:ret=-EISDIR -- dot -/
theorem dot_excl_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 193) absent_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-- …and no kernel opens "." exclusively.
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat:ret=3 -- dot -/
theorem dot_excl_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 193) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- "..." IS AN ORDINARY NAME: `path_is_dirref` is an equality against the
two constants, so the create arm mints a key for it exactly as for "f".  A
prefix or leading-".." test would break this silently.
rocq-twin: openat_dot3_is_an_ordinary_name
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem dot3_is_an_ordinary_name (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46, 46, 46] 577) absent_model o ↔
      (env_errnos 4 absent_model o ∨
       o = ret 3 4 (fixture_of (fds := (3, .FdFileW [46, 46, 46] 0) :: init_fds)
                                (fs := [([46, 46, 46], [])]))) := by
  sys_norm

/-- …so the -EISDIR "." and ".." get is refused for it.
rocq-twin: openat_dot3_is_an_ordinary_name
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem dot3_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46, 46, 46] 577) absent_model (forged_errno 21 4 m' evs) := by
  sys_refute

/-! ## `lookup_open` and `do_open`: plain names, by word

For a LAST_NORM component `open_last_lookups` reaches the name by
`lookup_fast_for_open` (fs/namei.c:3817-3846, Linux v6.18.46) or `lookup_open`
(:3698-3810), and `do_open` (:3931-3987) decides: -EEXIST under O_EXCL on
an uncreated name (:3949-3950), -EISDIR on a directory under O_CREAT
(:3951-3952), -ENOTDIR under LOOKUP_DIRECTORY (:3958-3959), truncation
only on a regular file that was not just created (:3963-3972), and
`may_open` (:3973) before the file's own open.  An absent name under a word
without O_CREAT never gets there: the negative dentry's -ENOENT comes out
of `traverse_mounts` (:1537-1538) on the trailing `step_into` (:3922). -/

/-! ### O_RDONLY -/

/-- Opening the existing "f" for reading: a read-only file fd at the
lowest free slot, offset 0 (`init_file`, fs/file_table.c:216, Linux v6.18.46), with the
model's file system untouched — or one of the four environment errnos.
probe: testing/syscall-check/tests/openat_nonblock.c#conform -- rdonly-fd -/
theorem read_existing_f_is_a_file_fd (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 0) have_model o ↔
      (env_errnos 2 have_model o ∨
       o = ret 3 2 (fixture_of (fds := (3, .FdFile [102] 0) :: init_fds) (fs := have_fs))) := by
  sys_norm

/-- No kernel hands out a non-lowest fd: `alloc_fd` returns `find_next_fd`'s
first clear bit (fs/file.c:584-585, Linux v6.18.46), which is 3 here.
probe: testing/syscall-check/tests/openat_nonblock.c#reject --mutate openat#2:ret+1 -- rdonly-bare -/
theorem read_existing_non_lowest_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 0) have_model (forged 4 2 m' evs) := by
  sys_refute

/-- …nor an fd that is already open (0).
probe: testing/syscall-check/tests/openat_nonblock.c#reject --mutate openat#2:ret=0 -- rdonly-bare -/
theorem read_existing_open_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 0) have_model (forged 0 2 m' evs) := by
  sys_refute

/-- -ENOENT on a path that is right there is refused: existence is tracked.
probe: testing/syscall-check/tests/errno_openat.c#reject --mutate openat#2:ret=-ENOENT -- openat-existing -/
theorem read_existing_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 0) have_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- -EBADF is not an openat answer with AT_FDCWD: `path_init` answers it for
a closed DIRFD only (fs/namei.c:2610-2611, Linux v6.18.46).
probe: testing/syscall-check/tests/errno_openat.c#reject --mutate openat#2:ret=-EBADF -- openat-existing -/
theorem read_existing_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 0) have_model (forged_errno 9 2 m' evs) := by
  sys_refute

/-- -EINTR is real for getrandom, not for openat.
probe: testing/syscall-check/tests/errno_openat.c#reject --mutate openat#2:ret=-EINTR -- openat-existing -/
theorem read_existing_eintr_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 0) have_model (forged_errno 4 2 m' evs) := by
  sys_refute

/-- -EAGAIN is not an openat answer without a lease.
probe: testing/syscall-check/tests/openat_nonblock.c#reject --mutate openat#2:ret=-EAGAIN -- rdonly-bare -/
theorem read_existing_eagain_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 0) have_model (forged_errno 11 2 m' evs) := by
  sys_refute

/-- -EEXIST is O_EXCL's answer, not this word's: `do_open` reads O_EXCL only
inside its O_CREAT block (fs/namei.c:3948-3950, Linux v6.18.46).
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem read_existing_eexist_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 0) have_model (forged_errno 17 2 m' evs) := by
  sys_refute

/-- A success that installed no entry is refused: the fd TABLE is part of
the answer, which no return value reveals.
kernel: fs/file.c:fd_install@v6.18.46 -/
theorem read_existing_success_without_the_entry_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [102] 0) have_model (forged 3 2 have_model evs) := by
  intro h; sys_refute at h

/-- The four environment errnos are admitted on an open that can succeed,
with nothing changed: -ENOMEM (`alloc_empty_file`, fs/file_table.c:258-260, Linux v6.18.46)…
probe: testing/syscall-check/tests/errno_openat.c#conform --mutate openat#2:ret=-ENOMEM -- openat-existing -/
theorem read_existing_enomem_admitted :
    syscall_spec (openat_in [102] 0) have_model (errno 12 2 have_model) := by
  sys_norm

/-- …-EACCES (`may_open`, fs/namei.c:3565-3567, Linux v6.18.46, the inode_permission call)…
probe: testing/syscall-check/tests/errno_openat.c#conform --mutate openat#2:ret=-EACCES -- openat-existing -/
theorem read_existing_eacces_admitted :
    syscall_spec (openat_in [102] 0) have_model (errno 13 2 have_model) := by
  sys_norm

/-- …-EMFILE (`alloc_fd` at RLIMIT_NOFILE, fs/file.c:591-593, Linux v6.18.46)…
probe: testing/syscall-check/tests/errno_openat.c#conform --mutate openat#2:ret=-EMFILE -- openat-existing -/
theorem read_existing_emfile_admitted :
    syscall_spec (openat_in [102] 0) have_model (errno 24 2 have_model) := by
  sys_norm

/-- …and -ENFILE (`alloc_empty_file` at `files_stat.max_files`,
fs/file_table.c:272-278, Linux v6.18.46).
probe: testing/syscall-check/tests/errno_openat.c#conform --mutate openat#2:ret=-ENFILE -- openat-existing -/
theorem read_existing_enfile_admitted :
    syscall_spec (openat_in [102] 0) have_model (errno 23 2 have_model) := by
  sys_norm

/-- An ABSENT name under O_RDONLY is the deterministic -ENOENT of the
negative dentry (`traverse_mounts`, fs/namei.c:1537-1538, Linux v6.18.46): the model is
untouched and nothing else is admitted.
probe: testing/syscall-check/tests/errno_openat.c#conform -- openat-missing -/
theorem read_absent_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 0) absent_model o ↔ o = errno 2 2 absent_model := by
  sys_norm

/-- …a descriptor for a path that is not there is refused.
probe: testing/syscall-check/tests/mined100_surface.c#reject --mutate openat#5:ret=3 -- files -/
theorem read_absent_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 0) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- …and so is an injected -EMFILE: the arm reports the resolution errno
and admits no environment alternative, the documented narrowing (Linux
would raise -EMFILE before path resolution, `do_sys_openat2`,
fs/open.c:1435, Linux v6.18.46), pinned rather than only written down.
probe: testing/syscall-check/tests/mined100_surface.c#reject --mutate openat#5:ret=-EMFILE -- files -/
theorem read_absent_emfile_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 0) absent_model (forged_errno 24 2 m' evs) := by
  sys_refute

/-- …nor -EACCES: injection does not apply to a deterministic arm.
probe: testing/syscall-check/tests/errno_openat.c#reject --mutate openat:ret=-EACCES -- openat-missing -/
theorem read_absent_eacces_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 0) absent_model (forged_errno 13 2 m' evs) := by
  sys_refute

/-! ### O_WRONLY|O_CREAT|O_TRUNC -/

/-- The clobbering create of an absent "a" mints the key empty and a
write-only fd at 3 (`plain_create_mints_the_key` above states the iff);
the refusals are these.  A non-lowest fd: `alloc_fd` (fs/file.c:584-585,
Linux v6.18.46) returns the first clear bit, 3 here.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem create_absent_non_lowest_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) absent_model (forged 4 2 m' evs) := by
  sys_refute

/-- An already-open fd (0): `__set_open_fd` marks the slot and `find_next_fd`
never returns a set bit (fs/file.c:606, :544-565, Linux v6.18.46).
kernel: fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem create_absent_open_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) absent_model (forged 0 2 m' evs) := by
  sys_refute

/-- -EEXIST needs O_EXCL, which this word lacks: `do_open` answers it only
under `open_flag & O_EXCL` (fs/namei.c:3949-3950, Linux v6.18.46).
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem create_absent_eexist_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) absent_model (forged_errno 17 2 m' evs) := by
  sys_refute

/-- -EISDIR on a regular absent path: `do_open`'s `d_is_dir` test
(fs/namei.c:3951-3952, Linux v6.18.46) sees the file `lookup_open` just
created, never a directory.
kernel: fs/namei.c:do_open,lookup_open@v6.18.46 -/
theorem create_absent_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) absent_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-- -ENOENT: O_CREAT means the path need not exist — `lookup_open` creates
the negative dentry's file (fs/namei.c:3788-3800, Linux v6.18.46) instead
of failing on it.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem create_absent_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) absent_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- -EBADF is out of the set on the create path too.
probe: testing/syscall-check/tests/errno_openat.c#reject --mutate openat:ret=-EBADF -- openat-create -/
theorem create_absent_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) absent_model (forged_errno 9 2 m' evs) := by
  sys_refute

/-- A success that recorded no key is refused: the create is part of the
answer.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem create_absent_without_the_key_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) absent_model
        (forged 3 2 (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds)) evs) := by
  intro h; sys_refute at h

/-- -ENFILE is admitted on the create path, with nothing minted.
probe: testing/syscall-check/tests/errno_openat.c#conform --no-fs-check --mutate openat:ret=-ENFILE -- openat-create -/
theorem create_absent_enfile_admitted :
    syscall_spec (openat_in [97] 577) absent_model (errno 23 2 absent_model) := by
  sys_norm

/-- The clobbering create of the EXISTING "f" empties it — `do_open` arms
`handle_truncate` on `d_is_reg && O_TRUNC` (fs/namei.c:3967-3972, Linux v6.18.46,
:3978-3979) — and binds a write-only fd at offset 0.
probe: testing/syscall-check/tests/fs_image.c#conform -/
theorem create_existing_truncates (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 577) have_model o ↔
      (env_errnos 2 have_model o ∨
       o = ret 3 2 (fixture_of (fds := (3, .FdFileW [102] 0) :: init_fds) (fs := [([102], [])]))) := by
  sys_norm

/-- …a success that kept the bytes is refused.
kernel: fs/namei.c:do_open,handle_truncate@v6.18.46 -/
theorem create_existing_keeping_the_bytes_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [102] 577) have_model
        (forged 3 2 (fixture_of (fds := (3, .FdFileW [102] 0) :: init_fds) (fs := have_fs)) evs) := by
  intro h; sys_refute at h

/-! ### O_WRONLY|O_CREAT|O_EXCL, with or without O_TRUNC -/

/-- The exclusive create of an absent "a": the same key and the same
write-only fd as the clobbering word (`lookup_open` creates it,
fs/namei.c:3788-3800, Linux v6.18.46, and FMODE_CREATED lets `do_open`'s O_EXCL test pass,
:3949).
probe: testing/syscall-check/tests/openat_excl.c#conform -- create -/
theorem excl_absent_creates (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 193) absent_model o ↔
      (env_errnos 2 absent_model o ∨
       o = ret 3 2 (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])]))) := by
  sys_norm

/-- -EEXIST on an ABSENT path is refused: the file is not there.
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat:ret=-EEXIST -- create-bare -/
theorem excl_absent_eexist_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 193) absent_model (forged_errno 17 2 m' evs) := by
  sys_refute

/-- -ENOENT on the exclusive create: O_CREAT means the path need not exist.
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat:ret=-ENOENT -- create-bare -/
theorem excl_absent_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 193) absent_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- The exclusive open of the EXISTING "f" is -EEXIST, deterministic, and
the file is untouched.
probe: testing/syscall-check/tests/openat_excl.c#conform -- exists -/
theorem excl_existing_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 193) have_model o ↔ o = errno 17 2 have_model := by
  sys_norm

/-- O_EXCL cannot open an existing path.
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat#2:ret=3 -- exists -/
theorem excl_existing_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 193) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- The errno-injection alternative does NOT apply once the path exists:
the arm answers -EEXIST deterministically, so -EACCES is refused — the
-EACCES `may_lookup` has for an unsearchable working directory
(fs/namei.c:2467-2469, Linux v6.18.46) with it, on the premise
`openat_body_spec` names…
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat#2:ret=-EACCES -- exists -/
theorem excl_existing_eacces_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 193) have_model (forged_errno 13 2 m' evs) := by
  sys_refute

/-- …and -ENFILE, which Linux CAN raise here — `alloc_empty_file` fails
before the walk (fs/file_table.c:272-278, Linux v6.18.46) — and the arm
refuses by the APPROXIMATION `openat_body_spec` documents: a narrowing,
pinned so that it stays a known one.
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat#2:ret=-ENFILE -- exists -/
theorem excl_existing_enfile_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 193) have_model (forged_errno 23 2 m' evs) := by
  sys_refute

/-- …-EISDIR, the clobbering shape's answer for a directory, not O_EXCL's…
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat#2:ret=-EISDIR -- exists -/
theorem excl_existing_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 193) have_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-- …and -ENOENT on a path that is right there.
probe: testing/syscall-check/tests/openat_excl.c#reject --mutate openat#2:ret=-ENOENT -- exists -/
theorem excl_existing_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 193) have_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-! ### An implied directory under the create words

`Namei.fs_under` says some key of the image lives UNDER the name, so the
name is a directory the flat map only implies; the lookup finds a positive
directory dentry with FMODE_CREATED clear (`lookup_fast_for_open`,
fs/namei.c:3837-3845, Linux v6.18.46, and `lookup_open`, fs/namei.c:3714 and
:3734-3737), and `do_open`
answers it -EEXIST under O_EXCL (:3949-3950) and -EISDIR otherwise
(:3951-3952).  No probe can set the image up — the harness starts in an
empty directory — so both halves are pinned here. -/

/-- With "a/b" in the image, the clobbering create of "a" is -EISDIR and the
model is untouched.
rocq-twin: openat_implied_directory_create_eisdir
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem implied_directory_create_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 577) under_model o ↔ o = errno 21 2 under_model := by
  sys_norm

/-- …the descriptor the arm used to mint is refused…
rocq-twin: openat_implied_directory_create_eisdir
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem implied_directory_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) under_model (forged 3 2 m' evs) := by
  sys_refute

/-- …and the control, "c", which nothing lives under, still creates its key
beside "a/b".
rocq-twin: openat_implied_directory_create_eisdir
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem implied_directory_control_creates (o : outcome SyscallEffect) :
    syscall_spec (openat_in [99] 577) under_model o ↔
      (env_errnos 2 under_model o ∨
       o = ret 3 2 (fixture_of (fds := (3, .FdFileW [99] 0) :: init_fds) (fs := fs_set under_fs [99] []))) := by
  sys_norm

/-- THE TEST IS A COMPONENT PREFIX, NOT A BYTE PREFIX: an image holding "ab"
does not make "a" a directory, so the create of "a" mints its key beside
"ab".
rocq-twin: openat_byte_prefix_and_exact_key_still_create
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem byte_prefix_is_not_a_directory (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 577) sibling_model o ↔
      (env_errnos 2 sibling_model o ∨
       o = ret 3 2 (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := fs_set sibling_fs [97] []))) := by
  sys_norm

/-- …so the -EISDIR is refused there.
rocq-twin: openat_byte_prefix_and_exact_key_still_create
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem byte_prefix_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) sibling_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-- …AND NOT EQUALITY: an image holding "a" itself is the ordinary
truncating create, emptied and no -EISDIR.
rocq-twin: openat_byte_prefix_and_exact_key_still_create
kernel: fs/namei.c:do_open,handle_truncate@v6.18.46 -/
theorem exact_key_is_the_truncating_create (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 577) exact_model o ↔
      (env_errnos 2 exact_model o ∨
       o = ret 3 2 (fixture_of (fds := (3, .FdFileW [97] 0) :: init_fds) (fs := [([97], [])]))) := by
  sys_norm

/-- …with the -EISDIR refused.
rocq-twin: openat_byte_prefix_and_exact_key_still_create
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem exact_key_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 577) exact_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-- The exclusive create of the implied directory "a" is -EEXIST, not
-EISDIR: O_EXCL is tested against FMODE_CREATED before `d_is_dir`.
rocq-twin: openat_implied_directory_excl_eexist
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem implied_directory_excl_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 193) under_model o ↔ o = errno 17 2 under_model := by
  sys_norm

/-- …the descriptor refused…
rocq-twin: openat_implied_directory_excl_eexist
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem implied_directory_excl_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 193) under_model (forged 3 2 m' evs) := by
  sys_refute

/-- …the clobbering shape's -EISDIR refused…
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem implied_directory_excl_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 193) under_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-- …and the control on "c" creates.
rocq-twin: openat_implied_directory_excl_eexist
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem implied_directory_excl_control_creates (o : outcome SyscallEffect) :
    syscall_spec (openat_in [99] 193) under_model o ↔
      (env_errnos 2 under_model o ∨
       o = ret 3 2 (fixture_of (fds := (3, .FdFileW [99] 0) :: init_fds) (fs := fs_set under_fs [99] []))) := by
  sys_norm

/-! ### O_RDONLY|O_DIRECTORY

`build_open_flags` turns O_DIRECTORY into LOOKUP_DIRECTORY
(fs/open.c:1337-1338, Linux v6.18.46) and `do_open` answers -ENOTDIR for a resolved dentry
`d_can_lookup` refuses (fs/namei.c:3958-3959, Linux v6.18.46; include/linux/dcache.h:427-430, Linux v6.18.46),
after the O_CREAT block and before `may_open`, so the errno does not turn
on which kind of non-directory the name is.  The arm takes two guards the
read arm cannot: NAME_MAX, and the implied directory. -/

/-- "." under the directory word: the same directory fd the plain read
arm hands back.
rocq-twin: openat_directory_answers
probe: testing/syscall-check/tests/openat_directory.c#conform -- dot -/
theorem dot_dir_word_is_a_directory_fd (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46] 65536) absent_model o ↔
      (env_errnos 2 absent_model o ∨ o = ret 3 2 (fixture_of (fds := (3, .FdDir) :: init_fds))) := by
  sys_norm

/-- "." IS a directory: -ENOTDIR is the answer this arm must never give it.
probe: testing/syscall-check/tests/openat_directory.c#reject --mutate openat:ret=-ENOTDIR -- dot -/
theorem dot_dir_word_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 65536) absent_model (forged_errno 20 2 m' evs) := by
  sys_refute

/-- ".." likewise.
rocq-twin: openat_directory_answers
probe: testing/syscall-check/tests/openat_directory.c#conform -- dotdot -/
theorem dotdot_dir_word_is_a_directory_fd (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46, 46] 65536) absent_model o ↔
      (env_errnos 3 absent_model o ∨ o = ret 3 3 (fixture_of (fds := (3, .FdDir) :: init_fds))) := by
  sys_norm

/-- ".." resolves in every run this model admits: the -ENOENT Linux has for
it is `follow_dotdot`'s `path_connected` failure on a bind-mounted,
disconnected working directory (fs/namei.c:2084-2086, Linux v6.18.46), a
case the flat map's root-anchored premise excludes and the arm is narrower
than Linux by.  So the errno a flat map would otherwise guess for ".." is
refused.
probe: testing/syscall-check/tests/openat_directory.c#reject --mutate openat:ret=-ENOENT -- dotdot -/
theorem dotdot_dir_word_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46, 46] 65536) absent_model (forged_errno 2 3 m' evs) := by
  sys_refute

/-- The directory fd is at the lowest free slot: 4 is refused.
probe: testing/syscall-check/tests/openat_directory.c#reject --mutate openat:ret=4 -- bare -/
theorem dot_dir_word_non_lowest_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 65536) absent_model (forged 4 2 m' evs) := by
  sys_refute

/-- A name the map HOLDS is a non-directory: -ENOTDIR, model unchanged, and
nothing else admitted.
rocq-twin: openat_directory_answers
probe: testing/syscall-check/tests/openat_directory.c#conform -- notdir -/
theorem dir_word_existing_name_is_enotdir (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 65536) have_model o ↔ o = errno 20 2 have_model := by
  sys_norm

/-- …a descriptor for the name the map holds is REFUSED…
rocq-twin: openat_directory_answers
probe: testing/syscall-check/tests/openat_directory.c#reject --mutate openat#2:ret=3 -- notdir -/
theorem dir_word_existing_name_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 65536) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- …and no `openat_errnos` member rescues it: the documented narrowing,
pinned.
probe: testing/syscall-check/tests/openat_directory.c#reject --mutate openat#2:ret=-EMFILE -- notdir -/
theorem dir_word_existing_name_emfile_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 65536) have_model (forged_errno 24 2 m' evs) := by
  sys_refute

/-- An ABSENT name never reaches the directory test: -ENOENT.
rocq-twin: openat_directory_answers
probe: testing/syscall-check/tests/openat_directory.c#conform -- absent -/
theorem dir_word_absent_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 65536) absent_model o ↔ o = errno 2 2 absent_model := by
  sys_norm

/-- …a descriptor refused…
probe: testing/syscall-check/tests/openat_directory.c#reject --mutate openat:ret=3 -- absent -/
theorem dir_word_absent_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 65536) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- …and the same narrowing on this deterministic branch.
probe: testing/syscall-check/tests/openat_directory.c#reject --mutate openat:ret=-EMFILE -- absent -/
theorem dir_word_absent_emfile_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 65536) absent_model (forged_errno 24 2 m' evs) := by
  sys_refute

/-- THE IGNORED BITS ARE IGNORED HERE TOO, over all of the arm's answers:
O_DIRECTORY|O_LARGEFILE|O_CLOEXEC lands where O_DIRECTORY lands, on ".",
on a name the map holds and on one it does not.
rocq-twin: openat_directory_ignores_largefile_and_cloexec
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem dir_word_ignores_largefile_and_cloexec_dot (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46] 622592) absent_model o ↔ syscall_spec (openat_in [46] 65536) absent_model o := by
  sys_norm

/-- …on the name the map holds…
rocq-twin: openat_directory_ignores_largefile_and_cloexec
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem dir_word_ignores_largefile_and_cloexec_existing (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 622592) have_model o ↔ syscall_spec (openat_in [102] 65536) have_model o := by
  sys_norm

/-- …and on the absent one.
rocq-twin: openat_directory_ignores_largefile_and_cloexec
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem dir_word_ignores_largefile_and_cloexec_absent (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 622592) absent_model o ↔ syscall_spec (openat_in [97] 65536) absent_model o := by
  sys_norm

/-- …and on "..", the row Rocq has and a mask applied on one branch but not
another would miss: the bridge for the probe's "dotdot" cases, whose word
is 622592.
rocq-twin: openat_directory_ignores_largefile_and_cloexec
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem dir_word_ignores_largefile_and_cloexec_dotdot (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46, 46] 622592) absent_model o ↔ syscall_spec (openat_in [46, 46] 65536) absent_model o := by
  sys_norm

/-- THE IMPLIED-DIRECTORY DECLINE: a key "a/b" means reality has a
directory "a", so Linux hands back a directory fd where the map would
answer -ENOENT — the arm declines whichever the kernel is offered.
rocq-twin: openat_directory_implied_directory_unmodeled
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem dir_implied_directory_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 65536) under_model o ↔ o = Unmodeled := by
  sys_norm

/-- …refusing the directory fd…
rocq-twin: openat_directory_implied_directory_unmodeled
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem dir_implied_directory_declines_a_success (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 65536) under_model (forged 3 2 m' evs) := by
  sys_refute

/-- …and the -ENOENT; the control is `dir_word_absent_is_enoent`, the same
name with nothing under it, which IS answered.
rocq-twin: openat_directory_implied_directory_unmodeled
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem dir_implied_directory_declines_an_enoent (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 65536) under_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- THE NAME_MAX BOUNDARY, declined side: a 256-byte component is
`Unmodeled`, because the -ENAMETOOLONG belongs to the FILESYSTEM
(`simple_lookup`, fs/libfs.c:71-72; `ext4_lookup`, fs/ext4/namei.c:1768-1769)
and a model with no filesystem type would be inventing one.  Stated over
any 256-byte plain name the fetch returns; the proof hands the fetch result
and the name's three facts to `simp`, then reads the rest.
rocq-twin: openat_directory_name_max_boundary
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup@v6.18.46 -/
theorem dir_name_max_256_declines (i : SyscallInput) (p : path)
    (hp : read_cstr i.in_mem 8192 = CstrOk p) (hlen : p.length = 256)
    (hs : path_has_slash p = false) (hd : path_is_dirref p = false) (o : outcome SyscallEffect) :
    openat_spec 4294967196 8192 65536 i absent_model o ↔ o = Unmodeled := by
  have hne : path_eqb p [] = false :=
    path_eqb_false_of_ne p [] (by intro h; subst h; simp only [List.length_nil] at hlen; omega)
  have hu : fs_under [] p = false := rfl
  sys_simp_pass +decide
  simp only [hp, hne, hs, hd, hlen, hu]
  sys_norm

/-- …answered side: a 255-byte component passes the guard and gets the
arm's -ENOENT on the empty image.
rocq-twin: openat_directory_name_max_boundary
kernel: fs/namei.c:traverse_mounts; include/uapi/linux/limits.h:NAME_MAX@v6.18.46 -/
theorem dir_name_max_255_answers (i : SyscallInput) (p : path)
    (hp : read_cstr i.in_mem 8192 = CstrOk p) (hlen : p.length = 255)
    (hs : path_has_slash p = false) (hd : path_is_dirref p = false) (o : outcome SyscallEffect) :
    openat_spec 4294967196 8192 65536 i absent_model o ↔
      o = Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
               (mkEffect (errno_ret 2) [] [])) absent_model [] := by
  have hne : path_eqb p [] = false :=
    path_eqb_false_of_ne p [] (by intro h; subst h; simp only [List.length_nil] at hlen; omega)
  have hu : fs_under [] p = false := rfl
  sys_simp_pass +decide
  simp only [hp, hne, hs, hd, hlen, hu]
  sys_norm

/-! ## "/etc/localtime", the answered exception

`openat_localtime_spec` answers -ENOENT for exactly this byte string under
a maintainer-declared assumption about the image (issue #696,
bugs/openat-localtime-assumed-absent.md): the walk of the last component
finds no inode, so `open_last_lookups` (fs/namei.c:3919-3922, Linux v6.18.46) hands a
negative dentry to step_into, and `traverse_mounts` (fs/namei.c:1537-1538, Linux v6.18.46)
answers -ENOENT before `do_open` looks at any flag.  Fail-closed wherever the
assumption does not reach. -/

/-- Under O_RDONLY the answer is -ENOENT, an Ok in the unchanged model, and
nothing else is admitted.
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem localtime_rdonly_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 0) absent_model o ↔ o = errno 2 15 absent_model := by
  sys_norm

/-- A claimed descriptor is refused: the answer is deterministic.
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem localtime_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in localtime_path 0) absent_model (forged 3 15 m' evs) := by
  sys_refute

/-- …and so is -EACCES: no environment alternative on this arm.
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem localtime_eacces_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in localtime_path 0) absent_model (forged_errno 13 15 m' evs) := by
  sys_refute

/-- musl's `__map_file` word, O_RDONLY|O_CLOEXEC|O_NONBLOCK, is the O_RDONLY
arm: both bits are ignored.
rocq-twin: openat_localtime_enoent
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem localtime_musl_word_is_the_read_word (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 526336) absent_model o ↔
      syscall_spec (openat_in localtime_path 0) absent_model o := by
  sys_norm

/-- The answer does not turn on the access mode: O_RDWR is -ENOENT too, the
walk failing before `do_open` reads any flag.
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem localtime_rdwr_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 2) absent_model o ↔ o = errno 2 15 absent_model := by
  sys_norm

/-- …O_RDWR|O_TRUNC…
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem localtime_rdwr_trunc_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 514) absent_model o ↔ o = errno 2 15 absent_model := by
  sys_norm

/-- …and O_RDONLY|O_DIRECTORY, before the -ENOTDIR test is reached.
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem localtime_dir_word_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 65536) absent_model o ↔ o = errno 2 15 absent_model := by
  sys_norm

/-- With O_CREAT the arm fails closed, in every spelling the model admits:
Linux would create the file under /etc (`lookup_open`, fs/namei.c:3788-3800),
a directory the model has no representation of.  The clobbering word:
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem localtime_create_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 577) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and its -ENOENT is refused: the decline does not side with the map.
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem localtime_create_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in localtime_path 577) absent_model (forged_errno 2 15 m' evs) := by
  sys_refute

/-- …nor does it side with a kernel that created the file.
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem localtime_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in localtime_path 577) absent_model (forged 3 15 m' evs) := by
  sys_refute

/-- The exclusive word…
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem localtime_excl_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 193) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the append word…
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem localtime_append_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 1089) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the exclusive append word, which carries O_CREAT too (#1752)…
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem localtime_excl_append_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 1217) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …O_RDWR|O_CREAT…
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem localtime_rdwr_creat_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 66) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the exclusive read-write word.
rocq-twin: openat_localtime_enoent
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem localtime_rdwr_excl_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 194) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE ASSUMPTION DOES NOT REACH AN IMAGE THAT SHIPS THE FILE: a map
holding the key "/etc/localtime" describes an image the declaration was
not made about, and the open is declined rather than answered from the
map.
rocq-twin: openat_localtime_in_image_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem localtime_key_in_image_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 0) localtime_key_model o ↔ o = Unmodeled := by
  sys_norm

/-- …whatever the kernel is offered as having said: the -ENOENT…
rocq-twin: openat_localtime_in_image_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem localtime_key_in_image_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in localtime_path 0) localtime_key_model (forged_errno 2 15 m' evs) := by
  sys_refute

/-- …or a descriptor.
rocq-twin: openat_localtime_in_image_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem localtime_key_in_image_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in localtime_path 0) localtime_key_model (forged 3 15 m' evs) := by
  sys_refute

/-- A key UNDER it ("/etc/localtime/x") makes the path a directory Linux
would open: declined too.
rocq-twin: openat_localtime_in_image_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem localtime_under_key_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 0) localtime_under_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE CONTROL: an unrelated key ("a") leaves the answer in place.
rocq-twin: openat_localtime_in_image_unmodeled
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem localtime_unrelated_key_answers (o : outcome SyscallEffect) :
    syscall_spec (openat_in localtime_path 0) exact_model o ↔ o = errno 2 15 exact_model := by
  sys_norm

/-- THE MATCH IS EXACT.  "/etc//localtime" names the same file on Linux and
is the ordinary separator decline here, the -ENOENT refused.
rocq-twin: openat_localtime_match_is_exact
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem localtime_match_is_exact_double_slash (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 101, 116, 99, 47, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] 0)
      absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- "//etc/localtime" likewise.
rocq-twin: openat_localtime_match_is_exact
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem localtime_match_is_exact_double_root (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] 0)
      absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- A prefix of the name, "/etc/localtim", names a different file.
rocq-twin: openat_localtime_match_is_exact
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem localtime_match_is_exact_prefix (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109] 0)
      absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and so does an extension, "/etc/localtimes".
rocq-twin: openat_localtime_match_is_exact
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem localtime_match_is_exact_extended (o : outcome SyscallEffect) :
    syscall_spec (openat_in (localtime_path ++ [115]) 0) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …with the -ENOENT refused on the doubled-slash spelling, so the four
above are not a model that declines everything (the control is
`localtime_rdonly_is_enoent`).
rocq-twin: openat_localtime_match_is_exact
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem localtime_double_slash_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 101, 116, 99, 47, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101] 0)
        absent_model (forged_errno 2 16 m' evs) := by
  sys_refute

/-! ## "/dev/null", the answered device

`openat_devnull_spec` answers the exact byte string ahead of the separator
decline and mints `FdDevNull` with the granted mode, on the assumption
(issue #696, bugs/openat-devnull-assumed-null-device.md) that the image's
/dev/null is the null device: `devlist[3]` (drivers/char/mem.c:694, Linux v6.18.46) and
`memory_open` installing `null_fops` (:707-727, :644-652) out of
`chrdev_open` (fs/char_dev.c:373-424, Linux v6.18.46).  Every word below is decided in
`do_open` before that open runs.

A device cgroup can refuse the open with -EPERM: `may_open` asks
`inode_permission` for MAY_OPEN|acc_mode (fs/namei.c:3565-3567, Linux
v6.18.46), which runs devcgroup_inode_permission on the character device
(:597-599), and -EPERM is not among the four `openat_errnos`.  The arms
answer on the premise that the run's cgroup allows the devices it
declares — the same shape as the nodev mount, whose -EACCES IS admitted. -/

/-- O_RDONLY: a read-only device entry at the lowest free fd, the image
untouched.
rocq-twin: devnull_open_by_word
kernel: fs/namei.c:may_open; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem devnull_rdonly_mints_the_reader (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 0) absent_model o ↔
      (env_errnos 10 absent_model o ∨
       o = ret 3 10 (fixture_of (fds := (3, .FdDevNull true false) :: init_fds))) := by
  sys_norm

/-- O_RDONLY|O_CLOEXEC is the same open, stated on the answer itself — the
read-only device entry or an environment errno — rather than as an
equation between two words, which two declines would also satisfy.
rocq-twin: devnull_open_by_word
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem devnull_cloexec_is_the_rdonly_open (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 524288) absent_model o ↔
      (env_errnos 10 absent_model o ∨
       o = ret 3 10 (fixture_of (fds := (3, .FdDevNull true false) :: init_fds))) := by
  sys_norm

/-- O_WRONLY|O_CREAT|O_TRUNC: a write-only entry.  O_CREAT creates nothing on
the existing node (`lookup_open` fs/namei.c:3734-3737) and `do_open` arms
truncation only under `d_is_reg` (:3967), which a character device fails.
rocq-twin: devnull_open_by_word
kernel: fs/namei.c:do_open,lookup_open@v6.18.46 -/
theorem devnull_create_word_mints_the_writer (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 577) absent_model o ↔
      (env_errnos 10 absent_model o ∨
       o = ret 3 10 (fixture_of (fds := (3, .FdDevNull false true) :: init_fds))) := by
  sys_norm

/-- The append word mints the same write-only entry: nothing in `null_fops`
reads `f_flags` (`write_null` drivers/char/mem.c:418-422, `write_iter_null`
:429-434).  The one place this twin answers the append word.
rocq-twin: devnull_open_by_word
kernel: drivers/char/mem.c:write_null,write_iter_null@v6.18.46 -/
theorem devnull_append_word_mints_the_writer (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 1089) absent_model o ↔
      (env_errnos 10 absent_model o ∨
       o = ret 3 10 (fixture_of (fds := (3, .FdDevNull false true) :: init_fds))) := by
  sys_norm

/-- O_RDWR: an entry open both ways.
rocq-twin: devnull_open_by_word
kernel: fs/namei.c:may_open; fs/file_table.c:init_file@v6.18.46 -/
theorem devnull_rdwr_mints_the_readwriter (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 2) absent_model o ↔
      (env_errnos 10 absent_model o ∨
       o = ret 3 10 (fixture_of (fds := (3, .FdDevNull true true) :: init_fds))) := by
  sys_norm

/-- O_RDWR|O_CREAT|O_TRUNC: the same entry, O_TRUNC inert on the device.
rocq-twin: devnull_open_by_word
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem devnull_rdwr_create_trunc_mints_the_readwriter (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 578) absent_model o ↔
      (env_errnos 10 absent_model o ∨
       o = ret 3 10 (fixture_of (fds := (3, .FdDevNull true true) :: init_fds))) := by
  sys_norm

/-- O_RDWR|O_TRUNC (514): the same entry.  `do_open` (fs/namei.c:3967) arms
truncation only when d_is_reg holds, which the character device fails, so
O_TRUNC is inert and `may_open` grants both directions.  The one word that
tells `rdwr_open_word`'s O_TRUNC spelling from its O_CREAT one; Rocq's
`devnull_open_by_word` pins the other two read-write spellings.
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem devnull_rdwr_trunc_mints_the_readwriter (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 514) absent_model o ↔
      (env_errnos 10 absent_model o ∨
       o = ret 3 10 (fixture_of (fds := (3, .FdDevNull true true) :: init_fds))) := by
  sys_norm

/-- O_RDWR|O_CREAT (66): the same entry.  O_CREAT creates nothing on the
existing node (`lookup_open` fs/namei.c:3734-3737), and `do_open`'s O_CREAT
block (:3948-3957) refuses only O_EXCL and a directory, neither of which
holds.
kernel: fs/namei.c:do_open,lookup_open@v6.18.46 -/
theorem devnull_rdwr_create_mints_the_readwriter (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 66) absent_model o ↔
      (env_errnos 10 absent_model o ∨
       o = ret 3 10 (fixture_of (fds := (3, .FdDevNull true true) :: init_fds))) := by
  sys_norm

/-- The exclusive words are -EEXIST, deterministic: `do_open`'s O_EXCL test
on an existing name (fs/namei.c:3949-3950).
rocq-twin: devnull_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem devnull_excl_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 193) absent_model o ↔ o = errno 17 10 absent_model := by
  sys_norm

/-- …the read-write spelling too.
rocq-twin: devnull_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem devnull_rdwr_excl_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 194) absent_model o ↔ o = errno 17 10 absent_model := by
  sys_norm

/-- …and a claimed success under O_EXCL is refused.
rocq-twin: devnull_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem devnull_excl_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in devnull_path 193) absent_model (forged 3 10 m' evs) := by
  sys_refute

/-- The exclusive append word is -EEXIST too (#1752): O_EXCL is tested before
anything else in `do_open`'s O_CREAT block (fs/namei.c:3949-3950, Linux
v6.18.46), so the device is never opened and O_APPEND never matters.
probe: testing/syscall-check/tests/openat_excl_append.c#conform -- devnull -/
theorem devnull_excl_append_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 1217) absent_model o ↔ o = errno 17 10 absent_model := by
  sys_norm

/-- …and the descriptor a kernel that opened the device would hand back is
refused.
probe: testing/syscall-check/tests/openat_excl_append.c#reject --mutate openat:ret=3 -- devnull -/
theorem devnull_excl_append_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in devnull_path 1217) absent_model (forged 3 10 m' evs) := by
  sys_refute

/-- O_RDONLY|O_DIRECTORY is -ENOTDIR: `do_open`'s LOOKUP_DIRECTORY test
(fs/namei.c:3958-3959).
rocq-twin: devnull_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem devnull_dir_word_is_enotdir (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 65536) absent_model o ↔ o = errno 20 10 absent_model := by
  sys_norm

/-- …with a claimed success refused.
rocq-twin: devnull_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem devnull_dir_word_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in devnull_path 65536) absent_model (forged 3 10 m' evs) := by
  sys_refute

/-- THE ASSUMPTION DOES NOT REACH AN IMAGE THAT SHIPS A FILE UNDER THE
NAME: declined, whatever the kernel said.
rocq-twin: devnull_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem devnull_key_in_image_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 0) devnull_key_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor refused…
rocq-twin: devnull_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem devnull_key_in_image_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in devnull_path 0) devnull_key_model (forged 3 10 m' evs) := by
  sys_refute

/-- …and the -ENOENT refused.
rocq-twin: devnull_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem devnull_key_in_image_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in devnull_path 0) devnull_key_model (forged_errno 2 10 m' evs) := by
  sys_refute

/-- A key under it ("/dev/null/x") declines too.
rocq-twin: devnull_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem devnull_under_key_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in devnull_path 0) devnull_under_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE MATCH IS EXACT: "/dev//null" is the separator decline…
rocq-twin: devnull_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem devnull_match_is_exact_double_slash (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 100, 101, 118, 47, 47, 110, 117, 108, 108] 0) absent_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …and so is "/dev/nul", a different name.
rocq-twin: devnull_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem devnull_match_is_exact_prefix (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 100, 101, 118, 47, 110, 117, 108] 0) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …with the descriptor refused on the doubled-slash spelling (the control
is `devnull_rdonly_mints_the_reader`).
rocq-twin: devnull_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem devnull_double_slash_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 100, 101, 118, 47, 47, 110, 117, 108, 108] 0) absent_model
        (forged 3 11 m' evs) := by
  sys_refute

/-! ## "/tmp/<name>", the answered private directory

`openat_tmp_spec` answers two words for a path `Namei.tmp_name` accepts —
"/tmp/" and one component that is not empty, "." or ".." — over the run's
declared private /tmp (`State.in_tmp`, seeded under absolute keys by
`State.fs_seed_tmp`; bugs/tmp-assumed-private-directory.md; issue #562,
rung 4 of #696).  Linux starts the absolute name at the root (`path_init`,
fs/namei.c:2582-2587, Linux v6.18.46), walks "tmp" as a non-final component
(`link_path_walk`, :2517-2519) and reaches `lookup_open` and `do_open` with
the same `last` a relative name would, in a parent that is /tmp; the flat
map answers for that parent under the privacy premise and declines every
shape the ruling left out. -/

/-- The create word on a name the run does not hold: `lookup_open` finds
the negative dentry and creates (fs/namei.c:3788-3800, Linux v6.18.46),
`do_open` clears O_TRUNC under FMODE_CREATED (:3963-3966), and the
descriptor is write-only at offset 0; the model records the key EMPTY,
`create_wronly` unchanged, at the lowest free fd.
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/namei.c:lookup_open,do_open@v6.18.46 -/
theorem tmp_create_mints_the_key (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 577) absent_model o ↔
      (env_errnos 7 absent_model o ∨
       o = ret 3 7 (fixture_of (fds := (3, .FdFileW [47, 116, 109, 112, 47, 120] 0) :: init_fds)
                               (fs := [([47, 116, 109, 112, 47, 120], [])]))) := by
  sys_norm

/-- …and the -ENOENT the absent name would get without O_CREAT is refused:
the negative dentry takes `lookup_open`'s create branch (fs/namei.c:3788),
not `step_into`'s (:1989-1992).
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem tmp_create_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 577) absent_model (forged_errno 2 7 m' evs) := by
  sys_refute

/-- The create word carrying O_CLOEXEC is the same open: the word is matched
past `open_ignored_flags`, the file's shared mask, as every arm here
matches it; `build_open_flags` strips the bit (`u64 strip = O_CLOEXEC`,
fs/open.c:1241, Linux v6.18.46, and :1251) and `do_sys_openat2` spends it on
the descriptor table's close-on-exec bit (:1435), which the model does not
record.
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/open.c:build_open_flags,do_sys_openat2@v6.18.46 -/
theorem tmp_create_cloexec_lands_where_create_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 524865) absent_model o ↔
      syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 577) absent_model o := by
  sys_norm

/-- …O_NONBLOCK, inert on a regular file: it reaches `f_flags` (`init_file`,
fs/file_table.c:198, Linux v6.18.46) and nothing a modeled arm reads.
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/file_table.c:init_file@v6.18.46 -/
theorem tmp_create_nonblock_lands_where_create_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 2625) absent_model o ↔
      syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 577) absent_model o := by
  sys_norm

/-- …O_LARGEFILE, which `openat`'s SYSCALL_DEFINE4 ORs into every open on
a 64-bit ABI (fs/open.c:1466-1467, Linux v6.18.46).
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/open.c:openat@v6.18.46 -/
theorem tmp_create_largefile_lands_where_create_does (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 33345) absent_model o ↔
      syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 577) absent_model o := by
  sys_norm

/-- The create word on a name the run HOLDS: the dentry is positive
(`lookup_open`, fs/namei.c:3734-3737, Linux v6.18.46), so `do_open` arms
the truncation of the regular file (:3967-3972) and the key is emptied
under a write-only descriptor at offset 0.
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/namei.c:lookup_open,do_open@v6.18.46 -/
theorem tmp_create_on_held_key_empties_it (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 577) tmp_held_model o ↔
      (env_errnos 7 tmp_held_model o ∨
       o = ret 3 7 (fixture_of (fds := (3, .FdFileW [47, 116, 109, 112, 47, 120] 0) :: init_fds)
                               (fs := fs_set tmp_held_fs [47, 116, 109, 112, 47, 120] []))) := by
  sys_norm

/-- …the held byte does not survive the create word: the image unchanged is
refused (`handle_truncate`, fs/namei.c:3586-3602, truncates to length 0).
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/namei.c:handle_truncate@v6.18.46 -/
theorem tmp_create_on_held_key_keeping_bytes_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 577) tmp_held_model
        (forged 3 7 (fixture_of (fds := (3, .FdFileW [47, 116, 109, 112, 47, 120] 0) :: init_fds) (fs := tmp_held_fs)) evs) := by
  intro h; sys_refute at h

/-- O_RDONLY of a name the run holds: `may_open`'s S_IFREG arm
(fs/namei.c:3557-3560, Linux v6.18.46) refuses nothing, and the descriptor is
read-only at offset 0 (`init_file`, fs/file_table.c:216, Linux v6.18.46).
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/namei.c:may_open; fs/file_table.c:init_file@v6.18.46 -/
theorem tmp_read_held_mints_the_reader (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 0) tmp_held_model o ↔
      (env_errnos 7 tmp_held_model o ∨
       o = ret 3 7 (fixture_of (fds := (3, .FdFile [47, 116, 109, 112, 47, 120] 0) :: init_fds) (fs := tmp_held_fs))) := by
  sys_norm

/-- …-ENOENT for the held name is refused: past the walk the only -ENOENT is
`may_open`'s on a missing inode (fs/namei.c:3534-3535), and the inode is there.
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_read_held_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 0) tmp_held_model (forged_errno 2 7 m' evs) := by
  sys_refute

/-- O_RDONLY|O_CLOEXEC of the held name is the same open (the bit is stripped
and spent as above).
rocq-twin: openat_tmp_create_read_unlink
kernel: fs/open.c:build_open_flags,do_sys_openat2@v6.18.46 -/
theorem tmp_read_cloexec_is_the_same_open (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 524288) tmp_held_model o ↔
      syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 0) tmp_held_model o := by
  sys_norm

/-- A read of the name the ENVIRONMENT declared rather than the run created:
the declaration is keyed by the component "x" and the program names the
whole path, and `State.fs_seed_tmp` makes those one file (it seeds under
`State.tmp_key`, the path `Namei.tmp_name_key` says the gate accepts;
`seed_x` is the closed instance), so the read of the declared name is the
read of the held key: Linux walks "tmp" then "x" to the inode the
environment placed there (`link_path_walk`, fs/namei.c:2517-2519, Linux v6.18.46)
and `may_open`'s S_IFREG arm (:3557-3560) lets it through.
rocq-twin: openat_tmp_declared_name_reads
kernel: fs/namei.c:link_path_walk,may_open@v6.18.46 -/
theorem tmp_declared_name_reads (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 0) tmp_seeded_model o ↔
      (env_errnos 7 tmp_seeded_model o ∨
       o = ret 3 7 (fixture_of (fds := (3, .FdFile [47, 116, 109, 112, 47, 120] 0) :: init_fds)
                               (fs := tmp_held_fs))) := by
  rw [tmp_seeded_is_held]
  exact tmp_read_held_mints_the_reader o

/-- The declaration needs no validity clause: an unsorted declaration with a
repeat seeds the canonical map, the later entry winning; and an image that
already holds the absolute key resolves to the DECLARATION's bytes, since
the seeding's `fs_set` replaces rather than appends.
rocq-twin: openat_tmp_unsorted_declaration_is_canonical
model: `State.fs_seed_tmp` is `Fs.fs_set` one declared entry at a time; a closed evaluation. -/
theorem tmp_seed_unsorted_is_canonical :
    fs_seed_tmp [] [([98], [1]), ([97], [2]), ([98], [3])] = [(tmp_key [97], [2]), (tmp_key [98], [3])]
    ∧ fs_seed_tmp [([47, 116, 109, 112, 47, 120], [1])] [([120], [2])] = [([47, 116, 109, 112, 47, 120], [2])] := by
  decide

/-! ### What the ruling declines, each on the model that HOLDS the key

None below is declining for want of the file; the one exception, a read of
a name the run does NOT hold, is stated on the empty image beside them.
Linux answers every one of them, and the intersection would let the model
derive several; the ruling (issue #562) takes the shapes the reported
programs need and leaves the rest, the narrower choice at each. -/

/-- A read of a name the run does not hold: the privacy premise would give
the negative dentry's -ENOENT (`traverse_mounts`, fs/namei.c:1537-1538, Linux v6.18.46,
on the trailing `step_into`, :1989-1992); the ruling declines instead.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:traverse_mounts,step_into@v6.18.46 -/
theorem tmp_read_not_held_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 0) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -ENOENT itself refused.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem tmp_read_not_held_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 0) absent_model (forged_errno 2 7 m' evs) := by
  sys_refute

/-- O_RDWR|O_CREAT|O_TRUNC on the held name: Linux truncates and opens it
both ways (`do_open`, fs/namei.c:3967-3972; `may_open`, :3557-3560, Linux v6.18.46); declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem tmp_rdwr_create_trunc_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 578) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor refused.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_rdwr_create_trunc_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 578) tmp_held_model (forged 3 7 m' evs) := by
  sys_refute

/-- O_WRONLY|O_CREAT|O_APPEND on the held name: Linux opens it for appending
(`may_open`'s IS_APPEND test is about the inode flag, not this word,
fs/namei.c:3572-3577, Linux v6.18.46); declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_append_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 1089) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor refused.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_append_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 1089) tmp_held_model (forged 3 7 m' evs) := by
  sys_refute

/-- O_WRONLY|O_CREAT|O_EXCL on the held name: Linux answers -EEXIST
(`do_open`, fs/namei.c:3949-3950, Linux v6.18.46), deterministic; declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_excl_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 193) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -EEXIST refused.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_excl_eexist_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 193) tmp_held_model (forged_errno 17 7 m' evs) := by
  sys_refute

/-- O_RDONLY|O_DIRECTORY on the held regular file: Linux answers -ENOTDIR
(`do_open`, fs/namei.c:3958-3959, Linux v6.18.46); declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_directory_word_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 65536) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -ENOTDIR refused.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_directory_word_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 65536) tmp_held_model (forged_errno 20 7 m' evs) := by
  sys_refute

/-- A second component, "/tmp/d/f" under the create word on the empty
run: `Namei.tmp_name` rejects the name, and the path falls to the separator
decline.  Linux would walk "d" in /tmp (`link_path_walk`, fs/namei.c:2517-2519, Linux v6.18.46)
and, the private directory being empty, answer -ENOENT; declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_second_component_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 100, 47, 102] 577) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -ENOENT refused.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_second_component_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 100, 47, 102] 577) absent_model
        (forged_errno 2 9 m' evs) := by
  sys_refute

/-- The directory itself, "/tmp" under O_RDONLY: Linux hands back a
directory descriptor (`may_open`'s S_IFDIR arm, fs/namei.c:3540-3545, Linux v6.18.46);
`Namei.tmp_name` rejects the bare prefix and the path is declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_directory_itself_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112] 0) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the directory descriptor refused.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_directory_itself_fd_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112] 0) tmp_held_model
        (forged 3 5 (fixture_of (fds := (3, .FdDir) :: init_fds) (fs := tmp_held_fs)) evs) := by
  intro h; sys_refute at h

/-- "/tmp/", the same directory with a trailing separator: the byte past the
last component makes `lookup_fast_for_open` type it as a directory
(fs/namei.c:3830-3831, Linux v6.18.46) and Linux opens it; declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:lookup_fast_for_open@v6.18.46 -/
theorem tmp_directory_slash_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47] 0) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the directory descriptor refused (`may_open`'s S_IFDIR arm, fs/namei.c:3540-3545, Linux v6.18.46).
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_directory_slash_fd_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47] 0) tmp_held_model
        (forged 3 6 (fixture_of (fds := (3, .FdDir) :: init_fds) (fs := tmp_held_fs)) evs) := by
  intro h; sys_refute at h

/-- "/tmp/.", the directory through its own reference (`handle_dots`,
fs/namei.c:2096-2132, Linux v6.18.46); declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:handle_dots@v6.18.46 -/
theorem tmp_dot_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 46] 0) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the directory descriptor refused.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:handle_dots,may_open@v6.18.46 -/
theorem tmp_dot_fd_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 46] 0) tmp_held_model
        (forged 3 7 (fixture_of (fds := (3, .FdDir) :: init_fds) (fs := tmp_held_fs)) evs) := by
  intro h; sys_refute at h

/-- "/tmp/..", the root through the parent reference (`follow_dotdot`,
fs/namei.c:2064-2094, Linux v6.18.46); declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:follow_dotdot@v6.18.46 -/
theorem tmp_dotdot_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 46, 46] 0) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the directory descriptor refused.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:follow_dotdot,may_open@v6.18.46 -/
theorem tmp_dotdot_fd_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 46, 46] 0) tmp_held_model
        (forged 3 8 (fixture_of (fds := (3, .FdDir) :: init_fds) (fs := tmp_held_fs)) evs) := by
  intro h; sys_refute at h

/-- "/tmpfoo" under the create word: not under /tmp at all — the prefix
strip needs the separator — so the separator decline stands.  Linux would
create the name in the root directory or refuse it with the root's
permission (`may_o_create`, fs/namei.c:3611-3628, Linux v6.18.46); declined.
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:may_o_create@v6.18.46 -/
theorem tmpfoo_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 102, 111, 111] 577) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the unprivileged run's -EACCES refused: `may_o_create`'s
`inode_permission` on the root directory (fs/namei.c:3622-3625, Linux v6.18.46).
rocq-twin: openat_tmp_excluded_shapes_unmodeled
kernel: fs/namei.c:may_o_create@v6.18.46 -/
theorem tmpfoo_eacces_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 102, 111, 111] 577) absent_model
        (forged_errno 13 8 m' evs) := by
  sys_refute

/-! ### The NAME_MAX boundary, from both sides

The -ENAMETOOLONG a longer component really gets comes out of the
FILESYSTEM's own lookup rather than out of fs/namei.c — tmpfs from
`simple_lookup` (fs/libfs.c:71-72, Linux v6.18.46), ext4 from `ext4_lookup`
(fs/ext4/namei.c:1768-1769, Linux v6.18.46) — so the guard is one-sided: it
defends against a filesystem whose limit is larger than 255 and not against
one whose limit is smaller (bugs/tmp-assumed-private-directory.md). -/

set_option maxRecDepth 8192 in
/-- A 256-byte component is declined at the create word.
rocq-twin: openat_tmp_name_max_boundary
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup@v6.18.46 -/
theorem tmp_name_max_256_declines_the_create (o : outcome SyscallEffect) :
    syscall_spec (openat_in (tmp_key name256) 577) absent_model o ↔ o = Unmodeled := by
  sys_norm

set_option maxRecDepth 8192 in
/-- …and at the read word.
rocq-twin: openat_tmp_name_max_boundary
kernel: fs/libfs.c:simple_lookup; fs/ext4/namei.c:ext4_lookup@v6.18.46 -/
theorem tmp_name_max_256_declines_the_read (o : outcome SyscallEffect) :
    syscall_spec (openat_in (tmp_key name256) 0) absent_model o ↔ o = Unmodeled := by
  sys_norm

set_option maxRecDepth 8192 in
/-- …the -ENAMETOOLONG itself refused: it is a filesystem's answer, not one
the model can give.
rocq-twin: openat_tmp_name_max_boundary
kernel: fs/libfs.c:simple_lookup@v6.18.46 -/
theorem tmp_name_max_256_enametoolong_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in (tmp_key name256) 577) absent_model (forged_errno 36 262 m' evs) := by
  sys_refute

set_option maxRecDepth 8192 in
/-- A 255-byte component passes the guard: the create mints the key.
rocq-twin: openat_tmp_name_max_boundary
kernel: fs/namei.c:lookup_open; include/uapi/linux/limits.h:NAME_MAX@v6.18.46 -/
theorem tmp_name_max_255_answers (o : outcome SyscallEffect) :
    syscall_spec (openat_in (tmp_key name255) 577) absent_model o ↔
      (env_errnos 261 absent_model o ∨
       o = ret 3 261 (fixture_of (fds := (3, .FdFileW (tmp_key name255) 0) :: init_fds)
                                 (fs := [(tmp_key name255, [])]))) := by
  sys_norm

set_option maxRecDepth 8192 in
/-- …and the READ of the 255-byte name, on a run that holds it, mints the
reader: the boundary's other word on its answering side, which the Rocq
case leaves to the declined 256 side alone.
kernel: fs/namei.c:may_open; include/uapi/linux/limits.h:NAME_MAX@v6.18.46 -/
theorem tmp_name_max_255_read_mints_the_reader (o : outcome SyscallEffect) :
    syscall_spec (openat_in (tmp_key name255) 0) tmp_name255_held_model o ↔
      (env_errnos 261 tmp_name255_held_model o ∨
       o = ret 3 261 (fixture_of (fds := (3, .FdFile (tmp_key name255) 0) :: init_fds)
                                 (fs := tmp_name255_held_fs))) := by
  sys_norm

/-! ### A directory inside /tmp, which the flat map only implies

The declaration names "d/f", so a key lives under "/tmp/d" and
`Namei.fs_under` sees it there.  The two words part company: the create
word reaches `openat_create_spec`, the arm a working-directory name takes,
and answers `do_open`'s -EISDIR (fs/namei.c:3951-3952, Linux v6.18.46)
without moving the model; the read word still declines, because answering
it means the directory descriptor `may_open` permits (:3540-3545) and the
model has no directory semantics to give one. -/

/-- The create word at the implied directory: -EISDIR, the model untouched.
rocq-twin: openat_tmp_implied_directory_create_eisdir
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_implied_directory_create_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 577) tmp_dir_model o ↔
      o = errno 21 7 tmp_dir_model := by
  sys_norm

/-- …the descriptor the arm would otherwise have minted is refused…
rocq-twin: openat_tmp_implied_directory_create_eisdir
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_implied_directory_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 577) tmp_dir_model
        (forged 3 7 m' evs) := by
  sys_refute

/-- …and so is the -ENOENT a flat map would have reached for, which is what
separates this answer from a lookup miss.
rocq-twin: openat_tmp_implied_directory_create_eisdir
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_implied_directory_create_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 577) tmp_dir_model
        (forged_errno 2 7 m' evs) := by
  sys_refute

/-- …and the -EISDIR does not leak onto a sibling: "/tmp/x", which nothing
lives under, still mints its key beside "/tmp/d/f".
rocq-twin: openat_tmp_implied_directory_sibling_still_creates
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem tmp_implied_directory_sibling_still_creates (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120] 577) tmp_dir_model o ↔
      (env_errnos 7 tmp_dir_model o ∨
       o = ret 3 7 (fixture_of
             (fds := (3, .FdFileW [47, 116, 109, 112, 47, 120] 0) :: init_fds)
             (fs := fs_set tmp_dir_fs [47, 116, 109, 112, 47, 120] []))) := by
  sys_norm

/-- The read word at the implied directory: declined.
rocq-twin: openat_tmp_implied_directory_read_unmodeled
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_implied_directory_declines_the_read (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 0) tmp_dir_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the directory descriptor refused.
rocq-twin: openat_tmp_implied_directory_read_unmodeled
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_implied_directory_fd_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 0) tmp_dir_model
        (forged 3 7 (fixture_of (fds := (3, .FdDir) :: init_fds) (fs := tmp_dir_fs)) evs) := by
  intro h; sys_refute at h

/-! ### The read branch's guard, where it decides

On `tmp_dir_model` "/tmp/d" is not a key, so the read above declines through
the not-held branch whether or not `Namei.fs_under` is tested first, and
the pins above cannot tell the two orderings apart.  `Fs.valid_fs` admits an
image holding BOTH "/tmp/d" and "/tmp/d/f" — no reality has both, but
nothing refuses it — and there the lookup of "/tmp/d" would succeed: without
the guard the read word would mint an `FdFile` on a name reality makes a
directory.  It is the one image on which the guard changes an answer, so it
is the one that pins it. -/

/-- The image really holds both: the name is a key and has a key under it.
rocq-twin: openat_tmp_implied_directory_unrealizable_image
model: a closed `Fs.fs_lookup` and `Namei.fs_under` over the unrealizable image. -/
theorem tmp_unrealizable_image_holds_both :
    fs_lookup (m_fs tmp_unreal_model) [47, 116, 109, 112, 47, 100] = some [104]
    ∧ fs_under (m_fs tmp_unreal_model) [47, 116, 109, 112, 47, 100] = true := by
  decide

/-- The read word declines there too: the guard runs before the lookup that
would have found the key.
rocq-twin: openat_tmp_implied_directory_unrealizable_image
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_unrealizable_read_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 0) tmp_unreal_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor the lookup would have minted refused…
rocq-twin: openat_tmp_implied_directory_unrealizable_image
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_unrealizable_read_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 0) tmp_unreal_model
        (forged 3 7 m' evs) := by
  sys_refute

/-- …and the -ENOENT of a lookup miss with it: the decline is the arm's, not
an answer about the errno.
rocq-twin: openat_tmp_implied_directory_unrealizable_image
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem tmp_unrealizable_read_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 0) tmp_unreal_model
        (forged_errno 2 7 m' evs) := by
  sys_refute

/-- The create answers -EISDIR ahead of the lookup that would otherwise have
truncated the held key, the model untouched.
rocq-twin: openat_tmp_implied_directory_unrealizable_image
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_unrealizable_create_is_eisdir (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 577) tmp_unreal_model o ↔
      o = errno 21 7 tmp_unreal_model := by
  sys_norm

/-- …and the descriptor refused.
rocq-twin: openat_tmp_implied_directory_unrealizable_image
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_unrealizable_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 100] 577) tmp_unreal_model
        (forged 3 7 m' evs) := by
  sys_refute

/-! ### The separator, not the prefix — and the separator edges after it

`Namei.fs_under` asks whether a held key lies UNDER the name, the name
followed by '/', so a key that merely begins with the name's bytes is a
sibling and the create proceeds; `Namei.tmp_name` refuses a name with a
separator in it, so a repeated or trailing '/' after the prefix is no tmp
name and both words decline. -/

/-- "/tmp/ab" held, "/tmp/a" created: the byte-prefix sibling is no
directory over "a", so the create mints the key — the control the plain
arm has in `byte_prefix_is_not_a_directory` and the tmp arm lacked.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem tmp_sibling_key_is_not_a_directory (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 97] 577) tmp_sibling_model o ↔
      (env_errnos 7 tmp_sibling_model o ∨
       o = ret 3 7 (fixture_of (fds := (3, .FdFileW [47, 116, 109, 112, 47, 97] 0) :: init_fds)
                               (fs := fs_set tmp_sibling_fs [47, 116, 109, 112, 47, 97] []))) := by
  sys_norm

/-- "/tmp//x" is no tmp name, so the read declines, where Linux collapses
the repeated separator (`link_path_walk`, fs/namei.c:2502-2504, Linux
v6.18.46) and reads the held "x": a gap, not an empty intersection, and
the edge a gate that skipped separators would close wrongly.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_double_slash_declines_the_read (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 47, 120] 0) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the reader Linux mints refused…
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_double_slash_read_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 47, 120] 0) tmp_held_model (forged 3 8 m' evs) := by
  sys_refute

/-- …and the create word declines too, where Linux truncates the held "x".
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_double_slash_declines_the_create (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 47, 120] 577) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor on the truncated "x" refused (`link_path_walk` skips the
repeated separator, fs/namei.c:2502-2504, Linux v6.18.46).
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem tmp_double_slash_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 47, 120] 577) tmp_held_model (forged 3 8 m' evs) := by
  sys_refute

/-- "/tmp/x/" names the held regular file with a trailing separator, no tmp
name either: the read declines, where `lookup_fast_for_open` sets
LOOKUP_DIRECTORY off the byte past the last component (fs/namei.c:3830-3831,
Linux v6.18.46) and `do_open` answers -ENOTDIR for a regular file
(fs/namei.c:3958-3959, Linux v6.18.46).  A gate that stripped trailing
separators the way the `unlinkat` gate does would read "x" here instead.
kernel: fs/namei.c:lookup_fast_for_open,do_open@v6.18.46 -/
theorem tmp_trailing_slash_declines_the_read (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120, 47] 0) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -ENOTDIR refused…
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem tmp_trailing_slash_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120, 47] 0) tmp_held_model (forged_errno 20 8 m' evs) := by
  sys_refute

/-- …and the create word declines, where `lookup_fast_for_open` answers
-EISDIR under O_CREAT before the last component is looked up
(fs/namei.c:3821-3823, Linux v6.18.46); `do_open` is never reached on that
path.
kernel: fs/namei.c:lookup_fast_for_open@v6.18.46 -/
theorem tmp_trailing_slash_declines_the_create (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 116, 109, 112, 47, 120, 47] 577) tmp_held_model o ↔ o = Unmodeled := by
  sys_norm

/-- …that -EISDIR refused.
kernel: fs/namei.c:lookup_fast_for_open@v6.18.46 -/
theorem tmp_trailing_slash_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 116, 109, 112, 47, 120, 47] 577) tmp_held_model (forged_errno 21 8 m' evs) := by
  sys_refute

/-! ## The declared declines

Two groups of words Rocq answers and this twin declines, each because a
piece of the port is missing rather than because the kernel is unclear (the
header of `Sys/Fs/Open.lean`): the append word's arm mints `FdFileA` and the
read-write words' arms mint `FdFileRW`, and every spec arm that would write
or resize either descriptor, or read the read-write one, declines so far.
Each is pinned with the kernel's real answer REFUSED beside the `Unmodeled`,
so a later arm has to land that piece before it can answer, and cannot turn
the gap into a guess. -/

/-- The append word on an absent plain name: Linux creates the file and
hands back fd 3 (`lookup_open` fs/namei.c:3788-3800); the arm that says so
mints `FdFileA`, which every spec arm that would write or resize it declines
so far, so the open is a declared decline (`Sys/Fs/Open.lean`'s header).
The probe's `create` case (openat_append.c) is the kernel's success.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem append_word_declines_the_create (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 1089) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the kernel's descriptor is refused, not admitted by another arm.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem append_word_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 1089) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- The append word on an existing file, which Linux opens without
truncating.
The probe's `no-truncate` case (openat_append.c) is the kernel's success.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem append_word_declines_the_existing (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 1089) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and whatever model and events a kernel claims beside that descriptor: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem append_word_existing_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 1089) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- …refusing a descriptor bound to a WRITE-ONLY file entry, the answer a
model that routed the word to `FdFileW` would give and that would make
`Fcntl.setfl_noop_on` unsound (the argument is on Rocq's
`Open.append_create_flags`).
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem append_word_existing_wronly_entry_rejected (evs : List event) :
    ¬ syscall_spec (openat_in [102] 1089) have_model
        (forged 3 2 (fixture_of (fds := (3, .FdFileW [102] 0) :: init_fds) (fs := have_fs)) evs) := by
  intro h; sys_refute at h

/-- The append word on ".": Linux answers -EISDIR (`do_open`,
fs/namei.c:3951-3952); this twin declines the word before the arm and
refuses that -EISDIR too, so the decline is one on the WORD, not a guess
at the dot answer.
The probe's `dot` case (openat_append.c) is the kernel's -EISDIR.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem append_word_declines_the_dot (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46] 1089) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -EISDIR `do_open`'s O_CREAT block answers for "." (fs/namei.c:3951-3952, Linux v6.18.46): refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem append_word_dot_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 1089) absent_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-- The exclusive append word (#1752) on an absent plain name: Linux creates
the file and hands back fd 3 (`lookup_open` fs/namei.c:3788-3800, with
O_APPEND kept in `f_flags`, fs/open.c:981); the arm that says so mints
`FdFileA`, which the Lean `FdEntry` lacks, so the model declines.
The probe's `create` case (openat_excl_append.c) is the kernel's success.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem excl_append_word_declines_the_create (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 1217) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the kernel's descriptor is refused, not admitted by another arm.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem excl_append_word_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 1217) absent_model (forged 3 2 m' evs) := by
  sys_refute

/- The same word on the existing "f" is `append_excl_declines` above. -/

/-- O_RDWR on the existing "f": Linux opens it read-write at fd 3; the arm
mints `FdFileRW`, which every spec arm that would read, write or resize it
declines so far, so the open is a declared decline (`Sys/Fs/Open.lean`'s
header).
The probe's `open-existing` case (openat_rdwr.c) is the kernel's success.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_word_declines_the_read (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 2) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the kernel's descriptor refused.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_word_read_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 2) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_RDWR|O_NONBLOCK (2050) lands where O_RDWR lands — here the decline; the
ignored bit is still ignored on a declined word (Rocq's
`o_nonblock_is_an_ignored_open_flag` states the same equation as two
successes).
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem rdwr_nonblock_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 2050) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the read-write descriptor Linux hands out, O_NONBLOCK inert: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_nonblock_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 2050) have_model (forged 3 2 m' evs) := by
  sys_refute


/-- O_RDWR|O_CREAT on an absent name.
The probe's `create` case (openat_rdwr.c) is the kernel's success.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem rdwr_create_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 66) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor Linux hands out for the file it creates: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem rdwr_create_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 66) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_RDWR|O_TRUNC on the existing file.
The probe's `trunc` case (openat_rdwr.c) is the kernel's truncating success.
kernel: fs/namei.c:do_open,handle_truncate@v6.18.46 -/
theorem rdwr_trunc_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 514) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor Linux hands out after truncating "f": refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_trunc_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 514) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_RDWR|O_CREAT|O_TRUNC on the existing file.
The probe's `creat-trunc` case (openat_rdwr.c) is the kernel's success.
kernel: fs/namei.c:do_open,handle_truncate@v6.18.46 -/
theorem rdwr_create_trunc_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 578) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor Linux hands out after truncating the existing "f": refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_create_trunc_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 578) have_model (forged 3 2 m' evs) := by
  sys_refute

/-- O_RDWR alone on an absent name: Linux answers -ENOENT, and the model
declines rather than answering it, since the word has no arm.
The probe's `absent` case (openat_rdwr.c) is the kernel's -ENOENT.
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem rdwr_absent_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 2) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -ENOENT refused.
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem rdwr_absent_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 2) absent_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- The exclusive read-write words on an absent name.
The probe's `excl-absent` case (openat_rdwr.c) is the kernel's success.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem rdwr_excl_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 194) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor Linux hands out for the file it creates: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem rdwr_excl_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 194) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- …its O_TRUNC spelling…
The probe's `excl-trunc-absent` case (openat_rdwr.c) is the kernel's success.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem rdwr_excl_trunc_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 706) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor Linux hands out for the file it creates: refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:lookup_open@v6.18.46 -/
theorem rdwr_excl_trunc_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 706) absent_model (forged 3 2 m' evs) := by
  sys_refute

/-- …and on the existing file, where Linux answers -EEXIST: refused, since
the word is declined before the arm.
The probe's `excl-exists` case (openat_rdwr.c) is the kernel's -EEXIST.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_excl_existing_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [102] 194) have_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -EEXIST `do_open`'s O_CREAT block answers for the existing "f" (fs/namei.c:3949-3950, Linux v6.18.46): refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_excl_existing_eexist_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [102] 194) have_model (forged_errno 17 2 m' evs) := by
  sys_refute

/-- O_RDWR on ".": Linux answers -EISDIR from `may_open`'s S_IFDIR arm
(fs/namei.c:3540-3542); refused here with the word.
The probe's `dot` case (openat_rdwr.c) is the kernel's -EISDIR.
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem rdwr_dot_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [46] 2) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -EISDIR refused.
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem rdwr_dot_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [46] 2) absent_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-- The read-write words on the implied directory "a" (Rocq answers -EISDIR
and -EEXIST): declined with the words.
kernel: fs/namei.c:do_open,may_open@v6.18.46 -/
theorem rdwr_implied_directory_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [97] 66) under_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -EISDIR `do_open`'s O_CREAT block answers for the implied directory "a" (fs/namei.c:3951-3952, Linux v6.18.46): refused, so the decline is fail-closed rather than an alias of
another word.
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem rdwr_implied_directory_eisdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [97] 66) under_model (forged_errno 21 2 m' evs) := by
  sys_refute

/-! ## "/dev/urandom", the random device (#712)

`openat_urandom_spec` answers the exact byte string ahead of the separator
decline and mints `FdUrandom`, the read-only entry whose reads hand out the
run's declared stream, on the assumption (issue #696,
bugs/openat-urandom-assumed-random-device.md) that the image's
/dev/urandom is the random device: `devlist[9]` (drivers/char/mem.c:701,
Linux v6.18.46) and `memory_open` installing `urandom_fops` (:707-727;
drivers/char/random.c:1572-1581) out of `chrdev_open` (fs/char_dev.c:373-424,
Linux v6.18.46).  Every word below is decided in `do_open` before that open
runs.  What is pinned is the open under each word, Rocq's
`urandom_open_by_word` and `urandom_open_declines`; the census shapes that
read the descriptor are the T9 register's.  No probe can conform past the
open — the harness cannot declare the kernel generator's bytes
(`testing/syscall-check/tests/dev_urandom_decline.c` says so) — so the
kernel side of each pin is read in the source.

A device cgroup can refuse the open with -EPERM: `may_open` asks
`inode_permission` for MAY_OPEN|acc_mode (fs/namei.c:3565-3567, Linux
v6.18.46), which runs devcgroup_inode_permission on the character device
(:597-599), and -EPERM is not among the four `openat_errnos`.  The arms
answer on the premise that the run's cgroup allows the devices it
declares — the same shape as the nodev mount, whose -EACCES IS admitted. -/

/-- O_RDONLY: the read-only device entry at the lowest free fd, the image
untouched, or one of the four environment errnos.  `may_open`'s S_IFCHR arm
(fs/namei.c:3546-3549) tests `may_open_dev` and nothing else, then
`vfs_open` runs `memory_open`, which installs `urandom_fops`.
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:may_open; drivers/char/mem.c:memory_open@v6.18.46 -/
theorem urandom_rdonly_mints_the_reader (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 0) absent_model o ↔
      (env_errnos 13 absent_model o ∨
       o = ret 3 13 (fixture_of (fds := (3, .FdUrandom) :: init_fds))) := by
  sys_norm

/-- …a non-lowest fd refused: `alloc_fd` hands out the lowest free one
(`find_next_fd`, fs/file.c:544-565, called at :584-585).
rocq-twin: urandom_open_by_word
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem urandom_rdonly_non_lowest_fd_rejected (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 0) absent_model
        (forged 4 13 (fixture_of (fds := (4, .FdUrandom) :: init_fds)) evs) := by
  intro h; sys_refute at h

/-- …the entry minted is the random device's, not the null device's: a
success that binds fd 3 to `FdDevNull` is refused.
rocq-twin: urandom_open_by_word
kernel: drivers/char/mem.c:memory_open@v6.18.46 -/
theorem urandom_rdonly_devnull_entry_rejected (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 0) absent_model
        (forged 3 13 (fixture_of (fds := (3, .FdDevNull true false) :: init_fds)) evs) := by
  intro h; sys_refute at h

/-- …and -ENOENT refused: under the premise the node exists, and the walk
finds it (`step_into`, fs/namei.c:2001-2002, is the negative-dentry exit it
does not take).
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:step_into@v6.18.46 -/
theorem urandom_rdonly_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 0) absent_model (forged_errno 2 13 m' evs) := by
  sys_refute

/-- O_RDONLY|O_CLOEXEC is the same open: `build_open_flags` strips the bit
from the open word (fs/open.c:1241, :1251) and no Lean entry records
close-on-exec.
rocq-twin: urandom_open_by_word
kernel: fs/open.c:build_open_flags@v6.18.46 -/
theorem urandom_cloexec_is_the_rdonly_open (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 524288) absent_model o ↔
      (env_errnos 13 absent_model o ∨
       o = ret 3 13 (fixture_of (fds := (3, .FdUrandom) :: init_fds))) := by
  sys_norm

/-- The exclusive words are -EEXIST, deterministic: `do_open`'s O_EXCL test
on an existing name (fs/namei.c:3949-3950), before `may_open`.
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem urandom_excl_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 193) absent_model o ↔ o = errno 17 13 absent_model := by
  sys_norm

/-- …the read-write spelling too.
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem urandom_rdwr_excl_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 194) absent_model o ↔ o = errno 17 13 absent_model := by
  sys_norm

/-- …and a claimed success under O_EXCL is refused.
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem urandom_excl_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 193) absent_model (forged 3 13 m' evs) := by
  sys_refute

/-- The exclusive append word is -EEXIST (#1752), although it is a write
word the arm otherwise declines: O_EXCL refuses the existing node in
`do_open` (fs/namei.c:3949-3950, Linux v6.18.46) before the device is opened.
probe: testing/syscall-check/tests/openat_excl_append.c#conform -- urandom -/
theorem urandom_excl_append_is_eexist (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 1217) absent_model o ↔ o = errno 17 13 absent_model := by
  sys_norm

/-- …and the descriptor refused.
probe: testing/syscall-check/tests/openat_excl_append.c#reject --mutate openat:ret=3 -- urandom -/
theorem urandom_excl_append_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 1217) absent_model (forged 3 13 m' evs) := by
  sys_refute

/-- O_RDONLY|O_DIRECTORY is -ENOTDIR: `do_open`'s LOOKUP_DIRECTORY test
(fs/namei.c:3958-3959).
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem urandom_dir_word_is_enotdir (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 65536) absent_model o ↔ o = errno 20 13 absent_model := by
  sys_norm

/-- …with a claimed success refused.
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:do_open@v6.18.46 -/
theorem urandom_dir_word_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 65536) absent_model (forged 3 13 m' evs) := by
  sys_refute

/-- THE WRITE WORDS ARE DECLINED, NOT ANSWERED.  Linux opens the device for
writing — `may_open` passes a character device and drops O_TRUNC
(fs/namei.c:3546-3555) — and a write through the descriptor reaches
`random_write_iter` (drivers/char/random.c:1448), which mixes the bytes
into the pool; the model has no descriptor on this device that can carry a
write, so the clobbering create word is a decline…
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem urandom_create_word_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 577) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …with the descriptor Linux hands out refused rather than minted by
another arm.
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem urandom_create_word_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 577) absent_model (forged 3 13 m' evs) := by
  sys_refute

/-- …the append word…
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem urandom_append_word_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 1089) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor Linux hands out refused (`may_open`'s S_IFCHR arm,
fs/namei.c:3546-3555, Linux v6.18.46, lets the write word through).
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem urandom_append_word_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 1089) absent_model (forged 3 13 m' evs) := by
  sys_refute

/-- …O_RDWR alone…
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem urandom_rdwr_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 2) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor refused.
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem urandom_rdwr_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 2) absent_model (forged 3 13 m' evs) := by
  sys_refute

/-- …and O_RDWR|O_CREAT|O_TRUNC, O_TRUNC inert on the device.
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem urandom_rdwr_create_trunc_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 578) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor refused.
rocq-twin: urandom_open_by_word
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem urandom_rdwr_create_trunc_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 578) absent_model (forged 3 13 m' evs) := by
  sys_refute

/-- THE ASSUMPTION DOES NOT REACH AN IMAGE THAT SHIPS A FILE UNDER THE
NAME: declined, whatever the kernel said.
rocq-twin: urandom_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem urandom_key_in_image_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 0) urandom_key_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor refused…
rocq-twin: urandom_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem urandom_key_in_image_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 0) urandom_key_model (forged 3 13 m' evs) := by
  sys_refute

/-- …and a key under it ("/dev/urandom/x") declines too.
rocq-twin: urandom_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem urandom_under_key_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in urandom_path 0) urandom_under_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the descriptor Linux would still hand out refused: a key under the name
makes the node a directory, which the read-only word opens (`may_open`'s
S_IFDIR arm, fs/namei.c:3540-3545, Linux v6.18.46).
rocq-twin: urandom_open_declines
kernel: fs/namei.c:may_open@v6.18.46 -/
theorem urandom_under_key_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in urandom_path 0) urandom_under_model (forged 3 13 m' evs) := by
  sys_refute

/-- THE MATCH IS EXACT: "/dev//urandom" is the separator decline…
rocq-twin: urandom_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem urandom_match_is_exact_double_slash (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 100, 101, 118, 47, 47, 117, 114, 97, 110, 100, 111, 109] 0)
        absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …with the descriptor refused on that spelling (the control is
`urandom_rdonly_mints_the_reader`).
rocq-twin: urandom_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem urandom_double_slash_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 100, 101, 118, 47, 47, 117, 114, 97, 110, 100, 111, 109] 0)
        absent_model (forged 3 14 m' evs) := by
  sys_refute

/-- …and so is "/dev/random", the next device over: Linux opens it
(`random_fops`, drivers/char/random.c:1560, Linux v6.18.46, whose read
blocks until the pool is ready), and the ruling on #696 does not name it,
so the separator decline stands.
rocq-twin: urandom_open_declines
probe: testing/syscall-check/tests/dev_urandom_decline.c#fail-closed --expect-unmodeled openat --no-fs-check -- devrandom -/
theorem urandom_dev_random_declines (o : outcome SyscallEffect) :
    syscall_spec (openat_in [47, 100, 101, 118, 47, 114, 97, 110, 100, 111, 109] 0) absent_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …with the descriptor Linux hands out on "/dev/random" refused.
rocq-twin: urandom_open_declines
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem urandom_dev_random_fd_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (openat_in [47, 100, 101, 118, 47, 114, 97, 110, 100, 111, 109] 0) absent_model
        (forged 3 12 m' evs) := by
  sys_refute

/-! # faccessat (48) and faccessat2 (439)

Worked examples over `Sys.Fs.Open.faccessat_spec` and
`Sys.Fs.Open.faccessat2_spec`, the faccessat half of the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/Open.v`.  The same rules as
above: a call goes through the dispatcher on an input numbered 48
(`faccessat_in`) or 439 (`faccessat2_in`), so the table's `fd32`
narrowing of the dirfd is under test with the arm, or through the spec
itself where the pathname is symbolic; every decision is an `iff` over
every outcome beside the refutation of the concrete answer a wrong model
or a lying kernel would give.  Both syscalls are `do_faccessat`
(fs/open.c:467-537, Linux v6.18.46, commit 1f99e9ab748f); each section
below is headed by the statement of it, or the function under it, that
decides the pins the section holds, the 48 arm's sections first and the
flag word's after them.

THE ROCQ WORKED CASES of this half, and where each lives here.  This
list is prose: the file claims no coverage header (the block
`check_lean_cases_parity.py` reads within a file's first 4096 bytes),
because a claim owes one line for every worked case of
`Checks/Cases/Fs/Open.v`, the openat and ftruncate ones included, and
that is a whole-file change; until it is made, that checker counts this
twin unclaimed and nothing mechanical reads this list.

- `faccessat_implied_directory_unmodeled` → `fa_implied_directory_declines`,
  `fa_implied_directory_success_rejected`, `fa_implied_directory_enoent_rejected`
- `faccessat_byte_prefix_is_not_a_directory` → `fa_byte_prefix_is_not_a_directory`,
  `fa_byte_prefix_enoent_rejected`, `fa_byte_prefix_model_untouched`
- `faccessat_bad_mode_beats_an_unreadable_path` → `fa_bad_mode_beats_an_unreadable_path`,
  `fa_bad_mode_unreadable_efault_rejected`
- `faccessat_bad_mode_records_no_copyin` → `fa_bad_mode_ledger_rejected`
- `faccessat_existence_needs_the_copyin` → `fa_present_without_the_ledger_rejected`
- `faccessat2_accepted_flags_change_no_answer` → `fa2_eaccess_changes_no_answer`,
  `fa2_nofollow_changes_no_answer`, `fa2_both_flags_change_no_answer`, and the four
  pins they are assembled from (`fa2_ok_zero`, `fa2_eaccess_answers_as_zero_does`,
  `fa2_nofollow_answers_as_zero_does`, `fa2_both_flags_answer_as_zero_does`)
- `faccessat2_empty_path_flag_declined_either_way` → `fa2_empty_path_flag_declines`,
  `fa2_empty_path_flag_success_rejected`, `fa2_empty_path_flag_enoent_rejected`
- `faccessat2_bad_flag_records_no_copyin` → `fa2_bad_flag_is_einval`,
  `fa2_bad_flag_ledger_rejected`
- `faccessat2_implied_directory_unmodeled` → `fa2_implied_directory_declines`,
  `fa2_implied_directory_success_rejected` -/

/-! ## The register lines, the fixtures and the call -/

attribute [sys_simp low]
  faccessat_spec.eq_1 faccessat2_spec.eq_1 faccessat_body_spec.eq_1
  access_exists_spec.eq_1 faccessat_errnos.eq_1

/-- `faccessat(dirfd, pathp, mode)` as the dispatcher sees it, over the
memory `mem`; nothing writable. -/
def faccessat_in' (dirfd pathp mode : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 48 [dirfd, pathp, mode, 0, 0, 0] mem (fun _ => none)

/-- The ordinary call: `AT_FDCWD`, the pathname `bs` at 8192, the mode `mode`. -/
def faccessat_in (bs : List byte) (mode : word) : SyscallInput :=
  faccessat_in' AT_FDCWD 8192 mode (open_path_mem bs)

/-- `faccessat2(dirfd, pathp, mode, flags)` the same way. -/
def faccessat2_in' (dirfd pathp mode flags : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 439 [dirfd, pathp, mode, flags, 0, 0] mem (fun _ => none)

/-- The ordinary faccessat2 call: `AT_FDCWD`, `bs` at 8192, `mode`, `flags`. -/
def faccessat2_in (bs : List byte) (mode flags : word) : SyscallInput :=
  faccessat2_in' AT_FDCWD 8192 mode flags (open_path_mem bs)

attribute [sys_simp low] faccessat_in'.eq_1 faccessat_in.eq_1 faccessat2_in'.eq_1 faccessat2_in.eq_1

/-- The flags word, faccessat2's fourth argument.
model: `in_arg` on a literal argument list, a rewrite for `sys_norm`. -/
theorem in_arg_mkInput_3 (n a0 a1 a2 a3 a4 a5 : word) (mem wmem : word → Option byte) :
    in_arg (SyscallInput.mkInput n [a0, a1, a2, a3, a4, a5] mem wmem) 3 = a3 := rfl

attribute [sys_simp] in_arg_mkInput_3

/-- The two environment errnos an F_OK probe that finds its name may
answer instead of 0, with nothing changed: -ENOMEM, -EACCES, in the order
`faccessat_errnos` lists them. -/
def access_env_errnos (n : Nat) (m : Model) (o : outcome SyscallEffect) : Prop :=
  o = errno 12 n m ∨ o = errno 13 n m

attribute [sys_simp low] access_env_errnos.eq_1

/-- Rocq's `fa2_model` image. -/
def fa_fs : Fs.Fs := [([97], [])]
/-- Rocq's image for `faccessat_implied_directory_unmodeled`: the key is
present AND implied a directory. -/
def fa_under_fs : Fs.Fs := [([97], []), ([97, 47, 98], [104])]
/-- Rocq's image for `faccessat_byte_prefix_is_not_a_directory`. -/
def fa_sibling_fs : Fs.Fs := [([97], []), ([97, 98], [104])]
/-- What "./x" would resolve to, held. -/
def fa_x_fs : Fs.Fs := [([120], [104])]
/-- The `bytes` probe's name, "fa a\x80": a space and a high byte. -/
def fa_bytes_fs : Fs.Fs := [([102, 97, 32, 97, 128], [])]
def fa_model : Model := fixture_of (fs := fa_fs)
def fa_under_model : Model := fixture_of (fs := fa_under_fs)
def fa_sibling_model : Model := fixture_of (fs := fa_sibling_fs)
def fa_x_model : Model := fixture_of (fs := fa_x_fs)
def fa_bytes_model : Model := fixture_of (fs := fa_bytes_fs)
/-- The `dirfd-file` probe's state: fd 3 open read-only on the held key "a". -/
def fa_file3_model : Model := fixture_of (fds := (3, .FdFile [97] 0) :: init_fds) (fs := fa_fs)

attribute [sys_simp low]
  fa_model.eq_1 fa_under_model.eq_1 fa_sibling_model.eq_1 fa_x_model.eq_1 fa_bytes_model.eq_1
  fa_file3_model.eq_1

/-- "a" is the key of Rocq's `fa2_model` image.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_fa_a : fs_lookup fa_fs [97] = some [] := rfl
/-- "a" is a key of the implied-directory image too — the decline is not
about a missing key.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_fa_under_a : fs_lookup fa_under_fs [97] = some [] := rfl
/-- …and of the byte-prefix image.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_fa_sibling_a : fs_lookup fa_sibling_fs [97] = some [] := rfl
/-- "fa a\x80" is the key of the bytes image.
model: a closed `fs_lookup`, a rewrite for `sys_norm`. -/
theorem lookup_fa_bytes : fs_lookup fa_bytes_fs [102, 97, 32, 97, 128] = some [] := rfl
/-- "fa a\x80".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_fa_bytes :
    read_cstr (open_path_mem [102, 97, 32, 97, 128]) 8192 = CstrOk [102, 97, 32, 97, 128] := rfl
/-- "fa a\x80".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_fa_bytes : cstr_access_len_aux (open_path_mem [102, 97, 32, 97, 128]) 8192 path_max = 6 := rfl
/-- "/".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_root : read_cstr (open_path_mem [47]) 8192 = CstrOk [47] := rfl
/-- "./x".
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_dotslash_x : read_cstr (open_path_mem [46, 47, 120]) 8192 = CstrOk [46, 47, 120] := rfl
/-- "x", the dirfd-file probe's name.
model: a closed `read_cstr`, a rewrite for `sys_norm`. -/
theorem read_x : read_cstr (open_path_mem [120]) 8192 = CstrOk [120] := rfl
/-- "/".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_root : cstr_access_len_aux (open_path_mem [47]) 8192 path_max = 2 := rfl
/-- "x".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_x : cstr_access_len_aux (open_path_mem [120]) 8192 path_max = 2 := rfl
/-- "./x".
model: a closed `cstr_access_len_aux`, a rewrite for `sys_norm`. -/
theorem len_dotslash_x : cstr_access_len_aux (open_path_mem [46, 47, 120]) 8192 path_max = 4 := rfl

attribute [sys_simp]
  lookup_fa_a lookup_fa_under_a lookup_fa_sibling_a lookup_fa_bytes read_root read_dotslash_x read_x
  read_fa_bytes len_root len_dotslash_x len_x len_fa_bytes

/-! ## The constants these checks spell out -/

/-- The two injectable errnos, in the order `errno_from` enumerates them.
kernel: include/uapi/asm-generic/errno-base.h:ENOMEM,EACCES@v6.18.46 -/
theorem faccessat_errnos_are_the_two : faccessat_errnos = [12, 13] := by decide
/-- The three accepted flags as one word: AT_EACCESS (0x200,
include/uapi/linux/fcntl.h:165, Linux v6.18.46) | AT_SYMLINK_NOFOLLOW
(0x100, :120) | AT_EMPTY_PATH (0x1000, :126) — the mask `do_faccessat`
tests the word against.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem access_flags_mask_is_4864 : access_flags_mask = 4864 := by decide
/-- The mode bits the kernel accepts at all.
kernel: include/uapi/linux/stat.h:S_IRWXO@v6.18.46 -/
example : S_IRWXO = 7 := by decide

/-! ## `SYSCALL_DEFINE3(faccessat, …)`: the `int` mode

`SYSCALL_DEFINE3(faccessat, int, dfd, const char __user *, filename, int,
mode)` (fs/open.c:539-542, Linux v6.18.46) declares the mode `int`, so the
register's high half is gone before `do_faccessat` reads a bit of it. -/

/-- 2^32 truncates to F_OK: the present key answers 0, or an environment
errno.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- mode-trunc -/
theorem fa_mode_2_32_is_f_ok (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 4294967296) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- 2^32 + 8 truncates to 8: -EINVAL, nothing read.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- mode-trunc -/
theorem fa_mode_2_32_plus_8_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 4294967304) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-! ## `do_faccessat`: the mode gate

`if (mode & ~S_IRWXO) return -EINVAL;` is the function's opening statement
(fs/open.c:475-476, Linux v6.18.46): ahead of the flag test, of
`access_need_override_creds` and of `user_path_at`.  So the -EINVAL is
deterministic, records no read, and beats every later answer — the
-EFAULT of a NULL pathname, the -EBADF of a closed dirfd, the -ENOENT of an
absent name. -/

/-- Mode 8 on a present key is -EINVAL with an EMPTY ledger and the model
untouched.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- mode-bad -/
theorem fa_bad_mode_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 8) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- …refusing the -EINVAL that CLAIMS the two-byte read: the pathname was
never fetched.
rocq-twin: faccessat_bad_mode_records_no_copyin -/
theorem fa_bad_mode_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 8) fa_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- …and refusing the ONE-byte ledger `smuggle-copyin:a1:1` appends to the
empty one — the harness's lie, where Rocq's is the two-byte range.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:smuggle-copyin:a1:1 -- mode-bad -/
theorem fa_bad_mode_smuggled_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 8) fa_model (forged_errno 22 1 m' evs) := by
  sys_refute

/-- …and refusing -EFAULT, the answer a fetch-first kernel would give.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-EFAULT -- mode-bad -/
theorem fa_bad_mode_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 8) fa_model (Ok (mkEffect (errno_ret 14) [] []) m' evs) := by
  sys_refute

/-- …and -ENOENT, the lookup's answer, which is never reached.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-ENOENT -- mode-bad -/
theorem fa_bad_mode_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 8) fa_model (Ok (mkEffect (errno_ret 2) [] []) m' evs) := by
  sys_refute

/-- 0x10000 is outside S_IRWXO too.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- mode-bad -/
theorem fa_mode_0x10000_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 65536) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- A NEGATIVE mode truncates to 0xffffffff, whose bits outside the mask are
set: -EINVAL.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- mode-bad -/
theorem fa_negative_mode_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 18446744073709551615) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- THE MODE BEATS THE PATHNAME FETCH: mode 8 with a pathname at an address
no byte answers at is -EINVAL with an empty ledger, never -EFAULT.
rocq-twin: faccessat_bad_mode_beats_an_unreadable_path
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_bad_mode_beats_an_unreadable_path (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 4294967196 8192 8 (fun _ => none)) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- …the -EFAULT a spec that fetched first would answer is refused.
rocq-twin: faccessat_bad_mode_beats_an_unreadable_path
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_bad_mode_unreadable_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 4294967196 8192 8 (fun _ => none)) fa_model
        (Ok (mkEffect (errno_ret 14) [] []) m' evs) := by
  sys_refute

/-- The NULL pathname with mode 8: -EINVAL, the pointer never dereferenced.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- mode-first -/
theorem fa_bad_mode_beats_the_null_pointer (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 4294967196 0 8 (open_path_mem [97])) absent_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) absent_model [] := by
  sys_norm

/-- …refusing the -EFAULT of a kernel that fetched the NULL pathname before
testing the mode, ledger included.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat#3:ret=-EFAULT -- mode-first -/
theorem fa_bad_mode_null_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 4294967196 0 8 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 14) [] [])) m' evs) := by
  sys_refute

/-- …and refusing it without the ledger as well.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat#3:ret=-EFAULT -- mode-first -/
theorem fa_bad_mode_null_bare_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 4294967196 0 8 (open_path_mem [97])) absent_model
        (Ok (mkEffect (errno_ret 14) [] []) m' evs) := by
  sys_refute

/-- A closed dirfd (5) loses to the mode: -EINVAL, not -EBADF.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- mode-first -/
theorem fa_bad_mode_beats_the_dirfd (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 5 8192 8 (open_path_mem [97])) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- …the -EBADF refused.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-EBADF -- mode-first -/
theorem fa_bad_mode_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 5 8192 8 (open_path_mem [97])) fa_model
        (Ok (mkEffect (errno_ret 9) [] []) m' evs) := by
  sys_refute

/-- An absent name loses to the mode: -EINVAL, not -ENOENT.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- mode-first -/
theorem fa_bad_mode_beats_the_lookup (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 8) absent_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) absent_model [] := by
  sys_norm

/-- The mode is decided on ANY input before the fetch: over a symbolic
memory the answer is -EINVAL with nothing read, which is what lets a
pathname of no particular shape be left unread.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_bad_mode_reads_no_memory (i : SyscallInput) (o : outcome SyscallEffect) :
    faccessat_spec 4294967196 8192 8 i absent_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) absent_model [] := by
  sys_norm

/-! ## The permission modes: declined after the gate, before the pathname

R_OK, W_OK and X_OK are answered by `inode_permission`
(fs/namei.c:568-602, Linux v6.18.46) out of `inode->i_mode` against the
caller's ids, which the flat map does not hold; the model declines them
after the -EINVAL gate — a bad mode is still the kernel's -EINVAL — and
before the pathname, so the decline never depends on a fetch it could not
then judge. -/

/-- R_OK on a present 0644 file is `Unmodeled`, refusing the 0 Linux answers.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- r-ok -/
theorem fa_r_ok_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 4) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the kernel's 0 refused explicitly.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- r-ok -/
theorem fa_r_ok_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 4) fa_model (forged 0 2 m' evs) := by
  sys_refute

/-- …and the decline is about the mode, not the answer: an -ENOENT forged
on the present name is refused too, as the same forgery on an absent one
would be.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed --mutate faccessat:ret=-ENOENT -- r-ok -/
theorem fa_r_ok_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 4) fa_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- …on the absent name as well: the decline precedes the fetch
(fs/open.c:493, Linux v6.18.46), so the walk's -ENOENT is refused with
everything else.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_r_ok_absent_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 4) absent_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- W_OK likewise.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- w-ok -/
theorem fa_w_ok_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 2) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- X_OK on a 0644 file: Linux answers -EACCES, and the model still declines.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- x-ok -/
theorem fa_x_ok_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 1) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- …refusing that -EACCES, which is not the model's to assert.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- x-ok -/
theorem fa_x_ok_eacces_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 1) fa_model (forged_errno 13 2 m' evs) := by
  sys_refute

/-- R_OK|W_OK|X_OK likewise.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- rwx-ok -/
theorem fa_rwx_ok_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 7) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- The decline precedes the fetch: R_OK with a NULL pathname is `Unmodeled`,
not the -EFAULT Linux answers.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_r_ok_reads_nothing (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 4294967196 0 4 (open_path_mem [97])) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …that -EFAULT refused, with the one-byte ledger it would carry.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_r_ok_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 4294967196 0 4 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 14) [] [])) m' evs) := by
  sys_refute

/-- …and the mode -EINVAL still comes FIRST: mode 12 (R_OK | 8) is -EINVAL,
not a decline.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_bad_mode_beats_the_decline (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 12) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-! ## `getname_flags`: the three fetch answers, before the dirfd

`user_path_at` (fs/namei.c:3211-3219, Linux v6.18.46) calls
`getname_flags` (fs/namei.c:136-216, Linux v6.18.46) before
`filename_lookup` and so before `path_init` sees the dirfd: -EFAULT is
`strncpy_from_user`'s (:157, :161-165), the empty string is -ENOENT
(:167-171; LOOKUP_EMPTY is set only under AT_EMPTY_PATH, fs/open.c:483-484,
Linux v6.18.46, and faccessat passes no flags at all), and a copy that reaches PATH_MAX is
-ENAMETOOLONG (:207-210).  Each is deterministic — no `faccessat_errnos`
member stands beside it — and each records exactly the bytes attempted. -/

/-- A NULL pathname pointer is -EFAULT with the one attempted byte at 0 in the
ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- fault-null -/
theorem fa_null_pointer_is_efault (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 4294967196 0 0 (open_path_mem [97])) absent_model o ↔
      o = Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 14) [] [])) absent_model [] := by
  sys_norm

/-- …not -ENOMEM with this ledger: the -ENOMEMs that precede the copy —
`getname_flags`' own (fs/namei.c:146-148, Linux v6.18.46) and
`access_override_creds`' (fs/open.c:418-465, Linux v6.18.46; its failure
is the -ENOMEM `do_faccessat` returns at :486-489) — carry an empty
ledger, which the wrapper refuses as well.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-ENOMEM -- fault-null -/
theorem fa_null_pointer_enomem_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 4294967196 0 0 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 12) [] [])) m' evs) := by
  sys_refute

/-- …nor -ENAMETOOLONG, the other fetch failure.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-ENAMETOOLONG -- fault-null -/
theorem fa_null_pointer_enametoolong_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 4294967196 0 0 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 36) [] [])) m' evs) := by
  sys_refute

/-- …and the attempted byte cannot be dropped from the ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:drop-copyins -- fault-null -/
theorem fa_null_pointer_without_the_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 4294967196 0 0 (open_path_mem [97])) absent_model
        (Ok (mkEffect (errno_ret 14) [] []) m' evs) := by
  sys_refute

/-- …nor grown: two bytes claimed at 0 is a read the kernel did not make.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:grow-copyins:1 -- fault-null -/
theorem fa_null_pointer_ledger_grown_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 4294967196 0 0 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 2)] (mkEffect (errno_ret 14) [] [])) m' evs) := by
  sys_refute

/-- Mapped bytes whose NUL is unmapped: -EFAULT after the mapped byte and
the faulting one, two bytes in the ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- fault-runoff -/
theorem fa_runoff_is_efault (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 4294967196 8192 0 (bytes_at 8192 [97])) absent_model o ↔
      o = errno 14 2 absent_model := by
  sys_norm

/-- A pathname with no NUL within PATH_MAX is -ENAMETOOLONG, stated over any
memory whose fetch says so, with the bytes `getname` attempted in the
ledger.  The proof hands the fetch result to `simp` after the first pass.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- toolong -/
theorem fa_too_long_is_enametoolong (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (o : outcome SyscallEffect) :
    faccessat_spec 4294967196 8192 0 i absent_model o ↔
      o = Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
               (mkEffect (errno_ret 36) [] [])) absent_model [] := by
  sys_simp_pass +decide
  simp only [hp]
  sys_norm

/-- …not -ENOMEM.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-ENOMEM -- toolong -/
theorem fa_too_long_enomem_rejected (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (m' : Model) (evs : List event) :
    ¬ faccessat_spec 4294967196 8192 0 i absent_model
        (Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
              (mkEffect (errno_ret 12) [] [])) m' evs) := by
  intro h
  sys_simp_pass +decide at h
  simp only [hp] at h
  sys_refute at h

/-- …not -EFAULT: `getname`'s three answers are not interchangeable.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-EFAULT -- toolong -/
theorem fa_too_long_efault_rejected (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (m' : Model) (evs : List event) :
    ¬ faccessat_spec 4294967196 8192 0 i absent_model
        (Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
              (mkEffect (errno_ret 14) [] [])) m' evs) := by
  intro h
  sys_simp_pass +decide at h
  simp only [hp] at h
  sys_refute at h

/-- …and the range attempted stays in the ledger: dropped, it is refused.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:drop-copyins -- toolong -/
theorem fa_too_long_without_the_ledger_rejected (i : SyscallInput)
    (hp : read_cstr i.in_mem 8192 = CstrTooLong) (m' : Model) (evs : List event) :
    ¬ faccessat_spec 4294967196 8192 0 i absent_model (Ok (mkEffect (errno_ret 36) [] []) m' evs) := by
  intro h
  sys_simp_pass +decide at h
  simp only [hp] at h
  sys_refute at h

/-- …and not a byte past it: one more than the bytes attempted is refused.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:grow-copyins:1 -- toolong -/
theorem fa_too_long_ledger_grown_rejected (i : SyscallInput)
    (hp : read_cstr i.in_mem 8192 = CstrTooLong) (m' : Model) (evs : List event) :
    ¬ faccessat_spec 4294967196 8192 0 i absent_model
        (Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max + 1)]
              (mkEffect (errno_ret 36) [] [])) m' evs) := by
  intro h
  sys_simp_pass +decide at h
  simp only [hp] at h
  sys_norm at h
  exact Nat.succ_ne_self _ h.1

/-- The empty pathname is -ENOENT with the one NUL byte in the ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- empty -/
theorem fa_empty_path_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [] 0) absent_model o ↔ o = errno 2 1 absent_model := by
  sys_norm

/-- …-ENOMEM refused on it: nothing allocates between the copy of the
NUL and the -ENOENT `getname_flags` answers for it (fs/namei.c:167-171,
Linux v6.18.46).
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-ENOMEM -- empty -/
theorem fa_empty_path_enomem_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [] 0) absent_model (forged_errno 12 1 m' evs) := by
  sys_refute

/-- …and the NUL that terminated it stays in the ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:drop-copyins -- empty -/
theorem fa_empty_path_without_the_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [] 0) absent_model (Ok (mkEffect (errno_ret 2) [] []) m' evs) := by
  sys_refute

/-- …and it never matches an empty KEY in the image: `getname_flags`
answers before any lookup.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem fa_empty_path_with_an_empty_key_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [] 0) empty_key_model o ↔ o = errno 2 1 empty_key_model := by
  sys_norm

/-- …refusing the 0 a model that looked the empty key up would answer.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem fa_empty_path_empty_key_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [] 0) empty_key_model (forged 0 1 m' evs) := by
  sys_refute

/-! ### The fetch beats the dirfd

`path_init` (fs/namei.c:2540-2645, Linux v6.18.46) resolves the dirfd
inside `filename_lookup`, after `getname_flags` has answered, so a NULL,
over-long or empty pathname answers its errno even beside a dirfd the model
declines — never the -EBADF of a closed one (:2610-2611). -/

/-- The NULL pathname with dirfd 5: -EFAULT, one byte in the ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- dirfd-order -/
theorem fa_null_pointer_beats_the_dirfd (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 5 0 0 (open_path_mem [97])) absent_model o ↔
      o = Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 14) [] [])) absent_model [] := by
  sys_norm

/-- …the -EBADF refused.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem fa_null_pointer_dirfd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 5 0 0 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 9) [] [])) m' evs) := by
  sys_refute

/-- The over-long pathname with dirfd 5: -ENAMETOOLONG.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- dirfd-order -/
theorem fa_too_long_beats_the_dirfd (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (o : outcome SyscallEffect) :
    faccessat_spec 5 8192 0 i absent_model o ↔
      o = Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
               (mkEffect (errno_ret 36) [] [])) absent_model [] := by
  sys_simp_pass +decide
  simp only [hp]
  sys_norm

/-- The empty pathname with dirfd 5: -ENOENT, ahead of the dirfd.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem fa_empty_path_beats_the_dirfd (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 5 8192 0 (open_path_mem [])) absent_model o ↔
      o = errno 2 1 absent_model := by
  sys_norm

/-! ## `path_init`: the dirfd

`path_init` (fs/namei.c:2540-2645, Linux v6.18.46) starts a relative walk
at the working directory for AT_FDCWD (:2590-2604) and otherwise at the
dirfd's file (:2605-2632): -EBADF on a closed fd (:2610-2611), -ENOTDIR on
an open one that is not a directory (:2621-2622), and a walk under a
directory the flat map cannot represent otherwise.  The model answers
AT_FDCWD only and declines the rest — never with one of those errnos,
which it cannot judge without knowing what the fd names. -/

/-- A closed dirfd (5) is `Unmodeled`, not the -EBADF Linux answers.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- dirfd-bad -/
theorem fa_dirfd_bad_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 5 8192 0 (open_path_mem [97])) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -EBADF refused.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- dirfd-bad -/
theorem fa_dirfd_bad_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 5 8192 0 (open_path_mem [97])) fa_model (forged_errno 9 2 m' evs) := by
  sys_refute

/-- …and the 0 a model that ignored the dirfd would answer for the present
key.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem fa_dirfd_bad_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 5 8192 0 (open_path_mem [97])) fa_model (forged 0 2 m' evs) := by
  sys_refute

/-- dirfd 3, open on the regular file "a" as the probe's is, is `Unmodeled`
too, not the -ENOTDIR Linux answers for a non-directory dirfd: the arm
declines every dirfd but AT_FDCWD before it would read the table.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- dirfd-file -/
theorem fa_dirfd_file_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 3 8192 0 (open_path_mem [120])) fa_file3_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -ENOTDIR refused.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- dirfd-file -/
theorem fa_dirfd_file_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 3 8192 0 (open_path_mem [120])) fa_file3_model
        (forged_errno 20 2 m' evs) := by
  sys_refute

/-- …and dirfd 1, an open channel, declines the same way.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem fa_dirfd_channel_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 1 8192 0 (open_path_mem [120])) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- "." relative to a dirfd the model declines is declined, not answered:
`path_init` resolves the dirfd before `handle_dots` sees the component, and
on Linux a closed dirfd is -EBADF here too.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem fa_dot_with_dirfd_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 5 8192 0 (open_path_mem [46])) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- …refusing the 0 a model that answered "." before reading the dirfd would
give.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem fa_dot_with_dirfd_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in' 5 8192 0 (open_path_mem [46])) fa_model (forged 0 2 m' evs) := by
  sys_refute

/-- AT_FDCWD is compared in the low 32 bits: 2^32 - 100 in the register is
AT_FDCWD, and the present key answers.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- dirfd-cwd -/
theorem fa_dirfd_low_half_is_at_fdcwd (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 4294967196 8192 0 (open_path_mem [97])) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- …and so is the full sign-extended word, which `fd32` narrows to the same.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- f-ok-present -/
theorem fa_dirfd_sign_extended_is_at_fdcwd (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 18446744073709551516 8192 0 (open_path_mem [97])) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- …while 2^32 + (2^32 - 100), whose low half is also AT_FDCWD, is AT_FDCWD
as well: the `int dfd` reads the low half alone.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem fa_dirfd_high_bits_dropped (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in' 8589934492 8192 0 (open_path_mem [97])) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-! ## `handle_dots`: "." and ".."

`link_path_walk` types the last component LAST_DOT or LAST_DOTDOT
(fs/namei.c:2475-2482, Linux v6.18.46) and `handle_dots`
(fs/namei.c:2096-2132, Linux v6.18.46) answers them without a filesystem
lookup: "." is the working directory and ".." its parent, and both exist.
"..." is LAST_NORM, an ordinary name. -/

/-- "." exists: 0, or an environment errno, two bytes in the ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- dot -/
theorem fa_dot_exists (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [46] 0) absent_model o ↔
      (access_env_errnos 2 absent_model o ∨ o = ret 0 2 absent_model) := by
  sys_norm

/-- …never -ENOENT: the working directory is not looked up.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-ENOENT -- dot -/
theorem fa_dot_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [46] 0) absent_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- …but a search-denied working directory is -EACCES, which is accepted.
probe: testing/syscall-check/tests/faccessat_spec.c#conform --mutate faccessat:ret=-EACCES -- dot -/
theorem fa_dot_eacces_allowed :
    syscall_spec (faccessat_in [46] 0) absent_model (errno 13 2 absent_model) := by
  sys_norm

/-- ".." exists likewise, three bytes in the ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- dotdot -/
theorem fa_dotdot_exists (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [46, 46] 0) absent_model o ↔
      (access_env_errnos 3 absent_model o ∨ o = ret 0 3 absent_model) := by
  sys_norm

/-- …and is never absent either.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-ENOENT -- dotdot -/
theorem fa_dotdot_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [46, 46] 0) absent_model (forged_errno 2 3 m' evs) := by
  sys_refute

/-- "..." is an ordinary name: absent, -ENOENT, four bytes in the ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- dot3 -/
theorem fa_dot3_is_an_ordinary_name (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [46, 46, 46] 0) absent_model o ↔ o = errno 2 4 absent_model := by
  sys_norm

/-- …refusing the 0 a model that treated every dot-run as a directory
reference would answer.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem fa_dot3_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [46, 46, 46] 0) absent_model (forged 0 4 m' evs) := by
  sys_refute

/-! ## `link_path_walk`: the separator decline

`link_path_walk` (fs/namei.c:2441-2537, Linux v6.18.46) walks every
interior component through the filesystem, and none of its answers — the
-ENOTDIR of a regular file in the middle, the 0 of "/" and "./x" — is one
a flat key can stand for.  So a pathname with a separator is declined,
whatever the map holds. -/

/-- "a/b" is `Unmodeled` on the image holding "a" — the probe's shape, a
walk into a regular file.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- slash -/
theorem fa_slash_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97, 47, 98] 0) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- …refusing the -ENOENT a flat map holding no "a/b" would confidently
answer.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- slash -/
theorem fa_slash_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97, 47, 98] 0) fa_model (forged_errno 2 4 m' evs) := by
  sys_refute

/-- …and refusing the -ENOTDIR Linux answers when "a" is a regular file.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- slash -/
theorem fa_slash_enotdir_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97, 47, 98] 0) fa_model (forged_errno 20 4 m' evs) := by
  sys_refute

/-- A KEY spelled with a separator is declined even when the map holds it.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem fa_slash_key_in_image_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97, 47, 98] 0) under_model o ↔ o = Unmodeled := by
  sys_norm

/-- …refusing the 0 a "just look the key up" model would answer.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem fa_slash_key_in_image_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97, 47, 98] 0) under_model (forged 0 4 m' evs) := by
  sys_refute

/-- "/" resolves on Linux and returns 0; the model declines it.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- root -/
theorem fa_root_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [47] 0) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …that 0 refused.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- root -/
theorem fa_root_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [47] 0) absent_model (forged 0 2 m' evs) := by
  sys_refute

/-- "./x" resolves to "x" on Linux; the model has no normalization and
declines it even when "x" is held.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- dotslash -/
theorem fa_dotslash_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [46, 47, 120] 0) fa_x_model o ↔ o = Unmodeled := by
  sys_norm

/-- …refusing both the -ENOENT of a flat lookup of "./x"…
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- dotslash -/
theorem fa_dotslash_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [46, 47, 120] 0) fa_x_model (forged_errno 2 4 m' evs) := by
  sys_refute

/-- …and the 0 Linux answers when "x" exists.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- dotslash -/
theorem fa_dotslash_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [46, 47, 120] 0) fa_x_model (forged 0 4 m' evs) := by
  sys_refute

/-- "/a" is declined as well: an absolute path is a walk from the root,
which `path_init` sets (fs/namei.c:2582-2586, Linux v6.18.46) before
`link_path_walk` strips the leading slashes.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem fa_absolute_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [47, 97] 0) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-! ## The NAME_MAX boundary

`getname_flags`' PATH_MAX bound lets a 4095-byte component through, and the
FILESYSTEM then answers -ENAMETOOLONG for one over NAME_MAX
(include/uapi/linux/limits.h:12, Linux v6.18.46) — ext4's lookup, tmpfs's
`simple_lookup` — which the model has no filesystem type to ask.  A
255-byte component is an ordinary name.  The pins here are over a symbolic
pathname whose length is given, as the O_DIRECTORY pins above are. -/

/-- A 255-byte absent component is -ENOENT.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- name255 -/
theorem fa_name_max_255_answers (i : SyscallInput) (p : path)
    (hp : read_cstr i.in_mem 8192 = CstrOk p) (hlen : p.length = 255)
    (hs : path_has_slash p = false) (o : outcome SyscallEffect) :
    faccessat_spec 4294967196 8192 0 i absent_model o ↔
      o = Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
               (mkEffect (errno_ret 2) [] [])) absent_model [] := by
  have hne : path_eqb p [] = false :=
    path_eqb_false_of_ne p [] (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hd1 : path_eqb p dot_path = false :=
    path_eqb_false_of_ne p dot_path (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hd2 : path_eqb p dotdot_path = false :=
    path_eqb_false_of_ne p dotdot_path (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hu : fs_under [] p = false := rfl
  sys_simp_pass +decide
  simp only [hp, hne, hd1, hd2, hs, hlen, hu]
  sys_norm

/-- A 256-byte component is `Unmodeled`.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- name256 -/
theorem fa_name_max_256_declines (i : SyscallInput) (p : path)
    (hp : read_cstr i.in_mem 8192 = CstrOk p) (hlen : p.length = 256)
    (hs : path_has_slash p = false) (o : outcome SyscallEffect) :
    faccessat_spec 4294967196 8192 0 i absent_model o ↔ o = Unmodeled := by
  have hne : path_eqb p [] = false :=
    path_eqb_false_of_ne p [] (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hd1 : path_eqb p dot_path = false :=
    path_eqb_false_of_ne p dot_path (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hd2 : path_eqb p dotdot_path = false :=
    path_eqb_false_of_ne p dotdot_path (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hu : fs_under [] p = false := rfl
  sys_simp_pass +decide
  simp only [hp, hne, hd1, hd2, hs, hlen, hu]
  sys_norm

/-- …refusing the -ENAMETOOLONG the filesystem really answers: it is not
the model's to assert.
probe: testing/syscall-check/tests/faccessat_spec.c#fail-closed -- name256 -/
theorem fa_name_max_256_enametoolong_rejected (i : SyscallInput) (p : path)
    (hp : read_cstr i.in_mem 8192 = CstrOk p) (hlen : p.length = 256)
    (hs : path_has_slash p = false) (m' : Model) (evs : List event) :
    ¬ faccessat_spec 4294967196 8192 0 i absent_model
        (Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
              (mkEffect (errno_ret 36) [] [])) m' evs) := by
  have hne : path_eqb p [] = false :=
    path_eqb_false_of_ne p [] (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hd1 : path_eqb p dot_path = false :=
    path_eqb_false_of_ne p dot_path (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hd2 : path_eqb p dotdot_path = false :=
    path_eqb_false_of_ne p dotdot_path (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hu : fs_under [] p = false := rfl
  intro h
  sys_simp_pass +decide at h
  simp only [hp, hne, hd1, hd2, hs, hlen, hu] at h
  sys_refute at h

/-! ## `fs_under`: the implied directory, and the byte prefix that is not one

A key "a/b" means reality has a DIRECTORY "a", and F_OK of a directory is 0
where the flat map would answer for the key "a" alone.  So a name some key
lives under is declined — here to avoid a wrong exists-or-not rather than
the wrong errno `unlinkat` guards against.  "ab" is a BYTE prefix, not a
component prefix, and "a" beside it is an ordinary key. -/

/-- F_OK of "a" on the image holding "a" and "a/b" is `Unmodeled`.
rocq-twin: faccessat_implied_directory_unmodeled -/
theorem fa_implied_directory_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 0) fa_under_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the 0 Rocq's case offers refused…
rocq-twin: faccessat_implied_directory_unmodeled -/
theorem fa_implied_directory_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_under_model (forged 0 2 m' evs) := by
  sys_refute

/-- …and the -ENOENT a map that only saw "a/b" would answer refused too:
on Linux "a" is then a directory, a positive dentry, and F_OK of it is 0.
rocq-twin: faccessat_implied_directory_unmodeled
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem fa_implied_directory_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_under_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- The decline holds when "a" is NOT itself a key: "a/b" alone declines "a",
whose real directory Linux answers 0 for (the MAY_ACCESS-only permission
test at fs/open.c:509, Linux v6.18.46).
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_implied_directory_without_the_key_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 0) under_model o ↔ o = Unmodeled := by
  sys_norm

/-- THE CONTRAST: on the image holding "a" and "ab", F_OK of "a" is answered
— 0 or an environment errno — with the model exactly as it was.
rocq-twin: faccessat_byte_prefix_is_not_a_directory -/
theorem fa_byte_prefix_is_not_a_directory (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 0) fa_sibling_model o ↔
      (access_env_errnos 2 fa_sibling_model o ∨ o = ret 0 2 fa_sibling_model) := by
  sys_norm

/-- …refusing -ENOENT: "a" is there, a positive dentry beside "ab".
rocq-twin: faccessat_byte_prefix_is_not_a_directory
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem fa_byte_prefix_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_sibling_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- …and refusing a success that changed the file system.
rocq-twin: faccessat_byte_prefix_is_not_a_directory -/
theorem fa_byte_prefix_model_untouched (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_sibling_model (forged 0 2 fa_model evs) := by
  sys_refute

/-- And when "a" is absent beside "ab": -ENOENT.
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem fa_byte_prefix_absent_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 0) sibling_model o ↔ o = errno 2 2 sibling_model := by
  sys_norm

/-! ## The lookup: a present key, an absent one

Past every guard the map is the answer.  A present key is the existence
arm: 0, or -ENOMEM from the walk's own dentry allocation — `__lookup_slow`
(fs/namei.c:1789-1824, Linux v6.18.46) asks `d_alloc_parallel` for the
dentry at :1801, and the allocation failing there is -ENOMEM
(fs/dcache.c:2549-2554, Linux v6.18.46), after the pathname has been read
— or the -EACCES `may_lookup` (fs/namei.c:1852-1874, Linux v6.18.46)
raises on a search-denied working directory.  An absent key is the
negative dentry `traverse_mounts` (fs/namei.c:1529-1542, Linux v6.18.46)
turns into -ENOENT (:1537-1538) inside `step_into`.  That -ENOENT is the
model's ONE answer there, not a kernel determinism: the same two errnos
reach an absent name — on tmpfs every absent lookup allocates, since
`simple_lookup` marks its negatives DCACHE_DONTCACHE (fs/libfs.c:73-76,
Linux v6.18.46) and they do not survive in the cache, and `may_lookup`
runs on the working directory before the last component is looked up —
and the pins below refuse both.  That is the narrowing Rocq's
`Open.faccessat_body_spec` APPROXIMATION paragraph declares and
`openat_body_spec` carries too, at the same cost to the theorem.  Nothing
F_OK reaches is gated on a bit it sets: -EROFS needs S_IWOTH
(fs/open.c:511-524, Linux v6.18.46), -EPERM needs MAY_WRITE, and the DAC
comparison narrows a zero mask away. -/

/-- F_OK on a present key: 0 or an environment errno, two bytes in the
ledger, the model untouched.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- f-ok-present -/
theorem fa_present_exists (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 0) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- …a key that is there cannot be missing.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-ENOENT -- f-ok-present -/
theorem fa_present_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- …-ENOMEM is accepted…
probe: testing/syscall-check/tests/faccessat_spec.c#conform --mutate faccessat:ret=-ENOMEM -- f-ok-present -/
theorem fa_present_enomem_allowed :
    syscall_spec (faccessat_in [97] 0) fa_model (errno 12 2 fa_model) := by
  sys_norm

/-- …and so is -EACCES.
probe: testing/syscall-check/tests/faccessat_spec.c#conform --mutate faccessat:ret=-EACCES -- f-ok-present -/
theorem fa_present_eacces_allowed :
    syscall_spec (faccessat_in [97] 0) fa_model (errno 13 2 fa_model) := by
  sys_norm

/-- -EROFS is refused: F_OK never reaches the read-only test.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-EROFS -- f-ok-present -/
theorem fa_present_erofs_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model (forged_errno 30 2 m' evs) := by
  sys_refute

/-- -EPERM is refused: the immutable test is gated on MAY_WRITE.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-EPERM -- f-ok-present -/
theorem fa_present_eperm_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model (forged_errno 1 2 m' evs) := by
  sys_refute

/-- -EINVAL is refused: the mode was fine.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-EINVAL -- f-ok-present -/
theorem fa_present_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- A positive return is refused: faccessat answers 0 or an errno.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=1 -- f-ok-present -/
theorem fa_present_positive_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model (forged 1 2 m' evs) := by
  sys_refute

/-- THE LEDGER IS REQUIRED past the mode test: the F_OK call read the
pathname, so a 0 that recorded no read is refused.
rocq-twin: faccessat_existence_needs_the_copyin
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:drop-copyins -- f-ok-present -/
theorem fa_present_without_the_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and it ends at the NUL: three bytes claimed for "a\0" is refused.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:grow-copyins:1 -- f-ok-present -/
theorem fa_present_ledger_grown_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model (forged 0 3 m' evs) := by
  sys_refute

/-- …and it is recorded once: a second copy of the range is refused.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:smuggle-copyin:a1:1 -- f-ok-present -/
theorem fa_present_double_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model
        (Ok (with_copyins [(8192, 2), (8192, 1)] (mkEffect 0 [] [])) m' evs) := by
  sys_refute

/-- faccessat writes nothing: a success carrying a write is refused.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:smuggle-write:a1:1 -- f-ok-present -/
theorem fa_present_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model
        (Ok (with_copyins [(8192, 2)] (mkEffect 0 [(8192, [0])] [])) m' evs) := by
  sys_refute

/-- …and zeroes nothing.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:smuggle-zeros:a1 -- f-ok-present -/
theorem fa_present_zero_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model
        (Ok (with_copyins [(8192, 2)] (mkEffect 0 [] [(8192, 1)])) m' evs) := by
  sys_refute

/-- …unmaps nothing…
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:smuggle-unmap:a1 -- f-ok-present -/
theorem fa_present_unmap_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(8192, 4096)] [] [(8192, 2)]) m' evs) := by
  sys_refute

/-- …and copies nothing.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:smuggle-copy:a1:a1:1 -- f-ok-present -/
theorem fa_present_copy_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 8192 8192 1] [(8192, 2)]) m' evs) := by
  sys_refute

/-- …and touches no state: a 0 that changed the model is refused.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_present_model_untouched (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model (forged 0 2 absent_model evs) := by
  sys_refute

/-- …nor does an -ENOMEM, and neither emits an event.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa_present_enomem_events_rejected (e : event) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) fa_model (forged_errno 12 2 fa_model (e :: evs)) := by
  sys_refute

/-- The present key with data: "f" holding "hi" is there too.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- f-ok-present -/
theorem fa_present_with_bytes_exists (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [102] 0) have_model o ↔
      (access_env_errnos 2 have_model o ∨ o = ret 0 2 have_model) := by
  sys_norm

/-- A name is a byte string to both sides: "fa a\x80", a space and a high
byte, is looked up as the five bytes it is (six in the ledger, with the NUL).
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- bytes -/
theorem fa_byte_name_exists (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [102, 97, 32, 97, 128] 0) fa_bytes_model o ↔
      (access_env_errnos 6 fa_bytes_model o ∨ o = ret 0 6 fa_bytes_model) := by
  sys_norm

/-- …and is absent on the image that holds only "a".
kernel: fs/namei.c:traverse_mounts@v6.18.46 -/
theorem fa_byte_name_absent_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [102, 97, 32, 97, 128] 0) fa_model o ↔ o = errno 2 6 fa_model := by
  sys_norm

/-- F_OK on an absent name is -ENOENT, deterministic, two bytes in the ledger.
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- f-ok-absent -/
theorem fa_absent_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 0) absent_model o ↔ o = errno 2 2 absent_model := by
  sys_norm

/-- …existence IS tracked: a 0 is refused.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=0 -- f-ok-absent -/
theorem fa_absent_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) absent_model (forged 0 2 m' evs) := by
  sys_refute

/-- …and the model gives its -ENOENT no alternative — not the -ENOMEM the
walk's dentry allocation can raise on it (the section header says where):
the declared narrowing, pinned…
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-ENOMEM -- f-ok-absent -/
theorem fa_absent_enomem_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) absent_model (forged_errno 12 2 m' evs) := by
  sys_refute

/-- …nor the -EACCES `may_lookup` can raise on the working directory
first: refused all the same.
probe: testing/syscall-check/tests/faccessat_spec.c#reject --mutate faccessat:ret=-EACCES -- f-ok-absent -/
theorem fa_absent_eacces_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat_in [97] 0) absent_model (forged_errno 13 2 m' evs) := by
  sys_refute

/-- An absent name on a NON-empty image is -ENOENT as well: "a" beside "f".
probe: testing/syscall-check/tests/faccessat_spec.c#conform -- f-ok-absent -/
theorem fa_absent_beside_another_key_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat_in [97] 0) have_model o ↔ o = errno 2 2 have_model := by
  sys_norm

/-! # faccessat2 (439)

`SYSCALL_DEFINE4(faccessat2, …)` (fs/open.c:544-548, Linux v6.18.46) is
`do_faccessat` with the caller's flag word.  Everything above holds on
this arm unchanged — the shared `faccessat_body_spec` is what makes it
hold, and the pins below on "." and the guards are what say the sharing
survived — and the flag word adds two gates in the kernel's order: the
flag -EINVAL (fs/open.c:478-479, Linux v6.18.46) right after the mode
-EINVAL, and, after
both, the AT_EMPTY_PATH decline. -/

/-! ## The answered flag words: 0, AT_EACCESS, AT_SYMLINK_NOFOLLOW, both -/

/-- Flags 0 on a present key: 0 or an environment errno, the same answer as
`faccessat`.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- ok-zero -/
theorem fa2_ok_zero (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 0) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- …-ENOENT refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-ENOENT -- ok-zero -/
theorem fa2_ok_zero_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- …-ENOMEM accepted…
probe: testing/syscall-check/tests/faccessat2_spec.c#conform --mutate faccessat2:ret=-ENOMEM -- ok-zero -/
theorem fa2_ok_zero_enomem_allowed :
    syscall_spec (faccessat2_in [97] 0 0) fa_model (errno 12 2 fa_model) := by
  sys_norm

/-- …-EACCES accepted…
probe: testing/syscall-check/tests/faccessat2_spec.c#conform --mutate faccessat2:ret=-EACCES -- ok-zero -/
theorem fa2_ok_zero_eacces_allowed :
    syscall_spec (faccessat2_in [97] 0 0) fa_model (errno 13 2 fa_model) := by
  sys_norm

/-- …-EINVAL refused: both words were accepted.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-EINVAL -- ok-zero -/
theorem fa2_ok_zero_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- …-EROFS refused: F_OK never reaches the read-only test.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-EROFS -- ok-zero -/
theorem fa2_ok_zero_erofs_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model (forged_errno 30 2 m' evs) := by
  sys_refute

/-- …a positive return refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=1 -- ok-zero -/
theorem fa2_ok_zero_positive_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model (forged 1 2 m' evs) := by
  sys_refute

/-- …the ledger required…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:drop-copyins -- ok-zero -/
theorem fa2_ok_zero_without_the_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …ending at the NUL…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:grow-copyins:1 -- ok-zero -/
theorem fa2_ok_zero_ledger_grown_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model (forged 0 3 m' evs) := by
  sys_refute

/-- …and recorded once.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:smuggle-copyin:a1:1 -- ok-zero -/
theorem fa2_ok_zero_double_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model
        (Ok (with_copyins [(8192, 2), (8192, 1)] (mkEffect 0 [] [])) m' evs) := by
  sys_refute

/-- faccessat2 writes nothing either…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:smuggle-write:a1:1 -- ok-zero -/
theorem fa2_ok_zero_write_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model
        (Ok (with_copyins [(8192, 2)] (mkEffect 0 [(8192, [0])] [])) m' evs) := by
  sys_refute

/-- …unmaps nothing…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:smuggle-unmap:a1 -- ok-zero -/
theorem fa2_ok_zero_unmap_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [(8192, 4096)] [] [(8192, 2)]) m' evs) := by
  sys_refute

/-- …and copies nothing.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:smuggle-copy:a1:a1:1 -- ok-zero -/
theorem fa2_ok_zero_copy_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) fa_model
        (Ok (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 8192 8192 1] [(8192, 2)]) m' evs) := by
  sys_refute

/-- Flags 0 on an absent name: -ENOENT.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- absent -/
theorem fa2_absent_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 0) absent_model o ↔ o = errno 2 2 absent_model := by
  sys_norm

/-- …a 0 refused…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=0 -- absent -/
theorem fa2_absent_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) absent_model (forged 0 2 m' evs) := by
  sys_refute

/-- …and -ENOMEM refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-ENOMEM -- absent -/
theorem fa2_absent_enomem_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 0) absent_model (forged_errno 12 2 m' evs) := by
  sys_refute

/-- AT_EACCESS (512) on a present key answers exactly as flags 0 does:
`access_need_override_creds` (fs/open.c:391-416, Linux v6.18.46) returns
false at once (:395-396), the walk runs under the caller's own cred, and
under F_OK no comparison reads either cred.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- eaccess -/
theorem fa2_eaccess_answers_as_zero_does (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 512) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- …-ENOENT refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-ENOENT -- eaccess -/
theorem fa2_eaccess_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 512) fa_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- …-ENOMEM still accepted: `getname_flags`' allocation survives the cred
override being skipped.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform --mutate faccessat2:ret=-ENOMEM -- eaccess -/
theorem fa2_eaccess_enomem_allowed :
    syscall_spec (faccessat2_in [97] 0 512) fa_model (errno 12 2 fa_model) := by
  sys_norm

/-- …-EINVAL refused: AT_EACCESS is an accepted bit.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-EINVAL -- eaccess -/
theorem fa2_eaccess_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 512) fa_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- …and it is not a decline: `Unmodeled` is refused (the `iff` above says so;
this is the concrete half).
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- eaccess -/
theorem fa2_eaccess_is_not_declined :
    ¬ syscall_spec (faccessat2_in [97] 0 512) fa_model Unmodeled := by
  sys_refute

/-- AT_EACCESS on an absent name: -ENOENT, as with flags 0.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- eaccess -/
theorem fa2_eaccess_absent_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 512) absent_model o ↔ o = errno 2 2 absent_model := by
  sys_norm

/-- …an absent name is still absent.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2#2:ret=0 -- eaccess -/
theorem fa2_eaccess_absent_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 512) absent_model (forged 0 2 m' evs) := by
  sys_refute

/-- AT_SYMLINK_NOFOLLOW (256) on a present regular file: the same answer.
It clears LOOKUP_FOLLOW (fs/open.c:481-482, Linux v6.18.46), which changes
what a trailing SYMLINK resolves to, and a resolvable key here is a
regular file.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- nofollow -/
theorem fa2_nofollow_answers_as_zero_does (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 256) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- …-ENOENT refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-ENOENT -- nofollow -/
theorem fa2_nofollow_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 256) fa_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- AT_SYMLINK_NOFOLLOW on an absent name: -ENOENT.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- nofollow -/
theorem fa2_nofollow_absent_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 256) absent_model o ↔ o = errno 2 2 absent_model := by
  sys_norm

/-- …a 0 refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2#2:ret=0 -- nofollow -/
theorem fa2_nofollow_absent_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 256) absent_model (forged 0 2 m' evs) := by
  sys_refute

/-- Both together (768): the same answer.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- both-flags -/
theorem fa2_both_flags_answer_as_zero_does (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 768) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- …an accepted PAIR is not a bad word: -EINVAL refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-EINVAL -- both-flags -/
theorem fa2_both_flags_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 768) fa_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- ACCEPTED FLAGS CHANGE NO ANSWER, as an equality between flag words — the
claim no probe reaches, since a run is shown the answer for the word it
passed: the call under AT_EACCESS has exactly the outcomes the call under
0 has.  Assembled from the two `iff`s above.
rocq-twin: faccessat2_accepted_flags_change_no_answer -/
theorem fa2_eaccess_changes_no_answer (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 512) fa_model o ↔ syscall_spec (faccessat2_in [97] 0 0) fa_model o :=
  (fa2_eaccess_answers_as_zero_does o).trans (fa2_ok_zero o).symm

/-- …AT_SYMLINK_NOFOLLOW likewise.
rocq-twin: faccessat2_accepted_flags_change_no_answer -/
theorem fa2_nofollow_changes_no_answer (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 256) fa_model o ↔ syscall_spec (faccessat2_in [97] 0 0) fa_model o :=
  (fa2_nofollow_answers_as_zero_does o).trans (fa2_ok_zero o).symm

/-- …and both together.
rocq-twin: faccessat2_accepted_flags_change_no_answer -/
theorem fa2_both_flags_change_no_answer (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 768) fa_model o ↔ syscall_spec (faccessat2_in [97] 0 0) fa_model o :=
  (fa2_both_flags_answer_as_zero_does o).trans (fa2_ok_zero o).symm

/-- "." with AT_SYMLINK_NOFOLLOW exists: `handle_dots` reads no link.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- dot -/
theorem fa2_dot_nofollow_exists (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [46] 0 256) absent_model o ↔
      (access_env_errnos 2 absent_model o ∨ o = ret 0 2 absent_model) := by
  sys_norm

/-- …never -ENOENT…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-ENOENT -- dot -/
theorem fa2_dot_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [46] 0 256) absent_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- …but -EACCES on a search-denied working directory.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform --mutate faccessat2:ret=-EACCES -- dot -/
theorem fa2_dot_eacces_allowed :
    syscall_spec (faccessat2_in [46] 0 256) absent_model (errno 13 2 absent_model) := by
  sys_norm

/-- ".." with AT_EACCESS exists.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- dot -/
theorem fa2_dotdot_eaccess_exists (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [46, 46] 0 512) absent_model o ↔
      (access_env_errnos 3 absent_model o ∨ o = ret 0 3 absent_model) := by
  sys_norm

/-! ## `do_faccessat`: the flag gate, second, and before the pathname

`if (flags & ~(AT_EACCESS | AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH)) return
-EINVAL;` is the function's second statement (fs/open.c:478-479, Linux
v6.18.46), after the mode test and before `user_path_at`: a bad flag word
is the kernel's own -EINVAL, records no read, and beats the dirfd and the
pathname alike. -/

/-- AT_SYMLINK_FOLLOW (0x400) is outside the three: -EINVAL with an EMPTY
ledger, on a name that IS there.
rocq-twin: faccessat2_bad_flag_records_no_copyin
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- flags-bad -/
theorem fa2_bad_flag_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 1024) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- …the -EINVAL that CLAIMS the two-byte read refused.
rocq-twin: faccessat2_bad_flag_records_no_copyin -/
theorem fa2_bad_flag_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 1024) fa_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- …and the ONE-byte ledger `smuggle-copyin:a1:1` appends, the harness's
lie beside Rocq's two-byte one.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:smuggle-copyin:a1:1 -- flags-bad -/
theorem fa2_bad_flag_smuggled_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 1024) fa_model (forged_errno 22 1 m' evs) := by
  sys_refute

/-- …a 0 refused…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=0 -- flags-bad -/
theorem fa2_bad_flag_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 1024) fa_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and -EFAULT refused: the -EINVAL arm takes nothing else.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-EFAULT -- flags-bad -/
theorem fa2_bad_flag_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 1024) fa_model (Ok (mkEffect (errno_ret 14) [] []) m' evs) := by
  sys_refute

/-- AT_NO_AUTOMOUNT (0x800) and 1 are bad words too.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- flags-bad -/
theorem fa2_other_bad_flags_are_einval (o : outcome SyscallEffect) :
    (syscall_spec (faccessat2_in [97] 0 2048) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [])
    ∧ (syscall_spec (faccessat2_in [97] 0 1) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model []) := by
  constructor <;> sys_norm

/-- A NEGATIVE flags word truncates to 0xffffffff, which is bad too.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- flags-bad -/
theorem fa2_negative_flags_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 18446744073709551615) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- …the 0 refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2#4:ret=0 -- flags-bad -/
theorem fa2_negative_flags_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 18446744073709551615) fa_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A closed dirfd AND a NULL pathname both lose to the flag word: -EINVAL,
nothing read.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- flags-first -/
theorem fa2_bad_flag_beats_dirfd_and_pathname (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in' 5 0 0 1024 (open_path_mem [97])) absent_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) absent_model [] := by
  sys_norm

/-- …the -EBADF refused: the dirfd never got a say…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-EBADF -- flags-first -/
theorem fa2_bad_flag_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in' 5 0 0 1024 (open_path_mem [97])) absent_model
        (Ok (mkEffect (errno_ret 9) [] []) m' evs) := by
  sys_refute

/-- …and the -EFAULT refused: the NULL pathname is never fetched, so the
answer the mutation forges carries no ledger…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2#1:ret=-EFAULT -- flags-first -/
theorem fa2_bad_flag_bare_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in' 5 0 0 1024 (open_path_mem [97])) absent_model
        (Ok (mkEffect (errno_ret 14) [] []) m' evs) := by
  sys_refute

/-- …and the -EFAULT a fetch-first kernel would answer, WITH the one-byte
ledger, is refused as well.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_bad_flag_efault_with_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in' 5 0 0 1024 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 14) [] [])) m' evs) := by
  sys_refute

/-- An absent name loses to the flag word: -EINVAL, not -ENOENT.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- flags-first -/
theorem fa2_bad_flag_beats_the_lookup (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 1024) absent_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) absent_model [] := by
  sys_norm

/-- The flag word is an `int`: 2^32 is a zero word and the present key
answers.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- flags-trunc -/
theorem fa2_flags_2_32_is_zero (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 4294967296) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- …-EINVAL refused on it, with the ledger the real read left…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2#1:ret=-EINVAL -- flags-trunc -/
theorem fa2_flags_2_32_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 4294967296) fa_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- …and without it: the -EINVAL arm is not reached by a zero word.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_flags_2_32_bare_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 4294967296) fa_model (Ok (mkEffect (errno_ret 22) [] []) m' evs) := by
  sys_refute

/-- 2^32 | AT_SYMLINK_FOLLOW truncates to a bad word: -EINVAL.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- flags-trunc -/
theorem fa2_flags_2_32_or_follow_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 4294968320) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- …the 0 refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2#2:ret=0 -- flags-trunc -/
theorem fa2_flags_2_32_or_follow_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 4294968320) fa_model (forged 0 2 m' evs) := by
  sys_refute

/-- 2^32 | AT_EACCESS truncates onto an accepted bit: the present key
answers.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- flags-trunc -/
theorem fa2_flags_2_32_or_eaccess_answers (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 4294967808) fa_model o ↔
      (access_env_errnos 2 fa_model o ∨ o = ret 0 2 fa_model) := by
  sys_norm

/-- …-EINVAL refused on it.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2#3:ret=-EINVAL -- flags-trunc -/
theorem fa2_flags_2_32_or_eaccess_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 4294967808) fa_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- The mode gate is still first on this arm: mode 8 with flags 0 is
-EINVAL, nothing read.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_bad_mode_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 8 0) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- A bad mode beside a bad flag word: one -EINVAL, and no user memory
read for it.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- mode-and-flags -/
theorem fa2_mode_and_flags_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 8 1024) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- …the two-byte ledger a fetch-first kernel would record refused on it:
the mode test precedes the pathname fetch (fs/open.c:475-476 and :493,
Linux v6.18.46).
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_mode_and_flags_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 8 1024) fa_model (forged_errno 22 2 m' evs) := by
  sys_refute

/-- …and the one-byte ledger `smuggle-copyin:a1:1` appends refused too.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:smuggle-copyin:a1:1 -- mode-and-flags -/
theorem fa2_mode_and_flags_smuggled_byte_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 8 1024) fa_model (forged_errno 22 1 m' evs) := by
  sys_refute

/-- WHY THE FLAG -EINVAL PRECEDES THE MODE DECLINE: R_OK beside a bad flag
word is a deterministic -EINVAL Linux decides without the permission
machinery, so the model answers it rather than declining.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_r_ok_with_a_bad_flag_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 4 1024) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-! ## The two declines after the gates: AT_EMPTY_PATH and a permission mode -/

/-- AT_EMPTY_PATH beside a name that is really there is `Unmodeled`: the
decline is written on the FLAG, not on the pathname.
rocq-twin: faccessat2_empty_path_flag_declined_either_way
probe: testing/syscall-check/tests/faccessat2_spec.c#fail-closed --expect-unmodeled faccessat2 -- empty-path-name -/
theorem fa2_empty_path_flag_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 4096) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the 0 Linux answers refused…
rocq-twin: faccessat2_empty_path_flag_declined_either_way
probe: testing/syscall-check/tests/faccessat2_spec.c#fail-closed --expect-unmodeled faccessat2 -- empty-path-name -/
theorem fa2_empty_path_flag_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 4096) fa_model (forged 0 2 m' evs) := by
  sys_refute

/-- …and the -ENOENT refused: the decline does not depend on what the
kernel said.
rocq-twin: faccessat2_empty_path_flag_declined_either_way
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_empty_path_flag_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 4096) fa_model (forged_errno 2 2 m' evs) := by
  sys_refute

/-- "" with AT_EMPTY_PATH resolves to the working directory on Linux, and is
`Unmodeled` here.
probe: testing/syscall-check/tests/faccessat2_spec.c#fail-closed --expect-unmodeled faccessat2 -- empty-path -/
theorem fa2_empty_path_flag_on_empty_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [] 0 4096) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …that 0 refused…
probe: testing/syscall-check/tests/faccessat2_spec.c#fail-closed --expect-unmodeled faccessat2 -- empty-path -/
theorem fa2_empty_path_flag_on_empty_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [] 0 4096) absent_model (forged 0 1 m' evs) := by
  sys_refute

/-- …and the -ENOENT the flag-less arm answers refused too.
probe: testing/syscall-check/tests/faccessat2_spec.c#fail-closed --expect-unmodeled faccessat2 -- empty-path -/
theorem fa2_empty_path_flag_on_empty_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [] 0 4096) absent_model (forged_errno 2 1 m' evs) := by
  sys_refute

/-- The decline precedes the pathname read: AT_EMPTY_PATH with a NULL
pointer is `Unmodeled`, not -EFAULT.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_empty_path_flag_reads_nothing (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in' 4294967196 0 0 4096 (open_path_mem [97])) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …but a bad flag BESIDE it is still -EINVAL: the decline is after the gate.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_empty_path_flag_with_a_bad_flag_is_einval (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 5120) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- AT_EMPTY_PATH with AT_EACCESS declines as well: the bit is declined in
any accepted company.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_empty_path_flag_with_eaccess_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 4608) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- R_OK with AT_EACCESS is `Unmodeled`: the map has no mode bits, whichever
ids the call asks about.
probe: testing/syscall-check/tests/faccessat2_spec.c#fail-closed --expect-unmodeled faccessat2 -- r-ok -/
theorem fa2_r_ok_eaccess_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 4 512) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the 0 refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#fail-closed --expect-unmodeled faccessat2 -- r-ok -/
theorem fa2_r_ok_eaccess_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 4 512) fa_model (forged 0 2 m' evs) := by
  sys_refute

/-- R_OK with flags 0 declines the same way.
kernel: fs/namei.c:inode_permission@v6.18.46 -/
theorem fa2_r_ok_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 4 0) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- On 439 too the permission-mode decline precedes the fetch: R_OK with a
NULL pathname and flags 0 is `Unmodeled`, not the -EFAULT Linux answers.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_r_ok_reads_nothing (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in' 4294967196 0 4 0 (open_path_mem [97])) absent_model o ↔
      o = Unmodeled := by
  sys_norm

/-- …that -EFAULT refused, with the one-byte ledger it would carry.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_r_ok_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in' 4294967196 0 4 0 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 14) [] [])) m' evs) := by
  sys_refute

/-- The AT_EMPTY_PATH decline comes BEFORE the mode decline; both are
`Unmodeled`, so the order is invisible in the answer, and this pin says only
that R_OK with AT_EMPTY_PATH is declined and not -EINVAL.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_r_ok_with_empty_path_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 4 4096) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the mode -EINVAL beats the AT_EMPTY_PATH decline: mode 8 beside
the bit alone is -EINVAL with nothing read, not `Unmodeled` — the mode test
is the function's first statement (fs/open.c:475-476, Linux v6.18.46), and
the bit's decline is the model's, after both gates.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_bad_mode_beats_the_empty_path_decline (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 8 4096) fa_model o ↔
      o = Ok (mkEffect (errno_ret 22) [] []) fa_model [] := by
  sys_norm

/-- …so it is not a decline: `Unmodeled` is refused, the concrete half of
the `iff` above.
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_bad_mode_with_empty_path_is_not_declined :
    ¬ syscall_spec (faccessat2_in [97] 8 4096) fa_model Unmodeled := by
  sys_refute

/-! ## The shared body, reached through the 439 arm -/

/-- The empty pathname without AT_EMPTY_PATH is -ENOENT, flags 0…
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- empty -/
theorem fa2_empty_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [] 0 0) absent_model o ↔ o = errno 2 1 absent_model := by
  sys_norm

/-- …a 0 refused…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=0 -- empty -/
theorem fa2_empty_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [] 0 0) absent_model (forged 0 1 m' evs) := by
  sys_refute

/-- …and under AT_EACCESS too.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- empty -/
theorem fa2_empty_eaccess_is_enoent (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [] 0 512) absent_model o ↔ o = errno 2 1 absent_model := by
  sys_norm

/-- …its 0 refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2#2:ret=0 -- empty -/
theorem fa2_empty_eaccess_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [] 0 512) absent_model (forged 0 1 m' evs) := by
  sys_refute

/-- …and the NUL that terminated it stays in the ledger.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:drop-copyins -- empty -/
theorem fa2_empty_without_the_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [] 0 0) absent_model (Ok (mkEffect (errno_ret 2) [] []) m' evs) := by
  sys_refute

/-- A NULL pathname with flags 0 is -EFAULT, one byte in the ledger.
probe: testing/syscall-check/tests/faccessat2_spec.c#conform -- fault-null -/
theorem fa2_null_pointer_is_efault (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in' 4294967196 0 0 0 (open_path_mem [97])) absent_model o ↔
      o = Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 14) [] [])) absent_model [] := by
  sys_norm

/-- …not -ENOENT…
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:ret=-ENOENT -- fault-null -/
theorem fa2_null_pointer_enoent_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in' 4294967196 0 0 0 (open_path_mem [97])) absent_model
        (Ok (with_copyins [(0, 1)] (mkEffect (errno_ret 2) [] [])) m' evs) := by
  sys_refute

/-- …and the attempted byte stays in the ledger.
probe: testing/syscall-check/tests/faccessat2_spec.c#reject --mutate faccessat2:drop-copyins -- fault-null -/
theorem fa2_null_pointer_without_the_ledger_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in' 4294967196 0 0 0 (open_path_mem [97])) absent_model
        (Ok (mkEffect (errno_ret 14) [] []) m' evs) := by
  sys_refute

/-- A closed dirfd (5) is `Unmodeled` on this arm too.
probe: testing/syscall-check/tests/faccessat2_spec.c#fail-closed --expect-unmodeled faccessat2 -- dirfd-bad -/
theorem fa2_dirfd_bad_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in' 5 8192 0 0 (open_path_mem [97])) fa_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the -EBADF refused.
probe: testing/syscall-check/tests/faccessat2_spec.c#fail-closed --expect-unmodeled faccessat2 -- dirfd-bad -/
theorem fa2_dirfd_bad_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in' 5 8192 0 0 (open_path_mem [97])) fa_model (forged_errno 9 2 m' evs) := by
  sys_refute

/-- The implied-directory decline reaches the 439 arm, under AT_EACCESS:
sharing `faccessat_body_spec` is what makes it hold.
rocq-twin: faccessat2_implied_directory_unmodeled -/
theorem fa2_implied_directory_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 512) fa_under_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the 0 Rocq's case offers refused.
rocq-twin: faccessat2_implied_directory_unmodeled -/
theorem fa2_implied_directory_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (faccessat2_in [97] 0 512) fa_under_model (forged 0 2 m' evs) := by
  sys_refute

/-- The byte-prefix contrast reaches it too: a present "a" is answered 0
(fs/open.c:509, Linux v6.18.46).
kernel: fs/open.c:do_faccessat@v6.18.46 -/
theorem fa2_byte_prefix_is_not_a_directory (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97] 0 512) fa_sibling_model o ↔
      (access_env_errnos 2 fa_sibling_model o ∨ o = ret 0 2 fa_sibling_model) := by
  sys_norm

/-- A separator declines on this arm as well.
kernel: fs/namei.c:link_path_walk@v6.18.46 -/
theorem fa2_slash_declines (o : outcome SyscallEffect) :
    syscall_spec (faccessat2_in [97, 47, 98] 0 256) absent_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and so does a 256-byte component, under AT_SYMLINK_NOFOLLOW: the
-ENAMETOOLONG is `simple_lookup`'s (fs/libfs.c:71-72, Linux v6.18.46),
reached through `__lookup_slow` (fs/namei.c:1816, Linux v6.18.46).
kernel: fs/libfs.c:simple_lookup@v6.18.46 -/
theorem fa2_name_max_256_declines (i : SyscallInput) (p : path)
    (hp : read_cstr i.in_mem 8192 = CstrOk p) (hlen : p.length = 256)
    (hs : path_has_slash p = false) (o : outcome SyscallEffect) :
    faccessat2_spec 4294967196 8192 0 256 i absent_model o ↔ o = Unmodeled := by
  have hne : path_eqb p [] = false :=
    path_eqb_false_of_ne p [] (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hd1 : path_eqb p dot_path = false :=
    path_eqb_false_of_ne p dot_path (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hd2 : path_eqb p dotdot_path = false :=
    path_eqb_false_of_ne p dotdot_path (by intro h; rw [h] at hlen; exact absurd hlen (by decide))
  have hu : fs_under [] p = false := rfl
  sys_simp_pass +decide
  simp only [hp, hne, hd1, hd2, hs, hlen, hu]
  sys_norm

/-- A pathname with no NUL within PATH_MAX is -ENAMETOOLONG on this arm,
with the flag word accepted first.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem fa2_too_long_is_enametoolong (i : SyscallInput) (hp : read_cstr i.in_mem 8192 = CstrTooLong)
    (o : outcome SyscallEffect) :
    faccessat2_spec 4294967196 8192 0 512 i absent_model o ↔
      o = Ok (with_copyins [(8192, cstr_access_len_aux i.in_mem 8192 path_max)]
               (mkEffect (errno_ret 36) [] [])) absent_model [] := by
  sys_simp_pass +decide
  simp only [hp]
  sys_norm

/-! # Part two: `close` (57)

Worked examples over `Sys.Fs.Open.close_spec`.  Line numbers are Linux
v6.18.46 (commit 1f99e9ab748f) throughout.

HOW THESE ARE STATED.  The arm is called directly, `close_spec fd i
close_model o`, over one fixture holding a descriptor of every kind but
`FdFileRW`; the dispatcher pins at the end go through
`syscall_spec` on a `SyscallInput` numbered 57, so the table's `fd32`
narrowing is under test with the arm.  Each decision is pinned twice, an
`iff` over every outcome and a refutation of the answer a wrong model or a
lying kernel would give, as the openat part does.

THE KERNEL'S ORDER.  `SYSCALL_DEFINE1(close, unsigned int, fd)`
(fs/open.c:1574-1602, Linux v6.18.46) calls `file_close_fd` (fs/file.c:850-860, Linux v6.18.46),
which under the table lock calls `file_close_fd_locked` (fs/file.c:692-709, Linux v6.18.46):
NULL for a number at or past `max_fds` (:699-700) or with no file
installed (:703-704), otherwise the slot is cleared (:705) and
`__put_unused_fd` (fs/file.c:626-632, Linux v6.18.46) lowers `next_fd` to it when
it was above (:630-631).  NULL is the -EBADF of fs/open.c:1580-1581 (Linux v6.18.46), and it is
the ONLY errno the model can answer: `filp_flush` (fs/open.c:1538-1556, Linux v6.18.46) returns what
`f_op->flush` answers (:1548-1549) and its initial 0 otherwise (:1540,
:1555); none of the file-operations tables listed on `close_spec`'s
docstring defines a flush, and `ovl_flush` (fs/overlayfs/file.c:645-662,
Linux v6.18.46), the forwarding flush an overlay puts in front of them,
returns 0 over them (the docstring says what the 0 rests on), so the
`retval == 0` branch at fs/open.c:1591-1592 returns 0 and the -EINTR
mapping at :1594-1599 is never reached.  The slot is cleared BEFORE the flush and the
`fput_close_sync` (fs/file_table.c:607-611, Linux v6.18.46), which is why a second
close of the number is -EBADF whatever the first answered (the kernel's
own comment at fs/open.c:1594, Linux v6.18.46).

THE PIPE ENDS.  Closing one end of a pipe runs `pipe_release`
(fs/pipe.c:725-746, Linux v6.18.46): a reader or writer count is lowered (:730-733)
and `put_pipe_info` (fs/pipe.c:709-722, Linux v6.18.46) frees the pipe only when its
last FILE goes (:714).  The model keeps its pipe-table entry — the spec
rewrites the fd table alone, which `Checks/Cases/State.lean` pins as
`pipe_table_survives_fd_remove` — and the live counters are
`State.pipe_end_live` over the fd table, so the pins here fix that the
buffer survives and that only the closed end dies. -/

/-! ## The fixture and its readings

`close_fds` holds one descriptor of every kind: the three channels, a
read-only file (3) and a write-only one (4) over `close_fs`, a directory
(5), a fresh socket (6), both ends of pipe 0 (7 reads, 8 writes) over a
two-byte buffer, /dev/null opened read-write (9) and /dev/urandom (11);
10 stays closed for the -EBADF pins.  Each `close_fds_less_<fd>` is the
same table with that one entry gone, spelled out rather than computed, so
a pin's right-hand side states the table the kernel leaves and not the
function the spec applies; `after_close_<fd>` is the fixture over it.  The
models unfold at `low`, as the openat part's do; the closed `fd_lookup`
facts are registered at the default priority so the first pass decides the
`match` before the alternatives are read, and the closed `fd_remove` facts
beside them fold the post-state `fd_remove close_fds n` onto the table the
pin names, pinning each spelled table to the removal it claims to be.  A
refutation whose forged outcome differs from the admitted one in the fd
TABLE is stated on the hypothesis (`intro h; sys_refute at h`), for the
reason `Checks/Cases/Fs/File.lean`'s `dup_success_without_the_copy_rejected`
gives. -/

/-- One descriptor of every kind; 10 is closed. -/
def close_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (5, .FdDir), (6, .FdSocket .SkFresh),
    (7, .FdPipe 0 false), (8, .FdPipe 0 true), (9, .FdDevNull true true),
    (11, .FdUrandom) ]

/-- Pipe 0 holds two bytes, "hi". -/
def close_pipes : List (word × PipeBuf) := [(0, ([104, 105], 2))]

/-- The files behind descriptors 3 and 4. -/
def close_fs : Fs.Fs := [([102], [120]), ([103], [121])]

def close_model : Model := fixture_of (fds := close_fds) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 0. -/
def close_fds_less_0 : List (word × FdEntry) :=
  [ (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (5, .FdDir), (6, .FdSocket .SkFresh),
    (7, .FdPipe 0 false), (8, .FdPipe 0 true), (9, .FdDevNull true true),
    (11, .FdUrandom) ]
def after_close_0 : Model :=
  fixture_of (fds := close_fds_less_0) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 2. -/
def close_fds_less_2 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (3, .FdFile [102] 7), (4, .FdFileW [103] 9),
    (5, .FdDir), (6, .FdSocket .SkFresh), (7, .FdPipe 0 false), (8, .FdPipe 0 true),
    (9, .FdDevNull true true), (11, .FdUrandom) ]
def after_close_2 : Model :=
  fixture_of (fds := close_fds_less_2) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 3. -/
def close_fds_less_3 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (4, .FdFileW [103] 9),
    (5, .FdDir), (6, .FdSocket .SkFresh), (7, .FdPipe 0 false),
    (8, .FdPipe 0 true), (9, .FdDevNull true true), (11, .FdUrandom) ]
def after_close_3 : Model :=
  fixture_of (fds := close_fds_less_3) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 4. -/
def close_fds_less_4 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (5, .FdDir), (6, .FdSocket .SkFresh), (7, .FdPipe 0 false),
    (8, .FdPipe 0 true), (9, .FdDevNull true true), (11, .FdUrandom) ]
def after_close_4 : Model :=
  fixture_of (fds := close_fds_less_4) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 5. -/
def close_fds_less_5 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (6, .FdSocket .SkFresh), (7, .FdPipe 0 false),
    (8, .FdPipe 0 true), (9, .FdDevNull true true), (11, .FdUrandom) ]
def after_close_5 : Model :=
  fixture_of (fds := close_fds_less_5) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 6. -/
def close_fds_less_6 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (5, .FdDir), (7, .FdPipe 0 false), (8, .FdPipe 0 true),
    (9, .FdDevNull true true), (11, .FdUrandom) ]
def after_close_6 : Model :=
  fixture_of (fds := close_fds_less_6) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 7. -/
def close_fds_less_7 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (5, .FdDir), (6, .FdSocket .SkFresh),
    (8, .FdPipe 0 true), (9, .FdDevNull true true), (11, .FdUrandom) ]
def after_close_7 : Model :=
  fixture_of (fds := close_fds_less_7) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 8. -/
def close_fds_less_8 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (5, .FdDir), (6, .FdSocket .SkFresh),
    (7, .FdPipe 0 false), (9, .FdDevNull true true), (11, .FdUrandom) ]
def after_close_8 : Model :=
  fixture_of (fds := close_fds_less_8) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 9. -/
def close_fds_less_9 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (5, .FdDir), (6, .FdSocket .SkFresh),
    (7, .FdPipe 0 false), (8, .FdPipe 0 true), (11, .FdUrandom) ]
def after_close_9 : Model :=
  fixture_of (fds := close_fds_less_9) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without descriptor 11. -/
def close_fds_less_11 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (5, .FdDir), (6, .FdSocket .SkFresh),
    (7, .FdPipe 0 false), (8, .FdPipe 0 true), (9, .FdDevNull true true) ]
def after_close_11 : Model :=
  fixture_of (fds := close_fds_less_11) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without either end of pipe 0: what a close of one end must
NOT leave, and what closing the second end after the first does. -/
def close_fds_less_7_8 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (5, .FdDir), (6, .FdSocket .SkFresh),
    (9, .FdDevNull true true), (11, .FdUrandom) ]
/-- The fixture after both ends of pipe 0 are closed, one after the other. -/
def after_close_7_8 : Model :=
  fixture_of (fds := close_fds_less_7_8) (pipes := close_pipes) (fs := close_fs)

/-- `close_fds` without 3 AND its neighbour 4: what a close of 3 must NOT leave. -/
def close_fds_less_3_4 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
    (5, .FdDir), (6, .FdSocket .SkFresh),
    (7, .FdPipe 0 false), (8, .FdPipe 0 true), (9, .FdDevNull true true),
    (11, .FdUrandom) ]

attribute [sys_simp low]
  close_model.eq_1
  after_close_0.eq_1 after_close_2.eq_1 after_close_3.eq_1 after_close_4.eq_1 after_close_5.eq_1 after_close_6.eq_1 after_close_7.eq_1 after_close_8.eq_1 after_close_9.eq_1 after_close_11.eq_1
  after_close_7_8.eq_1

-- Sys/Fs/Open.lean: the spec's unfolding, at the priority every spec has.
attribute [sys_simp low] close_spec.eq_1

/-! ### The closed readings the first pass needs -/
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_0 : fd_lookup close_fds 0 = some (.FdChannel 0) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_2 : fd_lookup close_fds 2 = some (.FdChannel 2) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_3 : fd_lookup close_fds 3 = some (.FdFile [102] 7) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_4 : fd_lookup close_fds 4 = some (.FdFileW [103] 9) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_5 : fd_lookup close_fds 5 = some (.FdDir) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_6 : fd_lookup close_fds 6 = some (.FdSocket .SkFresh) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_7 : fd_lookup close_fds 7 = some (.FdPipe 0 false) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_8 : fd_lookup close_fds 8 = some (.FdPipe 0 true) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_9 : fd_lookup close_fds 9 = some (.FdDevNull true true) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_11 : fd_lookup close_fds 11 = some (.FdUrandom) := rfl
/-- The closed number.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_10 : fd_lookup close_fds 10 = none := rfl
/-- The number `close(-1)` narrows to, past every table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_4294967295 : fd_lookup close_fds 4294967295 = none := rfl
/-- The signed-int boundary, 2^31, past every table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_2147483648 : fd_lookup close_fds 2147483648 = none := rfl
/-- INT_MAX, 2^31 - 1, past every table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_close_2147483647 : fd_lookup close_fds 2147483647 = none := rfl
/-- The write end, looked up after the read end's close.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_less_7_8 : fd_lookup close_fds_less_7 8 = some (.FdPipe 0 true) := rfl
/-- The table after the second removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_less_7_8 : fd_remove close_fds_less_7 8 = close_fds_less_7_8 := rfl
/-- The closed descriptor, looked up again after its close.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_less_3_3 : fd_lookup close_fds_less_3 3 = none := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_0 : fd_remove close_fds 0 = close_fds_less_0 := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_2 : fd_remove close_fds 2 = close_fds_less_2 := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_3 : fd_remove close_fds 3 = close_fds_less_3 := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_4 : fd_remove close_fds 4 = close_fds_less_4 := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_5 : fd_remove close_fds 5 = close_fds_less_5 := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_6 : fd_remove close_fds 6 = close_fds_less_6 := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_7 : fd_remove close_fds 7 = close_fds_less_7 := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_8 : fd_remove close_fds 8 = close_fds_less_8 := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_9 : fd_remove close_fds 9 = close_fds_less_9 := rfl
/-- The table after one removal, closed.
model: a closed `fd_remove` at a numeral, a rewrite for `sys_norm`. -/
theorem remove_close_11 : fd_remove close_fds 11 = close_fds_less_11 := rfl

attribute [sys_simp]
  lookup_close_0 lookup_close_2 lookup_close_3 lookup_close_4 lookup_close_5 lookup_close_6 lookup_close_7 lookup_close_8 lookup_close_9 lookup_close_11 lookup_close_10
  lookup_close_4294967295 lookup_close_2147483648 lookup_close_2147483647 lookup_less_3_3 lookup_less_7_8
  remove_less_7_8 remove_close_0 remove_close_2 remove_close_3 remove_close_4 remove_close_5 remove_close_6 remove_close_7 remove_close_8 remove_close_9 remove_close_11

/-! ## `file_close_fd_locked`: the number is resolved first

`close` (fs/open.c:1574-1602, Linux v6.18.46) asks `file_close_fd` for the file at
`fd` (:1579) and returns -EBADF on NULL (:1580-1581) before anything else
is read; `file_close_fd_locked` (fs/file.c:692-709, Linux v6.18.46) answers NULL for a
number at or past `max_fds` (:699-700) and for a slot with no file
(:703-704).  So a number with no open file is -EBADF whatever kind of
object a neighbouring number names, and the -EBADF path clears nothing:
the slot is cleared inside `if (file)` (:704-707). -/

/-- A number with no file installed is -EBADF, and nothing else: not 0,
not a decline.
kernel: fs/open.c:close; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem closed_fd_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 10 i close_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) close_model [] := by
  sys_norm

/-- A closed number never answers 0: the NULL test at fs/open.c:1580 comes
before the flush and the return of 0 at :1591-1592.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem closed_fd_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 10 i close_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …and the -EBADF path touches no other slot: a model that dropped the
neighbouring descriptor 11 on the way to its errno is refused
(`file_close_fd_locked` clears a slot only inside `if (file)`,
fs/file.c:704-707).
kernel: fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem closed_fd_leaves_the_table (i : SyscallInput) (evs : List event) :
    ¬ close_spec 10 i close_model
        (Ok (mkEffect (errno_ret EBADF) [] []) after_close_11 evs) := by
  intro h
  sys_refute at h

/-- `close(-1)`: the register narrows to 4294967295, at or past every
`max_fds` (`file_close_fd_locked`, fs/file.c:699-700), so it is the same
-EBADF as a free slot's.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem close_of_minus_one_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 4294967295 i close_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) close_model [] := by
  sys_norm

/-- A model that read the fd as signed and answered -EINVAL on a negative
one is refused: the argument is `unsigned int`, and the only test on it is
the bound at fs/file.c:699-700.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem close_of_minus_one_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 4294967295 i close_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- 2^31, the number a signed reading would flip on, is -EBADF the same
way: `fd` is `unsigned int` and the bound at fs/file.c:699-700 is the
only test.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem close_of_2_pow_31_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 2147483648 i close_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) close_model [] := by
  sys_norm

/-- `close(INT_MAX)`: 2^31 - 1 is the largest number a C `int` fd can
hold, and it is past every table on this kernel — `sysctl_nr_open_max`
(fs/file.c:100-101, Linux v6.18.46) caps `nr_open`, and with it `max_fds`,
at `INT_MAX & -BITS_PER_LONG`, below it — so the bound at fs/file.c:699-700
answers -EBADF.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem close_of_int_max_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 2147483647 i close_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) close_model [] := by
  sys_norm

/-! ## Every open descriptor closes to 0, and the arm is kind-blind

Once `file_close_fd` has handed back a file, the return value is what
`filp_flush` hands back: `SYSCALL_DEFINE1(close, unsigned int, fd)`
(fs/open.c:1574-1602, Linux v6.18.46) assigns it at :1583, and
`filp_flush` (fs/open.c:1538-1556, Linux v6.18.46)
returns 0 unless the file's `f_op->flush` says otherwise (:1548-1549).
None of the tables listed here defines one — `ext4_file_operations`
(fs/ext4/file.c, Linux v6.18.46) and `shmem_file_operations` (mm/shmem.c, Linux v6.18.46)
for the regular files, `ext4_dir_operations` (fs/ext4/dir.c, Linux v6.18.46) and
`simple_offset_dir_operations` (fs/libfs.c, Linux v6.18.46) for the directories,
`pipeanon_fops` (fs/pipe.c:1257-1266, Linux v6.18.46) for the pipe ends — and
for the three channels as the VM harness hands them to a probe, which are
`pipe2` pipes (`testing/vm/tracer.c`'s `make_pipe`) — `socket_file_ops`
(net/socket.c), `null_fops` (drivers/char/mem.c) and `urandom_fops`
(drivers/char/random.c), all Linux v6.18.46 — so fs/open.c:1591-1592
returns 0 for every kind on them.  The forwarding flush an overlay puts in
front of them, `ovl_flush` (fs/overlayfs/file.c:645-662, Linux v6.18.46;
`.flush = ovl_flush` at :674 of `ovl_file_operations`, :664), returns the
lower file's answer or its initial 0 (:649, :655-661): still 0.  What a
flush that can fail would do, and the premise about the run's filesystem
the 0 rests on, is on `close_spec`'s docstring.  What the kind decides is
the file's own release, which runs from the `fput_close_sync`
(fs/file_table.c:607-611, Linux v6.18.46) call at fs/open.c:1589 after the
return value is fixed, when the descriptor held the file's last reference,
and, for every kind but a pipe end, changes nothing the model records. -/

/-- The stdio channel closes to 0 and leaves the table.
kernel: fs/open.c:close,filp_flush; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem channel_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 0 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_0 [] := by
  sys_norm

/-- A model that kept the standard descriptors unclosable — answering
-EBADF on stdin — is refused: fd 0 is a slot like any other to
`file_close_fd_locked`.
kernel: fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem channel_close_is_not_ebadf (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 0 i close_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- stderr closes the same way: the channel number is not read by the
arm, and 0, 1 and 2 are three slots of one table.
kernel: fs/open.c:close,filp_flush; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem stderr_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 2 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_2 [] := by
  sys_norm

/-- A read-only regular file closes to 0 and leaves the table.
kernel: fs/open.c:close,filp_flush; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem readonly_file_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 3 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_3 [] := by
  sys_norm

/-- The entry goes: a model that answered 0 and kept the descriptor is
refused (fs/file.c:705 clears the slot).
kernel: fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem file_close_removes_the_entry (i : SyscallInput) (evs : List event) :
    ¬ close_spec 3 i close_model (Ok (mkEffect 0 [] []) close_model evs) := by
  intro h
  sys_refute at h

/-- …and only that entry: a model that cleared the neighbouring slot 4
instead is refused.
kernel: fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem file_close_removes_only_its_entry (i : SyscallInput) (evs : List event) :
    ¬ close_spec 3 i close_model (Ok (mkEffect 0 [] []) after_close_4 evs) := by
  intro h
  sys_refute at h

/-- …and nothing beside it: a model that cleared 3 and its neighbour 4
together is refused — the forged table differs from the admitted one in
that one extra removal, so this is the over-removal the previous pin's
forgery (3 kept, 4 gone) does not isolate.  `file_close_fd_locked` clears
the one slot it was handed (fs/file.c:705).
kernel: fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem file_close_removes_nothing_else (i : SyscallInput) (evs : List event) :
    ¬ close_spec 3 i close_model
        (Ok (mkEffect 0 [] [])
          (fixture_of (fds := close_fds_less_3_4) (pipes := close_pipes) (fs := close_fs)) evs) := by
  intro h
  sys_refute at h

/-- The restart-to--EINTR mapping (fs/open.c:1594-1599) needs a nonzero
`retval` from `filp_flush`, which no modeled kind's flush can produce; a
kernel answering -EINTR on a regular file is refused.
kernel: fs/open.c:close,filp_flush@v6.18.46 -/
theorem file_close_is_not_eintr (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 3 i close_model (Ok (mkEffect (errno_ret EINTR) [] []) m' evs) := by
  sys_refute

/-- A write-only regular file closes to 0 the same way.  The file's bytes
are unchanged — `close` writes nothing back, the data went to the page
cache at `write` time — and the model's image keeps both files.
kernel: fs/open.c:close,filp_flush; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem write_file_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 4 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_4 [] := by
  sys_norm

/-- The image is not touched: a model that dropped the closed file from the
file system is refused.
kernel: fs/open.c:close,filp_flush@v6.18.46 -/
theorem write_file_close_keeps_the_image (i : SyscallInput) (evs : List event) :
    ¬ close_spec 4 i close_model
        (Ok (mkEffect 0 [] [])
          (fixture_of (fds := close_fds_less_4) (pipes := close_pipes) (fs := [([102], [120])]))
          evs) := by
  sys_refute

/-- Success is inert on user memory: `close` takes an int and returns one,
and nothing under it copies to user space.  A kernel reporting a write is
refused.
kernel: fs/open.c:close@v6.18.46 -/
theorem close_writes_nothing (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 4 i close_model (Ok (mkEffect 0 [(4096, [0])] []) m' evs) := by
  sys_refute

/-- Success emits no event: nothing a channel would carry is written.
kernel: fs/open.c:close@v6.18.46 -/
theorem close_emits_nothing (i : SyscallInput) (m' : Model) :
    ¬ close_spec 4 i close_model (Ok (mkEffect 0 [] []) m' [event.WriteEv 1 0]) := by
  sys_refute

/-- Success records no copy-in: `close` reads no user memory, so a ledger
entry — the shape a pathname fetch leaves — is refused.
kernel: fs/open.c:close@v6.18.46 -/
theorem close_records_no_copyin (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 4 i close_model (Ok (with_copyins [(4096, 1)] (mkEffect 0 [] [])) m' evs) := by
  sys_refute

/-- A directory descriptor closes to 0 and leaves the table; dirfd_spec's
`close` case is this call on a real ".".
probe: testing/syscall-check/tests/dirfd_spec.c#conform -- close -/
theorem dir_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 5 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_5 [] := by
  sys_norm

/-- The directory's read errno is not its close answer: -EISDIR is
what `generic_read_dir` (fs/libfs.c:224-227, Linux v6.18.46) returns as the
directory tables' `.read`, reached through `vfs_read` (fs/read_write.c, Linux v6.18.46); `close` asks
the file for nothing but its flush.
kernel: fs/open.c:close,filp_flush@v6.18.46 -/
theorem dir_close_is_not_eisdir (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 5 i close_model (Ok (mkEffect (errno_ret EISDIR) [] []) m' evs) := by
  sys_refute

/-- A socket closes to 0 and leaves the table.  The socket's own teardown
is `sock_close` (net/socket.c, Linux v6.18.46), its release, which runs from the
`fput_close_sync` (fs/file_table.c:607-611, Linux v6.18.46) call at fs/open.c:1589
after the return value is fixed, on the file's last reference (this
descriptor is its only one).
kernel: fs/open.c:close,filp_flush; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem socket_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 6 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_6 [] := by
  sys_norm

/-- -ENOTSOCK is the socket calls' errno on a descriptor that is not a
socket; `close` has no such test in either direction, and the mutated run
that claims it is refused.
probe: testing/syscall-check/tests/socket_rw.c#reject --mutate close#1:ret=-ENOTSOCK -- rw -/
theorem socket_close_is_not_enotsock (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 6 i close_model (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- The read end of a pipe closes to 0 and the pipe's bytes stay:
`pipe_release` (fs/pipe.c:725-746, Linux v6.18.46) lowers `readers` (:730-731), and
`put_pipe_info` (fs/pipe.c:709-722, Linux v6.18.46) frees nothing while the write
end's file still counts in `pipe->files` (:714).
kernel: fs/open.c:close; fs/pipe.c:pipe_release,put_pipe_info@v6.18.46 -/
theorem pipe_read_end_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 7 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_7 [] := by
  sys_norm

/-- A model that dropped the buffer with the read end is refused: the pipe
outlives the descriptor until its last file goes (fs/pipe.c:714).
kernel: fs/pipe.c:pipe_release,put_pipe_info@v6.18.46 -/
theorem pipe_read_end_close_keeps_the_buffer (i : SyscallInput) (evs : List event) :
    ¬ close_spec 7 i close_model
        (Ok (mkEffect 0 [] [])
          (fixture_of (fds := close_fds_less_7) (pipes := []) (fs := close_fs)) evs) := by
  sys_refute

/-- What dies is the read end alone: over the table the spec leaves,
`pipe_end_live` reports no reader and a live writer on pipe 0 — the
counters `pipe_release` lowers one at a time (fs/pipe.c:730-733), read
off the fd table.
kernel: fs/pipe.c:pipe_release@v6.18.46 -/
theorem pipe_read_end_close_kills_only_the_reader :
    pipe_end_live close_fds_less_7 0 false = false ∧
    pipe_end_live close_fds_less_7 0 true = true := by
  decide

/-- The write end of a pipe closes to 0 the same way.
kernel: fs/open.c:close; fs/pipe.c:pipe_release,put_pipe_info@v6.18.46 -/
theorem pipe_write_end_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 8 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_8 [] := by
  sys_norm

/-- Closing the write end does not close the read end: a model that dropped
both descriptors of pipe 0 is refused — `pipe_release` lowers one counter
per `f_mode` bit (fs/pipe.c:730-733) and `file_close_fd_locked` clears one
slot.
kernel: fs/pipe.c:pipe_release; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem pipe_write_end_close_spares_the_reader (i : SyscallInput) (evs : List event) :
    ¬ close_spec 8 i close_model
        (Ok (mkEffect 0 [] [])
          (fixture_of (fds := close_fds_less_7_8) (pipes := close_pipes) (fs := close_fs)) evs) := by
  intro h
  sys_refute at h

/-- …and over the table it leaves, the writer is dead and the reader live:
the state a later read of 7 finds as end-of-file once the buffer drains.
kernel: fs/pipe.c:pipe_release@v6.18.46 -/
theorem pipe_write_end_close_kills_only_the_writer :
    pipe_end_live close_fds_less_8 0 true = false ∧
    pipe_end_live close_fds_less_8 0 false = true := by
  decide

/-- The LAST end: with 7 already closed, `close(8)` is 0 too and the
pipe-table entry stays.  Here Linux frees the pipe — `put_pipe_info`
(fs/pipe.c:709-722, Linux v6.18.46) sees `!--pipe->files` (:714) on the
second release — while the model keeps an entry no descriptor reaches; the
argument that no program tells the two apart is on `State/Pipes.lean`'s
`pipe_new_id`.
kernel: fs/open.c:close; fs/pipe.c:pipe_release,put_pipe_info@v6.18.46 -/
theorem pipe_last_end_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 8 i after_close_7 o ↔ o = Ok (mkEffect 0 [] []) after_close_7_8 [] := by
  sys_norm

/-- …and a model that mirrored the freeing, dropping pipe 0's entry when
its last end went, is refused: the spec rewrites the fd table alone, as
Rocq's does, and the entry stays whichever end goes last.
kernel: fs/pipe.c:put_pipe_info@v6.18.46 -/
theorem pipe_last_end_close_keeps_the_table (i : SyscallInput) (evs : List event) :
    ¬ close_spec 8 i after_close_7
        (Ok (mkEffect 0 [] []) (fixture_of (fds := close_fds_less_7_8) (fs := close_fs)) evs) := by
  intro h
  sys_refute at h

/-- /dev/null closes to 0 and leaves the table.
kernel: fs/open.c:close,filp_flush; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem devnull_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 9 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_9 [] := by
  sys_norm

/-- Rocq's `devnull_open_write_read_close`, close leg: the descriptor the
open minted at 3 (write-only) is closed, and the model is the one the open
started from — on which the openat part's `plain_create_mints_the_key`
mints 3 again, since `__put_unused_fd` (fs/file.c:630-631, Linux v6.18.46) lowered
`next_fd` to the freed number.
rocq-twin: devnull_open_write_read_close
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked,__put_unused_fd@v6.18.46 -/
theorem devnull_close_restores_the_model (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 3 i (fixture_of (fds := (3, .FdDevNull false true) :: init_fds)) o ↔
      o = Ok (mkEffect 0 [] []) absent_model [] := by
  sys_norm

/-- …and the slot is not kept: a model whose close answered 0 and left the
descriptor in place is refused — a corollary of the leg's equality, which
Rocq states and does not refute.
kernel: fs/file.c:file_close_fd_locked,__put_unused_fd@v6.18.46 -/
theorem devnull_close_frees_the_slot (i : SyscallInput) (evs : List event) :
    ¬ close_spec 3 i (fixture_of (fds := (3, .FdDevNull false true) :: init_fds))
        (Ok (mkEffect 0 [] []) (fixture_of (fds := (3, .FdDevNull false true) :: init_fds)) evs) := by
  sys_refute

/-- /dev/urandom closes to 0 and leaves the table.
kernel: fs/open.c:close,filp_flush; fs/file.c:file_close_fd,file_close_fd_locked@v6.18.46 -/
theorem urandom_close_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 11 i close_model o ↔ o = Ok (mkEffect 0 [] []) after_close_11 [] := by
  sys_norm

/-- A model that answered -EBADF on the device — treating a descriptor
with no offset as no descriptor — is refused.
kernel: fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem urandom_close_is_not_ebadf (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 11 i close_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- Rocq's `urandom_open_read_close`, close leg: the reader minted at 3 is
closed and the model is the one the open started from; the declared
stream is the run's, not the descriptor's, and comes through untouched.
Rocq's run declares sixteen bytes; `s` here is any stream, `fixture_of`
having no slot for one.
rocq-twin: urandom_open_read_close
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked,__put_unused_fd@v6.18.46 -/
theorem urandom_close_restores_the_model (s : InputStream) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    close_spec 3 i (with_urandom s (fixture_of (fds := (3, .FdUrandom) :: init_fds))) o ↔
      o = Ok (mkEffect 0 [] []) (with_urandom s absent_model) [] := by
  sys_norm

/-- …and a model that emptied the declared stream with the descriptor is
refused: the bytes are the device's, and `file_close_fd_locked` touches
the fd table alone (fs/file.c:705).  The forged outcome's stream is at end
of input, the admitted one's still holds `b`.

THE FORGED MODEL SPELLS THE EMPTY STREAM OUT, and it has to since
`Run.valid_urandom`: `fixture_of`'s own slot is `default_urandom`, which
is endless, so `absent_model` alone would no longer be a model whose
stream ended — it would be one whose stream is a different endless one,
and at `b = 0`, `s = default_urandom` the two would agree.  Writing
`with_urandom IEof` keeps this case about EMPTYING the stream, which is
what the prose above claims.
rocq-twin: urandom_open_read_close
kernel: fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem urandom_close_keeps_the_stream (b : byte) (s : InputStream) (i : SyscallInput)
    (evs : List event) :
    ¬ close_spec 3 i (with_urandom (ICons b s) (fixture_of (fds := (3, .FdUrandom) :: init_fds)))
        (Ok (mkEffect 0 [] []) (with_urandom IEof absent_model) evs) := by
  intro h
  sys_norm at h
  exact IEof_ne_ICons b s h.1

/-! ## The slot is freed for good, and reused lowest-first

`file_close_fd_locked` clears the slot before the flush (fs/file.c:705, Linux v6.18.46)
and `__put_unused_fd` lowers `next_fd` to it when it was above
(fs/file.c:630-631, Linux v6.18.46), and `alloc_fd` (fs/file.c:570, Linux v6.18.46) finds
the lowest free bit from there.  Two consequences, both
pinned: a second close of the number is -EBADF, and the next open lands on
it. -/

/-- The second close of a number is -EBADF: the table `close(3)` leaves
has no file at 3 (fs/file.c:705, and the kernel's comment at
fs/open.c:1594).
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem second_close_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 3 i after_close_3 o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) after_close_3 [] := by
  sys_norm

/-- …never 0 again.
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem second_close_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ close_spec 3 i after_close_3 (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- dirfd_spec's `close-reopen`: "." opened at 3, closed, and reopened at
3.  The close leg leaves the model the open started from, on which every
open of the openat part mints 3 (`plain_create_mints_the_key` is one).
probe: testing/syscall-check/tests/dirfd_spec.c#conform -- close-reopen -/
theorem dir_close_frees_the_lowest_slot (i : SyscallInput) (o : outcome SyscallEffect) :
    close_spec 3 i (fixture_of (fds := (3, .FdDir) :: init_fds)) o ↔
      o = Ok (mkEffect 0 [] []) absent_model [] := by
  sys_norm

/-- A model whose close left the slot occupied — so the reopen would land
at 4 — is refused.
kernel: fs/file.c:file_close_fd_locked,__put_unused_fd@v6.18.46 -/
theorem dir_close_slot_kept_rejected (i : SyscallInput) (evs : List event) :
    ¬ close_spec 3 i (fixture_of (fds := (3, .FdDir) :: init_fds))
        (Ok (mkEffect 0 [] []) (fixture_of (fds := (3, .FdDir) :: init_fds)) evs) := by
  sys_refute

/-! ## No arm declines -/

/-- Every descriptor kind is answered, and so is a number that names none:
`close` has two outcomes and the model has both, over ANY model and fd.
Both are symbolic, so the lookup is case-split by hand before the
normalizer reads each arm (`sys_norm` reads a spec whose gates are
decided, and a `match` on an open lookup is not one).
kernel: fs/open.c:close; fs/file.c:file_close_fd_locked@v6.18.46 -/
theorem close_never_unmodeled (m : Model) (fd : word) (i : SyscallInput) :
    ¬ close_spec fd i m Unmodeled := by
  intro h
  unfold close_spec at h
  rw [bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none => sys_refute at h
  | some e => sys_refute at h

/-! ## The dispatcher: syscall 57 and its 32-bit fd

`SYSCALL_DEFINE1(close, unsigned int, fd)` (fs/open.c:1574): the fd is
`unsigned int`, narrowed by `__SYSCALL_DEFINEx`
(arch/riscv/include/asm/syscall_wrapper.h:82-88, Linux v6.18.46) through
`__SC_CAST` (include/linux/syscalls.h:132, Linux v6.18.46), which the
table's `fd32` mirrors. -/

/-- Syscall 57 on fd 3 reaches the arm and closes the read-only file.
kernel: include/uapi/asm-generic/unistd.h:__NR_close; fs/open.c:close@v6.18.46 -/
theorem sysno_57_is_close (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 57 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        close_model o
      ↔ o = Ok (mkEffect 0 [] []) after_close_3 [] := by
  sys_norm

/-- Syscall 57 on the closed number 10 is -EBADF through the table too.
kernel: include/uapi/asm-generic/unistd.h:__NR_close; fs/open.c:close@v6.18.46 -/
theorem sysno_57_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 57 [10, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        close_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) close_model [] := by
  sys_norm

/-- Only a0 is read: `SYSCALL_DEFINE1` takes one argument, so garbage in
the other five registers — the flags a `close_range` would read — changes
nothing.
kernel: include/uapi/asm-generic/unistd.h:__NR_close; fs/open.c:close@v6.18.46 -/
theorem sysno_57_reads_only_the_fd (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 57 [3, 7, 7, 7, 7, 7] (fun _ => none) (fun _ => none))
        close_model o
      ↔ o = Ok (mkEffect 0 [] []) after_close_3 [] := by
  sys_norm

/-- `close(2^32 + 3)` IS `close(3)`: the register's high half is dropped
by the `unsigned int` cast, so the call aliases onto the file at 3 and
closes it.
kernel: include/uapi/asm-generic/unistd.h:__NR_close; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:close@v6.18.46 -/
theorem close_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 57 [Z_to_bv 64 (2 ^ 32 + 3), 0, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) close_model o
      ↔ o = Ok (mkEffect 0 [] []) after_close_3 [] := by
  sys_norm

/-- Truncation ALIASES rather than REJECTS: a model comparing the full
64-bit register would find no such fd and answer -EBADF, which the kernel
never does here.
kernel: include/uapi/asm-generic/unistd.h:__NR_close; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:close@v6.18.46 -/
theorem close_fd_2_pow_32_plus_3_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 57 [Z_to_bv 64 (2 ^ 32 + 3), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) close_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and it aliases onto the LOW half exactly: `close(2^32 + 10)` is
`close(10)`, a free number, and is -EBADF; a model that let the high half
pick some other open slot and answered 0 is refused.
kernel: include/uapi/asm-generic/unistd.h:__NR_close; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:close@v6.18.46 -/
theorem close_fd_2_pow_32_plus_10_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 57 [Z_to_bv 64 (2 ^ 32 + 10), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) close_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `close(2^32)` IS `close(0)`, the spec docstring's own example: bit 32
falls off the `unsigned int` cast and stdin closes.
kernel: include/uapi/asm-generic/unistd.h:__NR_close; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:close@v6.18.46 -/
theorem close_fd_2_pow_32_is_close_0 (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 57 [Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) close_model o
      ↔ o = Ok (mkEffect 0 [] []) after_close_0 [] := by
  sys_norm

/-- …and is not -EBADF: a model reading the register whole finds no fd
2^32 and answers -EBADF, which the kernel never does here.
kernel: include/uapi/asm-generic/unistd.h:__NR_close; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:close@v6.18.46 -/
theorem close_fd_2_pow_32_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 57 [Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) close_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `close(-1)` through the table: the all-ones register narrows to
4294967295 and is -EBADF, never a success on some aliased slot.
kernel: include/uapi/asm-generic/unistd.h:__NR_close; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:close@v6.18.46 -/
theorem sysno_57_minus_one_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 57 [Z_to_bv 64 (2 ^ 64 - 1), 0, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) close_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) close_model [] := by
  sys_norm

/-! # Part three: `ftruncate` (46)

Worked examples over `Sys.Fs.Open.ftruncate_spec` and its guard
`modeled_truncate_gap`.  Line numbers are Linux v6.18.46 (commit
1f99e9ab748f) throughout.

HOW THESE ARE STATED.  The arm is called directly, `ftruncate_spec fd len
i ft_model o`, over one fixture holding a descriptor of every kind but
`FdFileRW` and two write-only files to resize; the dispatcher
pins at the end go through `syscall_spec` on a `SyscallInput` numbered 46,
so the table's `fd32` narrowing of a0 and its whole-register reading of
a1 are under test with the arm.  Each decision is pinned twice, an `iff`
over every outcome and a refutation of the answer a wrong model or a
lying kernel would give, as the other parts do.  The probe every `probe:`
line below cites is `testing/syscall-check/tests/ftruncate_spec.c`; its
`kinds` mode numbers the calls 1 (stdin), 2 (stdout), 3 (stderr), 4
(stderr, 2^40), 5 and 6 (a directory), 7 (an O_RDONLY file), 8 and 9 (a
closed number), and its `order` mode 1 (`ftruncate(-1, -1)`), 2 (a closed
number, -1), 3 and 4 (a closed number, 0 and 2^40), 5 (a writable file,
-1).  That numbering is read by nothing: the `probe:` lines are what
`check_lean_pin_evidence.py` checks, and one ftruncate call added ahead
of these in the probe renumbers every `#n` they cite.

THE KERNEL'S ORDER.  `SYSCALL_DEFINE2(ftruncate, unsigned int, fd, off_t,
length)` (fs/open.c:213-216, Linux v6.18.46) calls `do_sys_ftruncate`
(fs/open.c:202-211, Linux v6.18.46), which refuses a negative length
(:204-205) BEFORE it resolves the descriptor (`CLASS(fd, f)(fd)`, :206),
answers -EBADF on an empty one (:207-208) and hands the file to
`do_ftruncate` (fs/open.c:163-200, Linux v6.18.46), whose one test
`!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)` (:175-176)
is the -EINVAL of every kind here but the write-only file; the size then
goes through `do_truncate` (fs/open.c:39-71, Linux v6.18.46) and
`notify_change` (fs/attr.c:417, Linux v6.18.46) to the filesystem, and
the call answers 0.  The descriptor's position is never read or written
on that path — the class at include/linux/file.h:83 (Linux v6.18.46) is
over `fdget` (fs/file.c:1179, Linux v6.18.46), not `fdget_pos` — so the
offset pins state that the fd table the call leaves is the one it found.

THE MODEL'S BOUND.  Above `rw_bytes_max` bytes of zero-fill the arm
declines, and the decline is the model's, not a kernel test: the kernel
answers 0 there on tmpfs and -EFBIG only on a filesystem whose
`s_maxbytes` the length exceeds (`inode_newsize_ok`, fs/attr.c:244-271,
Linux v6.18.46), so the pins just over the bound refuse the 0 and the
pins at the largest `off_t` refuse BOTH answers beside the `Unmodeled`;
the spec's docstring says why neither can be admitted. -/

/-! ## The fixture and its readings

`ft_fds` holds one descriptor of every kind: the three channels, a
read-only file (3) and a write-only one (4, at offset 9) over `ft_fs`, a
directory (5), a fresh socket (6), both ends of pipe 0 (7 reads, 8
writes), /dev/null opened read-write (9), /dev/urandom (11), a write-only
descriptor on a path the file system does NOT hold (12, Rocq's
`ftruncate_dangling_model` shape) and a write-only descriptor on an
EMPTY file (13, at offset 4); 10 stays closed for the -EBADF pins.  The
file behind 4 is three bytes, "yz{", so a shrink, an equal length and a
grow are all one small numeral away; the file behind 13 is empty, the
probe's `ft-a` and `ft-e` shapes.  The model unfolds at `low`, as the
other parts' do; the closed `fd_lookup` and `fs_lookup` facts are
registered at the default priority so the first pass decides both
`match`es before the alternatives are read — and, on the bound pins, so
that the `Ok`-versus-`Unmodeled` mismatch is decided there too, before
the second pass could try to build a 131072-byte zero-fill (and the arm
pins above the bound run that first pass ALONE; the bound section says
what happened when they did not).  A refutation
whose forged outcome differs from the admitted one only in the MODEL is
stated on the hypothesis (`intro h; sys_refute at h`), for the reason
`Checks/Cases/Fs/File.lean`'s `dup_success_without_the_copy_rejected`
gives.  `ft_devnull_fds` and `ft_urandom_fds` are the descriptor tables
of Rocq's `devnull_model` and `urandom_model`, for the two
`*_dispatch_sites` legs. -/

/-- One descriptor of every kind, two of them writable files; 10 is closed. -/
def ft_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 7),
    (4, .FdFileW [103] 9), (5, .FdDir), (6, .FdSocket .SkFresh),
    (7, .FdPipe 0 false), (8, .FdPipe 0 true), (9, .FdDevNull true true),
    (11, .FdUrandom), (12, .FdFileW [104] 0), (13, .FdFileW [105] 4) ]

/-- Pipe 0 holds two bytes, "hi". -/
def ft_pipes : List (word × PipeBuf) := [(0, ([104, 105], 2))]

/-- The files behind descriptors 3 ("x"), 4 ("yz{") and 13 (empty); [104]
is absent on purpose. -/
def ft_fs : Fs.Fs := [([102], [120]), ([103], [121, 122, 123]), ([105], [])]

def ft_model : Model := fixture_of (fds := ft_fds) (pipes := ft_pipes) (fs := ft_fs)

/-- Rocq's `devnull_model` table: /dev/null read-only at 3, write-only at
4, read-write at 5. -/
def ft_devnull_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
    (3, .FdDevNull true false), (4, .FdDevNull false true), (5, .FdDevNull true true) ]
def ft_devnull_model : Model := fixture_of (fds := ft_devnull_fds)

/-- Rocq's `urandom_model` table: /dev/urandom at 3.  The stream Rocq
attaches is not read by ftruncate and is left out. -/
def ft_urandom_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdUrandom) ]
def ft_urandom_model : Model := fixture_of (fds := ft_urandom_fds)

attribute [sys_simp low] ft_model.eq_1 ft_devnull_model.eq_1 ft_urandom_model.eq_1

-- Sys/Fs/Open.lean: the spec's unfolding and its guard's, at the priority every spec has.
attribute [sys_simp low] ftruncate_spec.eq_1 modeled_truncate_gap.eq_1

/- `modeled_zero_fill` is `Sys/Fs/ReadWrite.lean`'s, the comparison the
guard applies; its unfolding is registered here `local`, so that it
reaches this part's pins and nothing else, because this port edits only
its own files, and the ReadWrite twin's Cases file registers it for its
own (when a shared register exists, one of the two lines goes). -/
attribute [local sys_simp low] Sys.Fs.ReadWrite.modeled_zero_fill.eq_1

/-! ### The closed readings the first pass needs -/
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_0 : fd_lookup ft_fds 0 = some (.FdChannel 0) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_2 : fd_lookup ft_fds 2 = some (.FdChannel 2) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_3 : fd_lookup ft_fds 3 = some (.FdFile [102] 7) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_4 : fd_lookup ft_fds 4 = some (.FdFileW [103] 9) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_5 : fd_lookup ft_fds 5 = some (.FdDir) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_6 : fd_lookup ft_fds 6 = some (.FdSocket .SkFresh) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_7 : fd_lookup ft_fds 7 = some (.FdPipe 0 false) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_8 : fd_lookup ft_fds 8 = some (.FdPipe 0 true) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_9 : fd_lookup ft_fds 9 = some (.FdDevNull true true) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_11 : fd_lookup ft_fds 11 = some (.FdUrandom) := rfl
/-- The write-only descriptor whose path the file system does not hold.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_12 : fd_lookup ft_fds 12 = some (.FdFileW [104] 0) := rfl
/-- The write-only descriptor on the empty file.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_13 : fd_lookup ft_fds 13 = some (.FdFileW [105] 4) := rfl
/-- The closed number.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_10 : fd_lookup ft_fds 10 = none := rfl
/-- The number `ftruncate(-1, …)` narrows to, past every table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_4294967295 : fd_lookup ft_fds 4294967295 = none := rfl
/-- The file behind descriptor 4, closed.
model: a closed `fs_lookup` at a literal path, a rewrite for `sys_norm`. -/
theorem fs_lookup_ft_103 : fs_lookup ft_fs [103] = some [121, 122, 123] := rfl
/-- The file behind descriptor 13, closed: empty.
model: a closed `fs_lookup` at a literal path, a rewrite for `sys_norm`. -/
theorem fs_lookup_ft_105 : fs_lookup ft_fs [105] = some [] := rfl
/-- The path behind descriptor 12, absent.
model: a closed `fs_lookup` at a literal path, a rewrite for `sys_norm`. -/
theorem fs_lookup_ft_104 : fs_lookup ft_fs [104] = none := rfl
/-- The write-only /dev/null of Rocq's `devnull_model`.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_devnull_4 : fd_lookup ft_devnull_fds 4 = some (.FdDevNull false true) := rfl
/-- The read-only /dev/null of Rocq's `devnull_model`.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_devnull_3 : fd_lookup ft_devnull_fds 3 = some (.FdDevNull true false) := rfl
/-- The /dev/urandom of Rocq's `urandom_model`.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_ft_urandom_3 : fd_lookup ft_urandom_fds 3 = some (.FdUrandom) := rfl

/-- `fd32 4` read closed, so the first pass alone resolves the table's a0
narrowing on the pins above the bound (`sysno_46_len_2_pow_32_*`), which
use that pass alone (the bound section says why).
model: `Syscall.fd32` at a numeral, a rewrite for the normal form. -/
theorem fd32_ft_4 : fd32 4 = 4 := by decide

attribute [sys_simp]
  fd32_ft_4 lookup_ft_0 lookup_ft_2 lookup_ft_3 lookup_ft_4 lookup_ft_5 lookup_ft_6 lookup_ft_7 lookup_ft_8
  lookup_ft_9 lookup_ft_11 lookup_ft_12 lookup_ft_13 lookup_ft_10 lookup_ft_4294967295
  fs_lookup_ft_103 fs_lookup_ft_105 fs_lookup_ft_104 lookup_ft_devnull_4 lookup_ft_devnull_3
  lookup_ft_urandom_3

/-! ## `do_sys_ftruncate`: a negative length is refused before the fd is looked up

`do_sys_ftruncate` (fs/open.c:202-211, Linux v6.18.46) tests `length < 0`
(:204-205) and returns -EINVAL before `CLASS(fd, f)(fd)` (:206) resolves
anything, so `ftruncate(-1, -1)` is -EINVAL and not -EBADF — the ordering
a spec written from the man page gets backwards.  `length` is the
`off_t`, the whole 64-bit register read signed: 2^63 is negative and
2^63 - 1 is not.  The first pin is over EVERY model and descriptor, which
is what "before the lookup" means. -/

/-- A negative length is -EINVAL on ANY model and ANY descriptor: the test
sits ahead of the lookup, so nothing about the table is consulted.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem negative_len_is_einval_before_the_lookup (m : Model) (fd : word) (i : SyscallInput)
    (o : outcome SyscallEffect) :
    ftruncate_spec fd (Z_to_bv 64 (2 ^ 64 - 1)) i m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- `ftruncate(<closed>, -1)` is not -EBADF: a spec that looked the number
up first would answer that, and the kernel never does.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#2:ret=-EBADF -- order -/
theorem negative_len_on_a_closed_fd_is_not_ebadf (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 10 (Z_to_bv 64 (2 ^ 64 - 1)) i ft_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `ftruncate(-1, -1)`: the fd narrows to 4294967295, past every table,
and the length still wins — -EINVAL.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem minus_one_fd_negative_len_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4294967295 (Z_to_bv 64 (2 ^ 64 - 1)) i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- …and a negative length on the WRITABLE file is the same -EINVAL: the
kind is never reached.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem negative_len_on_a_writable_file_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4 (Z_to_bv 64 (2 ^ 64 - 1)) i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- A model that truncated the file to 2^64 - 1 read as unsigned — or to
anything — on a negative length is refused: no success leaves this arm.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem negative_len_on_a_writable_file_is_not_a_success (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ ftruncate_spec 4 (Z_to_bv 64 (2 ^ 64 - 1)) i ft_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- 2^63 is NEGATIVE as an `off_t`: -EINVAL, not a huge grow.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem two_pow_63_is_a_negative_length (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4 (Z_to_bv 64 (2 ^ 63)) i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- …so it is not a decline: a model reading the length unsigned would
send 2^63 to the bound and decline, where the kernel answers -EINVAL
(the probe's `zero` mode injects 0x8000000000000000 as the length and
records the reject).
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem two_pow_63_is_not_a_huge_grow (i : SyscallInput) :
    ¬ ftruncate_spec 4 (Z_to_bv 64 (2 ^ 63)) i ft_model Unmodeled := by
  sys_refute

/-! ## `fd_empty`: a number with no file is -EBADF, whatever the length

Once the length is non-negative the descriptor is resolved, and an empty
one is -EBADF (fs/open.c:207-208, Linux v6.18.46; `fd_empty`,
include/linux/file.h:45, Linux v6.18.46) — for a length of 0 and for
2^40 alike, since the size is not looked at until `do_ftruncate` has a
file.  A model that hoisted its bound above the lookup would decline the
2^40 call instead. -/

/-- The closed number is -EBADF, and nothing else.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- order -/
theorem closed_number_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 10 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) ft_model [] := by
  sys_norm

/-- A closed number is not -EINVAL: the kind it used to have is gone with
the file.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#8:ret=-EINVAL -- kinds -/
theorem closed_fd_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 10 0 i ft_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and not 0.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem closed_fd_is_not_a_success (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 10 0 i ft_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A huge length on a closed number is still -EBADF: the lookup comes
before any reading of the size.
kernel: fs/open.c:do_sys_ftruncate; include/linux/file.h:fd_empty@v6.18.46 -/
theorem closed_fd_huge_len_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 10 (Z_to_bv 64 (2 ^ 40)) i ft_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) ft_model [] := by
  sys_norm

/-- …and not a decline: the model's bound is consulted only once the
descriptor is a writable regular file.
kernel: fs/open.c:do_sys_ftruncate@v6.18.46 -/
theorem closed_fd_huge_len_is_not_a_decline (i : SyscallInput) :
    ¬ ftruncate_spec 10 (Z_to_bv 64 (2 ^ 40)) i ft_model Unmodeled := by
  sys_refute

/-- `ftruncate(-1, 0)`: the register narrows to 4294967295, at or past
every table, so the fine length reaches the lookup and it is -EBADF.
kernel: fs/open.c:do_sys_ftruncate; include/linux/file.h:fd_empty@v6.18.46 -/
theorem minus_one_fd_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4294967295 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) ft_model [] := by
  sys_norm

/-! ## `do_ftruncate`: every kind but a writable regular file is -EINVAL

`do_ftruncate` (fs/open.c:163-200, Linux v6.18.46) has one test for the
kind, `!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)`
(:175-176), and it answers -EINVAL — so a directory is -EINVAL and not
read's -EISDIR, a pipe is -EINVAL and not lseek's -ESPIPE, and an
O_RDONLY file is -EINVAL and not write's -EBADF.  The two halves are
both pinned: the pipe's WRITE end holds FMODE_WRITE (`create_pipe_files`,
fs/pipe.c:944-945, Linux v6.18.46, opens it O_WRONLY) and fails S_ISREG
alone; the read-only file is S_ISREG and fails FMODE_WRITE alone.  The
model reads neither the pipe's direction bit nor /dev/null's mode bits
on this arm.  The size is not consulted before the kind: 2^40 on a
directory is the same -EINVAL. -/

/-- A channel is -EINVAL: no channel is a writable regular file, so each
fails the S_ISREG half of `do_ftruncate`'s test or the FMODE_WRITE half.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- kinds -/
theorem channel_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 0 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- stdin is never truncated to 0: a model treating the channels as
writable regular files is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#1:ret=0 -- kinds -/
theorem channel_is_not_a_success (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 0 0 i ft_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- stderr with a huge length is still -EINVAL: the kind is decided before
the size is read, so a model that hoisted its bound above the kind
dispatch — and declined here — is refused by the `iff`.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem channel_huge_len_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 2 (Z_to_bv 64 (2 ^ 40)) i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- stderr is not -ESPIPE: under the tracer it is a pipe (the harness's
1 MiB pipes, testing/vm/README.md), and the probe's `kinds` call 3 is
`ftruncate(2, 0)`, so this channel pin is the one the recorded -ESPIPE
lie exercises; `pipe_is_not_espipe` below states the same refusal on the
model's `FdPipe` kind, which THIS probe never opens: `ftruncate_spec.c`
calls no `pipe2`, so the `FdPipe` pins carry `do_ftruncate`'s line rather
than a run.  A probe can hold one — `pipe2` (59) is an arm and the
`pipe2` probes open it — so a `pipe2` leg mutated to -ESPIPE is the
run-backed negative those pins still owe.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#3:ret=-ESPIPE -- kinds -/
theorem channel_is_not_espipe (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 2 0 i ft_model (Ok (mkEffect (errno_ret ESPIPE) [] []) m' evs) := by
  sys_refute

/-- A socket inode is S_ISSOCK: -EINVAL from the first half of the test,
before FMODE_WRITE is consulted.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem socket_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 6 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- …and never 0: a socket is opened read-write, and a model reading the
mode rather than S_ISREG would truncate it.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem socket_is_not_a_success (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 6 0 i ft_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The read end of a pipe is -EINVAL.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem pipe_read_end_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 7 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- A pipe is not -ESPIPE: that is lseek's errno, and it appears nowhere
on this path.  fs/open.c's one -ESPIPE is `vfs_fallocate`'s S_ISFIFO test
(fs/open.c:322-323, Linux v6.18.46), which no truncate reaches, and
fs/attr.c has none.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem pipe_is_not_espipe (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 7 0 i ft_model (Ok (mkEffect (errno_ret ESPIPE) [] []) m' evs) := by
  sys_refute

/-- The WRITE end of a pipe is -EINVAL too: it holds FMODE_WRITE, so it is
the S_ISREG half alone that refuses it, and an arm reading the direction
bit as "writable, so truncate" would be wrong here.
kernel: fs/open.c:do_ftruncate; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem pipe_write_end_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 8 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- …and is never a success.
kernel: fs/open.c:do_ftruncate; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem pipe_write_end_is_not_a_success (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 8 0 i ft_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- /dev/null opened read-write is -EINVAL: a character device is not
S_ISREG, whatever mode it was granted.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem devnull_rw_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 9 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- /dev/null is never truncated: the write mode it was granted does not
make it a regular file.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem devnull_rw_is_not_a_success (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 9 0 i ft_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- /dev/urandom is -EINVAL: a character device, and read-only besides.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem urandom_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 11 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- …and not write's -EBADF for the read-only description: the kind is
refused before the mode is read.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem urandom_is_not_ebadf (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 11 0 i ft_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A read-only regular file is -EINVAL: S_ISREG holds and FMODE_WRITE
does not.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- kinds -/
theorem readonly_file_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 3 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- …not write's -EBADF: `vfs_write` refuses a read-only file with -EBADF,
and this path never does.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#7:ret=-EBADF -- kinds -/
theorem readonly_file_is_not_ebadf (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 3 0 i ft_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and the file behind it is not touched: a model that truncated "x"
through its read-only descriptor is refused.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem readonly_file_is_not_truncated (i : SyscallInput) (evs : List event) :
    ¬ ftruncate_spec 3 0 i ft_model
        (Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [102] []) ft_model) evs) := by
  sys_refute

/-- A directory is -EINVAL.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- kinds -/
theorem dir_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 5 0 i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- …not read's -EISDIR: that errno belongs to `vfs_truncate`
(fs/open.c:73, Linux v6.18.46, -EISDIR at :81-83), which only the
path-based truncate(2) reaches.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#5:ret=-EISDIR -- kinds -/
theorem dir_is_not_eisdir (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 5 0 i ft_model (Ok (mkEffect (errno_ret EISDIR) [] []) m' evs) := by
  sys_refute

/-- A directory with a huge length is -EINVAL, not a decline: the kind is
decided before the model's bound is consulted.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem dir_huge_len_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 5 (Z_to_bv 64 (2 ^ 40)) i ft_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- …and is not a decline.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem dir_huge_len_is_not_a_decline (i : SyscallInput) :
    ¬ ftruncate_spec 5 (Z_to_bv 64 (2 ^ 40)) i ft_model Unmodeled := by
  sys_refute

/-! ## The write-only file: the size is set, the offset is not

`do_truncate` (fs/open.c:39-71, Linux v6.18.46) sets `ia_size = length`
(:49) and hands the change to `notify_change` (:68); the filesystem
drops the tail or extends the file into a hole, which the model writes
as `Fs.file_truncate`: the first `len` bytes, then zeros.  The call
answers 0 — a bare 0, not the new length — and the descriptor's offset
stays where it was: the class over `fdget` (include/linux/file.h:83,
Linux v6.18.46) never takes the position lock, and nothing on the path
assigns `f_pos`.  So the admitted post-state below is `with_fs` alone,
over the fixture's fd table unchanged; a model that reset, clamped or
moved the offset is refused beside each. -/

/-- Shrink to nothing: "yz{" becomes empty, and the call is 0.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- data -/
theorem shrink_to_zero_empties_the_file (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4 0 i ft_model o ↔
      o = Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [103] []) ft_model) [] := by
  sys_norm

/-- Shrink to a middle offset: "yz{" becomes "y".
probe: testing/syscall-check/tests/ftruncate_spec.c#conform --seed-file ft-s=616263 -- seeded -/
theorem shrink_to_one_keeps_the_prefix (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4 1 i ft_model o ↔
      o = Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [103] [121]) ft_model) [] := by
  sys_norm

/-- Success is a BARE 0, not write's new-length return: a model answering
the length is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#3:ret=3 -- data -/
theorem shrink_does_not_return_the_length (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 4 1 i ft_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- A shrink leaves the offset PAST end-of-file: a model that clamped the
descriptor to the new length (1) is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate lseek#1:ret=2 -- offset -/
theorem shrink_does_not_clamp_the_offset (i : SyscallInput) (evs : List event) :
    ¬ ftruncate_spec 4 1 i ft_model
        (Ok (mkEffect 0 [] [])
            (with_fds (fd_insert ft_fds 4 (.FdFileW [103] 1))
              (with_fs (fs_set ft_fs [103] [121]) ft_model)) evs) := by
  intro h
  sys_refute at h

/-- …and a model that reset it to 0 is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate lseek#1:ret=0 -- offset -/
theorem shrink_does_not_reset_the_offset (i : SyscallInput) (evs : List event) :
    ¬ ftruncate_spec 4 1 i ft_model
        (Ok (mkEffect 0 [] [])
            (with_fds (fd_insert ft_fds 4 (.FdFileW [103] 0))
              (with_fs (fs_set ft_fs [103] [121]) ft_model)) evs) := by
  intro h
  sys_refute at h

/-- …and a model that answered 0 and left the file as it was is refused:
the length did change.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate lseek#2:ret=5 -- offset -/
theorem shrink_changes_the_file (i : SyscallInput) (evs : List event) :
    ¬ ftruncate_spec 4 1 i ft_model (Ok (mkEffect 0 [] []) ft_model evs) := by
  intro h
  sys_refute at h

/-- Truncating to the CURRENT length is a real 0 with the file as it was:
`do_truncate` runs, and `Fs.file_truncate` at the length is the identity.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- data -/
theorem truncate_to_the_current_length_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4 3 i ft_model o ↔
      o = Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [103] [121, 122, 123]) ft_model) [] := by
  sys_norm

/-- …not -EINVAL: no test on this path compares the length to the size.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate ftruncate#4:ret=-EINVAL -- data -/
theorem truncate_to_the_current_length_is_not_einval (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ ftruncate_spec 4 3 i ft_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- Grow from non-empty: "yz{" to five bytes is "yz{" and two zeros.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- data -/
theorem grow_zero_fills_the_tail (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4 5 i ft_model o ↔
      o = Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [103] [121, 122, 123, 0, 0]) ft_model) [] := by
  sys_norm

/-- A grow leaves the offset alone too: a model that moved the descriptor
to the new end (5) is refused.
probe: testing/syscall-check/tests/ftruncate_spec.c#reject --mutate lseek#1:ret=6 -- grow-offset -/
theorem grow_does_not_move_the_offset (i : SyscallInput) (evs : List event) :
    ¬ ftruncate_spec 4 5 i ft_model
        (Ok (mkEffect 0 [] [])
            (with_fds (fd_insert ft_fds 4 (.FdFileW [103] 5))
              (with_fs (fs_set ft_fs [103] [121, 122, 123, 0, 0]) ft_model)) evs) := by
  intro h
  sys_refute at h

/-- A grow is not -EINVAL: the only REACHABLE -EINVAL on a writable
regular file is the negative length, already refused — the other,
`small && length > MAX_NON_LFS` (fs/open.c:179-180, Linux v6.18.46), sits
behind the `small` flag every 64-bit open's O_LARGEFILE clears.
kernel: fs/open.c:do_sys_ftruncate,do_ftruncate@v6.18.46 -/
theorem grow_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 4 5 i ft_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- A grow zero-fills, it does not repeat: a model extending "yz{" with
its last byte is refused.  `do_truncate` only sets `ia_size`; the bytes
past the old end are a hole, which the filesystem reads as zeros (on
tmpfs `shmem_setattr` merely moves `i_size`).
kernel: fs/open.c:do_truncate; mm/shmem.c:shmem_setattr@v6.18.46 -/
theorem grow_fills_with_zeros_not_bytes (i : SyscallInput) (evs : List event) :
    ¬ ftruncate_spec 4 5 i ft_model
        (Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [103] [121, 122, 123, 123, 123]) ft_model) evs) := by
  intro h
  sys_refute at h

/-- Grow from EMPTY: four zeros, through a descriptor whose offset (4)
lands exactly at the new end and stays there.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- data -/
theorem grow_from_empty_is_zeros (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 13 4 i ft_model o ↔
      o = Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [105] [0, 0, 0, 0]) ft_model) [] := by
  sys_norm

/-- Truncating the empty file to 0 is a real 0 and leaves it empty.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- zero -/
theorem empty_file_to_zero_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 13 0 i ft_model o ↔
      o = Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [105] []) ft_model) [] := by
  sys_norm

/-- Only the named file changes: a model whose truncation of 4 also
touched the file behind 3 is refused.
kernel: fs/open.c:do_truncate@v6.18.46 -/
theorem truncation_touches_one_file (i : SyscallInput) (evs : List event) :
    ¬ ftruncate_spec 4 0 i ft_model
        (Ok (mkEffect 0 [] [])
            (with_fs (fs_set (fs_set ft_fs [103] []) [102] []) ft_model) evs) := by
  intro h
  sys_refute at h

/-! ## The bound: a grow the model can build is judged, a larger one declines

`modeled_truncate_gap` compares the new length against the file's length
plus `rw_bytes_max` (131072).  On "yz{" the bound sits at 131075: a grow
to it is judged and one byte more declines; on the EMPTY file, which is
what the probe's `bound-at` and `bound-over` cases open, it sits at
131072 exactly, and both files are pinned.  The decline is the model's
own — Linux answers 0 on tmpfs, whose `s_maxbytes` is LLONG_MAX, and
-EFBIG only on a filesystem whose `s_maxbytes` the new length exceeds
(`inode_newsize_ok`, fs/attr.c:254-255 and :269-270, Linux v6.18.46), so
the pins just over the bound refuse the 0 and the pins at the largest
`off_t` refuse both answers beside the `Unmodeled`.  The value pins read
the guard directly; the arm pins go through the spec, where the first
pass decides the guard and the `Ok`/`Unmodeled` mismatch before any
zero-fill would be built.  EVERY ARM PIN ABOVE THE BOUND IS PROVED BY
THAT FIRST PASS ALONE (`sys_simp_pass +decide`, not `sys_norm`), and the
reason is the spec the pins have to refuse, not the one they are proved
on: a spec with the gate removed answers `Ok` here with
`file_truncate "yz{" 131076` in its model, and `sys_norm`'s second pass
would then evaluate that closed term — a 131073-element `replicate` —
and overflow the stack.  Measured on this tree: the `branch-else` and
`negate` mutants of the gate made Lean abort (exit 134, "Stack overflow
detected") and `lean_mutate.py` scored them ERROR, a verdict no
allowlist covers.  Under one pass the same mutants fail these pins with
`unsolved goals`, which is the kill they deserve; under the real spec
one pass closes them, since the guard is decided and `Unmodeled` meets
`Ok` by constructor.  The table pins at 2^32 need `fd32 4` read closed
for that (`fd32_ft_4`), which the direct calls do not.  2^31 is a huge
POSITIVE length (the
`O_LARGEFILE` clear at fs/open.c:170-171, Linux v6.18.46, makes
`MAX_NON_LFS` unreachable, and the kernel answers 0), and 2^63 - 1 is the
largest `off_t`: both decline here, and neither is -EINVAL. -/

/-- A grow of exactly `rw_bytes_max` past "yz{" is within the model.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- bound-at -/
theorem grow_at_the_bound_is_modeled :
    modeled_truncate_gap [121, 122, 123] (Z_to_bv 64 131075) = true := by
  decide

/-- …and one byte more is not.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- bound-over -/
theorem grow_over_the_bound_is_not_modeled :
    ¬ (modeled_truncate_gap [121, 122, 123] (Z_to_bv 64 131076) = true) := by
  decide

/-- The probe's `bound-at` case grows a FRESH file, so the bound it
exercises is 131072 exactly: judged from empty.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- bound-at -/
theorem grow_from_empty_at_the_bound_is_modeled :
    modeled_truncate_gap [] (Z_to_bv 64 131072) = true := by
  decide

/-- …and 131073 from empty is not.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- bound-over -/
theorem grow_from_empty_over_the_bound_is_not_modeled :
    ¬ (modeled_truncate_gap [] (Z_to_bv 64 131073) = true) := by
  decide

/-- A shrink is always within the model, however large: the gap is
negative.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- bound-shrink -/
theorem shrink_is_always_modeled :
    modeled_truncate_gap [121, 122, 123] 0 = true := by
  decide

/-- …for EVERY length that does not grow the file, whatever the file's
size: the gap is decided on the `Int` difference `len - data.length`, and
a shrink makes it negative.  What this refuses that the literal pin above
cannot is a guard on the wrong quantity: the absolute difference (the
probe's `bound-shrink` target), the new length itself (`len ≤ 131072`,
which declines the shrink of a large file), a reversed subtraction, or a
bound on the file's size.  A guard on a truncating `Nat` subtraction is
the same guard (a shrink is `0 ≤ 131072` either way), and one with a
larger constant passes here too; `grow_from_empty_over_the_bound_is_not_modeled`
is what refuses that one.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- bound-shrink -/
theorem shrink_is_modeled_for_every_length (data : List byte) (len : word)
    (h : bv_unsigned len ≤ data.length) : modeled_truncate_gap data len = true := by
  unfold modeled_truncate_gap Sys.Fs.ReadWrite.modeled_zero_fill Sys.Uaccess.rw_bytes_max
  simp only [decide_eq_true_eq]
  omega

/-- 2^30 from empty is out of the model, and the guard says so on the
`Int`, without building the numeral.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- guard-z -/
theorem two_pow_30_is_not_modeled :
    ¬ (modeled_truncate_gap [] (Z_to_bv 64 (2 ^ 30)) = true) := by
  decide

/-- 2^63 - 1, the largest `off_t`, is out of the model.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- huge -/
theorem largest_off_t_is_not_modeled :
    ¬ (modeled_truncate_gap [] (Z_to_bv 64 (2 ^ 63 - 1)) = true) := by
  decide

/-- The arm judges a grow to the bound: it is not a decline.  What the
call leaves is 131075 bytes, which this pin does not spell out; it fixes
only that the bound itself is judged.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- bound-at -/
theorem grow_at_the_bound_is_judged (i : SyscallInput) :
    ¬ ftruncate_spec 4 (Z_to_bv 64 131075) i ft_model Unmodeled := by
  sys_refute

/-- …and one byte over the bound declines.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- bound-over -/
theorem grow_over_the_bound_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4 (Z_to_bv 64 131076) i ft_model o ↔ o = Unmodeled := by
  sys_simp_pass +decide

/-- The empty file's bound through the arm: 131072 on fd 13 is judged,
which is the probe's `bound-at` call itself.
probe: testing/syscall-check/tests/ftruncate_spec.c#conform -- bound-at -/
theorem grow_from_empty_at_the_bound_is_judged (i : SyscallInput) :
    ¬ ftruncate_spec 13 (Z_to_bv 64 131072) i ft_model Unmodeled := by
  sys_refute

/-- …and 131073 on fd 13 declines, the probe's `bound-over` call itself.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- bound-over -/
theorem grow_from_empty_over_the_bound_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 13 (Z_to_bv 64 131073) i ft_model o ↔ o = Unmodeled := by
  sys_simp_pass +decide

/-- Over the bound the kernel's 0 is refused — the decline is the model's,
and a model that answered 0 there has to build the zero-fill it cannot.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- bound-over -/
theorem grow_over_the_bound_is_not_a_success (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 4 (Z_to_bv 64 131076) i ft_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_simp_pass +decide

/-- 2^31 is a huge POSITIVE length: it declines rather than answering.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- big31 -/
theorem two_pow_31_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4 (Z_to_bv 64 (2 ^ 31)) i ft_model o ↔ o = Unmodeled := by
  sys_simp_pass +decide

/-- …and is not -EINVAL: a spec reading the length as a 32-bit `off_t`, or
keeping the `MAX_NON_LFS` test the `O_LARGEFILE` clear disables, would
answer that, and the kernel answers 0.
kernel: fs/open.c:do_ftruncate; include/linux/fcntl.h:force_o_largefile@v6.18.46 -/
theorem two_pow_31_is_not_einval (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 4 (Z_to_bv 64 (2 ^ 31)) i ft_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_simp_pass +decide

/-- 2^30 from the empty file declines, decided on the guard's `Int`
comparison: the normalizer never builds the numeral.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- guard-z -/
theorem two_pow_30_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 13 (Z_to_bv 64 (2 ^ 30)) i ft_model o ↔ o = Unmodeled := by
  sys_simp_pass +decide

/-- The largest `off_t` declines: the recorded tmpfs 0 and the -EFBIG
Rocq's prose measured on virtiofs are both real, so neither can be
admitted.
probe: testing/syscall-check/tests/ftruncate_spec.c#fail-closed -- huge -/
theorem largest_off_t_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 4 (Z_to_bv 64 (2 ^ 63 - 1)) i ft_model o ↔ o = Unmodeled := by
  sys_simp_pass +decide

/-- …so the tmpfs answer, 0, is refused.
kernel: fs/attr.c:inode_newsize_ok@v6.18.46 -/
theorem largest_off_t_is_not_a_success (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 4 (Z_to_bv 64 (2 ^ 63 - 1)) i ft_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_simp_pass +decide

/-- …and so is -EFBIG (27; the register `State/Errno.lean` has no constant
for it, so it is spelled as its numeral): `inode_newsize_ok`'s answer
where `s_maxbytes` is below the length — vfat's `0xffffffff`
(`fat_fill_super`, fs/fat/inode.c:1663, Linux v6.18.46) — and the one a
virtiofs server relays (the guest's FUSE superblock takes
MAX_LFS_FILESIZE, `fuse_sb_defaults`, fs/fuse/inode.c, Linux v6.18.46).
The model has no filesystem to read either from.
kernel: fs/attr.c:inode_newsize_ok@v6.18.46 -/
theorem largest_off_t_is_not_efbig (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 4 (Z_to_bv 64 (2 ^ 63 - 1)) i ft_model
        (Ok (mkEffect (errno_ret 27) [] []) m' evs) := by
  sys_simp_pass +decide

/-! ## A writable descriptor on a path the file system does not hold

Rocq's `ftruncate_on_a_dangling_fd_is_unmodeled`: an `FdFileW` whose path
`fs_lookup` does not find is `unmodeled`.  The arm is unreachable on a
model the openat arm built — a write-only descriptor always points into
the fs — so this is a fixture the spec can only decline, never judge. -/

/-- The dangling descriptor declines, on the arm.
rocq-twin: ftruncate_on_a_dangling_fd_is_unmodeled -/
theorem dangling_writable_fd_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 12 0 i ft_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and through the table, the 0 Rocq's example offers the checker is
refused (Rocq states it as `check_syscall … = CheckUnmodeled`).
rocq-twin: ftruncate_on_a_dangling_fd_is_unmodeled -/
theorem dangling_writable_fd_success_rejected (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 46 [12, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        ft_model (Ok (mkEffect 0 [] []) ft_model evs) := by
  sys_refute

/-! ## The two device fixtures of the openat part

The ftruncate legs of Rocq's `devnull_dispatch_sites` and
`urandom_dispatch_sites`, stated through the table on the descriptor
tables those Rocq models carry: the write-only /dev/null at 4 and the
/dev/urandom at 3 are each -EINVAL. -/

/-- The write-only /dev/null is -EINVAL through syscall 46.
kernel: fs/open.c:do_ftruncate@v6.18.46
rocq-twin: devnull_dispatch_sites -/
theorem devnull_ftruncate_is_einval (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [4, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        ft_devnull_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_devnull_model [] := by
  sys_norm

/-- …and never 0, though it was opened for writing: `do_ftruncate`'s
S_ISREG half refuses a character device whatever its mode.
kernel: fs/open.c:do_ftruncate@v6.18.46
rocq-twin: devnull_dispatch_sites -/
theorem devnull_ftruncate_is_not_a_success (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 46 [4, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        ft_devnull_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The READ-ONLY /dev/null is the same -EINVAL: `do_ftruncate`'s test is
`!S_ISREG(inode->i_mode) || !(f_mode & FMODE_WRITE)` (fs/open.c:175-176,
Linux v6.18.46), and a character device fails the first half whatever
its mode bits say, so the arm never consults them.  Rocq's
`devnull_model` holds this descriptor at 3 and its Cases file does not
truncate it; a spec that read the direction bits and answered write's
-EBADF on the read-only one would be refused here.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem devnull_readonly_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    ftruncate_spec 3 0 i ft_devnull_model o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_devnull_model [] := by
  sys_norm

/-- …and not -EBADF, the errno a mode-bit reading would borrow from write.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem devnull_readonly_is_not_ebadf (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ ftruncate_spec 3 0 i ft_devnull_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- /dev/urandom is -EINVAL through syscall 46: a character device, so
`do_ftruncate`'s S_ISREG half refuses it.
kernel: fs/open.c:do_ftruncate@v6.18.46
rocq-twin: urandom_dispatch_sites -/
theorem urandom_ftruncate_is_einval (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        ft_urandom_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_urandom_model [] := by
  sys_norm

/-! ## The dispatcher: syscall 46, its 32-bit fd and its 64-bit length

`SYSCALL_DEFINE2(ftruncate, unsigned int, fd, off_t, length)`
(fs/open.c:213, Linux v6.18.46): the fd is `unsigned int`, narrowed by
`__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:82-88,
Linux v6.18.46) through `__SC_CAST` (include/linux/syscalls.h:132, Linux
v6.18.46), which the table's `fd32` mirrors; the length is `off_t`, a
64-bit signed integer on riscv64, and the table hands the register over
whole.  `__NR3264_ftruncate` is 46 (include/uapi/asm-generic/unistd.h,
Linux v6.18.46). -/

/-- Syscall 46 on fd 4 with length 5 reaches the arm and grows the file.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_ftruncate; fs/open.c:ftruncate@v6.18.46 -/
theorem sysno_46_is_ftruncate (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [4, 5, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        ft_model o
      ↔ o = Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [103] [121, 122, 123, 0, 0]) ft_model) [] := by
  sys_norm

/-- Syscall 46 on the closed number 10 is -EBADF through the table too.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_ftruncate; fs/open.c:ftruncate,do_sys_ftruncate@v6.18.46 -/
theorem sysno_46_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [10, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        ft_model o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) ft_model [] := by
  sys_norm

/-- Only a0 and a1 are read: `SYSCALL_DEFINE2` takes two arguments, so
garbage in the other four registers changes nothing.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_ftruncate; fs/open.c:ftruncate@v6.18.46 -/
theorem sysno_46_reads_only_fd_and_len (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [4, 5, 7, 7, 7, 7] (fun _ => none) (fun _ => none))
        ft_model o
      ↔ o = Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [103] [121, 122, 123, 0, 0]) ft_model) [] := by
  sys_norm

/-- `ftruncate(2^32 + 4, 5)` IS `ftruncate(4, 5)`: the register's high
half is dropped by the `unsigned int` cast, so the call aliases onto the
writable file at 4 and grows it.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_ftruncate; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:ftruncate@v6.18.46 -/
theorem ftruncate_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [Z_to_bv 64 (2 ^ 32 + 4), 5, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) ft_model o
      ↔ o = Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [103] [121, 122, 123, 0, 0]) ft_model) [] := by
  sys_norm

/-- Truncation ALIASES rather than REJECTS: a model comparing the full
64-bit register would find no such fd and answer -EBADF, which the kernel
never does here.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_ftruncate; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:ftruncate@v6.18.46 -/
theorem ftruncate_fd_2_pow_32_plus_4_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 46 [Z_to_bv 64 (2 ^ 32 + 4), 5, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) ft_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The LENGTH is not narrowed: 2^63 in a1 is the negative `off_t` and is
-EINVAL, where a model reading a 32-bit length would see 0 and empty the
file.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_ftruncate; fs/open.c:ftruncate,do_sys_ftruncate@v6.18.46 -/
theorem sysno_46_len_is_the_whole_register (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [4, Z_to_bv 64 (2 ^ 63), 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) ft_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-- …and 2^32 in a1 is a huge grow, which declines; a model that narrowed
it to 0 and emptied the file is refused.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_ftruncate; fs/open.c:ftruncate,do_sys_ftruncate@v6.18.46 -/
theorem sysno_46_len_2_pow_32_is_not_zero (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 46 [4, Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none)) ft_model
        (Ok (mkEffect 0 [] []) (with_fs (fs_set ft_fs [103] []) ft_model) evs) := by
  sys_simp_pass +decide

/-- …and what it does answer is the decline, as 2^31 and the largest
`off_t` do through the arm.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_ftruncate; fs/open.c:ftruncate,do_sys_ftruncate@v6.18.46 -/
theorem sysno_46_len_2_pow_32_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [4, Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) ft_model o
      ↔ o = Unmodeled := by
  sys_simp_pass +decide

/-- `ftruncate(-1, -1)` through the table: the all-ones a0 narrows to
4294967295 and the all-ones a1 stays negative, so it is -EINVAL and not
-EBADF.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_ftruncate; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/open.c:ftruncate,do_sys_ftruncate@v6.18.46 -/
theorem sysno_46_minus_one_minus_one_is_einval (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [Z_to_bv 64 (2 ^ 64 - 1), Z_to_bv 64 (2 ^ 64 - 1), 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none)) ft_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) ft_model [] := by
  sys_norm

/-! ## A17: FdFileRW and FdFileA -/

def a17_open_model : Model :=
  fixture_of (fds := [(3, .FdFileRW [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_open_model.eq_1

/-- `ftruncate(fd, 0)` through a read-write file declines
(`Sys/Fs/Open.lean`'s header declares the narrowing).  The same call on
an `FdFileW` answers 0 and empties the file (`do_ftruncate`, fs/open.c,
Linux v6.18.46: an O_RDWR file passes the `FMODE_WRITE` test as a
write-only one does), so a mutant answering this kind as `FdFileW` fails
here.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem a17_rdwr_ftruncate_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [3, 0, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_open_model o ↔ o = Unmodeled := by
  sys_norm

def a17_open_append_model : Model :=
  fixture_of (fds := [(3, .FdFileA [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_open_append_model.eq_1

/-- `ftruncate(fd, 0)` through an append-mode file declines
(`Sys/Fs/Open.lean`'s header declares the narrowing).  The same call on
an `FdFileW` answers 0 and empties the file (`do_ftruncate`, fs/open.c,
Linux v6.18.46: O_APPEND rides on O_WRONLY, which passes the
`FMODE_WRITE` test, and nothing on the path reads it), so a mutant
answering this kind as `FdFileW` fails here.
kernel: fs/open.c:do_ftruncate@v6.18.46 -/
theorem a17_append_ftruncate_declines (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 46 [3, 0, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_open_append_model o ↔ o = Unmodeled := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Open
