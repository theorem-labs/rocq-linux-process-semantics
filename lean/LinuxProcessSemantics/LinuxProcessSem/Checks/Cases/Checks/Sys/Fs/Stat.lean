-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Stat
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Stat
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.Arms.Fs.Stat

/-! # Checks.Cases.Checks.Sys.Fs.Stat — what the `stat` checkers answer, read off against Linux

Pins over `Checks.Sys.Fs.Stat`'s executable checkers, the twin of the
`check_syscall` examples in `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`.
Not part of the trusted specification: this file is QA on the checkers,
and every claim in it is a claim about what the kernel does, with the
citation beside it.  Line numbers are Linux v6.18.46 (commit 1f99e9ab748f).

WHY A SECOND FILE BESIDE `Checks/Cases/Fs/Stat.lean`.  That file pins the
SPECS — the relations — and already twins every Rocq example as an `iff`
or a refutation over `fstat_spec`.  Rocq states the same examples over the
CHECKER, `check_syscall … = CheckReject`, and that is a different claim: it
says the executable acceptor computes the verdict, on these bytes, in one
`vm_compute`.  The two agree by the checkers' soundness and completeness
lemmas, but those proofs are what linux-process-semantics@ff0313ba4f:AGENTS.md says the proofs cannot check —
a spec and a checker altered the same wrong way still agree — so the
concrete answers are pinned on the checker too, from outside.  The
fixtures are that file's, imported, bar the six one-byte variants of
`stat_truthful` the section after the `open`s adds for pins that file has
no use for; nothing is redefined here.

WHY THE CHECKERS AND NOT `check_syscall`.  Rocq's examples enter through
the dispatcher, which decodes each arm's registers from the table, so a
transposed register in an arm is caught where the registers are named.
The new `V_Fs_Stat` section pins the registrations through the real table;
the checker-level discussion here describes the pins preceding that section.
The arms that read
the registers through `in_arg` — for all three the descriptor from
argument 0 through `fd32`, its low 32 bits; for `newfstatat` the pathname
pointer from argument 1 and the flag word from argument 3 through
`flag32`, its `statbuf` in argument 2 never read; for `newfstat` `statbuf`
from argument 1 (Rocq's `arm_readlinkat`, `arm_newfstatat` and `arm_fstat`
in `Checks/Sys/Dispatch.v`) — are built at that registration.
So every pin here applies a checker to its register values directly, in
the kernel's register order (fs/stat.c, Linux v6.18.46: dfd first for
readlinkat, whose other three registers the spec never reads; dfd,
filename and flag for newfstatat, whose statbuf it never writes; fd and
statbuf for newfstat), with the offered effect and the fixture of the Rocq
example it twins.  Where a pin passes a `SyscallInput`, the values beside
it are the ones the arm would decode from that input's own registers, so
no pin hands a checker an argument its fixture contradicts — the
descriptor is the fixture's register 0, which `fd32` fixes, and the flag
its register 3.  What these pins cannot see is a transposed register in
an arm; that fact is the registration's to pin, beside the arm it is
about.  `tools/check_lean_cases_parity.py` pairs a Cases file with the
Rocq file at its mirrored path and none sits at this one, so this file is
listed `unmirrored` — a status, not a finding —; the Rocq example each one
twins is named in its prose.

WHICH ROCQ EXAMPLES ARE NOT PORTED.
`fstat_pin_dies_with_the_file` and `fstat_pin_survives_a_rewrite` are
about `State.with_fs`, not about a checker, and the spec's Cases file
already twins them.

HOW THE PROOFS RUN.  `check_norm` is one `simp only` pass: the fixture
readings the spec's Cases file registers under `sys_simp`, the checkers'
own definitions, `Prelude`'s two acceptors and the effect wrapper, with
every closed gate decided.  A concrete `check_*` call reduces to its
verdict, and the theorem holds when that verdict is the one stated; a
residue is reported, not closed by another tactic, with one exception:
`check_fstat_pinned_f_leaves_g_unpinned` rewrites one fixture reading,
`size0_ifchr_zero`, between two passes, because `check_norm` cannot
decide `stat_size_ok 0 stat_ifchr_zero` under the fixture's
`@[irreducible]`, and that reading is itself a `decide` stated beside
the pin.  `Model` has no `DecidableEq`, so nothing here is `decide`d
whole. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Stat

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Stat
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Stat
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## Fixtures this file adds

Six records the spec's Cases file has no use for, each `stat_truthful`
with one byte or one bit changed, and their predicate readings decided by
the kernel and handed to `check_norm` below (a reading only these pins
use lives beside them).  Three poison the LAST byte of a
padding member where the spec's Cases file poisons the first, so a
one-byte-short width in `Uapi`'s `ST_PAD1_OFF`, `ST_PAD2_OFF` or
`ST_UNUSED45_OFF` read — bytes 47, 63 and 127 going unchecked — fails a
pin here instead of passing every pin in the tree; two set the byte just
outside each of those members, the controls that show the refusals are the
padding's and not the neighbourhood's.  The sixth sets a bit in the half
of `st_mode` no `umode_t` reaches. -/

/-- `stat_truthful` with byte 47, the last of `__pad1`, nonzero. -/
@[irreducible] def stat_pad1_last_poisoned : List byte :=
  stat_truthful.take 47 ++ Z_to_le_bytes 1 1 ++ stat_truthful.drop 48
/-- Byte 63, the last of `__pad2`, nonzero. -/
@[irreducible] def stat_pad2_last_poisoned : List byte :=
  stat_truthful.take 63 ++ Z_to_le_bytes 1 1 ++ stat_truthful.drop 64
/-- Byte 127, the last of `__unused5`, nonzero. -/
@[irreducible] def stat_unused5_last_poisoned : List byte :=
  stat_truthful.take 127 ++ Z_to_le_bytes 1 1
/-- Byte 59, the high byte of `st_blksize`, the member before `__pad2`. -/
@[irreducible] def stat_blksize_high_byte : List byte :=
  stat_truthful.take 59 ++ Z_to_le_bytes 1 1 ++ stat_truthful.drop 60
/-- Byte 119, the high byte of `st_ctime_nsec`, the member before `__unused4`. -/
@[irreducible] def stat_ctime_nsec_high_byte : List byte :=
  stat_truthful.take 119 ++ Z_to_le_bytes 1 1 ++ stat_truthful.drop 120
/-- `S_IFREG` in the low half of `st_mode` and bit 16 set above it. -/
@[irreducible] def stat_high_mode_bit : List byte :=
  stat_of 4711 (S_IFREG + 0x10000) 9 8 1700000000

/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `check_norm`. -/
theorem wf_pad1_last_poisoned : stat_buf_wf stat_pad1_last_poisoned = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `check_norm`. -/
theorem wf_pad2_last_poisoned : stat_buf_wf stat_pad2_last_poisoned = false := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `check_norm`. -/
theorem wf_unused5_last_poisoned : stat_buf_wf stat_unused5_last_poisoned = false := by
  decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `check_norm`. -/
theorem wf_blksize_high_byte : stat_buf_wf stat_blksize_high_byte = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `check_norm`. -/
theorem wf_ctime_nsec_high_byte : stat_buf_wf stat_ctime_nsec_high_byte = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `check_norm`. -/
theorem wf_high_mode_bit : stat_buf_wf stat_high_mode_bit = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `check_norm`. -/
theorem size9_blksize_high_byte : stat_size_ok 9 stat_blksize_high_byte = true := by decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `check_norm`. -/
theorem size9_ctime_nsec_high_byte : stat_size_ok 9 stat_ctime_nsec_high_byte = true := by
  decide +kernel
/-- model: a `Uapi` predicate on a struct fixture, decided by the kernel; a rewrite for `check_norm`. -/
theorem size9_high_mode_bit : stat_size_ok 9 stat_high_mode_bit = true := by decide +kernel

/-- The checker's evaluation on a concrete call: fixture readings, checker
definitions, acceptors, wrapper, and every closed gate decided. -/
syntax "check_norm" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| check_norm $[$loc]?) =>
    `(tactic| simp +decide only [sys_simp, ↓reduceIte, reduceCtorEq,
        check_readlinkat, check_newfstatat, check_fstat, check_fstat_file, check_fstat_chrdev,
        check_fstat_devnull, check_fstat_urandom, check_fstat_deliver, check_fstat_deliver_by,
        check_ret_only, check_ret_only_copyins, clear_copyins, access_ranges_eqb, with_copyins,
        statpin_lookup, List.append_nil, List.length_nil,
        wf_pad1_last_poisoned, wf_pad2_last_poisoned, wf_unused5_last_poisoned,
        wf_blksize_high_byte, wf_ctime_nsec_high_byte, wf_high_mode_bit,
        size9_blksize_high_byte, size9_ctime_nsec_high_byte, size9_high_mode_bit,
        Bool.false_eq_true, Bool.not_false, Bool.not_true, Bool.and_self, Bool.and_true,
        Bool.true_and, Bool.and_false, Bool.false_and] $[$loc]?)

/-! ## readlinkat (78)

Rocq keeps no checker example for `readlinkat`; its checker is pinned
here because one that only ever declined would still close its four
lemmas over a spec that only ever declined, and `readlinkat_spec` does
not: under `AT_FDCWD` it answers. -/

/-- Under `AT_FDCWD` the bare -EINVAL return is accepted, with the model
unchanged: `do_readlinkat`'s `else` arm (fs/stat.c:592-594, v6.18.46) for
a name that is not a symlink, which nothing in the modeled image is.
kernel: fs/stat.c:do_readlinkat; fs/namei.c:path_init@v6.18.46 -/
theorem check_readlinkat_einval_accepted (m : Model) :
    check_readlinkat (fd32 AT_FDCWD) (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m [] := by
  check_norm

/-- A kernel reporting the link read — a positive return — is refused.
kernel: fs/stat.c:do_readlinkat; fs/namei.c:path_init@v6.18.46 -/
theorem check_readlinkat_success_rejected (m : Model) :
    check_readlinkat (fd32 AT_FDCWD) (mkEffect 7 [] []) m = CheckReject := by
  check_norm

/-- A zero return — a kernel claiming a zero-length target — is refused
too: a count is `vfs_readlink`'s answer (fs/stat.c:590, v6.18.46) for a
link the spec's commitment (linux-process-semantics@ff0313ba4f:bugs/readlinkat-path-not-interpreted.md) says
nothing in the image is.  `tests/readlinkat_dirfd.c` mutates to this lie
(`ret=0 -- ok`).
kernel: fs/stat.c:do_readlinkat; fs/namei.c:path_init@v6.18.46 -/
theorem check_readlinkat_zero_return_rejected (m : Model) :
    check_readlinkat (fd32 AT_FDCWD) (mkEffect 0 [] []) m = CheckReject := by
  check_norm

/-- -EBADF under `AT_FDCWD` is a lie the kernel cannot tell: `path_init`
takes the cwd branch for `AT_FDCWD` (fs/namei.c:2590-2604, v6.18.46) and
its -EBADF (:2611) sits on the other branch.
kernel: fs/stat.c:do_readlinkat; fs/namei.c:path_init@v6.18.46 -/
theorem check_readlinkat_ebadf_rejected (m : Model) :
    check_readlinkat (fd32 AT_FDCWD) (mkEffect (errno_ret EBADF) [] []) m = CheckReject := by
  check_norm

/-- …and so is -ENOENT.  This one is NOT a kernel lie for a positive
`bufsiz`: Linux answers -ENOENT for a name that resolves to nothing
(`do_readlinkat`'s lookup, fs/stat.c:576-579, v6.18.46, through
`filename_lookup`, fs/namei.c:2697-2705), and
the spec, which never reads `bufsiz`, commits to -EINVAL without reading
the name, so the checker refuses a conforming trace here.  (With
`bufsiz <= 0` the kernel answers -EINVAL at fs/stat.c:571-572, v6.18.46,
before any lookup, and the refusal is the kernel's own.)  That is the false rejection
linux-process-semantics@ff0313ba4f:bugs/readlinkat-path-not-interpreted.md records; the pin fixes the
checker's answer so that the bug entry and the code cannot drift apart.
model: the spec's -EINVAL-without-reading commitment; see
linux-process-semantics@ff0313ba4f:bugs/readlinkat-path-not-interpreted.md -/
theorem check_readlinkat_enoent_rejected (m : Model) :
    check_readlinkat (fd32 AT_FDCWD) (mkEffect (errno_ret ENOENT) [] []) m = CheckReject := by
  check_norm

/-- …and so is the right errno beside a write: an error return copies
nothing out.
kernel: fs/stat.c:do_readlinkat; fs/namei.c:path_init@v6.18.46 -/
theorem check_readlinkat_einval_with_write_rejected (m : Model) :
    check_readlinkat (fd32 AT_FDCWD) (mkEffect (errno_ret EINVAL) [(0x3000, [0])] []) m
      = CheckReject := by
  check_norm

/-- …and so is a copy-in ledger beside it: `readlinkat_spec` reads no user
byte on this arm and records none, so `check_ret_only`'s empty-ledger
demand refuses a ledger of any length.  For a positive `bufsiz` Linux does
read the name before it answers (`getname_flags`, fs/namei.c:157,
v6.18.46), and the spec's refusal to charge that read is the same
commitment as the -ENOENT refusal above; for `bufsiz <= 0` it reads
nothing (fs/stat.c:571-572) and the empty ledger is the kernel's.  This
pin fixes the commitment's checker-level shape.
model: the spec's -EINVAL-without-reading commitment; see
linux-process-semantics@ff0313ba4f:bugs/readlinkat-path-not-interpreted.md -/
theorem check_readlinkat_einval_with_copyin_rejected (m : Model) :
    check_readlinkat (fd32 AT_FDCWD)
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret EINVAL) [] [])) m
      = CheckReject := by
  check_norm

/-- Any other dirfd is declined, whatever the kernel answered: the spec
does not interpret a directory descriptor here.
kernel: fs/stat.c:do_readlinkat; fs/namei.c:path_init@v6.18.46 -/
theorem check_readlinkat_other_dirfd_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_readlinkat 3 eff m = CheckUnmodeled := by
  check_norm

/-- The register as the kernel receives it — `AT_FDCWD` sign-extended to
64 bits — is NOT `AT_FDCWD32`, and the checker declines it: the `fd32`
truncation of register 0 is the registering arm's, not this checker's (the
header above), and this pin fixes that division.  It is not what catches
an arm that forgets the truncation — that arm hands this register through
and gets exactly this decline, so what goes red is `tests/readlinkat_dirfd.c`
(its `conform -- ok` case first), once V-Fs-Stat replays it through the Lean
arm: Linux reads the `int dfd` (fs/stat.c:563, v6.18.46) and names the cwd.
kernel: fs/stat.c:do_readlinkat; fs/namei.c:path_init@v6.18.46 -/
theorem check_readlinkat_untruncated_register_is_unmodeled (eff : SyscallEffect) (m : Model) :
    check_readlinkat AT_FDCWD eff m = CheckUnmodeled := by
  check_norm

/-! ## newfstatat (79): the pathname's copy-in is charged

Rocq's `newfstatat_pathname_copyin_is_charged`, one conjunct per theorem.
Rocq's prose says why a probe cannot pin this: the harness builds the
ledger it supplies by calling the extracted `cstr_access_len_aux`, so both
sides of that comparison are the model's; only a literal range written
down here separates the checker from one demanding no ledger at all — the
shape `Prelude.check_ret_only` would have accepted. -/

/-- The ledger is not optional: the effect a spec with no `record_copyins`
wrapper would produce is refused.
kernel: fs/stat.c:newfstatat,vfs_fstatat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_ledger_dropped_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (mkEffect (errno_ret ENOENT) [] []) statat_absent_model
      = CheckReject := by
  check_norm

/-- Nor may it over-report: the ledger is exactly `cstr_access_len_aux`'s
count for "f\0", two bytes, and three is refused.  The count is the
MODEL's: Linux's `strncpy_from_user` loads a whole word at an aligned
pointer (linux-process-semantics@ff0313ba4f:bugs/openat-getname-word-at-a-time.md), so its read set here is
eight bytes, and the harness supplies the checker the model's two — the
comparison is model against model, as the section header says.
model: `State.cstr_access_len_aux`'s count, the convention the harness
supplies; see linux-process-semantics@ff0313ba4f:bugs/openat-getname-word-at-a-time.md -/
theorem check_newfstatat_ledger_grown_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 3)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- Nor start anywhere but the pathname pointer.
kernel: fs/stat.c:newfstatat,vfs_fstatat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_ledger_shifted_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2001, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- Control: the truthful ledger IS accepted, so the three refusals above
are refusals of the ledger and not of the errno beside it.
kernel: fs/stat.c:newfstatat,vfs_fstatat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_truthful_ledger_accepted :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  check_norm

/-- …and a success on the absent file is refused, with the truthful ledger
beside it: the refusal is the errno's.
kernel: fs/stat.c:newfstatat,vfs_fstatat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_absent_success_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect 0 [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- -EFAULT for a readable name of an absent file is refused: the copy at
fs/namei.c:157 (v6.18.46) succeeded, so `getname_flags` returns the name
and -ENOENT is `filename_lookup`'s.  `tests/newfstatat_spec.c` mutates to
this lie (`ret=-EFAULT -- absent`).
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/stat.c:vfs_fstatat; fs/namei.c:getname_flags,filename_lookup,path_init@v6.18.46 -/
theorem check_newfstatat_absent_efault_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret EFAULT) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- -EBADF for it is refused: under `AT_FDCWD` `path_init` takes the cwd
(fs/namei.c:2590-2604, v6.18.46) and its -EBADF (:2611) is never reached.
kernel: fs/stat.c:newfstatat,vfs_fstatat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_absent_ebadf_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret EBADF) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- A file the image holds is declined, whatever was answered: the spec
does not build the struct for a path, and the checker declines with it
rather than guessing.
kernel: fs/stat.c:newfstatat,vfs_fstatat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_existing_file_is_unmodeled (eff : SyscallEffect) :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0 eff statat_exists_model
      = CheckUnmodeled := by
  check_norm

/-- A flag bit no stat flag uses is declined, and the pathname is never
read.  Linux answers -EINVAL for it whatever the name: `vfs_fstatat`
(fs/stat.c:370, v6.18.46) fetches the name FIRST, but the errno that fetch
stashes surfaces only in `filename_lookup`, after `vfs_statx` (:348-350)
has tested the flag mask — so the flag is the errno's PRIORITY, not the
kernel's chronology.  The spec declines rather than answering, so no
effect is accepted and none is refused.
kernel: fs/stat.c:newfstatat,vfs_fstatat,vfs_statx; fs/namei.c:path_init@v6.18.46 -/
theorem check_newfstatat_unknown_flag_is_unmodeled (eff : SyscallEffect) :
    check_newfstatat (statat_call AT_FDCWD 0x1 path_f) (fd32 AT_FDCWD) 0x2000 0x1 eff
        statat_absent_model
      = CheckUnmodeled := by
  check_norm

/-- `AT_EMPTY_PATH` (0x1000) is a flag Linux ACCEPTS — it is inside
`vfs_statx`'s mask (fs/stat.c:348-350, v6.18.46) and changes what
`getname_maybe_null` does with the name — and the spec still declines it,
because the model does not interpret it.  The decline is the honest answer
for a flag outside the modeled surface; nothing here claims a kernel error.
kernel: fs/stat.c:newfstatat,vfs_fstatat,vfs_statx; fs/namei.c:path_init@v6.18.46 -/
theorem check_newfstatat_empty_path_flag_is_unmodeled (eff : SyscallEffect) :
    check_newfstatat (statat_call AT_FDCWD 0x1000 path_f) (fd32 AT_FDCWD) 0x2000 0x1000 eff
        statat_absent_model
      = CheckUnmodeled := by
  check_norm

/-! ## fstat (80): the delivered `struct stat`

Rocq's prose for this section: the refusing direction needs a kernel
behaving inadmissibly — one reporting a length its own S_IFREG contradicts,
scribbling `cp_new_stat`'s cleared padding, naming no file type, or
changing a file's inode between two stats — and no Linux does any of those,
so no probe and no `--mutate` operator reaches them.  The accepting
controls beside them are what attribute each refusal to the member it
names rather than to the address, the width or the return value. -/

/-! ### The accepting controls -/

/-- Rocq's `fstat_first_answer_pins`: the first stat of a file is where its
identity enters the model — the answer is accepted and BECOMES the pin.
kernel: fs/stat.c:vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_first_answer_pins :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_truthful)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_truthful fstat_model) [] := by
  check_norm

/-- Rocq's `fstat_character_device_answer_admitted`: the model does NOT
claim the file is regular.  S_IFCHR with `st_size` 0 — the true answer for
the character device linux-process-semantics@ff0313ba4f:bugs/fs-paths-assumed-regular-files.md exhibits — is
accepted; this is what would fail if `stat_size_ok`'s implication were
strengthened to an assertion.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_character_device_answer_accepted :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_ifchr_zero)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_ifchr_zero fstat_model) [] := by
  check_norm

/-! ### The read-write descriptor answers as the other file kinds do

A stat reads the INODE: neither `f_mode` nor `f_flags` is a member of
`struct stat` (`cp_new_stat`/`generic_fillattr`, fs/stat.c:88-106 and
:470-507, Linux v6.18.46, commit 1f99e9ab748f), so how a descriptor was
opened is not something a stat can report.  The accepting half and the
rejecting half are both here, so the pair attributes the answer to the
arm rather than to the checker being lax about a kind it does not
recognise. -/

/-- Rocq's `fstat_read_write_fd_answers_as_a_file`: `FdFileRW` gets the
SAME answer as `FdFile` does above, from the same `check_fstat_file`
under the same implication, and pins it the same way.
kernel: fs/stat.c:vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_read_write_fd_answers_as_a_file :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_truthful)] []) fstat_model_rw
      = CheckOk (with_statpin fstat_path stat_truthful fstat_model_rw) [] := by
  check_norm

/-- Rocq's `fstat_read_write_wrong_size_rejected`: the length obligation
BITES through the read-write descriptor too.  Eight bytes under the
kernel's own S_IFREG where the map holds nine: inadmissible, exactly as
for `FdFile`.  Without this the pin above would pass just as happily if
the arm declined, since a decline is not a rejection.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_read_write_wrong_size_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_short_size)] []) fstat_model_rw
      = CheckReject := by
  check_norm

/-! ### What the length obligation refuses -/

/-- Rocq's `fstat_wrong_size_under_ifreg_rejected`: eight bytes where the
map holds nine, under the kernel's own S_IFREG.  Paired with the control
above, this attributes the refusal to the length rather than to the type.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_wrong_size_under_ifreg_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_short_size)] []) fstat_model
      = CheckReject := by
  check_norm

/-- Rocq's `fstat_stale_size_after_growth_rejected`: a file that GREW must
report the new length.  The pin is not what settles this, but it is where
the two halves meet — the length tracks the map, the identity does not.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_stale_size_after_growth_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_truthful)] [])
        fstat_model_grown_pinned
      = CheckReject := by
  check_norm

/-- Rocq's `fstat_grown_size_admitted`: the new length under the old pin is
accepted, and the pin stays.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_grown_size_accepted :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_grown)] []) fstat_model_grown_pinned
      = CheckOk fstat_model_grown_pinned [] := by
  check_norm

/-! ### What the padding and the type bits refuse -/

/-- Rocq's `fstat_nonzero_pad1_rejected`: `cp_new_stat` clears the whole
struct through `INIT_STRUCT_STAT_PADDING` (fs/stat.c:483, v6.18.46) and
then assigns the members, so no assignment covers `__pad1` and it is
delivered as zero.  One nonzero byte there is a kernel this model refuses.
kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem check_fstat_nonzero_pad1_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_pad1_poisoned)] []) fstat_model
      = CheckReject := by
  check_norm

/-- Rocq's `fstat_nonzero_unused45_rejected`: the same for `__unused4` and
`__unused5`.
kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem check_fstat_nonzero_unused45_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_unused45_poisoned)] []) fstat_model
      = CheckReject := by
  check_norm

/-- The LAST byte of each padding member is refused too — 47 for `__pad1`,
63 for `__pad2`, 127 for `__unused5` (include/uapi/asm-generic/stat.h:24-45,
v6.18.46): `INIT_STRUCT_STAT_PADDING` (fs/stat.c:466-467, applied at :483)
is a memset over the whole struct, and a `Uapi` read one byte short of a
member's width would pass the first-byte pins above and fail here.
kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem check_fstat_nonzero_pad1_last_byte_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_pad1_last_poisoned)] []) fstat_model
      = CheckReject := by
  check_norm

/-- kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem check_fstat_nonzero_pad2_last_byte_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_pad2_last_poisoned)] []) fstat_model
      = CheckReject := by
  check_norm

/-- kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem check_fstat_nonzero_unused5_last_byte_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_unused5_last_poisoned)] []) fstat_model
      = CheckReject := by
  check_norm

/-- Controls, one byte outside each of those members: a nonzero high byte
of `st_blksize` (byte 59, `generic_fillattr` fs/stat.c:105, v6.18.46) and
of `st_ctime_nsec` (byte 119, :96-103) are members the kernel fills, so the
records are accepted and pin — the three refusals above are the padding's.
The two values are not ones `generic_fillattr` writes — a `st_blksize` that
is no power of two, where `i_blocksize` is `1 << i_blkbits`
(include/linux/fs.h:931-934, v6.18.46; a filesystem's own `getattr`, XFS's
`xfs_stat_blksize` in fs/xfs/xfs_iops.c:548-566 for one, may report another
width, but the modeled image has no such filesystem), and a nanosecond field
past 2^32, which no inode time holds (`u32` nanoseconds,
include/linux/fs.h:831-833) — so these acceptances are also over-admissions
of the class the `st_mode` pin at the end of this file writes down; here they
serve as controls only.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_blksize_high_byte_accepted :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_blksize_high_byte)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_blksize_high_byte fstat_model) [] := by
  check_norm

/-- kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_ctime_nsec_high_byte_accepted :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_ctime_nsec_high_byte)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_ctime_nsec_high_byte fstat_model) [] := by
  check_norm

/-- Rocq's `fstat_all_zero_struct_rejected`: the shape a kernel that wrote
nothing and said it did would produce, refused by `st_mode` naming no file
type.  Without that conjunct it would be accepted — the padding is zero,
the width is right, and a zero `st_mode` is not S_IFREG so the length
obligation would not apply.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_all_zero_struct_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, zero_stat)] []) fstat_model
      = CheckReject := by
  check_norm

/-- Rocq's `fstat_impossible_type_rejected`: a type word that is none of the
seven — every S_IFMT bit set, which no inode holds.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_impossible_type_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_ifmt_type)] []) fstat_model
      = CheckReject := by
  check_norm

/-! ### The pin: two stats of one file cannot disagree -/

/-- Rocq's `fstat_pinned_repeat_admitted`: once pinned, the same answer is
accepted again, and the model is handed back as it was.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_pinned_repeat_accepted :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_truthful)] []) fstat_model_pinned
      = CheckOk fstat_model_pinned [] := by
  check_norm

/-- Rocq's `fstat_pinned_inode_defector_rejected`: a later stat differing
in `st_ino` alone is refused for disagreeing with the record.  That is the
whole content of "a file keeps its inode for the life of a run", and the
conjunct a per-call `choose` would have dropped.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_pinned_inode_defector_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_other_inode)] []) fstat_model_pinned
      = CheckReject := by
  check_norm

/-- Rocq's `fstat_inode_defector_is_itself_admissible_first`: the same
struct is accepted as a FIRST answer, so the refusal above is about the
record and not about the number.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_inode_defector_is_itself_accepted_first :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_other_inode)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_other_inode fstat_model) [] := by
  check_norm

/-- Rocq's `fstat_pinned_new_times_and_blocks_admitted`: the members the
pin does not hold, pinned as a NON-refusal.  New timestamps and a new block
count against the same pin are accepted — every read and write moves them.
Without this `stat_stable_eqb` could be widened to the whole buffer and
every other pin here would still hold.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_pinned_new_times_and_blocks_accepted :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_new_times)] []) fstat_model_pinned
      = CheckOk fstat_model_pinned [] := by
  check_norm

/-! ### The write itself: width, address and the empty copy-in ledger -/

/-- Rocq's `fstat_short_struct_rejected`: the copy is `cp_new_stat`'s single
128-byte copy_to_user (fs/stat.c:506, v6.18.46); 127 bytes is not a short
answer this model has a name for.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_short_struct_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_short127)] []) fstat_model
      = CheckReject := by
  check_norm

/-- Rocq's `fstat_shifted_write_rejected`: it lands at `statbuf`, not one
byte past it.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_shifted_write_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4097, stat_truthful)] []) fstat_model
      = CheckReject := by
  check_norm

/-- Rocq's `fstat_forged_copyin_rejected`: `fstat` takes its descriptor in
a register and reads no user byte, so there is no copy_from_user on the
path and the ledger must be empty.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_forged_copyin_rejected :
    check_fstat fstat_input 3 4096
        (with_copyins [(4096, 128)] (mkEffect 0 [(4096, stat_truthful)] [])) fstat_model
      = CheckReject := by
  check_norm

/-- Two writes where the kernel makes one: refused on the shape of the
effect before any byte is looked at.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_two_writes_rejected :
    check_fstat fstat_input 3 4096
        (mkEffect 0 [(4096, stat_truthful), (4224, stat_truthful)] []) fstat_model
      = CheckReject := by
  check_norm

/-! ### The destination, in the three bands -/

/-- Rocq's `fstat_access_ok_fault`: `access_ok` refuses the 128-byte range
at the top of the address space — copy_to_user's own gate, which fires
before a byte moves, so -EFAULT is exact and the model is unchanged.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_access_ok_fault :
    check_fstat (fstat_call 3 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) 3 (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EFAULT) [] []) fstat_model
      = CheckOk fstat_model [] := by
  check_norm

/-- …and a delivery into that range is refused: the gate fired.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_access_ok_delivery_rejected :
    check_fstat (fstat_call 3 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) 3 (Z_to_bv 64 (2 ^ 63))
        (mkEffect 0 [(Z_to_bv 64 (2 ^ 63), stat_truthful)] []) fstat_model
      = CheckReject := by
  check_norm

/-- Rocq's `fstat_one_byte_short_is_unmodeled`: a range `access_ok` admits
but memory does not wholly back is declined rather than faulted —
copy_to_user would commit a prefix and then answer -EFAULT, and the model
cannot say how long that prefix is.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_one_byte_short_is_unmodeled :
    check_fstat fstat_input_short 3 4096 (mkEffect 0 [(4096, stat_truthful)] []) fstat_model
      = CheckUnmodeled := by
  check_norm

/-! ### The descriptor -/

/-- A descriptor the table does not hold is -EBADF, from `vfs_fstat`
(fs/stat.c:279-280, v6.18.46) before anything is read or written; the
model is unchanged.
kernel: fs/stat.c:vfs_fstat@v6.18.46 -/
theorem check_fstat_ebadf_accepted :
    check_fstat (fstat_call 12345 4096 stat_out) 12345 4096 (mkEffect (errno_ret EBADF) [] [])
        fstat_model
      = CheckOk fstat_model [] := by
  check_norm

/-- …and a delivery on a descriptor the table does not hold is refused.
kernel: fs/stat.c:vfs_fstat@v6.18.46 -/
theorem check_fstat_ebadf_delivery_rejected :
    check_fstat (fstat_call 12345 4096 stat_out) 12345 4096 (mkEffect 0 [(4096, stat_truthful)] [])
        fstat_model
      = CheckReject := by
  check_norm

/-- A descriptor opened for writing answers as the read-only one does: a
stat reads the inode, and neither `f_mode` nor `f_flags` is a member of
`struct stat`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_write_fd_answers_as_a_file :
    check_fstat (fstat_call 9 4096 stat_out) 9 4096 (mkEffect 0 [(4096, stat_truthful)] [])
        fstat_kinds_model
      = CheckOk (with_statpin fstat_path stat_truthful fstat_kinds_model) [] := by
  check_norm

/-- The kinds the spec declines are declined by the checker whatever was
answered: a channel, a directory, a socket, a pipe end.
kernel: fs/stat.c:vfs_fstat,vfs_getattr@v6.18.46 -/
theorem check_fstat_channel_is_unmodeled (eff : SyscallEffect) :
    check_fstat (fstat_call 0 4096 stat_out) 0 4096 eff fstat_kinds_model = CheckUnmodeled := by
  check_norm

/-- kernel: fs/stat.c:vfs_fstat,vfs_getattr@v6.18.46 -/
theorem check_fstat_dir_is_unmodeled (eff : SyscallEffect) :
    check_fstat (fstat_call 5 4096 stat_out) 5 4096 eff fstat_kinds_model = CheckUnmodeled := by
  check_norm

/-- kernel: fs/stat.c:vfs_fstat,vfs_getattr@v6.18.46 -/
theorem check_fstat_socket_is_unmodeled (eff : SyscallEffect) :
    check_fstat (fstat_call 6 4096 stat_out) 6 4096 eff fstat_kinds_model = CheckUnmodeled := by
  check_norm

/-- kernel: fs/stat.c:vfs_fstat,vfs_getattr@v6.18.46 -/
theorem check_fstat_pipe_is_unmodeled (eff : SyscallEffect) :
    check_fstat (fstat_call 7 4096 stat_out) 7 4096 eff fstat_kinds_model = CheckUnmodeled := by
  check_norm

/-! ### The unlinked file, and the pin that dies with it -/

/-- Rocq's `fstat_unlinked_path_is_unmodeled`: a descriptor whose path the
map no longer holds is declined.  Linux answers from the surviving inode
with `st_nlink` 0 (`generic_fillattr`, fs/stat.c:82-113, v6.18.46); the
model has no contents to size and no link count to drop.
kernel: fs/stat.c:generic_fillattr,cp_new_stat@v6.18.46 -/
theorem check_fstat_unlinked_path_is_unmodeled (eff : SyscallEffect) :
    check_fstat fstat_input 3 4096 eff fstat_model_unlinked = CheckUnmodeled := by
  check_norm

/-- The order of the two gates, fixed from outside: the unlinked path is
declined BEFORE the buffer is judged, so a buffer at 2^63, which
`access_ok` refuses, still yields the decline and never the -EFAULT that
`cp_new_stat` (fs/stat.c:506, v6.18.46) answers for the surviving inode.
A checker that judged the buffer first would accept -EFAULT here, a real
answer the spec does not accept; `check_fstat_file_sound_ok` refuses a
one-sided swap, and this pin refuses the swap made on both sides.
model: the spec declines an unlinked path ahead of the buffer -/
theorem check_fstat_unlinked_path_precedes_the_buffer (eff : SyscallEffect) :
    check_fstat (fstat_call 3 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) 3 (Z_to_bv 64 (2 ^ 63))
      eff fstat_model_unlinked = CheckUnmodeled := by
  check_norm

/-- Rocq's `fstat_recreated_file_takes_a_new_inode`: with the pin gone, the
file created next at that name may report ANY inode, exactly as a first
stat may.  Read beside `check_fstat_pinned_inode_defector_rejected`, the
same struct against a live pin.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_recreated_file_takes_a_new_inode :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_other_inode)] []) fstat_model_recreated
      = CheckOk (with_statpin fstat_path stat_other_inode fstat_model_recreated) [] := by
  check_norm

/-! ### The receptiveness guard on a pin no run builds

The only writer of a pin is the branch that has just checked its
predicate, so a pin failing `stat_buf_wf` exists in no reachable model.
The checker declines on one all the same, as the spec does: receptiveness
is a statement about every `Model`. -/

/-- kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_malformed_pin_is_unmodeled (eff : SyscallEffect) :
    check_fstat fstat_input 3 4096 eff fstat_model_badpin = CheckUnmodeled := by
  check_norm

/-! ## fstat (80): the character devices

`/dev/null` at fd 4 and `/dev/urandom` at fd 8 of the kinds fixture.  The
arm's predicate is checked beside `stat_buf_wf`: a device answer under a
regular file's type, or with a size, is refused, and so is one device's
record offered for the other. -/

/-- The first stat of `/dev/null` is accepted and pins.
kernel: fs/stat.c:vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_devnull_first_answer_pins :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, devnull_truthful)] [])
        fstat_kinds_model
      = CheckOk (with_statpin devnull_path devnull_truthful fstat_kinds_model) [] := by
  check_norm

/-- `/dev/null` under S_IFREG is refused: the arm's predicate, not only
`stat_buf_wf`, decides.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_devnull_as_regular_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, devnull_as_regular)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- A 100-byte record for `/dev/null` is refused on its width, though the
device predicate would pass it: the two are tested together.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_devnull_short_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, devnull_short100)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- Pinned, `/dev/null` may report new timestamps…
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_devnull_pinned_new_times_accepted :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, devnull_new_times)] [])
        fstat_kinds_model_pinned
      = CheckOk fstat_kinds_model_pinned [] := by
  check_norm

/-- …and not a new inode.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_devnull_pinned_inode_defector_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, devnull_other_inode)] [])
        fstat_kinds_model_pinned
      = CheckReject := by
  check_norm

/-- The first stat of `/dev/urandom` is accepted and pins.
kernel: fs/stat.c:vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_urandom_first_answer_pins :
    check_fstat (fstat_call 8 4096 stat_out) 8 4096 (mkEffect 0 [(4096, urandom_truthful)] [])
        fstat_kinds_model
      = CheckOk (with_statpin urandom_path urandom_truthful fstat_kinds_model) [] := by
  check_norm

/-- `/dev/null`'s record offered for `/dev/urandom` is refused: the device
numbers differ, and the arm's predicate reads `st_rdev`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_urandom_given_devnull_record_rejected :
    check_fstat (fstat_call 8 4096 stat_out) 8 4096 (mkEffect 0 [(4096, devnull_truthful)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- A device pinned under a regular file's record — a model no run builds —
is declined, as the spec declines it.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem check_fstat_devnull_malformed_pin_is_unmodeled (eff : SyscallEffect) :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 eff fstat_kinds_model_badpin_file
      = CheckUnmodeled := by
  check_norm


/-! ## newfstatat (79): two conditions at once

Each pathname fate — empty, too long, faulting, unmapped — is decided by
`getname_flags` (fs/namei.c:136-216, v6.18.46) inside `vfs_fstatat`
(fs/stat.c:365-379) BEFORE the dirfd is looked at, and the errno is only
stashed in the `filename`: `vfs_statx` (fs/stat.c:341-363) tests the flag
mask first, then `filename_lookup` (fs/namei.c:2697-2705) hands the stashed
errno back before `path_init` (:2540-2645) resolves the dfd.  So under a
dirfd the spec declines, a pathname that fails on its own is still
answered, with the ledger `read_cstr` charged for it.  A checker with the
dirfd test ahead of the pathname would decline every one of these; the
accepting pins detect that swap and the refusals show the errno beside the
ledger is what is accepted, not the ledger alone. -/

/-- The empty pathname under dirfd 5: -ENOENT, the dirfd never consulted
(`getname_flags` fs/namei.c:167-171, `filename_lookup` :2702-2703,
`path_init` :2590 onwards, v6.18.46), and the model's one byte charged —
the NUL `cstr_access_len_aux` counts, where the kernel's aligned read is
the word (linux-process-semantics@ff0313ba4f:bugs/openat-getname-word-at-a-time.md).
kernel: fs/namei.c:getname_flags,filename_lookup,path_init; fs/stat.c:vfs_fstatat@v6.18.46 -/
theorem check_newfstatat_empty_path_preempts_dirfd_accepted :
    check_newfstatat (statat_call 5 0 path_empty) 5 0x2000 0
        (with_copyins [(0x2000, 1)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  check_norm

/-- ...and -EBADF there is a lie: `path_init`'s -EBADF (fs/namei.c:2611,
v6.18.46) is never reached for a name `getname_flags` already refused.
kernel: fs/namei.c:getname_flags,filename_lookup,path_init; fs/stat.c:vfs_fstatat@v6.18.46 -/
theorem check_newfstatat_empty_path_ebadf_rejected :
    check_newfstatat (statat_call 5 0 path_empty) 5 0x2000 0
        (with_copyins [(0x2000, 1)] (mkEffect (errno_ret EBADF) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- ...and success there is a lie beside the truthful ledger: the empty
name is refused by `getname_flags` (fs/namei.c:167-171, v6.18.46) before
anything could be stat'ed.
kernel: fs/namei.c:getname_flags,filename_lookup,path_init; fs/stat.c:vfs_fstatat@v6.18.46 -/
theorem check_newfstatat_empty_path_success_rejected :
    check_newfstatat (statat_call 5 0 path_empty) 5 0x2000 0
        (with_copyins [(0x2000, 1)] (mkEffect 0 [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- A pathname of `PATH_MAX` bytes without a NUL under dirfd 5:
-ENAMETOOLONG (`getname_flags` fs/namei.c:207-211, v6.18.46), the whole
4096-byte window charged, the dirfd never consulted.
kernel: fs/namei.c:getname_flags,filename_lookup,path_init; fs/stat.c:vfs_fstatat@v6.18.46 -/
theorem check_newfstatat_toolong_preempts_dirfd_accepted :
    check_newfstatat (statat_call 5 0 path_toolong) 5 0x2000 0
        (with_copyins [(0x2000, 4096)] (mkEffect (errno_ret ENAMETOOLONG) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  check_norm

/-- -EBADF for the too-long name is the same lie as for the empty one.
kernel: fs/namei.c:getname_flags,filename_lookup,path_init; fs/stat.c:vfs_fstatat@v6.18.46 -/
theorem check_newfstatat_toolong_ebadf_rejected :
    check_newfstatat (statat_call 5 0 path_toolong) 5 0x2000 0
        (with_copyins [(0x2000, 4096)] (mkEffect (errno_ret EBADF) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- Success for the too-long name is refused with the truthful ledger
beside it, and so is -ENOENT: `getname_flags` returns -ENAMETOOLONG
(fs/namei.c:207-211, v6.18.46) before any lookup could find or miss.
kernel: fs/namei.c:getname_flags,filename_lookup,path_init; fs/stat.c:vfs_fstatat@v6.18.46 -/
theorem check_newfstatat_toolong_success_rejected :
    check_newfstatat (statat_call 5 0 path_toolong) 5 0x2000 0
        (with_copyins [(0x2000, 4096)] (mkEffect 0 [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- kernel: fs/namei.c:getname_flags,filename_lookup,path_init; fs/stat.c:vfs_fstatat@v6.18.46 -/
theorem check_newfstatat_toolong_enoent_rejected :
    check_newfstatat (statat_call 5 0 path_toolong) 5 0x2000 0
        (with_copyins [(0x2000, 4096)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- The too-long name's ledger is exactly `PATH_MAX` bytes: one byte fewer
is refused, so the accepted 4096 above is the charge and not a lower bound.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_newfstatat_toolong_ledger_4095_rejected :
    check_newfstatat (statat_call 5 0 path_toolong) 5 0x2000 0
        (with_copyins [(0x2000, 4095)] (mkEffect (errno_ret ENAMETOOLONG) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- A name whose second byte is unreadable: -EFAULT from
`strncpy_from_user` (lib/strncpy_from_user.c:113-155, v6.18.46), passed up
by `getname_flags` (fs/namei.c:162-165); the model charges two bytes, the
one read and the one that faulted (`cstr_access_len_aux`'s count — the
kernel's word read at this aligned pointer touches neither exactly,
linux-process-semantics@ff0313ba4f:bugs/openat-getname-word-at-a-time.md).
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_runoff_efault_accepted :
    check_newfstatat (statat_input path_runoff) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret EFAULT) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  check_norm

/-- -ENOENT for the runoff name is refused: the name was never read to the
end, so nothing was looked up.
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_runoff_enoent_rejected :
    check_newfstatat (statat_input path_runoff) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- Success for the runoff name is refused, and so is -ENAMETOOLONG: the
fault at the second byte (fs/namei.c:162-165, v6.18.46) precedes both the
lookup and the `PATH_MAX` test at :207-211.
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_runoff_success_rejected :
    check_newfstatat (statat_input path_runoff) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect 0 [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_runoff_enametoolong_rejected :
    check_newfstatat (statat_input path_runoff) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENAMETOOLONG) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- The runoff ledger is two bytes, not one: `cstr_access_len_aux` charges
the faulting byte, and the checker holds the ledger to that count.
model: `State.cstr_access_len_aux`'s count, the convention the harness
supplies; see linux-process-semantics@ff0313ba4f:bugs/openat-getname-word-at-a-time.md -/
theorem check_newfstatat_runoff_ledger_1_rejected :
    check_newfstatat (statat_input path_runoff) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 1)] (mkEffect (errno_ret EFAULT) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- Nothing mapped at the pathname under dirfd 5: -EFAULT, the dirfd never
consulted, and the model's one byte charged — the byte that faulted, where
the kernel's faulting word load records no read at all
(linux-process-semantics@ff0313ba4f:bugs/openat-getname-word-at-a-time.md).
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,filename_lookup,path_init@v6.18.46 -/
theorem check_newfstatat_unmapped_path_preempts_dirfd_accepted :
    check_newfstatat (statat_call 5 0 path_none) 5 0x2000 0
        (with_copyins [(0x2000, 1)] (mkEffect (errno_ret EFAULT) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  check_norm

/-- -EBADF for the unmapped pathname is refused for the same reason.
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,filename_lookup,path_init@v6.18.46 -/
theorem check_newfstatat_unmapped_path_ebadf_rejected :
    check_newfstatat (statat_call 5 0 path_none) 5 0x2000 0
        (with_copyins [(0x2000, 1)] (mkEffect (errno_ret EBADF) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- ...and success for it: nothing was read, so nothing could be found.
kernel: lib/strncpy_from_user.c:strncpy_from_user; fs/namei.c:getname_flags,filename_lookup,path_init@v6.18.46 -/
theorem check_newfstatat_unmapped_path_success_rejected :
    check_newfstatat (statat_call 5 0 path_none) 5 0x2000 0
        (with_copyins [(0x2000, 1)] (mkEffect 0 [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- An unknown flag bit beside a pathname nothing backs: the flag wins.
Linux answers -EINVAL from `vfs_statx` (fs/stat.c:348-350, v6.18.46) before
`filename_lookup` surfaces the stashed -EFAULT; the spec declines the flag,
so the checker declines every effect and charges no read — Linux has read
the name (fs/stat.c:370) by the time `vfs_statx` answers.
kernel: fs/stat.c:vfs_fstatat,vfs_statx; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_unknown_flag_precedes_fault (eff : SyscallEffect) :
    check_newfstatat (statat_call (fd32 AT_FDCWD) 0x1 path_none) (fd32 AT_FDCWD) 0x2000 0x1
        eff statat_absent_model
      = CheckUnmodeled := by
  check_norm

/-- `AT_SYMLINK_NOFOLLOW` (0x100) is inside the modeled flag set: an absent
file is still -ENOENT under it, with the same two-byte ledger.
kernel: fs/stat.c:vfs_fstatat,vfs_statx; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_nofollow_absent_accepted :
    check_newfstatat (statat_call (fd32 AT_FDCWD) 256 path_f) (fd32 AT_FDCWD) 0x2000 256
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  check_norm

/-- -EINVAL under `AT_SYMLINK_NOFOLLOW` is a lie: the flag is in
`vfs_statx`'s mask (fs/stat.c:348-350, v6.18.46).
kernel: fs/stat.c:vfs_fstatat,vfs_statx; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_nofollow_einval_rejected :
    check_newfstatat (statat_call (fd32 AT_FDCWD) 256 path_f) (fd32 AT_FDCWD) 0x2000 256
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret EINVAL) [] [])) statat_absent_model
      = CheckReject := by
  check_norm

/-- A readable relative pathname under a dirfd other than `AT_FDCWD` is
declined for every effect: Linux resolves it from the descriptor
(`path_init` fs/namei.c:2605-2632, v6.18.46) and the model has no
directory descriptors to resolve from.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem check_newfstatat_other_dirfd_is_unmodeled (eff : SyscallEffect) :
    check_newfstatat (statat_call 5 0 path_f) 5 0x2000 0 eff statat_absent_model
      = CheckUnmodeled := by
  check_norm

/-- `.` is declined for every effect: Linux answers from the working
directory (`path_init` fs/namei.c:2590-2604, v6.18.46, then `handle_dots`
:2096), which the flat namespace has no node for.  Whether the dirfd or
the dot is tested first is unobservable here, since both decline.
kernel: fs/namei.c:path_init,handle_dots@v6.18.46 -/
theorem check_newfstatat_dot_is_unmodeled (eff : SyscallEffect) :
    check_newfstatat (statat_input path_dot) (fd32 AT_FDCWD) 0x2000 0 eff statat_absent_model
      = CheckUnmodeled := by
  check_norm

/-- A write smuggled behind the accepted -ENOENT is refused: `cp_new_stat`
runs only on success (fs/stat.c:542-546, v6.18.46), so an erroring
`newfstatat` writes nothing.
kernel: fs/stat.c:newfstatat,vfs_fstatat,cp_new_stat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_smuggled_write_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [(4096, zero_stat)] []))
        statat_absent_model
      = CheckReject := by
  check_norm

/-- A zero-fill smuggled behind it is refused the same way.
kernel: fs/stat.c:newfstatat,vfs_fstatat,cp_new_stat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_smuggled_zeros_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [(4096, 128)]))
        statat_absent_model
      = CheckReject := by
  check_norm

/-- And an unmapping: the effect record's `eff_unmaps` field is matched
against the empty list like every other field, so an unmap beside the
right errno and the right ledger is still refused.
kernel: fs/stat.c:newfstatat,vfs_fstatat,cp_new_stat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_smuggled_unmap_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (SyscallEffect.mkEffectU (errno_ret ENOENT) [] [] [(4096, 4096)] [] [(0x2000, 2)])
        statat_absent_model
      = CheckReject := by
  check_norm

/-- And a pre-effect memory copy, the record's fifth field: `newfstatat`
moves no user memory on an error path (fs/stat.c:542-546, v6.18.46).
kernel: fs/stat.c:newfstatat,vfs_fstatat,cp_new_stat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem check_newfstatat_smuggled_copy_rejected :
    check_newfstatat (statat_input path_f) (fd32 AT_FDCWD) 0x2000 0
        (SyscallEffect.mkEffectU (errno_ret ENOENT) [] [] [] [MemCopy.mkCopy 4096 8192 16]
          [(0x2000, 2)])
        statat_absent_model
      = CheckReject := by
  check_norm

/-! ## fstat (80): effect shapes beside a truthful record

`stat_out` backs the whole 128-byte window (`stat_out_reads`), so on fd 3
`copy_to_user` cannot fail and `cp_new_stat` (fs/stat.c:470-507, v6.18.46)
returns 0 with exactly one write.  Every other shape of the effect record
is a lie, field by field: the return, the write list, the zero-fills, the
unmappings, and the errno a lying kernel might put beside a delivery. -/

/-- A zero return with no write: `cp_new_stat` returns 0 only after the
copy (fs/stat.c:506, v6.18.46).
kernel: fs/stat.c:newfstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_success_without_the_struct_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [] []) fstat_model = CheckReject := by
  check_norm

/-- -EFAULT beside the struct: the only -EFAULT site is the copy itself
(fs/stat.c:506, v6.18.46), which either wrote everything and returned 0 or
wrote nothing the model sees and returned -EFAULT.
kernel: fs/stat.c:newfstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_struct_behind_efault_rejected :
    check_fstat fstat_input 3 4096 (mkEffect (errno_ret EFAULT) [(4096, stat_truthful)] []) fstat_model
      = CheckReject := by
  check_norm

/-- -EFAULT alone on a fully backed buffer: both destination gates pass, so
the EFAULT arm is never reached and the bare errno is a lie.
kernel: fs/stat.c:newfstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_efault_on_backed_statbuf_rejected :
    check_fstat fstat_input 3 4096 (mkEffect (errno_ret EFAULT) [] []) fstat_model
      = CheckReject := by
  check_norm

/-- A zero-fill beside the truthful record: `newfstat` (fs/stat.c:550-560,
v6.18.46) touches user memory only through the one `copy_to_user`.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_zeros_beside_struct_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_truthful)] [(4096, 128)]) fstat_model
      = CheckReject := by
  check_norm

/-- An unmapping beside it, stated on the full record so the `eff_unmaps`
field's position in the pattern is what is tested: a transcription slip
that swapped two empty-list fields would still type-check and would accept
this.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_unmap_beside_struct_rejected :
    check_fstat fstat_input 3 4096
        (SyscallEffect.mkEffectU 0 [(4096, stat_truthful)] [] [(4096, 4096)] [] []) fstat_model
      = CheckReject := by
  check_norm

/-- A pre-effect memory copy beside it — the record's fifth field, the one
the zeros, unmaps and copy-ins pins around it leave untested: `newfstat`
moves user memory through `cp_new_stat`'s one copy out (fs/stat.c:506,
v6.18.46) and nothing else.  The deep review's kill-the-rule pass found a
checker wildcarding this field passed every pin then in the file.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_copy_beside_struct_rejected :
    check_fstat fstat_input 3 4096
        (SyscallEffect.mkEffectU 0 [(4096, stat_truthful)] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        fstat_model
      = CheckReject := by
  check_norm

/-- The same through the device arm: `/dev/null`'s truthful record with a
copy beside it is refused on fd 4.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_devnull_copy_beside_struct_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096
        (SyscallEffect.mkEffectU 0 [(4096, devnull_truthful)] [] []
          [MemCopy.mkCopy 4096 8192 16] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- A 136-byte write: `sizeof(tmp)` at fs/stat.c:506 (v6.18.46) is the
128 bytes of `struct stat` (include/uapi/asm-generic/stat.h), so a longer
write is refused as a shorter one is.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_long_struct_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_long136)] []) fstat_model
      = CheckReject := by
  check_norm

/-- `__pad2`, the four bytes at 60..63 between `st_blksize` and `st_blocks`
(include/uapi/asm-generic/stat.h:35), is zeroed like __pad1
(`INIT_STRUCT_STAT_PADDING`, fs/stat.c:466-467 and :483, v6.18.46) and never
assigned; a nonzero byte there is refused.  The trailing `__unused4` and
`__unused5` words are `check_fstat_nonzero_unused45_rejected`'s.
kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem check_fstat_nonzero_pad2_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_pad2_poisoned)] []) fstat_model
      = CheckReject := by
  check_norm

/-- `st_blksize` is a stable field: `generic_fillattr` (fs/stat.c:105,
v6.18.46) reads `i_blocksize(inode)`, which does not change between two
stats of one inode, so a record that differs from the pin there is refused.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_pinned_blksize_defector_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_other_blksize)] []) fstat_model_pinned
      = CheckReject := by
  check_norm

/-- ...and as a first answer the other block size is accepted and pinned:
the model does not know the block size, it only holds it fixed.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_other_blksize_first_answer_pins :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_other_blksize)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_other_blksize fstat_model) [] := by
  check_norm

/-- An unknown fd AND an unmapped buffer: -EBADF wins, because `newfstat`
(fs/stat.c:550-560, v6.18.46) calls `vfs_fstat` (:279-280) before
`cp_new_stat` ever looks at the buffer.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_ebadf_precedes_efault_accepted :
    check_fstat (fstat_call 12345 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) 12345 (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EBADF) [] []) fstat_model
      = CheckOk fstat_model [] := by
  check_norm

/-- -EFAULT there is the lie a kernel that checked the buffer first would tell.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_ebadf_precedes_efault_rejected :
    check_fstat (fstat_call 12345 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) 12345 (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EFAULT) [] []) fstat_model
      = CheckReject := by
  check_norm

/-! ## fstat (80): two files, and the write descriptor

`fstat_two_files_model` holds "f" (nine bytes, fd 3) and the empty "g"
(fd 4).  The size obligation is per inode (`generic_fillattr` fs/stat.c:95,
v6.18.46) and so is the pin (:89), so a record right for one file is a lie
for the other, and a pin on one is not consulted for the other. -/

/-- fd 4 names the empty "g": "f"'s nine-byte record is refused.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_nine_bytes_on_the_empty_file_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, stat_truthful)] [])
        fstat_two_files_model
      = CheckReject := by
  check_norm

/-- Control: the same record on fd 3 is accepted and pins "f".
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_two_files_f_first_answer_pins :
    check_fstat (fstat_call 3 4096 stat_out) 3 4096 (mkEffect 0 [(4096, stat_truthful)] [])
        fstat_two_files_model
      = CheckOk (with_statpin fstat_path stat_truthful fstat_two_files_model) [] := by
  check_norm

/-- The pin on "f" is consulted for fd 3: a different inode number is
refused (`generic_fillattr` fs/stat.c:89, v6.18.46).
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_two_files_pinned_f_defector_rejected :
    check_fstat (fstat_call 3 4096 stat_out) 3 4096 (mkEffect 0 [(4096, stat_other_inode)] [])
        fstat_two_files_model_pinned_f
      = CheckReject := by
  check_norm

/-- Through a write descriptor the size obligation is the same: fd 9 is
"f" opened for writing, and a record with the wrong `st_size` is refused
(`generic_fillattr` fs/stat.c:95, v6.18.46).
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_write_fd_wrong_size_rejected :
    check_fstat (fstat_call 9 4096 stat_out) 9 4096 (mkEffect 0 [(4096, stat_short_size)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-! ## fstat (80): the character devices, adversarially

`/dev/null` is character device 1:3 and `/dev/urandom` 1:9;
`init_special_inode` (fs/inode.c:2552-2558, v6.18.46) stores the device
number in `i_rdev` and `generic_fillattr` (fs/stat.c:94) reports it.
`st_size` (:95) and `st_blocks` (:106) are copied from the inode the same
way, and are zero for these two nodes because nothing in the image writes
either — the premise `Uapi.stat_chrdev_ok` asserts, argued at
`Uapi.DEVNULL_RDEV`, not a property `generic_fillattr` imposes on a device
node.  Each device's acceptor is its own record and nobody else's. -/

/-- `/dev/null` given `/dev/urandom`'s record: refused on `st_rdev`.
kernel: fs/stat.c:generic_fillattr; fs/inode.c:init_special_inode@v6.18.46 -/
theorem check_fstat_devnull_given_urandom_record_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, urandom_truthful)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- `/dev/null` given a regular file's record: refused on the type bits.
kernel: fs/stat.c:generic_fillattr; fs/inode.c:init_special_inode@v6.18.46 -/
theorem check_fstat_devnull_given_file_record_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, stat_truthful)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- `/dev/urandom` reported as a regular file: refused on the type bits.
kernel: fs/stat.c:generic_fillattr; fs/inode.c:init_special_inode@v6.18.46 -/
theorem check_fstat_urandom_as_regular_rejected :
    check_fstat (fstat_call 8 4096 stat_out) 8 4096 (mkEffect 0 [(4096, urandom_as_regular)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- `/dev/null` with a size: the `st_size` `generic_fillattr` copies
(fs/stat.c:95, v6.18.46) is the inode's, which nothing resizes, and
`Uapi.stat_devnull_ok` holds it at zero.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_devnull_sized_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, devnull_sized)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- Nor blocks: `i_blocks` (fs/stat.c:106, v6.18.46) is copied the same
way and held at zero the same way.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_devnull_blocks_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, devnull_blocks)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- A zero `st_rdev` under `S_IFCHR`: `/dev/null` is 1:3, not 0:0.
kernel: fs/stat.c:generic_fillattr; fs/inode.c:init_special_inode@v6.18.46 -/
theorem check_fstat_devnull_zero_rdev_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, devnull_zero_rdev)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- `/dev/urandom` with a size: refused.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_urandom_sized_rejected :
    check_fstat (fstat_call 8 4096 stat_out) 8 4096 (mkEffect 0 [(4096, urandom_sized)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- `/dev/urandom` with blocks: refused.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_urandom_blocks_rejected :
    check_fstat (fstat_call 8 4096 stat_out) 8 4096 (mkEffect 0 [(4096, urandom_blocks)] [])
        fstat_kinds_model
      = CheckReject := by
  check_norm

/-- Pinned `/dev/urandom`: new timestamps are accepted, the model unmoved
(`generic_fillattr` fs/stat.c:96-103, v6.18.46, reads the live times).
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_urandom_pinned_new_times_accepted :
    check_fstat (fstat_call 8 4096 stat_out) 8 4096 (mkEffect 0 [(4096, urandom_new_times)] [])
        fstat_kinds_model_urandom_pinned
      = CheckOk fstat_kinds_model_urandom_pinned [] := by
  check_norm

/-- Pinned `/dev/urandom`: a new inode number is refused (fs/stat.c:89).
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_urandom_pinned_inode_defector_rejected :
    check_fstat (fstat_call 8 4096 stat_out) 8 4096 (mkEffect 0 [(4096, urandom_other_inode)] [])
        fstat_kinds_model_urandom_pinned
      = CheckReject := by
  check_norm

/-- The two device pins are independent: with `/dev/null` pinned,
`/dev/urandom`'s first answer is accepted and pins its own path.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_urandom_first_beside_devnull_pin :
    check_fstat (fstat_call 8 4096 stat_out) 8 4096 (mkEffect 0 [(4096, urandom_truthful)] [])
        fstat_kinds_model_pinned
      = CheckOk (with_statpin urandom_path urandom_truthful fstat_kinds_model_pinned) [] := by
  check_norm

/-- A device pinned under a SHORT record — one `stat_devnull_ok` accepts
but `stat_buf_wf` does not — is declined for every effect.  This is the
pin that separates the gate `stat_buf_wf b0 && ok b0` from `ok b0` alone.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_devnull_short_pin_is_unmodeled (eff : SyscallEffect) :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 eff fstat_kinds_model_badpin_short
      = CheckUnmodeled := by
  check_norm

/-- `/dev/urandom` pinned under `/dev/null`'s record is declined for every
effect: the pin gate applies the arm's own acceptor to the pinned record.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem check_fstat_urandom_other_device_pin_is_unmodeled (eff : SyscallEffect) :
    check_fstat (fstat_call 8 4096 stat_out) 8 4096 eff fstat_kinds_model_urandom_badpin_devnull
      = CheckUnmodeled := by
  check_norm

/-- The device arm has its own destination gates.  A buffer above the
user range: -EFAULT accepted, the model unmoved (fs/stat.c:506, v6.18.46).
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_devnull_access_ok_fault :
    check_fstat (fstat_call 4 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) 4 (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EFAULT) [] []) fstat_kinds_model
      = CheckOk fstat_kinds_model [] := by
  check_norm

/-- …and a delivery into that range on the device arm is refused, as on
the file arm: the gate fired before a byte moved.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_devnull_access_ok_delivery_rejected :
    check_fstat (fstat_call 4 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) 4 (Z_to_bv 64 (2 ^ 63))
        (mkEffect 0 [(Z_to_bv 64 (2 ^ 63), devnull_truthful)] []) fstat_kinds_model
      = CheckReject := by
  check_norm

/-- A buffer one byte short of backing, on the device arm: declined for
every effect, as on the file arm.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_devnull_one_byte_short_is_unmodeled (eff : SyscallEffect) :
    check_fstat (fstat_call 4 4096 stat_out_short) 4 4096 eff fstat_kinds_model
      = CheckUnmodeled := by
  check_norm

/-- A zero return with no write, on the device arm: refused.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_devnull_success_without_the_struct_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [] []) fstat_kinds_model
      = CheckReject := by
  check_norm

/-- -EFAULT beside the device's own record, on the device arm: refused.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_devnull_struct_behind_efault_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096
        (mkEffect (errno_ret EFAULT) [(4096, devnull_truthful)] []) fstat_kinds_model
      = CheckReject := by
  check_norm


/-! ## The review's kill-the-rule pass

Verdicts a wrong port would still pass with everything above in place:
a nonzero return beside a perfect struct, an errno beside a write on the
fault and bad-fd paths, a ledger beside -EBADF, the two-files model with
"f" pinned, and the grown file with NO pin. -/

/-- A return of 1 beside the truthful struct: `cp_new_stat` returns 0 or
-EFAULT and nothing else (fs/stat.c:506, v6.18.46).  Every accepting pin
above returns 0 and every refusal varies the bytes or the address, so an
acceptor that forgot the return would pass all of them.
kernel: fs/stat.c:newfstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_nonzero_return_beside_struct_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 1 [(4096, stat_truthful)] []) fstat_model
      = CheckReject := by
  check_norm

/-- -EFAULT beside a write into the range the gate refused: the errno is
right and the write is the lie.
kernel: fs/stat.c:newfstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_access_ok_efault_with_write_rejected :
    check_fstat (fstat_call 3 (Z_to_bv 64 (2 ^ 63)) (fun _ => none)) 3 (Z_to_bv 64 (2 ^ 63))
        (mkEffect (errno_ret EFAULT) [(Z_to_bv 64 (2 ^ 63), stat_truthful)] []) fstat_model
      = CheckReject := by
  check_norm

/-- -EBADF beside a write: `vfs_fstat` (fs/stat.c:279-280, v6.18.46)
returns before `cp_new_stat` runs, so nothing is written.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem check_fstat_ebadf_with_write_rejected :
    check_fstat (fstat_call 12345 4096 stat_out) 12345 4096
        (mkEffect (errno_ret EBADF) [(4096, stat_truthful)] []) fstat_model
      = CheckReject := by
  check_norm

/-- -EBADF beside a copy-in ledger: `newfstat` reads no user memory at
all (fs/stat.c:550-560, v6.18.46), so the ledger must be empty.
kernel: fs/stat.c:newfstat,vfs_fstat@v6.18.46 -/
theorem check_fstat_ebadf_with_copyin_rejected :
    check_fstat (fstat_call 12345 4096 stat_out) 12345 4096
        (with_copyins [(4096, 128)] (mkEffect (errno_ret EBADF) [] [])) fstat_model
      = CheckReject := by
  check_norm

/-- With "f" pinned, fd 4 (the empty "g") still refuses "f"'s nine-byte
record: the size obligation is "g"'s own (`generic_fillattr` fs/stat.c:95,
v6.18.46), and the pin on "f" plays no part.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_pinned_f_does_not_excuse_g_rejected :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, stat_truthful)] [])
        fstat_two_files_model_pinned_f
      = CheckReject := by
  check_norm

/-- `stat_size_ok` ignores the length of a record that is not a regular
file, so the empty "g" accepts the zero-size character-device fixture.
model: `stat_size_ok 0 stat_ifchr_zero` computed -/
theorem size0_ifchr_zero : stat_size_ok 0 stat_ifchr_zero = true := by
  decide +kernel

/-- With "f" pinned, fd 4's FIRST record is accepted on its own terms and
pins "g", not "f": `statpin_lookup` keys on the path
(`generic_fillattr` fs/stat.c:89, v6.18.46, reports each inode's own
number).  This is the checker-level witness that a pin on one file is not
consulted for another.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_pinned_f_leaves_g_unpinned :
    check_fstat (fstat_call 4 4096 stat_out) 4 4096 (mkEffect 0 [(4096, stat_ifchr_zero)] [])
        fstat_two_files_model_pinned_f
      = CheckOk (with_statpin [103] stat_ifchr_zero fstat_two_files_model_pinned_f) [] := by
  check_norm
  rw [size0_ifchr_zero]
  check_norm

/-- The grown file with NO pin: the stale nine-byte record is refused on
its length alone (`generic_fillattr` fs/stat.c:95, v6.18.46), so the
refusal above under the pin is not the pin's doing.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_stale_size_unpinned_rejected :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_truthful)] []) fstat_model_grown
      = CheckReject := by
  check_norm

/-- ...and the grown record is accepted there and pins the grown file.
kernel: fs/stat.c:generic_fillattr@v6.18.46 -/
theorem check_fstat_grown_size_unpinned_pins :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_grown)] []) fstat_model_grown
      = CheckOk (with_statpin fstat_path stat_grown fstat_model_grown) [] := by
  check_norm

/-- AN OVER-ADMISSION, WRITTEN DOWN.  `st_mode` is delivered as
`tmp.st_mode = stat->mode` (`cp_new_stat` fs/stat.c:488, v6.18.46) from a
`umode_t`, an `unsigned short` (include/linux/types.h:24), so bits 16..31 of
the four-byte member are zero in every record Linux writes.  `Uapi.stat_ifmt`
masks the low half only and no predicate reads the rest, so a record with
bit 16 set beside `S_IFREG` is accepted and pinned: the spec's, inherited by
the checker, of the class the `linux-process-semantics@ff0313ba4f:bugs/` entry on fstat's unpinned members
over-admitting records (its path is on the Rocq `stat_stable_eqb`, as
`Sys/Uapi/Fs.lean` spells it; it does not list this member yet).  The pin
fixes the acceptance so that tightening `Uapi.stat_buf_wf` goes red here
rather than silently.
model: `Uapi.stat_ifmt` reads the low half of `st_mode` only; an
over-admission of the class the `linux-process-semantics@ff0313ba4f:bugs/` entry on fstat's unpinned members
records -/
theorem check_fstat_high_mode_bit_accepted :
    check_fstat fstat_input 3 4096 (mkEffect 0 [(4096, stat_high_mode_bit)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_high_mode_bit fstat_model) [] := by
  check_norm

-- lean-port sentinel: ticket V-Fs-Stat appends below this line

section V_Fs_Stat

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-Stat — the decoded registers over the real checked table

The Rocq checker examples below reuse the imported fixtures, including
aliases for Rocq's literal struct bytes. The register pins additionally
separate the arm's decoding from a wrong reading; checker-level pins
cannot see that boundary. Citations below were read in Linux v6.18.46,
commit 1f99e9ab748f. -/

/-- The lookup is independent of argument registers and memory.
include/uapi/asm-generic/unistd.h:206-207 (`__NR_readlinkat`)
assigns 78 to `sys_readlinkat`; this pins that ABI choice in the table.
kernel: include/uapi/asm-generic/unistd.h:__NR_readlinkat@v6.18.46 -/
theorem lookup_readlinkat_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 78 args mem wmem).in_sysno)
      = some arm_readlinkat := rfl

/-- Lean-only closed form of the ABI lookup above: include/uapi/asm-generic/unistd.h:206-207
assigns this syscall number; the closed form lets simp rewrite the projected input.
kernel: include/uapi/asm-generic/unistd.h:__NR_readlinkat@v6.18.46 -/
theorem lookup_readlinkat_number :
    lookup_ca checked_table (bv_unsigned (78 : word)) = some arm_readlinkat := rfl

/-- The lookup is independent of argument registers and memory.
include/uapi/asm-generic/unistd.h:210-211 (`__NR3264_fstatat`)
assigns 79 to `sys_newfstatat`; this pins that ABI choice in the table.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_fstatat@v6.18.46 -/
theorem lookup_newfstatat_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 79 args mem wmem).in_sysno)
      = some arm_newfstatat := rfl

/-- Lean-only closed form of the ABI lookup above: include/uapi/asm-generic/unistd.h:210-211
assigns this syscall number; the closed form lets simp rewrite the projected input.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_fstatat@v6.18.46 -/
theorem lookup_newfstatat_number :
    lookup_ca checked_table (bv_unsigned (79 : word)) = some arm_newfstatat := rfl

/-- The lookup is independent of argument registers and memory.
include/uapi/asm-generic/unistd.h:212-213 (`__NR3264_fstat`)
assigns 80 to `sys_newfstat`; this pins that ABI choice in the table.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_fstat@v6.18.46 -/
theorem lookup_fstat_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 80 args mem wmem).in_sysno)
      = some arm_fstat := rfl

/-- Lean-only closed form of the ABI lookup above: include/uapi/asm-generic/unistd.h:212-213
assigns this syscall number; the closed form lets simp rewrite the projected input.
kernel: include/uapi/asm-generic/unistd.h:__NR3264_fstat@v6.18.46 -/
theorem lookup_fstat_number :
    lookup_ca checked_table (bv_unsigned (80 : word)) = some arm_fstat := rfl

/-- `getname_flags` copies the pathname at fs/namei.c:157, reached
from `vfs_fstatat` at fs/stat.c:370 before its error is returned at :378.
The literal two-byte ledger pins the model's copy-in convention (Linux's
word loads are the bound documented in linux-process-semantics@ff0313ba4f:bugs/openat-getname-word-at-a-time.md);
dropping, growing or shifting that ledger is rejected, with an accepting control.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`newfstatat_pathname_copyin_is_charged`.
kernel: fs/stat.c:newfstatat,vfs_fstatat; fs/namei.c:getname_flags,path_init@v6.18.46 -/
theorem newfstatat_pathname_copyin_is_charged_over_the_real_table :
    check_syscall (statat_input path_f) (mkEffect (errno_ret ENOENT) [] []) statat_absent_model
      = CheckReject
    ∧ check_syscall (statat_input path_f)
        (with_copyins [(0x2000, 3)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckReject
    ∧ check_syscall (statat_input path_f)
        (with_copyins [(0x2001, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckReject
    ∧ check_syscall (statat_input path_f)
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  simp only [check_syscall, check_syscall_in, statat_input, statat_call, lookup_newfstatat_number,
    arm_unfold, in_arg_0, in_arg_1, in_arg_3]
  check_norm

/-- `generic_fillattr` (fs/stat.c:89-106) reads the inode, and
`cp_new_stat` delivers its fields at :484-506; the first answer records the identity.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_first_answer_pins`.
kernel: fs/stat.c:vfs_fstat,cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_first_answer_pins_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_truthful fstat_model) [] := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` (fs/stat.c:90) reads the actual inode mode;
`cp_new_stat` copies it at :488 and size at :495. A modeled path is not
a guarantee of S_IFREG (linux-process-semantics@ff0313ba4f:bugs/fs-paths-assumed-regular-files.md).
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_character_device_answer_admitted`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_character_device_answer_admitted_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_ifchr_zero)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_ifchr_zero fstat_model) [] := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` (fs/stat.c:95) reads the file length, and
`cp_new_stat` copies it at :495: eight is wrong for the nine-byte regular file.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_wrong_size_under_ifreg_rejected`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_wrong_size_under_ifreg_rejected_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_short_size)] []) fstat_model
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` reads the current file length at fs/stat.c:95,
then `cp_new_stat` copies it at :495. Growth invalidates the old size.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_stale_size_after_growth_rejected`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_stale_size_after_growth_rejected_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] [])
        fstat_model_grown_pinned
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- The current size is copied by `cp_new_stat` at fs/stat.c:495,
from `generic_fillattr` at :95; growth preserves the identity pin.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_grown_size_admitted`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_grown_size_admitted_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_grown)] []) fstat_model_grown_pinned
      = CheckOk fstat_model_grown_pinned [] := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `cp_new_stat` clears the struct at fs/stat.c:483 through
`INIT_STRUCT_STAT_PADDING` (:466-468); no member assignment writes pad1.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_nonzero_pad1_rejected`.
kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem fstat_nonzero_pad1_rejected_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_pad1_poisoned)] []) fstat_model
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `cp_new_stat` clears the struct at fs/stat.c:483 through
`INIT_STRUCT_STAT_PADDING` (:466-468); unused4/5 stay zero.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_nonzero_unused45_rejected`.
kernel: fs/stat.c:cp_new_stat,INIT_STRUCT_STAT_PADDING@v6.18.46 -/
theorem fstat_nonzero_unused45_rejected_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_unused45_poisoned)] []) fstat_model
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` (fs/stat.c:90) reads the inode mode, and
`cp_new_stat` copies it at :488. Zero names no file type.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_all_zero_struct_rejected`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_all_zero_struct_rejected_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, zero_stat)] []) fstat_model
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` (fs/stat.c:90) reads the inode mode, and
`cp_new_stat` copies it at :488. S_IFMT with every type bit set names no inode kind.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_impossible_type_rejected`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_impossible_type_rejected_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_ifmt_type)] []) fstat_model
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` (fs/stat.c:89-94) reads the same inode, and
`cp_new_stat` delivers it at :484-494. Repeating its stable fields is admitted.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_pinned_repeat_admitted`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_pinned_repeat_admitted_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] []) fstat_model_pinned
      = CheckOk fstat_model_pinned [] := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` (fs/stat.c:89) reads this inode's i_ino, and
`cp_new_stat` copies it at :485: a later stat cannot change that identity.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_pinned_inode_defector_rejected`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_pinned_inode_defector_rejected_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_other_inode)] []) fstat_model_pinned
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` (fs/stat.c:89) reads i_ino;
`cp_new_stat` copies it at :485. A first answer may establish a different inode.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_inode_defector_is_itself_admissible_first`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_inode_defector_is_itself_admissible_first_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_other_inode)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_other_inode fstat_model) [] := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` reads current timestamps and blocks at
fs/stat.c:96-106, copied by `cp_new_stat` at :496-504; these are not identity fields.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_pinned_new_times_and_blocks_admitted`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_pinned_new_times_and_blocks_admitted_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_new_times)] []) fstat_model_pinned
      = CheckOk fstat_model_pinned [] := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `cp_new_stat` copies sizeof(tmp), not a short prefix, on
success at fs/stat.c:506. The 127-byte success is rejected.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_short_struct_rejected`.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem fstat_short_struct_rejected_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_short127)] []) fstat_model
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `cp_new_stat` copies to statbuf itself at fs/stat.c:506.
A success write one byte later is rejected.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_shifted_write_rejected`.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem fstat_shifted_write_rejected_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4097, stat_truthful)] []) fstat_model
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `newfstat` (fs/stat.c:550-559) resolves a register descriptor
through `vfs_fstat` (:276-281) and `cp_new_stat` only copies out (:506): no user copy-in.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_forged_copyin_rejected`.
kernel: fs/stat.c:newfstat,vfs_fstat,cp_new_stat@v6.18.46 -/
theorem fstat_forged_copyin_rejected_over_the_real_table :
    check_syscall fstat_input
        (with_copyins [(4096, 128)] (mkEffect 0 [(4096, stat_truthful)] [])) fstat_model
      = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `cp_new_stat` returns EFAULT at fs/stat.c:506 when copy_to_user
refuses the range; `__access_ok` (include/asm-generic/access_ok.h:31-41)
rejects this address before copying.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_access_ok_fault`.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem fstat_access_ok_fault_over_the_real_table :
    check_syscall (fstat_call 3 (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        (mkEffect (errno_ret EFAULT) [] []) fstat_model
      = CheckOk fstat_model [] := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_call, lookup_fstat_number, arm_unfold,
    in_arg_0, in_arg_1, hfd]
  check_norm

/-- `cp_new_stat` calls copy_to_user at fs/stat.c:506;
`_inline_copy_to_user` (include/linux/uaccess.h:190-199) can copy a prefix.
The model declines this partially backed destination instead of guessing the prefix.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_one_byte_short_is_unmodeled`.
kernel: fs/stat.c:cp_new_stat@v6.18.46 -/
theorem fstat_one_byte_short_is_unmodeled_over_the_real_table :
    check_syscall fstat_input_short (mkEffect 0 [(4096, stat_truthful)] []) fstat_model
      = CheckUnmodeled := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input_short, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `vfs_fstat` reaches the surviving file path at fs/stat.c:281
even after unlink; `generic_fillattr` reads its inode at :89-106.
The model has lost the path's contents and declines that case.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_unlinked_path_is_unmodeled`.
kernel: fs/stat.c:generic_fillattr,cp_new_stat@v6.18.46 -/
theorem fstat_unlinked_path_is_unmodeled_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_truthful)] []) fstat_model_unlinked = CheckUnmodeled := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-- `generic_fillattr` (fs/stat.c:89) reads the current node's i_ino, and
`cp_new_stat` copies it at :485. Recreating the path permits a new
identity; a pin belonging to the removed file must not constrain it.
Twins `theories/LinuxProcessSem/Checks/Cases/Fs/Stat.v`'s
`fstat_recreated_file_takes_a_new_inode`.
kernel: fs/stat.c:cp_new_stat,generic_fillattr@v6.18.46 -/
theorem fstat_recreated_file_takes_a_new_inode_over_the_real_table :
    check_syscall fstat_input (mkEffect 0 [(4096, stat_other_inode)] []) fstat_model_recreated
      = CheckOk (with_statpin fstat_path stat_other_inode fstat_model_recreated) [] := by
  have hfd : fd32 (3 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_input, fstat_call, lookup_fstat_number,
    arm_unfold, in_arg_0, in_arg_1, hfd]
  check_norm

/-! ### Register-reading pins

The high-dirfd newfstatat case uses a nonempty readable name: empty and
faulting names answer before the checker consults dirfd and would not
catch a missing `fd32`. The fstat address pair backs both destinations
fully, so a wrong register reaches the delivery check and is rejected. -/

/-- `newfstat` takes unsigned int fd (fs/stat.c:550); `__SC_CAST`
(include/linux/syscalls.h:132, applied at arch/riscv/include/asm/syscall_wrapper.h:88)
drops the high half. A raw-word arm would find no descriptor and reject
this success, or accept EBADF, which the actual arm rejects
(`vfs_fstat`, fs/stat.c:279-280).
kernel: fs/stat.c:newfstat,vfs_fstat; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem fstat_fd32_alias_over_the_real_table :
    check_syscall (fstat_call 4294967299 4096 stat_out)
        (mkEffect 0 [(4096, stat_truthful)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_truthful fstat_model) []
    ∧ check_syscall (fstat_call 4294967299 4096 stat_out)
        (mkEffect (errno_ret EBADF) [] []) fstat_model = CheckReject := by
  have hfd : fd32 (4294967299 : word) = 3 := by decide
  simp only [check_syscall, check_syscall_in, fstat_call, lookup_fstat_number, arm_unfold,
    in_arg_0, in_arg_1, hfd]
  check_norm

/-- `readlinkat` takes int dfd at fs/stat.c:604-605; `__SC_CAST`
(include/linux/syscalls.h:132, used at arch/riscv/include/asm/syscall_wrapper.h:88)
turns the low 32 bits of 8589934492 into AT_FDCWD. An arm passing the
whole register would decline. The zero bufsiz makes EINVAL the kernel's
own answer before pathname lookup (`do_readlinkat`, fs/stat.c:571-572).
kernel: fs/stat.c:readlinkat,do_readlinkat; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem readlinkat_fd32_alias_over_the_real_table (m : Model) :
    check_syscall (readlinkat_call 8589934492 0 path_none)
        (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
    ∧ check_syscall (readlinkat_call 8589934492 0 path_none)
        (mkEffect 0 [] []) m = CheckReject := by
  simp only [check_syscall, check_syscall_in, readlinkat_call, lookup_readlinkat_number,
    arm_unfold, in_arg_0]
  check_norm

/-- `newfstatat` takes int dfd at fs/stat.c:536; `__SC_CAST`
(include/linux/syscalls.h:132, applied at arch/riscv/include/asm/syscall_wrapper.h:88)
reads AT_FDCWD from the low half. The readable nonempty name reaches
`vfs_statx`'s lookup (fs/stat.c:353); handing the checker the whole dirfd
would decline instead of accepting this missing-file ENOENT.
`path_init` selects the cwd (fs/namei.c:2590-2604); a missing inode
returns ENOENT in `step_into` (:2001-2002).
kernel: fs/stat.c:newfstatat,vfs_statx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:path_init,step_into@v6.18.46 -/
theorem newfstatat_fd32_alias_over_the_real_table :
    check_syscall (statat_call 8589934492 0 path_f)
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  simp only [check_syscall, check_syscall_in, statat_call, lookup_newfstatat_number, arm_unfold,
    in_arg_0, in_arg_1, in_arg_3]
  check_norm

/-- `newfstatat` declares statbuf third and int flag fourth
(fs/stat.c:536-537); `SC_RISCV_REGS_TO_ARGS`
(arch/riscv/include/asm/syscall_wrapper.h:21-24) maps them to a2 and a3.
The unmodeled flag 1024 in a3 is declined; in a2 alone it is an unused
buffer on this ENOENT path (`vfs_statx`, fs/stat.c:348-355). An arm reading
flags from a2 instead would interchange the two verdicts.
`path_init` selects the cwd (fs/namei.c:2590-2604); a missing inode
returns ENOENT in `step_into` (:2001-2002).
kernel: fs/stat.c:newfstatat,vfs_statx; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/namei.c:path_init,step_into@v6.18.46 -/
theorem newfstatat_flag_is_a3_over_the_real_table :
    check_syscall (statat_call AT_FDCWD 1024 path_f)
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckUnmodeled
    ∧ check_syscall
        (SyscallInput.mkInput 79 [AT_FDCWD, 0x2000, 1024, 0, 0, 0] path_f (fun _ => none))
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  simp only [check_syscall, check_syscall_in, statat_call, lookup_newfstatat_number, arm_unfold,
    in_arg_0, in_arg_1, in_arg_3]
  check_norm

/-- int flag at fs/stat.c:537 is narrowed by `__SC_CAST`
(include/linux/syscalls.h:132, applied at arch/riscv/include/asm/syscall_wrapper.h:88).
A flag with only bit 32 set is zero before `vfs_statx`'s test at
fs/stat.c:348-350. An arm omitting flag32 would decline this accepted ENOENT.
`path_init` selects the cwd (fs/namei.c:2590-2604); a missing inode
returns ENOENT in `step_into` (:2001-2002).
kernel: fs/stat.c:newfstatat,vfs_statx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:path_init,step_into@v6.18.46 -/
theorem newfstatat_flag32_over_the_real_table :
    check_syscall (statat_call AT_FDCWD 4294967296 path_f)
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckOk statat_absent_model [] := by
  simp only [check_syscall, check_syscall_in, statat_call, lookup_newfstatat_number, arm_unfold,
    in_arg_0, in_arg_1, in_arg_3]
  check_norm

/-- filename is a1 (`newfstatat`, fs/stat.c:536-537;
`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24).
`vfs_fstatat` reads it at fs/stat.c:370. A wrong arm reading a2=0 would
fault and reject this ENOENT and its ledger; changing a1 to zero rejects
that same delivery even with the readable pointer in a2.
`path_init` selects the cwd (fs/namei.c:2590-2604); a missing inode
returns ENOENT in `step_into` (:2001-2002).
kernel: fs/stat.c:newfstatat,vfs_fstatat; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS; fs/namei.c:path_init,step_into@v6.18.46 -/
theorem newfstatat_pathname_is_a1_over_the_real_table :
    check_syscall (statat_input path_f)
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckOk statat_absent_model []
    ∧ check_syscall
        (SyscallInput.mkInput 79 [AT_FDCWD, 0, 0x2000, 0, 0, 0] path_f (fun _ => none))
        (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] [])) statat_absent_model
      = CheckReject := by
  have hpath : read_cstr path_f 0 = CstrFault := by decide
  have hlen : cstr_access_len_aux path_f 0 path_max = 1 := by decide
  simp only [check_syscall, check_syscall_in, statat_input, statat_call, lookup_newfstatat_number,
    arm_unfold, in_arg_0, in_arg_1, in_arg_3]
  simp only [check_newfstatat, hpath, hlen]
  check_norm

/-- statbuf is a1 (`newfstat`, fs/stat.c:550;
`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24),
and `cp_new_stat` copies there at fs/stat.c:506. Both candidate addresses
are writable. An arm reading a0 or a2 for statbuf would reject the first
success; one hardcoding 4096 would wrongly accept the second.
kernel: fs/stat.c:newfstat,cp_new_stat; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS@v6.18.46 -/
theorem fstat_statbuf_is_a1_over_the_real_table :
    check_syscall (fstat_call 3 4096 (fun _ => some 0))
        (mkEffect 0 [(4096, stat_truthful)] []) fstat_model
      = CheckOk (with_statpin fstat_path stat_truthful fstat_model) []
    ∧ check_syscall (fstat_call 3 4097 (fun _ => some 0))
        (mkEffect 0 [(4096, stat_truthful)] []) fstat_model = CheckReject := by
  have hfd : fd32 (3 : word) = 3 := by decide
  have h4096 : read_bytes_map (fun _ => some 0) 4096 (Z_to_bv 64 STAT_SIZE)
      = some (List.replicate 128 0) := by decide
  have h4097 : read_bytes_map (fun _ => some 0) 4097 (Z_to_bv 64 STAT_SIZE)
      = some (List.replicate 128 0) := by decide
  simp only [check_syscall, check_syscall_in, fstat_call, lookup_fstat_number, arm_unfold,
    in_arg_0, in_arg_1, hfd]
  check_norm
  simp only [h4096, h4097]
  check_norm

/-! ### The witnesses receive the same decoded registers -/

/-- The witness sees AT_FDCWD after the int cast (`readlinkat`,
fs/stat.c:604-605; `__SC_CAST`, include/linux/syscalls.h:132), and
exhibits the EINVAL decided at zero bufsiz (`do_readlinkat`, fs/stat.c:571-572).
kernel: fs/stat.c:readlinkat,do_readlinkat; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem readlinkat_witness_over_the_real_table (m : Model) :
    syscall_spec_witness (readlinkat_call 8589934492 0 path_none) m
      = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := rfl

/-- The witness gets the low halves of dfd and flag and the whole a1
pointer (`newfstatat`, fs/stat.c:536-537; `__SC_CAST`, include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88); `vfs_fstatat`
fetches the name at fs/stat.c:370 before returning ENOENT via :375-378.
`path_init` selects the cwd (fs/namei.c:2590-2604); a missing inode
returns ENOENT in `step_into` (:2001-2002).
kernel: fs/stat.c:newfstatat,vfs_fstatat; include/linux/syscalls.h:__SC_CAST; fs/namei.c:path_init,step_into@v6.18.46 -/
theorem newfstatat_witness_over_the_real_table :
    syscall_spec_witness (statat_call 8589934492 4294967296 path_f) statat_absent_model
      = Ok (with_copyins [(0x2000, 2)] (mkEffect (errno_ret ENOENT) [] []))
          statat_absent_model [] := rfl

/-- The witness receives fd 3 after the unsigned int cast and statbuf
from a1 (`newfstat`, fs/stat.c:550; `__SC_CAST`, include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88). The out-of-range
buffer returns EFAULT through `cp_new_stat` (fs/stat.c:506); a witness
receiving the uncut fd would return EBADF instead.
kernel: fs/stat.c:newfstat,cp_new_stat; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem fstat_witness_over_the_real_table :
    syscall_spec_witness (fstat_call 4294967299 (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
        fstat_model = Ok (mkEffect (errno_ret EFAULT) [] []) fstat_model [] := rfl

end V_Fs_Stat

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Stat
