import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Namei
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Namei

/-! # Checks.Cases.Checks.Sys.Fs.Namei — what the unlinkat checker accepts and refuses, and what its witness names

Pins over `Checks.Sys.Fs.Namei.check_unlinkat`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/Namei.v`'s checker for unlinkat,
and over `unlinkat_witness`, the twin of
`theories/LinuxProcessSem/Checks/Witness/Fs/Namei.v`'s.  Not part of the
trusted specification: this file is QA on the checker, written to be READ,
and every claim in it is a claim about what the kernel does, with the
citation beside it.  `Checks/Cases/Fs/Namei.lean` pins the same calls on
`unlinkat_spec` and carries the `covers:` register for the Rocq Cases
file; what it cannot say is that the executable acceptor answers the same
way, which is what a graded trace is decided by.  The theorems below say
that: each an equation `check_unlinkat_row … = <verdict>` closed by `rfl`,
or a conjunction of such equations — the same computation `vm_compute`
performs in Rocq, on the same fixtures spelled through `fixture_of`.

WHAT THIS TWINS.  Rocq keeps the checker's worked examples for unlinkat in
`Checks/Cases/Fs/Namei.v`, beside the spec's, as `Example`s over
`check_syscall`, the dispatcher.  Those are restated here under the Rocq
examples' own names, and stated on `check_unlinkat_row`, which applies
`check_unlinkat` as the row for 35 in `Sys/Registry/Fs/Namei.lean` applies
the spec — the dirfd through `fd32`, the pathname pointer and the flag word
as they arrive in a1 and a2.
The `V_Fs_Namei` section below states the dispatcher pins.

WHY A SEPARATE FILE, AND WHY NO COVERAGE HEADER (the one
`tools/check_lean_cases_parity.py` reads).  The mirror-by-path of a Rocq
Cases file is its spec twin, so the register for `Checks/Cases/Fs/Namei.v`
belongs to `Checks/Cases/Fs/Namei.lean` and is there; a second register for
the same Rocq names would count each twice.  This file stands where
`Checks/Cases/Checks/Sys/Dispatch.lean` stands: in the tree the pin tools
read, mirroring nothing by path, named after the checker module it
exercises.

WHAT IS HERE BEYOND THE TWINS.  The checker's soundness and completeness
are proved beside it, and those proofs cannot catch a change made to the
checker and the spec alike (`CLAUDE.md`, "The proofs cannot catch a change
made on both sides at once").  The deep review of #1178 ran the mutation
tester over this checker with its twin lemmas deleted, so that only the
pins in this file judged each mutant, and every decision a mutant could
move unnoticed has a pin below naming the concrete answer Linux gives:
the five injectable errnos, the three answers `getname` gives before the
dirfd, the dirfd decline, the two arms of each of "/", "." and "..", the
AT_REMOVEDIR arm on a held file, the /tmp implied directory, and the
witness's answer on every arm.  Each is the lie the mutant would have
told, refused, or the honest answer it would have withheld, required.

Line numbers are Linux v6.18.46 (commit 1f99e9ab748f), all in
`fs/namei.c` unless said otherwise. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Namei

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Namei

/-! ## The row, and the fixtures

Every memory map, model and ledger below is `Checks/Cases/Fs/Namei.lean`'s,
so the checker is graded on exactly the fixtures the spec was pinned on.
Those added here are shapes the Rocq examples use and the spec pins did
not need. -/

/-- `check_unlinkat` as the row for 35 in `Sys/Registry/Fs/Namei.lean`
applies the spec: the dirfd through `fd32`, the pathname pointer and the
flag word as they arrive in a1 and a2. -/
def check_unlinkat_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

/-- …and the witness through the same row. -/
def unlinkat_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  unlinkat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- The dispatcher-shaped call: syscall 35, the dirfd in `a0` as the 64-bit
word the row's `fd32` truncates, the pathname at 8192, `flags` in `a2`.
Spelled with `mkInput` here rather than through `unlink_in` so that the
evidence checker reads the number off this file. -/
def unlink_call_at (dirfd flags : word) (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 35 [dirfd, 8192, flags, 0, 0, 0] mem (fun _ => none)

/-- The same call at `AT_FDCWD`, which `fd32` takes to `AT_FDCWD32`. -/
def unlink_call (flags : word) (mem : word → Option byte) : SyscallInput :=
  unlink_call_at AT_FDCWD flags mem

/-- Rocq's image for the flag cases: a file `a` holding nothing. -/
def a_empty_model : Model := fixture_of (fs := [([97], [])])

/-- "/tmp/d/f": a second component under /tmp. -/
def tmp_d_f : List byte := [47, 116, 109, 112, 47, 100, 47, 102]

/-- "/tmp/d": the directory `tmp_d_f` implies. -/
def tmp_d : List byte := [47, 116, 109, 112, 47, 100]

/-- "/tmp/d/": the same, with the trailing separator. -/
def tmp_d_slash : List byte := [47, 116, 109, 112, 47, 100, 47]

/-- A 255-byte name in the working directory, held. -/
def cwd_name255_model : Model := fixture_of (fs := [(name255, [104])])
/-- …and a 256-byte one, which no directory can hold. -/
def cwd_name256_model : Model := fixture_of (fs := [(name256, [104])])
/-- A key the declaration put UNDER a 256-byte component of /tmp,
"/tmp/<256 a's>/x": `fs_under` then sees a directory at the 256-byte name,
one no tmpfs directory could hold. -/
def tmp_name256_under_model : Model :=
  fixture_of (fs := [(tmp_key name256 ++ [47, 120], [104])])

/-! ## The implied directory -/

/-- A key living UNDER a name means reality has a DIRECTORY that the flat
map only implies, and a non-empty one (#1753): Linux answers -EISDIR for
unlink, in `may_delete` (fs/namei.c:3290, the `d_is_dir(victim)` test of
the non-`isdir` call), and -ENOTEMPTY for AT_REMOVEDIR, from the
filesystem's `->rmdir` through `vfs_rmdir` (4552; `simple_rmdir`,
fs/libfs.c:801-802).  The flat map's -ENOENT, a removal, the file's
-ENOTDIR and an injectable errno are refused.  This image holds "a/b" and
NOT "a", the REALIZABLE shape.
kernel: fs/namei.c:may_delete,vfs_rmdir,generic_permission; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem unlinkat_implied_directory_answers :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret EISDIR) 2)
      implied_dir_model = CheckOk implied_dir_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret ENOENT) 2)
      implied_dir_model = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered 0 2) implied_dir_model
      = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret EACCES) 2)
      implied_dir_model = CheckReject
    ∧ check_unlinkat_row (unlink_call 512 (name_at [97])) (ledgered (errno_ret ENOTEMPTY) 2)
      implied_dir_model = CheckOk implied_dir_model []
    ∧ check_unlinkat_row (unlink_call 512 (name_at [97])) (ledgered (errno_ret ENOTDIR) 2)
      implied_dir_model = CheckReject
    ∧ check_unlinkat_row (unlink_call 512 (name_at [97])) (ledgered 0 2) implied_dir_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The same answers on the UNREALIZABLE image holding both "a" and "a/b".
Here the lookup of "a" would SUCCEED, so a test placed after the lookup
would remove the file and return 0 (flags 0) or answer the file's
-ENOTDIR (AT_REMOVEDIR); this is the case that pins the test's place,
since on the realizable image the lookup misses either way.
kernel: fs/namei.c:may_delete,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem unlinkat_implied_directory_unrealizable_image :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret EISDIR) 2)
      unrealizable_model = CheckOk unrealizable_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered 0 2) unrealizable_model
      = CheckReject
    ∧ check_unlinkat_row (unlink_call 512 (name_at [97])) (ledgered (errno_ret ENOTEMPTY) 2)
      unrealizable_model = CheckOk unrealizable_model []
    ∧ check_unlinkat_row (unlink_call 512 (name_at [97])) (ledgered (errno_ret ENOTDIR) 2)
      unrealizable_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The contrast: "ab" does not live under "a", so the guard is a COMPONENT
prefix and not a byte prefix, and the removal goes through — `do_unlinkat`
(fs/namei.c:4741) reaches `vfs_unlink` — leaving the map with the one key.
The effect carries the two-byte pathname copy-in the spec records.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem unlinkat_byte_prefix_is_not_a_directory :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered 0 2) ab_model
      = CheckOk ab_unlinked_model [] := rfl

/-! ## Where the ledger starts

The copy-in boundary is a CHOICE, and a checker that wrapped the whole call
in a ledger would pass every conformance run just as well.  These four pin
the boundary itself, two on either side of it and two on the extent. -/

/-- The flag word is decided BEFORE `getname()`: `SYSCALL_DEFINE3(unlinkat)`
returns -EINVAL at fs/namei.c:4777-4778 and calls `getname` only after
(4781-4782).  So that arm reads NO user memory, and a ledger claimed there
is a read the kernel did not perform — the case a whole-call wrapper gets
wrong, since it would EXPECT this range and accept.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem unlinkat_bad_flags_records_no_copyin :
    check_unlinkat_row (unlink_call 1 (name_at [97])) (ledgered (errno_ret EINVAL) 2)
      a_empty_model = CheckReject := rfl

/-- …and the same call with an EMPTY ledger is admitted, so the rejection
above is about the ledger and not about the arm (fs/namei.c:4777-4778).
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem unlinkat_bad_flags_empty_ledger_ok :
    check_unlinkat_row (unlink_call 1 (name_at [97])) (mkEffect (errno_ret EINVAL) [] [])
      a_empty_model = CheckOk a_empty_model [] := rfl

/-- Past the flag test the ledger is REQUIRED: `getname_flags`
(fs/namei.c:157) copied the name in, through `strncpy_from_user`
(lib/strncpy_from_user.c), so a removal that denies the read is rejected.
The call differs from the two above in the flag word alone, and the
ledger obligation flips with it.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem unlinkat_removal_needs_the_copyin :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (mkEffect 0 [] []) ab_model
      = CheckReject := rfl

/-- And the EXTENT is the NUL-terminated prefix, 'a' and the NUL: two
bytes.  One byte short is the name without its terminator, which is not
what `getname_flags` (fs/namei.c:157) reads, so a one-byte ledger is
refused and the number `main.ml` computes has a literal here to agree with.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem unlinkat_copyin_extent_is_the_nul_terminated_prefix :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered 0 1) ab_model
      = CheckReject := rfl

/-- One byte LONG is refused too — `strncpy_from_user` stops at the NUL
(lib/strncpy_from_user.c:91-92) and reads nothing past it — and so is a
second, separate read of the same name: `getname_flags` copies the
pathname once (fs/namei.c:157).  `check_copyins_after` compares the whole
ledger, not its first entry.  The probe's `grow-copyins:1` and
`smuggle-copyin:a1:1` cases on `two-files` are the runs that show it.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user@v6.18.46 -/
theorem unlinkat_copyin_overrun_and_second_read_rejected :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered 0 3) unlink_model = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97]))
        (with_copyins [(8192, 2), (8192, 1)] (mkEffect 0 [] [])) unlink_model = CheckReject :=
  ⟨rfl, rfl⟩

/-! ## The two arms typed by the walk

A TRAILING separator and an all-separator path are settled by the kernel
without a directory structure, so the spec answers them without one
either.  Each is pinned from both sides: the accepting half a conformance
run shows, and the rejecting half only a `--mutate` lie shows — no kernel
removes a file through a name with a trailing separator, so
`unlinkat_spec.c`'s `reject --mutate unlinkat:ret=0 -- slash` is the run
that exercises it. -/

/-- "a/" names the same component as "a", but `do_unlinkat` tests the byte
just past it (`last.name[last.len]`, fs/namei.c:4734) and jumps to its
`slashes:` label, which for a regular file is -ENOTDIR (4767-4771).  The
file survives: the answer is reached from ABOVE `vfs_unlink`.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem unlinkat_trailing_slash_on_a_file_is_enotdir :
    check_unlinkat_row (unlink_call 0 (name_at [97, 47])) (ledgered (errno_ret ENOTDIR) 3)
      unlink_model = CheckOk unlink_model [] := rfl

/-- The rejecting half: a kernel that removed the file through "a/" and
returned 0 is one this model must refuse — `do_unlinkat` never reaches
`vfs_unlink` from the `slashes:` path (fs/namei.c:4734, 4767-4771).
Without the `path_trailing_slash` test this case is the ordinary removal
and accepts, so this is what separates the two spellings of the arm; the
probe's `reject --mutate unlinkat:ret=0 -- slash` is the run that shows it.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem unlinkat_trailing_slash_success_rejected :
    check_unlinkat_row (unlink_call 0 (name_at [97, 47])) (ledgered 0 3) unlink_model
      = CheckReject := rfl

/-- The `slashes:` answer is decided by the dentry the lookup found and by
nothing the run holds open: "a/" over an image where fd 3 is open on "a"
is -ENOTDIR all the same (fs/namei.c:4734, 4767-4771), and the open
descriptor's decline is not reached.  This is the order of the two tests
in `check_unlink_found`; swapping them declines here.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem unlinkat_trailing_slash_beside_an_open_fd_is_enotdir :
    check_unlinkat_row (unlink_call 0 (name_at [97, 47])) (ledgered (errno_ret ENOTDIR) 3)
      open_fd_model = CheckOk open_fd_model [] := rfl

/-- "/" has no component, so the walk leaves the type at LAST_ROOT and
`do_rmdir`'s `case LAST_ROOT` answers -EBUSY (fs/namei.c:4590-4591), under
the AT_REMOVEDIR the syscall dispatches on (4780-4781).  The file system
is not consulted, so an EMPTY map gives the same answer as any other.
kernel: fs/namei.c:unlinkat,do_rmdir@v6.18.46 -/
theorem unlinkat_root_removedir_is_ebusy :
    check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [47]))
      (ledgered (errno_ret EBUSY) 2) empty_model = CheckOk empty_model [] := rfl

/-- The rejecting half, and the one that matters most: -ENOENT is the
answer the flat map WOULD give on its own — "no such key", the answer
`lookup_one_qstr_excl` gives a negative dentry (fs/namei.c:1713-1715) —
and it is the confident wrong one.  `do_rmdir` returns -EBUSY for "/"
before any lookup (4590-4591); Linux never answers -ENOENT for it.
kernel: fs/namei.c:unlinkat,do_rmdir,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_root_enoent_rejected :
    check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [47]))
      (ledgered (errno_ret ENOENT) 2) empty_model = CheckReject := rfl

/-- The PLAIN arm on "/": `do_unlinkat` types the last component and
answers -EISDIR for anything but LAST_NORM (fs/namei.c:4720-4722), so the
two flag words give two different answers for the one name — which is
what the `unlink_rmdir` test inside the all-separator arm is for.  "//" is
the same name: `link_path_walk` skips a leading run of separators as one
(2450-2454).
kernel: fs/namei.c:link_path_walk,do_unlinkat@v6.18.46 -/
theorem unlinkat_root_plain_is_eisdir :
    check_unlinkat_row (unlink_call 0 (name_at [47])) (ledgered (errno_ret EISDIR) 2) empty_model
      = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [47, 47])) (ledgered (errno_ret EISDIR) 3)
        empty_model = CheckOk empty_model [] :=
  ⟨rfl, rfl⟩

/-- …and each arm refuses the other's answer: -EBUSY on the plain call,
-EISDIR under AT_REMOVEDIR, and -ENOENT on either (the map's own).  The
flag word is what `do_unlinkat`'s `type != LAST_NORM` test (4720-4722)
does not read, and `do_rmdir`'s `case LAST_ROOT` (4590-4591) is reached
only under AT_REMOVEDIR (4780-4781); -ENOENT is `lookup_one_qstr_excl`'s
(1713-1715), which neither caller reaches for "/".  The probe's
`ret=-ENOENT -- root` and `unlinkat#2:ret=-EISDIR -- root` cases show two
of the three.
kernel: fs/namei.c:unlinkat,do_unlinkat,do_rmdir,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_root_arms_refuse_each_other :
    check_unlinkat_row (unlink_call 0 (name_at [47])) (ledgered (errno_ret EBUSY) 2) empty_model
      = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [47])) (ledgered (errno_ret ENOENT) 2) empty_model
      = CheckReject
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [47]))
        (ledgered (errno_ret EISDIR) 2) empty_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-! ## The dot names

"." and ".." are typed by `link_path_walk` (LAST_DOT and LAST_DOTDOT,
fs/namei.c:2474-2482, Linux v6.18.46, off the word `hash_name` hands back)
and answered by the two callers without a lookup:
`do_unlinkat` says -EISDIR for either (4720-4722, the same test as "/"),
and `do_rmdir` tells them apart — -EINVAL for "." (4587-4589), -ENOTEMPTY
for ".." (4584-4586).  A trailing separator changes none of this.  "..."
is an ordinary name. -/

/-- The four answers, each on the empty image so that none is about a key.
kernel: fs/namei.c:unlinkat,link_path_walk,do_unlinkat,do_rmdir@v6.18.46 -/
theorem unlinkat_dot_names_answered :
    check_unlinkat_row (unlink_call 0 (name_at [46])) (ledgered (errno_ret EISDIR) 2) empty_model
      = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46]))
        (ledgered (errno_ret EINVAL) 2) empty_model = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [46, 46])) (ledgered (errno_ret EISDIR) 3)
        empty_model = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46, 46]))
        (ledgered (errno_ret ENOTEMPTY) 3) empty_model = CheckOk empty_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- …with the trailing separator: "./" and "../" are the same two names
to `link_path_walk`, which types the component (2474-2482) and then skips
the separator after it (2502-2504), so the type stands.
kernel: fs/namei.c:unlinkat,link_path_walk,do_unlinkat,do_rmdir@v6.18.46 -/
theorem unlinkat_dot_slash_names_answered :
    check_unlinkat_row (unlink_call 0 (name_at [46, 47])) (ledgered (errno_ret EISDIR) 3)
        empty_model = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46, 47]))
        (ledgered (errno_ret EINVAL) 3) empty_model = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [46, 46, 47])) (ledgered (errno_ret EISDIR) 4)
        empty_model = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46, 46, 47]))
        (ledgered (errno_ret ENOTEMPTY) 4) empty_model = CheckOk empty_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The arms are deterministic: the plain "." admits no injectable errno
(the probe's `ret=-ENOMEM -- dot`), rmdir("..") is not -EISDIR
(`do_rmdir`'s `case LAST_DOTDOT`, 4584-4586, and not `do_unlinkat`'s type
test), and rmdir("../") is not -EBUSY, since "../" is not typed LAST_ROOT.
Each mutant that swapped an arm's errno, or exchanged the two arms under
the flag word, is refused by one of these; the -ENOMEM is `getname`'s
(146-148), an allocation that precedes the copy and so never follows a
typed name.  The probe's `dot`, `dotdot` and `dot-slash` reject cases are
the runs that show them.
kernel: fs/namei.c:unlinkat,do_unlinkat,do_rmdir,getname_flags@v6.18.46 -/
theorem unlinkat_dot_names_refuse_the_other_answers :
    check_unlinkat_row (unlink_call 0 (name_at [46])) (ledgered (errno_ret ENOMEM) 2) empty_model
      = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [46])) (ledgered (errno_ret EINVAL) 2) empty_model
      = CheckReject
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46]))
        (ledgered (errno_ret EISDIR) 2) empty_model = CheckReject
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46, 46]))
        (ledgered (errno_ret EISDIR) 3) empty_model = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [46, 46])) (ledgered (errno_ret ENOTEMPTY) 3)
        empty_model = CheckReject
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46, 46, 47]))
        (ledgered (errno_ret EBUSY) 4) empty_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "..." is an ordinary component: LAST_NORM to `link_path_walk`
(2474-2485; `hash_name`'s word names only one and two dots), looked up,
and -ENOENT on an image
that lacks it (`lookup_one_qstr_excl`, 1713-1715).
kernel: fs/namei.c:link_path_walk,do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_dot3_is_an_ordinary_name :
    check_unlinkat_row (unlink_call 0 (name_at [46, 46, 46])) (ledgered (errno_ret ENOENT) 4)
      empty_model = CheckOk empty_model [] := rfl

/-! ## The name arrives before the dirfd

`getname` runs first (fs/namei.c:4781-4782, Linux v6.18.46) and has three
answers of its own — -ENAMETOOLONG, -EFAULT, -ENOENT — before `path_init` reads the
dirfd (2590, 2606-2622).  The model answers all three and declines every
dirfd but AT_FDCWD, in that order. -/

set_option maxRecDepth 100000 in
/-- A name with no NUL inside PATH_MAX: `getname_flags` copies up to
PATH_MAX bytes (fs/namei.c:157, 195) and answers -ENAMETOOLONG when the
copy filled the buffer (207-210).  The ledger is the whole 4096-byte
attempt, and the kernel read that much.
kernel: fs/namei.c:getname_flags; include/uapi/linux/limits.h:PATH_MAX@v6.18.46 -/
theorem unlinkat_toolong_is_enametoolong :
    check_unlinkat_row (unlink_call 0 endless) (ledgered (errno_ret ENAMETOOLONG) 4096)
      unlink_model = CheckOk unlink_model [] := rfl

set_option maxRecDepth 100000 in
/-- …and admits nothing else: the spec's arm has no errno alternative.
`getname_flags` has two -ENOMEM sites, `__getname` before any byte is read
(146-148) and the `kzalloc` for a name that filled the embedded buffer
(188-192), between the first copy and the PATH_MAX one; the second would
come with a ledger of EMBEDDED_NAME_MAX bytes, never the 4096 this pin
carries, and the spec admits it under no ledger at all — a question for
the spec, not the checker, which mirrors it.  The probe's
`ret=-ENOMEM -- toolong` case is the run that shows the refusal.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem unlinkat_toolong_enomem_rejected :
    check_unlinkat_row (unlink_call 0 endless) (ledgered (errno_ret ENOMEM) 4096) unlink_model
      = CheckReject := rfl

/-- An unmapped pathname is -EFAULT from `strncpy_from_user`
(lib/strncpy_from_user.c:154), and so is a name whose NUL falls off the
mapping (do_strncpy_from_user, 91-92): one byte and two bytes of ledger,
which is what the kernel touched before the fault.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user,do_strncpy_from_user@v6.18.46 -/
theorem unlinkat_fault_is_efault :
    check_unlinkat_row (unlink_call 0 unmapped) (ledgered (errno_ret EFAULT) 1) unlink_model
      = CheckOk unlink_model []
    ∧ check_unlinkat_row (unlink_call 0 unterminated) (ledgered (errno_ret EFAULT) 2) unlink_model
      = CheckOk unlink_model [] :=
  ⟨rfl, rfl⟩

/-- …deterministic likewise: the fault is found by the copy (157) and
`getname`'s -ENOMEM (146-148) precedes it.  The probe's
`ret=-ENOMEM -- fault` case is the run that shows the refusal.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem unlinkat_fault_enomem_rejected :
    check_unlinkat_row (unlink_call 0 unmapped) (ledgered (errno_ret ENOMEM) 1) unlink_model
      = CheckReject := rfl

/-- The empty pathname is -ENOENT inside `getname_flags` (fs/namei.c:168-170),
under either flag word — the syscall splits on AT_REMOVEDIR only after
`getname` returned (4780-4782) — and before the dirfd is read: with a
dirfd of 3 the answer is the same, where the model would otherwise
decline.  One byte of ledger, the NUL.
kernel: fs/namei.c:getname_flags,unlinkat,path_init@v6.18.46 -/
theorem unlinkat_empty_path_is_enoent :
    check_unlinkat_row (unlink_call 0 (name_at [])) (ledgered (errno_ret ENOENT) 1) unlink_model
      = CheckOk unlink_model []
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at []))
        (ledgered (errno_ret ENOENT) 1) unlink_model = CheckOk unlink_model []
    ∧ check_unlinkat_row (unlink_call_at 3 0 (name_at [])) (ledgered (errno_ret ENOENT) 1)
        unlink_model = CheckOk unlink_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- …and admits nothing else: the empty name is found by the copy (157,
then 168-170) and `getname`'s -ENOMEM (146-148) precedes it.  The probe's
`ret=-ENOMEM -- empty` case is the run that shows the refusal.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem unlinkat_empty_path_enomem_rejected :
    check_unlinkat_row (unlink_call 0 (name_at [])) (ledgered (errno_ret ENOMEM) 1) unlink_model
      = CheckReject := rfl

/-- A dirfd of 3 declines, whatever the run holds at the name: the model
has no directory to start the walk in, so neither the kernel's -EBADF nor
the map's own answer — the key is present, remove it — is claimed: a
closed fd is -EBADF in `path_init` (fs/namei.c:2610-2611) and a
non-directory -ENOTDIR (2621-2622), and the model has neither fact.  The
ledger is the fetched name, since `getname` ran before `path_init`.  The
probe's `fail-closed -- dirfd-bad` case is the run that shows it.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem unlinkat_other_dirfd_unmodeled :
    check_unlinkat_row (unlink_call_at 3 0 (name_at [97])) (ledgered 0 2) unlink_model
      = CheckUnmodeled
    ∧ check_unlinkat_row (unlink_call_at 3 0 (name_at [97])) (ledgered (errno_ret EBADF) 2)
        unlink_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- THE WIDTHS.  `SYSCALL_DEFINE3(unlinkat, int, dfd, …, int, flag)`
receives each as an `int`, cast down from the register by
`__SC_CAST` in `__SYSCALL_DEFINEx`.  So the dirfd 2^32-100 is AT_FDCWD
and the removal proceeds; the flag word 2^32 is 0 and 2^32+512 is
AT_REMOVEDIR — which on a held file is `may_delete`'s -ENOTDIR (3285-3286)
— and an all-ones word is a bad flag, -EINVAL with no ledger.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:unlinkat,do_unlinkat,vfs_unlink,do_rmdir,may_delete@v6.18.46 -/
theorem unlinkat_arguments_are_ints :
    check_unlinkat_row (unlink_call_at (Z_to_bv 64 4294967196) 0 (name_at [97])) (ledgered 0 2)
      unlink_model = CheckOk unlinked_model []
    ∧ check_unlinkat_row (unlink_call 4294967296 (name_at [97])) (ledgered 0 2) unlink_model
      = CheckOk unlinked_model []
    ∧ check_unlinkat_row (unlink_call 4294967808 (name_at [97])) (ledgered (errno_ret ENOTDIR) 2)
        unlink_model = CheckOk unlink_model []
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 (-1)) (name_at [97]))
        (mkEffect (errno_ret EINVAL) [] []) unlink_model = CheckOk unlink_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- …and a flag word of 2^32 is not -EINVAL: a checker comparing the full
register would refuse the removal Linux performs; the probe's
`conform -- flag-trunc` case is the run, returning 0 where this pin
refuses -EINVAL.
kernel: arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST; fs/namei.c:unlinkat@v6.18.46 -/
theorem unlinkat_flag_2_pow_32_einval_rejected :
    check_unlinkat_row (unlink_call 4294967296 (name_at [97])) (mkEffect (errno_ret EINVAL) [] [])
      unlink_model = CheckReject := rfl

/-! ## The shape a fuzz harness actually issues

Issue #562's harness unlinks the temporary file it writes by an ABSOLUTE
name under /tmp.  The /tmp arm answers that shape: the removal of a key the
run holds, since the ruling on #1136 the -ENOENT of one it does not, and
since #1193 the -EISDIR of a directory the run's own keys imply; these pin
each from the sides a probe cannot reach.  An absolute name under any
OTHER directory is still the separator guard's decline. -/

/-- The harness's own call on a name the run does not hold: the empty image
the model starts a run with and an EMPTY declared /tmp.  The path is one the
/tmp arm names, so the separator gate is not what answers it.  The run
declared nothing at that name and created nothing there, and the privacy
premise makes the run's own table the whole truth about the directory, so
the answer is the real -ENOENT Linux gives for a negative dentry
(`lookup_one_qstr_excl`, fs/namei.c:1713-1715): the ruling on #1136.
Nothing moves — the model handed back is the one handed in — and the
success a kernel holding the file would return is refused, which is what
keeps the answer from being a licence to remove: `do_unlinkat`'s
`if (!IS_ERR(dentry))` (4731) skips the block that reaches `vfs_unlink` (4741).
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_tmp_key_not_held_is_enoent :
    check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered (errno_ret ENOENT) 13)
        empty_model = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13) empty_model
        = CheckReject := ⟨rfl, rfl⟩

/-- THE REMOVAL ITSELF, over a /tmp the run DECLARED: `fs_seed_tmp` seeds
the one component "out.gif" under "/tmp/", and `do_unlinkat`
(fs/namei.c:4741) reaches `vfs_unlink`.  The key is gone afterwards and nothing
else moved: the model is the empty one.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem unlinkat_tmp_declared_key_removed :
    check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13)
      tmp_declared_model = CheckOk empty_model [] := rfl

/-- THE SECOND UNLINK: a key the run DECLARED and then removed ITSELF.  The
first call takes the key out and returns 0; the second reads the table that
call left and answers -ENOENT, and a second success is refused.  Stated as
Rocq states it, over the model the first call HANDS BACK rather than over a
fixture spelling it; the model is read off `unlinkat_tmp_declared_key_removed`'s
right-hand side, which is why this sits below that theorem rather than in the
Rocq file's order.

DOCUMENTARY, and saying so is worth more than a stronger-sounding claim: it
distinguishes no kernel this file does not already distinguish.  Its first
call is `unlinkat_tmp_declared_key_removed`, and since the arm reads only
`m_fs`, the model the removal leaves is indistinguishable to it from the
empty one `unlinkat_tmp_key_not_held_is_enoent` is stated over.  What it
records is the COMPOSITION a program that cleans up after itself makes.
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_tmp_removed_key_second_unlink_is_enoent :
    match check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13)
        tmp_declared_model with
    | CheckOk m1 [] =>
        m_fs m1 = []
        ∧ check_unlinkat_row (unlink_call 0 (name_at abs_gif_name))
            (ledgered (errno_ret ENOENT) 13) m1 = CheckOk m1 []
        ∧ check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13) m1
            = CheckReject
    | _ => False := by
  rw [unlinkat_tmp_declared_key_removed]
  exact ⟨rfl, rfl, rfl⟩

/-- The SAME image written as a raw key rather than as a declaration.  The
two are one model, so the arm cannot tell a declared entry from an image
key that spells the same path, and this case says so: the removal goes
through `do_unlinkat` (fs/namei.c:4741) to `vfs_unlink` the same way.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem unlinkat_tmp_image_key_removed :
    check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13)
      abs_gif_model = CheckOk empty_model [] := rfl

/-- What stays declined under /tmp, each on the image that HOLDS the key,
so that none of them is declining for want of the file.  AT_REMOVEDIR
(fs/namei.c:4780) on a file is -ENOTDIR in `may_delete` (3285-3286), but
which answer it is turns on /tmp holding a directory, which this rung
defers.  A second component needs a walk.  "/tmp" itself, "/tmp/",
"/tmp/." and "/tmp/.." name the directory rather than a file in it, and
each is answered from a directory fact the flat map does not hold:
`do_unlinkat` for the last three — its `slashes:` label for "/tmp/"
(4767-4769) and its `type != LAST_NORM` test for the two dot names
(4720-4722) — and `may_delete` for "/tmp", whose last component is
LAST_NORM and reaches the victim, where the answer turns on WHO runs it:
write permission on the parent "/" is tested first (`inode_permission`,
3274-3276), so root sees the -EISDIR of `d_is_dir(victim)` (3289-3290)
and an unprivileged run -EACCES.  One more reason the rung declines it.
kernel: fs/namei.c:unlinkat,may_delete,do_unlinkat@v6.18.46 -/
theorem unlinkat_tmp_excluded_shapes_unmodeled :
    check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at abs_gif_name))
      (ledgered (errno_ret ENOTDIR) 13) tmp_shapes_model = CheckUnmodeled
    ∧ check_unlinkat_row (unlink_call 0 (name_at tmp_d_f)) (ledgered 0 9)
      tmp_shapes_model = CheckUnmodeled
    ∧ check_unlinkat_row (unlink_call 0 (name_at [47, 116, 109, 112]))
      (ledgered (errno_ret EISDIR) 5) tmp_shapes_model = CheckUnmodeled
    ∧ check_unlinkat_row (unlink_call 0 (name_at [47, 116, 109, 112, 47]))
      (ledgered (errno_ret EISDIR) 6) tmp_shapes_model = CheckUnmodeled
    ∧ check_unlinkat_row (unlink_call 0 (name_at [47, 116, 109, 112, 47, 46]))
      (ledgered (errno_ret EISDIR) 7) tmp_shapes_model = CheckUnmodeled
    ∧ check_unlinkat_row (unlink_call 0 (name_at [47, 116, 109, 112, 47, 46, 46]))
      (ledgered (errno_ret EISDIR) 8) tmp_shapes_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE IMPLIED DIRECTORY UNDER /tmp IS ANSWERED, not declined as it is in
the working directory: "/tmp/d" over an image holding "/tmp/d/f" is a
directory the run's own declaration put there, and Linux refuses to unlink
a directory in `may_delete` (fs/namei.c:3289-3290, the `d_is_dir(victim)`
test of the non-`isdir` call), reached from `vfs_unlink` (4658) before
anything is removed.  The victim is the run's own, so the tests ahead of
it pass — write permission on the sticky, world-writable /tmp (3274-3276)
and `check_sticky` for the owner (3280-3283) — and -EISDIR is the answer
where POSIX allows -EPERM.  Nothing moves, the removal a flat map would
have performed is refused, and the trailing separator changes neither
half: for "/tmp/d/" the same -EISDIR comes one step earlier, from
`do_unlinkat`'s `slashes:` label (the `last.name[last.len]` test, 4734,
then `d_is_dir(dentry)`, 4767-4768), before `vfs_unlink` is reached.
The Rocq example is `unlinkat_tmp_implied_directory_is_eisdir`.
kernel: fs/namei.c:link_path_walk,do_unlinkat,vfs_unlink,may_delete@v6.18.46 -/
theorem unlinkat_tmp_implied_directory_is_eisdir :
    check_unlinkat_row (unlink_call 0 (name_at tmp_d)) (ledgered (errno_ret EISDIR) 7)
      tmp_only_dir_model = CheckOk tmp_only_dir_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at tmp_d)) (ledgered 0 7) tmp_only_dir_model
      = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at tmp_d_slash)) (ledgered (errno_ret EISDIR) 8)
        tmp_only_dir_model = CheckOk tmp_only_dir_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at tmp_d_slash)) (ledgered 0 8) tmp_only_dir_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- THE ORDER OF THE TWO /tmp RULES, which is the whole of what keeps the
answer above from being -ENOENT: "/tmp/d" is not a key the run holds, so
the rule that answers -ENOENT for a name not held would call it absent;
`check_unlinkat_tmp` tests `fs_under` BEFORE the lookup, so the directory
wins, and the -ENOENT is refused.  The honest twin of that order is a name
with nothing under it, "/tmp/out.gif" on the same image, where the
not-held rule still answers -ENOENT (`lookup_one_qstr_excl`,
fs/namei.c:1713-1715) and -EISDIR is refused.  The Rocq example is
`unlinkat_tmp_implied_directory_precedes_not_held`.
kernel: fs/namei.c:do_unlinkat,may_delete,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_tmp_implied_directory_precedes_not_held :
    check_unlinkat_row (unlink_call 0 (name_at tmp_d)) (ledgered (errno_ret ENOENT) 7)
      tmp_only_dir_model = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at tmp_d)) (ledgered (errno_ret EISDIR) 7)
        tmp_only_dir_model = CheckOk tmp_only_dir_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered (errno_ret ENOENT) 13)
        tmp_only_dir_model = CheckOk tmp_only_dir_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered (errno_ret EISDIR) 13)
        tmp_only_dir_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A sibling in the same declared /tmp is untouched by the -EISDIR: on the
image holding both "/tmp/d/f" and "/tmp/out.gif", the plain key is removed
(`do_unlinkat`, fs/namei.c:4741, through `vfs_unlink`) and the image left
is the one holding the directory's key alone.  The Rocq example is
`unlinkat_tmp_implied_directory_sibling_still_unlinks`, which reads the
key back off the model the call hands out; the model here is named.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem unlinkat_tmp_implied_directory_sibling_still_unlinks :
    fs_lookup (m_fs tmp_shapes_model) tmp_d_f = some [104]
    ∧ check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13) tmp_shapes_model
      = CheckOk tmp_only_dir_model []
    ∧ fs_lookup (m_fs tmp_only_dir_model) abs_gif_name = none
    ∧ fs_lookup (m_fs tmp_only_dir_model) tmp_d_f = some [104] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The trailing separator on a held /tmp key: "/tmp/out.gif/" reaches the
found tail as "a/" does in the working directory, and `do_unlinkat`'s
`slashes:` label answers -ENOTDIR for the regular file (fs/namei.c:4734,
4767-4771), which survives; the removal is refused.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem unlinkat_tmp_trailing_slash_on_a_file_is_enotdir :
    check_unlinkat_row (unlink_call 0 (name_at (abs_gif_name ++ [47])))
      (ledgered (errno_ret ENOTDIR) 14) tmp_declared_model = CheckOk tmp_declared_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at (abs_gif_name ++ [47]))) (ledgered 0 14)
        tmp_declared_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The open-descriptor guard holds under /tmp as it does in the working
directory: a held /tmp key some fd is open on is declined, not removed.
model: a file fd records its path, not an inode; an unlinked-but-open file
has no state to hold it, so the spec declines and the checker must too. -/
theorem unlinkat_tmp_open_fd_unmodeled :
    check_unlinkat_row (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13) tmp_open_fd_model
      = CheckUnmodeled := rfl

set_option maxRecDepth 8192 in
/-- The `NAME_MAX` boundary (`include/uapi/linux/limits.h`) on this arm,
from both sides, as the openat twin has it: both arms draw the line at the
same place, since "held" is one predicate over one key space, and a
component the open can mint and the unlink cannot remove would be a file
the run could not get rid of.  A component of 255 bytes is REMOVED
(`do_unlinkat`, fs/namei.c:4741, through `vfs_unlink`) and one of 256 is
DECLINED: Linux answers -ENAMETOOLONG for it from the filesystem's own
lookup — `simple_lookup` (fs/libfs.c:71-72), which tmpfs directories use —
reached from `do_unlinkat`'s lookup (4729), and the model claims nothing
past the bound.
kernel: fs/namei.c:do_unlinkat,vfs_unlink; fs/libfs.c:simple_lookup@v6.18.46 -/
theorem unlinkat_tmp_name_max_boundary :
    check_unlinkat_row (unlink_call 0 (name_at (tmp_key name255))) (ledgered 0 261)
      tmp_name255_model = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at (tmp_key name256))) (ledgered 0 262)
      tmp_name256_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- The bound is tested BEFORE the implied directory, on both sides of the
checker.  A key the declaration put under a 256-byte component makes
`fs_under` true at that component, and the checker still declines rather
than accept `may_delete`'s -EISDIR (fs/namei.c:3289-3290) for it: Linux
never reaches `may_delete` for this name, since `do_unlinkat`'s lookup
(4729) goes to the filesystem's own `simple_lookup`, which answers
-ENAMETOOLONG for a component over NAME_MAX (fs/libfs.c:71-72) before any
dentry exists to be a directory.  So an -EISDIR offered here is declined
along with the removal — the mutation sweep found the order of the two
tests pinned by nothing before this.
kernel: fs/namei.c:do_unlinkat,may_delete; fs/libfs.c:simple_lookup@v6.18.46 -/
theorem unlinkat_tmp_name_max_precedes_implied_directory :
    check_unlinkat_row (unlink_call 0 (name_at (tmp_key name256)))
      (ledgered (errno_ret EISDIR) 262) tmp_name256_under_model = CheckUnmodeled
    ∧ check_unlinkat_row (unlink_call 0 (name_at (tmp_key name256))) (ledgered 0 262)
      tmp_name256_under_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- A NAME the declaration could not put anywhere: a component with a NUL
byte in it.  `fs_seed_tmp` drops it, so the run holds nothing at that
name, and no pathname could reach it in any case, since `read_cstr` stops
at the NUL.  The declaration is not an image the model can be surprised by.
model: `fs_seed_tmp` drops a component `tmp_nul_free` refuses; a State fact,
no kernel line decides it. -/
theorem unlinkat_tmp_nul_name_is_not_seeded :
    m_fs (fixture_of (fs := fs_seed_tmp [] [([111, 0, 117, 116], [104])])) = [] := rfl

/-- The rejecting half, reached through the name the walk WOULD end at.
"out.gif" carries no separator, so it is answered rather than declined,
and on this image it is answered -ENOENT: `fs_under` is a COMPONENT prefix
and "/tmp/out.gif" does not live under "out.gif".  A kernel that removed
something through it — `lookup_one_qstr_excl` finding a positive dentry
(fs/namei.c:1692-1694, then `found:`) where the working directory holds
none — is not admitted.  Without this the two removals above are
consistent with a model that reads the flat map as a directory tree.
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_absolute_basename_success_rejected :
    check_unlinkat_row (unlink_call 0 (name_at gif_basename)) (ledgered 0 8) abs_gif_model
      = CheckReject := rfl

/-- …and the answer it does accept: the -ENOENT `lookup_one_qstr_excl`
gives a name the directory lacks (fs/namei.c:1713-1715), so the rejection above
is about the removal and not about the ledger.
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_absolute_basename_is_enoent :
    check_unlinkat_row (unlink_call 0 (name_at gif_basename)) (ledgered (errno_ret ENOENT) 8)
      abs_gif_model = CheckOk abs_gif_model [] := rfl

/-! ## Lies no Rocq example reaches

Rocq's Cases file has no example for any of these — the C probe carries
that half for Rocq — so none is drift, but they are exactly the holes
`CLAUDE.md` warns about: a change made to the checker and the spec alike
leaves every proof closing, and only a concrete answer from outside
separates them.  Each is the lie a mutant of the checker told, refused,
or the honest answer a mutant withheld, required. -/

/-- A held key is removed and answers 0, and NOTHING else the map could
say: Linux cannot say -ENOENT for a name it holds, since
`lookup_one_qstr_excl`'s -ENOENT needs a negative dentry (fs/namei.c:1713-1715)
or a DEAD parent (1698-1699) — a working directory removed under the run,
which the privacy premise rules out — and `do_unlinkat` then goes on to
`vfs_unlink` (4741).  A checker that accepted any errno on the removal arm
passes every conformance run — a kernel never volunteers the lie — and
every twin above, which is why this one exists.
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_held_key_enoent_rejected :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret ENOENT) 2)
      unlink_model = CheckReject := rfl

/-- What the removal arm admits BESIDE the removal: the five environment
failures the model does not track, each with the model unchanged.
-ENOMEM from `getname`'s allocation (fs/namei.c:146-148) or the dentry's
(`lookup_one_qstr_excl`, 1701-1703); -EROFS from `mnt_want_write`
(4724; `mnt_get_write_access`, fs/namespace.c:476-478); -EACCES from the
parent's `inode_permission` in `may_delete` (3274-3276, through
`generic_permission`); -EPERM from `may_delete`'s sticky and immutable
tests (3277-3283); -EBUSY from `vfs_unlink`'s mount check (4669-4670).
A checker that refused the set would fail a real run that hit one; a
checker that widened it would accept answers Linux never gives, which the
next pin refuses.
kernel: fs/namei.c:do_unlinkat,vfs_unlink,may_delete,generic_permission,lookup_one_qstr_excl,getname_flags; fs/namespace.c:mnt_get_write_access@v6.18.46 -/
theorem unlinkat_removal_env_failures_admitted :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret ENOMEM) 2) unlink_model
      = CheckOk unlink_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret EROFS) 2) unlink_model
      = CheckOk unlink_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret EACCES) 2) unlink_model
      = CheckOk unlink_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret EPERM) 2) unlink_model
      = CheckOk unlink_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret EBUSY) 2) unlink_model
      = CheckOk unlink_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered 0 2) unlink_model
      = CheckOk unlinked_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- …and the set is closed: -EBADF is `path_init`'s answer for a closed
dirfd (fs/namei.c:2610-2611), which AT_FDCWD never reaches, and unlink
returns no positive value.  The probe's `ret=-EBADF -- two-files` and
`ret=1 -- two-files` cases are the runs that show it.
kernel: fs/namei.c:path_init,do_unlinkat@v6.18.46 -/
theorem unlinkat_removal_other_returns_rejected :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered (errno_ret EBADF) 2) unlink_model
      = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered 1 2) unlink_model
      = CheckReject :=
  ⟨rfl, rfl⟩

/-- AT_REMOVEDIR on a held FILE: `do_rmdir` looks the name up (4600) and
`vfs_rmdir` asks `may_delete` with `isdir` set, whose `!d_is_dir(victim)`
is -ENOTDIR (fs/namei.c:3285-3286).  The file survives, and the arm is
deterministic: it admits neither the removal nor an injectable errno,
since -ENOTDIR is not in `unlinkat_errnos` and 0 is refused.
kernel: fs/namei.c:unlinkat,do_rmdir,may_delete@v6.18.46 -/
theorem unlinkat_rmdir_on_a_file_is_enotdir :
    check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [97]))
      (ledgered (errno_ret ENOTDIR) 2) unlink_model = CheckOk unlink_model [] := rfl

/-- …the two refusals: `may_delete`'s -ENOTDIR (3285-3286) stops
`vfs_rmdir` before anything is removed, and -ENOMEM is not an answer of
this arm — `getname`'s (146-148) precedes the copy and
`lookup_one_qstr_excl`'s (1701-1703) is a lookup that here succeeded.  The
probe's `ret=0 -- rmdir-file` and `ret=-ENOMEM -- rmdir-file` cases are
the runs that show them.
kernel: fs/namei.c:unlinkat,do_rmdir,may_delete,getname_flags,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_rmdir_on_a_file_refuses_removal_and_enomem :
    check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [97])) (ledgered 0 2)
      unlink_model = CheckReject
    ∧ check_unlinkat_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [97]))
        (ledgered (errno_ret ENOMEM) 2) unlink_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- unlinkat writes, zeroes, unmaps and copies no user memory:
`SYSCALL_DEFINE3(unlinkat)` reads the name once, at fs/namei.c:4782, and
passes the `struct filename` down; `do_unlinkat` (4741) then hands
`vfs_unlink` the dentry and the inode, which is all the removal touches.
So a ledger that claims a write, a zero-fill, an unmap or a copy beside
the copy-in is a lie, and `check_unlink_result`'s six-field match is what
refuses it — a checker matching only the return value would take all four.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem unlinkat_forged_ledgers_rejected :
    check_unlinkat_row (unlink_call 0 (name_at [97]))
      (with_copyins [(8192, 2)] (SyscallEffect.mkEffectU 0 [(8192, [0])] [] [] [] []))
      unlink_model = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97]))
      (with_copyins [(8192, 2)] (SyscallEffect.mkEffectU 0 [] [(8192, 4096)] [] [] []))
      unlink_model = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97]))
      (with_copyins [(8192, 2)] (SyscallEffect.mkEffectU 0 [] [] [(8192, 4096)] [] []))
      unlink_model = CheckReject
    ∧ check_unlinkat_row (unlink_call 0 (name_at [97]))
      (with_copyins [(8192, 2)] (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 8192 8192 1] []))
      unlink_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A path some open descriptor names is declined, not removed: Linux would
unlink it and keep the inode alive behind fd 3, and a file fd here records
the PATH it was opened on, not an inode, so the unlinked-but-open file has
no representation.  Dropping the `fd_names_path` guard makes this a plain
removal, and nothing above notices.  The probe's `fail-closed -- openfd`
case is the run that shows the decline.
model: a file fd records its path, not an inode; an unlinked-but-open file
has no state to hold it, so the spec declines and the checker must too. -/
theorem unlinkat_open_fd_unmodeled :
    check_unlinkat_row (unlink_call 0 (name_at [97])) (ledgered 0 2) open_fd_model
      = CheckUnmodeled := rfl

set_option maxRecDepth 8192 in
/-- The NAME_MAX boundary on the working-directory arm, the twin of the
/tmp one above: a 255-byte component is removed, a 256-byte one is
declined — Linux answers -ENAMETOOLONG for it from the filesystem's
lookup, `simple_lookup` (fs/libfs.c:71-72) being the one tmpfs uses,
reached from `do_unlinkat` (4729), and the model claims nothing past the
bound.  Removing the bound from the cwd arm alone leaves the /tmp twin
green.
kernel: fs/namei.c:do_unlinkat; fs/libfs.c:simple_lookup@v6.18.46 -/
theorem unlinkat_cwd_name_max_boundary :
    check_unlinkat_row (unlink_call 0 (name_at name255)) (ledgered 0 256) cwd_name255_model
      = CheckOk empty_model []
    ∧ check_unlinkat_row (unlink_call 0 (name_at name256)) (ledgered 0 257) cwd_name256_model
      = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-! ## The witness

`unlinkat_witness` names, for each call, one outcome the spec admits, and
`unlinkat_witness_ok` in the checker's file proves the checker accepts
it.  What that theorem cannot say is WHICH outcome: a witness that named
-EISDIR where the spec's one answer is -ENOTDIR would be refused by the
checker and the theorem would stop closing, but a witness that named a
different admitted answer on an alternative — or declined where it could
answer — is still receptive.  These pin the answer on every arm, so that a
mutant of the witness alone does not pass.  On the removal arm the witness
picks `witness_errno`, -ENOMEM, the LEFT branch of the alternative, and
never builds the removed file system. -/

/-- Ahead of the copy-in: the bad flag word, with no ledger.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem unlinkat_witness_bad_flags :
    unlinkat_witness_row (unlink_call 1 (name_at [97])) a_empty_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) a_empty_model [] := rfl

set_option maxRecDepth 100000 in
/-- `getname`'s -ENAMETOOLONG (fs/namei.c:207-210), with the PATH_MAX ledger.
kernel: fs/namei.c:getname_flags; include/uapi/linux/limits.h:PATH_MAX@v6.18.46 -/
theorem unlinkat_witness_toolong :
    unlinkat_witness_row (unlink_call 0 endless) unlink_model
      = Ok (ledgered (errno_ret ENAMETOOLONG) 4096) unlink_model [] := rfl

/-- `getname`'s -EFAULT (lib/strncpy_from_user.c:154; 91-92 for the NUL
off the mapping), one and two bytes of ledger.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:strncpy_from_user,do_strncpy_from_user@v6.18.46 -/
theorem unlinkat_witness_fault :
    unlinkat_witness_row (unlink_call 0 unmapped) unlink_model
      = Ok (ledgered (errno_ret EFAULT) 1) unlink_model []
    ∧ unlinkat_witness_row (unlink_call 0 unterminated) unlink_model
      = Ok (ledgered (errno_ret EFAULT) 2) unlink_model [] :=
  ⟨rfl, rfl⟩

/-- `getname`'s -ENOENT for the empty name (fs/namei.c:168-170), under
either flag word and ahead of the dirfd.
kernel: fs/namei.c:getname_flags,unlinkat,path_init@v6.18.46 -/
theorem unlinkat_witness_empty_path :
    unlinkat_witness_row (unlink_call 0 (name_at [])) unlink_model
      = Ok (ledgered (errno_ret ENOENT) 1) unlink_model []
    ∧ unlinkat_witness_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [])) unlink_model
      = Ok (ledgered (errno_ret ENOENT) 1) unlink_model []
    ∧ unlinkat_witness_row (unlink_call_at 3 0 (name_at [])) unlink_model
      = Ok (ledgered (errno_ret ENOENT) 1) unlink_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- The dirfd decline, and the guards that decline in the working
directory: the open descriptor and the 256-byte name.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- dirfd-bad -/
theorem unlinkat_witness_declines :
    unlinkat_witness_row (unlink_call_at 3 0 (name_at [97])) unlink_model = Unmodeled
    ∧ unlinkat_witness_row (unlink_call 0 (name_at [97])) open_fd_model = Unmodeled :=
  ⟨rfl, rfl⟩

/-- The implied directory is answered (#1753): `may_delete`'s -EISDIR
(fs/namei.c:3289-3290) for unlink and the filesystem's -ENOTEMPTY through
`vfs_rmdir` (4552) for AT_REMOVEDIR.
kernel: fs/namei.c:may_delete,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem unlinkat_witness_implied_directory :
    unlinkat_witness_row (unlink_call 0 (name_at [97])) implied_dir_model
      = Ok (ledgered (errno_ret EISDIR) 2) implied_dir_model []
    ∧ unlinkat_witness_row (unlink_call 512 (name_at [97])) implied_dir_model
      = Ok (ledgered (errno_ret ENOTEMPTY) 2) implied_dir_model [] :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- …the 256-byte name, from both sides: 255 is answered on the removal
arm and 256 declined, in the working directory and under /tmp.
probe: testing/syscall-check/tests/unlinkat_spec.c#fail-closed -- name256 -/
theorem unlinkat_witness_name_max_boundary :
    unlinkat_witness_row (unlink_call 0 (name_at name255)) cwd_name255_model
      = Ok (ledgered (errno_ret ENOMEM) 256) cwd_name255_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at name256)) cwd_name256_model = Unmodeled
    ∧ unlinkat_witness_row (unlink_call 0 (name_at (tmp_key name255))) tmp_name255_model
      = Ok (ledgered (errno_ret ENOMEM) 261) tmp_name255_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at (tmp_key name256))) tmp_name256_model
      = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- …and the 256-byte name stays declined when the declaration put a key
under it: the witness tests the bound before the implied directory, as the
checker does (`unlinkat_tmp_name_max_precedes_implied_directory`), because
`simple_lookup`'s -ENAMETOOLONG (fs/libfs.c:71-72) comes before any
directory could be found at the name.
kernel: fs/namei.c:do_unlinkat; fs/libfs.c:simple_lookup@v6.18.46 -/
theorem unlinkat_witness_name_max_precedes_implied_directory :
    unlinkat_witness_row (unlink_call 0 (name_at (tmp_key name256))) tmp_name256_under_model
      = Unmodeled :=
  rfl

/-- The two arms of "/", "." and "..": -EISDIR on the plain call from
`do_unlinkat`'s type test (fs/namei.c:4720-4722); -EBUSY, -EINVAL and
-ENOTEMPTY under AT_REMOVEDIR from `do_rmdir`'s three cases (4584-4592).
kernel: fs/namei.c:unlinkat,link_path_walk,do_unlinkat,do_rmdir@v6.18.46 -/
theorem unlinkat_witness_typed_names :
    unlinkat_witness_row (unlink_call 0 (name_at [47])) empty_model
      = Ok (ledgered (errno_ret EISDIR) 2) empty_model []
    ∧ unlinkat_witness_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [47])) empty_model
      = Ok (ledgered (errno_ret EBUSY) 2) empty_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at [46])) empty_model
      = Ok (ledgered (errno_ret EISDIR) 2) empty_model []
    ∧ unlinkat_witness_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46])) empty_model
      = Ok (ledgered (errno_ret EINVAL) 2) empty_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at [46, 46])) empty_model
      = Ok (ledgered (errno_ret EISDIR) 3) empty_model []
    ∧ unlinkat_witness_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46, 46])) empty_model
      = Ok (ledgered (errno_ret ENOTEMPTY) 3) empty_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The working-directory arm: a held key draws `witness_errno`, -ENOMEM
(`lookup_one_qstr_excl`'s `d_alloc` failure, fs/namei.c:1701-1703, is one
place Linux can say it on this path), the model unchanged; a held key
under AT_REMOVEDIR or through a trailing separator is `may_delete`'s and
`do_unlinkat`'s -ENOTDIR (3285-3286; 4767-4771), the separator ahead of
the open-descriptor guard; an absent key is -ENOENT (1713-1715).
kernel: fs/namei.c:unlinkat,do_unlinkat,may_delete,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_witness_cwd_arm :
    unlinkat_witness_row (unlink_call 0 (name_at [97])) unlink_model
      = Ok (ledgered (errno_ret ENOMEM) 2) unlink_model []
    ∧ unlinkat_witness_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [97])) unlink_model
      = Ok (ledgered (errno_ret ENOTDIR) 2) unlink_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at [97, 47])) unlink_model
      = Ok (ledgered (errno_ret ENOTDIR) 3) unlink_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at [97, 47])) open_fd_model
      = Ok (ledgered (errno_ret ENOTDIR) 3) open_fd_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at [97])) empty_model
      = Ok (ledgered (errno_ret ENOENT) 2) empty_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The /tmp arm: the implied directory is `may_delete`'s -EISDIR
(fs/namei.c:3289-3290); a name not held is -ENOENT (1713-1715); a held
key draws -ENOMEM as above; a held key through a trailing separator is
-ENOTDIR (4767-4771).
kernel: fs/namei.c:do_unlinkat,may_delete,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_witness_tmp_arm :
    unlinkat_witness_row (unlink_call 0 (name_at tmp_d)) tmp_only_dir_model
      = Ok (ledgered (errno_ret EISDIR) 7) tmp_only_dir_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at abs_gif_name)) tmp_only_dir_model
      = Ok (ledgered (errno_ret ENOENT) 13) tmp_only_dir_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at abs_gif_name)) tmp_declared_model
      = Ok (ledgered (errno_ret ENOMEM) 13) tmp_declared_model []
    ∧ unlinkat_witness_row (unlink_call 0 (name_at (abs_gif_name ++ [47]))) tmp_declared_model
      = Ok (ledgered (errno_ret ENOTDIR) 14) tmp_declared_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- …and its declines: AT_REMOVEDIR under /tmp, a second component, an
open descriptor on the key.
model: each is a decline of `unlinkat_tmp_spec`'s rung, the reasons on
`unlinkat_tmp_excluded_shapes_unmodeled` and `unlinkat_tmp_open_fd_unmodeled`
above; no kernel answer is claimed. -/
theorem unlinkat_witness_tmp_declines :
    unlinkat_witness_row (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at abs_gif_name))
      tmp_shapes_model = Unmodeled
    ∧ unlinkat_witness_row (unlink_call 0 (name_at tmp_d_f)) tmp_shapes_model = Unmodeled
    ∧ unlinkat_witness_row (unlink_call 0 (name_at abs_gif_name)) tmp_open_fd_model = Unmodeled :=
  ⟨rfl, rfl, rfl⟩

-- lean-port sentinel: ticket V-Fs-Namei appends below this line
section V_Fs_Namei

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Fs-Namei — unlinkat over the real table

Kernel lines in this section refer to Linux v6.18.46, commit 1f99e9ab748f.
The observed-read mutation in `getname_reads.c` and the final-filesystem
comparison in `unlinkat_spec.c` are harness checks: their observations
are not fields of `SyscallEffect`, so `check_syscall` does not judge them. -/

/-- The lookup is independent of the argument registers and memory.
model: the generated table's lookup at 35 -/
theorem lookup_unlinkat_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 35 args mem wmem).in_sysno)
      = some arm_unlinkat :=
  lookup_ca_checked_table_unlinkat

/-- The implied directory is answered through the table as through the row
checker: -EISDIR from the directory type check at fs/namei.c:3289-3290 and
-ENOTEMPTY from `vfs_rmdir` (4552).
kernel: fs/namei.c:may_delete,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem unlinkat_implied_directory_answers_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97])) (ledgered (errno_ret EISDIR) 2)
      implied_dir_model = CheckOk implied_dir_model []
    ∧ check_syscall (unlink_call 512 (name_at [97])) (ledgered (errno_ret ENOTEMPTY) 2)
      implied_dir_model = CheckOk implied_dir_model [] :=
  ⟨rfl, rfl⟩

/-- The unrealizable file-and-child image gets the directory's answers ahead
of the lookup; fs/namei.c:3289-3290 checks the victim type.
kernel: fs/namei.c:may_delete,vfs_rmdir; fs/libfs.c:simple_rmdir@v6.18.46 -/
theorem unlinkat_implied_directory_unrealizable_image_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97])) (ledgered (errno_ret EISDIR) 2)
      unrealizable_model = CheckOk unrealizable_model []
    ∧ check_syscall (unlink_call 512 (name_at [97])) (ledgered (errno_ret ENOTEMPTY) 2)
      unrealizable_model = CheckOk unrealizable_model [] :=
  ⟨rfl, rfl⟩

/-- The held file is removed through fs/namei.c:4741; the sibling key survives.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem unlinkat_byte_prefix_is_not_a_directory_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97])) (ledgered 0 2) ab_model
      = CheckOk ab_unlinked_model [] := rfl

/-- The bad flag returns before pathname acquisition at fs/namei.c:4777-4782, refusing a claimed copy-in.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem unlinkat_bad_flags_records_no_copyin_over_the_real_table :
    check_syscall (unlink_call 1 (name_at [97])) (ledgered (errno_ret EINVAL) 2)
      a_empty_model = CheckReject := rfl

/-- The bad flag returns -EINVAL at fs/namei.c:4777-4778 with no pathname copy-in.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem unlinkat_bad_flags_empty_ledger_ok_over_the_real_table :
    check_syscall (unlink_call 1 (name_at [97])) (mkEffect (errno_ret EINVAL) [] [])
      a_empty_model = CheckOk a_empty_model [] := rfl

/-- Removal follows pathname acquisition at fs/namei.c:4782 and :157; a dropped copy-in is refused.
kernel: fs/namei.c:unlinkat,getname_flags@v6.18.46 -/
theorem unlinkat_removal_needs_the_copyin_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97])) (mkEffect 0 [] []) ab_model
      = CheckReject := rfl

/-- The pathname acquisition at fs/namei.c:157 needs the terminating NUL; omitting it from the logical copy-in ledger is refused.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem unlinkat_copyin_extent_is_the_nul_terminated_prefix_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97])) (ledgered 0 1) ab_model
      = CheckReject := rfl

/-- The trailing separator reaches -ENOTDIR at fs/namei.c:4734-4735 and :4767-4771.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem unlinkat_trailing_slash_on_a_file_is_enotdir_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97, 47])) (ledgered (errno_ret ENOTDIR) 3)
      unlink_model = CheckOk unlink_model [] := rfl

/-- The trailing separator takes the -ENOTDIR branch at fs/namei.c:4767-4771, refusing ret=0.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem unlinkat_trailing_slash_success_rejected_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97, 47])) (ledgered 0 3) unlink_model
      = CheckReject := rfl

/-- LAST_ROOT under AT_REMOVEDIR returns -EBUSY at fs/namei.c:4590-4591.
kernel: fs/namei.c:unlinkat,do_rmdir@v6.18.46 -/
theorem unlinkat_root_removedir_is_ebusy_over_the_real_table :
    check_syscall (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [47]))
      (ledgered (errno_ret EBUSY) 2) empty_model = CheckOk empty_model [] := rfl

/-- LAST_ROOT is handled at fs/namei.c:4590-4591 before lookup, refusing ret=-ENOENT.
kernel: fs/namei.c:unlinkat,do_rmdir,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_root_enoent_rejected_over_the_real_table :
    check_syscall (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [47]))
      (ledgered (errno_ret ENOENT) 2) empty_model = CheckReject := rfl

/-- The absent basename fails lookup at fs/namei.c:1713-1715, refusing ret=0.
kernel: fs/namei.c:lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_absolute_basename_success_rejected_over_the_real_table :
    check_syscall (unlink_call 0 (name_at gif_basename)) (ledgered 0 8) abs_gif_model
      = CheckReject := rfl

/-- The absent basename fails lookup at fs/namei.c:1713-1715 with -ENOENT.
kernel: fs/namei.c:lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_absolute_basename_is_enoent_over_the_real_table :
    check_syscall (unlink_call 0 (name_at gif_basename)) (ledgered (errno_ret ENOENT) 8)
      abs_gif_model = CheckOk abs_gif_model [] := rfl

/-- An absent /tmp key yields -ENOENT at fs/namei.c:1713-1715 (called at :4729); ret=0 is refused.
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_tmp_key_not_held_is_enoent_over_the_real_table :
    check_syscall (unlink_call 0 (name_at abs_gif_name)) (ledgered (errno_ret ENOENT) 13)
        empty_model = CheckOk empty_model []
    ∧ check_syscall (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13) empty_model
        = CheckReject := ⟨rfl, rfl⟩

/-- A held /tmp key reaches removal at fs/namei.c:4741.
kernel: fs/namei.c:do_unlinkat@v6.18.46 -/
theorem unlinkat_tmp_image_key_removed_over_the_real_table :
    check_syscall (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13)
      abs_gif_model = CheckOk empty_model [] := rfl

/-- The declared /tmp key reaches `vfs_unlink` through `do_unlinkat`
(fs/namei.c:4741), removing the held file.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem unlinkat_tmp_declared_key_removed_over_the_real_table :
    check_syscall (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13)
      tmp_declared_model = CheckOk empty_model [] := rfl

/-- After `do_unlinkat` removes the declared key, `lookup_one_qstr_excl`
finds a negative dentry on the second call, so -ENOENT replaces success.
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_tmp_removed_key_second_unlink_is_enoent_over_the_real_table :
    match check_syscall (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13)
        tmp_declared_model with
    | CheckOk m1 [] =>
        m_fs m1 = []
        ∧ check_syscall (unlink_call 0 (name_at abs_gif_name))
            (ledgered (errno_ret ENOENT) 13) m1 = CheckOk m1 []
        ∧ check_syscall (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13) m1
            = CheckReject
    | _ => False := by
  rw [unlinkat_tmp_declared_key_removed_over_the_real_table]
  exact ⟨rfl, rfl, rfl⟩

/-- These shapes need directory facts or a further walk: fs/namei.c:4780,
:3285-3290, :4767-4769 and :4720-4722 distinguish removal modes and final
component types, while :3274-3276 checks parent permission first.
kernel: fs/namei.c:unlinkat,may_delete,do_unlinkat@v6.18.46 -/
theorem unlinkat_tmp_excluded_shapes_unmodeled_over_the_real_table :
    check_syscall (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at abs_gif_name))
      (ledgered (errno_ret ENOTDIR) 13) tmp_shapes_model = CheckUnmodeled
    ∧ check_syscall (unlink_call 0 (name_at tmp_d_f)) (ledgered 0 9)
      tmp_shapes_model = CheckUnmodeled
    ∧ check_syscall (unlink_call 0 (name_at [47, 116, 109, 112]))
      (ledgered (errno_ret EISDIR) 5) tmp_shapes_model = CheckUnmodeled
    ∧ check_syscall (unlink_call 0 (name_at [47, 116, 109, 112, 47]))
      (ledgered (errno_ret EISDIR) 6) tmp_shapes_model = CheckUnmodeled
    ∧ check_syscall (unlink_call 0 (name_at [47, 116, 109, 112, 47, 46]))
      (ledgered (errno_ret EISDIR) 7) tmp_shapes_model = CheckUnmodeled
    ∧ check_syscall (unlink_call 0 (name_at [47, 116, 109, 112, 47, 46, 46]))
      (ledgered (errno_ret EISDIR) 8) tmp_shapes_model = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- For the run's own directory under /tmp, `may_delete` returns -EISDIR
(fs/namei.c:3289-3290); with a trailing separator, `do_unlinkat` returns it
at :4767-4768 before reaching `vfs_unlink`.
kernel: fs/namei.c:link_path_walk,do_unlinkat,vfs_unlink,may_delete@v6.18.46 -/
theorem unlinkat_tmp_implied_directory_is_eisdir_over_the_real_table :
    check_syscall (unlink_call 0 (name_at tmp_d)) (ledgered (errno_ret EISDIR) 7)
      tmp_only_dir_model = CheckOk tmp_only_dir_model []
    ∧ check_syscall (unlink_call 0 (name_at tmp_d)) (ledgered 0 7) tmp_only_dir_model
      = CheckReject
    ∧ check_syscall (unlink_call 0 (name_at tmp_d_slash)) (ledgered (errno_ret EISDIR) 8)
        tmp_only_dir_model = CheckOk tmp_only_dir_model []
    ∧ check_syscall (unlink_call 0 (name_at tmp_d_slash)) (ledgered 0 8) tmp_only_dir_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The implied directory reaches `may_delete`'s directory check, whereas
the absent sibling gets -ENOENT from `lookup_one_qstr_excl`
(fs/namei.c:1713-1715), so exchanging those answers is refused.
kernel: fs/namei.c:do_unlinkat,may_delete,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_tmp_implied_directory_precedes_not_held_over_the_real_table :
    check_syscall (unlink_call 0 (name_at tmp_d)) (ledgered (errno_ret ENOENT) 7)
      tmp_only_dir_model = CheckReject
    ∧ check_syscall (unlink_call 0 (name_at tmp_d)) (ledgered (errno_ret EISDIR) 7)
        tmp_only_dir_model = CheckOk tmp_only_dir_model []
    ∧ check_syscall (unlink_call 0 (name_at abs_gif_name)) (ledgered (errno_ret ENOENT) 13)
        tmp_only_dir_model = CheckOk tmp_only_dir_model []
    ∧ check_syscall (unlink_call 0 (name_at abs_gif_name)) (ledgered (errno_ret EISDIR) 13)
        tmp_only_dir_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The plain sibling reaches `vfs_unlink` through `do_unlinkat`
(fs/namei.c:4741); removing it leaves the nested directory's key intact.
kernel: fs/namei.c:do_unlinkat,vfs_unlink@v6.18.46 -/
theorem unlinkat_tmp_implied_directory_sibling_still_unlinks_over_the_real_table :
    fs_lookup (m_fs tmp_shapes_model) tmp_d_f = some [104]
    ∧ check_syscall (unlink_call 0 (name_at abs_gif_name)) (ledgered 0 13) tmp_shapes_model
      = CheckOk tmp_only_dir_model []
    ∧ fs_lookup (m_fs tmp_only_dir_model) abs_gif_name = none
    ∧ fs_lookup (m_fs tmp_only_dir_model) tmp_d_f = some [104] :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- A 255-byte component reaches removal at fs/namei.c:4741, whereas a
256-byte component gets -ENAMETOOLONG from `simple_lookup`
(fs/libfs.c:71-72), beyond the model's claimed surface.
kernel: fs/namei.c:do_unlinkat,vfs_unlink; fs/libfs.c:simple_lookup@v6.18.46 -/
theorem unlinkat_tmp_name_max_boundary_over_the_real_table :
    check_syscall (unlink_call 0 (name_at (tmp_key name255))) (ledgered 0 261)
      tmp_name255_model = CheckOk empty_model []
    ∧ check_syscall (unlink_call 0 (name_at (tmp_key name256))) (ledgered 0 262)
      tmp_name256_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- Under the private-directory premise a held key passes the negative-dentry test at fs/namei.c:1713-1715 and reaches :4741; ret=-ENOENT lies about its existence.
kernel: fs/namei.c:do_unlinkat,lookup_one_qstr_excl@v6.18.46 -/
theorem unlinkat_held_key_enoent_rejected_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97])) (ledgered (errno_ret ENOENT) 2)
      unlink_model = CheckReject := rfl

/-- The short pathname copy at fs/namei.c:157 stops at its NUL (lib/strncpy_from_user.c:68-75); grow-copyins and a second smuggled logical copy-in are refused.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem unlinkat_copyin_overrun_and_second_read_rejected_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97])) (ledgered 0 3) unlink_model = CheckReject
    ∧ check_syscall (unlink_call 0 (name_at [97]))
        (with_copyins [(8192, 2), (8192, 1)] (mkEffect 0 [] [])) unlink_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- The path at fs/namei.c:4775-4782 and :4705-4773 reads a pathname and removes a dentry; forged user writes, zeroes, unmaps and copies are refused.
kernel: fs/namei.c:unlinkat,do_unlinkat@v6.18.46 -/
theorem unlinkat_forged_ledgers_rejected_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97]))
      (with_copyins [(8192, 2)] (SyscallEffect.mkEffectU 0 [(8192, [0])] [] [] [] []))
      unlink_model = CheckReject
    ∧ check_syscall (unlink_call 0 (name_at [97]))
      (with_copyins [(8192, 2)] (SyscallEffect.mkEffectU 0 [] [(8192, 4096)] [] [] []))
      unlink_model = CheckReject
    ∧ check_syscall (unlink_call 0 (name_at [97]))
      (with_copyins [(8192, 2)] (SyscallEffect.mkEffectU 0 [] [] [(8192, 4096)] [] []))
      unlink_model = CheckReject
    ∧ check_syscall (unlink_call 0 (name_at [97]))
      (with_copyins [(8192, 2)] (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 8192 8192 1] []))
      unlink_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The AT_FDCWD branch of fs/namei.c:2589-2603 bypasses the descriptor lookup at :2610-2611; removal at :4741 returns no positive byte count. This refuses ret=-EBADF and ret=1.
kernel: fs/namei.c:path_init,do_unlinkat@v6.18.46 -/
theorem unlinkat_removal_other_returns_rejected_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97])) (ledgered (errno_ret EBADF) 2) unlink_model
      = CheckReject
    ∧ check_syscall (unlink_call 0 (name_at [97])) (ledgered 1 2) unlink_model
      = CheckReject :=
  ⟨rfl, rfl⟩

/-- The typed-name returns at fs/namei.c:4720-4722 and :4584-4592 distinguish dot, dotdot and root; forged alternative errnos are refused.
kernel: fs/namei.c:unlinkat,do_unlinkat,do_rmdir,getname_flags@v6.18.46 -/
theorem unlinkat_dot_names_refuse_the_other_answers_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [46])) (ledgered (errno_ret ENOMEM) 2) empty_model
      = CheckReject
    ∧ check_syscall (unlink_call 0 (name_at [46])) (ledgered (errno_ret EINVAL) 2) empty_model
      = CheckReject
    ∧ check_syscall (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46]))
        (ledgered (errno_ret EISDIR) 2) empty_model = CheckReject
    ∧ check_syscall (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46, 46]))
        (ledgered (errno_ret EISDIR) 3) empty_model = CheckReject
    ∧ check_syscall (unlink_call 0 (name_at [46, 46])) (ledgered (errno_ret ENOTEMPTY) 3)
        empty_model = CheckReject
    ∧ check_syscall (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at [46, 46, 47]))
        (ledgered (errno_ret EBUSY) 4) empty_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The int flag cast precedes fs/namei.c:4777: bit 32 alone becomes zero, so a bare -EINVAL is refused (include/linux/syscalls.h:132).
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem unlinkat_flag_2_pow_32_einval_rejected_over_the_real_table :
    check_syscall (unlink_call 4294967296 (name_at [97])) (mkEffect (errno_ret EINVAL) [] [])
      unlink_model = CheckReject := rfl

/-- The int casts (include/linux/syscalls.h:132) precede fs/namei.c:4777-4782; AT_REMOVEDIR on the held file gets -ENOTDIR at :3285-3286.
kernel: fs/namei.c:unlinkat,may_delete@v6.18.46 -/
theorem unlinkat_arguments_are_ints_over_the_real_table :
    check_syscall (unlink_call_at (Z_to_bv 64 4294967196) 0 (name_at [97])) (ledgered 0 2)
      unlink_model = CheckOk unlinked_model []
    ∧ check_syscall (unlink_call 4294967296 (name_at [97])) (ledgered 0 2) unlink_model
      = CheckOk unlinked_model []
    ∧ check_syscall (unlink_call 4294967808 (name_at [97])) (ledgered (errno_ret ENOTDIR) 2)
        unlink_model = CheckOk unlink_model []
    ∧ check_syscall (unlink_call (Z_to_bv 64 (-1)) (name_at [97]))
        (mkEffect (errno_ret EINVAL) [] []) unlink_model = CheckOk unlink_model [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The empty pathname returns -ENOENT at fs/namei.c:168-170, before directory lookup.
kernel: fs/namei.c:getname_flags,unlinkat@v6.18.46 -/
theorem unlinkat_empty_path_is_enoent_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [])) (ledgered (errno_ret ENOENT) 1) unlink_model
      = CheckOk unlink_model []
    ∧ check_syscall (unlink_call (Z_to_bv 64 AT_REMOVEDIR) (name_at []))
        (ledgered (errno_ret ENOENT) 1) unlink_model = CheckOk unlink_model []
    ∧ check_syscall (unlink_call_at 3 0 (name_at [])) (ledgered (errno_ret ENOENT) 1)
        unlink_model = CheckOk unlink_model [] :=
  ⟨rfl, rfl, rfl⟩

/-- A failed pathname copy propagates its fault at fs/namei.c:161-164.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem unlinkat_fault_is_efault_over_the_real_table :
    check_syscall (unlink_call 0 unmapped) (ledgered (errno_ret EFAULT) 1) unlink_model
      = CheckOk unlink_model []
    ∧ check_syscall (unlink_call 0 unterminated) (ledgered (errno_ret EFAULT) 2) unlink_model
      = CheckOk unlink_model [] :=
  ⟨rfl, rfl⟩

/-- The zero-high-half spelling 0x00000000FFFFFF9C denotes AT_FDCWD
through the int cast (include/linux/syscalls.h:132), before the working-directory
branch at fs/namei.c:2589-2603. A sign-extended spelling also exercises the
arm's fd32 conversion: passing that whole register to the checker declines.
kernel: fs/namei.c:path_init; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem dirfd_narrowing_over_the_real_table :
    check_syscall (unlink_call_at 0x00000000FFFFFF9C 0 (name_at [97]))
      (ledgered 0 2) unlink_model = CheckOk unlinked_model []
    ∧ check_syscall (unlink_call_at 0x00000000FFFFFF9C 0 (name_at [97]))
      (ledgered (errno_ret ENOENT) 2) unlink_model = CheckReject
    ∧ check_syscall (unlink_call_at AT_FDCWD 0 (name_at [97]))
      (ledgered 0 2) unlink_model = CheckOk unlinked_model []
    ∧ check_syscall (unlink_call_at AT_FDCWD 0 (name_at [97]))
      (ledgered (errno_ret ENOENT) 2) unlink_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Bit 32 is discarded before the flag gate at fs/namei.c:4777; even
beside the correct pathname ledger, -EINVAL is refused on the held file.
kernel: fs/namei.c:unlinkat; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem narrowed_flag_einval_with_copyin_rejected_over_the_real_table :
    check_syscall (unlink_call 4294967296 (name_at [97]))
      (ledgered (errno_ret EINVAL) 2) unlink_model = CheckReject := rfl

/-- A bad flag is -EINVAL before getname at fs/namei.c:4777-4782:
ret=0, ret=-EFAULT and ret=-ENAMETOOLONG are lies about this gate.
kernel: fs/namei.c:unlinkat,getname_flags; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem bad_flag_return_lies_over_the_real_table :
    check_syscall (unlink_call 1 unmapped) (mkEffect 0 [] []) unlink_model = CheckReject
    ∧ check_syscall (unlink_call 1 unmapped) (mkEffect (errno_ret EFAULT) [] [])
        unlink_model = CheckReject
    ∧ check_syscall (unlink_call 1 unmapped) (mkEffect (errno_ret ENAMETOOLONG) [] [])
        unlink_model = CheckReject := ⟨rfl, rfl, rfl⟩

/-- Hiding the terminator makes the copy fail at fs/namei.c:161-164;
ret=-ENOENT then lies about the fetched name. The paired -EFAULT is accepted.
kernel: fs/namei.c:getname_flags; lib/strncpy_from_user.c:do_strncpy_from_user@v6.18.46 -/
theorem hidden_path_byte_over_the_real_table :
    check_syscall (unlink_call 0 unterminated) (ledgered (errno_ret ENOENT) 2)
        empty_model = CheckReject
    ∧ check_syscall (unlink_call 0 unterminated) (ledgered (errno_ret EFAULT) 2)
        empty_model = CheckOk empty_model [] := ⟨rfl, rfl⟩

/-- The wrapper gives pathname a1 (arch/riscv/include/asm/syscall_wrapper.h:21-24).
Only address 8192 holds the name: a transposed register faults in the
getname_flags copy at fs/namei.c:157-164 instead of reaching removal at :4741.
kernel: fs/namei.c:unlinkat,getname_flags,do_unlinkat,path_init; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS@v6.18.46 -/
theorem pathname_is_a1_over_the_real_table :
    check_syscall
      (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 31, 47, 63] (name_at [97]) unmapped)
      (ledgered 0 2) unlink_model = CheckOk unlinked_model [] := rfl

/-- The witness's accepted answer comes from the flag gate at
fs/namei.c:4777-4778; this is decided before the pathname acquisition.
kernel: fs/namei.c:unlinkat@v6.18.46 -/
theorem witness_bad_flag_over_the_real_table :
    syscall_spec_witness (unlink_call 1 (name_at [97])) a_empty_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) a_empty_model [] := rfl

/-- The witness declines a foreign dirfd; fs/namei.c:2610-2622 is where
the kernel resolves it, after getname at :4782.
kernel: fs/namei.c:path_init@v6.18.46 -/
theorem witness_dirfd_decline_over_the_real_table :
    syscall_spec_witness (unlink_call_at 3 0 (name_at [97])) unlink_model = Unmodeled := rfl

/-- An absent name fails the lookup at fs/namei.c:4729-4731 and
:1713-1715 before the trailing-separator branch at :4734; do_rmdir
likewise propagates lookup failure at :4600-4603. ret=-ENOTDIR is refused.
kernel: fs/namei.c:do_unlinkat,do_rmdir,lookup_one_qstr_excl@v6.18.46 -/
theorem absent_slash_enotdir_rejected_over_the_real_table :
    check_syscall (unlink_call 0 (name_at [97, 47])) (ledgered (errno_ret ENOENT) 3)
      empty_model = CheckOk empty_model []
    ∧ check_syscall (unlink_call 0 (name_at [97, 47])) (ledgered (errno_ret ENOTDIR) 3)
      empty_model = CheckReject
    ∧ check_syscall (unlink_call 512 (name_at [97, 47])) (ledgered (errno_ret ENOENT) 3)
      empty_model = CheckOk empty_model []
    ∧ check_syscall (unlink_call 512 (name_at [97, 47])) (ledgered (errno_ret ENOTDIR) 3)
      empty_model = CheckReject := ⟨rfl, rfl, rfl, rfl⟩

/-- `pathname` is a `const char __user *` (fs/namei.c:4775), and `__SC_CAST`
(include/linux/syscalls.h:132) casts the register to it without narrowing it,
so `getname_flags` copies the name from the full address (fs/namei.c:157).
The name here is mapped at 0x100002000 alone: its removal at AT_FDCWD is
admitted with the copy-in at that address, and refused when the copy-in is
ledgered at 0x2000, the low 32 bits of the pointer; so is ret=-EFAULT with a
one-byte copy-in at 0x2000, the fault a read there would take.
kernel: fs/namei.c:unlinkat,getname_flags,path_init; lib/strncpy_from_user.c:do_strncpy_from_user; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem unlinkat_pathname_pointer_keeps_register_width_over_the_real_table :
    check_syscall
      (SyscallInput.mkInput 35 [AT_FDCWD, 0x100002000, 0, 0, 0, 0]
        (bytes_at 0x100002000 [97, 0]) (fun _ => none))
      (with_copyins [(0x100002000, 2)] (mkEffect 0 [] [])) unlink_model
      = CheckOk unlinked_model []
    ∧ check_syscall
      (SyscallInput.mkInput 35 [AT_FDCWD, 0x100002000, 0, 0, 0, 0]
        (bytes_at 0x100002000 [97, 0]) (fun _ => none))
      (with_copyins [(0x2000, 2)] (mkEffect 0 [] [])) unlink_model = CheckReject
    ∧ check_syscall
      (SyscallInput.mkInput 35 [AT_FDCWD, 0x100002000, 0, 0, 0, 0]
        (bytes_at 0x100002000 [97, 0]) (fun _ => none))
      (with_copyins [(0x2000, 1)] (mkEffect (errno_ret EFAULT) [] [])) unlink_model
      = CheckReject := ⟨rfl, rfl, rfl⟩

end V_Fs_Namei

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Namei
